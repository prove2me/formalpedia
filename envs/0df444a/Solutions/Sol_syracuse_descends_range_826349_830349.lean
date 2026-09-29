-- Prove2me | solution 1 for syracuse_descends_range_826349_830349
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:46.425048+00:00
-- url     : https://prove2.me/submissions/08394645-9525-4175-a811-d4456add63a5

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


theorem B1245197 : Blo 826349 1245197 := bbase (se 3 (by rfl) ⟨233474, by rfl⟩ : syracuseStep 1245197 = 466949) (by norm_num)
theorem B1867805 : Blo 826349 1867805 := bbase (se 3 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 1867805 = 700427) (by norm_num)
theorem B4194341 : Blo 826349 4194341 := bbase (se 4 (by rfl) ⟨393219, by rfl⟩ : syracuseStep 4194341 = 786439) (by norm_num)
theorem B1245221 : Blo 826349 1245221 := bbase (se 4 (by rfl) ⟨116739, by rfl⟩ : syracuseStep 1245221 = 233479) (by norm_num)
theorem B1048621 : Blo 826349 1048621 := bbase (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) (by norm_num)
theorem B1245245 : Blo 826349 1245245 := bbase (se 3 (by rfl) ⟨233483, by rfl⟩ : syracuseStep 1245245 = 466967) (by norm_num)
theorem B1245269 : Blo 826349 1245269 := bbase (se 8 (by rfl) ⟨7296, by rfl⟩ : syracuseStep 1245269 = 14593) (by norm_num)
theorem B3539045 : Blo 826349 3539045 := bbase (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) (by norm_num)
theorem B1867877 : Blo 826349 1867877 := bbase (se 4 (by rfl) ⟨175113, by rfl⟩ : syracuseStep 1867877 = 350227) (by norm_num)
theorem B1245293 : Blo 826349 1245293 := bbase (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) (by norm_num)
theorem B1245317 : Blo 826349 1245317 := bbase (se 4 (by rfl) ⟨116748, by rfl⟩ : syracuseStep 1245317 = 233497) (by norm_num)
theorem B1048717 : Blo 826349 1048717 := bbase (se 3 (by rfl) ⟨196634, by rfl⟩ : syracuseStep 1048717 = 393269) (by norm_num)
theorem B884881 : Blo 826349 884881 := bbase (se 2 (by rfl) ⟨331830, by rfl⟩ : syracuseStep 884881 = 663661) (by norm_num)
theorem B2130077 : Blo 826349 2130077 := bbase (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) (by norm_num)
theorem B1245341 : Blo 826349 1245341 := bbase (se 3 (by rfl) ⟨233501, by rfl⟩ : syracuseStep 1245341 = 467003) (by norm_num)
theorem B1867949 : Blo 826349 1867949 := bbase (se 3 (by rfl) ⟨350240, by rfl⟩ : syracuseStep 1867949 = 700481) (by norm_num)
theorem B1245365 : Blo 826349 1245365 := bbase (se 5 (by rfl) ⟨58376, by rfl⟩ : syracuseStep 1245365 = 116753) (by norm_num)
theorem B1245389 : Blo 826349 1245389 := bbase (se 3 (by rfl) ⟨233510, by rfl⟩ : syracuseStep 1245389 = 467021) (by norm_num)
theorem B2097373 : Blo 826349 2097373 := bbase (se 3 (by rfl) ⟨393257, by rfl⟩ : syracuseStep 2097373 = 786515) (by norm_num)
theorem B1769693 : Blo 826349 1769693 := bbase (se 3 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 1769693 = 663635) (by norm_num)
theorem B1245413 : Blo 826349 1245413 := bbase (se 4 (by rfl) ⟨116757, by rfl⟩ : syracuseStep 1245413 = 233515) (by norm_num)
theorem B1868021 : Blo 826349 1868021 := bbase (se 5 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 1868021 = 175127) (by norm_num)
theorem B1245437 : Blo 826349 1245437 := bbase (se 3 (by rfl) ⟨233519, by rfl⟩ : syracuseStep 1245437 = 467039) (by norm_num)
theorem B1245461 : Blo 826349 1245461 := bbase (se 6 (by rfl) ⟨29190, by rfl⟩ : syracuseStep 1245461 = 58381) (by norm_num)
theorem B1245485 : Blo 826349 1245485 := bbase (se 3 (by rfl) ⟨233528, by rfl⟩ : syracuseStep 1245485 = 467057) (by norm_num)
theorem B1048889 : Blo 826349 1048889 := bbase (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) (by norm_num)
theorem B1868093 : Blo 826349 1868093 := bbase (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) (by norm_num)
theorem B1245509 : Blo 826349 1245509 := bbase (se 4 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 1245509 = 233533) (by norm_num)
theorem B2097485 : Blo 826349 2097485 := bbase (se 3 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 2097485 = 786557) (by norm_num)
theorem B3539285 : Blo 826349 3539285 := bbase (se 10 (by rfl) ⟨5184, by rfl⟩ : syracuseStep 3539285 = 10369) (by norm_num)
theorem B2359637 : Blo 826349 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B1048945 : Blo 826349 1048945 := bbase (se 2 (by rfl) ⟨393354, by rfl⟩ : syracuseStep 1048945 = 786709) (by norm_num)
theorem B1868165 : Blo 826349 1868165 := bbase (se 4 (by rfl) ⟨175140, by rfl⟩ : syracuseStep 1868165 = 350281) (by norm_num)
theorem B1769933 : Blo 826349 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1180109 : Blo 826349 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B1868237 : Blo 826349 1868237 := bbase (se 3 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 1868237 = 700589) (by norm_num)
theorem B1049041 : Blo 826349 1049041 := bbase (se 2 (by rfl) ⟨393390, by rfl⟩ : syracuseStep 1049041 = 786781) (by norm_num)
theorem B1573357 : Blo 826349 1573357 := bbase (se 3 (by rfl) ⟨295004, by rfl⟩ : syracuseStep 1573357 = 590009) (by norm_num)
theorem B2097677 : Blo 826349 2097677 := bbase (se 3 (by rfl) ⟨393314, by rfl⟩ : syracuseStep 2097677 = 786629) (by norm_num)
theorem B2982437 : Blo 826349 2982437 := bbase (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) (by norm_num)
theorem B1573501 : Blo 826349 1573501 := bbase (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) (by norm_num)
theorem B1049213 : Blo 826349 1049213 := bbase (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) (by norm_num)
theorem B1049269 : Blo 826349 1049269 := bbase (se 5 (by rfl) ⟨49184, by rfl⟩ : syracuseStep 1049269 = 98369) (by norm_num)
theorem B3146485 : Blo 826349 3146485 := bbase (se 5 (by rfl) ⟨147491, by rfl⟩ : syracuseStep 3146485 = 294983) (by norm_num)
theorem B1049365 : Blo 826349 1049365 := bbase (se 6 (by rfl) ⟨24594, by rfl⟩ : syracuseStep 1049365 = 49189) (by norm_num)
theorem B1573661 : Blo 826349 1573661 := bbase (se 3 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 1573661 = 590123) (by norm_num)
theorem B2098021 : Blo 826349 2098021 := bbase (se 4 (by rfl) ⟨196689, by rfl⟩ : syracuseStep 2098021 = 393379) (by norm_num)
theorem B10617749 : Blo 826349 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B1573805 : Blo 826349 1573805 := bbase (se 3 (by rfl) ⟨295088, by rfl⟩ : syracuseStep 1573805 = 590177) (by norm_num)
theorem B1049537 : Blo 826349 1049537 := bbase (se 2 (by rfl) ⟨393576, by rfl⟩ : syracuseStep 1049537 = 787153) (by norm_num)
theorem B1770437 : Blo 826349 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B885701 : Blo 826349 885701 := bbase (se 4 (by rfl) ⟨83034, by rfl⟩ : syracuseStep 885701 = 166069) (by norm_num)
theorem B1770445 : Blo 826349 1770445 := bbase (se 3 (by rfl) ⟨331958, by rfl⟩ : syracuseStep 1770445 = 663917) (by norm_num)
theorem B2098133 : Blo 826349 2098133 := bbase (se 7 (by rfl) ⟨24587, by rfl⟩ : syracuseStep 2098133 = 49175) (by norm_num)
theorem B1180661 : Blo 826349 1180661 := bbase (se 5 (by rfl) ⟨55343, by rfl⟩ : syracuseStep 1180661 = 110687) (by norm_num)
theorem B1049593 : Blo 826349 1049593 := bbase (se 2 (by rfl) ⟨393597, by rfl⟩ : syracuseStep 1049593 = 787195) (by norm_num)
theorem B3146789 : Blo 826349 3146789 := bbase (se 4 (by rfl) ⟨295011, by rfl⟩ : syracuseStep 3146789 = 590023) (by norm_num)
theorem B1049689 : Blo 826349 1049689 := bbase (se 2 (by rfl) ⟨393633, by rfl⟩ : syracuseStep 1049689 = 787267) (by norm_num)
theorem B2098325 : Blo 826349 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B2655413 : Blo 826349 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B1574093 : Blo 826349 1574093 := bbase (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) (by norm_num)
theorem B1049861 : Blo 826349 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B4195637 : Blo 826349 4195637 := bbase (se 5 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 4195637 = 393341) (by norm_num)
theorem B1049917 : Blo 826349 1049917 := bbase (se 3 (by rfl) ⟨196859, by rfl⟩ : syracuseStep 1049917 = 393719) (by norm_num)
theorem B1574245 : Blo 826349 1574245 := bbase (se 4 (by rfl) ⟨147585, by rfl⟩ : syracuseStep 1574245 = 295171) (by norm_num)
theorem B886145 : Blo 826349 886145 := bbase (se 2 (by rfl) ⟨332304, by rfl⟩ : syracuseStep 886145 = 664609) (by norm_num)
theorem B1050013 : Blo 826349 1050013 := bbase (se 3 (by rfl) ⟨196877, by rfl⟩ : syracuseStep 1050013 = 393755) (by norm_num)
theorem B2098669 : Blo 826349 2098669 := bbase (se 3 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 2098669 = 787001) (by norm_num)
theorem B2360821 : Blo 826349 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B1050185 : Blo 826349 1050185 := bbase (se 2 (by rfl) ⟨393819, by rfl⟩ : syracuseStep 1050185 = 787639) (by norm_num)
theorem B2098781 : Blo 826349 2098781 := bbase (se 3 (by rfl) ⟨393521, by rfl⟩ : syracuseStep 2098781 = 787043) (by norm_num)
theorem B886393 : Blo 826349 886393 := bbase (se 2 (by rfl) ⟨332397, by rfl⟩ : syracuseStep 886393 = 664795) (by norm_num)
theorem B1050241 : Blo 826349 1050241 := bbase (se 2 (by rfl) ⟨393840, by rfl⟩ : syracuseStep 1050241 = 787681) (by norm_num)
theorem B2360981 : Blo 826349 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B1574549 : Blo 826349 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B1050337 : Blo 826349 1050337 := bbase (se 2 (by rfl) ⟨393876, by rfl⟩ : syracuseStep 1050337 = 787753) (by norm_num)
theorem B1181413 : Blo 826349 1181413 := bbase (se 4 (by rfl) ⟨110757, by rfl⟩ : syracuseStep 1181413 = 221515) (by norm_num)
theorem B7571189 : Blo 826349 7571189 := bbase (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) (by norm_num)
theorem B2098973 : Blo 826349 2098973 := bbase (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) (by norm_num)
theorem B2361221 : Blo 826349 2361221 := bbase (se 4 (by rfl) ⟨221364, by rfl⟩ : syracuseStep 2361221 = 442729) (by norm_num)
theorem B1050509 : Blo 826349 1050509 := bbase (se 3 (by rfl) ⟨196970, by rfl⟩ : syracuseStep 1050509 = 393941) (by norm_num)
theorem B2295749 : Blo 826349 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B1050565 : Blo 826349 1050565 := bbase (se 4 (by rfl) ⟨98490, by rfl⟩ : syracuseStep 1050565 = 196981) (by norm_num)
theorem B1050661 : Blo 826349 1050661 := bbase (se 4 (by rfl) ⟨98499, by rfl⟩ : syracuseStep 1050661 = 196999) (by norm_num)
theorem B2656309 : Blo 826349 2656309 := bbase (se 5 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 2656309 = 249029) (by norm_num)
theorem B1771573 : Blo 826349 1771573 := bbase (se 5 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 1771573 = 166085) (by norm_num)
theorem B2361413 : Blo 826349 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B2099317 : Blo 826349 2099317 := bbase (se 5 (by rfl) ⟨98405, by rfl⟩ : syracuseStep 2099317 = 196811) (by norm_num)
theorem B1050833 : Blo 826349 1050833 := bbase (se 2 (by rfl) ⟨394062, by rfl⟩ : syracuseStep 1050833 = 788125) (by norm_num)
theorem B2099429 : Blo 826349 2099429 := bbase (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) (by norm_num)
theorem B1050889 : Blo 826349 1050889 := bbase (se 2 (by rfl) ⟨394083, by rfl⟩ : syracuseStep 1050889 = 788167) (by norm_num)
theorem B1575301 : Blo 826349 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B2099621 : Blo 826349 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B1771949 : Blo 826349 1771949 := bbase (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) (by norm_num)
theorem B5048821 : Blo 826349 5048821 := bbase (se 5 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 5048821 = 473327) (by norm_num)
theorem B1182205 : Blo 826349 1182205 := bbase (se 3 (by rfl) ⟨221663, by rfl⟩ : syracuseStep 1182205 = 443327) (by norm_num)
theorem B1575445 : Blo 826349 1575445 := bbase (se 6 (by rfl) ⟨36924, by rfl⟩ : syracuseStep 1575445 = 73849) (by norm_num)
theorem B4196933 : Blo 826349 4196933 := bbase (se 4 (by rfl) ⟨393462, by rfl⟩ : syracuseStep 4196933 = 786925) (by norm_num)
theorem B3541573 : Blo 826349 3541573 := bbase (se 4 (by rfl) ⟨332022, by rfl⟩ : syracuseStep 3541573 = 664045) (by norm_num)
theorem B1575605 : Blo 826349 1575605 := bbase (se 5 (by rfl) ⟨73856, by rfl⟩ : syracuseStep 1575605 = 147713) (by norm_num)
theorem B2099965 : Blo 826349 2099965 := bbase (se 3 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 2099965 = 787487) (by norm_num)
theorem B2394917 : Blo 826349 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1575749 : Blo 826349 1575749 := bbase (se 4 (by rfl) ⟨147726, by rfl⟩ : syracuseStep 1575749 = 295453) (by norm_num)
theorem B13405013 : Blo 826349 13405013 := bbase (se 9 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 13405013 = 78545) (by norm_num)
theorem B2100077 : Blo 826349 2100077 := bbase (se 3 (by rfl) ⟨393764, by rfl⟩ : syracuseStep 2100077 = 787529) (by norm_num)
theorem B2362405 : Blo 826349 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B2100269 : Blo 826349 2100269 := bbase (se 3 (by rfl) ⟨393800, by rfl⟩ : syracuseStep 2100269 = 787601) (by norm_num)
theorem B3148901 : Blo 826349 3148901 := bbase (se 4 (by rfl) ⟨295209, by rfl⟩ : syracuseStep 3148901 = 590419) (by norm_num)
theorem B1576037 : Blo 826349 1576037 := bbase (se 4 (by rfl) ⟨147753, by rfl⟩ : syracuseStep 1576037 = 295507) (by norm_num)
theorem B1576189 : Blo 826349 1576189 := bbase (se 3 (by rfl) ⟨295535, by rfl⟩ : syracuseStep 1576189 = 591071) (by norm_num)
theorem B3149189 : Blo 826349 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B2100613 : Blo 826349 2100613 := bbase (se 4 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 2100613 = 393865) (by norm_num)
theorem B1347005 : Blo 826349 1347005 := bbase (se 3 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 1347005 = 505127) (by norm_num)
theorem B2100725 : Blo 826349 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B1379885 : Blo 826349 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B1117765 : Blo 826349 1117765 := bbase (se 4 (by rfl) ⟨104790, by rfl⟩ : syracuseStep 1117765 = 209581) (by norm_num)
theorem B6295157 : Blo 826349 6295157 := bbase (se 5 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 6295157 = 590171) (by norm_num)
theorem B2789045 : Blo 826349 2789045 := bbase (se 5 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 2789045 = 261473) (by norm_num)
theorem B2100917 : Blo 826349 2100917 := bbase (se 5 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 2100917 = 196961) (by norm_num)
theorem B15109973 : Blo 826349 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B4198229 : Blo 826349 4198229 := bbase (se 9 (by rfl) ⟨12299, by rfl⟩ : syracuseStep 4198229 = 24599) (by norm_num)
theorem B2101261 : Blo 826349 2101261 := bbase (se 3 (by rfl) ⟨393986, by rfl⟩ : syracuseStep 2101261 = 787973) (by norm_num)
theorem B3543061 : Blo 826349 3543061 := bbase (se 6 (by rfl) ⟨83040, by rfl⟩ : syracuseStep 3543061 = 166081) (by norm_num)
theorem B3543077 : Blo 826349 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B2789477 : Blo 826349 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B5967989 : Blo 826349 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B2363509 : Blo 826349 2363509 := bbase (se 5 (by rfl) ⟨110789, by rfl⟩ : syracuseStep 2363509 = 221579) (by norm_num)
theorem B2101373 : Blo 826349 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B2298133 : Blo 826349 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B2101565 : Blo 826349 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B2789909 : Blo 826349 2789909 := bbase (se 6 (by rfl) ⟨65388, by rfl⟩ : syracuseStep 2789909 = 130777) (by norm_num)
theorem B3150373 : Blo 826349 3150373 := bbase (se 4 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 3150373 = 590695) (by norm_num)
theorem B3150677 : Blo 826349 3150677 := bbase (se 9 (by rfl) ⟨9230, by rfl⟩ : syracuseStep 3150677 = 18461) (by norm_num)
theorem B2659205 : Blo 826349 2659205 := bbase (se 4 (by rfl) ⟨249300, by rfl⟩ : syracuseStep 2659205 = 498601) (by norm_num)
theorem B2790341 : Blo 826349 2790341 := bbase (se 4 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 2790341 = 523189) (by norm_num)
theorem B1414181 : Blo 826349 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B1119317 : Blo 826349 1119317 := bbase (se 8 (by rfl) ⟨6558, by rfl⟩ : syracuseStep 1119317 = 13117) (by norm_num)
theorem B1676381 : Blo 826349 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1676389 : Blo 826349 1676389 := bbase (se 4 (by rfl) ⟨157161, by rfl⟩ : syracuseStep 1676389 = 314323) (by norm_num)
theorem B4199525 : Blo 826349 4199525 := bbase (se 4 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 4199525 = 787411) (by norm_num)
theorem B4723829 : Blo 826349 4723829 := bbase (se 5 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 4723829 = 442859) (by norm_num)
theorem B2790773 : Blo 826349 2790773 := bbase (se 5 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 2790773 = 261635) (by norm_num)
theorem B1676837 : Blo 826349 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B10753685 : Blo 826349 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B1119949 : Blo 826349 1119949 := bbase (se 3 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 1119949 = 419981) (by norm_num)
theorem B2791205 : Blo 826349 2791205 := bbase (se 4 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 2791205 = 523351) (by norm_num)
theorem B1120069 : Blo 826349 1120069 := bbase (se 4 (by rfl) ⟨105006, by rfl⟩ : syracuseStep 1120069 = 210013) (by norm_num)
theorem B3774485 : Blo 826349 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B3446885 : Blo 826349 3446885 := bbase (se 4 (by rfl) ⟨323145, by rfl⟩ : syracuseStep 3446885 = 646291) (by norm_num)
theorem B1415357 : Blo 826349 1415357 := bbase (se 3 (by rfl) ⟨265379, by rfl⟩ : syracuseStep 1415357 = 530759) (by norm_num)
theorem B2791637 : Blo 826349 2791637 := bbase (se 7 (by rfl) ⟨32714, by rfl⟩ : syracuseStep 2791637 = 65429) (by norm_num)
theorem B3545333 : Blo 826349 3545333 := bbase (se 5 (by rfl) ⟨166187, by rfl⟩ : syracuseStep 3545333 = 332375) (by norm_num)
theorem B4725013 : Blo 826349 4725013 := bbase (se 6 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 4725013 = 221485) (by norm_num)
theorem B4200821 : Blo 826349 4200821 := bbase (se 5 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 4200821 = 393827) (by norm_num)
theorem B2792069 : Blo 826349 2792069 := bbase (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) (by norm_num)
theorem B1678205 : Blo 826349 1678205 := bbase (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) (by norm_num)
theorem B2792501 : Blo 826349 2792501 := bbase (se 5 (by rfl) ⟨130898, by rfl⟩ : syracuseStep 2792501 = 261797) (by norm_num)
theorem B1121333 : Blo 826349 1121333 := bbase (se 5 (by rfl) ⟨52562, by rfl⟩ : syracuseStep 1121333 = 105125) (by norm_num)
theorem B2694293 : Blo 826349 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B7085333 : Blo 826349 7085333 := bbase (se 6 (by rfl) ⟨166062, by rfl⟩ : syracuseStep 7085333 = 332125) (by norm_num)
theorem B2792933 : Blo 826349 2792933 := bbase (se 4 (by rfl) ⟨261837, by rfl⟩ : syracuseStep 2792933 = 523675) (by norm_num)
theorem B4202117 : Blo 826349 4202117 := bbase (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) (by norm_num)
theorem B1122085 : Blo 826349 1122085 := bbase (se 4 (by rfl) ⟨105195, by rfl⟩ : syracuseStep 1122085 = 210391) (by norm_num)
theorem B2793365 : Blo 826349 2793365 := bbase (se 6 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 2793365 = 130939) (by norm_num)
theorem B3973045 : Blo 826349 3973045 := bbase (se 5 (by rfl) ⟨186236, by rfl⟩ : syracuseStep 3973045 = 372473) (by norm_num)
theorem B16981973 : Blo 826349 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B1679437 : Blo 826349 1679437 := bbase (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) (by norm_num)
theorem B4726997 : Blo 826349 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B2793797 : Blo 826349 2793797 := bbase (se 4 (by rfl) ⟨261918, by rfl⟩ : syracuseStep 2793797 = 523837) (by norm_num)
theorem B2794229 : Blo 826349 2794229 := bbase (se 5 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 2794229 = 261959) (by norm_num)
theorem B4203413 : Blo 826349 4203413 := bbase (se 6 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 4203413 = 197035) (by norm_num)
theorem B1516501 : Blo 826349 1516501 := bbase (se 7 (by rfl) ⟨17771, by rfl⟩ : syracuseStep 1516501 = 35543) (by norm_num)
theorem B5317589 : Blo 826349 5317589 := bbase (se 7 (by rfl) ⟨62315, by rfl⟩ : syracuseStep 5317589 = 124631) (by norm_num)
theorem B2794661 : Blo 826349 2794661 := bbase (se 4 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 2794661 = 523999) (by norm_num)
theorem B1418629 : Blo 826349 1418629 := bbase (se 4 (by rfl) ⟨132996, by rfl⟩ : syracuseStep 1418629 = 265993) (by norm_num)
theorem B2795093 : Blo 826349 2795093 := bbase (se 8 (by rfl) ⟨16377, by rfl⟩ : syracuseStep 2795093 = 32755) (by norm_num)
theorem B6727349 : Blo 826349 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B7186133 : Blo 826349 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B993065 : Blo 826349 993065 := bbase (se 2 (by rfl) ⟨372399, by rfl⟩ : syracuseStep 993065 = 744799) (by norm_num)
theorem B1681205 : Blo 826349 1681205 := bbase (se 5 (by rfl) ⟨78806, by rfl⟩ : syracuseStep 1681205 = 157613) (by norm_num)
theorem B2795525 : Blo 826349 2795525 := bbase (se 4 (by rfl) ⟨262080, by rfl⟩ : syracuseStep 2795525 = 524161) (by norm_num)
theorem B7088309 : Blo 826349 7088309 := bbase (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) (by norm_num)
theorem B1681661 : Blo 826349 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B993665 : Blo 826349 993665 := bbase (se 2 (by rfl) ⟨372624, by rfl⟩ : syracuseStep 993665 = 745249) (by norm_num)
theorem B2795957 : Blo 826349 2795957 := bbase (se 5 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 2795957 = 262121) (by norm_num)
theorem B993973 : Blo 826349 993973 := bbase (se 5 (by rfl) ⟨46592, by rfl⟩ : syracuseStep 993973 = 93185) (by norm_num)
theorem B994069 : Blo 826349 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B994117 : Blo 826349 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B2796389 : Blo 826349 2796389 := bbase (se 4 (by rfl) ⟨262161, by rfl⟩ : syracuseStep 2796389 = 524323) (by norm_num)
theorem B2829509 : Blo 826349 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B6302933 : Blo 826349 6302933 := bbase (se 7 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 6302933 = 147725) (by norm_num)
theorem B2796821 : Blo 826349 2796821 := bbase (se 6 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 2796821 = 131101) (by norm_num)
theorem B1682869 : Blo 826349 1682869 := bbase (se 5 (by rfl) ⟨78884, by rfl⟩ : syracuseStep 1682869 = 157769) (by norm_num)
theorem B1682893 : Blo 826349 1682893 := bbase (se 3 (by rfl) ⟨315542, by rfl⟩ : syracuseStep 1682893 = 631085) (by norm_num)
theorem B1617509 : Blo 826349 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B2797253 : Blo 826349 2797253 := bbase (se 4 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 2797253 = 524485) (by norm_num)
theorem B3977045 : Blo 826349 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B7974773 : Blo 826349 7974773 := bbase (se 5 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 7974773 = 747635) (by norm_num)
theorem B929677 : Blo 826349 929677 := bbase (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) (by norm_num)
theorem B929713 : Blo 826349 929713 := bbase (se 2 (by rfl) ⟨348642, by rfl⟩ : syracuseStep 929713 = 697285) (by norm_num)
theorem B929749 : Blo 826349 929749 := bbase (se 7 (by rfl) ⟨10895, by rfl⟩ : syracuseStep 929749 = 21791) (by norm_num)
theorem B1257437 : Blo 826349 1257437 := bbase (se 3 (by rfl) ⟨235769, by rfl⟩ : syracuseStep 1257437 = 471539) (by norm_num)
theorem B929785 : Blo 826349 929785 := bbase (se 2 (by rfl) ⟨348669, by rfl⟩ : syracuseStep 929785 = 697339) (by norm_num)
theorem B995333 : Blo 826349 995333 := bbase (se 4 (by rfl) ⟨93312, by rfl⟩ : syracuseStep 995333 = 186625) (by norm_num)
theorem B929821 : Blo 826349 929821 := bbase (se 3 (by rfl) ⟨174341, by rfl⟩ : syracuseStep 929821 = 348683) (by norm_num)
theorem B929857 : Blo 826349 929857 := bbase (se 2 (by rfl) ⟨348696, by rfl⟩ : syracuseStep 929857 = 697393) (by norm_num)
theorem B929893 : Blo 826349 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B3977333 : Blo 826349 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B2797685 : Blo 826349 2797685 := bbase (se 5 (by rfl) ⟨131141, by rfl⟩ : syracuseStep 2797685 = 262283) (by norm_num)
theorem B929929 : Blo 826349 929929 := bbase (se 2 (by rfl) ⟨348723, by rfl⟩ : syracuseStep 929929 = 697447) (by norm_num)
theorem B929965 : Blo 826349 929965 := bbase (se 3 (by rfl) ⟨174368, by rfl⟩ : syracuseStep 929965 = 348737) (by norm_num)
theorem B995501 : Blo 826349 995501 := bbase (se 3 (by rfl) ⟨186656, by rfl⟩ : syracuseStep 995501 = 373313) (by norm_num)
theorem B930001 : Blo 826349 930001 := bbase (se 2 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 930001 = 697501) (by norm_num)
theorem B3354853 : Blo 826349 3354853 := bbase (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) (by norm_num)
theorem B930037 : Blo 826349 930037 := bbase (se 5 (by rfl) ⟨43595, by rfl⟩ : syracuseStep 930037 = 87191) (by norm_num)
theorem B930073 : Blo 826349 930073 := bbase (se 2 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 930073 = 697555) (by norm_num)
theorem B1257773 : Blo 826349 1257773 := bbase (se 3 (by rfl) ⟨235832, by rfl⟩ : syracuseStep 1257773 = 471665) (by norm_num)
theorem B930109 : Blo 826349 930109 := bbase (se 3 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 930109 = 348791) (by norm_num)
theorem B930145 : Blo 826349 930145 := bbase (se 2 (by rfl) ⟨348804, by rfl⟩ : syracuseStep 930145 = 697609) (by norm_num)
theorem B2240885 : Blo 826349 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B930181 : Blo 826349 930181 := bbase (se 4 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 930181 = 174409) (by norm_num)
theorem B930217 : Blo 826349 930217 := bbase (se 2 (by rfl) ⟨348831, by rfl⟩ : syracuseStep 930217 = 697663) (by norm_num)
theorem B930253 : Blo 826349 930253 := bbase (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) (by norm_num)
theorem B995809 : Blo 826349 995809 := bbase (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) (by norm_num)
theorem B930289 : Blo 826349 930289 := bbase (se 2 (by rfl) ⟨348858, by rfl⟩ : syracuseStep 930289 = 697717) (by norm_num)
theorem B930325 : Blo 826349 930325 := bbase (se 6 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 930325 = 43609) (by norm_num)
theorem B2798117 : Blo 826349 2798117 := bbase (se 4 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 2798117 = 524647) (by norm_num)
theorem B930361 : Blo 826349 930361 := bbase (se 2 (by rfl) ⟨348885, by rfl⟩ : syracuseStep 930361 = 697771) (by norm_num)
theorem B930397 : Blo 826349 930397 := bbase (se 3 (by rfl) ⟨174449, by rfl⟩ : syracuseStep 930397 = 348899) (by norm_num)
theorem B930433 : Blo 826349 930433 := bbase (se 2 (by rfl) ⟨348912, by rfl⟩ : syracuseStep 930433 = 697825) (by norm_num)
theorem B1323677 : Blo 826349 1323677 := bbase (se 3 (by rfl) ⟨248189, by rfl⟩ : syracuseStep 1323677 = 496379) (by norm_num)
theorem B930469 : Blo 826349 930469 := bbase (se 4 (by rfl) ⟨87231, by rfl⟩ : syracuseStep 930469 = 174463) (by norm_num)
theorem B996025 : Blo 826349 996025 := bbase (se 2 (by rfl) ⟨373509, by rfl⟩ : syracuseStep 996025 = 747019) (by norm_num)
theorem B930505 : Blo 826349 930505 := bbase (se 2 (by rfl) ⟨348939, by rfl⟩ : syracuseStep 930505 = 697879) (by norm_num)
theorem B930541 : Blo 826349 930541 := bbase (se 3 (by rfl) ⟨174476, by rfl⟩ : syracuseStep 930541 = 348953) (by norm_num)
theorem B930577 : Blo 826349 930577 := bbase (se 2 (by rfl) ⟨348966, by rfl⟩ : syracuseStep 930577 = 697933) (by norm_num)
theorem B930613 : Blo 826349 930613 := bbase (se 5 (by rfl) ⟨43622, by rfl⟩ : syracuseStep 930613 = 87245) (by norm_num)
theorem B930649 : Blo 826349 930649 := bbase (se 2 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 930649 = 697987) (by norm_num)
theorem B930685 : Blo 826349 930685 := bbase (se 3 (by rfl) ⟨174503, by rfl⟩ : syracuseStep 930685 = 349007) (by norm_num)
theorem B930721 : Blo 826349 930721 := bbase (se 2 (by rfl) ⟨349020, by rfl⟩ : syracuseStep 930721 = 698041) (by norm_num)
theorem B1258405 : Blo 826349 1258405 := bbase (se 4 (by rfl) ⟨117975, by rfl⟩ : syracuseStep 1258405 = 235951) (by norm_num)
theorem B7943093 : Blo 826349 7943093 := bbase (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) (by norm_num)
theorem B930757 : Blo 826349 930757 := bbase (se 4 (by rfl) ⟨87258, by rfl⟩ : syracuseStep 930757 = 174517) (by norm_num)
theorem B2798549 : Blo 826349 2798549 := bbase (se 7 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 2798549 = 65591) (by norm_num)
theorem B930793 : Blo 826349 930793 := bbase (se 2 (by rfl) ⟨349047, by rfl⟩ : syracuseStep 930793 = 698095) (by norm_num)
theorem B996337 : Blo 826349 996337 := bbase (se 2 (by rfl) ⟨373626, by rfl⟩ : syracuseStep 996337 = 747253) (by norm_num)
theorem B930829 : Blo 826349 930829 := bbase (se 3 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 930829 = 349061) (by norm_num)
theorem B930865 : Blo 826349 930865 := bbase (se 2 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 930865 = 698149) (by norm_num)
theorem B930901 : Blo 826349 930901 := bbase (se 8 (by rfl) ⟨5454, by rfl⟩ : syracuseStep 930901 = 10909) (by norm_num)
theorem B930937 : Blo 826349 930937 := bbase (se 2 (by rfl) ⟨349101, by rfl⟩ : syracuseStep 930937 = 698203) (by norm_num)
theorem B930973 : Blo 826349 930973 := bbase (se 3 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 930973 = 349115) (by norm_num)
theorem B4240565 : Blo 826349 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B931009 : Blo 826349 931009 := bbase (se 2 (by rfl) ⟨349128, by rfl⟩ : syracuseStep 931009 = 698257) (by norm_num)
theorem B931045 : Blo 826349 931045 := bbase (se 4 (by rfl) ⟨87285, by rfl⟩ : syracuseStep 931045 = 174571) (by norm_num)
theorem B931081 : Blo 826349 931081 := bbase (se 2 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 931081 = 698311) (by norm_num)
theorem B931117 : Blo 826349 931117 := bbase (se 3 (by rfl) ⟨174584, by rfl⟩ : syracuseStep 931117 = 349169) (by norm_num)
theorem B931153 : Blo 826349 931153 := bbase (se 2 (by rfl) ⟨349182, by rfl⟩ : syracuseStep 931153 = 698365) (by norm_num)
theorem B931189 : Blo 826349 931189 := bbase (se 5 (by rfl) ⟨43649, by rfl⟩ : syracuseStep 931189 = 87299) (by norm_num)
theorem B2798981 : Blo 826349 2798981 := bbase (se 4 (by rfl) ⟨262404, by rfl⟩ : syracuseStep 2798981 = 524809) (by norm_num)
theorem B931225 : Blo 826349 931225 := bbase (se 2 (by rfl) ⟨349209, by rfl⟩ : syracuseStep 931225 = 698419) (by norm_num)
theorem B931261 : Blo 826349 931261 := bbase (se 3 (by rfl) ⟨174611, by rfl⟩ : syracuseStep 931261 = 349223) (by norm_num)
theorem B931297 : Blo 826349 931297 := bbase (se 2 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 931297 = 698473) (by norm_num)
theorem B931333 : Blo 826349 931333 := bbase (se 4 (by rfl) ⟨87312, by rfl⟩ : syracuseStep 931333 = 174625) (by norm_num)
theorem B931369 : Blo 826349 931369 := bbase (se 2 (by rfl) ⟨349263, by rfl⟩ : syracuseStep 931369 = 698527) (by norm_num)
theorem B931405 : Blo 826349 931405 := bbase (se 3 (by rfl) ⟨174638, by rfl⟩ : syracuseStep 931405 = 349277) (by norm_num)
theorem B931441 : Blo 826349 931441 := bbase (se 2 (by rfl) ⟨349290, by rfl⟩ : syracuseStep 931441 = 698581) (by norm_num)
theorem B1324669 : Blo 826349 1324669 := bbase (se 3 (by rfl) ⟨248375, by rfl⟩ : syracuseStep 1324669 = 496751) (by norm_num)
theorem B931477 : Blo 826349 931477 := bbase (se 6 (by rfl) ⟨21831, by rfl⟩ : syracuseStep 931477 = 43663) (by norm_num)
theorem B1259189 : Blo 826349 1259189 := bbase (se 5 (by rfl) ⟨59024, by rfl⟩ : syracuseStep 1259189 = 118049) (by norm_num)
theorem B931513 : Blo 826349 931513 := bbase (se 2 (by rfl) ⟨349317, by rfl⟩ : syracuseStep 931513 = 698635) (by norm_num)
theorem B931549 : Blo 826349 931549 := bbase (se 3 (by rfl) ⟨174665, by rfl⟩ : syracuseStep 931549 = 349331) (by norm_num)
theorem B931585 : Blo 826349 931585 := bbase (se 2 (by rfl) ⟨349344, by rfl⟩ : syracuseStep 931585 = 698689) (by norm_num)
theorem B931621 : Blo 826349 931621 := bbase (se 4 (by rfl) ⟨87339, by rfl⟩ : syracuseStep 931621 = 174679) (by norm_num)
theorem B2799413 : Blo 826349 2799413 := bbase (se 5 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 2799413 = 262445) (by norm_num)
theorem B931657 : Blo 826349 931657 := bbase (se 2 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 931657 = 698743) (by norm_num)
theorem B931693 : Blo 826349 931693 := bbase (se 3 (by rfl) ⟨174692, by rfl⟩ : syracuseStep 931693 = 349385) (by norm_num)
theorem B931729 : Blo 826349 931729 := bbase (se 2 (by rfl) ⟨349398, by rfl⟩ : syracuseStep 931729 = 698797) (by norm_num)
theorem B931765 : Blo 826349 931765 := bbase (se 5 (by rfl) ⟨43676, by rfl⟩ : syracuseStep 931765 = 87353) (by norm_num)
theorem B931801 : Blo 826349 931801 := bbase (se 2 (by rfl) ⟨349425, by rfl⟩ : syracuseStep 931801 = 698851) (by norm_num)
theorem B931837 : Blo 826349 931837 := bbase (se 3 (by rfl) ⟨174719, by rfl⟩ : syracuseStep 931837 = 349439) (by norm_num)
theorem B931873 : Blo 826349 931873 := bbase (se 2 (by rfl) ⟨349452, by rfl⟩ : syracuseStep 931873 = 698905) (by norm_num)
theorem B1325117 : Blo 826349 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B931909 : Blo 826349 931909 := bbase (se 4 (by rfl) ⟨87366, by rfl⟩ : syracuseStep 931909 = 174733) (by norm_num)
theorem B931945 : Blo 826349 931945 := bbase (se 2 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 931945 = 698959) (by norm_num)
theorem B931981 : Blo 826349 931981 := bbase (se 3 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 931981 = 349493) (by norm_num)
theorem B932017 : Blo 826349 932017 := bbase (se 2 (by rfl) ⟨349506, by rfl⟩ : syracuseStep 932017 = 699013) (by norm_num)
theorem B932053 : Blo 826349 932053 := bbase (se 7 (by rfl) ⟨10922, by rfl⟩ : syracuseStep 932053 = 21845) (by norm_num)
theorem B2799845 : Blo 826349 2799845 := bbase (se 4 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 2799845 = 524971) (by norm_num)
theorem B932089 : Blo 826349 932089 := bbase (se 2 (by rfl) ⟨349533, by rfl⟩ : syracuseStep 932089 = 699067) (by norm_num)
theorem B1325317 : Blo 826349 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B932125 : Blo 826349 932125 := bbase (se 3 (by rfl) ⟨174773, by rfl⟩ : syracuseStep 932125 = 349547) (by norm_num)
theorem B932161 : Blo 826349 932161 := bbase (se 2 (by rfl) ⟨349560, by rfl⟩ : syracuseStep 932161 = 699121) (by norm_num)
theorem B932197 : Blo 826349 932197 := bbase (se 4 (by rfl) ⟨87393, by rfl⟩ : syracuseStep 932197 = 174787) (by norm_num)
theorem B932233 : Blo 826349 932233 := bbase (se 2 (by rfl) ⟨349587, by rfl⟩ : syracuseStep 932233 = 699175) (by norm_num)
theorem B932269 : Blo 826349 932269 := bbase (se 3 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 932269 = 349601) (by norm_num)
theorem B932305 : Blo 826349 932305 := bbase (se 2 (by rfl) ⟨349614, by rfl⟩ : syracuseStep 932305 = 699229) (by norm_num)
theorem B932341 : Blo 826349 932341 := bbase (se 5 (by rfl) ⟨43703, by rfl⟩ : syracuseStep 932341 = 87407) (by norm_num)
theorem B1325573 : Blo 826349 1325573 := bbase (se 4 (by rfl) ⟨124272, by rfl⟩ : syracuseStep 1325573 = 248545) (by norm_num)
theorem B932377 : Blo 826349 932377 := bbase (se 2 (by rfl) ⟨349641, by rfl⟩ : syracuseStep 932377 = 699283) (by norm_num)
theorem B932413 : Blo 826349 932413 := bbase (se 3 (by rfl) ⟨174827, by rfl⟩ : syracuseStep 932413 = 349655) (by norm_num)
theorem B932449 : Blo 826349 932449 := bbase (se 2 (by rfl) ⟨349668, by rfl⟩ : syracuseStep 932449 = 699337) (by norm_num)
theorem B3357317 : Blo 826349 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B932485 : Blo 826349 932485 := bbase (se 4 (by rfl) ⟨87420, by rfl⟩ : syracuseStep 932485 = 174841) (by norm_num)
theorem B2800277 : Blo 826349 2800277 := bbase (se 6 (by rfl) ⟨65631, by rfl⟩ : syracuseStep 2800277 = 131263) (by norm_num)
theorem B932521 : Blo 826349 932521 := bbase (se 2 (by rfl) ⟨349695, by rfl⟩ : syracuseStep 932521 = 699391) (by norm_num)
theorem B932557 : Blo 826349 932557 := bbase (se 3 (by rfl) ⟨174854, by rfl⟩ : syracuseStep 932557 = 349709) (by norm_num)
theorem B932593 : Blo 826349 932593 := bbase (se 2 (by rfl) ⟨349722, by rfl⟩ : syracuseStep 932593 = 699445) (by norm_num)
theorem B932629 : Blo 826349 932629 := bbase (se 6 (by rfl) ⟨21858, by rfl⟩ : syracuseStep 932629 = 43717) (by norm_num)
theorem B932665 : Blo 826349 932665 := bbase (se 2 (by rfl) ⟨349749, by rfl⟩ : syracuseStep 932665 = 699499) (by norm_num)
theorem B932701 : Blo 826349 932701 := bbase (se 3 (by rfl) ⟨174881, by rfl⟩ : syracuseStep 932701 = 349763) (by norm_num)
theorem B932737 : Blo 826349 932737 := bbase (se 2 (by rfl) ⟨349776, by rfl⟩ : syracuseStep 932737 = 699553) (by norm_num)
theorem B7551893 : Blo 826349 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B1915805 : Blo 826349 1915805 := bbase (se 3 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 1915805 = 718427) (by norm_num)
theorem B932773 : Blo 826349 932773 := bbase (se 4 (by rfl) ⟨87447, by rfl⟩ : syracuseStep 932773 = 174895) (by norm_num)
theorem B7650229 : Blo 826349 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B932809 : Blo 826349 932809 := bbase (se 2 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 932809 = 699607) (by norm_num)
theorem B932845 : Blo 826349 932845 := bbase (se 3 (by rfl) ⟨174908, by rfl⟩ : syracuseStep 932845 = 349817) (by norm_num)
theorem B932881 : Blo 826349 932881 := bbase (se 2 (by rfl) ⟨349830, by rfl⟩ : syracuseStep 932881 = 699661) (by norm_num)
theorem B932917 : Blo 826349 932917 := bbase (se 5 (by rfl) ⟨43730, by rfl⟩ : syracuseStep 932917 = 87461) (by norm_num)
theorem B2800709 : Blo 826349 2800709 := bbase (se 4 (by rfl) ⟨262566, by rfl⟩ : syracuseStep 2800709 = 525133) (by norm_num)
theorem B932953 : Blo 826349 932953 := bbase (se 2 (by rfl) ⟨349857, by rfl⟩ : syracuseStep 932953 = 699715) (by norm_num)
theorem B932989 : Blo 826349 932989 := bbase (se 3 (by rfl) ⟨174935, by rfl⟩ : syracuseStep 932989 = 349871) (by norm_num)
theorem B933025 : Blo 826349 933025 := bbase (se 2 (by rfl) ⟨349884, by rfl⟩ : syracuseStep 933025 = 699769) (by norm_num)
theorem B933061 : Blo 826349 933061 := bbase (se 4 (by rfl) ⟨87474, by rfl⟩ : syracuseStep 933061 = 174949) (by norm_num)
theorem B11943125 : Blo 826349 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B933097 : Blo 826349 933097 := bbase (se 2 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 933097 = 699823) (by norm_num)
theorem B933133 : Blo 826349 933133 := bbase (se 3 (by rfl) ⟨174962, by rfl⟩ : syracuseStep 933133 = 349925) (by norm_num)
theorem B933169 : Blo 826349 933169 := bbase (se 2 (by rfl) ⟨349938, by rfl⟩ : syracuseStep 933169 = 699877) (by norm_num)
theorem B3783989 : Blo 826349 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B933205 : Blo 826349 933205 := bbase (se 11 (by rfl) ⟨683, by rfl⟩ : syracuseStep 933205 = 1367) (by norm_num)
theorem B933241 : Blo 826349 933241 := bbase (se 2 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 933241 = 699931) (by norm_num)
theorem B933277 : Blo 826349 933277 := bbase (se 3 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 933277 = 349979) (by norm_num)
theorem B933313 : Blo 826349 933313 := bbase (se 2 (by rfl) ⟨349992, by rfl⟩ : syracuseStep 933313 = 699985) (by norm_num)
theorem B933349 : Blo 826349 933349 := bbase (se 4 (by rfl) ⟨87501, by rfl⟩ : syracuseStep 933349 = 175003) (by norm_num)
theorem B2801141 : Blo 826349 2801141 := bbase (se 5 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 2801141 = 262607) (by norm_num)
theorem B933385 : Blo 826349 933385 := bbase (se 2 (by rfl) ⟨350019, by rfl⟩ : syracuseStep 933385 = 700039) (by norm_num)
theorem B933421 : Blo 826349 933421 := bbase (se 3 (by rfl) ⟨175016, by rfl⟩ : syracuseStep 933421 = 350033) (by norm_num)
theorem B933457 : Blo 826349 933457 := bbase (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) (by norm_num)
theorem B2244181 : Blo 826349 2244181 := bbase (se 8 (by rfl) ⟨13149, by rfl⟩ : syracuseStep 2244181 = 26299) (by norm_num)
theorem B1064545 : Blo 826349 1064545 := bbase (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) (by norm_num)
theorem B1326701 : Blo 826349 1326701 := bbase (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) (by norm_num)
theorem B933493 : Blo 826349 933493 := bbase (se 5 (by rfl) ⟨43757, by rfl⟩ : syracuseStep 933493 = 87515) (by norm_num)
theorem B933529 : Blo 826349 933529 := bbase (se 2 (by rfl) ⟨350073, by rfl⟩ : syracuseStep 933529 = 700147) (by norm_num)
theorem B933565 : Blo 826349 933565 := bbase (se 3 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 933565 = 350087) (by norm_num)
theorem B933601 : Blo 826349 933601 := bbase (se 2 (by rfl) ⟨350100, by rfl⟩ : syracuseStep 933601 = 700201) (by norm_num)
theorem B933637 : Blo 826349 933637 := bbase (se 4 (by rfl) ⟨87528, by rfl⟩ : syracuseStep 933637 = 175057) (by norm_num)
theorem B933673 : Blo 826349 933673 := bbase (se 2 (by rfl) ⟨350127, by rfl⟩ : syracuseStep 933673 = 700255) (by norm_num)
theorem B933709 : Blo 826349 933709 := bbase (se 3 (by rfl) ⟨175070, by rfl⟩ : syracuseStep 933709 = 350141) (by norm_num)
theorem B933745 : Blo 826349 933745 := bbase (se 2 (by rfl) ⟨350154, by rfl⟩ : syracuseStep 933745 = 700309) (by norm_num)
theorem B933781 : Blo 826349 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B2801573 : Blo 826349 2801573 := bbase (se 4 (by rfl) ⟨262647, by rfl⟩ : syracuseStep 2801573 = 525295) (by norm_num)
theorem B933817 : Blo 826349 933817 := bbase (se 2 (by rfl) ⟨350181, by rfl⟩ : syracuseStep 933817 = 700363) (by norm_num)
theorem B933853 : Blo 826349 933853 := bbase (se 3 (by rfl) ⟨175097, by rfl⟩ : syracuseStep 933853 = 350195) (by norm_num)
theorem B933889 : Blo 826349 933889 := bbase (se 2 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 933889 = 700417) (by norm_num)
theorem B933925 : Blo 826349 933925 := bbase (se 4 (by rfl) ⟨87555, by rfl⟩ : syracuseStep 933925 = 175111) (by norm_num)
theorem B933961 : Blo 826349 933961 := bbase (se 2 (by rfl) ⟨350235, by rfl⟩ : syracuseStep 933961 = 700471) (by norm_num)
theorem B1327213 : Blo 826349 1327213 := bbase (se 3 (by rfl) ⟨248852, by rfl⟩ : syracuseStep 1327213 = 497705) (by norm_num)
theorem B933997 : Blo 826349 933997 := bbase (se 3 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 933997 = 350249) (by norm_num)
theorem B934033 : Blo 826349 934033 := bbase (se 2 (by rfl) ⟨350262, by rfl⟩ : syracuseStep 934033 = 700525) (by norm_num)
theorem B934069 : Blo 826349 934069 := bbase (se 5 (by rfl) ⟨43784, by rfl⟩ : syracuseStep 934069 = 87569) (by norm_num)
theorem B934105 : Blo 826349 934105 := bbase (se 2 (by rfl) ⟨350289, by rfl⟩ : syracuseStep 934105 = 700579) (by norm_num)
theorem B934141 : Blo 826349 934141 := bbase (se 3 (by rfl) ⟨175151, by rfl⟩ : syracuseStep 934141 = 350303) (by norm_num)
theorem B1818949 : Blo 826349 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B13648213 : Blo 826349 13648213 := bbase (se 10 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 13648213 = 39985) (by norm_num)
theorem B2802005 : Blo 826349 2802005 := bbase (se 10 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 2802005 = 8209) (by norm_num)
theorem B1360469 : Blo 826349 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B1327757 : Blo 826349 1327757 := bbase (se 3 (by rfl) ⟨248954, by rfl⟩ : syracuseStep 1327757 = 497909) (by norm_num)
theorem B1884845 : Blo 826349 1884845 := bbase (se 3 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 1884845 = 706817) (by norm_num)
theorem B1491637 : Blo 826349 1491637 := bbase (se 5 (by rfl) ⟨69920, by rfl⟩ : syracuseStep 1491637 = 139841) (by norm_num)
theorem B3982117 : Blo 826349 3982117 := bbase (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) (by norm_num)
theorem B1491853 : Blo 826349 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B1328309 : Blo 826349 1328309 := bbase (se 5 (by rfl) ⟨62264, by rfl⟩ : syracuseStep 1328309 = 124529) (by norm_num)
theorem B1328341 : Blo 826349 1328341 := bbase (se 7 (by rfl) ⟨15566, by rfl⟩ : syracuseStep 1328341 = 31133) (by norm_num)
theorem B1361485 : Blo 826349 1361485 := bbase (se 3 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 1361485 = 510557) (by norm_num)
theorem B3884645 : Blo 826349 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B1492661 : Blo 826349 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B14141141 : Blo 826349 14141141 := bbase (se 7 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 14141141 = 331433) (by norm_num)
theorem B5981941 : Blo 826349 5981941 := bbase (se 5 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 5981941 = 560807) (by norm_num)
theorem B1492805 : Blo 826349 1492805 := bbase (se 4 (by rfl) ⟨139950, by rfl⟩ : syracuseStep 1492805 = 279901) (by norm_num)
theorem B1394509 : Blo 826349 1394509 := bbase (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) (by norm_num)
theorem B1394597 : Blo 826349 1394597 := bbase (se 4 (by rfl) ⟨130743, by rfl⟩ : syracuseStep 1394597 = 261487) (by norm_num)
theorem B1493021 : Blo 826349 1493021 := bbase (se 3 (by rfl) ⟨279941, by rfl⟩ : syracuseStep 1493021 = 559883) (by norm_num)
theorem B1394725 : Blo 826349 1394725 := bbase (se 4 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 1394725 = 261511) (by norm_num)
theorem B1329269 : Blo 826349 1329269 := bbase (se 5 (by rfl) ⟨62309, by rfl⟩ : syracuseStep 1329269 = 124619) (by norm_num)
theorem B1394813 : Blo 826349 1394813 := bbase (se 3 (by rfl) ⟨261527, by rfl⟩ : syracuseStep 1394813 = 523055) (by norm_num)
theorem B2017445 : Blo 826349 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B837805 : Blo 826349 837805 := bbase (se 3 (by rfl) ⟨157088, by rfl⟩ : syracuseStep 837805 = 314177) (by norm_num)
theorem B1591501 : Blo 826349 1591501 := bbase (se 3 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 1591501 = 596813) (by norm_num)
theorem B1394941 : Blo 826349 1394941 := bbase (se 3 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 1394941 = 523103) (by norm_num)
theorem B1395029 : Blo 826349 1395029 := bbase (se 10 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 1395029 = 4087) (by norm_num)
theorem B1395157 : Blo 826349 1395157 := bbase (se 7 (by rfl) ⟨16349, by rfl⟩ : syracuseStep 1395157 = 32699) (by norm_num)
theorem B1493525 : Blo 826349 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B1395245 : Blo 826349 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B1395373 : Blo 826349 1395373 := bbase (se 3 (by rfl) ⟨261632, by rfl⟩ : syracuseStep 1395373 = 523265) (by norm_num)
theorem B1395461 : Blo 826349 1395461 := bbase (se 4 (by rfl) ⟨130824, by rfl⟩ : syracuseStep 1395461 = 261649) (by norm_num)
theorem B1329949 : Blo 826349 1329949 := bbase (se 3 (by rfl) ⟨249365, by rfl⟩ : syracuseStep 1329949 = 498731) (by norm_num)
theorem B5294933 : Blo 826349 5294933 := bbase (se 9 (by rfl) ⟨15512, by rfl⟩ : syracuseStep 5294933 = 31025) (by norm_num)
theorem B1330013 : Blo 826349 1330013 := bbase (se 3 (by rfl) ⟨249377, by rfl⟩ : syracuseStep 1330013 = 498755) (by norm_num)
theorem B1395589 : Blo 826349 1395589 := bbase (se 4 (by rfl) ⟨130836, by rfl⟩ : syracuseStep 1395589 = 261673) (by norm_num)
theorem B1985485 : Blo 826349 1985485 := bbase (se 3 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 1985485 = 744557) (by norm_num)
theorem B1395677 : Blo 826349 1395677 := bbase (se 3 (by rfl) ⟨261689, by rfl⟩ : syracuseStep 1395677 = 523379) (by norm_num)
theorem B1395805 : Blo 826349 1395805 := bbase (se 3 (by rfl) ⟨261713, by rfl⟩ : syracuseStep 1395805 = 523427) (by norm_num)
theorem B3361925 : Blo 826349 3361925 := bbase (se 4 (by rfl) ⟨315180, by rfl⟩ : syracuseStep 3361925 = 630361) (by norm_num)
theorem B1395893 : Blo 826349 1395893 := bbase (se 5 (by rfl) ⟨65432, by rfl⟩ : syracuseStep 1395893 = 130865) (by norm_num)
theorem B1396021 : Blo 826349 1396021 := bbase (se 5 (by rfl) ⟨65438, by rfl⟩ : syracuseStep 1396021 = 130877) (by norm_num)
theorem B839005 : Blo 826349 839005 := bbase (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) (by norm_num)
theorem B1396109 : Blo 826349 1396109 := bbase (se 3 (by rfl) ⟨261770, by rfl⟩ : syracuseStep 1396109 = 523541) (by norm_num)
theorem B1396237 : Blo 826349 1396237 := bbase (se 3 (by rfl) ⟨261794, by rfl⟩ : syracuseStep 1396237 = 523589) (by norm_num)
theorem B1887781 : Blo 826349 1887781 := bbase (se 4 (by rfl) ⟨176979, by rfl⟩ : syracuseStep 1887781 = 353959) (by norm_num)
theorem B1396325 : Blo 826349 1396325 := bbase (se 4 (by rfl) ⟨130905, by rfl⟩ : syracuseStep 1396325 = 261811) (by norm_num)
theorem B1396453 : Blo 826349 1396453 := bbase (se 4 (by rfl) ⟨130917, by rfl⟩ : syracuseStep 1396453 = 261835) (by norm_num)
theorem B1396541 : Blo 826349 1396541 := bbase (se 3 (by rfl) ⟨261851, by rfl⟩ : syracuseStep 1396541 = 523703) (by norm_num)
theorem B839533 : Blo 826349 839533 := bbase (se 3 (by rfl) ⟨157412, by rfl⟩ : syracuseStep 839533 = 314825) (by norm_num)
theorem B1789885 : Blo 826349 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B1396669 : Blo 826349 1396669 := bbase (se 3 (by rfl) ⟨261875, by rfl⟩ : syracuseStep 1396669 = 523751) (by norm_num)
theorem B1396757 : Blo 826349 1396757 := bbase (se 6 (by rfl) ⟨32736, by rfl⟩ : syracuseStep 1396757 = 65473) (by norm_num)
theorem B1986677 : Blo 826349 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B1396885 : Blo 826349 1396885 := bbase (se 6 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 1396885 = 65479) (by norm_num)
theorem B1396973 : Blo 826349 1396973 := bbase (se 3 (by rfl) ⟨261932, by rfl⟩ : syracuseStep 1396973 = 523865) (by norm_num)
theorem B1986869 : Blo 826349 1986869 := bbase (se 5 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 1986869 = 186269) (by norm_num)
theorem B1397101 : Blo 826349 1397101 := bbase (se 3 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 1397101 = 523913) (by norm_num)
theorem B1888637 : Blo 826349 1888637 := bbase (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) (by norm_num)
theorem B6279605 : Blo 826349 6279605 := bbase (se 5 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 6279605 = 588713) (by norm_num)
theorem B1397189 : Blo 826349 1397189 := bbase (se 4 (by rfl) ⟨130986, by rfl⟩ : syracuseStep 1397189 = 261973) (by norm_num)
theorem B1397317 : Blo 826349 1397317 := bbase (se 4 (by rfl) ⟨130998, by rfl⟩ : syracuseStep 1397317 = 261997) (by norm_num)
theorem B1397405 : Blo 826349 1397405 := bbase (se 3 (by rfl) ⟨262013, by rfl⟩ : syracuseStep 1397405 = 524027) (by norm_num)
theorem B3986117 : Blo 826349 3986117 := bbase (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) (by norm_num)
theorem B840449 : Blo 826349 840449 := bbase (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) (by norm_num)
theorem B1397533 : Blo 826349 1397533 := bbase (se 3 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 1397533 = 524075) (by norm_num)
theorem B840497 : Blo 826349 840497 := bbase (se 2 (by rfl) ⟨315186, by rfl⟩ : syracuseStep 840497 = 630373) (by norm_num)
theorem B1397621 : Blo 826349 1397621 := bbase (se 5 (by rfl) ⟨65513, by rfl⟩ : syracuseStep 1397621 = 131027) (by norm_num)
theorem B3986309 : Blo 826349 3986309 := bbase (se 4 (by rfl) ⟨373716, by rfl⟩ : syracuseStep 3986309 = 747433) (by norm_num)
theorem B1397749 : Blo 826349 1397749 := bbase (se 5 (by rfl) ⟨65519, by rfl⟩ : syracuseStep 1397749 = 131039) (by norm_num)
theorem B1397837 : Blo 826349 1397837 := bbase (se 3 (by rfl) ⟨262094, by rfl⟩ : syracuseStep 1397837 = 524189) (by norm_num)
theorem B10605653 : Blo 826349 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B1397965 : Blo 826349 1397965 := bbase (se 3 (by rfl) ⟨262118, by rfl⟩ : syracuseStep 1397965 = 524237) (by norm_num)
theorem B1398053 : Blo 826349 1398053 := bbase (se 4 (by rfl) ⟨131067, by rfl⟩ : syracuseStep 1398053 = 262135) (by norm_num)
theorem B7853429 : Blo 826349 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B1398181 : Blo 826349 1398181 := bbase (se 4 (by rfl) ⟨131079, by rfl⟩ : syracuseStep 1398181 = 262159) (by norm_num)
theorem B2840021 : Blo 826349 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B3364325 : Blo 826349 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B1398269 : Blo 826349 1398269 := bbase (se 3 (by rfl) ⟨262175, by rfl⟩ : syracuseStep 1398269 = 524351) (by norm_num)
theorem B1398397 : Blo 826349 1398397 := bbase (se 3 (by rfl) ⟨262199, by rfl⟩ : syracuseStep 1398397 = 524399) (by norm_num)
theorem B1398485 : Blo 826349 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1398613 : Blo 826349 1398613 := bbase (se 9 (by rfl) ⟨4097, by rfl⟩ : syracuseStep 1398613 = 8195) (by norm_num)
theorem B4183973 : Blo 826349 4183973 := bbase (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) (by norm_num)
theorem B1398701 : Blo 826349 1398701 := bbase (se 3 (by rfl) ⟨262256, by rfl⟩ : syracuseStep 1398701 = 524513) (by norm_num)
theorem B1890317 : Blo 826349 1890317 := bbase (se 3 (by rfl) ⟨354434, by rfl⟩ : syracuseStep 1890317 = 708869) (by norm_num)
theorem B1398829 : Blo 826349 1398829 := bbase (se 3 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 1398829 = 524561) (by norm_num)
theorem B1398917 : Blo 826349 1398917 := bbase (se 4 (by rfl) ⟨131148, by rfl⟩ : syracuseStep 1398917 = 262297) (by norm_num)
theorem B1399045 : Blo 826349 1399045 := bbase (se 4 (by rfl) ⟨131160, by rfl⟩ : syracuseStep 1399045 = 262321) (by norm_num)
theorem B1399133 : Blo 826349 1399133 := bbase (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) (by norm_num)
theorem B2513317 : Blo 826349 2513317 := bbase (se 4 (by rfl) ⟨235623, by rfl⟩ : syracuseStep 2513317 = 471247) (by norm_num)
theorem B1399261 : Blo 826349 1399261 := bbase (se 3 (by rfl) ⟨262361, by rfl⟩ : syracuseStep 1399261 = 524723) (by norm_num)
theorem B1366541 : Blo 826349 1366541 := bbase (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) (by norm_num)
theorem B1989157 : Blo 826349 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B1399349 : Blo 826349 1399349 := bbase (se 5 (by rfl) ⟨65594, by rfl⟩ : syracuseStep 1399349 = 131189) (by norm_num)
theorem B2120357 : Blo 826349 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B1399477 : Blo 826349 1399477 := bbase (se 5 (by rfl) ⟨65600, by rfl⟩ : syracuseStep 1399477 = 131201) (by norm_num)
theorem B3365621 : Blo 826349 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B1399565 : Blo 826349 1399565 := bbase (se 3 (by rfl) ⟨262418, by rfl⟩ : syracuseStep 1399565 = 524837) (by norm_num)
theorem B3824501 : Blo 826349 3824501 := bbase (se 5 (by rfl) ⟨179273, by rfl⟩ : syracuseStep 3824501 = 358547) (by norm_num)
theorem B2120573 : Blo 826349 2120573 := bbase (se 3 (by rfl) ⟨397607, by rfl⟩ : syracuseStep 2120573 = 795215) (by norm_num)
theorem B1399693 : Blo 826349 1399693 := bbase (se 3 (by rfl) ⟨262442, by rfl⟩ : syracuseStep 1399693 = 524885) (by norm_num)
theorem B1596341 : Blo 826349 1596341 := bbase (se 5 (by rfl) ⟨74828, by rfl⟩ : syracuseStep 1596341 = 149657) (by norm_num)
theorem B1399781 : Blo 826349 1399781 := bbase (se 4 (by rfl) ⟨131229, by rfl⟩ : syracuseStep 1399781 = 262459) (by norm_num)
theorem B1399909 : Blo 826349 1399909 := bbase (se 4 (by rfl) ⟨131241, by rfl⟩ : syracuseStep 1399909 = 262483) (by norm_num)
theorem B4185269 : Blo 826349 4185269 := bbase (se 5 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 4185269 = 392369) (by norm_num)
theorem B1989821 : Blo 826349 1989821 := bbase (se 3 (by rfl) ⟨373091, by rfl⟩ : syracuseStep 1989821 = 746183) (by norm_num)
theorem B1399997 : Blo 826349 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1400125 : Blo 826349 1400125 := bbase (se 3 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 1400125 = 525047) (by norm_num)
theorem B1400213 : Blo 826349 1400213 := bbase (se 6 (by rfl) ⟨32817, by rfl⟩ : syracuseStep 1400213 = 65635) (by norm_num)
theorem B3530213 : Blo 826349 3530213 := bbase (se 4 (by rfl) ⟨330957, by rfl⟩ : syracuseStep 3530213 = 661915) (by norm_num)
theorem B1400341 : Blo 826349 1400341 := bbase (se 6 (by rfl) ⟨32820, by rfl⟩ : syracuseStep 1400341 = 65641) (by norm_num)
theorem B2514485 : Blo 826349 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B1007165 : Blo 826349 1007165 := bbase (se 3 (by rfl) ⟨188843, by rfl⟩ : syracuseStep 1007165 = 377687) (by norm_num)
theorem B1400429 : Blo 826349 1400429 := bbase (se 3 (by rfl) ⟨262580, by rfl⟩ : syracuseStep 1400429 = 525161) (by norm_num)
theorem B1793701 : Blo 826349 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B1859309 : Blo 826349 1859309 := bbase (se 3 (by rfl) ⟨348620, by rfl⟩ : syracuseStep 1859309 = 697241) (by norm_num)
theorem B1400557 : Blo 826349 1400557 := bbase (se 3 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 1400557 = 525209) (by norm_num)
theorem B1859381 : Blo 826349 1859381 := bbase (se 5 (by rfl) ⟨87158, by rfl⟩ : syracuseStep 1859381 = 174317) (by norm_num)
theorem B1400645 : Blo 826349 1400645 := bbase (se 4 (by rfl) ⟨131310, by rfl⟩ : syracuseStep 1400645 = 262621) (by norm_num)
theorem B2121557 : Blo 826349 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B8085365 : Blo 826349 8085365 := bbase (se 5 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 8085365 = 758003) (by norm_num)
theorem B1859453 : Blo 826349 1859453 := bbase (se 3 (by rfl) ⟨348647, by rfl⟩ : syracuseStep 1859453 = 697295) (by norm_num)
theorem B9428885 : Blo 826349 9428885 := bbase (se 6 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 9428885 = 441979) (by norm_num)
theorem B1859525 : Blo 826349 1859525 := bbase (se 4 (by rfl) ⟨174330, by rfl⟩ : syracuseStep 1859525 = 348661) (by norm_num)
theorem B1400773 : Blo 826349 1400773 := bbase (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) (by norm_num)
theorem B1859597 : Blo 826349 1859597 := bbase (se 3 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 1859597 = 697349) (by norm_num)
theorem B1400861 : Blo 826349 1400861 := bbase (se 3 (by rfl) ⟨262661, by rfl⟩ : syracuseStep 1400861 = 525323) (by norm_num)
theorem B1859669 : Blo 826349 1859669 := bbase (se 8 (by rfl) ⟨10896, by rfl⟩ : syracuseStep 1859669 = 21793) (by norm_num)
theorem B1597573 : Blo 826349 1597573 := bbase (se 4 (by rfl) ⟨149772, by rfl⟩ : syracuseStep 1597573 = 299545) (by norm_num)
theorem B1859741 : Blo 826349 1859741 := bbase (se 3 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 1859741 = 697403) (by norm_num)
theorem B1400989 : Blo 826349 1400989 := bbase (se 3 (by rfl) ⟨262685, by rfl⟩ : syracuseStep 1400989 = 525371) (by norm_num)
theorem B1859813 : Blo 826349 1859813 := bbase (se 4 (by rfl) ⟨174357, by rfl⟩ : syracuseStep 1859813 = 348715) (by norm_num)
theorem B1401077 : Blo 826349 1401077 := bbase (se 5 (by rfl) ⟨65675, by rfl⟩ : syracuseStep 1401077 = 131351) (by norm_num)
theorem B1859885 : Blo 826349 1859885 := bbase (se 3 (by rfl) ⟨348728, by rfl⟩ : syracuseStep 1859885 = 697457) (by norm_num)
theorem B1859957 : Blo 826349 1859957 := bbase (se 5 (by rfl) ⟨87185, by rfl⟩ : syracuseStep 1859957 = 174371) (by norm_num)
theorem B1401205 : Blo 826349 1401205 := bbase (se 5 (by rfl) ⟨65681, by rfl⟩ : syracuseStep 1401205 = 131363) (by norm_num)
theorem B1860029 : Blo 826349 1860029 := bbase (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) (by norm_num)
theorem B4186565 : Blo 826349 4186565 := bbase (se 4 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 4186565 = 784981) (by norm_num)
theorem B3531221 : Blo 826349 3531221 := bbase (se 7 (by rfl) ⟨41381, by rfl⟩ : syracuseStep 3531221 = 82763) (by norm_num)
theorem B1860101 : Blo 826349 1860101 := bbase (se 4 (by rfl) ⟨174384, by rfl⟩ : syracuseStep 1860101 = 348769) (by norm_num)
theorem B13591061 : Blo 826349 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B1991213 : Blo 826349 1991213 := bbase (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) (by norm_num)
theorem B1860173 : Blo 826349 1860173 := bbase (se 3 (by rfl) ⟨348782, by rfl⟩ : syracuseStep 1860173 = 697565) (by norm_num)
theorem B942673 : Blo 826349 942673 := bbase (se 2 (by rfl) ⟨353502, by rfl⟩ : syracuseStep 942673 = 707005) (by norm_num)
theorem B1991309 : Blo 826349 1991309 := bbase (se 3 (by rfl) ⟨373370, by rfl⟩ : syracuseStep 1991309 = 746741) (by norm_num)
theorem B1860245 : Blo 826349 1860245 := bbase (se 6 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 1860245 = 87199) (by norm_num)
theorem B15131285 : Blo 826349 15131285 := bbase (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) (by norm_num)
theorem B1860317 : Blo 826349 1860317 := bbase (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) (by norm_num)
theorem B1008373 : Blo 826349 1008373 := bbase (se 5 (by rfl) ⟨47267, by rfl⟩ : syracuseStep 1008373 = 94535) (by norm_num)
theorem B1860389 : Blo 826349 1860389 := bbase (se 4 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 1860389 = 348823) (by norm_num)
theorem B1860461 : Blo 826349 1860461 := bbase (se 3 (by rfl) ⟨348836, by rfl⟩ : syracuseStep 1860461 = 697673) (by norm_num)
theorem B1860533 : Blo 826349 1860533 := bbase (se 5 (by rfl) ⟨87212, by rfl⟩ : syracuseStep 1860533 = 174425) (by norm_num)
theorem B22668245 : Blo 826349 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B1860605 : Blo 826349 1860605 := bbase (se 3 (by rfl) ⟨348863, by rfl⟩ : syracuseStep 1860605 = 697727) (by norm_num)
theorem B1860677 : Blo 826349 1860677 := bbase (se 4 (by rfl) ⟨174438, by rfl⟩ : syracuseStep 1860677 = 348877) (by norm_num)
theorem B1860749 : Blo 826349 1860749 := bbase (se 3 (by rfl) ⟨348890, by rfl⟩ : syracuseStep 1860749 = 697781) (by norm_num)
theorem B3138709 : Blo 826349 3138709 := bbase (se 6 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 3138709 = 147127) (by norm_num)
theorem B1860821 : Blo 826349 1860821 := bbase (se 7 (by rfl) ⟨21806, by rfl⟩ : syracuseStep 1860821 = 43613) (by norm_num)
theorem B1860893 : Blo 826349 1860893 := bbase (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) (by norm_num)
theorem B12739925 : Blo 826349 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B1860965 : Blo 826349 1860965 := bbase (se 4 (by rfl) ⟨174465, by rfl⟩ : syracuseStep 1860965 = 348931) (by norm_num)
theorem B1861037 : Blo 826349 1861037 := bbase (se 3 (by rfl) ⟨348944, by rfl⟩ : syracuseStep 1861037 = 697889) (by norm_num)
theorem B3139013 : Blo 826349 3139013 := bbase (se 4 (by rfl) ⟨294282, by rfl⟩ : syracuseStep 3139013 = 588565) (by norm_num)
theorem B3401189 : Blo 826349 3401189 := bbase (se 4 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 3401189 = 637723) (by norm_num)
theorem B1861109 : Blo 826349 1861109 := bbase (se 5 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 1861109 = 174479) (by norm_num)
theorem B6809141 : Blo 826349 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B1861181 : Blo 826349 1861181 := bbase (se 3 (by rfl) ⟨348971, by rfl⟩ : syracuseStep 1861181 = 697943) (by norm_num)
theorem B15754837 : Blo 826349 15754837 := bbase (se 8 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 15754837 = 184627) (by norm_num)
theorem B1861253 : Blo 826349 1861253 := bbase (se 4 (by rfl) ⟨174492, by rfl⟩ : syracuseStep 1861253 = 348985) (by norm_num)
theorem B1861325 : Blo 826349 1861325 := bbase (se 3 (by rfl) ⟨348998, by rfl⟩ : syracuseStep 1861325 = 697997) (by norm_num)
theorem B4187861 : Blo 826349 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B1861397 : Blo 826349 1861397 := bbase (se 6 (by rfl) ⟨43626, by rfl⟩ : syracuseStep 1861397 = 87253) (by norm_num)
theorem B1861469 : Blo 826349 1861469 := bbase (se 3 (by rfl) ⟨349025, by rfl⟩ : syracuseStep 1861469 = 698051) (by norm_num)
theorem B1861541 : Blo 826349 1861541 := bbase (se 4 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 1861541 = 349039) (by norm_num)
theorem B1861613 : Blo 826349 1861613 := bbase (se 3 (by rfl) ⟨349052, by rfl⟩ : syracuseStep 1861613 = 698105) (by norm_num)
theorem B1861685 : Blo 826349 1861685 := bbase (se 5 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 1861685 = 174533) (by norm_num)
theorem B1861757 : Blo 826349 1861757 := bbase (se 3 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 1861757 = 698159) (by norm_num)
theorem B2353349 : Blo 826349 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B3532997 : Blo 826349 3532997 := bbase (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) (by norm_num)
theorem B1861829 : Blo 826349 1861829 := bbase (se 4 (by rfl) ⟨174546, by rfl⟩ : syracuseStep 1861829 = 349093) (by norm_num)
theorem B1009873 : Blo 826349 1009873 := bbase (se 2 (by rfl) ⟨378702, by rfl⟩ : syracuseStep 1009873 = 757405) (by norm_num)
theorem B944365 : Blo 826349 944365 := bbase (se 3 (by rfl) ⟨177068, by rfl⟩ : syracuseStep 944365 = 354137) (by norm_num)
theorem B1861901 : Blo 826349 1861901 := bbase (se 3 (by rfl) ⟨349106, by rfl⟩ : syracuseStep 1861901 = 698213) (by norm_num)
theorem B2648389 : Blo 826349 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B944465 : Blo 826349 944465 := bbase (se 2 (by rfl) ⟨354174, by rfl⟩ : syracuseStep 944465 = 708349) (by norm_num)
theorem B1861973 : Blo 826349 1861973 := bbase (se 10 (by rfl) ⟨2727, by rfl⟩ : syracuseStep 1861973 = 5455) (by norm_num)
theorem B1862045 : Blo 826349 1862045 := bbase (se 3 (by rfl) ⟨349133, by rfl⟩ : syracuseStep 1862045 = 698267) (by norm_num)
theorem B1862117 : Blo 826349 1862117 := bbase (se 4 (by rfl) ⟨174573, by rfl⟩ : syracuseStep 1862117 = 349147) (by norm_num)
theorem B1239533 : Blo 826349 1239533 := bbase (se 3 (by rfl) ⟨232412, by rfl⟩ : syracuseStep 1239533 = 464825) (by norm_num)
theorem B1010161 : Blo 826349 1010161 := bbase (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) (by norm_num)
theorem B1239557 : Blo 826349 1239557 := bbase (se 4 (by rfl) ⟨116208, by rfl⟩ : syracuseStep 1239557 = 232417) (by norm_num)
theorem B1239581 : Blo 826349 1239581 := bbase (se 3 (by rfl) ⟨232421, by rfl⟩ : syracuseStep 1239581 = 464843) (by norm_num)
theorem B1862189 : Blo 826349 1862189 := bbase (se 3 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 1862189 = 698321) (by norm_num)
theorem B1239605 : Blo 826349 1239605 := bbase (se 5 (by rfl) ⟨58106, by rfl⟩ : syracuseStep 1239605 = 116213) (by norm_num)
theorem B1239629 : Blo 826349 1239629 := bbase (se 3 (by rfl) ⟨232430, by rfl⟩ : syracuseStep 1239629 = 464861) (by norm_num)
theorem B1239653 : Blo 826349 1239653 := bbase (se 4 (by rfl) ⟨116217, by rfl⟩ : syracuseStep 1239653 = 232435) (by norm_num)
theorem B1862261 : Blo 826349 1862261 := bbase (se 5 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 1862261 = 174587) (by norm_num)
theorem B1239677 : Blo 826349 1239677 := bbase (se 3 (by rfl) ⟨232439, by rfl⟩ : syracuseStep 1239677 = 464879) (by norm_num)
theorem B1239701 : Blo 826349 1239701 := bbase (se 6 (by rfl) ⟨29055, by rfl⟩ : syracuseStep 1239701 = 58111) (by norm_num)
theorem B1239725 : Blo 826349 1239725 := bbase (se 3 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 1239725 = 464897) (by norm_num)
theorem B1862333 : Blo 826349 1862333 := bbase (se 3 (by rfl) ⟨349187, by rfl⟩ : syracuseStep 1862333 = 698375) (by norm_num)
theorem B1993405 : Blo 826349 1993405 := bbase (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) (by norm_num)
theorem B1239749 : Blo 826349 1239749 := bbase (se 4 (by rfl) ⟨116226, by rfl⟩ : syracuseStep 1239749 = 232453) (by norm_num)
theorem B1239773 : Blo 826349 1239773 := bbase (se 3 (by rfl) ⟨232457, by rfl⟩ : syracuseStep 1239773 = 464915) (by norm_num)
theorem B1239797 : Blo 826349 1239797 := bbase (se 5 (by rfl) ⟨58115, by rfl⟩ : syracuseStep 1239797 = 116231) (by norm_num)
theorem B1862405 : Blo 826349 1862405 := bbase (se 4 (by rfl) ⟨174600, by rfl⟩ : syracuseStep 1862405 = 349201) (by norm_num)
theorem B1239821 : Blo 826349 1239821 := bbase (se 3 (by rfl) ⟨232466, by rfl⟩ : syracuseStep 1239821 = 464933) (by norm_num)
theorem B1239845 : Blo 826349 1239845 := bbase (se 4 (by rfl) ⟨116235, by rfl⟩ : syracuseStep 1239845 = 232471) (by norm_num)
theorem B1239869 : Blo 826349 1239869 := bbase (se 3 (by rfl) ⟨232475, by rfl⟩ : syracuseStep 1239869 = 464951) (by norm_num)
theorem B2091845 : Blo 826349 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B1862477 : Blo 826349 1862477 := bbase (se 3 (by rfl) ⟨349214, by rfl⟩ : syracuseStep 1862477 = 698429) (by norm_num)
theorem B1239893 : Blo 826349 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B1239917 : Blo 826349 1239917 := bbase (se 3 (by rfl) ⟨232484, by rfl⟩ : syracuseStep 1239917 = 464969) (by norm_num)
theorem B1239941 : Blo 826349 1239941 := bbase (se 4 (by rfl) ⟨116244, by rfl⟩ : syracuseStep 1239941 = 232489) (by norm_num)
theorem B1862549 : Blo 826349 1862549 := bbase (se 6 (by rfl) ⟨43653, by rfl⟩ : syracuseStep 1862549 = 87307) (by norm_num)
theorem B1239965 : Blo 826349 1239965 := bbase (se 3 (by rfl) ⟨232493, by rfl⟩ : syracuseStep 1239965 = 464987) (by norm_num)
theorem B1239989 : Blo 826349 1239989 := bbase (se 5 (by rfl) ⟨58124, by rfl⟩ : syracuseStep 1239989 = 116249) (by norm_num)
theorem B1240013 : Blo 826349 1240013 := bbase (se 3 (by rfl) ⟨232502, by rfl⟩ : syracuseStep 1240013 = 465005) (by norm_num)
theorem B1862621 : Blo 826349 1862621 := bbase (se 3 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 1862621 = 698483) (by norm_num)
theorem B1240037 : Blo 826349 1240037 := bbase (se 4 (by rfl) ⟨116253, by rfl⟩ : syracuseStep 1240037 = 232507) (by norm_num)
theorem B4189157 : Blo 826349 4189157 := bbase (se 4 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 4189157 = 785467) (by norm_num)
theorem B1240061 : Blo 826349 1240061 := bbase (se 3 (by rfl) ⟨232511, by rfl⟩ : syracuseStep 1240061 = 465023) (by norm_num)
theorem B1240085 : Blo 826349 1240085 := bbase (se 6 (by rfl) ⟨29064, by rfl⟩ : syracuseStep 1240085 = 58129) (by norm_num)
theorem B1862693 : Blo 826349 1862693 := bbase (se 4 (by rfl) ⟨174627, by rfl⟩ : syracuseStep 1862693 = 349255) (by norm_num)
theorem B1240109 : Blo 826349 1240109 := bbase (se 3 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 1240109 = 465041) (by norm_num)
theorem B1240133 : Blo 826349 1240133 := bbase (se 4 (by rfl) ⟨116262, by rfl⟩ : syracuseStep 1240133 = 232525) (by norm_num)
theorem B1240157 : Blo 826349 1240157 := bbase (se 3 (by rfl) ⟨232529, by rfl⟩ : syracuseStep 1240157 = 465059) (by norm_num)
theorem B1862765 : Blo 826349 1862765 := bbase (se 3 (by rfl) ⟨349268, by rfl⟩ : syracuseStep 1862765 = 698537) (by norm_num)
theorem B1240181 : Blo 826349 1240181 := bbase (se 5 (by rfl) ⟨58133, by rfl⟩ : syracuseStep 1240181 = 116267) (by norm_num)
theorem B1240205 : Blo 826349 1240205 := bbase (se 3 (by rfl) ⟨232538, by rfl⟩ : syracuseStep 1240205 = 465077) (by norm_num)
theorem B2092189 : Blo 826349 2092189 := bbase (se 3 (by rfl) ⟨392285, by rfl⟩ : syracuseStep 2092189 = 784571) (by norm_num)
theorem B1240229 : Blo 826349 1240229 := bbase (se 4 (by rfl) ⟨116271, by rfl⟩ : syracuseStep 1240229 = 232543) (by norm_num)
theorem B1862837 : Blo 826349 1862837 := bbase (se 5 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 1862837 = 174641) (by norm_num)
theorem B1240253 : Blo 826349 1240253 := bbase (se 3 (by rfl) ⟨232547, by rfl⟩ : syracuseStep 1240253 = 465095) (by norm_num)
theorem B1240277 : Blo 826349 1240277 := bbase (se 7 (by rfl) ⟨14534, by rfl⟩ : syracuseStep 1240277 = 29069) (by norm_num)
theorem B1240301 : Blo 826349 1240301 := bbase (se 3 (by rfl) ⟨232556, by rfl⟩ : syracuseStep 1240301 = 465113) (by norm_num)
theorem B1862909 : Blo 826349 1862909 := bbase (se 3 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 1862909 = 698591) (by norm_num)
theorem B1240325 : Blo 826349 1240325 := bbase (se 4 (by rfl) ⟨116280, by rfl⟩ : syracuseStep 1240325 = 232561) (by norm_num)
theorem B945413 : Blo 826349 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B2092301 : Blo 826349 2092301 := bbase (se 3 (by rfl) ⟨392306, by rfl⟩ : syracuseStep 2092301 = 784613) (by norm_num)
theorem B1240349 : Blo 826349 1240349 := bbase (se 3 (by rfl) ⟨232565, by rfl⟩ : syracuseStep 1240349 = 465131) (by norm_num)
theorem B1994021 : Blo 826349 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B1240373 : Blo 826349 1240373 := bbase (se 5 (by rfl) ⟨58142, by rfl⟩ : syracuseStep 1240373 = 116285) (by norm_num)
theorem B1862981 : Blo 826349 1862981 := bbase (se 4 (by rfl) ⟨174654, by rfl⟩ : syracuseStep 1862981 = 349309) (by norm_num)
theorem B1240397 : Blo 826349 1240397 := bbase (se 3 (by rfl) ⟨232574, by rfl⟩ : syracuseStep 1240397 = 465149) (by norm_num)
theorem B1240421 : Blo 826349 1240421 := bbase (se 4 (by rfl) ⟨116289, by rfl⟩ : syracuseStep 1240421 = 232579) (by norm_num)
theorem B1011061 : Blo 826349 1011061 := bbase (se 5 (by rfl) ⟨47393, by rfl⟩ : syracuseStep 1011061 = 94787) (by norm_num)
theorem B1240445 : Blo 826349 1240445 := bbase (se 3 (by rfl) ⟨232583, by rfl⟩ : syracuseStep 1240445 = 465167) (by norm_num)
theorem B1863053 : Blo 826349 1863053 := bbase (se 3 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 1863053 = 698645) (by norm_num)
theorem B1240469 : Blo 826349 1240469 := bbase (se 6 (by rfl) ⟨29073, by rfl⟩ : syracuseStep 1240469 = 58147) (by norm_num)
theorem B1240493 : Blo 826349 1240493 := bbase (se 3 (by rfl) ⟨232592, by rfl⟩ : syracuseStep 1240493 = 465185) (by norm_num)
theorem B1240517 : Blo 826349 1240517 := bbase (se 4 (by rfl) ⟨116298, by rfl⟩ : syracuseStep 1240517 = 232597) (by norm_num)
theorem B2092493 : Blo 826349 2092493 := bbase (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) (by norm_num)
theorem B1863125 : Blo 826349 1863125 := bbase (se 7 (by rfl) ⟨21833, by rfl⟩ : syracuseStep 1863125 = 43667) (by norm_num)
theorem B1240541 : Blo 826349 1240541 := bbase (se 3 (by rfl) ⟨232601, by rfl⟩ : syracuseStep 1240541 = 465203) (by norm_num)
theorem B1240565 : Blo 826349 1240565 := bbase (se 5 (by rfl) ⟨58151, by rfl⟩ : syracuseStep 1240565 = 116303) (by norm_num)
theorem B3141125 : Blo 826349 3141125 := bbase (se 4 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 3141125 = 588961) (by norm_num)
theorem B1240589 : Blo 826349 1240589 := bbase (se 3 (by rfl) ⟨232610, by rfl⟩ : syracuseStep 1240589 = 465221) (by norm_num)
theorem B1863197 : Blo 826349 1863197 := bbase (se 3 (by rfl) ⟨349349, by rfl⟩ : syracuseStep 1863197 = 698699) (by norm_num)
theorem B1240613 : Blo 826349 1240613 := bbase (se 4 (by rfl) ⟨116307, by rfl⟩ : syracuseStep 1240613 = 232615) (by norm_num)
theorem B1240637 : Blo 826349 1240637 := bbase (se 3 (by rfl) ⟨232619, by rfl⟩ : syracuseStep 1240637 = 465239) (by norm_num)
theorem B1240661 : Blo 826349 1240661 := bbase (se 8 (by rfl) ⟨7269, by rfl⟩ : syracuseStep 1240661 = 14539) (by norm_num)
theorem B1863269 : Blo 826349 1863269 := bbase (se 4 (by rfl) ⟨174681, by rfl⟩ : syracuseStep 1863269 = 349363) (by norm_num)
theorem B1240685 : Blo 826349 1240685 := bbase (se 3 (by rfl) ⟨232628, by rfl⟩ : syracuseStep 1240685 = 465257) (by norm_num)
theorem B1994357 : Blo 826349 1994357 := bbase (se 5 (by rfl) ⟨93485, by rfl⟩ : syracuseStep 1994357 = 186971) (by norm_num)
theorem B1240709 : Blo 826349 1240709 := bbase (se 4 (by rfl) ⟨116316, by rfl⟩ : syracuseStep 1240709 = 232633) (by norm_num)
theorem B1240733 : Blo 826349 1240733 := bbase (se 3 (by rfl) ⟨232637, by rfl⟩ : syracuseStep 1240733 = 465275) (by norm_num)
theorem B1863341 : Blo 826349 1863341 := bbase (se 3 (by rfl) ⟨349376, by rfl⟩ : syracuseStep 1863341 = 698753) (by norm_num)
theorem B1240757 : Blo 826349 1240757 := bbase (se 5 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 1240757 = 116321) (by norm_num)
theorem B1240781 : Blo 826349 1240781 := bbase (se 3 (by rfl) ⟨232646, by rfl⟩ : syracuseStep 1240781 = 465293) (by norm_num)
theorem B1240805 : Blo 826349 1240805 := bbase (se 4 (by rfl) ⟨116325, by rfl⟩ : syracuseStep 1240805 = 232651) (by norm_num)
theorem B2354933 : Blo 826349 2354933 := bbase (se 5 (by rfl) ⟨110387, by rfl⟩ : syracuseStep 2354933 = 220775) (by norm_num)
theorem B6713077 : Blo 826349 6713077 := bbase (se 5 (by rfl) ⟨314675, by rfl⟩ : syracuseStep 6713077 = 629351) (by norm_num)
theorem B1863413 : Blo 826349 1863413 := bbase (se 5 (by rfl) ⟨87347, by rfl⟩ : syracuseStep 1863413 = 174695) (by norm_num)
theorem B1240829 : Blo 826349 1240829 := bbase (se 3 (by rfl) ⟨232655, by rfl⟩ : syracuseStep 1240829 = 465311) (by norm_num)
theorem B1240853 : Blo 826349 1240853 := bbase (se 6 (by rfl) ⟨29082, by rfl⟩ : syracuseStep 1240853 = 58165) (by norm_num)
theorem B2092837 : Blo 826349 2092837 := bbase (se 4 (by rfl) ⟨196203, by rfl⟩ : syracuseStep 2092837 = 392407) (by norm_num)
theorem B3141413 : Blo 826349 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B1240877 : Blo 826349 1240877 := bbase (se 3 (by rfl) ⟨232664, by rfl⟩ : syracuseStep 1240877 = 465329) (by norm_num)
theorem B1863485 : Blo 826349 1863485 := bbase (se 3 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 1863485 = 698807) (by norm_num)
theorem B1240901 : Blo 826349 1240901 := bbase (se 4 (by rfl) ⟨116334, by rfl⟩ : syracuseStep 1240901 = 232669) (by norm_num)
theorem B7958357 : Blo 826349 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B1240925 : Blo 826349 1240925 := bbase (se 3 (by rfl) ⟨232673, by rfl⟩ : syracuseStep 1240925 = 465347) (by norm_num)
theorem B1240949 : Blo 826349 1240949 := bbase (se 5 (by rfl) ⟨58169, by rfl⟩ : syracuseStep 1240949 = 116339) (by norm_num)
theorem B1863557 : Blo 826349 1863557 := bbase (se 4 (by rfl) ⟨174708, by rfl⟩ : syracuseStep 1863557 = 349417) (by norm_num)
theorem B1240973 : Blo 826349 1240973 := bbase (se 3 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 1240973 = 465365) (by norm_num)
theorem B2092949 : Blo 826349 2092949 := bbase (se 6 (by rfl) ⟨49053, by rfl⟩ : syracuseStep 2092949 = 98107) (by norm_num)
theorem B1240997 : Blo 826349 1240997 := bbase (se 4 (by rfl) ⟨116343, by rfl⟩ : syracuseStep 1240997 = 232687) (by norm_num)
theorem B1241021 : Blo 826349 1241021 := bbase (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) (by norm_num)
theorem B946117 : Blo 826349 946117 := bbase (se 4 (by rfl) ⟨88698, by rfl⟩ : syracuseStep 946117 = 177397) (by norm_num)
theorem B1863629 : Blo 826349 1863629 := bbase (se 3 (by rfl) ⟨349430, by rfl⟩ : syracuseStep 1863629 = 698861) (by norm_num)
theorem B1241045 : Blo 826349 1241045 := bbase (se 7 (by rfl) ⟨14543, by rfl⟩ : syracuseStep 1241045 = 29087) (by norm_num)
theorem B1241069 : Blo 826349 1241069 := bbase (se 3 (by rfl) ⟨232700, by rfl⟩ : syracuseStep 1241069 = 465401) (by norm_num)
theorem B1994749 : Blo 826349 1994749 := bbase (se 3 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 1994749 = 748031) (by norm_num)
theorem B1241093 : Blo 826349 1241093 := bbase (se 4 (by rfl) ⟨116352, by rfl⟩ : syracuseStep 1241093 = 232705) (by norm_num)
theorem B6287381 : Blo 826349 6287381 := bbase (se 6 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 6287381 = 294721) (by norm_num)
theorem B1863701 : Blo 826349 1863701 := bbase (se 6 (by rfl) ⟨43680, by rfl⟩ : syracuseStep 1863701 = 87361) (by norm_num)
theorem B1765405 : Blo 826349 1765405 := bbase (se 3 (by rfl) ⟨331013, by rfl⟩ : syracuseStep 1765405 = 662027) (by norm_num)
theorem B1241117 : Blo 826349 1241117 := bbase (se 3 (by rfl) ⟨232709, by rfl⟩ : syracuseStep 1241117 = 465419) (by norm_num)
theorem B1241141 : Blo 826349 1241141 := bbase (se 5 (by rfl) ⟨58178, by rfl⟩ : syracuseStep 1241141 = 116357) (by norm_num)
theorem B1241165 : Blo 826349 1241165 := bbase (se 3 (by rfl) ⟨232718, by rfl⟩ : syracuseStep 1241165 = 465437) (by norm_num)
theorem B2093141 : Blo 826349 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B1863773 : Blo 826349 1863773 := bbase (se 3 (by rfl) ⟨349457, by rfl⟩ : syracuseStep 1863773 = 698915) (by norm_num)
theorem B1241189 : Blo 826349 1241189 := bbase (se 4 (by rfl) ⟨116361, by rfl⟩ : syracuseStep 1241189 = 232723) (by norm_num)
theorem B1241213 : Blo 826349 1241213 := bbase (se 3 (by rfl) ⟨232727, by rfl⟩ : syracuseStep 1241213 = 465455) (by norm_num)
theorem B1241237 : Blo 826349 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B1863845 : Blo 826349 1863845 := bbase (se 4 (by rfl) ⟨174735, by rfl⟩ : syracuseStep 1863845 = 349471) (by norm_num)
theorem B1241261 : Blo 826349 1241261 := bbase (se 3 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 1241261 = 465473) (by norm_num)
theorem B1241285 : Blo 826349 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B1274077 : Blo 826349 1274077 := bbase (se 3 (by rfl) ⟨238889, by rfl⟩ : syracuseStep 1274077 = 477779) (by norm_num)
theorem B1241309 : Blo 826349 1241309 := bbase (se 3 (by rfl) ⟨232745, by rfl⟩ : syracuseStep 1241309 = 465491) (by norm_num)
theorem B946409 : Blo 826349 946409 := bbase (se 2 (by rfl) ⟨354903, by rfl⟩ : syracuseStep 946409 = 709807) (by norm_num)
theorem B1863917 : Blo 826349 1863917 := bbase (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) (by norm_num)
theorem B1241333 : Blo 826349 1241333 := bbase (se 5 (by rfl) ⟨58187, by rfl⟩ : syracuseStep 1241333 = 116375) (by norm_num)
theorem B4190453 : Blo 826349 4190453 := bbase (se 5 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 4190453 = 392855) (by norm_num)
theorem B1241357 : Blo 826349 1241357 := bbase (se 3 (by rfl) ⟨232754, by rfl⟩ : syracuseStep 1241357 = 465509) (by norm_num)
theorem B1241381 : Blo 826349 1241381 := bbase (se 4 (by rfl) ⟨116379, by rfl⟩ : syracuseStep 1241381 = 232759) (by norm_num)
theorem B1863989 : Blo 826349 1863989 := bbase (se 5 (by rfl) ⟨87374, by rfl⟩ : syracuseStep 1863989 = 174749) (by norm_num)
theorem B1241405 : Blo 826349 1241405 := bbase (se 3 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 1241405 = 465527) (by norm_num)
theorem B1241429 : Blo 826349 1241429 := bbase (se 10 (by rfl) ⟨1818, by rfl⟩ : syracuseStep 1241429 = 3637) (by norm_num)
theorem B1241453 : Blo 826349 1241453 := bbase (se 3 (by rfl) ⟨232772, by rfl⟩ : syracuseStep 1241453 = 465545) (by norm_num)
theorem B2126189 : Blo 826349 2126189 := bbase (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) (by norm_num)
theorem B1864061 : Blo 826349 1864061 := bbase (se 3 (by rfl) ⟨349511, by rfl⟩ : syracuseStep 1864061 = 699023) (by norm_num)
theorem B1241477 : Blo 826349 1241477 := bbase (se 4 (by rfl) ⟨116388, by rfl⟩ : syracuseStep 1241477 = 232777) (by norm_num)
theorem B2355605 : Blo 826349 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B1241501 : Blo 826349 1241501 := bbase (se 3 (by rfl) ⟨232781, by rfl⟩ : syracuseStep 1241501 = 465563) (by norm_num)
theorem B2093485 : Blo 826349 2093485 := bbase (se 3 (by rfl) ⟨392528, by rfl⟩ : syracuseStep 2093485 = 785057) (by norm_num)
theorem B1241525 : Blo 826349 1241525 := bbase (se 5 (by rfl) ⟨58196, by rfl⟩ : syracuseStep 1241525 = 116393) (by norm_num)
theorem B1864133 : Blo 826349 1864133 := bbase (se 4 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 1864133 = 349525) (by norm_num)
theorem B1241549 : Blo 826349 1241549 := bbase (se 3 (by rfl) ⟨232790, by rfl⟩ : syracuseStep 1241549 = 465581) (by norm_num)
theorem B1241573 : Blo 826349 1241573 := bbase (se 4 (by rfl) ⟨116397, by rfl⟩ : syracuseStep 1241573 = 232795) (by norm_num)
theorem B1241597 : Blo 826349 1241597 := bbase (se 3 (by rfl) ⟨232799, by rfl⟩ : syracuseStep 1241597 = 465599) (by norm_num)
theorem B1765901 : Blo 826349 1765901 := bbase (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) (by norm_num)
theorem B1864205 : Blo 826349 1864205 := bbase (se 3 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 1864205 = 699077) (by norm_num)
theorem B1241621 : Blo 826349 1241621 := bbase (se 6 (by rfl) ⟨29100, by rfl⟩ : syracuseStep 1241621 = 58201) (by norm_num)
theorem B2093597 : Blo 826349 2093597 := bbase (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) (by norm_num)
theorem B1241645 : Blo 826349 1241645 := bbase (se 3 (by rfl) ⟨232808, by rfl⟩ : syracuseStep 1241645 = 465617) (by norm_num)
theorem B1241669 : Blo 826349 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B1864277 : Blo 826349 1864277 := bbase (se 8 (by rfl) ⟨10923, by rfl⟩ : syracuseStep 1864277 = 21847) (by norm_num)
theorem B1241693 : Blo 826349 1241693 := bbase (se 3 (by rfl) ⟨232817, by rfl⟩ : syracuseStep 1241693 = 465635) (by norm_num)
theorem B1241717 : Blo 826349 1241717 := bbase (se 5 (by rfl) ⟨58205, by rfl⟩ : syracuseStep 1241717 = 116411) (by norm_num)
theorem B1241741 : Blo 826349 1241741 := bbase (se 3 (by rfl) ⟨232826, by rfl⟩ : syracuseStep 1241741 = 465653) (by norm_num)
theorem B1864349 : Blo 826349 1864349 := bbase (se 3 (by rfl) ⟨349565, by rfl⟩ : syracuseStep 1864349 = 699131) (by norm_num)
theorem B1241765 : Blo 826349 1241765 := bbase (se 4 (by rfl) ⟨116415, by rfl⟩ : syracuseStep 1241765 = 232831) (by norm_num)
theorem B946873 : Blo 826349 946873 := bbase (se 2 (by rfl) ⟨355077, by rfl⟩ : syracuseStep 946873 = 710155) (by norm_num)
theorem B1569469 : Blo 826349 1569469 := bbase (se 3 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 1569469 = 588551) (by norm_num)
theorem B1241789 : Blo 826349 1241789 := bbase (se 3 (by rfl) ⟨232835, by rfl⟩ : syracuseStep 1241789 = 465671) (by norm_num)
theorem B1241813 : Blo 826349 1241813 := bbase (se 7 (by rfl) ⟨14552, by rfl⟩ : syracuseStep 1241813 = 29105) (by norm_num)
theorem B2093789 : Blo 826349 2093789 := bbase (se 3 (by rfl) ⟨392585, by rfl⟩ : syracuseStep 2093789 = 785171) (by norm_num)
theorem B1864421 : Blo 826349 1864421 := bbase (se 4 (by rfl) ⟨174789, by rfl⟩ : syracuseStep 1864421 = 349579) (by norm_num)
theorem B1241837 : Blo 826349 1241837 := bbase (se 3 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 1241837 = 465689) (by norm_num)
theorem B1241861 : Blo 826349 1241861 := bbase (se 4 (by rfl) ⟨116424, by rfl⟩ : syracuseStep 1241861 = 232849) (by norm_num)
theorem B1241885 : Blo 826349 1241885 := bbase (se 3 (by rfl) ⟨232853, by rfl⟩ : syracuseStep 1241885 = 465707) (by norm_num)
theorem B1864493 : Blo 826349 1864493 := bbase (se 3 (by rfl) ⟨349592, by rfl⟩ : syracuseStep 1864493 = 699185) (by norm_num)
theorem B1241909 : Blo 826349 1241909 := bbase (se 5 (by rfl) ⟨58214, by rfl⟩ : syracuseStep 1241909 = 116429) (by norm_num)
theorem B2356037 : Blo 826349 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B1569613 : Blo 826349 1569613 := bbase (se 3 (by rfl) ⟨294302, by rfl⟩ : syracuseStep 1569613 = 588605) (by norm_num)
theorem B1241933 : Blo 826349 1241933 := bbase (se 3 (by rfl) ⟨232862, by rfl⟩ : syracuseStep 1241933 = 465725) (by norm_num)
theorem B1241957 : Blo 826349 1241957 := bbase (se 4 (by rfl) ⟨116433, by rfl⟩ : syracuseStep 1241957 = 232867) (by norm_num)
theorem B1864565 : Blo 826349 1864565 := bbase (se 5 (by rfl) ⟨87401, by rfl⟩ : syracuseStep 1864565 = 174803) (by norm_num)
theorem B1241981 : Blo 826349 1241981 := bbase (se 3 (by rfl) ⟨232871, by rfl⟩ : syracuseStep 1241981 = 465743) (by norm_num)
theorem B1242005 : Blo 826349 1242005 := bbase (se 6 (by rfl) ⟨29109, by rfl⟩ : syracuseStep 1242005 = 58219) (by norm_num)
theorem B1242029 : Blo 826349 1242029 := bbase (se 3 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 1242029 = 465761) (by norm_num)
theorem B1864637 : Blo 826349 1864637 := bbase (se 3 (by rfl) ⟨349619, by rfl⟩ : syracuseStep 1864637 = 699239) (by norm_num)
theorem B3142597 : Blo 826349 3142597 := bbase (se 4 (by rfl) ⟨294618, by rfl⟩ : syracuseStep 3142597 = 589237) (by norm_num)
theorem B1242053 : Blo 826349 1242053 := bbase (se 4 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 1242053 = 232885) (by norm_num)
theorem B1242077 : Blo 826349 1242077 := bbase (se 3 (by rfl) ⟨232889, by rfl⟩ : syracuseStep 1242077 = 465779) (by norm_num)
theorem B1569773 : Blo 826349 1569773 := bbase (se 3 (by rfl) ⟨294332, by rfl⟩ : syracuseStep 1569773 = 588665) (by norm_num)
theorem B1242101 : Blo 826349 1242101 := bbase (se 5 (by rfl) ⟨58223, by rfl⟩ : syracuseStep 1242101 = 116447) (by norm_num)
theorem B1864709 : Blo 826349 1864709 := bbase (se 4 (by rfl) ⟨174816, by rfl⟩ : syracuseStep 1864709 = 349633) (by norm_num)
theorem B1242125 : Blo 826349 1242125 := bbase (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) (by norm_num)
theorem B1242149 : Blo 826349 1242149 := bbase (se 4 (by rfl) ⟨116451, by rfl⟩ : syracuseStep 1242149 = 232903) (by norm_num)
theorem B2094133 : Blo 826349 2094133 := bbase (se 5 (by rfl) ⟨98162, by rfl⟩ : syracuseStep 2094133 = 196325) (by norm_num)
theorem B1242173 : Blo 826349 1242173 := bbase (se 3 (by rfl) ⟨232907, by rfl⟩ : syracuseStep 1242173 = 465815) (by norm_num)
theorem B1864781 : Blo 826349 1864781 := bbase (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) (by norm_num)
theorem B1242197 : Blo 826349 1242197 := bbase (se 8 (by rfl) ⟨7278, by rfl⟩ : syracuseStep 1242197 = 14557) (by norm_num)
theorem B1242221 : Blo 826349 1242221 := bbase (se 3 (by rfl) ⟨232916, by rfl⟩ : syracuseStep 1242221 = 465833) (by norm_num)
theorem B1569917 : Blo 826349 1569917 := bbase (se 3 (by rfl) ⟨294359, by rfl⟩ : syracuseStep 1569917 = 588719) (by norm_num)
theorem B1176709 : Blo 826349 1176709 := bbase (se 4 (by rfl) ⟨110316, by rfl⟩ : syracuseStep 1176709 = 220633) (by norm_num)
theorem B1242245 : Blo 826349 1242245 := bbase (se 4 (by rfl) ⟨116460, by rfl⟩ : syracuseStep 1242245 = 232921) (by norm_num)
theorem B1864853 : Blo 826349 1864853 := bbase (se 6 (by rfl) ⟨43707, by rfl⟩ : syracuseStep 1864853 = 87415) (by norm_num)
theorem B1242269 : Blo 826349 1242269 := bbase (se 3 (by rfl) ⟨232925, by rfl⟩ : syracuseStep 1242269 = 465851) (by norm_num)
theorem B2094245 : Blo 826349 2094245 := bbase (se 4 (by rfl) ⟨196335, by rfl⟩ : syracuseStep 2094245 = 392671) (by norm_num)
theorem B1242293 : Blo 826349 1242293 := bbase (se 5 (by rfl) ⟨58232, by rfl⟩ : syracuseStep 1242293 = 116465) (by norm_num)
theorem B1242317 : Blo 826349 1242317 := bbase (se 3 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 1242317 = 465869) (by norm_num)
theorem B1864925 : Blo 826349 1864925 := bbase (se 3 (by rfl) ⟨349673, by rfl⟩ : syracuseStep 1864925 = 699347) (by norm_num)
theorem B1242341 : Blo 826349 1242341 := bbase (se 4 (by rfl) ⟨116469, by rfl⟩ : syracuseStep 1242341 = 232939) (by norm_num)
theorem B3142901 : Blo 826349 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B4715765 : Blo 826349 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B1242365 : Blo 826349 1242365 := bbase (se 3 (by rfl) ⟨232943, by rfl⟩ : syracuseStep 1242365 = 465887) (by norm_num)
theorem B1242389 : Blo 826349 1242389 := bbase (se 6 (by rfl) ⟨29118, by rfl⟩ : syracuseStep 1242389 = 58237) (by norm_num)
theorem B1864997 : Blo 826349 1864997 := bbase (se 4 (by rfl) ⟨174843, by rfl⟩ : syracuseStep 1864997 = 349687) (by norm_num)
theorem B1242413 : Blo 826349 1242413 := bbase (se 3 (by rfl) ⟨232952, by rfl⟩ : syracuseStep 1242413 = 465905) (by norm_num)
theorem B1242437 : Blo 826349 1242437 := bbase (se 4 (by rfl) ⟨116478, by rfl⟩ : syracuseStep 1242437 = 232957) (by norm_num)
theorem B1078601 : Blo 826349 1078601 := bbase (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) (by norm_num)
theorem B1176925 : Blo 826349 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B1275229 : Blo 826349 1275229 := bbase (se 3 (by rfl) ⟨239105, by rfl⟩ : syracuseStep 1275229 = 478211) (by norm_num)
theorem B1242461 : Blo 826349 1242461 := bbase (se 3 (by rfl) ⟨232961, by rfl⟩ : syracuseStep 1242461 = 465923) (by norm_num)
theorem B2094437 : Blo 826349 2094437 := bbase (se 4 (by rfl) ⟨196353, by rfl⟩ : syracuseStep 2094437 = 392707) (by norm_num)
theorem B1865069 : Blo 826349 1865069 := bbase (se 3 (by rfl) ⟨349700, by rfl⟩ : syracuseStep 1865069 = 699401) (by norm_num)
theorem B1242485 : Blo 826349 1242485 := bbase (se 5 (by rfl) ⟨58241, by rfl⟩ : syracuseStep 1242485 = 116483) (by norm_num)
theorem B1766789 : Blo 826349 1766789 := bbase (se 4 (by rfl) ⟨165636, by rfl⟩ : syracuseStep 1766789 = 331273) (by norm_num)
theorem B1242509 : Blo 826349 1242509 := bbase (se 3 (by rfl) ⟨232970, by rfl⟩ : syracuseStep 1242509 = 465941) (by norm_num)
theorem B1570205 : Blo 826349 1570205 := bbase (se 3 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 1570205 = 588827) (by norm_num)
theorem B1242533 : Blo 826349 1242533 := bbase (se 4 (by rfl) ⟨116487, by rfl⟩ : syracuseStep 1242533 = 232975) (by norm_num)
theorem B1865141 : Blo 826349 1865141 := bbase (se 5 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 1865141 = 174857) (by norm_num)
theorem B1242557 : Blo 826349 1242557 := bbase (se 3 (by rfl) ⟨232979, by rfl⟩ : syracuseStep 1242557 = 465959) (by norm_num)
theorem B1045973 : Blo 826349 1045973 := bbase (se 7 (by rfl) ⟨12257, by rfl⟩ : syracuseStep 1045973 = 24515) (by norm_num)
theorem B1242581 : Blo 826349 1242581 := bbase (se 7 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 1242581 = 29123) (by norm_num)
theorem B10221013 : Blo 826349 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B1242605 : Blo 826349 1242605 := bbase (se 3 (by rfl) ⟨232988, by rfl⟩ : syracuseStep 1242605 = 465977) (by norm_num)
theorem B1766909 : Blo 826349 1766909 := bbase (se 3 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 1766909 = 662591) (by norm_num)
theorem B1865213 : Blo 826349 1865213 := bbase (se 3 (by rfl) ⟨349727, by rfl⟩ : syracuseStep 1865213 = 699455) (by norm_num)
theorem B4191749 : Blo 826349 4191749 := bbase (se 4 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 4191749 = 785953) (by norm_num)
theorem B1242629 : Blo 826349 1242629 := bbase (se 4 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 1242629 = 232993) (by norm_num)
theorem B1046029 : Blo 826349 1046029 := bbase (se 3 (by rfl) ⟨196130, by rfl⟩ : syracuseStep 1046029 = 392261) (by norm_num)
theorem B1242653 : Blo 826349 1242653 := bbase (se 3 (by rfl) ⟨232997, by rfl⟩ : syracuseStep 1242653 = 465995) (by norm_num)
theorem B1570357 : Blo 826349 1570357 := bbase (se 5 (by rfl) ⟨73610, by rfl⟩ : syracuseStep 1570357 = 147221) (by norm_num)
theorem B2356789 : Blo 826349 2356789 := bbase (se 5 (by rfl) ⟨110474, by rfl⟩ : syracuseStep 2356789 = 220949) (by norm_num)
theorem B1242677 : Blo 826349 1242677 := bbase (se 5 (by rfl) ⟨58250, by rfl⟩ : syracuseStep 1242677 = 116501) (by norm_num)
theorem B1865285 : Blo 826349 1865285 := bbase (se 4 (by rfl) ⟨174870, by rfl⟩ : syracuseStep 1865285 = 349741) (by norm_num)
theorem B1242701 : Blo 826349 1242701 := bbase (se 3 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 1242701 = 466013) (by norm_num)
theorem B1242725 : Blo 826349 1242725 := bbase (se 4 (by rfl) ⟨116505, by rfl⟩ : syracuseStep 1242725 = 233011) (by norm_num)
theorem B1046125 : Blo 826349 1046125 := bbase (se 3 (by rfl) ⟨196148, by rfl⟩ : syracuseStep 1046125 = 392297) (by norm_num)
theorem B1242749 : Blo 826349 1242749 := bbase (se 3 (by rfl) ⟨233015, by rfl⟩ : syracuseStep 1242749 = 466031) (by norm_num)
theorem B1865357 : Blo 826349 1865357 := bbase (se 3 (by rfl) ⟨349754, by rfl⟩ : syracuseStep 1865357 = 699509) (by norm_num)
theorem B1242773 : Blo 826349 1242773 := bbase (se 6 (by rfl) ⟨29127, by rfl⟩ : syracuseStep 1242773 = 58255) (by norm_num)
theorem B1242797 : Blo 826349 1242797 := bbase (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) (by norm_num)
theorem B2094781 : Blo 826349 2094781 := bbase (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) (by norm_num)
theorem B1242821 : Blo 826349 1242821 := bbase (se 4 (by rfl) ⟨116514, by rfl⟩ : syracuseStep 1242821 = 233029) (by norm_num)
theorem B1177301 : Blo 826349 1177301 := bbase (se 7 (by rfl) ⟨13796, by rfl⟩ : syracuseStep 1177301 = 27593) (by norm_num)
theorem B1865429 : Blo 826349 1865429 := bbase (se 7 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 1865429 = 43721) (by norm_num)
theorem B1242845 : Blo 826349 1242845 := bbase (se 3 (by rfl) ⟨233033, by rfl⟩ : syracuseStep 1242845 = 466067) (by norm_num)
theorem B2127581 : Blo 826349 2127581 := bbase (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) (by norm_num)
theorem B1242869 : Blo 826349 1242869 := bbase (se 5 (by rfl) ⟨58259, by rfl⟩ : syracuseStep 1242869 = 116519) (by norm_num)
theorem B1242893 : Blo 826349 1242893 := bbase (se 3 (by rfl) ⟨233042, by rfl⟩ : syracuseStep 1242893 = 466085) (by norm_num)
theorem B1046297 : Blo 826349 1046297 := bbase (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) (by norm_num)
theorem B1865501 : Blo 826349 1865501 := bbase (se 3 (by rfl) ⟨349781, by rfl⟩ : syracuseStep 1865501 = 699563) (by norm_num)
theorem B1242917 : Blo 826349 1242917 := bbase (se 4 (by rfl) ⟨116523, by rfl⟩ : syracuseStep 1242917 = 233047) (by norm_num)
theorem B2094893 : Blo 826349 2094893 := bbase (se 3 (by rfl) ⟨392792, by rfl⟩ : syracuseStep 2094893 = 785585) (by norm_num)
theorem B1242941 : Blo 826349 1242941 := bbase (se 3 (by rfl) ⟨233051, by rfl⟩ : syracuseStep 1242941 = 466103) (by norm_num)
theorem B1046353 : Blo 826349 1046353 := bbase (se 2 (by rfl) ⟨392382, by rfl⟩ : syracuseStep 1046353 = 784765) (by norm_num)
theorem B1242965 : Blo 826349 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B1570661 : Blo 826349 1570661 := bbase (se 4 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 1570661 = 294499) (by norm_num)
theorem B1865573 : Blo 826349 1865573 := bbase (se 4 (by rfl) ⟨174897, by rfl⟩ : syracuseStep 1865573 = 349795) (by norm_num)
theorem B1242989 : Blo 826349 1242989 := bbase (se 3 (by rfl) ⟨233060, by rfl⟩ : syracuseStep 1242989 = 466121) (by norm_num)
theorem B1243013 : Blo 826349 1243013 := bbase (se 4 (by rfl) ⟨116532, by rfl⟩ : syracuseStep 1243013 = 233065) (by norm_num)
theorem B1243037 : Blo 826349 1243037 := bbase (se 3 (by rfl) ⟨233069, by rfl⟩ : syracuseStep 1243037 = 466139) (by norm_num)
theorem B1865645 : Blo 826349 1865645 := bbase (se 3 (by rfl) ⟨349808, by rfl⟩ : syracuseStep 1865645 = 699617) (by norm_num)
theorem B1046449 : Blo 826349 1046449 := bbase (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) (by norm_num)
theorem B1243061 : Blo 826349 1243061 := bbase (se 5 (by rfl) ⟨58268, by rfl⟩ : syracuseStep 1243061 = 116537) (by norm_num)
theorem B1243085 : Blo 826349 1243085 := bbase (se 3 (by rfl) ⟨233078, by rfl⟩ : syracuseStep 1243085 = 466157) (by norm_num)
theorem B1243109 : Blo 826349 1243109 := bbase (se 4 (by rfl) ⟨116541, by rfl⟩ : syracuseStep 1243109 = 233083) (by norm_num)
theorem B2095085 : Blo 826349 2095085 := bbase (se 3 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 2095085 = 785657) (by norm_num)
theorem B882677 : Blo 826349 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B1865717 : Blo 826349 1865717 := bbase (se 5 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 1865717 = 174911) (by norm_num)
theorem B1243133 : Blo 826349 1243133 := bbase (se 3 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 1243133 = 466175) (by norm_num)
theorem B1243157 : Blo 826349 1243157 := bbase (se 6 (by rfl) ⟨29136, by rfl⟩ : syracuseStep 1243157 = 58273) (by norm_num)
theorem B1243181 : Blo 826349 1243181 := bbase (se 3 (by rfl) ⟨233096, by rfl⟩ : syracuseStep 1243181 = 466193) (by norm_num)
theorem B1865789 : Blo 826349 1865789 := bbase (se 3 (by rfl) ⟨349835, by rfl⟩ : syracuseStep 1865789 = 699671) (by norm_num)
theorem B1243205 : Blo 826349 1243205 := bbase (se 4 (by rfl) ⟨116550, by rfl⟩ : syracuseStep 1243205 = 233101) (by norm_num)
theorem B1046621 : Blo 826349 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B1243229 : Blo 826349 1243229 := bbase (se 3 (by rfl) ⟨233105, by rfl⟩ : syracuseStep 1243229 = 466211) (by norm_num)
theorem B1767541 : Blo 826349 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B1243253 : Blo 826349 1243253 := bbase (se 5 (by rfl) ⟨58277, by rfl⟩ : syracuseStep 1243253 = 116555) (by norm_num)
theorem B1865861 : Blo 826349 1865861 := bbase (se 4 (by rfl) ⟨174924, by rfl⟩ : syracuseStep 1865861 = 349849) (by norm_num)
theorem B1243277 : Blo 826349 1243277 := bbase (se 3 (by rfl) ⟨233114, by rfl⟩ : syracuseStep 1243277 = 466229) (by norm_num)
theorem B1046677 : Blo 826349 1046677 := bbase (se 6 (by rfl) ⟨24531, by rfl⟩ : syracuseStep 1046677 = 49063) (by norm_num)
theorem B1243301 : Blo 826349 1243301 := bbase (se 4 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 1243301 = 233119) (by norm_num)
theorem B1243325 : Blo 826349 1243325 := bbase (se 3 (by rfl) ⟨233123, by rfl⟩ : syracuseStep 1243325 = 466247) (by norm_num)
theorem B1865933 : Blo 826349 1865933 := bbase (se 3 (by rfl) ⟨349862, by rfl⟩ : syracuseStep 1865933 = 699725) (by norm_num)
theorem B1243349 : Blo 826349 1243349 := bbase (se 7 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 1243349 = 29141) (by norm_num)
theorem B1243373 : Blo 826349 1243373 := bbase (se 3 (by rfl) ⟨233132, by rfl⟩ : syracuseStep 1243373 = 466265) (by norm_num)
theorem B1046773 : Blo 826349 1046773 := bbase (se 5 (by rfl) ⟨49067, by rfl⟩ : syracuseStep 1046773 = 98135) (by norm_num)
theorem B1243397 : Blo 826349 1243397 := bbase (se 4 (by rfl) ⟨116568, by rfl⟩ : syracuseStep 1243397 = 233137) (by norm_num)
theorem B1866005 : Blo 826349 1866005 := bbase (se 6 (by rfl) ⟨43734, by rfl⟩ : syracuseStep 1866005 = 87469) (by norm_num)
theorem B1243421 : Blo 826349 1243421 := bbase (se 3 (by rfl) ⟨233141, by rfl⟩ : syracuseStep 1243421 = 466283) (by norm_num)
theorem B1243445 : Blo 826349 1243445 := bbase (se 5 (by rfl) ⟨58286, by rfl⟩ : syracuseStep 1243445 = 116573) (by norm_num)
theorem B2095429 : Blo 826349 2095429 := bbase (se 4 (by rfl) ⟨196446, by rfl⟩ : syracuseStep 2095429 = 392893) (by norm_num)
theorem B1243469 : Blo 826349 1243469 := bbase (se 3 (by rfl) ⟨233150, by rfl⟩ : syracuseStep 1243469 = 466301) (by norm_num)
theorem B1866077 : Blo 826349 1866077 := bbase (se 3 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 1866077 = 699779) (by norm_num)
theorem B1243493 : Blo 826349 1243493 := bbase (se 4 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 1243493 = 233155) (by norm_num)
theorem B3537269 : Blo 826349 3537269 := bbase (se 5 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 3537269 = 331619) (by norm_num)
theorem B1243517 : Blo 826349 1243517 := bbase (se 3 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 1243517 = 466319) (by norm_num)
theorem B1243541 : Blo 826349 1243541 := bbase (se 6 (by rfl) ⟨29145, by rfl⟩ : syracuseStep 1243541 = 58291) (by norm_num)
theorem B1046945 : Blo 826349 1046945 := bbase (se 2 (by rfl) ⟨392604, by rfl⟩ : syracuseStep 1046945 = 785209) (by norm_num)
theorem B2652581 : Blo 826349 2652581 := bbase (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) (by norm_num)
theorem B1866149 : Blo 826349 1866149 := bbase (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) (by norm_num)
theorem B1243565 : Blo 826349 1243565 := bbase (se 3 (by rfl) ⟨233168, by rfl⟩ : syracuseStep 1243565 = 466337) (by norm_num)
theorem B883121 : Blo 826349 883121 := bbase (se 2 (by rfl) ⟨331170, by rfl⟩ : syracuseStep 883121 = 662341) (by norm_num)
theorem B2095541 : Blo 826349 2095541 := bbase (se 5 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 2095541 = 196457) (by norm_num)
theorem B1243589 : Blo 826349 1243589 := bbase (se 4 (by rfl) ⟨116586, by rfl⟩ : syracuseStep 1243589 = 233173) (by norm_num)
theorem B1047001 : Blo 826349 1047001 := bbase (se 2 (by rfl) ⟨392625, by rfl⟩ : syracuseStep 1047001 = 785251) (by norm_num)
theorem B1243613 : Blo 826349 1243613 := bbase (se 3 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 1243613 = 466355) (by norm_num)
theorem B883181 : Blo 826349 883181 := bbase (se 3 (by rfl) ⟨165596, by rfl⟩ : syracuseStep 883181 = 331193) (by norm_num)
theorem B1866221 : Blo 826349 1866221 := bbase (se 3 (by rfl) ⟨349916, by rfl⟩ : syracuseStep 1866221 = 699833) (by norm_num)
theorem B1243637 : Blo 826349 1243637 := bbase (se 5 (by rfl) ⟨58295, by rfl⟩ : syracuseStep 1243637 = 116591) (by norm_num)
theorem B4487669 : Blo 826349 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B1243661 : Blo 826349 1243661 := bbase (se 3 (by rfl) ⟨233186, by rfl⟩ : syracuseStep 1243661 = 466373) (by norm_num)
theorem B1243685 : Blo 826349 1243685 := bbase (se 4 (by rfl) ⟨116595, by rfl⟩ : syracuseStep 1243685 = 233191) (by norm_num)
theorem B1866293 : Blo 826349 1866293 := bbase (se 5 (by rfl) ⟨87482, by rfl⟩ : syracuseStep 1866293 = 174965) (by norm_num)
theorem B1047097 : Blo 826349 1047097 := bbase (se 2 (by rfl) ⟨392661, by rfl⟩ : syracuseStep 1047097 = 785323) (by norm_num)
theorem B1243709 : Blo 826349 1243709 := bbase (se 3 (by rfl) ⟨233195, by rfl⟩ : syracuseStep 1243709 = 466391) (by norm_num)
theorem B1571413 : Blo 826349 1571413 := bbase (se 8 (by rfl) ⟨9207, by rfl⟩ : syracuseStep 1571413 = 18415) (by norm_num)
theorem B1243733 : Blo 826349 1243733 := bbase (se 8 (by rfl) ⟨7287, by rfl⟩ : syracuseStep 1243733 = 14575) (by norm_num)
theorem B883309 : Blo 826349 883309 := bbase (se 3 (by rfl) ⟨165620, by rfl⟩ : syracuseStep 883309 = 331241) (by norm_num)
theorem B1243757 : Blo 826349 1243757 := bbase (se 3 (by rfl) ⟨233204, by rfl⟩ : syracuseStep 1243757 = 466409) (by norm_num)
theorem B2095733 : Blo 826349 2095733 := bbase (se 5 (by rfl) ⟨98237, by rfl⟩ : syracuseStep 2095733 = 196475) (by norm_num)
theorem B1866365 : Blo 826349 1866365 := bbase (se 3 (by rfl) ⟨349943, by rfl⟩ : syracuseStep 1866365 = 699887) (by norm_num)
theorem B1243781 : Blo 826349 1243781 := bbase (se 4 (by rfl) ⟨116604, by rfl⟩ : syracuseStep 1243781 = 233209) (by norm_num)
theorem B5307029 : Blo 826349 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B1243805 : Blo 826349 1243805 := bbase (se 3 (by rfl) ⟨233213, by rfl⟩ : syracuseStep 1243805 = 466427) (by norm_num)
theorem B1243829 : Blo 826349 1243829 := bbase (se 5 (by rfl) ⟨58304, by rfl⟩ : syracuseStep 1243829 = 116609) (by norm_num)
theorem B1866437 : Blo 826349 1866437 := bbase (se 4 (by rfl) ⟨174978, by rfl⟩ : syracuseStep 1866437 = 349957) (by norm_num)
theorem B1243853 : Blo 826349 1243853 := bbase (se 3 (by rfl) ⟨233222, by rfl⟩ : syracuseStep 1243853 = 466445) (by norm_num)
theorem B850649 : Blo 826349 850649 := bbase (se 2 (by rfl) ⟨318993, by rfl⟩ : syracuseStep 850649 = 637987) (by norm_num)
theorem B1047269 : Blo 826349 1047269 := bbase (se 4 (by rfl) ⟨98181, by rfl⟩ : syracuseStep 1047269 = 196363) (by norm_num)
theorem B1571557 : Blo 826349 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B1243877 : Blo 826349 1243877 := bbase (se 4 (by rfl) ⟨116613, by rfl⟩ : syracuseStep 1243877 = 233227) (by norm_num)
theorem B1243901 : Blo 826349 1243901 := bbase (se 3 (by rfl) ⟨233231, by rfl⟩ : syracuseStep 1243901 = 466463) (by norm_num)
theorem B1866509 : Blo 826349 1866509 := bbase (se 3 (by rfl) ⟨349970, by rfl⟩ : syracuseStep 1866509 = 699941) (by norm_num)
theorem B4193045 : Blo 826349 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B1243925 : Blo 826349 1243925 := bbase (se 6 (by rfl) ⟨29154, by rfl⟩ : syracuseStep 1243925 = 58309) (by norm_num)
theorem B1047325 : Blo 826349 1047325 := bbase (se 3 (by rfl) ⟨196373, by rfl⟩ : syracuseStep 1047325 = 392747) (by norm_num)
theorem B1243949 : Blo 826349 1243949 := bbase (se 3 (by rfl) ⟨233240, by rfl⟩ : syracuseStep 1243949 = 466481) (by norm_num)
theorem B1243973 : Blo 826349 1243973 := bbase (se 4 (by rfl) ⟨116622, by rfl⟩ : syracuseStep 1243973 = 233245) (by norm_num)
theorem B1866581 : Blo 826349 1866581 := bbase (se 9 (by rfl) ⟨5468, by rfl⟩ : syracuseStep 1866581 = 10937) (by norm_num)
theorem B1243997 : Blo 826349 1243997 := bbase (se 3 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 1243997 = 466499) (by norm_num)
theorem B1244021 : Blo 826349 1244021 := bbase (se 5 (by rfl) ⟨58313, by rfl⟩ : syracuseStep 1244021 = 116627) (by norm_num)
theorem B1047421 : Blo 826349 1047421 := bbase (se 3 (by rfl) ⟨196391, by rfl⟩ : syracuseStep 1047421 = 392783) (by norm_num)
theorem B1571717 : Blo 826349 1571717 := bbase (se 4 (by rfl) ⟨147348, by rfl⟩ : syracuseStep 1571717 = 294697) (by norm_num)
theorem B1244045 : Blo 826349 1244045 := bbase (se 3 (by rfl) ⟨233258, by rfl⟩ : syracuseStep 1244045 = 466517) (by norm_num)
theorem B1866653 : Blo 826349 1866653 := bbase (se 3 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 1866653 = 699995) (by norm_num)
theorem B1244069 : Blo 826349 1244069 := bbase (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) (by norm_num)
theorem B1244093 : Blo 826349 1244093 := bbase (se 3 (by rfl) ⟨233267, by rfl⟩ : syracuseStep 1244093 = 466535) (by norm_num)
theorem B2096077 : Blo 826349 2096077 := bbase (se 3 (by rfl) ⟨393014, by rfl⟩ : syracuseStep 2096077 = 786029) (by norm_num)
theorem B1244117 : Blo 826349 1244117 := bbase (se 7 (by rfl) ⟨14579, by rfl⟩ : syracuseStep 1244117 = 29159) (by norm_num)
theorem B1866725 : Blo 826349 1866725 := bbase (se 4 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 1866725 = 350011) (by norm_num)
theorem B1768429 : Blo 826349 1768429 := bbase (se 3 (by rfl) ⟨331580, by rfl⟩ : syracuseStep 1768429 = 663161) (by norm_num)
theorem B1244141 : Blo 826349 1244141 := bbase (se 3 (by rfl) ⟨233276, by rfl⟩ : syracuseStep 1244141 = 466553) (by norm_num)
theorem B1342469 : Blo 826349 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B1244165 : Blo 826349 1244165 := bbase (se 4 (by rfl) ⟨116640, by rfl⟩ : syracuseStep 1244165 = 233281) (by norm_num)
theorem B1571861 : Blo 826349 1571861 := bbase (se 6 (by rfl) ⟨36840, by rfl⟩ : syracuseStep 1571861 = 73681) (by norm_num)
theorem B1244189 : Blo 826349 1244189 := bbase (se 3 (by rfl) ⟨233285, by rfl⟩ : syracuseStep 1244189 = 466571) (by norm_num)
theorem B883753 : Blo 826349 883753 := bbase (se 2 (by rfl) ⟨331407, by rfl⟩ : syracuseStep 883753 = 662815) (by norm_num)
theorem B1047593 : Blo 826349 1047593 := bbase (se 2 (by rfl) ⟨392847, by rfl⟩ : syracuseStep 1047593 = 785695) (by norm_num)
theorem B1866797 : Blo 826349 1866797 := bbase (se 3 (by rfl) ⟨350024, by rfl⟩ : syracuseStep 1866797 = 700049) (by norm_num)
theorem B1244213 : Blo 826349 1244213 := bbase (se 5 (by rfl) ⟨58322, by rfl⟩ : syracuseStep 1244213 = 116645) (by norm_num)
theorem B2096189 : Blo 826349 2096189 := bbase (se 3 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 2096189 = 786071) (by norm_num)
theorem B1244237 : Blo 826349 1244237 := bbase (se 3 (by rfl) ⟨233294, by rfl⟩ : syracuseStep 1244237 = 466589) (by norm_num)
theorem B1047649 : Blo 826349 1047649 := bbase (se 2 (by rfl) ⟨392868, by rfl⟩ : syracuseStep 1047649 = 785737) (by norm_num)
theorem B1178725 : Blo 826349 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B1768549 : Blo 826349 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B1244261 : Blo 826349 1244261 := bbase (se 4 (by rfl) ⟨116649, by rfl⟩ : syracuseStep 1244261 = 233299) (by norm_num)
theorem B1866869 : Blo 826349 1866869 := bbase (se 5 (by rfl) ⟨87509, by rfl⟩ : syracuseStep 1866869 = 175019) (by norm_num)
theorem B1244285 : Blo 826349 1244285 := bbase (se 3 (by rfl) ⟨233303, by rfl⟩ : syracuseStep 1244285 = 466607) (by norm_num)
theorem B2522261 : Blo 826349 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B1244309 : Blo 826349 1244309 := bbase (se 6 (by rfl) ⟨29163, by rfl⟩ : syracuseStep 1244309 = 58327) (by norm_num)
theorem B883873 : Blo 826349 883873 := bbase (se 2 (by rfl) ⟨331452, by rfl⟩ : syracuseStep 883873 = 662905) (by norm_num)
theorem B1244333 : Blo 826349 1244333 := bbase (se 3 (by rfl) ⟨233312, by rfl⟩ : syracuseStep 1244333 = 466625) (by norm_num)
theorem B1866941 : Blo 826349 1866941 := bbase (se 3 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 1866941 = 700103) (by norm_num)
theorem B1047745 : Blo 826349 1047745 := bbase (se 2 (by rfl) ⟨392904, by rfl⟩ : syracuseStep 1047745 = 785809) (by norm_num)
theorem B1244357 : Blo 826349 1244357 := bbase (se 4 (by rfl) ⟨116658, by rfl⟩ : syracuseStep 1244357 = 233317) (by norm_num)
theorem B1244381 : Blo 826349 1244381 := bbase (se 3 (by rfl) ⟨233321, by rfl⟩ : syracuseStep 1244381 = 466643) (by norm_num)
theorem B1244405 : Blo 826349 1244405 := bbase (se 5 (by rfl) ⟨58331, by rfl⟩ : syracuseStep 1244405 = 116663) (by norm_num)
theorem B2096381 : Blo 826349 2096381 := bbase (se 3 (by rfl) ⟨393071, by rfl⟩ : syracuseStep 2096381 = 786143) (by norm_num)
theorem B1867013 : Blo 826349 1867013 := bbase (se 4 (by rfl) ⟨175032, by rfl⟩ : syracuseStep 1867013 = 350065) (by norm_num)
theorem B1244429 : Blo 826349 1244429 := bbase (se 3 (by rfl) ⟨233330, by rfl⟩ : syracuseStep 1244429 = 466661) (by norm_num)
theorem B1244453 : Blo 826349 1244453 := bbase (se 4 (by rfl) ⟨116667, by rfl⟩ : syracuseStep 1244453 = 233335) (by norm_num)
theorem B1572149 : Blo 826349 1572149 := bbase (se 5 (by rfl) ⟨73694, by rfl⟩ : syracuseStep 1572149 = 147389) (by norm_num)
theorem B3145013 : Blo 826349 3145013 := bbase (se 5 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 3145013 = 294845) (by norm_num)
theorem B1244477 : Blo 826349 1244477 := bbase (se 3 (by rfl) ⟨233339, by rfl⟩ : syracuseStep 1244477 = 466679) (by norm_num)
theorem B1867085 : Blo 826349 1867085 := bbase (se 3 (by rfl) ⟨350078, by rfl⟩ : syracuseStep 1867085 = 700157) (by norm_num)
theorem B1244501 : Blo 826349 1244501 := bbase (se 11 (by rfl) ⟨911, by rfl⟩ : syracuseStep 1244501 = 1823) (by norm_num)
theorem B1768805 : Blo 826349 1768805 := bbase (se 4 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 1768805 = 331651) (by norm_num)
theorem B1047917 : Blo 826349 1047917 := bbase (se 3 (by rfl) ⟨196484, by rfl⟩ : syracuseStep 1047917 = 392969) (by norm_num)
theorem B1244525 : Blo 826349 1244525 := bbase (se 3 (by rfl) ⟨233348, by rfl⟩ : syracuseStep 1244525 = 466697) (by norm_num)
theorem B1244549 : Blo 826349 1244549 := bbase (se 4 (by rfl) ⟨116676, by rfl⟩ : syracuseStep 1244549 = 233353) (by norm_num)
theorem B1867157 : Blo 826349 1867157 := bbase (se 6 (by rfl) ⟨43761, by rfl⟩ : syracuseStep 1867157 = 87523) (by norm_num)
theorem B884125 : Blo 826349 884125 := bbase (se 3 (by rfl) ⟨165773, by rfl⟩ : syracuseStep 884125 = 331547) (by norm_num)
theorem B1244573 : Blo 826349 1244573 := bbase (se 3 (by rfl) ⟨233357, by rfl⟩ : syracuseStep 1244573 = 466715) (by norm_num)
theorem B884129 : Blo 826349 884129 := bbase (se 2 (by rfl) ⟨331548, by rfl⟩ : syracuseStep 884129 = 663097) (by norm_num)
theorem B2981285 : Blo 826349 2981285 := bbase (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) (by norm_num)
theorem B1047973 : Blo 826349 1047973 := bbase (se 4 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 1047973 = 196495) (by norm_num)
theorem B1244597 : Blo 826349 1244597 := bbase (se 5 (by rfl) ⟨58340, by rfl⟩ : syracuseStep 1244597 = 116681) (by norm_num)
theorem B1572301 : Blo 826349 1572301 := bbase (se 3 (by rfl) ⟨294806, by rfl⟩ : syracuseStep 1572301 = 589613) (by norm_num)
theorem B1244621 : Blo 826349 1244621 := bbase (se 3 (by rfl) ⟨233366, by rfl⟩ : syracuseStep 1244621 = 466733) (by norm_num)
theorem B1867229 : Blo 826349 1867229 := bbase (se 3 (by rfl) ⟨350105, by rfl⟩ : syracuseStep 1867229 = 700211) (by norm_num)
theorem B1244645 : Blo 826349 1244645 := bbase (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) (by norm_num)
theorem B1703405 : Blo 826349 1703405 := bbase (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) (by norm_num)
theorem B1244669 : Blo 826349 1244669 := bbase (se 3 (by rfl) ⟨233375, by rfl⟩ : syracuseStep 1244669 = 466751) (by norm_num)
theorem B1048069 : Blo 826349 1048069 := bbase (se 4 (by rfl) ⟨98256, by rfl⟩ : syracuseStep 1048069 = 196513) (by norm_num)
theorem B1244693 : Blo 826349 1244693 := bbase (se 6 (by rfl) ⟨29172, by rfl⟩ : syracuseStep 1244693 = 58345) (by norm_num)
theorem B1867301 : Blo 826349 1867301 := bbase (se 4 (by rfl) ⟨175059, by rfl⟩ : syracuseStep 1867301 = 350119) (by norm_num)
theorem B1244717 : Blo 826349 1244717 := bbase (se 3 (by rfl) ⟨233384, by rfl⟩ : syracuseStep 1244717 = 466769) (by norm_num)
theorem B1244741 : Blo 826349 1244741 := bbase (se 4 (by rfl) ⟨116694, by rfl⟩ : syracuseStep 1244741 = 233389) (by norm_num)
theorem B2096725 : Blo 826349 2096725 := bbase (se 8 (by rfl) ⟨12285, by rfl⟩ : syracuseStep 2096725 = 24571) (by norm_num)
theorem B3145301 : Blo 826349 3145301 := bbase (se 8 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 3145301 = 36859) (by norm_num)
theorem B1244765 : Blo 826349 1244765 := bbase (se 3 (by rfl) ⟨233393, by rfl⟩ : syracuseStep 1244765 = 466787) (by norm_num)
theorem B1867373 : Blo 826349 1867373 := bbase (se 3 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 1867373 = 700265) (by norm_num)
theorem B1638005 : Blo 826349 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B1244789 : Blo 826349 1244789 := bbase (se 5 (by rfl) ⟨58349, by rfl⟩ : syracuseStep 1244789 = 116699) (by norm_num)
theorem B1244813 : Blo 826349 1244813 := bbase (se 3 (by rfl) ⟨233402, by rfl⟩ : syracuseStep 1244813 = 466805) (by norm_num)
theorem B1244837 : Blo 826349 1244837 := bbase (se 4 (by rfl) ⟨116703, by rfl⟩ : syracuseStep 1244837 = 233407) (by norm_num)
theorem B1048241 : Blo 826349 1048241 := bbase (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) (by norm_num)
theorem B1179317 : Blo 826349 1179317 := bbase (se 5 (by rfl) ⟨55280, by rfl⟩ : syracuseStep 1179317 = 110561) (by norm_num)
theorem B1867445 : Blo 826349 1867445 := bbase (se 5 (by rfl) ⟨87536, by rfl⟩ : syracuseStep 1867445 = 175073) (by norm_num)
theorem B1244861 : Blo 826349 1244861 := bbase (se 3 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 1244861 = 466823) (by norm_num)
theorem B2096837 : Blo 826349 2096837 := bbase (se 4 (by rfl) ⟨196578, by rfl⟩ : syracuseStep 2096837 = 393157) (by norm_num)
theorem B1244885 : Blo 826349 1244885 := bbase (se 7 (by rfl) ⟨14588, by rfl⟩ : syracuseStep 1244885 = 29177) (by norm_num)
theorem B1048297 : Blo 826349 1048297 := bbase (se 2 (by rfl) ⟨393111, by rfl⟩ : syracuseStep 1048297 = 786223) (by norm_num)
theorem B1244909 : Blo 826349 1244909 := bbase (se 3 (by rfl) ⟨233420, by rfl⟩ : syracuseStep 1244909 = 466841) (by norm_num)
theorem B1572605 : Blo 826349 1572605 := bbase (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) (by norm_num)
theorem B1867517 : Blo 826349 1867517 := bbase (se 3 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 1867517 = 700319) (by norm_num)
theorem B1179397 : Blo 826349 1179397 := bbase (se 4 (by rfl) ⟨110568, by rfl⟩ : syracuseStep 1179397 = 221137) (by norm_num)
theorem B1244933 : Blo 826349 1244933 := bbase (se 4 (by rfl) ⟨116712, by rfl⟩ : syracuseStep 1244933 = 233425) (by norm_num)
theorem B1244957 : Blo 826349 1244957 := bbase (se 3 (by rfl) ⟨233429, by rfl⟩ : syracuseStep 1244957 = 466859) (by norm_num)
theorem B1244981 : Blo 826349 1244981 := bbase (se 5 (by rfl) ⟨58358, by rfl⟩ : syracuseStep 1244981 = 116717) (by norm_num)
theorem B1867589 : Blo 826349 1867589 := bbase (se 4 (by rfl) ⟨175086, by rfl⟩ : syracuseStep 1867589 = 350173) (by norm_num)
theorem B1048393 : Blo 826349 1048393 := bbase (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) (by norm_num)
theorem B1245005 : Blo 826349 1245005 := bbase (se 3 (by rfl) ⟨233438, by rfl⟩ : syracuseStep 1245005 = 466877) (by norm_num)
theorem B851809 : Blo 826349 851809 := bbase (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) (by norm_num)
theorem B1245029 : Blo 826349 1245029 := bbase (se 4 (by rfl) ⟨116721, by rfl⟩ : syracuseStep 1245029 = 233443) (by norm_num)
theorem B1179517 : Blo 826349 1179517 := bbase (se 3 (by rfl) ⟨221159, by rfl⟩ : syracuseStep 1179517 = 442319) (by norm_num)
theorem B1245053 : Blo 826349 1245053 := bbase (se 3 (by rfl) ⟨233447, by rfl⟩ : syracuseStep 1245053 = 466895) (by norm_num)
theorem B2097029 : Blo 826349 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B1867661 : Blo 826349 1867661 := bbase (se 3 (by rfl) ⟨350186, by rfl⟩ : syracuseStep 1867661 = 700373) (by norm_num)
theorem B1245077 : Blo 826349 1245077 := bbase (se 6 (by rfl) ⟨29181, by rfl⟩ : syracuseStep 1245077 = 58363) (by norm_num)
theorem B1245101 : Blo 826349 1245101 := bbase (se 3 (by rfl) ⟨233456, by rfl⟩ : syracuseStep 1245101 = 466913) (by norm_num)
theorem B1245125 : Blo 826349 1245125 := bbase (se 4 (by rfl) ⟨116730, by rfl⟩ : syracuseStep 1245125 = 233461) (by norm_num)
theorem B884693 : Blo 826349 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B1867733 : Blo 826349 1867733 := bbase (se 7 (by rfl) ⟨21887, by rfl⟩ : syracuseStep 1867733 = 43775) (by norm_num)
theorem B1179613 : Blo 826349 1179613 := bbase (se 3 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 1179613 = 442355) (by norm_num)
theorem B1245149 : Blo 826349 1245149 := bbase (se 3 (by rfl) ⟨233465, by rfl⟩ : syracuseStep 1245149 = 466931) (by norm_num)
theorem B1048565 : Blo 826349 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B1245173 : Blo 826349 1245173 := bbase (se 5 (by rfl) ⟨58367, by rfl⟩ : syracuseStep 1245173 = 116735) (by norm_num)
theorem B1245185 : Blo 826349 1245185 := bstep (se 2 (by rfl) ⟨466944, by rfl⟩ : syracuseStep 1245185 = 933889) B933889
theorem B2654221 : Blo 826349 2654221 := bstep (se 3 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 2654221 = 995333) B995333
theorem B1245203 : Blo 826349 1245203 := bstep (se 1 (by rfl) ⟨933902, by rfl⟩ : syracuseStep 1245203 = 1867805) B1867805
theorem B1245233 : Blo 826349 1245233 := bstep (se 2 (by rfl) ⟨466962, by rfl⟩ : syracuseStep 1245233 = 933925) B933925
theorem B2359363 : Blo 826349 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B1245251 : Blo 826349 1245251 := bstep (se 1 (by rfl) ⟨933938, by rfl⟩ : syracuseStep 1245251 = 1867877) B1867877
theorem B1245281 : Blo 826349 1245281 := bstep (se 2 (by rfl) ⟨466980, by rfl⟩ : syracuseStep 1245281 = 933961) B933961
theorem B1245299 : Blo 826349 1245299 := bstep (se 1 (by rfl) ⟨933974, by rfl⟩ : syracuseStep 1245299 = 1867949) B1867949
theorem B1769617 : Blo 826349 1769617 := bstep (se 2 (by rfl) ⟨663606, by rfl⟩ : syracuseStep 1769617 = 1327213) B1327213
theorem B1245329 : Blo 826349 1245329 := bstep (se 2 (by rfl) ⟨466998, by rfl⟩ : syracuseStep 1245329 = 933997) B933997
theorem B1245347 : Blo 826349 1245347 := bstep (se 1 (by rfl) ⟨934010, by rfl⟩ : syracuseStep 1245347 = 1868021) B1868021
theorem B2130097 : Blo 826349 2130097 := bstep (se 2 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 2130097 = 1597573) B1597573
theorem B1179841 : Blo 826349 1179841 := bstep (se 2 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 1179841 = 884881) B884881
theorem B1245377 : Blo 826349 1245377 := bstep (se 2 (by rfl) ⟨467016, by rfl⟩ : syracuseStep 1245377 = 934033) B934033
theorem B1867985 : Blo 826349 1867985 := bstep (se 2 (by rfl) ⟨700494, by rfl⟩ : syracuseStep 1867985 = 1400989) B1400989
theorem B1245395 : Blo 826349 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B40337621 : Blo 826349 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B2359523 : Blo 826349 2359523 := bstep (se 1 (by rfl) ⟨1769642, by rfl⟩ : syracuseStep 2359523 = 3539285) B3539285
theorem B1573091 : Blo 826349 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1868003 : Blo 826349 1868003 := bstep (se 1 (by rfl) ⟨1401002, by rfl⟩ : syracuseStep 1868003 = 2802005) B2802005
theorem B1245425 : Blo 826349 1245425 := bstep (se 2 (by rfl) ⟨467034, by rfl⟩ : syracuseStep 1245425 = 934069) B934069
theorem B1245443 : Blo 826349 1245443 := bstep (se 1 (by rfl) ⟨934082, by rfl⟩ : syracuseStep 1245443 = 1868165) B1868165
theorem B1245473 : Blo 826349 1245473 := bstep (se 2 (by rfl) ⟨467052, by rfl⟩ : syracuseStep 1245473 = 934105) B934105
theorem B1179955 : Blo 826349 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B1245491 : Blo 826349 1245491 := bstep (se 1 (by rfl) ⟨934118, by rfl⟩ : syracuseStep 1245491 = 1868237) B1868237
theorem B1245521 : Blo 826349 1245521 := bstep (se 2 (by rfl) ⟨467070, by rfl⟩ : syracuseStep 1245521 = 934141) B934141
theorem B2425265 : Blo 826349 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B2654669 : Blo 826349 2654669 := bstep (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) B995501
theorem B1868273 : Blo 826349 1868273 := bstep (se 2 (by rfl) ⟨700602, by rfl⟩ : syracuseStep 1868273 = 1401205) B1401205
theorem B1049107 : Blo 826349 1049107 := bstep (se 1 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 1049107 = 1573661) B1573661
theorem B11960885 : Blo 826349 11960885 := bstep (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) B1121333
theorem B4719181 : Blo 826349 4719181 := bstep (se 3 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 4719181 = 1769693) B1769693
theorem B7078499 : Blo 826349 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B2523757 : Blo 826349 2523757 := bstep (se 3 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 2523757 = 946409) B946409
theorem B1049203 : Blo 826349 1049203 := bstep (se 1 (by rfl) ⟨786902, by rfl⟩ : syracuseStep 1049203 = 1573805) B1573805
theorem B2097809 : Blo 826349 2097809 := bstep (se 2 (by rfl) ⟨786678, by rfl⟩ : syracuseStep 2097809 = 1573357) B1573357
theorem B2097859 : Blo 826349 2097859 := bstep (se 1 (by rfl) ⟨1573394, by rfl⟩ : syracuseStep 2097859 = 3146789) B3146789
theorem B1770275 : Blo 826349 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B885539 : Blo 826349 885539 := bstep (se 1 (by rfl) ⟨664154, by rfl⟩ : syracuseStep 885539 = 1328309) B1328309
theorem B2098001 : Blo 826349 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B1344497 : Blo 826349 1344497 := bstep (se 2 (by rfl) ⟨504186, by rfl⟩ : syracuseStep 1344497 = 1008373) B1008373
theorem B4195313 : Blo 826349 4195313 := bstep (se 2 (by rfl) ⟨1573242, by rfl⟩ : syracuseStep 4195313 = 3146485) B3146485
theorem B5309489 : Blo 826349 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B2589763 : Blo 826349 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B1573987 : Blo 826349 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B1049699 : Blo 826349 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B3146957 : Blo 826349 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B1574147 : Blo 826349 1574147 := bstep (se 1 (by rfl) ⟨1180610, by rfl⟩ : syracuseStep 1574147 = 2361221) B2361221
theorem B2360593 : Blo 826349 2360593 := bstep (se 2 (by rfl) ⟨885222, by rfl⟩ : syracuseStep 2360593 = 1770445) B1770445
theorem B1771121 : Blo 826349 1771121 := bstep (se 2 (by rfl) ⟨664170, by rfl⟩ : syracuseStep 1771121 = 1328341) B1328341
theorem B1181299 : Blo 826349 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B5310157 : Blo 826349 5310157 := bstep (se 3 (by rfl) ⟨995654, by rfl⟩ : syracuseStep 5310157 = 1991309) B1991309
theorem B3540685 : Blo 826349 3540685 := bstep (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) B1327757
theorem B1050403 : Blo 826349 1050403 := bstep (se 1 (by rfl) ⟨787802, by rfl⟩ : syracuseStep 1050403 = 1575605) B1575605
theorem B2098993 : Blo 826349 2098993 := bstep (se 2 (by rfl) ⟨787122, by rfl⟩ : syracuseStep 2098993 = 1574245) B1574245
theorem B1050499 : Blo 826349 1050499 := bstep (se 1 (by rfl) ⟨787874, by rfl⟩ : syracuseStep 1050499 = 1575749) B1575749
theorem B886675 : Blo 826349 886675 := bstep (se 1 (by rfl) ⟨665006, by rfl⟩ : syracuseStep 886675 = 1330013) B1330013
theorem B3147761 : Blo 826349 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B2099267 : Blo 826349 2099267 := bstep (se 1 (by rfl) ⟨1574450, by rfl⟩ : syracuseStep 2099267 = 3148901) B3148901
theorem B21006449 : Blo 826349 21006449 := bstep (se 2 (by rfl) ⟨7877418, by rfl⟩ : syracuseStep 21006449 = 15754837) B15754837
theorem B2099459 : Blo 826349 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B1575217 : Blo 826349 1575217 := bstep (se 2 (by rfl) ⟨590706, by rfl⟩ : syracuseStep 1575217 = 1181413) B1181413
theorem B4196771 : Blo 826349 4196771 := bstep (se 1 (by rfl) ⟨3147578, by rfl⟩ : syracuseStep 4196771 = 6295157) B6295157
theorem B4721165 : Blo 826349 4721165 := bstep (se 3 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 4721165 = 1770437) B1770437
theorem B2361869 : Blo 826349 2361869 := bstep (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) B885701
theorem B3148429 : Blo 826349 3148429 := bstep (se 3 (by rfl) ⟨590330, by rfl⟩ : syracuseStep 3148429 = 1180661) B1180661
theorem B2362051 : Blo 826349 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B3541745 : Blo 826349 3541745 := bstep (se 2 (by rfl) ⟨1328154, by rfl⟩ : syracuseStep 3541745 = 2656309) B2656309
theorem B2362097 : Blo 826349 2362097 := bstep (se 2 (by rfl) ⟨885786, by rfl⟩ : syracuseStep 2362097 = 1771573) B1771573
theorem B2984845 : Blo 826349 2984845 := bstep (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) B1119317
theorem B1117073 : Blo 826349 1117073 := bstep (se 2 (by rfl) ⟨418902, by rfl⟩ : syracuseStep 1117073 = 837805) B837805
theorem B2657411 : Blo 826349 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B2100401 : Blo 826349 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B4197581 : Blo 826349 4197581 := bstep (se 3 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 4197581 = 1574093) B1574093
theorem B2100451 : Blo 826349 2100451 := bstep (se 1 (by rfl) ⟨1575338, by rfl⟩ : syracuseStep 2100451 = 3150677) B3150677
theorem B2657539 : Blo 826349 2657539 := bstep (se 1 (by rfl) ⟨1993154, by rfl⟩ : syracuseStep 2657539 = 3986309) B3986309
theorem B1772803 : Blo 826349 1772803 := bstep (se 1 (by rfl) ⟨1329602, by rfl⟩ : syracuseStep 1772803 = 2659205) B2659205
theorem B1346881 : Blo 826349 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B1576273 : Blo 826349 1576273 := bstep (se 2 (by rfl) ⟨591102, by rfl⟩ : syracuseStep 1576273 = 1182205) B1182205
theorem B2100593 : Blo 826349 2100593 := bstep (se 2 (by rfl) ⟨787722, by rfl⟩ : syracuseStep 2100593 = 1575445) B1575445
theorem B3149219 : Blo 826349 3149219 := bstep (se 1 (by rfl) ⟨2361914, by rfl⟩ : syracuseStep 3149219 = 4723829) B4723829
theorem B4722097 : Blo 826349 4722097 := bstep (se 2 (by rfl) ⟨1770786, by rfl⟩ : syracuseStep 4722097 = 3541573) B3541573
theorem B11505077 : Blo 826349 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B2657873 : Blo 826349 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B5049989 : Blo 826349 5049989 := bstep (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) B946873
theorem B1117891 : Blo 826349 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B1773265 : Blo 826349 1773265 := bstep (se 2 (by rfl) ⟨664974, by rfl⟩ : syracuseStep 1773265 = 1329949) B1329949
theorem B2789261 : Blo 826349 2789261 := bstep (se 3 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 2789261 = 1045973) B1045973
theorem B2789315 : Blo 826349 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B3149873 : Blo 826349 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B18157709 : Blo 826349 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B2363555 : Blo 826349 2363555 := bstep (se 1 (by rfl) ⟨1772666, by rfl⟩ : syracuseStep 2363555 = 3545333) B3545333
theorem B2789585 : Blo 826349 2789585 := bstep (se 2 (by rfl) ⟨1046094, by rfl⟩ : syracuseStep 2789585 = 2092189) B2092189
theorem B23892245 : Blo 826349 23892245 := bstep (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) B1119949
theorem B2101585 : Blo 826349 2101585 := bstep (se 2 (by rfl) ⟨788094, by rfl⟩ : syracuseStep 2101585 = 1576189) B1576189
theorem B1413715 : Blo 826349 1413715 := bstep (se 1 (by rfl) ⟨1060286, by rfl⟩ : syracuseStep 1413715 = 2120573) B2120573
theorem B20189837 : Blo 826349 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B2790125 : Blo 826349 2790125 := bstep (se 3 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 2790125 = 1046297) B1046297
theorem B2790179 : Blo 826349 2790179 := bstep (se 1 (by rfl) ⟨2092634, by rfl⟩ : syracuseStep 2790179 = 4185269) B4185269
theorem B4723555 : Blo 826349 4723555 := bstep (se 1 (by rfl) ⟨3542666, by rfl⟩ : syracuseStep 4723555 = 7085333) B7085333
theorem B8950769 : Blo 826349 8950769 := bstep (se 2 (by rfl) ⟨3356538, by rfl⟩ : syracuseStep 8950769 = 6713077) B6713077
theorem B1676323 : Blo 826349 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B2790449 : Blo 826349 2790449 := bstep (se 2 (by rfl) ⟨1046418, by rfl⟩ : syracuseStep 2790449 = 2092837) B2092837
theorem B1119377 : Blo 826349 1119377 := bstep (se 2 (by rfl) ⟨419766, by rfl⟩ : syracuseStep 1119377 = 839533) B839533
theorem B4724081 : Blo 826349 4724081 := bstep (se 2 (by rfl) ⟨1771530, by rfl⟩ : syracuseStep 4724081 = 3543061) B3543061
theorem B10065293 : Blo 826349 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B3151331 : Blo 826349 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B3151345 : Blo 826349 3151345 := bstep (se 2 (by rfl) ⟨1181754, by rfl⟩ : syracuseStep 3151345 = 2363509) B2363509
theorem B6297101 : Blo 826349 6297101 := bstep (se 3 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 6297101 = 2361413) B2361413
theorem B2790989 : Blo 826349 2790989 := bstep (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) B1046621
theorem B2791043 : Blo 826349 2791043 := bstep (se 1 (by rfl) ⟨2093282, by rfl⟩ : syracuseStep 2791043 = 4186565) B4186565
theorem B3544717 : Blo 826349 3544717 := bstep (se 3 (by rfl) ⟨664634, by rfl⟩ : syracuseStep 3544717 = 1329269) B1329269
theorem B5379853 : Blo 826349 5379853 := bstep (se 3 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 5379853 = 2017445) B2017445
theorem B14718773 : Blo 826349 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B2791313 : Blo 826349 2791313 := bstep (se 2 (by rfl) ⟨1046742, by rfl⟩ : syracuseStep 2791313 = 2093485) B2093485
theorem B15112163 : Blo 826349 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B3545059 : Blo 826349 3545059 := bstep (se 1 (by rfl) ⟨2658794, by rfl⟩ : syracuseStep 3545059 = 5317589) B5317589
theorem B4200497 : Blo 826349 4200497 := bstep (se 2 (by rfl) ⟨1575186, by rfl⟩ : syracuseStep 4200497 = 3150373) B3150373
theorem B8493283 : Blo 826349 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B2267459 : Blo 826349 2267459 := bstep (se 1 (by rfl) ⟨1700594, by rfl⟩ : syracuseStep 2267459 = 3401189) B3401189
theorem B2791853 : Blo 826349 2791853 := bstep (se 3 (by rfl) ⟨523472, by rfl⟩ : syracuseStep 2791853 = 1046945) B1046945
theorem B2791907 : Blo 826349 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B4790755 : Blo 826349 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B2792177 : Blo 826349 2792177 := bstep (se 2 (by rfl) ⟨1047066, by rfl⟩ : syracuseStep 2792177 = 2094133) B2094133
theorem B4725539 : Blo 826349 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B2235185 : Blo 826349 2235185 := bstep (se 2 (by rfl) ⟨838194, by rfl⟩ : syracuseStep 2235185 = 1676389) B1676389
theorem B826355 : Blo 826349 826355 := bstep (se 1 (by rfl) ⟨619766, by rfl⟩ : syracuseStep 826355 = 1239533) B1239533
theorem B826371 : Blo 826349 826371 := bstep (se 1 (by rfl) ⟨619778, by rfl⟩ : syracuseStep 826371 = 1239557) B1239557
theorem B826387 : Blo 826349 826387 := bstep (se 1 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 826387 = 1239581) B1239581
theorem B826403 : Blo 826349 826403 := bstep (se 1 (by rfl) ⟨619802, by rfl⟩ : syracuseStep 826403 = 1239605) B1239605
theorem B826419 : Blo 826349 826419 := bstep (se 1 (by rfl) ⟨619814, by rfl⟩ : syracuseStep 826419 = 1239629) B1239629
theorem B826435 : Blo 826349 826435 := bstep (se 1 (by rfl) ⟨619826, by rfl⟩ : syracuseStep 826435 = 1239653) B1239653
theorem B826451 : Blo 826349 826451 := bstep (se 1 (by rfl) ⟨619838, by rfl⟩ : syracuseStep 826451 = 1239677) B1239677
theorem B826467 : Blo 826349 826467 := bstep (se 1 (by rfl) ⟨619850, by rfl⟩ : syracuseStep 826467 = 1239701) B1239701
theorem B826483 : Blo 826349 826483 := bstep (se 1 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 826483 = 1239725) B1239725
theorem B826499 : Blo 826349 826499 := bstep (se 1 (by rfl) ⟨619874, by rfl⟩ : syracuseStep 826499 = 1239749) B1239749
theorem B826515 : Blo 826349 826515 := bstep (se 1 (by rfl) ⟨619886, by rfl⟩ : syracuseStep 826515 = 1239773) B1239773
theorem B826531 : Blo 826349 826531 := bstep (se 1 (by rfl) ⟨619898, by rfl⟩ : syracuseStep 826531 = 1239797) B1239797
theorem B826547 : Blo 826349 826547 := bstep (se 1 (by rfl) ⟨619910, by rfl⟩ : syracuseStep 826547 = 1239821) B1239821
theorem B826563 : Blo 826349 826563 := bstep (se 1 (by rfl) ⟨619922, by rfl⟩ : syracuseStep 826563 = 1239845) B1239845
theorem B826579 : Blo 826349 826579 := bstep (se 1 (by rfl) ⟨619934, by rfl⟩ : syracuseStep 826579 = 1239869) B1239869
theorem B826595 : Blo 826349 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B2268397 : Blo 826349 2268397 := bstep (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) B850649
theorem B826611 : Blo 826349 826611 := bstep (se 1 (by rfl) ⟨619958, by rfl⟩ : syracuseStep 826611 = 1239917) B1239917
theorem B826627 : Blo 826349 826627 := bstep (se 1 (by rfl) ⟨619970, by rfl⟩ : syracuseStep 826627 = 1239941) B1239941
theorem B2792717 : Blo 826349 2792717 := bstep (se 3 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 2792717 = 1047269) B1047269
theorem B826643 : Blo 826349 826643 := bstep (se 1 (by rfl) ⟨619982, by rfl⟩ : syracuseStep 826643 = 1239965) B1239965
theorem B826659 : Blo 826349 826659 := bstep (se 1 (by rfl) ⟨619994, by rfl⟩ : syracuseStep 826659 = 1239989) B1239989
theorem B826675 : Blo 826349 826675 := bstep (se 1 (by rfl) ⟨620006, by rfl⟩ : syracuseStep 826675 = 1240013) B1240013
theorem B826691 : Blo 826349 826691 := bstep (se 1 (by rfl) ⟨620018, by rfl⟩ : syracuseStep 826691 = 1240037) B1240037
theorem B2792771 : Blo 826349 2792771 := bstep (se 1 (by rfl) ⟨2094578, by rfl⟩ : syracuseStep 2792771 = 4189157) B4189157
theorem B826707 : Blo 826349 826707 := bstep (se 1 (by rfl) ⟨620030, by rfl⟩ : syracuseStep 826707 = 1240061) B1240061
theorem B826723 : Blo 826349 826723 := bstep (se 1 (by rfl) ⟨620042, by rfl⟩ : syracuseStep 826723 = 1240085) B1240085
theorem B826739 : Blo 826349 826739 := bstep (se 1 (by rfl) ⟨620054, by rfl⟩ : syracuseStep 826739 = 1240109) B1240109
theorem B826755 : Blo 826349 826755 := bstep (se 1 (by rfl) ⟨620066, by rfl⟩ : syracuseStep 826755 = 1240133) B1240133
theorem B826771 : Blo 826349 826771 := bstep (se 1 (by rfl) ⟨620078, by rfl⟩ : syracuseStep 826771 = 1240157) B1240157
theorem B826787 : Blo 826349 826787 := bstep (se 1 (by rfl) ⟨620090, by rfl⟩ : syracuseStep 826787 = 1240181) B1240181
theorem B826803 : Blo 826349 826803 := bstep (se 1 (by rfl) ⟨620102, by rfl⟩ : syracuseStep 826803 = 1240205) B1240205
theorem B826819 : Blo 826349 826819 := bstep (se 1 (by rfl) ⟨620114, by rfl⟩ : syracuseStep 826819 = 1240229) B1240229
theorem B826835 : Blo 826349 826835 := bstep (se 1 (by rfl) ⟨620126, by rfl⟩ : syracuseStep 826835 = 1240253) B1240253
theorem B826851 : Blo 826349 826851 := bstep (se 1 (by rfl) ⟨620138, by rfl⟩ : syracuseStep 826851 = 1240277) B1240277
theorem B4201955 : Blo 826349 4201955 := bstep (se 1 (by rfl) ⟨3151466, by rfl⟩ : syracuseStep 4201955 = 6302933) B6302933
theorem B826867 : Blo 826349 826867 := bstep (se 1 (by rfl) ⟨620150, by rfl⟩ : syracuseStep 826867 = 1240301) B1240301
theorem B826883 : Blo 826349 826883 := bstep (se 1 (by rfl) ⟨620162, by rfl⟩ : syracuseStep 826883 = 1240325) B1240325
theorem B826899 : Blo 826349 826899 := bstep (se 1 (by rfl) ⟨620174, by rfl⟩ : syracuseStep 826899 = 1240349) B1240349
theorem B826915 : Blo 826349 826915 := bstep (se 1 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 826915 = 1240373) B1240373
theorem B826931 : Blo 826349 826931 := bstep (se 1 (by rfl) ⟨620198, by rfl⟩ : syracuseStep 826931 = 1240397) B1240397
theorem B826947 : Blo 826349 826947 := bstep (se 1 (by rfl) ⟨620210, by rfl⟩ : syracuseStep 826947 = 1240421) B1240421
theorem B2793041 : Blo 826349 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B826963 : Blo 826349 826963 := bstep (se 1 (by rfl) ⟨620222, by rfl⟩ : syracuseStep 826963 = 1240445) B1240445
theorem B826979 : Blo 826349 826979 := bstep (se 1 (by rfl) ⟨620234, by rfl⟩ : syracuseStep 826979 = 1240469) B1240469
theorem B826995 : Blo 826349 826995 := bstep (se 1 (by rfl) ⟨620246, by rfl⟩ : syracuseStep 826995 = 1240493) B1240493
theorem B827011 : Blo 826349 827011 := bstep (se 1 (by rfl) ⟨620258, by rfl⟩ : syracuseStep 827011 = 1240517) B1240517
theorem B10198669 : Blo 826349 10198669 := bstep (se 3 (by rfl) ⟨1912250, by rfl⟩ : syracuseStep 10198669 = 3824501) B3824501
theorem B827027 : Blo 826349 827027 := bstep (se 1 (by rfl) ⟨620270, by rfl⟩ : syracuseStep 827027 = 1240541) B1240541
theorem B827043 : Blo 826349 827043 := bstep (se 1 (by rfl) ⟨620282, by rfl⟩ : syracuseStep 827043 = 1240565) B1240565
theorem B827059 : Blo 826349 827059 := bstep (se 1 (by rfl) ⟨620294, by rfl⟩ : syracuseStep 827059 = 1240589) B1240589
theorem B827075 : Blo 826349 827075 := bstep (se 1 (by rfl) ⟨620306, by rfl⟩ : syracuseStep 827075 = 1240613) B1240613
theorem B827091 : Blo 826349 827091 := bstep (se 1 (by rfl) ⟨620318, by rfl⟩ : syracuseStep 827091 = 1240637) B1240637
theorem B827107 : Blo 826349 827107 := bstep (se 1 (by rfl) ⟨620330, by rfl⟩ : syracuseStep 827107 = 1240661) B1240661
theorem B827123 : Blo 826349 827123 := bstep (se 1 (by rfl) ⟨620342, by rfl⟩ : syracuseStep 827123 = 1240685) B1240685
theorem B827139 : Blo 826349 827139 := bstep (se 1 (by rfl) ⟨620354, by rfl⟩ : syracuseStep 827139 = 1240709) B1240709
theorem B827155 : Blo 826349 827155 := bstep (se 1 (by rfl) ⟨620366, by rfl⟩ : syracuseStep 827155 = 1240733) B1240733
theorem B827171 : Blo 826349 827171 := bstep (se 1 (by rfl) ⟨620378, by rfl⟩ : syracuseStep 827171 = 1240757) B1240757
theorem B827187 : Blo 826349 827187 := bstep (se 1 (by rfl) ⟨620390, by rfl⟩ : syracuseStep 827187 = 1240781) B1240781
theorem B827203 : Blo 826349 827203 := bstep (se 1 (by rfl) ⟨620402, by rfl⟩ : syracuseStep 827203 = 1240805) B1240805
theorem B827219 : Blo 826349 827219 := bstep (se 1 (by rfl) ⟨620414, by rfl⟩ : syracuseStep 827219 = 1240829) B1240829
theorem B827235 : Blo 826349 827235 := bstep (se 1 (by rfl) ⟨620426, by rfl⟩ : syracuseStep 827235 = 1240853) B1240853
theorem B827251 : Blo 826349 827251 := bstep (se 1 (by rfl) ⟨620438, by rfl⟩ : syracuseStep 827251 = 1240877) B1240877
theorem B827267 : Blo 826349 827267 := bstep (se 1 (by rfl) ⟨620450, by rfl⟩ : syracuseStep 827267 = 1240901) B1240901
theorem B827283 : Blo 826349 827283 := bstep (se 1 (by rfl) ⟨620462, by rfl⟩ : syracuseStep 827283 = 1240925) B1240925
theorem B827299 : Blo 826349 827299 := bstep (se 1 (by rfl) ⟨620474, by rfl⟩ : syracuseStep 827299 = 1240949) B1240949
theorem B5316515 : Blo 826349 5316515 := bstep (se 1 (by rfl) ⟨3987386, by rfl⟩ : syracuseStep 5316515 = 7974773) B7974773
theorem B827315 : Blo 826349 827315 := bstep (se 1 (by rfl) ⟨620486, by rfl⟩ : syracuseStep 827315 = 1240973) B1240973
theorem B827331 : Blo 826349 827331 := bstep (se 1 (by rfl) ⟨620498, by rfl⟩ : syracuseStep 827331 = 1240997) B1240997
theorem B827347 : Blo 826349 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B827363 : Blo 826349 827363 := bstep (se 1 (by rfl) ⟨620522, by rfl⟩ : syracuseStep 827363 = 1241045) B1241045
theorem B827379 : Blo 826349 827379 := bstep (se 1 (by rfl) ⟨620534, by rfl⟩ : syracuseStep 827379 = 1241069) B1241069
theorem B827395 : Blo 826349 827395 := bstep (se 1 (by rfl) ⟨620546, by rfl⟩ : syracuseStep 827395 = 1241093) B1241093
theorem B3579917 : Blo 826349 3579917 := bstep (se 3 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 3579917 = 1342469) B1342469
theorem B827411 : Blo 826349 827411 := bstep (se 1 (by rfl) ⟨620558, by rfl⟩ : syracuseStep 827411 = 1241117) B1241117
theorem B827427 : Blo 826349 827427 := bstep (se 1 (by rfl) ⟨620570, by rfl⟩ : syracuseStep 827427 = 1241141) B1241141
theorem B827443 : Blo 826349 827443 := bstep (se 1 (by rfl) ⟨620582, by rfl⟩ : syracuseStep 827443 = 1241165) B1241165
theorem B827459 : Blo 826349 827459 := bstep (se 1 (by rfl) ⟨620594, by rfl⟩ : syracuseStep 827459 = 1241189) B1241189
theorem B827475 : Blo 826349 827475 := bstep (se 1 (by rfl) ⟨620606, by rfl⟩ : syracuseStep 827475 = 1241213) B1241213
theorem B827491 : Blo 826349 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B2793581 : Blo 826349 2793581 := bstep (se 3 (by rfl) ⟨523796, by rfl⟩ : syracuseStep 2793581 = 1047593) B1047593
theorem B827507 : Blo 826349 827507 := bstep (se 1 (by rfl) ⟨620630, by rfl⟩ : syracuseStep 827507 = 1241261) B1241261
theorem B827523 : Blo 826349 827523 := bstep (se 1 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 827523 = 1241285) B1241285
theorem B827539 : Blo 826349 827539 := bstep (se 1 (by rfl) ⟨620654, by rfl⟩ : syracuseStep 827539 = 1241309) B1241309
theorem B827555 : Blo 826349 827555 := bstep (se 1 (by rfl) ⟨620666, by rfl⟩ : syracuseStep 827555 = 1241333) B1241333
theorem B2793635 : Blo 826349 2793635 := bstep (se 1 (by rfl) ⟨2095226, by rfl⟩ : syracuseStep 2793635 = 4190453) B4190453
theorem B827571 : Blo 826349 827571 := bstep (se 1 (by rfl) ⟨620678, by rfl⟩ : syracuseStep 827571 = 1241357) B1241357
theorem B827587 : Blo 826349 827587 := bstep (se 1 (by rfl) ⟨620690, by rfl⟩ : syracuseStep 827587 = 1241381) B1241381
theorem B827603 : Blo 826349 827603 := bstep (se 1 (by rfl) ⟨620702, by rfl⟩ : syracuseStep 827603 = 1241405) B1241405
theorem B827619 : Blo 826349 827619 := bstep (se 1 (by rfl) ⟨620714, by rfl⟩ : syracuseStep 827619 = 1241429) B1241429
theorem B827635 : Blo 826349 827635 := bstep (se 1 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 827635 = 1241453) B1241453
theorem B1417459 : Blo 826349 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B827651 : Blo 826349 827651 := bstep (se 1 (by rfl) ⟨620738, by rfl⟩ : syracuseStep 827651 = 1241477) B1241477
theorem B4202765 : Blo 826349 4202765 := bstep (se 3 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 4202765 = 1576037) B1576037
theorem B827667 : Blo 826349 827667 := bstep (se 1 (by rfl) ⟨620750, by rfl⟩ : syracuseStep 827667 = 1241501) B1241501
theorem B827683 : Blo 826349 827683 := bstep (se 1 (by rfl) ⟨620762, by rfl⟩ : syracuseStep 827683 = 1241525) B1241525
theorem B827699 : Blo 826349 827699 := bstep (se 1 (by rfl) ⟨620774, by rfl⟩ : syracuseStep 827699 = 1241549) B1241549
theorem B827715 : Blo 826349 827715 := bstep (se 1 (by rfl) ⟨620786, by rfl⟩ : syracuseStep 827715 = 1241573) B1241573
theorem B827731 : Blo 826349 827731 := bstep (se 1 (by rfl) ⟨620798, by rfl⟩ : syracuseStep 827731 = 1241597) B1241597
theorem B827747 : Blo 826349 827747 := bstep (se 1 (by rfl) ⟨620810, by rfl⟩ : syracuseStep 827747 = 1241621) B1241621
theorem B6300017 : Blo 826349 6300017 := bstep (se 2 (by rfl) ⟨2362506, by rfl⟩ : syracuseStep 6300017 = 4725013) B4725013
theorem B827763 : Blo 826349 827763 := bstep (se 1 (by rfl) ⟨620822, by rfl⟩ : syracuseStep 827763 = 1241645) B1241645
theorem B827779 : Blo 826349 827779 := bstep (se 1 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 827779 = 1241669) B1241669
theorem B827795 : Blo 826349 827795 := bstep (se 1 (by rfl) ⟨620846, by rfl⟩ : syracuseStep 827795 = 1241693) B1241693
theorem B827811 : Blo 826349 827811 := bstep (se 1 (by rfl) ⟨620858, by rfl⟩ : syracuseStep 827811 = 1241717) B1241717
theorem B2793905 : Blo 826349 2793905 := bstep (se 2 (by rfl) ⟨1047714, by rfl⟩ : syracuseStep 2793905 = 2095429) B2095429
theorem B827827 : Blo 826349 827827 := bstep (se 1 (by rfl) ⟨620870, by rfl⟩ : syracuseStep 827827 = 1241741) B1241741
theorem B827843 : Blo 826349 827843 := bstep (se 1 (by rfl) ⟨620882, by rfl⟩ : syracuseStep 827843 = 1241765) B1241765
theorem B827859 : Blo 826349 827859 := bstep (se 1 (by rfl) ⟨620894, by rfl⟩ : syracuseStep 827859 = 1241789) B1241789
theorem B827875 : Blo 826349 827875 := bstep (se 1 (by rfl) ⟨620906, by rfl⟩ : syracuseStep 827875 = 1241813) B1241813
theorem B827891 : Blo 826349 827891 := bstep (se 1 (by rfl) ⟨620918, by rfl⟩ : syracuseStep 827891 = 1241837) B1241837
theorem B827907 : Blo 826349 827907 := bstep (se 1 (by rfl) ⟨620930, by rfl⟩ : syracuseStep 827907 = 1241861) B1241861
theorem B5677573 : Blo 826349 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B827923 : Blo 826349 827923 := bstep (se 1 (by rfl) ⟨620942, by rfl⟩ : syracuseStep 827923 = 1241885) B1241885
theorem B827939 : Blo 826349 827939 := bstep (se 1 (by rfl) ⟨620954, by rfl⟩ : syracuseStep 827939 = 1241909) B1241909
theorem B3351089 : Blo 826349 3351089 := bstep (se 2 (by rfl) ⟨1256658, by rfl⟩ : syracuseStep 3351089 = 2513317) B2513317
theorem B827955 : Blo 826349 827955 := bstep (se 1 (by rfl) ⟨620966, by rfl⟩ : syracuseStep 827955 = 1241933) B1241933
theorem B17932853 : Blo 826349 17932853 := bstep (se 5 (by rfl) ⟨840602, by rfl⟩ : syracuseStep 17932853 = 1681205) B1681205
theorem B827971 : Blo 826349 827971 := bstep (se 1 (by rfl) ⟨620978, by rfl⟩ : syracuseStep 827971 = 1241957) B1241957
theorem B827987 : Blo 826349 827987 := bstep (se 1 (by rfl) ⟨620990, by rfl⟩ : syracuseStep 827987 = 1241981) B1241981
theorem B828003 : Blo 826349 828003 := bstep (se 1 (by rfl) ⟨621002, by rfl⟩ : syracuseStep 828003 = 1242005) B1242005
theorem B828019 : Blo 826349 828019 := bstep (se 1 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 828019 = 1242029) B1242029
theorem B828035 : Blo 826349 828035 := bstep (se 1 (by rfl) ⟨621026, by rfl⟩ : syracuseStep 828035 = 1242053) B1242053
theorem B4727429 : Blo 826349 4727429 := bstep (se 4 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 4727429 = 886393) B886393
theorem B828051 : Blo 826349 828051 := bstep (se 1 (by rfl) ⟨621038, by rfl⟩ : syracuseStep 828051 = 1242077) B1242077
theorem B828067 : Blo 826349 828067 := bstep (se 1 (by rfl) ⟨621050, by rfl⟩ : syracuseStep 828067 = 1242101) B1242101
theorem B828083 : Blo 826349 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B828099 : Blo 826349 828099 := bstep (se 1 (by rfl) ⟨621074, by rfl⟩ : syracuseStep 828099 = 1242149) B1242149
theorem B828115 : Blo 826349 828115 := bstep (se 1 (by rfl) ⟨621086, by rfl⟩ : syracuseStep 828115 = 1242173) B1242173
theorem B828131 : Blo 826349 828131 := bstep (se 1 (by rfl) ⟨621098, by rfl⟩ : syracuseStep 828131 = 1242197) B1242197
theorem B828147 : Blo 826349 828147 := bstep (se 1 (by rfl) ⟨621110, by rfl⟩ : syracuseStep 828147 = 1242221) B1242221
theorem B828163 : Blo 826349 828163 := bstep (se 1 (by rfl) ⟨621122, by rfl⟩ : syracuseStep 828163 = 1242245) B1242245
theorem B828179 : Blo 826349 828179 := bstep (se 1 (by rfl) ⟨621134, by rfl⟩ : syracuseStep 828179 = 1242269) B1242269
theorem B2827043 : Blo 826349 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B828195 : Blo 826349 828195 := bstep (se 1 (by rfl) ⟨621146, by rfl⟩ : syracuseStep 828195 = 1242293) B1242293
theorem B828211 : Blo 826349 828211 := bstep (se 1 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 828211 = 1242317) B1242317
theorem B828227 : Blo 826349 828227 := bstep (se 1 (by rfl) ⟨621170, by rfl⟩ : syracuseStep 828227 = 1242341) B1242341
theorem B828243 : Blo 826349 828243 := bstep (se 1 (by rfl) ⟨621182, by rfl⟩ : syracuseStep 828243 = 1242365) B1242365
theorem B828259 : Blo 826349 828259 := bstep (se 1 (by rfl) ⟨621194, by rfl⟩ : syracuseStep 828259 = 1242389) B1242389
theorem B828275 : Blo 826349 828275 := bstep (se 1 (by rfl) ⟨621206, by rfl⟩ : syracuseStep 828275 = 1242413) B1242413
theorem B828291 : Blo 826349 828291 := bstep (se 1 (by rfl) ⟨621218, by rfl⟩ : syracuseStep 828291 = 1242437) B1242437
theorem B828307 : Blo 826349 828307 := bstep (se 1 (by rfl) ⟨621230, by rfl⟩ : syracuseStep 828307 = 1242461) B1242461
theorem B828323 : Blo 826349 828323 := bstep (se 1 (by rfl) ⟨621242, by rfl⟩ : syracuseStep 828323 = 1242485) B1242485
theorem B828339 : Blo 826349 828339 := bstep (se 1 (by rfl) ⟨621254, by rfl⟩ : syracuseStep 828339 = 1242509) B1242509
theorem B828355 : Blo 826349 828355 := bstep (se 1 (by rfl) ⟨621266, by rfl⟩ : syracuseStep 828355 = 1242533) B1242533
theorem B2794445 : Blo 826349 2794445 := bstep (se 3 (by rfl) ⟨523958, by rfl⟩ : syracuseStep 2794445 = 1047917) B1047917
theorem B828371 : Blo 826349 828371 := bstep (se 1 (by rfl) ⟨621278, by rfl⟩ : syracuseStep 828371 = 1242557) B1242557
theorem B828387 : Blo 826349 828387 := bstep (se 1 (by rfl) ⟨621290, by rfl⟩ : syracuseStep 828387 = 1242581) B1242581
theorem B828403 : Blo 826349 828403 := bstep (se 1 (by rfl) ⟨621302, by rfl⟩ : syracuseStep 828403 = 1242605) B1242605
theorem B2794499 : Blo 826349 2794499 := bstep (se 1 (by rfl) ⟨2095874, by rfl⟩ : syracuseStep 2794499 = 4191749) B4191749
theorem B828419 : Blo 826349 828419 := bstep (se 1 (by rfl) ⟨621314, by rfl⟩ : syracuseStep 828419 = 1242629) B1242629
theorem B828435 : Blo 826349 828435 := bstep (se 1 (by rfl) ⟨621326, by rfl⟩ : syracuseStep 828435 = 1242653) B1242653
theorem B828451 : Blo 826349 828451 := bstep (se 1 (by rfl) ⟨621338, by rfl⟩ : syracuseStep 828451 = 1242677) B1242677
theorem B828467 : Blo 826349 828467 := bstep (se 1 (by rfl) ⟨621350, by rfl⟩ : syracuseStep 828467 = 1242701) B1242701
theorem B828483 : Blo 826349 828483 := bstep (se 1 (by rfl) ⟨621362, by rfl⟩ : syracuseStep 828483 = 1242725) B1242725
theorem B828499 : Blo 826349 828499 := bstep (se 1 (by rfl) ⟨621374, by rfl⟩ : syracuseStep 828499 = 1242749) B1242749
theorem B828515 : Blo 826349 828515 := bstep (se 1 (by rfl) ⟨621386, by rfl⟩ : syracuseStep 828515 = 1242773) B1242773
theorem B828531 : Blo 826349 828531 := bstep (se 1 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 828531 = 1242797) B1242797
theorem B828547 : Blo 826349 828547 := bstep (se 1 (by rfl) ⟨621410, by rfl⟩ : syracuseStep 828547 = 1242821) B1242821
theorem B828563 : Blo 826349 828563 := bstep (se 1 (by rfl) ⟨621422, by rfl⟩ : syracuseStep 828563 = 1242845) B1242845
theorem B1418387 : Blo 826349 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B828579 : Blo 826349 828579 := bstep (se 1 (by rfl) ⟨621434, by rfl⟩ : syracuseStep 828579 = 1242869) B1242869
theorem B828595 : Blo 826349 828595 := bstep (se 1 (by rfl) ⟨621446, by rfl⟩ : syracuseStep 828595 = 1242893) B1242893
theorem B828611 : Blo 826349 828611 := bstep (se 1 (by rfl) ⟨621458, by rfl⟩ : syracuseStep 828611 = 1242917) B1242917
theorem B828627 : Blo 826349 828627 := bstep (se 1 (by rfl) ⟨621470, by rfl⟩ : syracuseStep 828627 = 1242941) B1242941
theorem B828643 : Blo 826349 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B10200305 : Blo 826349 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B828659 : Blo 826349 828659 := bstep (se 1 (by rfl) ⟨621494, by rfl⟩ : syracuseStep 828659 = 1242989) B1242989
theorem B828675 : Blo 826349 828675 := bstep (se 1 (by rfl) ⟨621506, by rfl⟩ : syracuseStep 828675 = 1243013) B1243013
theorem B2794769 : Blo 826349 2794769 := bstep (se 2 (by rfl) ⟨1048038, by rfl⟩ : syracuseStep 2794769 = 2096077) B2096077
theorem B828691 : Blo 826349 828691 := bstep (se 1 (by rfl) ⟨621518, by rfl⟩ : syracuseStep 828691 = 1243037) B1243037
theorem B828707 : Blo 826349 828707 := bstep (se 1 (by rfl) ⟨621530, by rfl⟩ : syracuseStep 828707 = 1243061) B1243061
theorem B828723 : Blo 826349 828723 := bstep (se 1 (by rfl) ⟨621542, by rfl⟩ : syracuseStep 828723 = 1243085) B1243085
theorem B828739 : Blo 826349 828739 := bstep (se 1 (by rfl) ⟨621554, by rfl⟩ : syracuseStep 828739 = 1243109) B1243109
theorem B828755 : Blo 826349 828755 := bstep (se 1 (by rfl) ⟨621566, by rfl⟩ : syracuseStep 828755 = 1243133) B1243133
theorem B828771 : Blo 826349 828771 := bstep (se 1 (by rfl) ⟨621578, by rfl⟩ : syracuseStep 828771 = 1243157) B1243157
theorem B828787 : Blo 826349 828787 := bstep (se 1 (by rfl) ⟨621590, by rfl⟩ : syracuseStep 828787 = 1243181) B1243181
theorem B828803 : Blo 826349 828803 := bstep (se 1 (by rfl) ⟨621602, by rfl⟩ : syracuseStep 828803 = 1243205) B1243205
theorem B828819 : Blo 826349 828819 := bstep (se 1 (by rfl) ⟨621614, by rfl⟩ : syracuseStep 828819 = 1243229) B1243229
theorem B828835 : Blo 826349 828835 := bstep (se 1 (by rfl) ⟨621626, by rfl⟩ : syracuseStep 828835 = 1243253) B1243253
theorem B828851 : Blo 826349 828851 := bstep (se 1 (by rfl) ⟨621638, by rfl⟩ : syracuseStep 828851 = 1243277) B1243277
theorem B828867 : Blo 826349 828867 := bstep (se 1 (by rfl) ⟨621650, by rfl⟩ : syracuseStep 828867 = 1243301) B1243301
theorem B828883 : Blo 826349 828883 := bstep (se 1 (by rfl) ⟨621662, by rfl⟩ : syracuseStep 828883 = 1243325) B1243325
theorem B828899 : Blo 826349 828899 := bstep (se 1 (by rfl) ⟨621674, by rfl⟩ : syracuseStep 828899 = 1243349) B1243349
theorem B828915 : Blo 826349 828915 := bstep (se 1 (by rfl) ⟨621686, by rfl⟩ : syracuseStep 828915 = 1243373) B1243373
theorem B828931 : Blo 826349 828931 := bstep (se 1 (by rfl) ⟨621698, by rfl⟩ : syracuseStep 828931 = 1243397) B1243397
theorem B828947 : Blo 826349 828947 := bstep (se 1 (by rfl) ⟨621710, by rfl⟩ : syracuseStep 828947 = 1243421) B1243421
theorem B828963 : Blo 826349 828963 := bstep (se 1 (by rfl) ⟨621722, by rfl⟩ : syracuseStep 828963 = 1243445) B1243445
theorem B828979 : Blo 826349 828979 := bstep (se 1 (by rfl) ⟨621734, by rfl⟩ : syracuseStep 828979 = 1243469) B1243469
theorem B828995 : Blo 826349 828995 := bstep (se 1 (by rfl) ⟨621746, by rfl⟩ : syracuseStep 828995 = 1243493) B1243493
theorem B829011 : Blo 826349 829011 := bstep (se 1 (by rfl) ⟨621758, by rfl⟩ : syracuseStep 829011 = 1243517) B1243517
theorem B829027 : Blo 826349 829027 := bstep (se 1 (by rfl) ⟨621770, by rfl⟩ : syracuseStep 829027 = 1243541) B1243541
theorem B829043 : Blo 826349 829043 := bstep (se 1 (by rfl) ⟨621782, by rfl⟩ : syracuseStep 829043 = 1243565) B1243565
theorem B829059 : Blo 826349 829059 := bstep (se 1 (by rfl) ⟨621794, by rfl⟩ : syracuseStep 829059 = 1243589) B1243589
theorem B4368013 : Blo 826349 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B829075 : Blo 826349 829075 := bstep (se 1 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 829075 = 1243613) B1243613
theorem B829091 : Blo 826349 829091 := bstep (se 1 (by rfl) ⟨621818, by rfl⟩ : syracuseStep 829091 = 1243637) B1243637
theorem B2991779 : Blo 826349 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B829107 : Blo 826349 829107 := bstep (se 1 (by rfl) ⟨621830, by rfl⟩ : syracuseStep 829107 = 1243661) B1243661
theorem B829123 : Blo 826349 829123 := bstep (se 1 (by rfl) ⟨621842, by rfl⟩ : syracuseStep 829123 = 1243685) B1243685
theorem B829139 : Blo 826349 829139 := bstep (se 1 (by rfl) ⟨621854, by rfl⟩ : syracuseStep 829139 = 1243709) B1243709
theorem B829155 : Blo 826349 829155 := bstep (se 1 (by rfl) ⟨621866, by rfl⟩ : syracuseStep 829155 = 1243733) B1243733
theorem B829171 : Blo 826349 829171 := bstep (se 1 (by rfl) ⟨621878, by rfl⟩ : syracuseStep 829171 = 1243757) B1243757
theorem B2238211 : Blo 826349 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B829187 : Blo 826349 829187 := bstep (se 1 (by rfl) ⟨621890, by rfl⟩ : syracuseStep 829187 = 1243781) B1243781
theorem B829203 : Blo 826349 829203 := bstep (se 1 (by rfl) ⟨621902, by rfl⟩ : syracuseStep 829203 = 1243805) B1243805
theorem B829219 : Blo 826349 829219 := bstep (se 1 (by rfl) ⟨621914, by rfl⟩ : syracuseStep 829219 = 1243829) B1243829
theorem B2795309 : Blo 826349 2795309 := bstep (se 3 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 2795309 = 1048241) B1048241
theorem B829235 : Blo 826349 829235 := bstep (se 1 (by rfl) ⟨621926, by rfl⟩ : syracuseStep 829235 = 1243853) B1243853
theorem B829251 : Blo 826349 829251 := bstep (se 1 (by rfl) ⟨621938, by rfl⟩ : syracuseStep 829251 = 1243877) B1243877
theorem B829267 : Blo 826349 829267 := bstep (se 1 (by rfl) ⟨621950, by rfl⟩ : syracuseStep 829267 = 1243901) B1243901
theorem B2795363 : Blo 826349 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B829283 : Blo 826349 829283 := bstep (se 1 (by rfl) ⟨621962, by rfl⟩ : syracuseStep 829283 = 1243925) B1243925
theorem B829299 : Blo 826349 829299 := bstep (se 1 (by rfl) ⟨621974, by rfl⟩ : syracuseStep 829299 = 1243949) B1243949
theorem B829315 : Blo 826349 829315 := bstep (se 1 (by rfl) ⟨621986, by rfl⟩ : syracuseStep 829315 = 1243973) B1243973
theorem B829331 : Blo 826349 829331 := bstep (se 1 (by rfl) ⟨621998, by rfl⟩ : syracuseStep 829331 = 1243997) B1243997
theorem B829347 : Blo 826349 829347 := bstep (se 1 (by rfl) ⟨622010, by rfl⟩ : syracuseStep 829347 = 1244021) B1244021
theorem B829363 : Blo 826349 829363 := bstep (se 1 (by rfl) ⟨622022, by rfl⟩ : syracuseStep 829363 = 1244045) B1244045
theorem B829379 : Blo 826349 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B829395 : Blo 826349 829395 := bstep (se 1 (by rfl) ⟨622046, by rfl⟩ : syracuseStep 829395 = 1244093) B1244093
theorem B829411 : Blo 826349 829411 := bstep (se 1 (by rfl) ⟨622058, by rfl⟩ : syracuseStep 829411 = 1244117) B1244117
theorem B829427 : Blo 826349 829427 := bstep (se 1 (by rfl) ⟨622070, by rfl⟩ : syracuseStep 829427 = 1244141) B1244141
theorem B829443 : Blo 826349 829443 := bstep (se 1 (by rfl) ⟨622082, by rfl⟩ : syracuseStep 829443 = 1244165) B1244165
theorem B829459 : Blo 826349 829459 := bstep (se 1 (by rfl) ⟨622094, by rfl⟩ : syracuseStep 829459 = 1244189) B1244189
theorem B829475 : Blo 826349 829475 := bstep (se 1 (by rfl) ⟨622106, by rfl⟩ : syracuseStep 829475 = 1244213) B1244213
theorem B829491 : Blo 826349 829491 := bstep (se 1 (by rfl) ⟨622118, by rfl⟩ : syracuseStep 829491 = 1244237) B1244237
theorem B829507 : Blo 826349 829507 := bstep (se 1 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 829507 = 1244261) B1244261
theorem B829523 : Blo 826349 829523 := bstep (se 1 (by rfl) ⟨622142, by rfl⟩ : syracuseStep 829523 = 1244285) B1244285
theorem B1681507 : Blo 826349 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B829539 : Blo 826349 829539 := bstep (se 1 (by rfl) ⟨622154, by rfl⟩ : syracuseStep 829539 = 1244309) B1244309
theorem B2795633 : Blo 826349 2795633 := bstep (se 2 (by rfl) ⟨1048362, by rfl⟩ : syracuseStep 2795633 = 2096725) B2096725
theorem B2992241 : Blo 826349 2992241 := bstep (se 2 (by rfl) ⟨1122090, by rfl⟩ : syracuseStep 2992241 = 2244181) B2244181
theorem B829555 : Blo 826349 829555 := bstep (se 1 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 829555 = 1244333) B1244333
theorem B829571 : Blo 826349 829571 := bstep (se 1 (by rfl) ⟨622178, by rfl⟩ : syracuseStep 829571 = 1244357) B1244357
theorem B829587 : Blo 826349 829587 := bstep (se 1 (by rfl) ⟨622190, by rfl⟩ : syracuseStep 829587 = 1244381) B1244381
theorem B829603 : Blo 826349 829603 := bstep (se 1 (by rfl) ⟨622202, by rfl⟩ : syracuseStep 829603 = 1244405) B1244405
theorem B829619 : Blo 826349 829619 := bstep (se 1 (by rfl) ⟨622214, by rfl⟩ : syracuseStep 829619 = 1244429) B1244429
theorem B829635 : Blo 826349 829635 := bstep (se 1 (by rfl) ⟨622226, by rfl⟩ : syracuseStep 829635 = 1244453) B1244453
theorem B829651 : Blo 826349 829651 := bstep (se 1 (by rfl) ⟨622238, by rfl⟩ : syracuseStep 829651 = 1244477) B1244477
theorem B829667 : Blo 826349 829667 := bstep (se 1 (by rfl) ⟨622250, by rfl⟩ : syracuseStep 829667 = 1244501) B1244501
theorem B829683 : Blo 826349 829683 := bstep (se 1 (by rfl) ⟨622262, by rfl⟩ : syracuseStep 829683 = 1244525) B1244525
theorem B829699 : Blo 826349 829699 := bstep (se 1 (by rfl) ⟨622274, by rfl⟩ : syracuseStep 829699 = 1244549) B1244549
theorem B829715 : Blo 826349 829715 := bstep (se 1 (by rfl) ⟨622286, by rfl⟩ : syracuseStep 829715 = 1244573) B1244573
theorem B829731 : Blo 826349 829731 := bstep (se 1 (by rfl) ⟨622298, by rfl⟩ : syracuseStep 829731 = 1244597) B1244597
theorem B829747 : Blo 826349 829747 := bstep (se 1 (by rfl) ⟨622310, by rfl⟩ : syracuseStep 829747 = 1244621) B1244621
theorem B829763 : Blo 826349 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B829779 : Blo 826349 829779 := bstep (se 1 (by rfl) ⟨622334, by rfl⟩ : syracuseStep 829779 = 1244669) B1244669
theorem B829795 : Blo 826349 829795 := bstep (se 1 (by rfl) ⟨622346, by rfl⟩ : syracuseStep 829795 = 1244693) B1244693
theorem B829811 : Blo 826349 829811 := bstep (se 1 (by rfl) ⟨622358, by rfl⟩ : syracuseStep 829811 = 1244717) B1244717
theorem B829827 : Blo 826349 829827 := bstep (se 1 (by rfl) ⟨622370, by rfl⟩ : syracuseStep 829827 = 1244741) B1244741
theorem B829843 : Blo 826349 829843 := bstep (se 1 (by rfl) ⟨622382, by rfl⟩ : syracuseStep 829843 = 1244765) B1244765
theorem B829859 : Blo 826349 829859 := bstep (se 1 (by rfl) ⟨622394, by rfl⟩ : syracuseStep 829859 = 1244789) B1244789
theorem B829875 : Blo 826349 829875 := bstep (se 1 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 829875 = 1244813) B1244813
theorem B829891 : Blo 826349 829891 := bstep (se 1 (by rfl) ⟨622418, by rfl⟩ : syracuseStep 829891 = 1244837) B1244837
theorem B829907 : Blo 826349 829907 := bstep (se 1 (by rfl) ⟨622430, by rfl⟩ : syracuseStep 829907 = 1244861) B1244861
theorem B829923 : Blo 826349 829923 := bstep (se 1 (by rfl) ⟨622442, by rfl⟩ : syracuseStep 829923 = 1244885) B1244885
theorem B829939 : Blo 826349 829939 := bstep (se 1 (by rfl) ⟨622454, by rfl⟩ : syracuseStep 829939 = 1244909) B1244909
theorem B829955 : Blo 826349 829955 := bstep (se 1 (by rfl) ⟨622466, by rfl⟩ : syracuseStep 829955 = 1244933) B1244933
theorem B829971 : Blo 826349 829971 := bstep (se 1 (by rfl) ⟨622478, by rfl⟩ : syracuseStep 829971 = 1244957) B1244957
theorem B829987 : Blo 826349 829987 := bstep (se 1 (by rfl) ⟨622490, by rfl⟩ : syracuseStep 829987 = 1244981) B1244981
theorem B830003 : Blo 826349 830003 := bstep (se 1 (by rfl) ⟨622502, by rfl⟩ : syracuseStep 830003 = 1245005) B1245005
theorem B830019 : Blo 826349 830019 := bstep (se 1 (by rfl) ⟨622514, by rfl⟩ : syracuseStep 830019 = 1245029) B1245029
theorem B3353165 : Blo 826349 3353165 := bstep (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) B1257437
theorem B830035 : Blo 826349 830035 := bstep (se 1 (by rfl) ⟨622526, by rfl⟩ : syracuseStep 830035 = 1245053) B1245053
theorem B830051 : Blo 826349 830051 := bstep (se 1 (by rfl) ⟨622538, by rfl⟩ : syracuseStep 830051 = 1245077) B1245077
theorem B830067 : Blo 826349 830067 := bstep (se 1 (by rfl) ⟨622550, by rfl⟩ : syracuseStep 830067 = 1245101) B1245101
theorem B830083 : Blo 826349 830083 := bstep (se 1 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 830083 = 1245125) B1245125
theorem B2796173 : Blo 826349 2796173 := bstep (se 3 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 2796173 = 1048565) B1048565
theorem B830099 : Blo 826349 830099 := bstep (se 1 (by rfl) ⟨622574, by rfl⟩ : syracuseStep 830099 = 1245149) B1245149
theorem B830115 : Blo 826349 830115 := bstep (se 1 (by rfl) ⟨622586, by rfl⟩ : syracuseStep 830115 = 1245173) B1245173
theorem B830131 : Blo 826349 830131 := bstep (se 1 (by rfl) ⟨622598, by rfl⟩ : syracuseStep 830131 = 1245197) B1245197
theorem B2796227 : Blo 826349 2796227 := bstep (se 1 (by rfl) ⟨2097170, by rfl⟩ : syracuseStep 2796227 = 4194341) B4194341
theorem B830147 : Blo 826349 830147 := bstep (se 1 (by rfl) ⟨622610, by rfl⟩ : syracuseStep 830147 = 1245221) B1245221
theorem B830163 : Blo 826349 830163 := bstep (se 1 (by rfl) ⟨622622, by rfl⟩ : syracuseStep 830163 = 1245245) B1245245
theorem B830179 : Blo 826349 830179 := bstep (se 1 (by rfl) ⟨622634, by rfl⟩ : syracuseStep 830179 = 1245269) B1245269
theorem B830195 : Blo 826349 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B830211 : Blo 826349 830211 := bstep (se 1 (by rfl) ⟨622658, by rfl⟩ : syracuseStep 830211 = 1245317) B1245317
theorem B2239249 : Blo 826349 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B1420051 : Blo 826349 1420051 := bstep (se 1 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 1420051 = 2130077) B2130077
theorem B830227 : Blo 826349 830227 := bstep (se 1 (by rfl) ⟨622670, by rfl⟩ : syracuseStep 830227 = 1245341) B1245341
theorem B830243 : Blo 826349 830243 := bstep (se 1 (by rfl) ⟨622682, by rfl⟩ : syracuseStep 830243 = 1245365) B1245365
theorem B830259 : Blo 826349 830259 := bstep (se 1 (by rfl) ⟨622694, by rfl⟩ : syracuseStep 830259 = 1245389) B1245389
theorem B830275 : Blo 826349 830275 := bstep (se 1 (by rfl) ⟨622706, by rfl⟩ : syracuseStep 830275 = 1245413) B1245413
theorem B830291 : Blo 826349 830291 := bstep (se 1 (by rfl) ⟨622718, by rfl⟩ : syracuseStep 830291 = 1245437) B1245437
theorem B830307 : Blo 826349 830307 := bstep (se 1 (by rfl) ⟨622730, by rfl⟩ : syracuseStep 830307 = 1245461) B1245461
theorem B830323 : Blo 826349 830323 := bstep (se 1 (by rfl) ⟨622742, by rfl⟩ : syracuseStep 830323 = 1245485) B1245485
theorem B830339 : Blo 826349 830339 := bstep (se 1 (by rfl) ⟨622754, by rfl⟩ : syracuseStep 830339 = 1245509) B1245509
theorem B2796497 : Blo 826349 2796497 := bstep (se 2 (by rfl) ⟨1048686, by rfl⟩ : syracuseStep 2796497 = 2097373) B2097373
theorem B18197617 : Blo 826349 18197617 := bstep (se 2 (by rfl) ⟨6824106, by rfl⟩ : syracuseStep 18197617 = 13648213) B13648213
theorem B1256563 : Blo 826349 1256563 := bstep (se 1 (by rfl) ⟨942422, by rfl⟩ : syracuseStep 1256563 = 1884845) B1884845
theorem B1256897 : Blo 826349 1256897 := bstep (se 2 (by rfl) ⟨471336, by rfl⟩ : syracuseStep 1256897 = 942673) B942673
theorem B3354061 : Blo 826349 3354061 := bstep (se 3 (by rfl) ⟨628886, by rfl⟩ : syracuseStep 3354061 = 1257773) B1257773
theorem B2797037 : Blo 826349 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B2797091 : Blo 826349 2797091 := bstep (se 1 (by rfl) ⟨2097818, by rfl⟩ : syracuseStep 2797091 = 4195637) B4195637
theorem B5385989 : Blo 826349 5385989 := bstep (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) B1009873
theorem B995107 : Blo 826349 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B2797361 : Blo 826349 2797361 := bstep (se 2 (by rfl) ⟨1049010, by rfl⟩ : syracuseStep 2797361 = 2098021) B2098021
theorem B995203 : Blo 826349 995203 := bstep (se 1 (by rfl) ⟨746402, by rfl⟩ : syracuseStep 995203 = 1492805) B1492805
theorem B929731 : Blo 826349 929731 := bstep (se 1 (by rfl) ⟨697298, by rfl⟩ : syracuseStep 929731 = 1394597) B1394597
theorem B995347 : Blo 826349 995347 := bstep (se 1 (by rfl) ⟨746510, by rfl⟩ : syracuseStep 995347 = 1493021) B1493021
theorem B929875 : Blo 826349 929875 := bstep (se 1 (by rfl) ⟨697406, by rfl⟩ : syracuseStep 929875 = 1394813) B1394813
theorem B930019 : Blo 826349 930019 := bstep (se 1 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 930019 = 1395029) B1395029
theorem B2797901 : Blo 826349 2797901 := bstep (se 3 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 2797901 = 1049213) B1049213
theorem B930163 : Blo 826349 930163 := bstep (se 1 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 930163 = 1395245) B1395245
theorem B2797955 : Blo 826349 2797955 := bstep (se 1 (by rfl) ⟨2098466, by rfl⟩ : syracuseStep 2797955 = 4196933) B4196933
theorem B930307 : Blo 826349 930307 := bstep (se 1 (by rfl) ⟨697730, by rfl⟩ : syracuseStep 930307 = 1395461) B1395461
theorem B2798225 : Blo 826349 2798225 := bstep (se 2 (by rfl) ⟨1049334, by rfl⟩ : syracuseStep 2798225 = 2098669) B2098669
theorem B930451 : Blo 826349 930451 := bstep (se 1 (by rfl) ⟨697838, by rfl⟩ : syracuseStep 930451 = 1395677) B1395677
theorem B2241197 : Blo 826349 2241197 := bstep (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) B840449
theorem B2241283 : Blo 826349 2241283 := bstep (se 1 (by rfl) ⟨1680962, by rfl⟩ : syracuseStep 2241283 = 3361925) B3361925
theorem B1815313 : Blo 826349 1815313 := bstep (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) B1361485
theorem B930595 : Blo 826349 930595 := bstep (se 1 (by rfl) ⟨697946, by rfl⟩ : syracuseStep 930595 = 1395893) B1395893
theorem B2241325 : Blo 826349 2241325 := bstep (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) B840497
theorem B930739 : Blo 826349 930739 := bstep (se 1 (by rfl) ⟨698054, by rfl⟩ : syracuseStep 930739 = 1396109) B1396109
theorem B898003 : Blo 826349 898003 := bstep (se 1 (by rfl) ⟨673502, by rfl⟩ : syracuseStep 898003 = 1347005) B1347005
theorem B7975921 : Blo 826349 7975921 := bstep (se 2 (by rfl) ⟨2990970, by rfl⟩ : syracuseStep 7975921 = 5981941) B5981941
theorem B930883 : Blo 826349 930883 := bstep (se 1 (by rfl) ⟨698162, by rfl⟩ : syracuseStep 930883 = 1396325) B1396325
theorem B2798765 : Blo 826349 2798765 := bstep (se 3 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 2798765 = 1049537) B1049537
theorem B931027 : Blo 826349 931027 := bstep (se 1 (by rfl) ⟨698270, by rfl⟩ : syracuseStep 931027 = 1396541) B1396541
theorem B10073315 : Blo 826349 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B2798819 : Blo 826349 2798819 := bstep (se 1 (by rfl) ⟨2099114, by rfl⟩ : syracuseStep 2798819 = 4198229) B4198229
theorem B931171 : Blo 826349 931171 := bstep (se 1 (by rfl) ⟨698378, by rfl⟩ : syracuseStep 931171 = 1396757) B1396757
theorem B1324451 : Blo 826349 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B3978659 : Blo 826349 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B2799089 : Blo 826349 2799089 := bstep (se 2 (by rfl) ⟨1049658, by rfl⟩ : syracuseStep 2799089 = 2099317) B2099317
theorem B931315 : Blo 826349 931315 := bstep (se 1 (by rfl) ⟨698486, by rfl⟩ : syracuseStep 931315 = 1396973) B1396973
theorem B4470349 : Blo 826349 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B931459 : Blo 826349 931459 := bstep (se 1 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 931459 = 1397189) B1397189
theorem B1259153 : Blo 826349 1259153 := bstep (se 2 (by rfl) ⟨472182, by rfl⟩ : syracuseStep 1259153 = 944365) B944365
theorem B931603 : Blo 826349 931603 := bstep (se 1 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 931603 = 1397405) B1397405
theorem B931747 : Blo 826349 931747 := bstep (se 1 (by rfl) ⟨698810, by rfl⟩ : syracuseStep 931747 = 1397621) B1397621
theorem B6731761 : Blo 826349 6731761 := bstep (se 2 (by rfl) ⟨2524410, by rfl⟩ : syracuseStep 6731761 = 5048821) B5048821
theorem B2799629 : Blo 826349 2799629 := bstep (se 3 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 2799629 = 1049861) B1049861
theorem B931891 : Blo 826349 931891 := bstep (se 1 (by rfl) ⟨698918, by rfl⟩ : syracuseStep 931891 = 1397837) B1397837
theorem B2799683 : Blo 826349 2799683 := bstep (se 1 (by rfl) ⟨2099762, by rfl⟩ : syracuseStep 2799683 = 4199525) B4199525
theorem B10074293 : Blo 826349 10074293 := bstep (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) B944465
theorem B932035 : Blo 826349 932035 := bstep (se 1 (by rfl) ⟨699026, by rfl⟩ : syracuseStep 932035 = 1398053) B1398053
theorem B1325297 : Blo 826349 1325297 := bstep (se 2 (by rfl) ⟨496986, by rfl⟩ : syracuseStep 1325297 = 993973) B993973
theorem B2242883 : Blo 826349 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B2799953 : Blo 826349 2799953 := bstep (se 2 (by rfl) ⟨1049982, by rfl⟩ : syracuseStep 2799953 = 2099965) B2099965
theorem B932179 : Blo 826349 932179 := bstep (se 1 (by rfl) ⟨699134, by rfl⟩ : syracuseStep 932179 = 1398269) B1398269
theorem B1325425 : Blo 826349 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1325489 : Blo 826349 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B932323 : Blo 826349 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B932467 : Blo 826349 932467 := bstep (se 1 (by rfl) ⟨699350, by rfl⟩ : syracuseStep 932467 = 1398701) B1398701
theorem B1260211 : Blo 826349 1260211 := bstep (se 1 (by rfl) ⟨945158, by rfl⟩ : syracuseStep 1260211 = 1890317) B1890317
theorem B9452213 : Blo 826349 9452213 := bstep (se 5 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 9452213 = 886145) B886145
theorem B932611 : Blo 826349 932611 := bstep (se 1 (by rfl) ⟨699458, by rfl⟩ : syracuseStep 932611 = 1398917) B1398917
theorem B2800493 : Blo 826349 2800493 := bstep (se 3 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 2800493 = 1050185) B1050185
theorem B932755 : Blo 826349 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B2800547 : Blo 826349 2800547 := bstep (se 1 (by rfl) ⟨2100410, by rfl⟩ : syracuseStep 2800547 = 4200821) B4200821
theorem B932899 : Blo 826349 932899 := bstep (se 1 (by rfl) ⟨699674, by rfl⟩ : syracuseStep 932899 = 1399349) B1399349
theorem B2243747 : Blo 826349 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B2800817 : Blo 826349 2800817 := bstep (se 2 (by rfl) ⟨1050306, by rfl⟩ : syracuseStep 2800817 = 2100613) B2100613
theorem B933043 : Blo 826349 933043 := bstep (se 1 (by rfl) ⟨699782, by rfl⟩ : syracuseStep 933043 = 1399565) B1399565
theorem B2243825 : Blo 826349 2243825 := bstep (se 2 (by rfl) ⟨841434, by rfl⟩ : syracuseStep 2243825 = 1682869) B1682869
theorem B2243857 : Blo 826349 2243857 := bstep (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) B1682893
theorem B1064227 : Blo 826349 1064227 := bstep (se 1 (by rfl) ⟨798170, by rfl⟩ : syracuseStep 1064227 = 1596341) B1596341
theorem B933187 : Blo 826349 933187 := bstep (se 1 (by rfl) ⟨699890, by rfl⟩ : syracuseStep 933187 = 1399781) B1399781
theorem B1326547 : Blo 826349 1326547 := bstep (se 1 (by rfl) ⟨994910, by rfl⟩ : syracuseStep 1326547 = 1989821) B1989821
theorem B933331 : Blo 826349 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B933475 : Blo 826349 933475 := bstep (se 1 (by rfl) ⟨700106, by rfl⟩ : syracuseStep 933475 = 1400213) B1400213
theorem B2801357 : Blo 826349 2801357 := bstep (se 3 (by rfl) ⟨525254, by rfl⟩ : syracuseStep 2801357 = 1050509) B1050509
theorem B933619 : Blo 826349 933619 := bstep (se 1 (by rfl) ⟨700214, by rfl⟩ : syracuseStep 933619 = 1400429) B1400429
theorem B2801411 : Blo 826349 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B933763 : Blo 826349 933763 := bstep (se 1 (by rfl) ⟨700322, by rfl⟩ : syracuseStep 933763 = 1400645) B1400645
theorem B5390243 : Blo 826349 5390243 := bstep (se 1 (by rfl) ⟨4042682, by rfl⟩ : syracuseStep 5390243 = 8085365) B8085365
theorem B1261489 : Blo 826349 1261489 := bstep (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) B946117
theorem B11321315 : Blo 826349 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B2801681 : Blo 826349 2801681 := bstep (se 2 (by rfl) ⟨1050630, by rfl⟩ : syracuseStep 2801681 = 2101261) B2101261
theorem B933907 : Blo 826349 933907 := bstep (se 1 (by rfl) ⟨700430, by rfl⟩ : syracuseStep 933907 = 1400861) B1400861
theorem B934051 : Blo 826349 934051 := bstep (se 1 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 934051 = 1401077) B1401077
theorem B9191693 : Blo 826349 9191693 := bstep (se 3 (by rfl) ⟨1723442, by rfl⟩ : syracuseStep 9191693 = 3446885) B3446885
theorem B4473137 : Blo 826349 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B9060707 : Blo 826349 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B3064177 : Blo 826349 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B1327475 : Blo 826349 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B2802221 : Blo 826349 2802221 := bstep (se 3 (by rfl) ⟨525416, by rfl⟩ : syracuseStep 2802221 = 1050833) B1050833
theorem B2802275 : Blo 826349 2802275 := bstep (se 1 (by rfl) ⟨2101706, by rfl⟩ : syracuseStep 2802275 = 4203413) B4203413
theorem B1327745 : Blo 826349 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B1328033 : Blo 826349 1328033 := bstep (se 2 (by rfl) ⟨498012, by rfl⟩ : syracuseStep 1328033 = 996025) B996025
theorem B1328449 : Blo 826349 1328449 := bstep (se 2 (by rfl) ⟨498168, by rfl⟩ : syracuseStep 1328449 = 996337) B996337
theorem B3982733 : Blo 826349 3982733 := bstep (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) B1493525
theorem B5654285 : Blo 826349 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B6801221 : Blo 826349 6801221 := bstep (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) B1275229
theorem B4474693 : Blo 826349 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B1394563 : Blo 826349 1394563 := bstep (se 1 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 1394563 = 2091845) B2091845
theorem B5392325 : Blo 826349 5392325 := bstep (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) B1011061
theorem B1394705 : Blo 826349 1394705 := bstep (se 2 (by rfl) ⟨523014, by rfl⟩ : syracuseStep 1394705 = 1046029) B1046029
theorem B1886339 : Blo 826349 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B1394833 : Blo 826349 1394833 := bstep (se 2 (by rfl) ⟨523062, by rfl⟩ : syracuseStep 1394833 = 1046125) B1046125
theorem B1394867 : Blo 826349 1394867 := bstep (se 1 (by rfl) ⟨1046150, by rfl⟩ : syracuseStep 1394867 = 2092301) B2092301
theorem B1329347 : Blo 826349 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B1394995 : Blo 826349 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B4475213 : Blo 826349 4475213 := bstep (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) B1678205
theorem B1329571 : Blo 826349 1329571 := bstep (se 1 (by rfl) ⟨997178, by rfl⟩ : syracuseStep 1329571 = 1994357) B1994357
theorem B1493425 : Blo 826349 1493425 := bstep (se 2 (by rfl) ⟨560034, by rfl⟩ : syracuseStep 1493425 = 1120069) B1120069
theorem B1395137 : Blo 826349 1395137 := bstep (se 2 (by rfl) ⟨523176, by rfl⟩ : syracuseStep 1395137 = 1046353) B1046353
theorem B1395265 : Blo 826349 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B1395299 : Blo 826349 1395299 := bstep (se 1 (by rfl) ⟨1046474, by rfl⟩ : syracuseStep 1395299 = 2092949) B2092949
theorem B1395427 : Blo 826349 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B1395569 : Blo 826349 1395569 := bstep (se 2 (by rfl) ⟨523338, by rfl⟩ : syracuseStep 1395569 = 1046677) B1046677
theorem B1493923 : Blo 826349 1493923 := bstep (se 1 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 1493923 = 2240885) B2240885
theorem B1395697 : Blo 826349 1395697 := bstep (se 2 (by rfl) ⟨523386, by rfl⟩ : syracuseStep 1395697 = 1046773) B1046773
theorem B1395731 : Blo 826349 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B1395859 : Blo 826349 1395859 := bstep (se 1 (by rfl) ⟨1046894, by rfl⟩ : syracuseStep 1395859 = 2093789) B2093789
theorem B1396001 : Blo 826349 1396001 := bstep (se 2 (by rfl) ⟨523500, by rfl⟩ : syracuseStep 1396001 = 1047001) B1047001
theorem B5295395 : Blo 826349 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B1396129 : Blo 826349 1396129 := bstep (se 2 (by rfl) ⟨523548, by rfl⟩ : syracuseStep 1396129 = 1047097) B1047097
theorem B1396163 : Blo 826349 1396163 := bstep (se 1 (by rfl) ⟨1047122, by rfl⟩ : syracuseStep 1396163 = 2094245) B2094245
theorem B1396291 : Blo 826349 1396291 := bstep (se 1 (by rfl) ⟨1047218, by rfl⟩ : syracuseStep 1396291 = 2094437) B2094437
theorem B1396433 : Blo 826349 1396433 := bstep (se 2 (by rfl) ⟨523662, by rfl⟩ : syracuseStep 1396433 = 1047325) B1047325
theorem B839459 : Blo 826349 839459 := bstep (se 1 (by rfl) ⟨629594, by rfl⟩ : syracuseStep 839459 = 1259189) B1259189
theorem B1396561 : Blo 826349 1396561 := bstep (se 2 (by rfl) ⟨523710, by rfl⟩ : syracuseStep 1396561 = 1047421) B1047421
theorem B1396595 : Blo 826349 1396595 := bstep (se 1 (by rfl) ⟨1047446, by rfl⟩ : syracuseStep 1396595 = 2094893) B2094893
theorem B1396723 : Blo 826349 1396723 := bstep (se 1 (by rfl) ⟨1047542, by rfl⟩ : syracuseStep 1396723 = 2095085) B2095085
theorem B1396865 : Blo 826349 1396865 := bstep (se 2 (by rfl) ⟨523824, by rfl⟩ : syracuseStep 1396865 = 1047649) B1047649
theorem B1396993 : Blo 826349 1396993 := bstep (se 2 (by rfl) ⟨523872, by rfl⟩ : syracuseStep 1396993 = 1047745) B1047745
theorem B4313357 : Blo 826349 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B1397027 : Blo 826349 1397027 := bstep (se 1 (by rfl) ⟨1047770, by rfl⟩ : syracuseStep 1397027 = 2095541) B2095541
theorem B1397155 : Blo 826349 1397155 := bstep (se 1 (by rfl) ⟨1047866, by rfl⟩ : syracuseStep 1397155 = 2095733) B2095733
theorem B1397297 : Blo 826349 1397297 := bstep (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) B1047973
theorem B5034595 : Blo 826349 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B1397425 : Blo 826349 1397425 := bstep (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) B1048069
theorem B1397459 : Blo 826349 1397459 := bstep (se 1 (by rfl) ⟨1048094, by rfl⟩ : syracuseStep 1397459 = 2096189) B2096189
theorem B1397587 : Blo 826349 1397587 := bstep (se 1 (by rfl) ⟨1048190, by rfl⟩ : syracuseStep 1397587 = 2096381) B2096381
theorem B5657485 : Blo 826349 5657485 := bstep (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) B2121557
theorem B1987523 : Blo 826349 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B1397729 : Blo 826349 1397729 := bstep (se 2 (by rfl) ⟨524148, by rfl⟩ : syracuseStep 1397729 = 1048297) B1048297
theorem B1135603 : Blo 826349 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1496113 : Blo 826349 1496113 := bstep (se 2 (by rfl) ⟨561042, by rfl⟩ : syracuseStep 1496113 = 1122085) B1122085
theorem B1397857 : Blo 826349 1397857 := bstep (se 2 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 1397857 = 1048393) B1048393
theorem B1135745 : Blo 826349 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B1397891 : Blo 826349 1397891 := bstep (se 1 (by rfl) ⟨1048418, by rfl⟩ : syracuseStep 1397891 = 2096837) B2096837
theorem B5297393 : Blo 826349 5297393 := bstep (se 2 (by rfl) ⟨1986522, by rfl⟩ : syracuseStep 5297393 = 3973045) B3973045
theorem B1398019 : Blo 826349 1398019 := bstep (se 1 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 1398019 = 2097029) B2097029
theorem B10638661 : Blo 826349 10638661 := bstep (se 4 (by rfl) ⟨997374, by rfl⟩ : syracuseStep 10638661 = 1994749) B1994749
theorem B1398161 : Blo 826349 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B1398289 : Blo 826349 1398289 := bstep (se 2 (by rfl) ⟨524358, by rfl⟩ : syracuseStep 1398289 = 1048717) B1048717
theorem B1398323 : Blo 826349 1398323 := bstep (se 1 (by rfl) ⟨1048742, by rfl⟩ : syracuseStep 1398323 = 2097485) B2097485
theorem B1398451 : Blo 826349 1398451 := bstep (se 1 (by rfl) ⟨1048838, by rfl⟩ : syracuseStep 1398451 = 2097677) B2097677
theorem B1988291 : Blo 826349 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B1398593 : Blo 826349 1398593 := bstep (se 2 (by rfl) ⟨524472, by rfl⟩ : syracuseStep 1398593 = 1048945) B1048945
theorem B1398721 : Blo 826349 1398721 := bstep (se 2 (by rfl) ⟨524520, by rfl⟩ : syracuseStep 1398721 = 1049041) B1049041
theorem B1398755 : Blo 826349 1398755 := bstep (se 1 (by rfl) ⟨1049066, by rfl⟩ : syracuseStep 1398755 = 2098133) B2098133
theorem B1398883 : Blo 826349 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B5298317 : Blo 826349 5298317 := bstep (se 3 (by rfl) ⟨993434, by rfl⟩ : syracuseStep 5298317 = 1986869) B1986869
theorem B1399025 : Blo 826349 1399025 := bstep (se 2 (by rfl) ⟨524634, by rfl⟩ : syracuseStep 1399025 = 1049269) B1049269
theorem B1988849 : Blo 826349 1988849 := bstep (se 2 (by rfl) ⟨745818, by rfl⟩ : syracuseStep 1988849 = 1491637) B1491637
theorem B5036365 : Blo 826349 5036365 := bstep (se 3 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 5036365 = 1888637) B1888637
theorem B1399153 : Blo 826349 1399153 := bstep (se 2 (by rfl) ⟨524682, by rfl⟩ : syracuseStep 1399153 = 1049365) B1049365
theorem B1399187 : Blo 826349 1399187 := bstep (se 1 (by rfl) ⟨1049390, by rfl⟩ : syracuseStep 1399187 = 2098781) B2098781
theorem B9427427 : Blo 826349 9427427 := bstep (se 1 (by rfl) ⟨7070570, by rfl⟩ : syracuseStep 9427427 = 14141141) B14141141
theorem B1989137 : Blo 826349 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1399315 : Blo 826349 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B1530499 : Blo 826349 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B1399457 : Blo 826349 1399457 := bstep (se 2 (by rfl) ⟨524796, by rfl⟩ : syracuseStep 1399457 = 1049593) B1049593
theorem B1399585 : Blo 826349 1399585 := bstep (se 2 (by rfl) ⟨524844, by rfl⟩ : syracuseStep 1399585 = 1049689) B1049689
theorem B1399619 : Blo 826349 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B4184945 : Blo 826349 4184945 := bstep (se 2 (by rfl) ⟨1569354, by rfl⟩ : syracuseStep 4184945 = 3138709) B3138709
theorem B3627917 : Blo 826349 3627917 := bstep (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) B1360469
theorem B1399747 : Blo 826349 1399747 := bstep (se 1 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 1399747 = 2099621) B2099621
theorem B1399889 : Blo 826349 1399889 := bstep (se 2 (by rfl) ⟨524958, by rfl⟩ : syracuseStep 1399889 = 1049917) B1049917
theorem B1891505 : Blo 826349 1891505 := bstep (se 2 (by rfl) ⟨709314, by rfl⟩ : syracuseStep 1891505 = 1418629) B1418629
theorem B1596611 : Blo 826349 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B1400017 : Blo 826349 1400017 := bstep (se 2 (by rfl) ⟨525006, by rfl⟩ : syracuseStep 1400017 = 1050013) B1050013
theorem B3529955 : Blo 826349 3529955 := bstep (se 1 (by rfl) ⟨2647466, by rfl⟩ : syracuseStep 3529955 = 5294933) B5294933
theorem B8936675 : Blo 826349 8936675 := bstep (se 1 (by rfl) ⟨6702506, by rfl⟩ : syracuseStep 8936675 = 13405013) B13405013
theorem B1400051 : Blo 826349 1400051 := bstep (se 1 (by rfl) ⟨1050038, by rfl⟩ : syracuseStep 1400051 = 2100077) B2100077
theorem B1400179 : Blo 826349 1400179 := bstep (se 1 (by rfl) ⟨1050134, by rfl⟩ : syracuseStep 1400179 = 2100269) B2100269
theorem B1400321 : Blo 826349 1400321 := bstep (se 2 (by rfl) ⟨525120, by rfl⟩ : syracuseStep 1400321 = 1050241) B1050241
theorem B1400449 : Blo 826349 1400449 := bstep (se 2 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 1400449 = 1050337) B1050337
theorem B1400483 : Blo 826349 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B1859345 : Blo 826349 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B1859363 : Blo 826349 1859363 := bstep (se 1 (by rfl) ⟨1394522, by rfl⟩ : syracuseStep 1859363 = 2789045) B2789045
theorem B1400611 : Blo 826349 1400611 := bstep (se 1 (by rfl) ⟨1050458, by rfl⟩ : syracuseStep 1400611 = 2100917) B2100917
theorem B1400753 : Blo 826349 1400753 := bstep (se 2 (by rfl) ⟨525282, by rfl⟩ : syracuseStep 1400753 = 1050565) B1050565
theorem B1859633 : Blo 826349 1859633 := bstep (se 2 (by rfl) ⟨697362, by rfl⟩ : syracuseStep 1859633 = 1394725) B1394725
theorem B1400881 : Blo 826349 1400881 := bstep (se 2 (by rfl) ⟨525330, by rfl⟩ : syracuseStep 1400881 = 1050661) B1050661
theorem B1859651 : Blo 826349 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B1400915 : Blo 826349 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1401043 : Blo 826349 1401043 := bstep (se 1 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 1401043 = 2101565) B2101565
theorem B2122001 : Blo 826349 2122001 := bstep (se 2 (by rfl) ⟨795750, by rfl⟩ : syracuseStep 2122001 = 1591501) B1591501
theorem B4186403 : Blo 826349 4186403 := bstep (se 1 (by rfl) ⟨3139802, by rfl⟩ : syracuseStep 4186403 = 6279605) B6279605
theorem B1859921 : Blo 826349 1859921 := bstep (se 2 (by rfl) ⟨697470, by rfl⟩ : syracuseStep 1859921 = 1394941) B1394941
theorem B1401185 : Blo 826349 1401185 := bstep (se 2 (by rfl) ⟨525444, by rfl⟩ : syracuseStep 1401185 = 1050889) B1050889
theorem B1859939 : Blo 826349 1859939 := bstep (se 1 (by rfl) ⟨1394954, by rfl⟩ : syracuseStep 1859939 = 2789909) B2789909
theorem B3531185 : Blo 826349 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B1860209 : Blo 826349 1860209 := bstep (se 2 (by rfl) ⟨697578, by rfl⟩ : syracuseStep 1860209 = 1395157) B1395157
theorem B1860227 : Blo 826349 1860227 := bstep (se 1 (by rfl) ⟨1395170, by rfl⟩ : syracuseStep 1860227 = 2790341) B2790341
theorem B942787 : Blo 826349 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B7070435 : Blo 826349 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B1860497 : Blo 826349 1860497 := bstep (se 2 (by rfl) ⟨697686, by rfl⟩ : syracuseStep 1860497 = 1395373) B1395373
theorem B5235619 : Blo 826349 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1860515 : Blo 826349 1860515 := bstep (se 1 (by rfl) ⟨1395386, by rfl⟩ : syracuseStep 1860515 = 2790773) B2790773
theorem B1893347 : Blo 826349 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B4187213 : Blo 826349 4187213 := bstep (se 3 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 4187213 = 1570205) B1570205
theorem B7169123 : Blo 826349 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B1860785 : Blo 826349 1860785 := bstep (se 2 (by rfl) ⟨697794, by rfl⟩ : syracuseStep 1860785 = 1395589) B1395589
theorem B1860803 : Blo 826349 1860803 := bstep (se 1 (by rfl) ⟨1395602, by rfl⟩ : syracuseStep 1860803 = 2791205) B2791205
theorem B2647313 : Blo 826349 2647313 := bstep (se 2 (by rfl) ⟨992742, by rfl⟩ : syracuseStep 2647313 = 1985485) B1985485
theorem B1861073 : Blo 826349 1861073 := bstep (se 2 (by rfl) ⟨697902, by rfl⟩ : syracuseStep 1861073 = 1395805) B1395805
theorem B943571 : Blo 826349 943571 := bstep (se 1 (by rfl) ⟨707678, by rfl⟩ : syracuseStep 943571 = 1415357) B1415357
theorem B1861091 : Blo 826349 1861091 := bstep (se 1 (by rfl) ⟨1395818, by rfl⟩ : syracuseStep 1861091 = 2791637) B2791637
theorem B911027 : Blo 826349 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B1861361 : Blo 826349 1861361 := bstep (se 2 (by rfl) ⟨698010, by rfl⟩ : syracuseStep 1861361 = 1396021) B1396021
theorem B1861379 : Blo 826349 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B3139469 : Blo 826349 3139469 := bstep (se 3 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 3139469 = 1177301) B1177301
theorem B1861649 : Blo 826349 1861649 := bstep (se 2 (by rfl) ⟨698118, by rfl⟩ : syracuseStep 1861649 = 1396237) B1396237
theorem B1861667 : Blo 826349 1861667 := bstep (se 1 (by rfl) ⟨1396250, by rfl⟩ : syracuseStep 1861667 = 2792501) B2792501
theorem B2517041 : Blo 826349 2517041 := bstep (se 2 (by rfl) ⟨943890, by rfl⟩ : syracuseStep 2517041 = 1887781) B1887781
theorem B1796195 : Blo 826349 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B2648173 : Blo 826349 2648173 := bstep (se 3 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 2648173 = 993065) B993065
theorem B6711493 : Blo 826349 6711493 := bstep (se 4 (by rfl) ⟨629202, by rfl⟩ : syracuseStep 6711493 = 1258405) B1258405
theorem B1861937 : Blo 826349 1861937 := bstep (se 2 (by rfl) ⟨698226, by rfl⟩ : syracuseStep 1861937 = 1396453) B1396453
theorem B2353475 : Blo 826349 2353475 := bstep (se 1 (by rfl) ⟨1765106, by rfl⟩ : syracuseStep 2353475 = 3530213) B3530213
theorem B1861955 : Blo 826349 1861955 := bstep (se 1 (by rfl) ⟨1396466, by rfl⟩ : syracuseStep 1861955 = 2792933) B2792933
theorem B8088005 : Blo 826349 8088005 := bstep (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) B1516501
theorem B1239539 : Blo 826349 1239539 := bstep (se 1 (by rfl) ⟨929654, by rfl⟩ : syracuseStep 1239539 = 1859309) B1859309
theorem B1239569 : Blo 826349 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B1239587 : Blo 826349 1239587 := bstep (se 1 (by rfl) ⟨929690, by rfl⟩ : syracuseStep 1239587 = 1859381) B1859381
theorem B1239617 : Blo 826349 1239617 := bstep (se 2 (by rfl) ⟨464856, by rfl⟩ : syracuseStep 1239617 = 929713) B929713
theorem B2386513 : Blo 826349 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B1862225 : Blo 826349 1862225 := bstep (se 2 (by rfl) ⟨698334, by rfl⟩ : syracuseStep 1862225 = 1396669) B1396669
theorem B1239635 : Blo 826349 1239635 := bstep (se 1 (by rfl) ⟨929726, by rfl⟩ : syracuseStep 1239635 = 1859453) B1859453
theorem B1862243 : Blo 826349 1862243 := bstep (se 1 (by rfl) ⟨1396682, by rfl⟩ : syracuseStep 1862243 = 2793365) B2793365
theorem B6285923 : Blo 826349 6285923 := bstep (se 1 (by rfl) ⟨4714442, by rfl⟩ : syracuseStep 6285923 = 9428885) B9428885
theorem B1239665 : Blo 826349 1239665 := bstep (se 2 (by rfl) ⟨464874, by rfl⟩ : syracuseStep 1239665 = 929749) B929749
theorem B1239683 : Blo 826349 1239683 := bstep (se 1 (by rfl) ⟨929762, by rfl⟩ : syracuseStep 1239683 = 1859525) B1859525
theorem B2353805 : Blo 826349 2353805 := bstep (se 3 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 2353805 = 882677) B882677
theorem B1239713 : Blo 826349 1239713 := bstep (se 2 (by rfl) ⟨464892, by rfl⟩ : syracuseStep 1239713 = 929785) B929785
theorem B1239731 : Blo 826349 1239731 := bstep (se 1 (by rfl) ⟨929798, by rfl⟩ : syracuseStep 1239731 = 1859597) B1859597
theorem B1239761 : Blo 826349 1239761 := bstep (se 2 (by rfl) ⟨464910, by rfl⟩ : syracuseStep 1239761 = 929821) B929821
theorem B2353873 : Blo 826349 2353873 := bstep (se 2 (by rfl) ⟨882702, by rfl⟩ : syracuseStep 2353873 = 1765405) B1765405
theorem B1239779 : Blo 826349 1239779 := bstep (se 1 (by rfl) ⟨929834, by rfl⟩ : syracuseStep 1239779 = 1859669) B1859669
theorem B1239809 : Blo 826349 1239809 := bstep (se 2 (by rfl) ⟨464928, by rfl⟩ : syracuseStep 1239809 = 929857) B929857
theorem B1239827 : Blo 826349 1239827 := bstep (se 1 (by rfl) ⟨929870, by rfl⟩ : syracuseStep 1239827 = 1859741) B1859741
theorem B1239857 : Blo 826349 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B1239875 : Blo 826349 1239875 := bstep (se 1 (by rfl) ⟨929906, by rfl⟩ : syracuseStep 1239875 = 1859813) B1859813
theorem B3533645 : Blo 826349 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B1239905 : Blo 826349 1239905 := bstep (se 2 (by rfl) ⟨464964, by rfl⟩ : syracuseStep 1239905 = 929929) B929929
theorem B1862513 : Blo 826349 1862513 := bstep (se 2 (by rfl) ⟨698442, by rfl⟩ : syracuseStep 1862513 = 1396885) B1396885
theorem B1239923 : Blo 826349 1239923 := bstep (se 1 (by rfl) ⟨929942, by rfl⟩ : syracuseStep 1239923 = 1859885) B1859885
theorem B1862531 : Blo 826349 1862531 := bstep (se 1 (by rfl) ⟨1396898, by rfl⟩ : syracuseStep 1862531 = 2793797) B2793797
theorem B4713349 : Blo 826349 4713349 := bstep (se 4 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 4713349 = 883753) B883753
theorem B1239953 : Blo 826349 1239953 := bstep (se 2 (by rfl) ⟨464982, by rfl⟩ : syracuseStep 1239953 = 929965) B929965
theorem B1239971 : Blo 826349 1239971 := bstep (se 1 (by rfl) ⟨929978, by rfl⟩ : syracuseStep 1239971 = 1859957) B1859957
theorem B1240001 : Blo 826349 1240001 := bstep (se 2 (by rfl) ⟨465000, by rfl⟩ : syracuseStep 1240001 = 930001) B930001
theorem B1698769 : Blo 826349 1698769 := bstep (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) B1274077
theorem B1240019 : Blo 826349 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B2354147 : Blo 826349 2354147 := bstep (se 1 (by rfl) ⟨1765610, by rfl⟩ : syracuseStep 2354147 = 3531221) B3531221
theorem B1240049 : Blo 826349 1240049 := bstep (se 2 (by rfl) ⟨465018, by rfl⟩ : syracuseStep 1240049 = 930037) B930037
theorem B1240067 : Blo 826349 1240067 := bstep (se 1 (by rfl) ⟨930050, by rfl⟩ : syracuseStep 1240067 = 1860101) B1860101
theorem B1240097 : Blo 826349 1240097 := bstep (se 2 (by rfl) ⟨465036, by rfl⟩ : syracuseStep 1240097 = 930073) B930073
theorem B1240115 : Blo 826349 1240115 := bstep (se 1 (by rfl) ⟨930086, by rfl⟩ : syracuseStep 1240115 = 1860173) B1860173
theorem B1240145 : Blo 826349 1240145 := bstep (se 2 (by rfl) ⟨465054, by rfl⟩ : syracuseStep 1240145 = 930109) B930109
theorem B1240163 : Blo 826349 1240163 := bstep (se 1 (by rfl) ⟨930122, by rfl⟩ : syracuseStep 1240163 = 1860245) B1860245
theorem B10087523 : Blo 826349 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B1240193 : Blo 826349 1240193 := bstep (se 2 (by rfl) ⟨465072, by rfl⟩ : syracuseStep 1240193 = 930145) B930145
theorem B1862801 : Blo 826349 1862801 := bstep (se 2 (by rfl) ⟨698550, by rfl⟩ : syracuseStep 1862801 = 1397101) B1397101
theorem B1240211 : Blo 826349 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B1862819 : Blo 826349 1862819 := bstep (se 1 (by rfl) ⟨1397114, by rfl⟩ : syracuseStep 1862819 = 2794229) B2794229
theorem B1240241 : Blo 826349 1240241 := bstep (se 2 (by rfl) ⟨465090, by rfl⟩ : syracuseStep 1240241 = 930181) B930181
theorem B1240259 : Blo 826349 1240259 := bstep (se 1 (by rfl) ⟨930194, by rfl⟩ : syracuseStep 1240259 = 1860389) B1860389
theorem B1240289 : Blo 826349 1240289 := bstep (se 2 (by rfl) ⟨465108, by rfl⟩ : syracuseStep 1240289 = 930217) B930217
theorem B1240307 : Blo 826349 1240307 := bstep (se 1 (by rfl) ⟨930230, by rfl⟩ : syracuseStep 1240307 = 1860461) B1860461
theorem B1240337 : Blo 826349 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B1240355 : Blo 826349 1240355 := bstep (se 1 (by rfl) ⟨930266, by rfl⟩ : syracuseStep 1240355 = 1860533) B1860533
theorem B1240385 : Blo 826349 1240385 := bstep (se 2 (by rfl) ⟨465144, by rfl⟩ : syracuseStep 1240385 = 930289) B930289
theorem B4484429 : Blo 826349 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1240403 : Blo 826349 1240403 := bstep (se 1 (by rfl) ⟨930302, by rfl⟩ : syracuseStep 1240403 = 1860605) B1860605
theorem B1240433 : Blo 826349 1240433 := bstep (se 2 (by rfl) ⟨465162, by rfl⟩ : syracuseStep 1240433 = 930325) B930325
theorem B1240451 : Blo 826349 1240451 := bstep (se 1 (by rfl) ⟨930338, by rfl⟩ : syracuseStep 1240451 = 1860677) B1860677
theorem B1240481 : Blo 826349 1240481 := bstep (se 2 (by rfl) ⟨465180, by rfl⟩ : syracuseStep 1240481 = 930361) B930361
theorem B1863089 : Blo 826349 1863089 := bstep (se 2 (by rfl) ⟨698658, by rfl⟩ : syracuseStep 1863089 = 1397317) B1397317
theorem B1240499 : Blo 826349 1240499 := bstep (se 1 (by rfl) ⟨930374, by rfl⟩ : syracuseStep 1240499 = 1860749) B1860749
theorem B1863107 : Blo 826349 1863107 := bstep (se 1 (by rfl) ⟨1397330, by rfl⟩ : syracuseStep 1863107 = 2794661) B2794661
theorem B1240529 : Blo 826349 1240529 := bstep (se 2 (by rfl) ⟨465198, by rfl⟩ : syracuseStep 1240529 = 930397) B930397
theorem B1240547 : Blo 826349 1240547 := bstep (se 1 (by rfl) ⟨930410, by rfl⟩ : syracuseStep 1240547 = 1860821) B1860821
theorem B1240577 : Blo 826349 1240577 := bstep (se 2 (by rfl) ⟨465216, by rfl⟩ : syracuseStep 1240577 = 930433) B930433
theorem B1240595 : Blo 826349 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B1240625 : Blo 826349 1240625 := bstep (se 2 (by rfl) ⟨465234, by rfl⟩ : syracuseStep 1240625 = 930469) B930469
theorem B1240643 : Blo 826349 1240643 := bstep (se 1 (by rfl) ⟨930482, by rfl⟩ : syracuseStep 1240643 = 1860965) B1860965
theorem B2092625 : Blo 826349 2092625 := bstep (se 2 (by rfl) ⟨784734, by rfl⟩ : syracuseStep 2092625 = 1569469) B1569469
theorem B1240673 : Blo 826349 1240673 := bstep (se 2 (by rfl) ⟨465252, by rfl⟩ : syracuseStep 1240673 = 930505) B930505
theorem B1240691 : Blo 826349 1240691 := bstep (se 1 (by rfl) ⟨930518, by rfl⟩ : syracuseStep 1240691 = 1861037) B1861037
theorem B2092675 : Blo 826349 2092675 := bstep (se 1 (by rfl) ⟨1569506, by rfl⟩ : syracuseStep 2092675 = 3139013) B3139013
theorem B1240721 : Blo 826349 1240721 := bstep (se 2 (by rfl) ⟨465270, by rfl⟩ : syracuseStep 1240721 = 930541) B930541
theorem B1240739 : Blo 826349 1240739 := bstep (se 1 (by rfl) ⟨930554, by rfl⟩ : syracuseStep 1240739 = 1861109) B1861109
theorem B2649773 : Blo 826349 2649773 := bstep (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) B993665
theorem B1240769 : Blo 826349 1240769 := bstep (se 2 (by rfl) ⟨465288, by rfl⟩ : syracuseStep 1240769 = 930577) B930577
theorem B1863377 : Blo 826349 1863377 := bstep (se 2 (by rfl) ⟨698766, by rfl⟩ : syracuseStep 1863377 = 1397533) B1397533
theorem B1240787 : Blo 826349 1240787 := bstep (se 1 (by rfl) ⟨930590, by rfl⟩ : syracuseStep 1240787 = 1861181) B1861181
theorem B1863395 : Blo 826349 1863395 := bstep (se 1 (by rfl) ⟨1397546, by rfl⟩ : syracuseStep 1863395 = 2795093) B2795093
theorem B1240817 : Blo 826349 1240817 := bstep (se 2 (by rfl) ⟨465306, by rfl⟩ : syracuseStep 1240817 = 930613) B930613
theorem B1240835 : Blo 826349 1240835 := bstep (se 1 (by rfl) ⟨930626, by rfl⟩ : syracuseStep 1240835 = 1861253) B1861253
theorem B2092817 : Blo 826349 2092817 := bstep (se 2 (by rfl) ⟨784806, by rfl⟩ : syracuseStep 2092817 = 1569613) B1569613
theorem B1240865 : Blo 826349 1240865 := bstep (se 2 (by rfl) ⟨465324, by rfl⟩ : syracuseStep 1240865 = 930649) B930649
theorem B4484899 : Blo 826349 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B2354989 : Blo 826349 2354989 := bstep (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) B883121
theorem B1240883 : Blo 826349 1240883 := bstep (se 1 (by rfl) ⟨930662, by rfl⟩ : syracuseStep 1240883 = 1861325) B1861325
theorem B1240913 : Blo 826349 1240913 := bstep (se 2 (by rfl) ⟨465342, by rfl⟩ : syracuseStep 1240913 = 930685) B930685
theorem B1240931 : Blo 826349 1240931 := bstep (se 1 (by rfl) ⟨930698, by rfl⟩ : syracuseStep 1240931 = 1861397) B1861397
theorem B1240961 : Blo 826349 1240961 := bstep (se 2 (by rfl) ⟨465360, by rfl⟩ : syracuseStep 1240961 = 930721) B930721
theorem B1240979 : Blo 826349 1240979 := bstep (se 1 (by rfl) ⟨930734, by rfl⟩ : syracuseStep 1240979 = 1861469) B1861469
theorem B1241009 : Blo 826349 1241009 := bstep (se 2 (by rfl) ⟨465378, by rfl⟩ : syracuseStep 1241009 = 930757) B930757
theorem B4190129 : Blo 826349 4190129 := bstep (se 2 (by rfl) ⟨1571298, by rfl⟩ : syracuseStep 4190129 = 3142597) B3142597
theorem B1241027 : Blo 826349 1241027 := bstep (se 1 (by rfl) ⟨930770, by rfl⟩ : syracuseStep 1241027 = 1861541) B1861541
theorem B2355149 : Blo 826349 2355149 := bstep (se 3 (by rfl) ⟨441590, by rfl⟩ : syracuseStep 2355149 = 883181) B883181
theorem B1241057 : Blo 826349 1241057 := bstep (se 2 (by rfl) ⟨465396, by rfl⟩ : syracuseStep 1241057 = 930793) B930793
theorem B1863665 : Blo 826349 1863665 := bstep (se 2 (by rfl) ⟨698874, by rfl⟩ : syracuseStep 1863665 = 1397749) B1397749
theorem B1241075 : Blo 826349 1241075 := bstep (se 1 (by rfl) ⟨930806, by rfl⟩ : syracuseStep 1241075 = 1861613) B1861613
theorem B1863683 : Blo 826349 1863683 := bstep (se 1 (by rfl) ⟨1397762, by rfl⟩ : syracuseStep 1863683 = 2795525) B2795525
theorem B1241105 : Blo 826349 1241105 := bstep (se 2 (by rfl) ⟨465414, by rfl⟩ : syracuseStep 1241105 = 930829) B930829
theorem B1241123 : Blo 826349 1241123 := bstep (se 1 (by rfl) ⟨930842, by rfl⟩ : syracuseStep 1241123 = 1861685) B1861685
theorem B1241153 : Blo 826349 1241153 := bstep (se 2 (by rfl) ⟨465432, by rfl⟩ : syracuseStep 1241153 = 930865) B930865
theorem B1241171 : Blo 826349 1241171 := bstep (se 1 (by rfl) ⟨930878, by rfl⟩ : syracuseStep 1241171 = 1861757) B1861757
theorem B1241201 : Blo 826349 1241201 := bstep (se 2 (by rfl) ⟨465450, by rfl⟩ : syracuseStep 1241201 = 930901) B930901
theorem B1568899 : Blo 826349 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B2355331 : Blo 826349 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B1241219 : Blo 826349 1241219 := bstep (se 1 (by rfl) ⟨930914, by rfl⟩ : syracuseStep 1241219 = 1861829) B1861829
theorem B1241249 : Blo 826349 1241249 := bstep (se 2 (by rfl) ⟨465468, by rfl⟩ : syracuseStep 1241249 = 930937) B930937
theorem B1568945 : Blo 826349 1568945 := bstep (se 2 (by rfl) ⟨588354, by rfl⟩ : syracuseStep 1568945 = 1176709) B1176709
theorem B1241267 : Blo 826349 1241267 := bstep (se 1 (by rfl) ⟨930950, by rfl⟩ : syracuseStep 1241267 = 1861901) B1861901
theorem B1241297 : Blo 826349 1241297 := bstep (se 2 (by rfl) ⟨465486, by rfl⟩ : syracuseStep 1241297 = 930973) B930973
theorem B1241315 : Blo 826349 1241315 := bstep (se 1 (by rfl) ⟨930986, by rfl⟩ : syracuseStep 1241315 = 1861973) B1861973
theorem B1241345 : Blo 826349 1241345 := bstep (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) B931009
theorem B1863953 : Blo 826349 1863953 := bstep (se 2 (by rfl) ⟨698982, by rfl⟩ : syracuseStep 1863953 = 1397965) B1397965
theorem B1241363 : Blo 826349 1241363 := bstep (se 1 (by rfl) ⟨931022, by rfl⟩ : syracuseStep 1241363 = 1862045) B1862045
theorem B1863971 : Blo 826349 1863971 := bstep (se 1 (by rfl) ⟨1397978, by rfl⟩ : syracuseStep 1863971 = 2795957) B2795957
theorem B1241393 : Blo 826349 1241393 := bstep (se 2 (by rfl) ⟨465522, by rfl⟩ : syracuseStep 1241393 = 931045) B931045
theorem B1241411 : Blo 826349 1241411 := bstep (se 1 (by rfl) ⟨931058, by rfl⟩ : syracuseStep 1241411 = 1862117) B1862117
theorem B1241441 : Blo 826349 1241441 := bstep (se 2 (by rfl) ⟨465540, by rfl⟩ : syracuseStep 1241441 = 931081) B931081
theorem B1241459 : Blo 826349 1241459 := bstep (se 1 (by rfl) ⟨931094, by rfl⟩ : syracuseStep 1241459 = 1862189) B1862189
theorem B1241489 : Blo 826349 1241489 := bstep (se 2 (by rfl) ⟨465558, by rfl⟩ : syracuseStep 1241489 = 931117) B931117
theorem B1241507 : Blo 826349 1241507 := bstep (se 1 (by rfl) ⟨931130, by rfl⟩ : syracuseStep 1241507 = 1862261) B1862261
theorem B1241537 : Blo 826349 1241537 := bstep (se 2 (by rfl) ⟨465576, by rfl⟩ : syracuseStep 1241537 = 931153) B931153
theorem B1569233 : Blo 826349 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B1241555 : Blo 826349 1241555 := bstep (se 1 (by rfl) ⟨931166, by rfl⟩ : syracuseStep 1241555 = 1862333) B1862333
theorem B1241585 : Blo 826349 1241585 := bstep (se 2 (by rfl) ⟨465594, by rfl⟩ : syracuseStep 1241585 = 931189) B931189
theorem B1241603 : Blo 826349 1241603 := bstep (se 1 (by rfl) ⟨931202, by rfl⟩ : syracuseStep 1241603 = 1862405) B1862405
theorem B1241633 : Blo 826349 1241633 := bstep (se 2 (by rfl) ⟨465612, by rfl⟩ : syracuseStep 1241633 = 931225) B931225
theorem B1864241 : Blo 826349 1864241 := bstep (se 2 (by rfl) ⟨699090, by rfl⟩ : syracuseStep 1864241 = 1398181) B1398181
theorem B1241651 : Blo 826349 1241651 := bstep (se 1 (by rfl) ⟨931238, by rfl⟩ : syracuseStep 1241651 = 1862477) B1862477
theorem B1864259 : Blo 826349 1864259 := bstep (se 1 (by rfl) ⟨1398194, by rfl⟩ : syracuseStep 1864259 = 2796389) B2796389
theorem B1241681 : Blo 826349 1241681 := bstep (se 2 (by rfl) ⟨465630, by rfl⟩ : syracuseStep 1241681 = 931261) B931261
theorem B1241699 : Blo 826349 1241699 := bstep (se 1 (by rfl) ⟨931274, by rfl⟩ : syracuseStep 1241699 = 1862549) B1862549
theorem B13628017 : Blo 826349 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B1241729 : Blo 826349 1241729 := bstep (se 2 (by rfl) ⟨465648, by rfl⟩ : syracuseStep 1241729 = 931297) B931297
theorem B1241747 : Blo 826349 1241747 := bstep (se 1 (by rfl) ⟨931310, by rfl⟩ : syracuseStep 1241747 = 1862621) B1862621
theorem B1241777 : Blo 826349 1241777 := bstep (se 2 (by rfl) ⟨465666, by rfl⟩ : syracuseStep 1241777 = 931333) B931333
theorem B1241795 : Blo 826349 1241795 := bstep (se 1 (by rfl) ⟨931346, by rfl⟩ : syracuseStep 1241795 = 1862693) B1862693
theorem B1241825 : Blo 826349 1241825 := bstep (se 2 (by rfl) ⟨465684, by rfl⟩ : syracuseStep 1241825 = 931369) B931369
theorem B2093809 : Blo 826349 2093809 := bstep (se 2 (by rfl) ⟨785178, by rfl⟩ : syracuseStep 2093809 = 1570357) B1570357
theorem B3142385 : Blo 826349 3142385 := bstep (se 2 (by rfl) ⟨1178394, by rfl⟩ : syracuseStep 3142385 = 2356789) B2356789
theorem B1241843 : Blo 826349 1241843 := bstep (se 1 (by rfl) ⟨931382, by rfl⟩ : syracuseStep 1241843 = 1862765) B1862765
theorem B1241873 : Blo 826349 1241873 := bstep (se 2 (by rfl) ⟨465702, by rfl⟩ : syracuseStep 1241873 = 931405) B931405
theorem B1241891 : Blo 826349 1241891 := bstep (se 1 (by rfl) ⟨931418, by rfl⟩ : syracuseStep 1241891 = 1862837) B1862837
theorem B1241921 : Blo 826349 1241921 := bstep (se 2 (by rfl) ⟨465720, by rfl⟩ : syracuseStep 1241921 = 931441) B931441
theorem B4715333 : Blo 826349 4715333 := bstep (se 4 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 4715333 = 884125) B884125
theorem B1766225 : Blo 826349 1766225 := bstep (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) B1324669
theorem B1864529 : Blo 826349 1864529 := bstep (se 2 (by rfl) ⟨699198, by rfl⟩ : syracuseStep 1864529 = 1398397) B1398397
theorem B1241939 : Blo 826349 1241939 := bstep (se 1 (by rfl) ⟨931454, by rfl⟩ : syracuseStep 1241939 = 1862909) B1862909
theorem B1864547 : Blo 826349 1864547 := bstep (se 1 (by rfl) ⟨1398410, by rfl⟩ : syracuseStep 1864547 = 2796821) B2796821
theorem B1241969 : Blo 826349 1241969 := bstep (se 2 (by rfl) ⟨465738, by rfl⟩ : syracuseStep 1241969 = 931477) B931477
theorem B1241987 : Blo 826349 1241987 := bstep (se 1 (by rfl) ⟨931490, by rfl⟩ : syracuseStep 1241987 = 1862981) B1862981
theorem B1242017 : Blo 826349 1242017 := bstep (se 2 (by rfl) ⟨465756, by rfl⟩ : syracuseStep 1242017 = 931513) B931513
theorem B1242035 : Blo 826349 1242035 := bstep (se 1 (by rfl) ⟨931526, by rfl⟩ : syracuseStep 1242035 = 1863053) B1863053
theorem B1242065 : Blo 826349 1242065 := bstep (se 2 (by rfl) ⟨465774, by rfl⟩ : syracuseStep 1242065 = 931549) B931549
theorem B1242083 : Blo 826349 1242083 := bstep (se 1 (by rfl) ⟨931562, by rfl⟩ : syracuseStep 1242083 = 1863125) B1863125
theorem B1242113 : Blo 826349 1242113 := bstep (se 2 (by rfl) ⟨465792, by rfl⟩ : syracuseStep 1242113 = 931585) B931585
theorem B2094083 : Blo 826349 2094083 := bstep (se 1 (by rfl) ⟨1570562, by rfl⟩ : syracuseStep 2094083 = 3141125) B3141125
theorem B1242131 : Blo 826349 1242131 := bstep (se 1 (by rfl) ⟨931598, by rfl⟩ : syracuseStep 1242131 = 1863197) B1863197
theorem B1242161 : Blo 826349 1242161 := bstep (se 2 (by rfl) ⟨465810, by rfl⟩ : syracuseStep 1242161 = 931621) B931621
theorem B1242179 : Blo 826349 1242179 := bstep (se 1 (by rfl) ⟨931634, by rfl⟩ : syracuseStep 1242179 = 1863269) B1863269
theorem B1242209 : Blo 826349 1242209 := bstep (se 2 (by rfl) ⟨465828, by rfl⟩ : syracuseStep 1242209 = 931657) B931657
theorem B1864817 : Blo 826349 1864817 := bstep (se 2 (by rfl) ⟨699306, by rfl⟩ : syracuseStep 1864817 = 1398613) B1398613
theorem B1242227 : Blo 826349 1242227 := bstep (se 1 (by rfl) ⟨931670, by rfl⟩ : syracuseStep 1242227 = 1863341) B1863341
theorem B1864835 : Blo 826349 1864835 := bstep (se 1 (by rfl) ⟨1398626, by rfl⟩ : syracuseStep 1864835 = 2797253) B2797253
theorem B1242257 : Blo 826349 1242257 := bstep (se 2 (by rfl) ⟨465846, by rfl⟩ : syracuseStep 1242257 = 931693) B931693
theorem B1569955 : Blo 826349 1569955 := bstep (se 1 (by rfl) ⟨1177466, by rfl⟩ : syracuseStep 1569955 = 2354933) B2354933
theorem B1242275 : Blo 826349 1242275 := bstep (se 1 (by rfl) ⟨931706, by rfl⟩ : syracuseStep 1242275 = 1863413) B1863413
theorem B1242305 : Blo 826349 1242305 := bstep (se 2 (by rfl) ⟨465864, by rfl⟩ : syracuseStep 1242305 = 931729) B931729
theorem B2094275 : Blo 826349 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B1242323 : Blo 826349 1242323 := bstep (se 1 (by rfl) ⟨931742, by rfl⟩ : syracuseStep 1242323 = 1863485) B1863485
theorem B2651363 : Blo 826349 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B5305571 : Blo 826349 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B1242353 : Blo 826349 1242353 := bstep (se 2 (by rfl) ⟨465882, by rfl⟩ : syracuseStep 1242353 = 931765) B931765
theorem B1242371 : Blo 826349 1242371 := bstep (se 1 (by rfl) ⟨931778, by rfl⟩ : syracuseStep 1242371 = 1863557) B1863557
theorem B1242401 : Blo 826349 1242401 := bstep (se 2 (by rfl) ⟨465900, by rfl⟩ : syracuseStep 1242401 = 931801) B931801
theorem B1242419 : Blo 826349 1242419 := bstep (se 1 (by rfl) ⟨931814, by rfl⟩ : syracuseStep 1242419 = 1863629) B1863629
theorem B1242449 : Blo 826349 1242449 := bstep (se 2 (by rfl) ⟨465918, by rfl⟩ : syracuseStep 1242449 = 931837) B931837
theorem B4191587 : Blo 826349 4191587 := bstep (se 1 (by rfl) ⟨3143690, by rfl⟩ : syracuseStep 4191587 = 6287381) B6287381
theorem B1242467 : Blo 826349 1242467 := bstep (se 1 (by rfl) ⟨931850, by rfl⟩ : syracuseStep 1242467 = 1863701) B1863701
theorem B1242497 : Blo 826349 1242497 := bstep (se 2 (by rfl) ⟨465936, by rfl⟩ : syracuseStep 1242497 = 931873) B931873
theorem B1865105 : Blo 826349 1865105 := bstep (se 2 (by rfl) ⟨699414, by rfl⟩ : syracuseStep 1865105 = 1398829) B1398829
theorem B1242515 : Blo 826349 1242515 := bstep (se 1 (by rfl) ⟨931886, by rfl⟩ : syracuseStep 1242515 = 1863773) B1863773
theorem B1865123 : Blo 826349 1865123 := bstep (se 1 (by rfl) ⟨1398842, by rfl⟩ : syracuseStep 1865123 = 2797685) B2797685
theorem B2651555 : Blo 826349 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B1242545 : Blo 826349 1242545 := bstep (se 2 (by rfl) ⟨465954, by rfl⟩ : syracuseStep 1242545 = 931909) B931909
theorem B1242563 : Blo 826349 1242563 := bstep (se 1 (by rfl) ⟨931922, by rfl⟩ : syracuseStep 1242563 = 1863845) B1863845
theorem B1242593 : Blo 826349 1242593 := bstep (se 2 (by rfl) ⟨465972, by rfl⟩ : syracuseStep 1242593 = 931945) B931945
theorem B2356721 : Blo 826349 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B1242611 : Blo 826349 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B1242641 : Blo 826349 1242641 := bstep (se 2 (by rfl) ⟨465990, by rfl⟩ : syracuseStep 1242641 = 931981) B931981
theorem B1242659 : Blo 826349 1242659 := bstep (se 1 (by rfl) ⟨931994, by rfl⟩ : syracuseStep 1242659 = 1863989) B1863989
theorem B1242689 : Blo 826349 1242689 := bstep (se 2 (by rfl) ⟨466008, by rfl⟩ : syracuseStep 1242689 = 932017) B932017
theorem B1242707 : Blo 826349 1242707 := bstep (se 1 (by rfl) ⟨932030, by rfl⟩ : syracuseStep 1242707 = 1864061) B1864061
theorem B1570403 : Blo 826349 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B1242737 : Blo 826349 1242737 := bstep (se 2 (by rfl) ⟨466026, by rfl⟩ : syracuseStep 1242737 = 932053) B932053
theorem B1242755 : Blo 826349 1242755 := bstep (se 1 (by rfl) ⟨932066, by rfl⟩ : syracuseStep 1242755 = 1864133) B1864133
theorem B1242785 : Blo 826349 1242785 := bstep (se 2 (by rfl) ⟨466044, by rfl⟩ : syracuseStep 1242785 = 932089) B932089
theorem B1767089 : Blo 826349 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B1865393 : Blo 826349 1865393 := bstep (se 2 (by rfl) ⟨699522, by rfl⟩ : syracuseStep 1865393 = 1399045) B1399045
theorem B1177267 : Blo 826349 1177267 := bstep (se 1 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 1177267 = 1765901) B1765901
theorem B1242803 : Blo 826349 1242803 := bstep (se 1 (by rfl) ⟨932102, by rfl⟩ : syracuseStep 1242803 = 1864205) B1864205
theorem B1865411 : Blo 826349 1865411 := bstep (se 1 (by rfl) ⟨1399058, by rfl⟩ : syracuseStep 1865411 = 2798117) B2798117
theorem B5961413 : Blo 826349 5961413 := bstep (se 4 (by rfl) ⟨558882, by rfl⟩ : syracuseStep 5961413 = 1117765) B1117765
theorem B1242833 : Blo 826349 1242833 := bstep (se 2 (by rfl) ⟨466062, by rfl⟩ : syracuseStep 1242833 = 932125) B932125
theorem B1242851 : Blo 826349 1242851 := bstep (se 1 (by rfl) ⟨932138, by rfl⟩ : syracuseStep 1242851 = 1864277) B1864277
theorem B1242881 : Blo 826349 1242881 := bstep (se 2 (by rfl) ⟨466080, by rfl⟩ : syracuseStep 1242881 = 932161) B932161
theorem B882451 : Blo 826349 882451 := bstep (se 1 (by rfl) ⟨661838, by rfl⟩ : syracuseStep 882451 = 1323677) B1323677
theorem B1242899 : Blo 826349 1242899 := bstep (se 1 (by rfl) ⟨932174, by rfl⟩ : syracuseStep 1242899 = 1864349) B1864349
theorem B1242929 : Blo 826349 1242929 := bstep (se 2 (by rfl) ⟨466098, by rfl⟩ : syracuseStep 1242929 = 932197) B932197
theorem B1242947 : Blo 826349 1242947 := bstep (se 1 (by rfl) ⟨932210, by rfl⟩ : syracuseStep 1242947 = 1864421) B1864421
theorem B1242977 : Blo 826349 1242977 := bstep (se 2 (by rfl) ⟨466116, by rfl⟩ : syracuseStep 1242977 = 932233) B932233
theorem B1242995 : Blo 826349 1242995 := bstep (se 1 (by rfl) ⟨932246, by rfl⟩ : syracuseStep 1242995 = 1864493) B1864493
theorem B1570691 : Blo 826349 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B1243025 : Blo 826349 1243025 := bstep (se 2 (by rfl) ⟨466134, by rfl⟩ : syracuseStep 1243025 = 932269) B932269
theorem B1243043 : Blo 826349 1243043 := bstep (se 1 (by rfl) ⟨932282, by rfl⟩ : syracuseStep 1243043 = 1864565) B1864565
theorem B1243073 : Blo 826349 1243073 := bstep (se 2 (by rfl) ⟨466152, by rfl⟩ : syracuseStep 1243073 = 932305) B932305
theorem B1865681 : Blo 826349 1865681 := bstep (se 2 (by rfl) ⟨699630, by rfl⟩ : syracuseStep 1865681 = 1399261) B1399261
theorem B1243091 : Blo 826349 1243091 := bstep (se 1 (by rfl) ⟨932318, by rfl⟩ : syracuseStep 1243091 = 1864637) B1864637
theorem B1865699 : Blo 826349 1865699 := bstep (se 1 (by rfl) ⟨1399274, by rfl⟩ : syracuseStep 1865699 = 2798549) B2798549
theorem B1243121 : Blo 826349 1243121 := bstep (se 2 (by rfl) ⟨466170, by rfl⟩ : syracuseStep 1243121 = 932341) B932341
theorem B1046515 : Blo 826349 1046515 := bstep (se 1 (by rfl) ⟨784886, by rfl⟩ : syracuseStep 1046515 = 1569773) B1569773
theorem B1243139 : Blo 826349 1243139 := bstep (se 1 (by rfl) ⟨932354, by rfl⟩ : syracuseStep 1243139 = 1864709) B1864709
theorem B1243169 : Blo 826349 1243169 := bstep (se 2 (by rfl) ⟨466188, by rfl⟩ : syracuseStep 1243169 = 932377) B932377
theorem B2652209 : Blo 826349 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B1243187 : Blo 826349 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B1243217 : Blo 826349 1243217 := bstep (se 2 (by rfl) ⟨466206, by rfl⟩ : syracuseStep 1243217 = 932413) B932413
theorem B1046611 : Blo 826349 1046611 := bstep (se 1 (by rfl) ⟨784958, by rfl⟩ : syracuseStep 1046611 = 1569917) B1569917
theorem B1243235 : Blo 826349 1243235 := bstep (se 1 (by rfl) ⟨932426, by rfl⟩ : syracuseStep 1243235 = 1864853) B1864853
theorem B2095217 : Blo 826349 2095217 := bstep (se 2 (by rfl) ⟨785706, by rfl⟩ : syracuseStep 2095217 = 1571413) B1571413
theorem B1243265 : Blo 826349 1243265 := bstep (se 2 (by rfl) ⟨466224, by rfl⟩ : syracuseStep 1243265 = 932449) B932449
theorem B4192397 : Blo 826349 4192397 := bstep (se 3 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 4192397 = 1572149) B1572149
theorem B1177745 : Blo 826349 1177745 := bstep (se 2 (by rfl) ⟨441654, by rfl⟩ : syracuseStep 1177745 = 883309) B883309
theorem B1243283 : Blo 826349 1243283 := bstep (se 1 (by rfl) ⟨932462, by rfl⟩ : syracuseStep 1243283 = 1864925) B1864925
theorem B2095267 : Blo 826349 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B3143843 : Blo 826349 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B1243313 : Blo 826349 1243313 := bstep (se 2 (by rfl) ⟨466242, by rfl⟩ : syracuseStep 1243313 = 932485) B932485
theorem B1243331 : Blo 826349 1243331 := bstep (se 1 (by rfl) ⟨932498, by rfl⟩ : syracuseStep 1243331 = 1864997) B1864997
theorem B1243361 : Blo 826349 1243361 := bstep (se 2 (by rfl) ⟨466260, by rfl⟩ : syracuseStep 1243361 = 932521) B932521
theorem B1865969 : Blo 826349 1865969 := bstep (se 2 (by rfl) ⟨699738, by rfl⟩ : syracuseStep 1865969 = 1399477) B1399477
theorem B1243379 : Blo 826349 1243379 := bstep (se 1 (by rfl) ⟨932534, by rfl⟩ : syracuseStep 1243379 = 1865069) B1865069
theorem B1177859 : Blo 826349 1177859 := bstep (se 1 (by rfl) ⟨883394, by rfl⟩ : syracuseStep 1177859 = 1766789) B1766789
theorem B1865987 : Blo 826349 1865987 := bstep (se 1 (by rfl) ⟨1399490, by rfl⟩ : syracuseStep 1865987 = 2798981) B2798981
theorem B1243409 : Blo 826349 1243409 := bstep (se 2 (by rfl) ⟨466278, by rfl⟩ : syracuseStep 1243409 = 932557) B932557
theorem B1243427 : Blo 826349 1243427 := bstep (se 1 (by rfl) ⟨932570, by rfl⟩ : syracuseStep 1243427 = 1865141) B1865141
theorem B2095409 : Blo 826349 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B1243457 : Blo 826349 1243457 := bstep (se 2 (by rfl) ⟨466296, by rfl⟩ : syracuseStep 1243457 = 932593) B932593
theorem B1177939 : Blo 826349 1177939 := bstep (se 1 (by rfl) ⟨883454, by rfl⟩ : syracuseStep 1177939 = 1766909) B1766909
theorem B1243475 : Blo 826349 1243475 := bstep (se 1 (by rfl) ⟨932606, by rfl⟩ : syracuseStep 1243475 = 1865213) B1865213
theorem B1243505 : Blo 826349 1243505 := bstep (se 2 (by rfl) ⟨466314, by rfl⟩ : syracuseStep 1243505 = 932629) B932629
theorem B1243523 : Blo 826349 1243523 := bstep (se 1 (by rfl) ⟨932642, by rfl⟩ : syracuseStep 1243523 = 1865285) B1865285
theorem B1243553 : Blo 826349 1243553 := bstep (se 2 (by rfl) ⟨466332, by rfl⟩ : syracuseStep 1243553 = 932665) B932665
theorem B2357677 : Blo 826349 2357677 := bstep (se 3 (by rfl) ⟨442064, by rfl⟩ : syracuseStep 2357677 = 884129) B884129
theorem B1243571 : Blo 826349 1243571 := bstep (se 1 (by rfl) ⟨932678, by rfl⟩ : syracuseStep 1243571 = 1865357) B1865357
theorem B1243601 : Blo 826349 1243601 := bstep (se 2 (by rfl) ⟨466350, by rfl⟩ : syracuseStep 1243601 = 932701) B932701
theorem B1243619 : Blo 826349 1243619 := bstep (se 1 (by rfl) ⟨932714, by rfl⟩ : syracuseStep 1243619 = 1865429) B1865429
theorem B1243649 : Blo 826349 1243649 := bstep (se 2 (by rfl) ⟨466368, by rfl⟩ : syracuseStep 1243649 = 932737) B932737
theorem B1866257 : Blo 826349 1866257 := bstep (se 2 (by rfl) ⟨699846, by rfl⟩ : syracuseStep 1866257 = 1399693) B1399693
theorem B1243667 : Blo 826349 1243667 := bstep (se 1 (by rfl) ⟨932750, by rfl⟩ : syracuseStep 1243667 = 1865501) B1865501
theorem B1866275 : Blo 826349 1866275 := bstep (se 1 (by rfl) ⟨1399706, by rfl⟩ : syracuseStep 1866275 = 2799413) B2799413
theorem B1243697 : Blo 826349 1243697 := bstep (se 2 (by rfl) ⟨466386, by rfl⟩ : syracuseStep 1243697 = 932773) B932773
theorem B1047107 : Blo 826349 1047107 := bstep (se 1 (by rfl) ⟨785330, by rfl⟩ : syracuseStep 1047107 = 1570661) B1570661
theorem B1243715 : Blo 826349 1243715 := bstep (se 1 (by rfl) ⟨932786, by rfl⟩ : syracuseStep 1243715 = 1865573) B1865573
theorem B1243745 : Blo 826349 1243745 := bstep (se 2 (by rfl) ⟨466404, by rfl⟩ : syracuseStep 1243745 = 932809) B932809
theorem B1243763 : Blo 826349 1243763 := bstep (se 1 (by rfl) ⟨932822, by rfl⟩ : syracuseStep 1243763 = 1865645) B1865645
theorem B2357905 : Blo 826349 2357905 := bstep (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) B1768429
theorem B1243793 : Blo 826349 1243793 := bstep (se 2 (by rfl) ⟨466422, by rfl⟩ : syracuseStep 1243793 = 932845) B932845
theorem B1243811 : Blo 826349 1243811 := bstep (se 1 (by rfl) ⟨932858, by rfl⟩ : syracuseStep 1243811 = 1865717) B1865717
theorem B1243841 : Blo 826349 1243841 := bstep (se 2 (by rfl) ⟨466440, by rfl⟩ : syracuseStep 1243841 = 932881) B932881
theorem B1243859 : Blo 826349 1243859 := bstep (se 1 (by rfl) ⟨932894, by rfl⟩ : syracuseStep 1243859 = 1865789) B1865789
theorem B1243889 : Blo 826349 1243889 := bstep (se 2 (by rfl) ⟨466458, by rfl⟩ : syracuseStep 1243889 = 932917) B932917
theorem B1243907 : Blo 826349 1243907 := bstep (se 1 (by rfl) ⟨932930, by rfl⟩ : syracuseStep 1243907 = 1865861) B1865861
theorem B1243937 : Blo 826349 1243937 := bstep (se 2 (by rfl) ⟨466476, by rfl⟩ : syracuseStep 1243937 = 932953) B932953
theorem B1571633 : Blo 826349 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B2358065 : Blo 826349 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B1243955 : Blo 826349 1243955 := bstep (se 1 (by rfl) ⟨932966, by rfl⟩ : syracuseStep 1243955 = 1865933) B1865933
theorem B1866545 : Blo 826349 1866545 := bstep (se 2 (by rfl) ⟨699954, by rfl⟩ : syracuseStep 1866545 = 1399909) B1399909
theorem B1866563 : Blo 826349 1866563 := bstep (se 1 (by rfl) ⟨1399922, by rfl⟩ : syracuseStep 1866563 = 2799845) B2799845
theorem B2685773 : Blo 826349 2685773 := bstep (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) B1007165
theorem B1243985 : Blo 826349 1243985 := bstep (se 2 (by rfl) ⟨466494, by rfl⟩ : syracuseStep 1243985 = 932989) B932989
theorem B1244003 : Blo 826349 1244003 := bstep (se 1 (by rfl) ⟨933002, by rfl⟩ : syracuseStep 1244003 = 1866005) B1866005
theorem B1178497 : Blo 826349 1178497 := bstep (se 2 (by rfl) ⟨441936, by rfl⟩ : syracuseStep 1178497 = 883873) B883873
theorem B1244033 : Blo 826349 1244033 := bstep (se 2 (by rfl) ⟨466512, by rfl⟩ : syracuseStep 1244033 = 933025) B933025
theorem B1244051 : Blo 826349 1244051 := bstep (se 1 (by rfl) ⟨933038, by rfl⟩ : syracuseStep 1244051 = 1866077) B1866077
theorem B2358179 : Blo 826349 2358179 := bstep (se 1 (by rfl) ⟨1768634, by rfl⟩ : syracuseStep 2358179 = 3537269) B3537269
theorem B1244081 : Blo 826349 1244081 := bstep (se 2 (by rfl) ⟨466530, by rfl⟩ : syracuseStep 1244081 = 933061) B933061
theorem B1768387 : Blo 826349 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B1244099 : Blo 826349 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B1244129 : Blo 826349 1244129 := bstep (se 2 (by rfl) ⟨466548, by rfl⟩ : syracuseStep 1244129 = 933097) B933097
theorem B1244147 : Blo 826349 1244147 := bstep (se 1 (by rfl) ⟨933110, by rfl⟩ : syracuseStep 1244147 = 1866221) B1866221
theorem B883715 : Blo 826349 883715 := bstep (se 1 (by rfl) ⟨662786, by rfl⟩ : syracuseStep 883715 = 1325573) B1325573
theorem B1244177 : Blo 826349 1244177 := bstep (se 2 (by rfl) ⟨466566, by rfl⟩ : syracuseStep 1244177 = 933133) B933133
theorem B1244195 : Blo 826349 1244195 := bstep (se 1 (by rfl) ⟨933146, by rfl⟩ : syracuseStep 1244195 = 1866293) B1866293
theorem B1244225 : Blo 826349 1244225 := bstep (se 2 (by rfl) ⟨466584, by rfl⟩ : syracuseStep 1244225 = 933169) B933169
theorem B1866833 : Blo 826349 1866833 := bstep (se 2 (by rfl) ⟨700062, by rfl⟩ : syracuseStep 1866833 = 1400125) B1400125
theorem B1244243 : Blo 826349 1244243 := bstep (se 1 (by rfl) ⟨933182, by rfl⟩ : syracuseStep 1244243 = 1866365) B1866365
theorem B3538019 : Blo 826349 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B1866851 : Blo 826349 1866851 := bstep (se 1 (by rfl) ⟨1400138, by rfl⟩ : syracuseStep 1866851 = 2800277) B2800277
theorem B1244273 : Blo 826349 1244273 := bstep (se 2 (by rfl) ⟨466602, by rfl⟩ : syracuseStep 1244273 = 933205) B933205
theorem B1244291 : Blo 826349 1244291 := bstep (se 1 (by rfl) ⟨933218, by rfl⟩ : syracuseStep 1244291 = 1866437) B1866437
theorem B3144845 : Blo 826349 3144845 := bstep (se 3 (by rfl) ⟨589658, by rfl⟩ : syracuseStep 3144845 = 1179317) B1179317
theorem B1244321 : Blo 826349 1244321 := bstep (se 2 (by rfl) ⟨466620, by rfl⟩ : syracuseStep 1244321 = 933241) B933241
theorem B1244339 : Blo 826349 1244339 := bstep (se 1 (by rfl) ⟨933254, by rfl⟩ : syracuseStep 1244339 = 1866509) B1866509
theorem B1244369 : Blo 826349 1244369 := bstep (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) B933277
theorem B1244387 : Blo 826349 1244387 := bstep (se 1 (by rfl) ⟨933290, by rfl⟩ : syracuseStep 1244387 = 1866581) B1866581
theorem B1244417 : Blo 826349 1244417 := bstep (se 2 (by rfl) ⟨466656, by rfl⟩ : syracuseStep 1244417 = 933313) B933313
theorem B1047811 : Blo 826349 1047811 := bstep (se 1 (by rfl) ⟨785858, by rfl⟩ : syracuseStep 1047811 = 1571717) B1571717
theorem B2096401 : Blo 826349 2096401 := bstep (se 2 (by rfl) ⟨786150, by rfl⟩ : syracuseStep 2096401 = 1572301) B1572301
theorem B1277203 : Blo 826349 1277203 := bstep (se 1 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 1277203 = 1915805) B1915805
theorem B1244435 : Blo 826349 1244435 := bstep (se 1 (by rfl) ⟨933326, by rfl⟩ : syracuseStep 1244435 = 1866653) B1866653
theorem B1244465 : Blo 826349 1244465 := bstep (se 2 (by rfl) ⟨466674, by rfl⟩ : syracuseStep 1244465 = 933349) B933349
theorem B1244483 : Blo 826349 1244483 := bstep (se 1 (by rfl) ⟨933362, by rfl⟩ : syracuseStep 1244483 = 1866725) B1866725
theorem B1244513 : Blo 826349 1244513 := bstep (se 2 (by rfl) ⟨466692, by rfl⟩ : syracuseStep 1244513 = 933385) B933385
theorem B1047907 : Blo 826349 1047907 := bstep (se 1 (by rfl) ⟨785930, by rfl⟩ : syracuseStep 1047907 = 1571861) B1571861
theorem B1867121 : Blo 826349 1867121 := bstep (se 2 (by rfl) ⟨700170, by rfl⟩ : syracuseStep 1867121 = 1400341) B1400341
theorem B1244531 : Blo 826349 1244531 := bstep (se 1 (by rfl) ⟨933398, by rfl⟩ : syracuseStep 1244531 = 1866797) B1866797
theorem B1867139 : Blo 826349 1867139 := bstep (se 1 (by rfl) ⟨1400354, by rfl⟩ : syracuseStep 1867139 = 2800709) B2800709
theorem B1244561 : Blo 826349 1244561 := bstep (se 2 (by rfl) ⟨466710, by rfl⟩ : syracuseStep 1244561 = 933421) B933421
theorem B1244579 : Blo 826349 1244579 := bstep (se 1 (by rfl) ⟨933434, by rfl⟩ : syracuseStep 1244579 = 1866869) B1866869
theorem B1244609 : Blo 826349 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B1244627 : Blo 826349 1244627 := bstep (se 1 (by rfl) ⟨933470, by rfl⟩ : syracuseStep 1244627 = 1866941) B1866941
theorem B7962083 : Blo 826349 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B1244657 : Blo 826349 1244657 := bstep (se 2 (by rfl) ⟨466746, by rfl⟩ : syracuseStep 1244657 = 933493) B933493
theorem B1244675 : Blo 826349 1244675 := bstep (se 1 (by rfl) ⟨933506, by rfl⟩ : syracuseStep 1244675 = 1867013) B1867013
theorem B1244705 : Blo 826349 1244705 := bstep (se 2 (by rfl) ⟨466764, by rfl⟩ : syracuseStep 1244705 = 933529) B933529
theorem B2096675 : Blo 826349 2096675 := bstep (se 1 (by rfl) ⟨1572506, by rfl⟩ : syracuseStep 2096675 = 3145013) B3145013
theorem B2522659 : Blo 826349 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B2391601 : Blo 826349 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B1244723 : Blo 826349 1244723 := bstep (se 1 (by rfl) ⟨933542, by rfl⟩ : syracuseStep 1244723 = 1867085) B1867085
theorem B1179203 : Blo 826349 1179203 := bstep (se 1 (by rfl) ⟨884402, by rfl⟩ : syracuseStep 1179203 = 1768805) B1768805
theorem B1244753 : Blo 826349 1244753 := bstep (se 2 (by rfl) ⟨466782, by rfl⟩ : syracuseStep 1244753 = 933565) B933565
theorem B1244771 : Blo 826349 1244771 := bstep (se 1 (by rfl) ⟨933578, by rfl⟩ : syracuseStep 1244771 = 1867157) B1867157
theorem B1244801 : Blo 826349 1244801 := bstep (se 2 (by rfl) ⟨466800, by rfl⟩ : syracuseStep 1244801 = 933601) B933601
theorem B1867409 : Blo 826349 1867409 := bstep (se 2 (by rfl) ⟨700278, by rfl⟩ : syracuseStep 1867409 = 1400557) B1400557
theorem B1244819 : Blo 826349 1244819 := bstep (se 1 (by rfl) ⟨933614, by rfl⟩ : syracuseStep 1244819 = 1867229) B1867229
theorem B1867427 : Blo 826349 1867427 := bstep (se 1 (by rfl) ⟨1400570, by rfl⟩ : syracuseStep 1867427 = 2801141) B2801141
theorem B1572529 : Blo 826349 1572529 := bstep (se 2 (by rfl) ⟨589698, by rfl⟩ : syracuseStep 1572529 = 1179397) B1179397
theorem B1244849 : Blo 826349 1244849 := bstep (se 2 (by rfl) ⟨466818, by rfl⟩ : syracuseStep 1244849 = 933637) B933637
theorem B1244867 : Blo 826349 1244867 := bstep (se 1 (by rfl) ⟨933650, by rfl⟩ : syracuseStep 1244867 = 1867301) B1867301
theorem B2096867 : Blo 826349 2096867 := bstep (se 1 (by rfl) ⟨1572650, by rfl⟩ : syracuseStep 2096867 = 3145301) B3145301
theorem B1244897 : Blo 826349 1244897 := bstep (se 2 (by rfl) ⟨466836, by rfl⟩ : syracuseStep 1244897 = 933673) B933673
theorem B884467 : Blo 826349 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B1244915 : Blo 826349 1244915 := bstep (se 1 (by rfl) ⟨933686, by rfl⟩ : syracuseStep 1244915 = 1867373) B1867373
theorem B1244945 : Blo 826349 1244945 := bstep (se 2 (by rfl) ⟨466854, by rfl⟩ : syracuseStep 1244945 = 933709) B933709
theorem B1244963 : Blo 826349 1244963 := bstep (se 1 (by rfl) ⟨933722, by rfl⟩ : syracuseStep 1244963 = 1867445) B1867445
theorem B1244993 : Blo 826349 1244993 := bstep (se 2 (by rfl) ⟨466872, by rfl⟩ : syracuseStep 1244993 = 933745) B933745
theorem B6291269 : Blo 826349 6291269 := bstep (se 4 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 6291269 = 1179613) B1179613
theorem B1572689 : Blo 826349 1572689 := bstep (se 2 (by rfl) ⟨589758, by rfl⟩ : syracuseStep 1572689 = 1179517) B1179517
theorem B1048403 : Blo 826349 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B1245011 : Blo 826349 1245011 := bstep (se 1 (by rfl) ⟨933758, by rfl⟩ : syracuseStep 1245011 = 1867517) B1867517
theorem B1245041 : Blo 826349 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B1245059 : Blo 826349 1245059 := bstep (se 1 (by rfl) ⟨933794, by rfl⟩ : syracuseStep 1245059 = 1867589) B1867589
theorem B2359181 : Blo 826349 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B1245089 : Blo 826349 1245089 := bstep (se 2 (by rfl) ⟨466908, by rfl⟩ : syracuseStep 1245089 = 933817) B933817
theorem B1867697 : Blo 826349 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B1245107 : Blo 826349 1245107 := bstep (se 1 (by rfl) ⟨933830, by rfl⟩ : syracuseStep 1245107 = 1867661) B1867661
theorem B1867715 : Blo 826349 1867715 := bstep (se 1 (by rfl) ⟨1400786, by rfl⟩ : syracuseStep 1867715 = 2801573) B2801573
theorem B1245137 : Blo 826349 1245137 := bstep (se 2 (by rfl) ⟨466926, by rfl⟩ : syracuseStep 1245137 = 933853) B933853
theorem B1245155 : Blo 826349 1245155 := bstep (se 1 (by rfl) ⟨933866, by rfl⟩ : syracuseStep 1245155 = 1867733) B1867733
theorem B1867787 : Blo 826349 1867787 := bstep (se 1 (by rfl) ⟨1400840, by rfl⟩ : syracuseStep 1867787 = 2801681) B2801681
theorem B3538961 : Blo 826349 3538961 := bstep (se 2 (by rfl) ⟨1327110, by rfl⟩ : syracuseStep 3538961 = 2654221) B2654221
theorem B1245209 : Blo 826349 1245209 := bstep (se 2 (by rfl) ⟨466953, by rfl⟩ : syracuseStep 1245209 = 933907) B933907
theorem B1867841 : Blo 826349 1867841 := bstep (se 2 (by rfl) ⟨700440, by rfl⟩ : syracuseStep 1867841 = 1400881) B1400881
theorem B3145817 : Blo 826349 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B5308517 : Blo 826349 5308517 := bstep (se 4 (by rfl) ⟨497673, by rfl⟩ : syracuseStep 5308517 = 995347) B995347
theorem B1245323 : Blo 826349 1245323 := bstep (se 1 (by rfl) ⟨933992, by rfl⟩ : syracuseStep 1245323 = 1867985) B1867985
theorem B1573015 : Blo 826349 1573015 := bstep (se 1 (by rfl) ⟨1179761, by rfl⟩ : syracuseStep 1573015 = 2359523) B2359523
theorem B1048727 : Blo 826349 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B1245335 : Blo 826349 1245335 := bstep (se 1 (by rfl) ⟨934001, by rfl⟩ : syracuseStep 1245335 = 1868003) B1868003
theorem B6127795 : Blo 826349 6127795 := bstep (se 1 (by rfl) ⟨4595846, by rfl⟩ : syracuseStep 6127795 = 9191693) B9191693
theorem B2359489 : Blo 826349 2359489 := bstep (se 2 (by rfl) ⟨884808, by rfl⟩ : syracuseStep 2359489 = 1769617) B1769617
theorem B2982091 : Blo 826349 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B1245401 : Blo 826349 1245401 := bstep (se 2 (by rfl) ⟨467025, by rfl⟩ : syracuseStep 1245401 = 934051) B934051
theorem B1573121 : Blo 826349 1573121 := bstep (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) B1179841
theorem B1868057 : Blo 826349 1868057 := bstep (se 2 (by rfl) ⟨700521, by rfl⟩ : syracuseStep 1868057 = 1401043) B1401043
theorem B1769779 : Blo 826349 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B1245515 : Blo 826349 1245515 := bstep (se 1 (by rfl) ⟨934136, by rfl⟩ : syracuseStep 1245515 = 1868273) B1868273
theorem B1868147 : Blo 826349 1868147 := bstep (se 1 (by rfl) ⟨1401110, by rfl⟩ : syracuseStep 1868147 = 2802221) B2802221
theorem B4718999 : Blo 826349 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B1868183 : Blo 826349 1868183 := bstep (se 1 (by rfl) ⟨1401137, by rfl⟩ : syracuseStep 1868183 = 2802275) B2802275
theorem B1573273 : Blo 826349 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B885163 : Blo 826349 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B1180183 : Blo 826349 1180183 := bstep (se 1 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 1180183 = 1770275) B1770275
theorem B7570097 : Blo 826349 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B6292241 : Blo 826349 6292241 := bstep (se 2 (by rfl) ⟨2359590, by rfl⟩ : syracuseStep 6292241 = 4719181) B4719181
theorem B2097971 : Blo 826349 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1049431 : Blo 826349 1049431 := bstep (se 1 (by rfl) ⟨787073, by rfl⟩ : syracuseStep 1049431 = 1574147) B1574147
theorem B2655155 : Blo 826349 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B3539933 : Blo 826349 3539933 := bstep (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) B1327475
theorem B1180747 : Blo 826349 1180747 := bstep (se 1 (by rfl) ⟨885560, by rfl⟩ : syracuseStep 1180747 = 1771121) B1771121
theorem B3769523 : Blo 826349 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B6980825 : Blo 826349 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B2098507 : Blo 826349 2098507 := bstep (se 1 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 2098507 = 3147761) B3147761
theorem B55248277 : Blo 826349 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B120620501 : Blo 826349 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B886231 : Blo 826349 886231 := bstep (se 1 (by rfl) ⟨664673, by rfl⟩ : syracuseStep 886231 = 1329347) B1329347
theorem B2098649 : Blo 826349 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B2983475 : Blo 826349 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B3147443 : Blo 826349 3147443 := bstep (se 1 (by rfl) ⟨2360582, by rfl⟩ : syracuseStep 3147443 = 4721165) B4721165
theorem B1574579 : Blo 826349 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B3147457 : Blo 826349 3147457 := bstep (se 2 (by rfl) ⟨1180296, by rfl⟩ : syracuseStep 3147457 = 2360593) B2360593
theorem B1771265 : Blo 826349 1771265 := bstep (se 2 (by rfl) ⟨664224, by rfl⟩ : syracuseStep 1771265 = 1328449) B1328449
theorem B2361163 : Blo 826349 2361163 := bstep (se 1 (by rfl) ⟨1770872, by rfl⟩ : syracuseStep 2361163 = 3541745) B3541745
theorem B1574731 : Blo 826349 1574731 := bstep (se 1 (by rfl) ⟨1181048, by rfl⟩ : syracuseStep 1574731 = 2362097) B2362097
theorem B1771607 : Blo 826349 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B2361437 : Blo 826349 2361437 := bstep (se 3 (by rfl) ⟨442769, by rfl⟩ : syracuseStep 2361437 = 885539) B885539
theorem B1575065 : Blo 826349 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B7080209 : Blo 826349 7080209 := bstep (se 2 (by rfl) ⟨2655078, by rfl⟩ : syracuseStep 7080209 = 5310157) B5310157
theorem B4720913 : Blo 826349 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B2099479 : Blo 826349 2099479 := bstep (se 1 (by rfl) ⟨1574609, by rfl⟩ : syracuseStep 2099479 = 3149219) B3149219
theorem B7670051 : Blo 826349 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B1771915 : Blo 826349 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B3541421 : Blo 826349 3541421 := bstep (se 3 (by rfl) ⟨664016, by rfl⟩ : syracuseStep 3541421 = 1328033) B1328033
theorem B5966257 : Blo 826349 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B1182233 : Blo 826349 1182233 := bstep (se 2 (by rfl) ⟨443337, by rfl⟩ : syracuseStep 1182233 = 886675) B886675
theorem B2099915 : Blo 826349 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B1575703 : Blo 826349 1575703 := bstep (se 1 (by rfl) ⟨1181777, by rfl⟩ : syracuseStep 1575703 = 2363555) B2363555
theorem B14158637 : Blo 826349 14158637 := bstep (se 3 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 14158637 = 5309489) B5309489
theorem B15928163 : Blo 826349 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B8948657 : Blo 826349 8948657 := bstep (se 2 (by rfl) ⟨3355746, by rfl⟩ : syracuseStep 8948657 = 6711493) B6711493
theorem B2985005 : Blo 826349 2985005 := bstep (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) B1119377
theorem B2100289 : Blo 826349 2100289 := bstep (se 2 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 2100289 = 1575217) B1575217
theorem B1772761 : Blo 826349 1772761 := bstep (se 2 (by rfl) ⟨664785, by rfl⟩ : syracuseStep 1772761 = 1329571) B1329571
theorem B72682757 : Blo 826349 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B5967179 : Blo 826349 5967179 := bstep (se 1 (by rfl) ⟨4475384, by rfl⟩ : syracuseStep 5967179 = 8950769) B8950769
theorem B3182017 : Blo 826349 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B4197905 : Blo 826349 4197905 := bstep (se 2 (by rfl) ⟨1574214, by rfl⟩ : syracuseStep 4197905 = 3148429) B3148429
theorem B3149387 : Blo 826349 3149387 := bstep (se 1 (by rfl) ⟨2362040, by rfl⟩ : syracuseStep 3149387 = 4724081) B4724081
theorem B3149401 : Blo 826349 3149401 := bstep (se 2 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 3149401 = 2362051) B2362051
theorem B2100887 : Blo 826349 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B4198067 : Blo 826349 4198067 := bstep (se 1 (by rfl) ⟨3148550, by rfl⟩ : syracuseStep 4198067 = 6297101) B6297101
theorem B2985665 : Blo 826349 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B1675417 : Blo 826349 1675417 := bstep (se 2 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 1675417 = 1256563) B1256563
theorem B1511639 : Blo 826349 1511639 := bstep (se 1 (by rfl) ⟨1133729, by rfl⟩ : syracuseStep 1511639 = 2267459) B2267459
theorem B3543385 : Blo 826349 3543385 := bstep (se 2 (by rfl) ⟨1328769, by rfl⟩ : syracuseStep 3543385 = 2657539) B2657539
theorem B2363737 : Blo 826349 2363737 := bstep (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) B1772803
theorem B2101697 : Blo 826349 2101697 := bstep (se 2 (by rfl) ⟨788136, by rfl⟩ : syracuseStep 2101697 = 1576273) B1576273
theorem B2429405 : Blo 826349 2429405 := bstep (se 3 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 2429405 = 911027) B911027
theorem B3150359 : Blo 826349 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B6296129 : Blo 826349 6296129 := bstep (se 2 (by rfl) ⟨2361048, by rfl⟩ : syracuseStep 6296129 = 4722097) B4722097
theorem B2789963 : Blo 826349 2789963 := bstep (se 1 (by rfl) ⟨2092472, by rfl⟩ : syracuseStep 2789963 = 4184945) B4184945
theorem B2790233 : Blo 826349 2790233 := bstep (se 2 (by rfl) ⟨1046337, by rfl⟩ : syracuseStep 2790233 = 2092675) B2092675
theorem B2364353 : Blo 826349 2364353 := bstep (se 2 (by rfl) ⟨886632, by rfl⟩ : syracuseStep 2364353 = 1773265) B1773265
theorem B3544343 : Blo 826349 3544343 := bstep (se 1 (by rfl) ⟨2658257, by rfl⟩ : syracuseStep 3544343 = 5316515) B5316515
theorem B1414667 : Blo 826349 1414667 := bstep (se 1 (by rfl) ⟨1061000, by rfl⟩ : syracuseStep 1414667 = 2122001) B2122001
theorem B2790935 : Blo 826349 2790935 := bstep (se 1 (by rfl) ⟨2093201, by rfl⟩ : syracuseStep 2790935 = 4186403) B4186403
theorem B4200011 : Blo 826349 4200011 := bstep (se 1 (by rfl) ⟨3150008, by rfl⟩ : syracuseStep 4200011 = 6300017) B6300017
theorem B4789853 : Blo 826349 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B3151619 : Blo 826349 3151619 := bstep (se 1 (by rfl) ⟨2363714, by rfl⟩ : syracuseStep 3151619 = 4727429) B4727429
theorem B2791475 : Blo 826349 2791475 := bstep (se 1 (by rfl) ⟨2093606, by rfl⟩ : syracuseStep 2791475 = 4187213) B4187213
theorem B2791745 : Blo 826349 2791745 := bstep (se 2 (by rfl) ⟨1046904, by rfl⟩ : syracuseStep 2791745 = 2093809) B2093809
theorem B2988377 : Blo 826349 2988377 := bstep (se 2 (by rfl) ⟨1120641, by rfl⟩ : syracuseStep 2988377 = 2241283) B2241283
theorem B2988433 : Blo 826349 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B6298073 : Blo 826349 6298073 := bstep (se 2 (by rfl) ⟨2361777, by rfl⟩ : syracuseStep 6298073 = 4723555) B4723555
theorem B7543313 : Blo 826349 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B12098117 : Blo 826349 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B1514137 : Blo 826349 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B2235097 : Blo 826349 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B2792285 : Blo 826349 2792285 := bstep (se 3 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 2792285 = 1047107) B1047107
theorem B826359 : Blo 826349 826359 := bstep (se 1 (by rfl) ⟨619769, by rfl⟩ : syracuseStep 826359 = 1239539) B1239539
theorem B826379 : Blo 826349 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B826391 : Blo 826349 826391 := bstep (se 1 (by rfl) ⟨619793, by rfl⟩ : syracuseStep 826391 = 1239587) B1239587
theorem B826411 : Blo 826349 826411 := bstep (se 1 (by rfl) ⟨619808, by rfl⟩ : syracuseStep 826411 = 1239617) B1239617
theorem B2235443 : Blo 826349 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B826423 : Blo 826349 826423 := bstep (se 1 (by rfl) ⟨619817, by rfl⟩ : syracuseStep 826423 = 1239635) B1239635
theorem B826443 : Blo 826349 826443 := bstep (se 1 (by rfl) ⟨619832, by rfl⟩ : syracuseStep 826443 = 1239665) B1239665
theorem B826455 : Blo 826349 826455 := bstep (se 1 (by rfl) ⟨619841, by rfl⟩ : syracuseStep 826455 = 1239683) B1239683
theorem B826475 : Blo 826349 826475 := bstep (se 1 (by rfl) ⟨619856, by rfl⟩ : syracuseStep 826475 = 1239713) B1239713
theorem B826487 : Blo 826349 826487 := bstep (se 1 (by rfl) ⟨619865, by rfl⟩ : syracuseStep 826487 = 1239731) B1239731
theorem B826507 : Blo 826349 826507 := bstep (se 1 (by rfl) ⟨619880, by rfl⟩ : syracuseStep 826507 = 1239761) B1239761
theorem B826519 : Blo 826349 826519 := bstep (se 1 (by rfl) ⟨619889, by rfl⟩ : syracuseStep 826519 = 1239779) B1239779
theorem B826539 : Blo 826349 826539 := bstep (se 1 (by rfl) ⟨619904, by rfl⟩ : syracuseStep 826539 = 1239809) B1239809
theorem B826551 : Blo 826349 826551 := bstep (se 1 (by rfl) ⟨619913, by rfl⟩ : syracuseStep 826551 = 1239827) B1239827
theorem B826571 : Blo 826349 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B826583 : Blo 826349 826583 := bstep (se 1 (by rfl) ⟨619937, by rfl⟩ : syracuseStep 826583 = 1239875) B1239875
theorem B826603 : Blo 826349 826603 := bstep (se 1 (by rfl) ⟨619952, by rfl⟩ : syracuseStep 826603 = 1239905) B1239905
theorem B826615 : Blo 826349 826615 := bstep (se 1 (by rfl) ⟨619961, by rfl⟩ : syracuseStep 826615 = 1239923) B1239923
theorem B826635 : Blo 826349 826635 := bstep (se 1 (by rfl) ⟨619976, by rfl⟩ : syracuseStep 826635 = 1239953) B1239953
theorem B826647 : Blo 826349 826647 := bstep (se 1 (by rfl) ⟨619985, by rfl⟩ : syracuseStep 826647 = 1239971) B1239971
theorem B826667 : Blo 826349 826667 := bstep (se 1 (by rfl) ⟨620000, by rfl⟩ : syracuseStep 826667 = 1240001) B1240001
theorem B826679 : Blo 826349 826679 := bstep (se 1 (by rfl) ⟨620009, by rfl⟩ : syracuseStep 826679 = 1240019) B1240019
theorem B4201793 : Blo 826349 4201793 := bstep (se 2 (by rfl) ⟨1575672, by rfl⟩ : syracuseStep 4201793 = 3151345) B3151345
theorem B826699 : Blo 826349 826699 := bstep (se 1 (by rfl) ⟨620024, by rfl⟩ : syracuseStep 826699 = 1240049) B1240049
theorem B826711 : Blo 826349 826711 := bstep (se 1 (by rfl) ⟨620033, by rfl⟩ : syracuseStep 826711 = 1240067) B1240067
theorem B826731 : Blo 826349 826731 := bstep (se 1 (by rfl) ⟨620048, by rfl⟩ : syracuseStep 826731 = 1240097) B1240097
theorem B826743 : Blo 826349 826743 := bstep (se 1 (by rfl) ⟨620057, by rfl⟩ : syracuseStep 826743 = 1240115) B1240115
theorem B826763 : Blo 826349 826763 := bstep (se 1 (by rfl) ⟨620072, by rfl⟩ : syracuseStep 826763 = 1240145) B1240145
theorem B826775 : Blo 826349 826775 := bstep (se 1 (by rfl) ⟨620081, by rfl⟩ : syracuseStep 826775 = 1240163) B1240163
theorem B6725015 : Blo 826349 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B826795 : Blo 826349 826795 := bstep (se 1 (by rfl) ⟨620096, by rfl⟩ : syracuseStep 826795 = 1240193) B1240193
theorem B826807 : Blo 826349 826807 := bstep (se 1 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 826807 = 1240211) B1240211
theorem B826827 : Blo 826349 826827 := bstep (se 1 (by rfl) ⟨620120, by rfl⟩ : syracuseStep 826827 = 1240241) B1240241
theorem B826839 : Blo 826349 826839 := bstep (se 1 (by rfl) ⟨620129, by rfl⟩ : syracuseStep 826839 = 1240259) B1240259
theorem B826859 : Blo 826349 826859 := bstep (se 1 (by rfl) ⟨620144, by rfl⟩ : syracuseStep 826859 = 1240289) B1240289
theorem B826871 : Blo 826349 826871 := bstep (se 1 (by rfl) ⟨620153, by rfl⟩ : syracuseStep 826871 = 1240307) B1240307
theorem B826891 : Blo 826349 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B4726289 : Blo 826349 4726289 := bstep (se 2 (by rfl) ⟨1772358, by rfl⟩ : syracuseStep 4726289 = 3544717) B3544717
theorem B826903 : Blo 826349 826903 := bstep (se 1 (by rfl) ⟨620177, by rfl⟩ : syracuseStep 826903 = 1240355) B1240355
theorem B826923 : Blo 826349 826923 := bstep (se 1 (by rfl) ⟨620192, by rfl⟩ : syracuseStep 826923 = 1240385) B1240385
theorem B2989619 : Blo 826349 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B826935 : Blo 826349 826935 := bstep (se 1 (by rfl) ⟨620201, by rfl⟩ : syracuseStep 826935 = 1240403) B1240403
theorem B826955 : Blo 826349 826955 := bstep (se 1 (by rfl) ⟨620216, by rfl⟩ : syracuseStep 826955 = 1240433) B1240433
theorem B826967 : Blo 826349 826967 := bstep (se 1 (by rfl) ⟨620225, by rfl⟩ : syracuseStep 826967 = 1240451) B1240451
theorem B826987 : Blo 826349 826987 := bstep (se 1 (by rfl) ⟨620240, by rfl⟩ : syracuseStep 826987 = 1240481) B1240481
theorem B826999 : Blo 826349 826999 := bstep (se 1 (by rfl) ⟨620249, by rfl⟩ : syracuseStep 826999 = 1240499) B1240499
theorem B827019 : Blo 826349 827019 := bstep (se 1 (by rfl) ⟨620264, by rfl⟩ : syracuseStep 827019 = 1240529) B1240529
theorem B827031 : Blo 826349 827031 := bstep (se 1 (by rfl) ⟨620273, by rfl⟩ : syracuseStep 827031 = 1240547) B1240547
theorem B827051 : Blo 826349 827051 := bstep (se 1 (by rfl) ⟨620288, by rfl⟩ : syracuseStep 827051 = 1240577) B1240577
theorem B827063 : Blo 826349 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B827083 : Blo 826349 827083 := bstep (se 1 (by rfl) ⟨620312, by rfl⟩ : syracuseStep 827083 = 1240625) B1240625
theorem B827095 : Blo 826349 827095 := bstep (se 1 (by rfl) ⟨620321, by rfl⟩ : syracuseStep 827095 = 1240643) B1240643
theorem B827115 : Blo 826349 827115 := bstep (se 1 (by rfl) ⟨620336, by rfl⟩ : syracuseStep 827115 = 1240673) B1240673
theorem B827127 : Blo 826349 827127 := bstep (se 1 (by rfl) ⟨620345, by rfl⟩ : syracuseStep 827127 = 1240691) B1240691
theorem B827147 : Blo 826349 827147 := bstep (se 1 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 827147 = 1240721) B1240721
theorem B827159 : Blo 826349 827159 := bstep (se 1 (by rfl) ⟨620369, by rfl⟩ : syracuseStep 827159 = 1240739) B1240739
theorem B827179 : Blo 826349 827179 := bstep (se 1 (by rfl) ⟨620384, by rfl⟩ : syracuseStep 827179 = 1240769) B1240769
theorem B827191 : Blo 826349 827191 := bstep (se 1 (by rfl) ⟨620393, by rfl⟩ : syracuseStep 827191 = 1240787) B1240787
theorem B827211 : Blo 826349 827211 := bstep (se 1 (by rfl) ⟨620408, by rfl⟩ : syracuseStep 827211 = 1240817) B1240817
theorem B827223 : Blo 826349 827223 := bstep (se 1 (by rfl) ⟨620417, by rfl⟩ : syracuseStep 827223 = 1240835) B1240835
theorem B827243 : Blo 826349 827243 := bstep (se 1 (by rfl) ⟨620432, by rfl⟩ : syracuseStep 827243 = 1240865) B1240865
theorem B827255 : Blo 826349 827255 := bstep (se 1 (by rfl) ⟨620441, by rfl⟩ : syracuseStep 827255 = 1240883) B1240883
theorem B827275 : Blo 826349 827275 := bstep (se 1 (by rfl) ⟨620456, by rfl⟩ : syracuseStep 827275 = 1240913) B1240913
theorem B827287 : Blo 826349 827287 := bstep (se 1 (by rfl) ⟨620465, by rfl⟩ : syracuseStep 827287 = 1240931) B1240931
theorem B827307 : Blo 826349 827307 := bstep (se 1 (by rfl) ⟨620480, by rfl⟩ : syracuseStep 827307 = 1240961) B1240961
theorem B827319 : Blo 826349 827319 := bstep (se 1 (by rfl) ⟨620489, by rfl⟩ : syracuseStep 827319 = 1240979) B1240979
theorem B827339 : Blo 826349 827339 := bstep (se 1 (by rfl) ⟨620504, by rfl⟩ : syracuseStep 827339 = 1241009) B1241009
theorem B2793419 : Blo 826349 2793419 := bstep (se 1 (by rfl) ⟨2095064, by rfl⟩ : syracuseStep 2793419 = 4190129) B4190129
theorem B827351 : Blo 826349 827351 := bstep (se 1 (by rfl) ⟨620513, by rfl⟩ : syracuseStep 827351 = 1241027) B1241027
theorem B4726745 : Blo 826349 4726745 := bstep (se 2 (by rfl) ⟨1772529, by rfl⟩ : syracuseStep 4726745 = 3545059) B3545059
theorem B827371 : Blo 826349 827371 := bstep (se 1 (by rfl) ⟨620528, by rfl⟩ : syracuseStep 827371 = 1241057) B1241057
theorem B827383 : Blo 826349 827383 := bstep (se 1 (by rfl) ⟨620537, by rfl⟩ : syracuseStep 827383 = 1241075) B1241075
theorem B827403 : Blo 826349 827403 := bstep (se 1 (by rfl) ⟨620552, by rfl⟩ : syracuseStep 827403 = 1241105) B1241105
theorem B827415 : Blo 826349 827415 := bstep (se 1 (by rfl) ⟨620561, by rfl⟩ : syracuseStep 827415 = 1241123) B1241123
theorem B827435 : Blo 826349 827435 := bstep (se 1 (by rfl) ⟨620576, by rfl⟩ : syracuseStep 827435 = 1241153) B1241153
theorem B827447 : Blo 826349 827447 := bstep (se 1 (by rfl) ⟨620585, by rfl⟩ : syracuseStep 827447 = 1241171) B1241171
theorem B827467 : Blo 826349 827467 := bstep (se 1 (by rfl) ⟨620600, by rfl⟩ : syracuseStep 827467 = 1241201) B1241201
theorem B827479 : Blo 826349 827479 := bstep (se 1 (by rfl) ⟨620609, by rfl⟩ : syracuseStep 827479 = 1241219) B1241219
theorem B827499 : Blo 826349 827499 := bstep (se 1 (by rfl) ⟨620624, by rfl⟩ : syracuseStep 827499 = 1241249) B1241249
theorem B827511 : Blo 826349 827511 := bstep (se 1 (by rfl) ⟨620633, by rfl⟩ : syracuseStep 827511 = 1241267) B1241267
theorem B827531 : Blo 826349 827531 := bstep (se 1 (by rfl) ⟨620648, by rfl⟩ : syracuseStep 827531 = 1241297) B1241297
theorem B827543 : Blo 826349 827543 := bstep (se 1 (by rfl) ⟨620657, by rfl⟩ : syracuseStep 827543 = 1241315) B1241315
theorem B827563 : Blo 826349 827563 := bstep (se 1 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 827563 = 1241345) B1241345
theorem B827575 : Blo 826349 827575 := bstep (se 1 (by rfl) ⟨620681, by rfl⟩ : syracuseStep 827575 = 1241363) B1241363
theorem B827595 : Blo 826349 827595 := bstep (se 1 (by rfl) ⟨620696, by rfl⟩ : syracuseStep 827595 = 1241393) B1241393
theorem B827607 : Blo 826349 827607 := bstep (se 1 (by rfl) ⟨620705, by rfl⟩ : syracuseStep 827607 = 1241411) B1241411
theorem B2793689 : Blo 826349 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B827627 : Blo 826349 827627 := bstep (se 1 (by rfl) ⟨620720, by rfl⟩ : syracuseStep 827627 = 1241441) B1241441
theorem B827639 : Blo 826349 827639 := bstep (se 1 (by rfl) ⟨620729, by rfl⟩ : syracuseStep 827639 = 1241459) B1241459
theorem B827659 : Blo 826349 827659 := bstep (se 1 (by rfl) ⟨620744, by rfl⟩ : syracuseStep 827659 = 1241489) B1241489
theorem B827671 : Blo 826349 827671 := bstep (se 1 (by rfl) ⟨620753, by rfl⟩ : syracuseStep 827671 = 1241507) B1241507
theorem B827691 : Blo 826349 827691 := bstep (se 1 (by rfl) ⟨620768, by rfl⟩ : syracuseStep 827691 = 1241537) B1241537
theorem B827703 : Blo 826349 827703 := bstep (se 1 (by rfl) ⟨620777, by rfl⟩ : syracuseStep 827703 = 1241555) B1241555
theorem B827723 : Blo 826349 827723 := bstep (se 1 (by rfl) ⟨620792, by rfl⟩ : syracuseStep 827723 = 1241585) B1241585
theorem B827735 : Blo 826349 827735 := bstep (se 1 (by rfl) ⟨620801, by rfl⟩ : syracuseStep 827735 = 1241603) B1241603
theorem B827755 : Blo 826349 827755 := bstep (se 1 (by rfl) ⟨620816, by rfl⟩ : syracuseStep 827755 = 1241633) B1241633
theorem B827767 : Blo 826349 827767 := bstep (se 1 (by rfl) ⟨620825, by rfl⟩ : syracuseStep 827767 = 1241651) B1241651
theorem B827787 : Blo 826349 827787 := bstep (se 1 (by rfl) ⟨620840, by rfl⟩ : syracuseStep 827787 = 1241681) B1241681
theorem B827799 : Blo 826349 827799 := bstep (se 1 (by rfl) ⟨620849, by rfl⟩ : syracuseStep 827799 = 1241699) B1241699
theorem B827819 : Blo 826349 827819 := bstep (se 1 (by rfl) ⟨620864, by rfl⟩ : syracuseStep 827819 = 1241729) B1241729
theorem B827831 : Blo 826349 827831 := bstep (se 1 (by rfl) ⟨620873, by rfl⟩ : syracuseStep 827831 = 1241747) B1241747
theorem B827851 : Blo 826349 827851 := bstep (se 1 (by rfl) ⟨620888, by rfl⟩ : syracuseStep 827851 = 1241777) B1241777
theorem B827863 : Blo 826349 827863 := bstep (se 1 (by rfl) ⟨620897, by rfl⟩ : syracuseStep 827863 = 1241795) B1241795
theorem B827883 : Blo 826349 827883 := bstep (se 1 (by rfl) ⟨620912, by rfl⟩ : syracuseStep 827883 = 1241825) B1241825
theorem B827895 : Blo 826349 827895 := bstep (se 1 (by rfl) ⟨620921, by rfl⟩ : syracuseStep 827895 = 1241843) B1241843
theorem B827915 : Blo 826349 827915 := bstep (se 1 (by rfl) ⟨620936, by rfl⟩ : syracuseStep 827915 = 1241873) B1241873
theorem B827927 : Blo 826349 827927 := bstep (se 1 (by rfl) ⟨620945, by rfl⟩ : syracuseStep 827927 = 1241891) B1241891
theorem B827947 : Blo 826349 827947 := bstep (se 1 (by rfl) ⟨620960, by rfl⟩ : syracuseStep 827947 = 1241921) B1241921
theorem B827959 : Blo 826349 827959 := bstep (se 1 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 827959 = 1241939) B1241939
theorem B827979 : Blo 826349 827979 := bstep (se 1 (by rfl) ⟨620984, by rfl⟩ : syracuseStep 827979 = 1241969) B1241969
theorem B827991 : Blo 826349 827991 := bstep (se 1 (by rfl) ⟨620993, by rfl⟩ : syracuseStep 827991 = 1241987) B1241987
theorem B828011 : Blo 826349 828011 := bstep (se 1 (by rfl) ⟨621008, by rfl⟩ : syracuseStep 828011 = 1242017) B1242017
theorem B828023 : Blo 826349 828023 := bstep (se 1 (by rfl) ⟨621017, by rfl⟩ : syracuseStep 828023 = 1242035) B1242035
theorem B828043 : Blo 826349 828043 := bstep (se 1 (by rfl) ⟨621032, by rfl⟩ : syracuseStep 828043 = 1242065) B1242065
theorem B828055 : Blo 826349 828055 := bstep (se 1 (by rfl) ⟨621041, by rfl⟩ : syracuseStep 828055 = 1242083) B1242083
theorem B828075 : Blo 826349 828075 := bstep (se 1 (by rfl) ⟨621056, by rfl⟩ : syracuseStep 828075 = 1242113) B1242113
theorem B828087 : Blo 826349 828087 := bstep (se 1 (by rfl) ⟨621065, by rfl⟩ : syracuseStep 828087 = 1242131) B1242131
theorem B828107 : Blo 826349 828107 := bstep (se 1 (by rfl) ⟨621080, by rfl⟩ : syracuseStep 828107 = 1242161) B1242161
theorem B828119 : Blo 826349 828119 := bstep (se 1 (by rfl) ⟨621089, by rfl⟩ : syracuseStep 828119 = 1242179) B1242179
theorem B828139 : Blo 826349 828139 := bstep (se 1 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 828139 = 1242209) B1242209
theorem B828151 : Blo 826349 828151 := bstep (se 1 (by rfl) ⟨621113, by rfl⟩ : syracuseStep 828151 = 1242227) B1242227
theorem B828171 : Blo 826349 828171 := bstep (se 1 (by rfl) ⟨621128, by rfl⟩ : syracuseStep 828171 = 1242257) B1242257
theorem B828183 : Blo 826349 828183 := bstep (se 1 (by rfl) ⟨621137, by rfl⟩ : syracuseStep 828183 = 1242275) B1242275
theorem B828203 : Blo 826349 828203 := bstep (se 1 (by rfl) ⟨621152, by rfl⟩ : syracuseStep 828203 = 1242305) B1242305
theorem B828215 : Blo 826349 828215 := bstep (se 1 (by rfl) ⟨621161, by rfl⟩ : syracuseStep 828215 = 1242323) B1242323
theorem B828235 : Blo 826349 828235 := bstep (se 1 (by rfl) ⟨621176, by rfl⟩ : syracuseStep 828235 = 1242353) B1242353
theorem B828247 : Blo 826349 828247 := bstep (se 1 (by rfl) ⟨621185, by rfl⟩ : syracuseStep 828247 = 1242371) B1242371
theorem B2040665 : Blo 826349 2040665 := bstep (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) B1530499
theorem B828267 : Blo 826349 828267 := bstep (se 1 (by rfl) ⟨621200, by rfl⟩ : syracuseStep 828267 = 1242401) B1242401
theorem B828279 : Blo 826349 828279 := bstep (se 1 (by rfl) ⟨621209, by rfl⟩ : syracuseStep 828279 = 1242419) B1242419
theorem B828299 : Blo 826349 828299 := bstep (se 1 (by rfl) ⟨621224, by rfl⟩ : syracuseStep 828299 = 1242449) B1242449
theorem B2794391 : Blo 826349 2794391 := bstep (se 1 (by rfl) ⟨2095793, by rfl⟩ : syracuseStep 2794391 = 4191587) B4191587
theorem B828311 : Blo 826349 828311 := bstep (se 1 (by rfl) ⟨621233, by rfl⟩ : syracuseStep 828311 = 1242467) B1242467
theorem B1680281 : Blo 826349 1680281 := bstep (se 2 (by rfl) ⟨630105, by rfl⟩ : syracuseStep 1680281 = 1260211) B1260211
theorem B828331 : Blo 826349 828331 := bstep (se 1 (by rfl) ⟨621248, by rfl⟩ : syracuseStep 828331 = 1242497) B1242497
theorem B828343 : Blo 826349 828343 := bstep (se 1 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 828343 = 1242515) B1242515
theorem B828363 : Blo 826349 828363 := bstep (se 1 (by rfl) ⟨621272, by rfl⟩ : syracuseStep 828363 = 1242545) B1242545
theorem B828375 : Blo 826349 828375 := bstep (se 1 (by rfl) ⟨621281, by rfl⟩ : syracuseStep 828375 = 1242563) B1242563
theorem B828395 : Blo 826349 828395 := bstep (se 1 (by rfl) ⟨621296, by rfl⟩ : syracuseStep 828395 = 1242593) B1242593
theorem B828407 : Blo 826349 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B828427 : Blo 826349 828427 := bstep (se 1 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 828427 = 1242641) B1242641
theorem B828439 : Blo 826349 828439 := bstep (se 1 (by rfl) ⟨621329, by rfl⟩ : syracuseStep 828439 = 1242659) B1242659
theorem B828459 : Blo 826349 828459 := bstep (se 1 (by rfl) ⟨621344, by rfl⟩ : syracuseStep 828459 = 1242689) B1242689
theorem B828471 : Blo 826349 828471 := bstep (se 1 (by rfl) ⟨621353, by rfl⟩ : syracuseStep 828471 = 1242707) B1242707
theorem B828491 : Blo 826349 828491 := bstep (se 1 (by rfl) ⟨621368, by rfl⟩ : syracuseStep 828491 = 1242737) B1242737
theorem B828503 : Blo 826349 828503 := bstep (se 1 (by rfl) ⟨621377, by rfl⟩ : syracuseStep 828503 = 1242755) B1242755
theorem B828523 : Blo 826349 828523 := bstep (se 1 (by rfl) ⟨621392, by rfl⟩ : syracuseStep 828523 = 1242785) B1242785
theorem B828535 : Blo 826349 828535 := bstep (se 1 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 828535 = 1242803) B1242803
theorem B3974275 : Blo 826349 3974275 := bstep (se 1 (by rfl) ⟨2980706, by rfl⟩ : syracuseStep 3974275 = 5961413) B5961413
theorem B828555 : Blo 826349 828555 := bstep (se 1 (by rfl) ⟨621416, by rfl⟩ : syracuseStep 828555 = 1242833) B1242833
theorem B828567 : Blo 826349 828567 := bstep (se 1 (by rfl) ⟨621425, by rfl⟩ : syracuseStep 828567 = 1242851) B1242851
theorem B828587 : Blo 826349 828587 := bstep (se 1 (by rfl) ⟨621440, by rfl⟩ : syracuseStep 828587 = 1242881) B1242881
theorem B3351725 : Blo 826349 3351725 := bstep (se 3 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 3351725 = 1256897) B1256897
theorem B828599 : Blo 826349 828599 := bstep (se 1 (by rfl) ⟨621449, by rfl⟩ : syracuseStep 828599 = 1242899) B1242899
theorem B828619 : Blo 826349 828619 := bstep (se 1 (by rfl) ⟨621464, by rfl⟩ : syracuseStep 828619 = 1242929) B1242929
theorem B828631 : Blo 826349 828631 := bstep (se 1 (by rfl) ⟨621473, by rfl⟩ : syracuseStep 828631 = 1242947) B1242947
theorem B828651 : Blo 826349 828651 := bstep (se 1 (by rfl) ⟨621488, by rfl⟩ : syracuseStep 828651 = 1242977) B1242977
theorem B828663 : Blo 826349 828663 := bstep (se 1 (by rfl) ⟨621497, by rfl⟩ : syracuseStep 828663 = 1242995) B1242995
theorem B828683 : Blo 826349 828683 := bstep (se 1 (by rfl) ⟨621512, by rfl⟩ : syracuseStep 828683 = 1243025) B1243025
theorem B828695 : Blo 826349 828695 := bstep (se 1 (by rfl) ⟨621521, by rfl⟩ : syracuseStep 828695 = 1243043) B1243043
theorem B828715 : Blo 826349 828715 := bstep (se 1 (by rfl) ⟨621536, by rfl⟩ : syracuseStep 828715 = 1243073) B1243073
theorem B828727 : Blo 826349 828727 := bstep (se 1 (by rfl) ⟨621545, by rfl⟩ : syracuseStep 828727 = 1243091) B1243091
theorem B828747 : Blo 826349 828747 := bstep (se 1 (by rfl) ⟨621560, by rfl⟩ : syracuseStep 828747 = 1243121) B1243121
theorem B828759 : Blo 826349 828759 := bstep (se 1 (by rfl) ⟨621569, by rfl⟩ : syracuseStep 828759 = 1243139) B1243139
theorem B11937125 : Blo 826349 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B828779 : Blo 826349 828779 := bstep (se 1 (by rfl) ⟨621584, by rfl⟩ : syracuseStep 828779 = 1243169) B1243169
theorem B828791 : Blo 826349 828791 := bstep (se 1 (by rfl) ⟨621593, by rfl⟩ : syracuseStep 828791 = 1243187) B1243187
theorem B828811 : Blo 826349 828811 := bstep (se 1 (by rfl) ⟨621608, by rfl⟩ : syracuseStep 828811 = 1243217) B1243217
theorem B828823 : Blo 826349 828823 := bstep (se 1 (by rfl) ⟨621617, by rfl⟩ : syracuseStep 828823 = 1243235) B1243235
theorem B828843 : Blo 826349 828843 := bstep (se 1 (by rfl) ⟨621632, by rfl⟩ : syracuseStep 828843 = 1243265) B1243265
theorem B2794931 : Blo 826349 2794931 := bstep (se 1 (by rfl) ⟨2096198, by rfl⟩ : syracuseStep 2794931 = 4192397) B4192397
theorem B828855 : Blo 826349 828855 := bstep (se 1 (by rfl) ⟨621641, by rfl⟩ : syracuseStep 828855 = 1243283) B1243283
theorem B828875 : Blo 826349 828875 := bstep (se 1 (by rfl) ⟨621656, by rfl⟩ : syracuseStep 828875 = 1243313) B1243313
theorem B828887 : Blo 826349 828887 := bstep (se 1 (by rfl) ⟨621665, by rfl⟩ : syracuseStep 828887 = 1243331) B1243331
theorem B828907 : Blo 826349 828907 := bstep (se 1 (by rfl) ⟨621680, by rfl⟩ : syracuseStep 828907 = 1243361) B1243361
theorem B828919 : Blo 826349 828919 := bstep (se 1 (by rfl) ⟨621689, by rfl⟩ : syracuseStep 828919 = 1243379) B1243379
theorem B828939 : Blo 826349 828939 := bstep (se 1 (by rfl) ⟨621704, by rfl⟩ : syracuseStep 828939 = 1243409) B1243409
theorem B828951 : Blo 826349 828951 := bstep (se 1 (by rfl) ⟨621713, by rfl⟩ : syracuseStep 828951 = 1243427) B1243427
theorem B828971 : Blo 826349 828971 := bstep (se 1 (by rfl) ⟨621728, by rfl⟩ : syracuseStep 828971 = 1243457) B1243457
theorem B828983 : Blo 826349 828983 := bstep (se 1 (by rfl) ⟨621737, by rfl⟩ : syracuseStep 828983 = 1243475) B1243475
theorem B829003 : Blo 826349 829003 := bstep (se 1 (by rfl) ⟨621752, by rfl⟩ : syracuseStep 829003 = 1243505) B1243505
theorem B829015 : Blo 826349 829015 := bstep (se 1 (by rfl) ⟨621761, by rfl⟩ : syracuseStep 829015 = 1243523) B1243523
theorem B829035 : Blo 826349 829035 := bstep (se 1 (by rfl) ⟨621776, by rfl⟩ : syracuseStep 829035 = 1243553) B1243553
theorem B829047 : Blo 826349 829047 := bstep (se 1 (by rfl) ⟨621785, by rfl⟩ : syracuseStep 829047 = 1243571) B1243571
theorem B829067 : Blo 826349 829067 := bstep (se 1 (by rfl) ⟨621800, by rfl⟩ : syracuseStep 829067 = 1243601) B1243601
theorem B829079 : Blo 826349 829079 := bstep (se 1 (by rfl) ⟨621809, by rfl⟩ : syracuseStep 829079 = 1243619) B1243619
theorem B829099 : Blo 826349 829099 := bstep (se 1 (by rfl) ⟨621824, by rfl⟩ : syracuseStep 829099 = 1243649) B1243649
theorem B829111 : Blo 826349 829111 := bstep (se 1 (by rfl) ⟨621833, by rfl⟩ : syracuseStep 829111 = 1243667) B1243667
theorem B2795201 : Blo 826349 2795201 := bstep (se 2 (by rfl) ⟨1048200, by rfl⟩ : syracuseStep 2795201 = 2096401) B2096401
theorem B2991809 : Blo 826349 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B829131 : Blo 826349 829131 := bstep (se 1 (by rfl) ⟨621848, by rfl⟩ : syracuseStep 829131 = 1243697) B1243697
theorem B829143 : Blo 826349 829143 := bstep (se 1 (by rfl) ⟨621857, by rfl⟩ : syracuseStep 829143 = 1243715) B1243715
theorem B1418969 : Blo 826349 1418969 := bstep (se 2 (by rfl) ⟨532113, by rfl⟩ : syracuseStep 1418969 = 1064227) B1064227
theorem B829163 : Blo 826349 829163 := bstep (se 1 (by rfl) ⟨621872, by rfl⟩ : syracuseStep 829163 = 1243745) B1243745
theorem B829175 : Blo 826349 829175 := bstep (se 1 (by rfl) ⟨621881, by rfl⟩ : syracuseStep 829175 = 1243763) B1243763
theorem B829195 : Blo 826349 829195 := bstep (se 1 (by rfl) ⟨621896, by rfl⟩ : syracuseStep 829195 = 1243793) B1243793
theorem B829207 : Blo 826349 829207 := bstep (se 1 (by rfl) ⟨621905, by rfl⟩ : syracuseStep 829207 = 1243811) B1243811
theorem B6301475 : Blo 826349 6301475 := bstep (se 1 (by rfl) ⟨4726106, by rfl⟩ : syracuseStep 6301475 = 9452213) B9452213
theorem B829227 : Blo 826349 829227 := bstep (se 1 (by rfl) ⟨621920, by rfl⟩ : syracuseStep 829227 = 1243841) B1243841
theorem B829239 : Blo 826349 829239 := bstep (se 1 (by rfl) ⟨621929, by rfl⟩ : syracuseStep 829239 = 1243859) B1243859
theorem B829259 : Blo 826349 829259 := bstep (se 1 (by rfl) ⟨621944, by rfl⟩ : syracuseStep 829259 = 1243889) B1243889
theorem B829271 : Blo 826349 829271 := bstep (se 1 (by rfl) ⟨621953, by rfl⟩ : syracuseStep 829271 = 1243907) B1243907
theorem B829291 : Blo 826349 829291 := bstep (se 1 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 829291 = 1243937) B1243937
theorem B829303 : Blo 826349 829303 := bstep (se 1 (by rfl) ⟨621977, by rfl⟩ : syracuseStep 829303 = 1243955) B1243955
theorem B829323 : Blo 826349 829323 := bstep (se 1 (by rfl) ⟨621992, by rfl⟩ : syracuseStep 829323 = 1243985) B1243985
theorem B829335 : Blo 826349 829335 := bstep (se 1 (by rfl) ⟨622001, by rfl⟩ : syracuseStep 829335 = 1244003) B1244003
theorem B829355 : Blo 826349 829355 := bstep (se 1 (by rfl) ⟨622016, by rfl⟩ : syracuseStep 829355 = 1244033) B1244033
theorem B829367 : Blo 826349 829367 := bstep (se 1 (by rfl) ⟨622025, by rfl⟩ : syracuseStep 829367 = 1244051) B1244051
theorem B829387 : Blo 826349 829387 := bstep (se 1 (by rfl) ⟨622040, by rfl⟩ : syracuseStep 829387 = 1244081) B1244081
theorem B829399 : Blo 826349 829399 := bstep (se 1 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 829399 = 1244099) B1244099
theorem B829419 : Blo 826349 829419 := bstep (se 1 (by rfl) ⟨622064, by rfl⟩ : syracuseStep 829419 = 1244129) B1244129
theorem B829431 : Blo 826349 829431 := bstep (se 1 (by rfl) ⟨622073, by rfl⟩ : syracuseStep 829431 = 1244147) B1244147
theorem B829451 : Blo 826349 829451 := bstep (se 1 (by rfl) ⟨622088, by rfl⟩ : syracuseStep 829451 = 1244177) B1244177
theorem B829463 : Blo 826349 829463 := bstep (se 1 (by rfl) ⟨622097, by rfl⟩ : syracuseStep 829463 = 1244195) B1244195
theorem B829483 : Blo 826349 829483 := bstep (se 1 (by rfl) ⟨622112, by rfl⟩ : syracuseStep 829483 = 1244225) B1244225
theorem B829495 : Blo 826349 829495 := bstep (se 1 (by rfl) ⟨622121, by rfl⟩ : syracuseStep 829495 = 1244243) B1244243
theorem B3188801 : Blo 826349 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B829515 : Blo 826349 829515 := bstep (se 1 (by rfl) ⟨622136, by rfl⟩ : syracuseStep 829515 = 1244273) B1244273
theorem B829527 : Blo 826349 829527 := bstep (se 1 (by rfl) ⟨622145, by rfl⟩ : syracuseStep 829527 = 1244291) B1244291
theorem B2238557 : Blo 826349 2238557 := bstep (se 3 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 2238557 = 839459) B839459
theorem B829547 : Blo 826349 829547 := bstep (se 1 (by rfl) ⟨622160, by rfl⟩ : syracuseStep 829547 = 1244321) B1244321
theorem B829559 : Blo 826349 829559 := bstep (se 1 (by rfl) ⟨622169, by rfl⟩ : syracuseStep 829559 = 1244339) B1244339
theorem B829579 : Blo 826349 829579 := bstep (se 1 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 829579 = 1244369) B1244369
theorem B829591 : Blo 826349 829591 := bstep (se 1 (by rfl) ⟨622193, by rfl⟩ : syracuseStep 829591 = 1244387) B1244387
theorem B829611 : Blo 826349 829611 := bstep (se 1 (by rfl) ⟨622208, by rfl⟩ : syracuseStep 829611 = 1244417) B1244417
theorem B829623 : Blo 826349 829623 := bstep (se 1 (by rfl) ⟨622217, by rfl⟩ : syracuseStep 829623 = 1244435) B1244435
theorem B829643 : Blo 826349 829643 := bstep (se 1 (by rfl) ⟨622232, by rfl⟩ : syracuseStep 829643 = 1244465) B1244465
theorem B829655 : Blo 826349 829655 := bstep (se 1 (by rfl) ⟨622241, by rfl⟩ : syracuseStep 829655 = 1244483) B1244483
theorem B2795741 : Blo 826349 2795741 := bstep (se 3 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 2795741 = 1048403) B1048403
theorem B829675 : Blo 826349 829675 := bstep (se 1 (by rfl) ⟨622256, by rfl⟩ : syracuseStep 829675 = 1244513) B1244513
theorem B829687 : Blo 826349 829687 := bstep (se 1 (by rfl) ⟨622265, by rfl⟩ : syracuseStep 829687 = 1244531) B1244531
theorem B829707 : Blo 826349 829707 := bstep (se 1 (by rfl) ⟨622280, by rfl⟩ : syracuseStep 829707 = 1244561) B1244561
theorem B829719 : Blo 826349 829719 := bstep (se 1 (by rfl) ⟨622289, by rfl⟩ : syracuseStep 829719 = 1244579) B1244579
theorem B829739 : Blo 826349 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B829751 : Blo 826349 829751 := bstep (se 1 (by rfl) ⟨622313, by rfl⟩ : syracuseStep 829751 = 1244627) B1244627
theorem B829771 : Blo 826349 829771 := bstep (se 1 (by rfl) ⟨622328, by rfl⟩ : syracuseStep 829771 = 1244657) B1244657
theorem B829783 : Blo 826349 829783 := bstep (se 1 (by rfl) ⟨622337, by rfl⟩ : syracuseStep 829783 = 1244675) B1244675
theorem B829803 : Blo 826349 829803 := bstep (se 1 (by rfl) ⟨622352, by rfl⟩ : syracuseStep 829803 = 1244705) B1244705
theorem B829815 : Blo 826349 829815 := bstep (se 1 (by rfl) ⟨622361, by rfl⟩ : syracuseStep 829815 = 1244723) B1244723
theorem B829835 : Blo 826349 829835 := bstep (se 1 (by rfl) ⟨622376, by rfl⟩ : syracuseStep 829835 = 1244753) B1244753
theorem B829847 : Blo 826349 829847 := bstep (se 1 (by rfl) ⟨622385, by rfl⟩ : syracuseStep 829847 = 1244771) B1244771
theorem B829867 : Blo 826349 829867 := bstep (se 1 (by rfl) ⟨622400, by rfl⟩ : syracuseStep 829867 = 1244801) B1244801
theorem B829879 : Blo 826349 829879 := bstep (se 1 (by rfl) ⟨622409, by rfl⟩ : syracuseStep 829879 = 1244819) B1244819
theorem B829899 : Blo 826349 829899 := bstep (se 1 (by rfl) ⟨622424, by rfl⟩ : syracuseStep 829899 = 1244849) B1244849
theorem B829911 : Blo 826349 829911 := bstep (se 1 (by rfl) ⟨622433, by rfl⟩ : syracuseStep 829911 = 1244867) B1244867
theorem B829931 : Blo 826349 829931 := bstep (se 1 (by rfl) ⟨622448, by rfl⟩ : syracuseStep 829931 = 1244897) B1244897
theorem B829943 : Blo 826349 829943 := bstep (se 1 (by rfl) ⟨622457, by rfl⟩ : syracuseStep 829943 = 1244915) B1244915
theorem B829963 : Blo 826349 829963 := bstep (se 1 (by rfl) ⟨622472, by rfl⟩ : syracuseStep 829963 = 1244945) B1244945
theorem B829975 : Blo 826349 829975 := bstep (se 1 (by rfl) ⟨622481, by rfl⟩ : syracuseStep 829975 = 1244963) B1244963
theorem B829995 : Blo 826349 829995 := bstep (se 1 (by rfl) ⟨622496, by rfl⟩ : syracuseStep 829995 = 1244993) B1244993
theorem B830007 : Blo 826349 830007 := bstep (se 1 (by rfl) ⟨622505, by rfl⟩ : syracuseStep 830007 = 1245011) B1245011
theorem B1681985 : Blo 826349 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B830027 : Blo 826349 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B830039 : Blo 826349 830039 := bstep (se 1 (by rfl) ⟨622529, by rfl⟩ : syracuseStep 830039 = 1245059) B1245059
theorem B830059 : Blo 826349 830059 := bstep (se 1 (by rfl) ⟨622544, by rfl⟩ : syracuseStep 830059 = 1245089) B1245089
theorem B830071 : Blo 826349 830071 := bstep (se 1 (by rfl) ⟨622553, by rfl⟩ : syracuseStep 830071 = 1245107) B1245107
theorem B830091 : Blo 826349 830091 := bstep (se 1 (by rfl) ⟨622568, by rfl⟩ : syracuseStep 830091 = 1245137) B1245137
theorem B7547543 : Blo 826349 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B830103 : Blo 826349 830103 := bstep (se 1 (by rfl) ⟨622577, by rfl⟩ : syracuseStep 830103 = 1245155) B1245155
theorem B830123 : Blo 826349 830123 := bstep (se 1 (by rfl) ⟨622592, by rfl⟩ : syracuseStep 830123 = 1245185) B1245185
theorem B830135 : Blo 826349 830135 := bstep (se 1 (by rfl) ⟨622601, by rfl⟩ : syracuseStep 830135 = 1245203) B1245203
theorem B830155 : Blo 826349 830155 := bstep (se 1 (by rfl) ⟨622616, by rfl⟩ : syracuseStep 830155 = 1245233) B1245233
theorem B9546445 : Blo 826349 9546445 := bstep (se 3 (by rfl) ⟨1789958, by rfl⟩ : syracuseStep 9546445 = 3579917) B3579917
theorem B830167 : Blo 826349 830167 := bstep (se 1 (by rfl) ⟨622625, by rfl⟩ : syracuseStep 830167 = 1245251) B1245251
theorem B830187 : Blo 826349 830187 := bstep (se 1 (by rfl) ⟨622640, by rfl⟩ : syracuseStep 830187 = 1245281) B1245281
theorem B830199 : Blo 826349 830199 := bstep (se 1 (by rfl) ⟨622649, by rfl⟩ : syracuseStep 830199 = 1245299) B1245299
theorem B830219 : Blo 826349 830219 := bstep (se 1 (by rfl) ⟨622664, by rfl⟩ : syracuseStep 830219 = 1245329) B1245329
theorem B830231 : Blo 826349 830231 := bstep (se 1 (by rfl) ⟨622673, by rfl⟩ : syracuseStep 830231 = 1245347) B1245347
theorem B830251 : Blo 826349 830251 := bstep (se 1 (by rfl) ⟨622688, by rfl⟩ : syracuseStep 830251 = 1245377) B1245377
theorem B830263 : Blo 826349 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B830283 : Blo 826349 830283 := bstep (se 1 (by rfl) ⟨622712, by rfl⟩ : syracuseStep 830283 = 1245425) B1245425
theorem B830295 : Blo 826349 830295 := bstep (se 1 (by rfl) ⟨622721, by rfl⟩ : syracuseStep 830295 = 1245443) B1245443
theorem B830315 : Blo 826349 830315 := bstep (se 1 (by rfl) ⟨622736, by rfl⟩ : syracuseStep 830315 = 1245473) B1245473
theorem B830327 : Blo 826349 830327 := bstep (se 1 (by rfl) ⟨622745, by rfl⟩ : syracuseStep 830327 = 1245491) B1245491
theorem B830347 : Blo 826349 830347 := bstep (se 1 (by rfl) ⟨622760, by rfl⟩ : syracuseStep 830347 = 1245521) B1245521
theorem B1616843 : Blo 826349 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B7973923 : Blo 826349 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B2796875 : Blo 826349 2796875 := bstep (se 1 (by rfl) ⟨2097656, by rfl⟩ : syracuseStep 2796875 = 4195313) B4195313
theorem B1257049 : Blo 826349 1257049 := bstep (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) B942787
theorem B2797145 : Blo 826349 2797145 := bstep (se 2 (by rfl) ⟨1048929, by rfl⟩ : syracuseStep 2797145 = 2097859) B2097859
theorem B24161885 : Blo 826349 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B4534147 : Blo 826349 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B929803 : Blo 826349 929803 := bstep (se 1 (by rfl) ⟨697352, by rfl⟩ : syracuseStep 929803 = 1394705) B1394705
theorem B14004299 : Blo 826349 14004299 := bstep (se 1 (by rfl) ⟨10503224, by rfl⟩ : syracuseStep 14004299 = 21006449) B21006449
theorem B929911 : Blo 826349 929911 := bstep (se 1 (by rfl) ⟨697433, by rfl⟩ : syracuseStep 929911 = 1394867) B1394867
theorem B2797847 : Blo 826349 2797847 := bstep (se 1 (by rfl) ⟨2098385, by rfl⟩ : syracuseStep 2797847 = 4196771) B4196771
theorem B930091 : Blo 826349 930091 := bstep (se 1 (by rfl) ⟨697568, by rfl⟩ : syracuseStep 930091 = 1395137) B1395137
theorem B930199 : Blo 826349 930199 := bstep (se 1 (by rfl) ⟨697649, by rfl⟩ : syracuseStep 930199 = 1395299) B1395299
theorem B930379 : Blo 826349 930379 := bstep (se 1 (by rfl) ⟨697784, by rfl⟩ : syracuseStep 930379 = 1395569) B1395569
theorem B930487 : Blo 826349 930487 := bstep (se 1 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 930487 = 1395731) B1395731
theorem B2798387 : Blo 826349 2798387 := bstep (se 1 (by rfl) ⟨2098790, by rfl⟩ : syracuseStep 2798387 = 4197581) B4197581
theorem B930667 : Blo 826349 930667 := bstep (se 1 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 930667 = 1396001) B1396001
theorem B930775 : Blo 826349 930775 := bstep (se 1 (by rfl) ⟨698081, by rfl⟩ : syracuseStep 930775 = 1396163) B1396163
theorem B2798657 : Blo 826349 2798657 := bstep (se 2 (by rfl) ⟨1049496, by rfl⟩ : syracuseStep 2798657 = 2098993) B2098993
theorem B930955 : Blo 826349 930955 := bstep (se 1 (by rfl) ⟨698216, by rfl⟩ : syracuseStep 930955 = 1396433) B1396433
theorem B931063 : Blo 826349 931063 := bstep (se 1 (by rfl) ⟨698297, by rfl⟩ : syracuseStep 931063 = 1396595) B1396595
theorem B3585325 : Blo 826349 3585325 := bstep (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) B1344497
theorem B931243 : Blo 826349 931243 := bstep (se 1 (by rfl) ⟨698432, by rfl⟩ : syracuseStep 931243 = 1396865) B1396865
theorem B2242009 : Blo 826349 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B931351 : Blo 826349 931351 := bstep (se 1 (by rfl) ⟨698513, by rfl⟩ : syracuseStep 931351 = 1397027) B1397027
theorem B2799197 : Blo 826349 2799197 := bstep (se 3 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 2799197 = 1049699) B1049699
theorem B931531 : Blo 826349 931531 := bstep (se 1 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 931531 = 1397297) B1397297
theorem B931639 : Blo 826349 931639 := bstep (se 1 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 931639 = 1397459) B1397459
theorem B1325015 : Blo 826349 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B931819 : Blo 826349 931819 := bstep (se 1 (by rfl) ⟨698864, by rfl⟩ : syracuseStep 931819 = 1397729) B1397729
theorem B931927 : Blo 826349 931927 := bstep (se 1 (by rfl) ⟨698945, by rfl⟩ : syracuseStep 931927 = 1397891) B1397891
theorem B932107 : Blo 826349 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B932215 : Blo 826349 932215 := bstep (se 1 (by rfl) ⟨699161, by rfl⟩ : syracuseStep 932215 = 1398323) B1398323
theorem B1325527 : Blo 826349 1325527 := bstep (se 1 (by rfl) ⟨994145, by rfl⟩ : syracuseStep 1325527 = 1988291) B1988291
theorem B3979793 : Blo 826349 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B9812515 : Blo 826349 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B932395 : Blo 826349 932395 := bstep (se 1 (by rfl) ⟨699296, by rfl⟩ : syracuseStep 932395 = 1398593) B1398593
theorem B10074775 : Blo 826349 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B932503 : Blo 826349 932503 := bstep (se 1 (by rfl) ⟨699377, by rfl⟩ : syracuseStep 932503 = 1398755) B1398755
theorem B2800331 : Blo 826349 2800331 := bstep (se 1 (by rfl) ⟨2100248, by rfl⟩ : syracuseStep 2800331 = 4200497) B4200497
theorem B24263489 : Blo 826349 24263489 := bstep (se 2 (by rfl) ⟨9098808, by rfl⟩ : syracuseStep 24263489 = 18197617) B18197617
theorem B1325899 : Blo 826349 1325899 := bstep (se 1 (by rfl) ⟨994424, by rfl⟩ : syracuseStep 1325899 = 1988849) B1988849
theorem B932683 : Blo 826349 932683 := bstep (se 1 (by rfl) ⟨699512, by rfl⟩ : syracuseStep 932683 = 1399025) B1399025
theorem B932791 : Blo 826349 932791 := bstep (se 1 (by rfl) ⟨699593, by rfl⟩ : syracuseStep 932791 = 1399187) B1399187
theorem B2800601 : Blo 826349 2800601 := bstep (se 2 (by rfl) ⟨1050225, by rfl⟩ : syracuseStep 2800601 = 2100451) B2100451
theorem B932971 : Blo 826349 932971 := bstep (se 1 (by rfl) ⟨699728, by rfl⟩ : syracuseStep 932971 = 1399457) B1399457
theorem B1490123 : Blo 826349 1490123 := bstep (se 1 (by rfl) ⟨1117592, by rfl⟩ : syracuseStep 1490123 = 2235185) B2235185
theorem B933079 : Blo 826349 933079 := bstep (se 1 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 933079 = 1399619) B1399619
theorem B4472081 : Blo 826349 4472081 := bstep (se 2 (by rfl) ⟨1677030, by rfl⟩ : syracuseStep 4472081 = 3354061) B3354061
theorem B933259 : Blo 826349 933259 := bstep (se 1 (by rfl) ⟨699944, by rfl⟩ : syracuseStep 933259 = 1399889) B1399889
theorem B1261003 : Blo 826349 1261003 := bstep (se 1 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 1261003 = 1891505) B1891505
theorem B933367 : Blo 826349 933367 := bstep (se 1 (by rfl) ⟨700025, by rfl⟩ : syracuseStep 933367 = 1400051) B1400051
theorem B1490521 : Blo 826349 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B2801303 : Blo 826349 2801303 := bstep (se 1 (by rfl) ⟨2100977, by rfl⟩ : syracuseStep 2801303 = 4201955) B4201955
theorem B933547 : Blo 826349 933547 := bstep (se 1 (by rfl) ⟨700160, by rfl⟩ : syracuseStep 933547 = 1400321) B1400321
theorem B1326809 : Blo 826349 1326809 := bstep (se 2 (by rfl) ⟨497553, by rfl⟩ : syracuseStep 1326809 = 995107) B995107
theorem B9060101 : Blo 826349 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B933655 : Blo 826349 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B1326937 : Blo 826349 1326937 := bstep (se 2 (by rfl) ⟨497601, by rfl⟩ : syracuseStep 1326937 = 995203) B995203
theorem B933835 : Blo 826349 933835 := bstep (se 1 (by rfl) ⟨700376, by rfl⟩ : syracuseStep 933835 = 1400753) B1400753
theorem B933943 : Blo 826349 933943 := bstep (se 1 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 933943 = 1400915) B1400915
theorem B2801843 : Blo 826349 2801843 := bstep (se 1 (by rfl) ⟨2101382, by rfl⟩ : syracuseStep 2801843 = 4202765) B4202765
theorem B934123 : Blo 826349 934123 := bstep (se 1 (by rfl) ⟨700592, by rfl⟩ : syracuseStep 934123 = 1401185) B1401185
theorem B7979269 : Blo 826349 7979269 := bstep (se 4 (by rfl) ⟨748056, by rfl⟩ : syracuseStep 7979269 = 1496113) B1496113
theorem B5030237 : Blo 826349 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B2802113 : Blo 826349 2802113 := bstep (se 2 (by rfl) ⟨1050792, by rfl⟩ : syracuseStep 2802113 = 2101585) B2101585
theorem B1262231 : Blo 826349 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B1884953 : Blo 826349 1884953 := bstep (se 2 (by rfl) ⟨706857, by rfl⟩ : syracuseStep 1884953 = 1413715) B1413715
theorem B6800203 : Blo 826349 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B1197337 : Blo 826349 1197337 := bstep (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) B898003
theorem B10634561 : Blo 826349 10634561 := bstep (se 2 (by rfl) ⟨3987960, by rfl⟩ : syracuseStep 10634561 = 7975921) B7975921
theorem B5392003 : Blo 826349 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B9423053 : Blo 826349 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1395083 : Blo 826349 1395083 := bstep (se 1 (by rfl) ⟨1046312, by rfl⟩ : syracuseStep 1395083 = 2092625) B2092625
theorem B3590659 : Blo 826349 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1395211 : Blo 826349 1395211 := bstep (se 1 (by rfl) ⟨1046408, by rfl⟩ : syracuseStep 1395211 = 2092817) B2092817
theorem B1395353 : Blo 826349 1395353 := bstep (se 2 (by rfl) ⟨523257, by rfl⟩ : syracuseStep 1395353 = 1046515) B1046515
theorem B1395481 : Blo 826349 1395481 := bstep (se 2 (by rfl) ⟨523305, by rfl⟩ : syracuseStep 1395481 = 1046611) B1046611
theorem B11324377 : Blo 826349 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B5983325 : Blo 826349 5983325 := bstep (se 3 (by rfl) ⟨1121873, by rfl⟩ : syracuseStep 5983325 = 2243747) B2243747
theorem B1494131 : Blo 826349 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B1396055 : Blo 826349 1396055 := bstep (se 1 (by rfl) ⟨1047041, by rfl⟩ : syracuseStep 1396055 = 2094083) B2094083
theorem B1396183 : Blo 826349 1396183 := bstep (se 1 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 1396183 = 2094275) B2094275
theorem B839435 : Blo 826349 839435 := bstep (se 1 (by rfl) ⟨629576, by rfl⟩ : syracuseStep 839435 = 1259153) B1259153
theorem B1396811 : Blo 826349 1396811 := bstep (se 1 (by rfl) ⟨1047608, by rfl⟩ : syracuseStep 1396811 = 2095217) B2095217
theorem B1396939 : Blo 826349 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B1495255 : Blo 826349 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1397081 : Blo 826349 1397081 := bstep (se 2 (by rfl) ⟨523905, by rfl⟩ : syracuseStep 1397081 = 1047811) B1047811
theorem B7066061 : Blo 826349 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B1397209 : Blo 826349 1397209 := bstep (se 2 (by rfl) ⟨523953, by rfl⟩ : syracuseStep 1397209 = 1047907) B1047907
theorem B1790515 : Blo 826349 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B3363545 : Blo 826349 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B1495883 : Blo 826349 1495883 := bstep (se 1 (by rfl) ⟨1121912, by rfl⟩ : syracuseStep 1495883 = 2243825) B2243825
theorem B1397783 : Blo 826349 1397783 := bstep (se 1 (by rfl) ⟨1048337, by rfl⟩ : syracuseStep 1397783 = 2096675) B2096675
theorem B1397911 : Blo 826349 1397911 := bstep (se 1 (by rfl) ⟨1048433, by rfl⟩ : syracuseStep 1397911 = 2096867) B2096867
theorem B3593495 : Blo 826349 3593495 := bstep (se 1 (by rfl) ⟨2695121, by rfl⟩ : syracuseStep 3593495 = 5390243) B5390243
theorem B26891747 : Blo 826349 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B2840129 : Blo 826349 2840129 := bstep (se 2 (by rfl) ⟨1065048, by rfl⟩ : syracuseStep 2840129 = 2130097) B2130097
theorem B1889945 : Blo 826349 1889945 := bstep (se 2 (by rfl) ⟨708729, by rfl⟩ : syracuseStep 1889945 = 1417459) B1417459
theorem B48420557 : Blo 826349 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B1398539 : Blo 826349 1398539 := bstep (se 1 (by rfl) ⟨1048904, by rfl⟩ : syracuseStep 1398539 = 2097809) B2097809
theorem B4085569 : Blo 826349 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B1398667 : Blo 826349 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B1398809 : Blo 826349 1398809 := bstep (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) B1049107
theorem B3365009 : Blo 826349 3365009 := bstep (se 2 (by rfl) ⟨1261878, by rfl⟩ : syracuseStep 3365009 = 2523757) B2523757
theorem B1398937 : Blo 826349 1398937 := bstep (se 2 (by rfl) ⟨524601, by rfl⟩ : syracuseStep 1398937 = 1049203) B1049203
theorem B4184621 : Blo 826349 4184621 := bstep (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) B1569233
theorem B3594883 : Blo 826349 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B12114613 : Blo 826349 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B1399511 : Blo 826349 1399511 := bstep (se 1 (by rfl) ⟨1049633, by rfl⟩ : syracuseStep 1399511 = 2099267) B2099267
theorem B8936237 : Blo 826349 8936237 := bstep (se 3 (by rfl) ⟨1675544, by rfl⟩ : syracuseStep 8936237 = 3351089) B3351089
theorem B1399639 : Blo 826349 1399639 := bstep (se 1 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 1399639 = 2099459) B2099459
theorem B15129461 : Blo 826349 15129461 := bstep (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) B1418387
theorem B1400267 : Blo 826349 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B3530263 : Blo 826349 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B4709933 : Blo 826349 4709933 := bstep (se 3 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 4709933 = 1766225) B1766225
theorem B1400395 : Blo 826349 1400395 := bstep (se 1 (by rfl) ⟨1050296, by rfl⟩ : syracuseStep 1400395 = 2100593) B2100593
theorem B1400537 : Blo 826349 1400537 := bstep (se 2 (by rfl) ⟨525201, by rfl⟩ : syracuseStep 1400537 = 1050403) B1050403
theorem B3366659 : Blo 826349 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B1859417 : Blo 826349 1859417 := bstep (se 2 (by rfl) ⟨697281, by rfl⟩ : syracuseStep 1859417 = 1394563) B1394563
theorem B1400665 : Blo 826349 1400665 := bstep (se 2 (by rfl) ⟨525249, by rfl⟩ : syracuseStep 1400665 = 1050499) B1050499
theorem B1859507 : Blo 826349 1859507 := bstep (se 1 (by rfl) ⟨1394630, by rfl⟩ : syracuseStep 1859507 = 2789261) B2789261
theorem B1859543 : Blo 826349 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B1859723 : Blo 826349 1859723 := bstep (se 1 (by rfl) ⟨1394792, by rfl⟩ : syracuseStep 1859723 = 2789585) B2789585
theorem B3530897 : Blo 826349 3530897 := bstep (se 2 (by rfl) ⟨1324086, by rfl⟩ : syracuseStep 3530897 = 2648173) B2648173
theorem B2875571 : Blo 826349 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B1859777 : Blo 826349 1859777 := bstep (se 2 (by rfl) ⟨697416, by rfl⟩ : syracuseStep 1859777 = 1394833) B1394833
theorem B93184277 : Blo 826349 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B1859993 : Blo 826349 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B13459891 : Blo 826349 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B1860083 : Blo 826349 1860083 := bstep (se 1 (by rfl) ⟨1395062, by rfl⟩ : syracuseStep 1860083 = 2790125) B2790125
theorem B1860119 : Blo 826349 1860119 := bstep (se 1 (by rfl) ⟨1395089, by rfl⟩ : syracuseStep 1860119 = 2790179) B2790179
theorem B1991233 : Blo 826349 1991233 := bstep (se 2 (by rfl) ⟨746712, by rfl⟩ : syracuseStep 1991233 = 1493425) B1493425
theorem B1860299 : Blo 826349 1860299 := bstep (se 1 (by rfl) ⟨1395224, by rfl⟩ : syracuseStep 1860299 = 2790449) B2790449
theorem B1860353 : Blo 826349 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B3531595 : Blo 826349 3531595 := bstep (se 1 (by rfl) ⟨2648696, by rfl⟩ : syracuseStep 3531595 = 5297393) B5297393
theorem B6710195 : Blo 826349 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B3138497 : Blo 826349 3138497 := bstep (se 2 (by rfl) ⟨1176936, by rfl⟩ : syracuseStep 3138497 = 2353873) B2353873
theorem B1860569 : Blo 826349 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B1893401 : Blo 826349 1893401 := bstep (se 2 (by rfl) ⟨710025, by rfl⟩ : syracuseStep 1893401 = 1420051) B1420051
theorem B1860659 : Blo 826349 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B1860695 : Blo 826349 1860695 := bstep (se 1 (by rfl) ⟨1395521, by rfl⟩ : syracuseStep 1860695 = 2791043) B2791043
theorem B3531869 : Blo 826349 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B7070813 : Blo 826349 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B6284465 : Blo 826349 6284465 := bstep (se 2 (by rfl) ⟨2356674, by rfl⟩ : syracuseStep 6284465 = 4713349) B4713349
theorem B1991897 : Blo 826349 1991897 := bstep (se 2 (by rfl) ⟨746961, by rfl⟩ : syracuseStep 1991897 = 1493923) B1493923
theorem B2516189 : Blo 826349 2516189 := bstep (se 3 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 2516189 = 943571) B943571
theorem B1860875 : Blo 826349 1860875 := bstep (se 1 (by rfl) ⟨1395656, by rfl⟩ : syracuseStep 1860875 = 2791313) B2791313
theorem B1860929 : Blo 826349 1860929 := bstep (se 2 (by rfl) ⟨697848, by rfl⟩ : syracuseStep 1860929 = 1395697) B1395697
theorem B3532211 : Blo 826349 3532211 := bstep (se 1 (by rfl) ⟨2649158, by rfl⟩ : syracuseStep 3532211 = 5298317) B5298317
theorem B1861145 : Blo 826349 1861145 := bstep (se 2 (by rfl) ⟨697929, by rfl⟩ : syracuseStep 1861145 = 1395859) B1395859
theorem B1861235 : Blo 826349 1861235 := bstep (se 1 (by rfl) ⟨1395926, by rfl⟩ : syracuseStep 1861235 = 2791853) B2791853
theorem B1861271 : Blo 826349 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B6284951 : Blo 826349 6284951 := bstep (se 1 (by rfl) ⟨4713713, by rfl⟩ : syracuseStep 6284951 = 9427427) B9427427
theorem B1795841 : Blo 826349 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B1861451 : Blo 826349 1861451 := bstep (se 1 (by rfl) ⟨1396088, by rfl⟩ : syracuseStep 1861451 = 2792177) B2792177
theorem B1861505 : Blo 826349 1861505 := bstep (se 2 (by rfl) ⟨698064, by rfl⟩ : syracuseStep 1861505 = 1396129) B1396129
theorem B2418611 : Blo 826349 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B1861721 : Blo 826349 1861721 := bstep (se 2 (by rfl) ⟨698145, by rfl⟩ : syracuseStep 1861721 = 1396291) B1396291
theorem B2353303 : Blo 826349 2353303 := bstep (se 1 (by rfl) ⟨1764977, by rfl⟩ : syracuseStep 2353303 = 3529955) B3529955
theorem B5957783 : Blo 826349 5957783 := bstep (se 1 (by rfl) ⟨4468337, by rfl⟩ : syracuseStep 5957783 = 8936675) B8936675
theorem B1861811 : Blo 826349 1861811 := bstep (se 1 (by rfl) ⟨1396358, by rfl⟩ : syracuseStep 1861811 = 2792717) B2792717
theorem B1861847 : Blo 826349 1861847 := bstep (se 1 (by rfl) ⟨1396385, by rfl⟩ : syracuseStep 1861847 = 2792771) B2792771
theorem B4188509 : Blo 826349 4188509 := bstep (se 3 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 4188509 = 1570691) B1570691
theorem B1862027 : Blo 826349 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B3139985 : Blo 826349 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B1862081 : Blo 826349 1862081 := bstep (se 2 (by rfl) ⟨698280, by rfl⟩ : syracuseStep 1862081 = 1396561) B1396561
theorem B1239563 : Blo 826349 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B1239575 : Blo 826349 1239575 := bstep (se 1 (by rfl) ⟨929681, by rfl⟩ : syracuseStep 1239575 = 1859363) B1859363
theorem B1239641 : Blo 826349 1239641 := bstep (se 2 (by rfl) ⟨464865, by rfl⟩ : syracuseStep 1239641 = 929731) B929731
theorem B1862297 : Blo 826349 1862297 := bstep (se 2 (by rfl) ⟨698361, by rfl⟩ : syracuseStep 1862297 = 1396723) B1396723
theorem B1239755 : Blo 826349 1239755 := bstep (se 1 (by rfl) ⟨929816, by rfl⟩ : syracuseStep 1239755 = 1859633) B1859633
theorem B1239767 : Blo 826349 1239767 := bstep (se 1 (by rfl) ⟨929825, by rfl⟩ : syracuseStep 1239767 = 1859651) B1859651
theorem B1862387 : Blo 826349 1862387 := bstep (se 1 (by rfl) ⟨1396790, by rfl⟩ : syracuseStep 1862387 = 2793581) B2793581
theorem B1862423 : Blo 826349 1862423 := bstep (se 1 (by rfl) ⟨1396817, by rfl⟩ : syracuseStep 1862423 = 2793635) B2793635
theorem B1239833 : Blo 826349 1239833 := bstep (se 2 (by rfl) ⟨464937, by rfl⟩ : syracuseStep 1239833 = 929875) B929875
theorem B6712109 : Blo 826349 6712109 := bstep (se 3 (by rfl) ⟨1258520, by rfl⟩ : syracuseStep 6712109 = 2517041) B2517041
theorem B2091865 : Blo 826349 2091865 := bstep (se 2 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 2091865 = 1568899) B1568899
theorem B3140441 : Blo 826349 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B1239947 : Blo 826349 1239947 := bstep (se 1 (by rfl) ⟨929960, by rfl⟩ : syracuseStep 1239947 = 1859921) B1859921
theorem B1239959 : Blo 826349 1239959 := bstep (se 1 (by rfl) ⟨929969, by rfl⟩ : syracuseStep 1239959 = 1859939) B1859939
theorem B2354123 : Blo 826349 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B1862603 : Blo 826349 1862603 := bstep (se 1 (by rfl) ⟨1396952, by rfl⟩ : syracuseStep 1862603 = 2793905) B2793905
theorem B1240025 : Blo 826349 1240025 := bstep (se 2 (by rfl) ⟨465009, by rfl⟩ : syracuseStep 1240025 = 930019) B930019
theorem B1862657 : Blo 826349 1862657 := bstep (se 2 (by rfl) ⟨698496, by rfl⟩ : syracuseStep 1862657 = 1396993) B1396993
theorem B11955235 : Blo 826349 11955235 := bstep (se 1 (by rfl) ⟨8966426, by rfl⟩ : syracuseStep 11955235 = 17932853) B17932853
theorem B3140653 : Blo 826349 3140653 := bstep (se 3 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 3140653 = 1177745) B1177745
theorem B1240139 : Blo 826349 1240139 := bstep (se 1 (by rfl) ⟨930104, by rfl⟩ : syracuseStep 1240139 = 1860209) B1860209
theorem B1240151 : Blo 826349 1240151 := bstep (se 1 (by rfl) ⟨930113, by rfl⟩ : syracuseStep 1240151 = 1860227) B1860227
theorem B4713623 : Blo 826349 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B1240217 : Blo 826349 1240217 := bstep (se 2 (by rfl) ⟨465081, by rfl⟩ : syracuseStep 1240217 = 930163) B930163
theorem B1862873 : Blo 826349 1862873 := bstep (se 2 (by rfl) ⟨698577, by rfl⟩ : syracuseStep 1862873 = 1397155) B1397155
theorem B1240331 : Blo 826349 1240331 := bstep (se 1 (by rfl) ⟨930248, by rfl⟩ : syracuseStep 1240331 = 1860497) B1860497
theorem B1240343 : Blo 826349 1240343 := bstep (se 1 (by rfl) ⟨930257, by rfl⟩ : syracuseStep 1240343 = 1860515) B1860515
theorem B1862963 : Blo 826349 1862963 := bstep (se 1 (by rfl) ⟨1397222, by rfl⟩ : syracuseStep 1862963 = 2794445) B2794445
theorem B1862999 : Blo 826349 1862999 := bstep (se 1 (by rfl) ⟨1397249, by rfl⟩ : syracuseStep 1862999 = 2794499) B2794499
theorem B1240409 : Blo 826349 1240409 := bstep (se 2 (by rfl) ⟨465153, by rfl⟩ : syracuseStep 1240409 = 930307) B930307
theorem B3140957 : Blo 826349 3140957 := bstep (se 3 (by rfl) ⟨588929, by rfl⟩ : syracuseStep 3140957 = 1177859) B1177859
theorem B4779415 : Blo 826349 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B1240523 : Blo 826349 1240523 := bstep (se 1 (by rfl) ⟨930392, by rfl⟩ : syracuseStep 1240523 = 1860785) B1860785
theorem B1240535 : Blo 826349 1240535 := bstep (se 1 (by rfl) ⟨930401, by rfl⟩ : syracuseStep 1240535 = 1860803) B1860803
theorem B6712793 : Blo 826349 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B1764875 : Blo 826349 1764875 := bstep (se 1 (by rfl) ⟨1323656, by rfl⟩ : syracuseStep 1764875 = 2647313) B2647313
theorem B1863179 : Blo 826349 1863179 := bstep (se 1 (by rfl) ⟨1397384, by rfl⟩ : syracuseStep 1863179 = 2794769) B2794769
theorem B1240601 : Blo 826349 1240601 := bstep (se 2 (by rfl) ⟨465225, by rfl⟩ : syracuseStep 1240601 = 930451) B930451
theorem B1863233 : Blo 826349 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B1240715 : Blo 826349 1240715 := bstep (se 1 (by rfl) ⟨930536, by rfl⟩ : syracuseStep 1240715 = 1861073) B1861073
theorem B1240727 : Blo 826349 1240727 := bstep (se 1 (by rfl) ⟨930545, by rfl⟩ : syracuseStep 1240727 = 1861091) B1861091
theorem B2420417 : Blo 826349 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B1240793 : Blo 826349 1240793 := bstep (se 2 (by rfl) ⟨465297, by rfl⟩ : syracuseStep 1240793 = 930595) B930595
theorem B1994519 : Blo 826349 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B1863449 : Blo 826349 1863449 := bstep (se 2 (by rfl) ⟨698793, by rfl⟩ : syracuseStep 1863449 = 1397587) B1397587
theorem B3534637 : Blo 826349 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B1240907 : Blo 826349 1240907 := bstep (se 1 (by rfl) ⟨930680, by rfl⟩ : syracuseStep 1240907 = 1861361) B1861361
theorem B1240919 : Blo 826349 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B1863539 : Blo 826349 1863539 := bstep (se 1 (by rfl) ⟨1397654, by rfl⟩ : syracuseStep 1863539 = 2795309) B2795309
theorem B1863575 : Blo 826349 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B1240985 : Blo 826349 1240985 := bstep (se 2 (by rfl) ⟨465369, by rfl⟩ : syracuseStep 1240985 = 930739) B930739
theorem B2092979 : Blo 826349 2092979 := bstep (se 1 (by rfl) ⟨1569734, by rfl⟩ : syracuseStep 2092979 = 3139469) B3139469
theorem B1241099 : Blo 826349 1241099 := bstep (se 1 (by rfl) ⟨930824, by rfl⟩ : syracuseStep 1241099 = 1861649) B1861649
theorem B1241111 : Blo 826349 1241111 := bstep (se 1 (by rfl) ⟨930833, by rfl⟩ : syracuseStep 1241111 = 1861667) B1861667
theorem B5304365 : Blo 826349 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B1863755 : Blo 826349 1863755 := bstep (se 1 (by rfl) ⟨1397816, by rfl⟩ : syracuseStep 1863755 = 2795633) B2795633
theorem B1994827 : Blo 826349 1994827 := bstep (se 1 (by rfl) ⟨1496120, by rfl⟩ : syracuseStep 1994827 = 2992241) B2992241
theorem B1241177 : Blo 826349 1241177 := bstep (se 2 (by rfl) ⟨465441, by rfl⟩ : syracuseStep 1241177 = 930883) B930883
theorem B1863809 : Blo 826349 1863809 := bstep (se 2 (by rfl) ⟨698928, by rfl⟩ : syracuseStep 1863809 = 1397857) B1397857
theorem B1241291 : Blo 826349 1241291 := bstep (se 1 (by rfl) ⟨930968, by rfl⟩ : syracuseStep 1241291 = 1861937) B1861937
theorem B1568983 : Blo 826349 1568983 := bstep (se 1 (by rfl) ⟨1176737, by rfl⟩ : syracuseStep 1568983 = 2353475) B2353475
theorem B1241303 : Blo 826349 1241303 := bstep (se 1 (by rfl) ⟨930977, by rfl⟩ : syracuseStep 1241303 = 1861955) B1861955
theorem B2093273 : Blo 826349 2093273 := bstep (se 2 (by rfl) ⟨784977, by rfl⟩ : syracuseStep 2093273 = 1569955) B1569955
theorem B1241369 : Blo 826349 1241369 := bstep (se 2 (by rfl) ⟨465513, by rfl⟩ : syracuseStep 1241369 = 931027) B931027
theorem B1864025 : Blo 826349 1864025 := bstep (se 2 (by rfl) ⟨699009, by rfl⟩ : syracuseStep 1864025 = 1398019) B1398019
theorem B1241483 : Blo 826349 1241483 := bstep (se 1 (by rfl) ⟨931112, by rfl⟩ : syracuseStep 1241483 = 1862225) B1862225
theorem B1241495 : Blo 826349 1241495 := bstep (se 1 (by rfl) ⟨931121, by rfl⟩ : syracuseStep 1241495 = 1862243) B1862243
theorem B4190615 : Blo 826349 4190615 := bstep (se 1 (by rfl) ⟨3142961, by rfl⟩ : syracuseStep 4190615 = 6285923) B6285923
theorem B14184881 : Blo 826349 14184881 := bstep (se 2 (by rfl) ⟨5319330, by rfl⟩ : syracuseStep 14184881 = 10638661) B10638661
theorem B1569203 : Blo 826349 1569203 := bstep (se 1 (by rfl) ⟨1176902, by rfl⟩ : syracuseStep 1569203 = 2353805) B2353805
theorem B1864115 : Blo 826349 1864115 := bstep (se 1 (by rfl) ⟨1398086, by rfl⟩ : syracuseStep 1864115 = 2796173) B2796173
theorem B1864151 : Blo 826349 1864151 := bstep (se 1 (by rfl) ⟨1398113, by rfl⟩ : syracuseStep 1864151 = 2796227) B2796227
theorem B1241561 : Blo 826349 1241561 := bstep (se 2 (by rfl) ⟨465585, by rfl⟩ : syracuseStep 1241561 = 931171) B931171
theorem B1241675 : Blo 826349 1241675 := bstep (se 1 (by rfl) ⟨931256, by rfl⟩ : syracuseStep 1241675 = 1862513) B1862513
theorem B1241687 : Blo 826349 1241687 := bstep (se 1 (by rfl) ⟨931265, by rfl⟩ : syracuseStep 1241687 = 1862531) B1862531
theorem B1864331 : Blo 826349 1864331 := bstep (se 1 (by rfl) ⟨1398248, by rfl⟩ : syracuseStep 1864331 = 2796497) B2796497
theorem B1569431 : Blo 826349 1569431 := bstep (se 1 (by rfl) ⟨1177073, by rfl⟩ : syracuseStep 1569431 = 2354147) B2354147
theorem B1241753 : Blo 826349 1241753 := bstep (se 2 (by rfl) ⟨465657, by rfl⟩ : syracuseStep 1241753 = 931315) B931315
theorem B1864385 : Blo 826349 1864385 := bstep (se 2 (by rfl) ⟨699144, by rfl⟩ : syracuseStep 1864385 = 1398289) B1398289
theorem B1241867 : Blo 826349 1241867 := bstep (se 1 (by rfl) ⟨931400, by rfl⟩ : syracuseStep 1241867 = 1862801) B1862801
theorem B5960465 : Blo 826349 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B1241879 : Blo 826349 1241879 := bstep (se 1 (by rfl) ⟨931409, by rfl⟩ : syracuseStep 1241879 = 1862819) B1862819
theorem B1241945 : Blo 826349 1241945 := bstep (se 2 (by rfl) ⟨465729, by rfl⟩ : syracuseStep 1241945 = 931459) B931459
theorem B1569689 : Blo 826349 1569689 := bstep (se 2 (by rfl) ⟨588633, by rfl⟩ : syracuseStep 1569689 = 1177267) B1177267
theorem B1864601 : Blo 826349 1864601 := bstep (se 2 (by rfl) ⟨699225, by rfl⟩ : syracuseStep 1864601 = 1398451) B1398451
theorem B1242059 : Blo 826349 1242059 := bstep (se 1 (by rfl) ⟨931544, by rfl⟩ : syracuseStep 1242059 = 1863089) B1863089
theorem B1242071 : Blo 826349 1242071 := bstep (se 1 (by rfl) ⟨931553, by rfl⟩ : syracuseStep 1242071 = 1863107) B1863107
theorem B1864691 : Blo 826349 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B7173137 : Blo 826349 7173137 := bstep (se 2 (by rfl) ⟨2689926, by rfl⟩ : syracuseStep 7173137 = 5379853) B5379853
theorem B1864727 : Blo 826349 1864727 := bstep (se 1 (by rfl) ⟨1398545, by rfl⟩ : syracuseStep 1864727 = 2797091) B2797091
theorem B1176601 : Blo 826349 1176601 := bstep (se 2 (by rfl) ⟨441225, by rfl⟩ : syracuseStep 1176601 = 882451) B882451
theorem B1242137 : Blo 826349 1242137 := bstep (se 2 (by rfl) ⟨465801, by rfl⟩ : syracuseStep 1242137 = 931603) B931603
theorem B2978861 : Blo 826349 2978861 := bstep (se 3 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 2978861 = 1117073) B1117073
theorem B1242251 : Blo 826349 1242251 := bstep (se 1 (by rfl) ⟨931688, by rfl⟩ : syracuseStep 1242251 = 1863377) B1863377
theorem B1242263 : Blo 826349 1242263 := bstep (se 1 (by rfl) ⟨931697, by rfl⟩ : syracuseStep 1242263 = 1863395) B1863395
theorem B1864907 : Blo 826349 1864907 := bstep (se 1 (by rfl) ⟨1398680, by rfl⟩ : syracuseStep 1864907 = 2797361) B2797361
theorem B1242329 : Blo 826349 1242329 := bstep (se 2 (by rfl) ⟨465873, by rfl⟩ : syracuseStep 1242329 = 931747) B931747
theorem B1864961 : Blo 826349 1864961 := bstep (se 2 (by rfl) ⟨699360, by rfl⟩ : syracuseStep 1864961 = 1398721) B1398721
theorem B1570099 : Blo 826349 1570099 := bstep (se 1 (by rfl) ⟨1177574, by rfl⟩ : syracuseStep 1570099 = 2355149) B2355149
theorem B8975681 : Blo 826349 8975681 := bstep (se 2 (by rfl) ⟨3365880, by rfl⟩ : syracuseStep 8975681 = 6731761) B6731761
theorem B1242443 : Blo 826349 1242443 := bstep (se 1 (by rfl) ⟨931832, by rfl⟩ : syracuseStep 1242443 = 1863665) B1863665
theorem B1242455 : Blo 826349 1242455 := bstep (se 1 (by rfl) ⟨931841, by rfl⟩ : syracuseStep 1242455 = 1863683) B1863683
theorem B2356573 : Blo 826349 2356573 := bstep (se 3 (by rfl) ⟨441857, by rfl⟩ : syracuseStep 2356573 = 883715) B883715
theorem B1242521 : Blo 826349 1242521 := bstep (se 2 (by rfl) ⟨465945, by rfl⟩ : syracuseStep 1242521 = 931891) B931891
theorem B1045963 : Blo 826349 1045963 := bstep (se 1 (by rfl) ⟨784472, by rfl⟩ : syracuseStep 1045963 = 1568945) B1568945
theorem B1865177 : Blo 826349 1865177 := bstep (se 2 (by rfl) ⟨699441, by rfl⟩ : syracuseStep 1865177 = 1398883) B1398883
theorem B1242635 : Blo 826349 1242635 := bstep (se 1 (by rfl) ⟨931976, by rfl⟩ : syracuseStep 1242635 = 1863953) B1863953
theorem B1242647 : Blo 826349 1242647 := bstep (se 1 (by rfl) ⟨931985, by rfl⟩ : syracuseStep 1242647 = 1863971) B1863971
theorem B1865267 : Blo 826349 1865267 := bstep (se 1 (by rfl) ⟨1398950, by rfl⟩ : syracuseStep 1865267 = 2797901) B2797901
theorem B1865303 : Blo 826349 1865303 := bstep (se 1 (by rfl) ⟨1398977, by rfl⟩ : syracuseStep 1865303 = 2797955) B2797955
theorem B1242713 : Blo 826349 1242713 := bstep (se 2 (by rfl) ⟨466017, by rfl⟩ : syracuseStep 1242713 = 932035) B932035
theorem B9434717 : Blo 826349 9434717 := bstep (se 3 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 9434717 = 3538019) B3538019
theorem B1242827 : Blo 826349 1242827 := bstep (se 1 (by rfl) ⟨932120, by rfl⟩ : syracuseStep 1242827 = 1864241) B1864241
theorem B1242839 : Blo 826349 1242839 := bstep (se 1 (by rfl) ⟨932129, by rfl⟩ : syracuseStep 1242839 = 1864259) B1864259
theorem B1865483 : Blo 826349 1865483 := bstep (se 1 (by rfl) ⟨1399112, by rfl⟩ : syracuseStep 1865483 = 2798225) B2798225
theorem B6715153 : Blo 826349 6715153 := bstep (se 2 (by rfl) ⟨2518182, by rfl⟩ : syracuseStep 6715153 = 5036365) B5036365
theorem B1570585 : Blo 826349 1570585 := bstep (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) B1177939
theorem B1242905 : Blo 826349 1242905 := bstep (se 2 (by rfl) ⟨466089, by rfl⟩ : syracuseStep 1242905 = 932179) B932179
theorem B1767233 : Blo 826349 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B1865537 : Blo 826349 1865537 := bstep (se 2 (by rfl) ⟨699576, by rfl⟩ : syracuseStep 1865537 = 1399153) B1399153
theorem B2094923 : Blo 826349 2094923 := bstep (se 1 (by rfl) ⟨1571192, by rfl⟩ : syracuseStep 2094923 = 3142385) B3142385
theorem B4257629 : Blo 826349 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B3143555 : Blo 826349 3143555 := bstep (se 1 (by rfl) ⟨2357666, by rfl⟩ : syracuseStep 3143555 = 4715333) B4715333
theorem B1243019 : Blo 826349 1243019 := bstep (se 1 (by rfl) ⟨932264, by rfl⟩ : syracuseStep 1243019 = 1864529) B1864529
theorem B3143569 : Blo 826349 3143569 := bstep (se 2 (by rfl) ⟨1178838, by rfl⟩ : syracuseStep 3143569 = 2357677) B2357677
theorem B1243031 : Blo 826349 1243031 := bstep (se 1 (by rfl) ⟨932273, by rfl⟩ : syracuseStep 1243031 = 1864547) B1864547
theorem B1243097 : Blo 826349 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B6387673 : Blo 826349 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B1865753 : Blo 826349 1865753 := bstep (se 2 (by rfl) ⟨699657, by rfl⟩ : syracuseStep 1865753 = 1399315) B1399315
theorem B1243211 : Blo 826349 1243211 := bstep (se 1 (by rfl) ⟨932408, by rfl⟩ : syracuseStep 1243211 = 1864817) B1864817
theorem B1243223 : Blo 826349 1243223 := bstep (se 1 (by rfl) ⟨932417, by rfl⟩ : syracuseStep 1243223 = 1864835) B1864835
theorem B1865843 : Blo 826349 1865843 := bstep (se 1 (by rfl) ⟨1399382, by rfl⟩ : syracuseStep 1865843 = 2798765) B2798765
theorem B1767575 : Blo 826349 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B3537047 : Blo 826349 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B6715543 : Blo 826349 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B1243289 : Blo 826349 1243289 := bstep (se 2 (by rfl) ⟨466233, by rfl⟩ : syracuseStep 1243289 = 932467) B932467
theorem B1865879 : Blo 826349 1865879 := bstep (se 1 (by rfl) ⟨1399409, by rfl⟩ : syracuseStep 1865879 = 2798819) B2798819
theorem B3143873 : Blo 826349 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B1243403 : Blo 826349 1243403 := bstep (se 1 (by rfl) ⟨932552, by rfl⟩ : syracuseStep 1243403 = 1865105) B1865105
theorem B2652439 : Blo 826349 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B1243415 : Blo 826349 1243415 := bstep (se 1 (by rfl) ⟨932561, by rfl⟩ : syracuseStep 1243415 = 1865123) B1865123
theorem B1571147 : Blo 826349 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B1866059 : Blo 826349 1866059 := bstep (se 1 (by rfl) ⟨1399544, by rfl⟩ : syracuseStep 1866059 = 2799089) B2799089
theorem B1243481 : Blo 826349 1243481 := bstep (se 2 (by rfl) ⟨466305, by rfl⟩ : syracuseStep 1243481 = 932611) B932611
theorem B1866113 : Blo 826349 1866113 := bstep (se 2 (by rfl) ⟨699792, by rfl⟩ : syracuseStep 1866113 = 1399585) B1399585
theorem B1046935 : Blo 826349 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B1178059 : Blo 826349 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B1243595 : Blo 826349 1243595 := bstep (se 1 (by rfl) ⟨932696, by rfl⟩ : syracuseStep 1243595 = 1865393) B1865393
theorem B1243607 : Blo 826349 1243607 := bstep (se 1 (by rfl) ⟨932705, by rfl⟩ : syracuseStep 1243607 = 1865411) B1865411
theorem B1571329 : Blo 826349 1571329 := bstep (se 2 (by rfl) ⟨589248, by rfl⟩ : syracuseStep 1571329 = 1178497) B1178497
theorem B1243673 : Blo 826349 1243673 := bstep (se 2 (by rfl) ⟨466377, by rfl⟩ : syracuseStep 1243673 = 932755) B932755
theorem B2357849 : Blo 826349 2357849 := bstep (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) B1768387
theorem B1866329 : Blo 826349 1866329 := bstep (se 2 (by rfl) ⟨699873, by rfl⟩ : syracuseStep 1866329 = 1399747) B1399747
theorem B1243787 : Blo 826349 1243787 := bstep (se 1 (by rfl) ⟨932840, by rfl⟩ : syracuseStep 1243787 = 1865681) B1865681
theorem B1243799 : Blo 826349 1243799 := bstep (se 1 (by rfl) ⟨932849, by rfl⟩ : syracuseStep 1243799 = 1865699) B1865699
theorem B1866419 : Blo 826349 1866419 := bstep (se 1 (by rfl) ⟨1399814, by rfl⟩ : syracuseStep 1866419 = 2799629) B2799629
theorem B1768139 : Blo 826349 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B1866455 : Blo 826349 1866455 := bstep (se 1 (by rfl) ⟨1399841, by rfl⟩ : syracuseStep 1866455 = 2799683) B2799683
theorem B1243865 : Blo 826349 1243865 := bstep (se 2 (by rfl) ⟨466449, by rfl⟩ : syracuseStep 1243865 = 932899) B932899
theorem B2095895 : Blo 826349 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B6716195 : Blo 826349 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B883531 : Blo 826349 883531 := bstep (se 1 (by rfl) ⟨662648, by rfl⟩ : syracuseStep 883531 = 1325297) B1325297
theorem B1243979 : Blo 826349 1243979 := bstep (se 1 (by rfl) ⟨932984, by rfl⟩ : syracuseStep 1243979 = 1865969) B1865969
theorem B1243991 : Blo 826349 1243991 := bstep (se 1 (by rfl) ⟨932993, by rfl⟩ : syracuseStep 1243991 = 1865987) B1865987
theorem B3144541 : Blo 826349 3144541 := bstep (se 3 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 3144541 = 1179203) B1179203
theorem B23919461 : Blo 826349 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B1866635 : Blo 826349 1866635 := bstep (se 1 (by rfl) ⟨1399976, by rfl⟩ : syracuseStep 1866635 = 2799953) B2799953
theorem B1244057 : Blo 826349 1244057 := bstep (se 2 (by rfl) ⟨466521, by rfl⟩ : syracuseStep 1244057 = 933043) B933043
theorem B1866689 : Blo 826349 1866689 := bstep (se 2 (by rfl) ⟨700008, by rfl⟩ : syracuseStep 1866689 = 1400017) B1400017
theorem B1244171 : Blo 826349 1244171 := bstep (se 1 (by rfl) ⟨933128, by rfl⟩ : syracuseStep 1244171 = 1866257) B1866257
theorem B1244183 : Blo 826349 1244183 := bstep (se 1 (by rfl) ⟨933137, by rfl⟩ : syracuseStep 1244183 = 1866275) B1866275
theorem B1702937 : Blo 826349 1702937 := bstep (se 2 (by rfl) ⟨638601, by rfl⟩ : syracuseStep 1702937 = 1277203) B1277203
theorem B1244249 : Blo 826349 1244249 := bstep (se 2 (by rfl) ⟨466593, by rfl⟩ : syracuseStep 1244249 = 933187) B933187
theorem B1866905 : Blo 826349 1866905 := bstep (se 2 (by rfl) ⟨700089, by rfl⟩ : syracuseStep 1866905 = 1400179) B1400179
theorem B1047755 : Blo 826349 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B1572043 : Blo 826349 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B1244363 : Blo 826349 1244363 := bstep (se 1 (by rfl) ⟨933272, by rfl⟩ : syracuseStep 1244363 = 1866545) B1866545
theorem B1244375 : Blo 826349 1244375 := bstep (se 1 (by rfl) ⟨933281, by rfl⟩ : syracuseStep 1244375 = 1866563) B1866563
theorem B1866995 : Blo 826349 1866995 := bstep (se 1 (by rfl) ⟨1400246, by rfl⟩ : syracuseStep 1866995 = 2800493) B2800493
theorem B1572119 : Blo 826349 1572119 := bstep (se 1 (by rfl) ⟨1179089, by rfl⟩ : syracuseStep 1572119 = 2358179) B2358179
theorem B1867031 : Blo 826349 1867031 := bstep (se 1 (by rfl) ⟨1400273, by rfl⟩ : syracuseStep 1867031 = 2800547) B2800547
theorem B1768729 : Blo 826349 1768729 := bstep (se 2 (by rfl) ⟨663273, by rfl⟩ : syracuseStep 1768729 = 1326547) B1326547
theorem B1244441 : Blo 826349 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B1244555 : Blo 826349 1244555 := bstep (se 1 (by rfl) ⟨933416, by rfl⟩ : syracuseStep 1244555 = 1866833) B1866833
theorem B1244567 : Blo 826349 1244567 := bstep (se 1 (by rfl) ⟨933425, by rfl⟩ : syracuseStep 1244567 = 1866851) B1866851
theorem B2096563 : Blo 826349 2096563 := bstep (se 1 (by rfl) ⟨1572422, by rfl⟩ : syracuseStep 2096563 = 3144845) B3144845
theorem B1867211 : Blo 826349 1867211 := bstep (se 1 (by rfl) ⟨1400408, by rfl⟩ : syracuseStep 1867211 = 2800817) B2800817
theorem B1244633 : Blo 826349 1244633 := bstep (se 2 (by rfl) ⟨466737, by rfl⟩ : syracuseStep 1244633 = 933475) B933475
theorem B1867265 : Blo 826349 1867265 := bstep (se 2 (by rfl) ⟨700224, by rfl⟩ : syracuseStep 1867265 = 1400449) B1400449
theorem B13598225 : Blo 826349 13598225 := bstep (se 2 (by rfl) ⟨5099334, by rfl⟩ : syracuseStep 13598225 = 10198669) B10198669
theorem B2096705 : Blo 826349 2096705 := bstep (se 2 (by rfl) ⟨786264, by rfl⟩ : syracuseStep 2096705 = 1572529) B1572529
theorem B1244747 : Blo 826349 1244747 := bstep (se 1 (by rfl) ⟨933560, by rfl⟩ : syracuseStep 1244747 = 1867121) B1867121
theorem B1244759 : Blo 826349 1244759 := bstep (se 1 (by rfl) ⟨933569, by rfl⟩ : syracuseStep 1244759 = 1867139) B1867139
theorem B5308055 : Blo 826349 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B1179289 : Blo 826349 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B1244825 : Blo 826349 1244825 := bstep (se 2 (by rfl) ⟨466809, by rfl⟩ : syracuseStep 1244825 = 933619) B933619
theorem B1867481 : Blo 826349 1867481 := bstep (se 2 (by rfl) ⟨700305, by rfl⟩ : syracuseStep 1867481 = 1400611) B1400611
theorem B1244939 : Blo 826349 1244939 := bstep (se 1 (by rfl) ⟨933704, by rfl⟩ : syracuseStep 1244939 = 1867409) B1867409
theorem B1244951 : Blo 826349 1244951 := bstep (se 1 (by rfl) ⟨933713, by rfl⟩ : syracuseStep 1244951 = 1867427) B1867427
theorem B1867571 : Blo 826349 1867571 := bstep (se 1 (by rfl) ⟨1400678, by rfl⟩ : syracuseStep 1867571 = 2801357) B2801357
theorem B1867607 : Blo 826349 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B1245017 : Blo 826349 1245017 := bstep (se 2 (by rfl) ⟨466881, by rfl⟩ : syracuseStep 1245017 = 933763) B933763
theorem B4194179 : Blo 826349 4194179 := bstep (se 1 (by rfl) ⟨3145634, by rfl⟩ : syracuseStep 4194179 = 6291269) B6291269
theorem B1048459 : Blo 826349 1048459 := bstep (se 1 (by rfl) ⟨786344, by rfl⟩ : syracuseStep 1048459 = 1572689) B1572689
theorem B1572787 : Blo 826349 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B1245131 : Blo 826349 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B1245143 : Blo 826349 1245143 := bstep (se 1 (by rfl) ⟨933857, by rfl⟩ : syracuseStep 1245143 = 1867715) B1867715
theorem B1245191 : Blo 826349 1245191 := bstep (se 1 (by rfl) ⟨933893, by rfl⟩ : syracuseStep 1245191 = 1867787) B1867787
theorem B2359307 : Blo 826349 2359307 := bstep (se 1 (by rfl) ⟨1769480, by rfl⟩ : syracuseStep 2359307 = 3538961) B3538961
theorem B1245227 : Blo 826349 1245227 := bstep (se 1 (by rfl) ⟨933920, by rfl⟩ : syracuseStep 1245227 = 1867841) B1867841
theorem B2097211 : Blo 826349 2097211 := bstep (se 1 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 2097211 = 3145817) B3145817
theorem B3539011 : Blo 826349 3539011 := bstep (se 1 (by rfl) ⟨2654258, by rfl⟩ : syracuseStep 3539011 = 5308517) B5308517
theorem B1245257 : Blo 826349 1245257 := bstep (se 2 (by rfl) ⟨466971, by rfl⟩ : syracuseStep 1245257 = 933943) B933943
theorem B1867895 : Blo 826349 1867895 := bstep (se 1 (by rfl) ⟨1400921, by rfl⟩ : syracuseStep 1867895 = 2801843) B2801843
theorem B1245371 : Blo 826349 1245371 := bstep (se 1 (by rfl) ⟨934028, by rfl⟩ : syracuseStep 1245371 = 1868057) B1868057
theorem B2097353 : Blo 826349 2097353 := bstep (se 2 (by rfl) ⟨786507, by rfl⟩ : syracuseStep 2097353 = 1573015) B1573015
theorem B1245431 : Blo 826349 1245431 := bstep (se 1 (by rfl) ⟨934073, by rfl⟩ : syracuseStep 1245431 = 1868147) B1868147
theorem B3145985 : Blo 826349 3145985 := bstep (se 2 (by rfl) ⟨1179744, by rfl⟩ : syracuseStep 3145985 = 2359489) B2359489
theorem B3145999 : Blo 826349 3145999 := bstep (se 1 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 3145999 = 4718999) B4718999
theorem B1245455 : Blo 826349 1245455 := bstep (se 1 (by rfl) ⟨934091, by rfl⟩ : syracuseStep 1245455 = 1868183) B1868183
theorem B1868075 : Blo 826349 1868075 := bstep (se 1 (by rfl) ⟨1401056, by rfl⟩ : syracuseStep 1868075 = 2802113) B2802113
theorem B1245497 : Blo 826349 1245497 := bstep (se 2 (by rfl) ⟨467061, by rfl⟩ : syracuseStep 1245497 = 934123) B934123
theorem B2359705 : Blo 826349 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B5046731 : Blo 826349 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B4194827 : Blo 826349 4194827 := bstep (se 1 (by rfl) ⟨3146120, by rfl⟩ : syracuseStep 4194827 = 6292241) B6292241
theorem B2097697 : Blo 826349 2097697 := bstep (se 2 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 2097697 = 1573273) B1573273
theorem B1180217 : Blo 826349 1180217 := bstep (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) B885163
theorem B1770103 : Blo 826349 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B2359955 : Blo 826349 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B4194989 : Blo 826349 4194989 := bstep (se 3 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 4194989 = 1573121) B1573121
theorem B1573577 : Blo 826349 1573577 := bstep (se 2 (by rfl) ⟨590091, by rfl⟩ : syracuseStep 1573577 = 1180183) B1180183
theorem B2654977 : Blo 826349 2654977 := bstep (se 2 (by rfl) ⟨995616, by rfl⟩ : syracuseStep 2654977 = 1991233) B1991233
theorem B4653883 : Blo 826349 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B80413667 : Blo 826349 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B2098295 : Blo 826349 2098295 := bstep (se 1 (by rfl) ⟨1573721, by rfl⟩ : syracuseStep 2098295 = 3147443) B3147443
theorem B1181071 : Blo 826349 1181071 := bstep (se 1 (by rfl) ⟨885803, by rfl⟩ : syracuseStep 1181071 = 1771607) B1771607
theorem B1574291 : Blo 826349 1574291 := bstep (se 1 (by rfl) ⟨1180718, by rfl⟩ : syracuseStep 1574291 = 2361437) B2361437
theorem B1574329 : Blo 826349 1574329 := bstep (se 2 (by rfl) ⟨590373, by rfl⟩ : syracuseStep 1574329 = 1180747) B1180747
theorem B4720139 : Blo 826349 4720139 := bstep (se 1 (by rfl) ⟨3540104, by rfl⟩ : syracuseStep 4720139 = 7080209) B7080209
theorem B3147275 : Blo 826349 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B5113367 : Blo 826349 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B2360947 : Blo 826349 2360947 := bstep (se 1 (by rfl) ⟨1770710, by rfl⟩ : syracuseStep 2360947 = 3541421) B3541421
theorem B73664369 : Blo 826349 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B9439091 : Blo 826349 9439091 := bstep (se 1 (by rfl) ⟨7079318, by rfl⟩ : syracuseStep 9439091 = 14158637) B14158637
theorem B10618775 : Blo 826349 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B1181641 : Blo 826349 1181641 := bstep (se 2 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 1181641 = 886231) B886231
theorem B5965771 : Blo 826349 5965771 := bstep (se 1 (by rfl) ⟨4474328, by rfl⟩ : syracuseStep 5965771 = 8948657) B8948657
theorem B4196609 : Blo 826349 4196609 := bstep (se 2 (by rfl) ⟨1573728, by rfl⟩ : syracuseStep 4196609 = 3147457) B3147457
theorem B2099591 : Blo 826349 2099591 := bstep (se 1 (by rfl) ⟨1574693, by rfl⟩ : syracuseStep 2099591 = 3149387) B3149387
theorem B3148217 : Blo 826349 3148217 := bstep (se 2 (by rfl) ⟨1180581, by rfl⟩ : syracuseStep 3148217 = 2361163) B2361163
theorem B2099641 : Blo 826349 2099641 := bstep (se 2 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 2099641 = 1574731) B1574731
theorem B2100239 : Blo 826349 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B4197419 : Blo 826349 4197419 := bstep (se 1 (by rfl) ⟨3148064, by rfl⟩ : syracuseStep 4197419 = 6296129) B6296129
theorem B2362553 : Blo 826349 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B1576235 : Blo 826349 1576235 := bstep (se 1 (by rfl) ⟨1182176, by rfl⟩ : syracuseStep 1576235 = 2364353) B2364353
theorem B4787545 : Blo 826349 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B2362895 : Blo 826349 2362895 := bstep (se 1 (by rfl) ⟨1772171, by rfl⟩ : syracuseStep 2362895 = 3544343) B3544343
theorem B2395663 : Blo 826349 2395663 := bstep (se 1 (by rfl) ⟨1796747, by rfl⟩ : syracuseStep 2395663 = 3593495) B3593495
theorem B17927831 : Blo 826349 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B2100937 : Blo 826349 2100937 := bstep (se 2 (by rfl) ⟨787851, by rfl⟩ : syracuseStep 2100937 = 1575703) B1575703
theorem B2789153 : Blo 826349 2789153 := bstep (se 2 (by rfl) ⟨1045932, by rfl⟩ : syracuseStep 2789153 = 2091865) B2091865
theorem B32280371 : Blo 826349 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B2101079 : Blo 826349 2101079 := bstep (se 1 (by rfl) ⟨1575809, by rfl⟩ : syracuseStep 2101079 = 3151619) B3151619
theorem B2363681 : Blo 826349 2363681 := bstep (se 2 (by rfl) ⟨886380, by rfl⟩ : syracuseStep 2363681 = 1772761) B1772761
theorem B4198715 : Blo 826349 4198715 := bstep (se 1 (by rfl) ⟨3149036, by rfl⟩ : syracuseStep 4198715 = 6298073) B6298073
theorem B2789747 : Blo 826349 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B4198877 : Blo 826349 4198877 := bstep (se 3 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 4198877 = 1574579) B1574579
theorem B4723373 : Blo 826349 4723373 := bstep (se 3 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 4723373 = 1771265) B1771265
theorem B1676065 : Blo 826349 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B4199201 : Blo 826349 4199201 := bstep (se 2 (by rfl) ⟨1574700, by rfl⟩ : syracuseStep 4199201 = 3149401) B3149401
theorem B3150859 : Blo 826349 3150859 := bstep (se 1 (by rfl) ⟨2363144, by rfl⟩ : syracuseStep 3150859 = 4726289) B4726289
theorem B3151163 : Blo 826349 3151163 := bstep (se 1 (by rfl) ⟨2363372, by rfl⟩ : syracuseStep 3151163 = 4726745) B4726745
theorem B2659769 : Blo 826349 2659769 := bstep (se 2 (by rfl) ⟨997413, by rfl⟩ : syracuseStep 2659769 = 1994827) B1994827
theorem B2233889 : Blo 826349 2233889 := bstep (se 2 (by rfl) ⟨837708, by rfl⟩ : syracuseStep 2233889 = 1675417) B1675417
theorem B5969485 : Blo 826349 5969485 := bstep (se 3 (by rfl) ⟨1119278, by rfl⟩ : syracuseStep 5969485 = 2238557) B2238557
theorem B4200173 : Blo 826349 4200173 := bstep (se 3 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 4200173 = 1575065) B1575065
theorem B4724513 : Blo 826349 4724513 := bstep (se 2 (by rfl) ⟨1771692, by rfl⟩ : syracuseStep 4724513 = 3543385) B3543385
theorem B3151649 : Blo 826349 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B1120187 : Blo 826349 1120187 := bstep (se 1 (by rfl) ⟨840140, by rfl⟩ : syracuseStep 1120187 = 1680281) B1680281
theorem B2234483 : Blo 826349 2234483 := bstep (se 1 (by rfl) ⟨1675862, by rfl⟩ : syracuseStep 2234483 = 3351725) B3351725
theorem B4200983 : Blo 826349 4200983 := bstep (se 1 (by rfl) ⟨3150737, by rfl⟩ : syracuseStep 4200983 = 6301475) B6301475
theorem B3152621 : Blo 826349 3152621 := bstep (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) B1182233
theorem B3971855 : Blo 826349 3971855 := bstep (se 1 (by rfl) ⟨2978891, by rfl⟩ : syracuseStep 3971855 = 5957783) B5957783
theorem B2792339 : Blo 826349 2792339 := bstep (se 1 (by rfl) ⟨2094254, by rfl⟩ : syracuseStep 2792339 = 4188509) B4188509
theorem B826375 : Blo 826349 826375 := bstep (se 1 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 826375 = 1239563) B1239563
theorem B826383 : Blo 826349 826383 := bstep (se 1 (by rfl) ⟨619787, by rfl⟩ : syracuseStep 826383 = 1239575) B1239575
theorem B826427 : Blo 826349 826427 := bstep (se 1 (by rfl) ⟨619820, by rfl⟩ : syracuseStep 826427 = 1239641) B1239641
theorem B826503 : Blo 826349 826503 := bstep (se 1 (by rfl) ⟨619877, by rfl⟩ : syracuseStep 826503 = 1239755) B1239755
theorem B826511 : Blo 826349 826511 := bstep (se 1 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 826511 = 1239767) B1239767
theorem B826555 : Blo 826349 826555 := bstep (se 1 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 826555 = 1239833) B1239833
theorem B826631 : Blo 826349 826631 := bstep (se 1 (by rfl) ⟨619973, by rfl⟩ : syracuseStep 826631 = 1239947) B1239947
theorem B826639 : Blo 826349 826639 := bstep (se 1 (by rfl) ⟨619979, by rfl⟩ : syracuseStep 826639 = 1239959) B1239959
theorem B2989345 : Blo 826349 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B826683 : Blo 826349 826683 := bstep (se 1 (by rfl) ⟨620012, by rfl⟩ : syracuseStep 826683 = 1240025) B1240025
theorem B826759 : Blo 826349 826759 := bstep (se 1 (by rfl) ⟨620069, by rfl⟩ : syracuseStep 826759 = 1240139) B1240139
theorem B826767 : Blo 826349 826767 := bstep (se 1 (by rfl) ⟨620075, by rfl⟩ : syracuseStep 826767 = 1240151) B1240151
theorem B826811 : Blo 826349 826811 := bstep (se 1 (by rfl) ⟨620108, by rfl⟩ : syracuseStep 826811 = 1240217) B1240217
theorem B826887 : Blo 826349 826887 := bstep (se 1 (by rfl) ⟨620165, by rfl⟩ : syracuseStep 826887 = 1240331) B1240331
theorem B826895 : Blo 826349 826895 := bstep (se 1 (by rfl) ⟨620171, by rfl⟩ : syracuseStep 826895 = 1240343) B1240343
theorem B826939 : Blo 826349 826939 := bstep (se 1 (by rfl) ⟨620204, by rfl⟩ : syracuseStep 826939 = 1240409) B1240409
theorem B827015 : Blo 826349 827015 := bstep (se 1 (by rfl) ⟨620261, by rfl⟩ : syracuseStep 827015 = 1240523) B1240523
theorem B40345229 : Blo 826349 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B827023 : Blo 826349 827023 := bstep (se 1 (by rfl) ⟨620267, by rfl⟩ : syracuseStep 827023 = 1240535) B1240535
theorem B827067 : Blo 826349 827067 := bstep (se 1 (by rfl) ⟨620300, by rfl⟩ : syracuseStep 827067 = 1240601) B1240601
theorem B8953537 : Blo 826349 8953537 := bstep (se 2 (by rfl) ⟨3357576, by rfl⟩ : syracuseStep 8953537 = 6715153) B6715153
theorem B5447425 : Blo 826349 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B827143 : Blo 826349 827143 := bstep (se 1 (by rfl) ⟨620357, by rfl⟩ : syracuseStep 827143 = 1240715) B1240715
theorem B827151 : Blo 826349 827151 := bstep (se 1 (by rfl) ⟨620363, by rfl⟩ : syracuseStep 827151 = 1240727) B1240727
theorem B1613611 : Blo 826349 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B827195 : Blo 826349 827195 := bstep (se 1 (by rfl) ⟨620396, by rfl⟩ : syracuseStep 827195 = 1240793) B1240793
theorem B827271 : Blo 826349 827271 := bstep (se 1 (by rfl) ⟨620453, by rfl⟩ : syracuseStep 827271 = 1240907) B1240907
theorem B827279 : Blo 826349 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B827323 : Blo 826349 827323 := bstep (se 1 (by rfl) ⟨620492, by rfl⟩ : syracuseStep 827323 = 1240985) B1240985
theorem B827399 : Blo 826349 827399 := bstep (se 1 (by rfl) ⟨620549, by rfl⟩ : syracuseStep 827399 = 1241099) B1241099
theorem B827407 : Blo 826349 827407 := bstep (se 1 (by rfl) ⟨620555, by rfl⟩ : syracuseStep 827407 = 1241111) B1241111
theorem B827451 : Blo 826349 827451 := bstep (se 1 (by rfl) ⟨620588, by rfl⟩ : syracuseStep 827451 = 1241177) B1241177
theorem B8953973 : Blo 826349 8953973 := bstep (se 5 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 8953973 = 839435) B839435
theorem B827527 : Blo 826349 827527 := bstep (se 1 (by rfl) ⟨620645, by rfl⟩ : syracuseStep 827527 = 1241291) B1241291
theorem B827535 : Blo 826349 827535 := bstep (se 1 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 827535 = 1241303) B1241303
theorem B827579 : Blo 826349 827579 := bstep (se 1 (by rfl) ⟨620684, by rfl⟩ : syracuseStep 827579 = 1241369) B1241369
theorem B8954057 : Blo 826349 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B827655 : Blo 826349 827655 := bstep (se 1 (by rfl) ⟨620741, by rfl⟩ : syracuseStep 827655 = 1241483) B1241483
theorem B827663 : Blo 826349 827663 := bstep (se 1 (by rfl) ⟨620747, by rfl⟩ : syracuseStep 827663 = 1241495) B1241495
theorem B2793743 : Blo 826349 2793743 := bstep (se 1 (by rfl) ⟨2095307, by rfl⟩ : syracuseStep 2793743 = 4190615) B4190615
theorem B827707 : Blo 826349 827707 := bstep (se 1 (by rfl) ⟨620780, by rfl⟩ : syracuseStep 827707 = 1241561) B1241561
theorem B827783 : Blo 826349 827783 := bstep (se 1 (by rfl) ⟨620837, by rfl⟩ : syracuseStep 827783 = 1241675) B1241675
theorem B827791 : Blo 826349 827791 := bstep (se 1 (by rfl) ⟨620843, by rfl⟩ : syracuseStep 827791 = 1241687) B1241687
theorem B827835 : Blo 826349 827835 := bstep (se 1 (by rfl) ⟨620876, by rfl⟩ : syracuseStep 827835 = 1241753) B1241753
theorem B827911 : Blo 826349 827911 := bstep (se 1 (by rfl) ⟨620933, by rfl⟩ : syracuseStep 827911 = 1241867) B1241867
theorem B3973643 : Blo 826349 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B827919 : Blo 826349 827919 := bstep (se 1 (by rfl) ⟨620939, by rfl⟩ : syracuseStep 827919 = 1241879) B1241879
theorem B3973661 : Blo 826349 3973661 := bstep (se 3 (by rfl) ⟨745061, by rfl⟩ : syracuseStep 3973661 = 1490123) B1490123
theorem B2794013 : Blo 826349 2794013 := bstep (se 3 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 2794013 = 1047755) B1047755
theorem B827963 : Blo 826349 827963 := bstep (se 1 (by rfl) ⟨620972, by rfl⟩ : syracuseStep 827963 = 1241945) B1241945
theorem B828039 : Blo 826349 828039 := bstep (se 1 (by rfl) ⟨621029, by rfl⟩ : syracuseStep 828039 = 1242059) B1242059
theorem B828047 : Blo 826349 828047 := bstep (se 1 (by rfl) ⟨621035, by rfl⟩ : syracuseStep 828047 = 1242071) B1242071
theorem B828091 : Blo 826349 828091 := bstep (se 1 (by rfl) ⟨621068, by rfl⟩ : syracuseStep 828091 = 1242137) B1242137
theorem B13083353 : Blo 826349 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B828167 : Blo 826349 828167 := bstep (se 1 (by rfl) ⟨621125, by rfl⟩ : syracuseStep 828167 = 1242251) B1242251
theorem B828175 : Blo 826349 828175 := bstep (se 1 (by rfl) ⟨621131, by rfl⟩ : syracuseStep 828175 = 1242263) B1242263
theorem B828219 : Blo 826349 828219 := bstep (se 1 (by rfl) ⟨621164, by rfl⟩ : syracuseStep 828219 = 1242329) B1242329
theorem B4793177 : Blo 826349 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B828295 : Blo 826349 828295 := bstep (se 1 (by rfl) ⟨621221, by rfl⟩ : syracuseStep 828295 = 1242443) B1242443
theorem B828303 : Blo 826349 828303 := bstep (se 1 (by rfl) ⟨621227, by rfl⟩ : syracuseStep 828303 = 1242455) B1242455
theorem B21767093 : Blo 826349 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B828347 : Blo 826349 828347 := bstep (se 1 (by rfl) ⟨621260, by rfl⟩ : syracuseStep 828347 = 1242521) B1242521
theorem B828423 : Blo 826349 828423 := bstep (se 1 (by rfl) ⟨621317, by rfl⟩ : syracuseStep 828423 = 1242635) B1242635
theorem B828431 : Blo 826349 828431 := bstep (se 1 (by rfl) ⟨621323, by rfl⟩ : syracuseStep 828431 = 1242647) B1242647
theorem B828475 : Blo 826349 828475 := bstep (se 1 (by rfl) ⟨621356, by rfl⟩ : syracuseStep 828475 = 1242713) B1242713
theorem B828551 : Blo 826349 828551 := bstep (se 1 (by rfl) ⟨621413, by rfl⟩ : syracuseStep 828551 = 1242827) B1242827
theorem B828559 : Blo 826349 828559 := bstep (se 1 (by rfl) ⟨621419, by rfl⟩ : syracuseStep 828559 = 1242839) B1242839
theorem B828603 : Blo 826349 828603 := bstep (se 1 (by rfl) ⟨621452, by rfl⟩ : syracuseStep 828603 = 1242905) B1242905
theorem B828679 : Blo 826349 828679 := bstep (se 1 (by rfl) ⟨621509, by rfl⟩ : syracuseStep 828679 = 1243019) B1243019
theorem B828687 : Blo 826349 828687 := bstep (se 1 (by rfl) ⟨621515, by rfl⟩ : syracuseStep 828687 = 1243031) B1243031
theorem B828731 : Blo 826349 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B828807 : Blo 826349 828807 := bstep (se 1 (by rfl) ⟨621605, by rfl⟩ : syracuseStep 828807 = 1243211) B1243211
theorem B828815 : Blo 826349 828815 := bstep (se 1 (by rfl) ⟨621611, by rfl⟩ : syracuseStep 828815 = 1243223) B1243223
theorem B828859 : Blo 826349 828859 := bstep (se 1 (by rfl) ⟨621644, by rfl⟩ : syracuseStep 828859 = 1243289) B1243289
theorem B828935 : Blo 826349 828935 := bstep (se 1 (by rfl) ⟨621701, by rfl⟩ : syracuseStep 828935 = 1243403) B1243403
theorem B828943 : Blo 826349 828943 := bstep (se 1 (by rfl) ⟨621707, by rfl⟩ : syracuseStep 828943 = 1243415) B1243415
theorem B828987 : Blo 826349 828987 := bstep (se 1 (by rfl) ⟨621740, by rfl⟩ : syracuseStep 828987 = 1243481) B1243481
theorem B829063 : Blo 826349 829063 := bstep (se 1 (by rfl) ⟨621797, by rfl⟩ : syracuseStep 829063 = 1243595) B1243595
theorem B829071 : Blo 826349 829071 := bstep (se 1 (by rfl) ⟨621803, by rfl⟩ : syracuseStep 829071 = 1243607) B1243607
theorem B829115 : Blo 826349 829115 := bstep (se 1 (by rfl) ⟨621836, by rfl⟩ : syracuseStep 829115 = 1243673) B1243673
theorem B829191 : Blo 826349 829191 := bstep (se 1 (by rfl) ⟨621893, by rfl⟩ : syracuseStep 829191 = 1243787) B1243787
theorem B829199 : Blo 826349 829199 := bstep (se 1 (by rfl) ⟨621899, by rfl⟩ : syracuseStep 829199 = 1243799) B1243799
theorem B829243 : Blo 826349 829243 := bstep (se 1 (by rfl) ⟨621932, by rfl⟩ : syracuseStep 829243 = 1243865) B1243865
theorem B829319 : Blo 826349 829319 := bstep (se 1 (by rfl) ⟨621989, by rfl⟩ : syracuseStep 829319 = 1243979) B1243979
theorem B829327 : Blo 826349 829327 := bstep (se 1 (by rfl) ⟨621995, by rfl⟩ : syracuseStep 829327 = 1243991) B1243991
theorem B2795417 : Blo 826349 2795417 := bstep (se 2 (by rfl) ⟨1048281, by rfl⟩ : syracuseStep 2795417 = 2096563) B2096563
theorem B1681337 : Blo 826349 1681337 := bstep (se 2 (by rfl) ⟨630501, by rfl⟩ : syracuseStep 1681337 = 1261003) B1261003
theorem B829371 : Blo 826349 829371 := bstep (se 1 (by rfl) ⟨622028, by rfl⟩ : syracuseStep 829371 = 1244057) B1244057
theorem B829447 : Blo 826349 829447 := bstep (se 1 (by rfl) ⟨622085, by rfl⟩ : syracuseStep 829447 = 1244171) B1244171
theorem B829455 : Blo 826349 829455 := bstep (se 1 (by rfl) ⟨622091, by rfl⟩ : syracuseStep 829455 = 1244183) B1244183
theorem B829499 : Blo 826349 829499 := bstep (se 1 (by rfl) ⟨622124, by rfl⟩ : syracuseStep 829499 = 1244249) B1244249
theorem B829575 : Blo 826349 829575 := bstep (se 1 (by rfl) ⟨622181, by rfl⟩ : syracuseStep 829575 = 1244363) B1244363
theorem B829583 : Blo 826349 829583 := bstep (se 1 (by rfl) ⟨622187, by rfl⟩ : syracuseStep 829583 = 1244375) B1244375
theorem B829627 : Blo 826349 829627 := bstep (se 1 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 829627 = 1244441) B1244441
theorem B829703 : Blo 826349 829703 := bstep (se 1 (by rfl) ⟨622277, by rfl⟩ : syracuseStep 829703 = 1244555) B1244555
theorem B829711 : Blo 826349 829711 := bstep (se 1 (by rfl) ⟨622283, by rfl⟩ : syracuseStep 829711 = 1244567) B1244567
theorem B829755 : Blo 826349 829755 := bstep (se 1 (by rfl) ⟨622316, by rfl⟩ : syracuseStep 829755 = 1244633) B1244633
theorem B829831 : Blo 826349 829831 := bstep (se 1 (by rfl) ⟨622373, by rfl⟩ : syracuseStep 829831 = 1244747) B1244747
theorem B829839 : Blo 826349 829839 := bstep (se 1 (by rfl) ⟨622379, by rfl⟩ : syracuseStep 829839 = 1244759) B1244759
theorem B829883 : Blo 826349 829883 := bstep (se 1 (by rfl) ⟨622412, by rfl⟩ : syracuseStep 829883 = 1244825) B1244825
theorem B6040067 : Blo 826349 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B829959 : Blo 826349 829959 := bstep (se 1 (by rfl) ⟨622469, by rfl⟩ : syracuseStep 829959 = 1244939) B1244939
theorem B829967 : Blo 826349 829967 := bstep (se 1 (by rfl) ⟨622475, by rfl⟩ : syracuseStep 829967 = 1244951) B1244951
theorem B830011 : Blo 826349 830011 := bstep (se 1 (by rfl) ⟨622508, by rfl⟩ : syracuseStep 830011 = 1245017) B1245017
theorem B2796119 : Blo 826349 2796119 := bstep (se 1 (by rfl) ⟨2097089, by rfl⟩ : syracuseStep 2796119 = 4194179) B4194179
theorem B830087 : Blo 826349 830087 := bstep (se 1 (by rfl) ⟨622565, by rfl⟩ : syracuseStep 830087 = 1245131) B1245131
theorem B830095 : Blo 826349 830095 := bstep (se 1 (by rfl) ⟨622571, by rfl⟩ : syracuseStep 830095 = 1245143) B1245143
theorem B830139 : Blo 826349 830139 := bstep (se 1 (by rfl) ⟨622604, by rfl⟩ : syracuseStep 830139 = 1245209) B1245209
theorem B830215 : Blo 826349 830215 := bstep (se 1 (by rfl) ⟨622661, by rfl⟩ : syracuseStep 830215 = 1245323) B1245323
theorem B830223 : Blo 826349 830223 := bstep (se 1 (by rfl) ⟨622667, by rfl⟩ : syracuseStep 830223 = 1245335) B1245335
theorem B830267 : Blo 826349 830267 := bstep (se 1 (by rfl) ⟨622700, by rfl⟩ : syracuseStep 830267 = 1245401) B1245401
theorem B830343 : Blo 826349 830343 := bstep (se 1 (by rfl) ⟨622757, by rfl⟩ : syracuseStep 830343 = 1245515) B1245515
theorem B3353491 : Blo 826349 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B3976121 : Blo 826349 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B2796605 : Blo 826349 2796605 := bstep (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) B1048727
theorem B1256635 : Blo 826349 1256635 := bstep (se 1 (by rfl) ⟨942476, by rfl⟩ : syracuseStep 1256635 = 1884953) B1884953
theorem B248491405 : Blo 826349 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B7089707 : Blo 826349 7089707 := bstep (se 1 (by rfl) ⟨5317280, by rfl⟩ : syracuseStep 7089707 = 10634561) B10634561
theorem B32681573 : Blo 826349 32681573 := bstep (se 4 (by rfl) ⟨3063897, by rfl⟩ : syracuseStep 32681573 = 6127795) B6127795
theorem B930055 : Blo 826349 930055 := bstep (se 1 (by rfl) ⟨697541, by rfl⟩ : syracuseStep 930055 = 1395083) B1395083
theorem B2798009 : Blo 826349 2798009 := bstep (se 2 (by rfl) ⟨1049253, by rfl⟩ : syracuseStep 2798009 = 2098507) B2098507
theorem B930235 : Blo 826349 930235 := bstep (se 1 (by rfl) ⟨697676, by rfl⟩ : syracuseStep 930235 = 1395353) B1395353
theorem B15938309 : Blo 826349 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B7189337 : Blo 826349 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B3978119 : Blo 826349 3978119 := bstep (se 1 (by rfl) ⟨2983589, by rfl⟩ : syracuseStep 3978119 = 5967179) B5967179
theorem B930703 : Blo 826349 930703 := bstep (se 1 (by rfl) ⟨698027, by rfl⟩ : syracuseStep 930703 = 1396055) B1396055
theorem B2798603 : Blo 826349 2798603 := bstep (se 1 (by rfl) ⟨2098952, by rfl⟩ : syracuseStep 2798603 = 4197905) B4197905
theorem B2798711 : Blo 826349 2798711 := bstep (se 1 (by rfl) ⟨2099033, by rfl⟩ : syracuseStep 2798711 = 4198067) B4198067
theorem B931207 : Blo 826349 931207 := bstep (se 1 (by rfl) ⟨698405, by rfl⟩ : syracuseStep 931207 = 1396811) B1396811
theorem B7943629 : Blo 826349 7943629 := bstep (se 3 (by rfl) ⟨1489430, by rfl⟩ : syracuseStep 7943629 = 2978861) B2978861
theorem B931387 : Blo 826349 931387 := bstep (se 1 (by rfl) ⟨698540, by rfl⟩ : syracuseStep 931387 = 1397081) B1397081
theorem B9549413 : Blo 826349 9549413 := bstep (se 4 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 9549413 = 1790515) B1790515
theorem B1619603 : Blo 826349 1619603 := bstep (se 1 (by rfl) ⟨1214702, by rfl⟩ : syracuseStep 1619603 = 2429405) B2429405
theorem B2799305 : Blo 826349 2799305 := bstep (se 2 (by rfl) ⟨1049739, by rfl⟩ : syracuseStep 2799305 = 2099479) B2099479
theorem B997255 : Blo 826349 997255 := bstep (se 1 (by rfl) ⟨747941, by rfl⟩ : syracuseStep 997255 = 1495883) B1495883
theorem B931855 : Blo 826349 931855 := bstep (se 1 (by rfl) ⟨698891, by rfl⟩ : syracuseStep 931855 = 1397783) B1397783
theorem B12728593 : Blo 826349 12728593 := bstep (se 2 (by rfl) ⟨4773222, by rfl⟩ : syracuseStep 12728593 = 9546445) B9546445
theorem B2800007 : Blo 826349 2800007 := bstep (se 1 (by rfl) ⟨2100005, by rfl⟩ : syracuseStep 2800007 = 4200011) B4200011
theorem B3193235 : Blo 826349 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B1259963 : Blo 826349 1259963 := bstep (se 1 (by rfl) ⟨944972, by rfl⟩ : syracuseStep 1259963 = 1889945) B1889945
theorem B932359 : Blo 826349 932359 := bstep (se 1 (by rfl) ⟨699269, by rfl⟩ : syracuseStep 932359 = 1398539) B1398539
theorem B932539 : Blo 826349 932539 := bstep (se 1 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 932539 = 1398809) B1398809
theorem B15940313 : Blo 826349 15940313 := bstep (se 2 (by rfl) ⟨5977617, by rfl⟩ : syracuseStep 15940313 = 11955235) B11955235
theorem B10631897 : Blo 826349 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B2800385 : Blo 826349 2800385 := bstep (se 2 (by rfl) ⟨1050144, by rfl⟩ : syracuseStep 2800385 = 2100289) B2100289
theorem B2243339 : Blo 826349 2243339 := bstep (se 1 (by rfl) ⟨1682504, by rfl⟩ : syracuseStep 2243339 = 3365009) B3365009
theorem B5028875 : Blo 826349 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B933007 : Blo 826349 933007 := bstep (se 1 (by rfl) ⟨699755, by rfl⟩ : syracuseStep 933007 = 1399511) B1399511
theorem B6372553 : Blo 826349 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B3783917 : Blo 826349 3783917 := bstep (se 3 (by rfl) ⟨709484, by rfl⟩ : syracuseStep 3783917 = 1418969) B1418969
theorem B4242689 : Blo 826349 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B2801195 : Blo 826349 2801195 := bstep (se 1 (by rfl) ⟨2100896, by rfl⟩ : syracuseStep 2801195 = 4201793) B4201793
theorem B933511 : Blo 826349 933511 := bstep (se 1 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 933511 = 1400267) B1400267
theorem B933691 : Blo 826349 933691 := bstep (se 1 (by rfl) ⟨700268, by rfl⟩ : syracuseStep 933691 = 1400537) B1400537
theorem B2244439 : Blo 826349 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B6045529 : Blo 826349 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B1917047 : Blo 826349 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B4473463 : Blo 826349 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B1262267 : Blo 826349 1262267 := bstep (se 1 (by rfl) ⟨946700, by rfl⟩ : syracuseStep 1262267 = 1893401) B1893401
theorem B1327931 : Blo 826349 1327931 := bstep (se 1 (by rfl) ⟨995948, by rfl⟩ : syracuseStep 1327931 = 1991897) B1991897
theorem B1197227 : Blo 826349 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B32261645 : Blo 826349 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B5031695 : Blo 826349 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B4474739 : Blo 826349 4474739 := bstep (se 1 (by rfl) ⟨3356054, by rfl⟩ : syracuseStep 4474739 = 6712109) B6712109
theorem B1394617 : Blo 826349 1394617 := bstep (se 2 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 1394617 = 1045963) B1045963
theorem B64702637 : Blo 826349 64702637 := bstep (se 3 (by rfl) ⟨12131744, by rfl⟩ : syracuseStep 64702637 = 24263489) B24263489
theorem B4475195 : Blo 826349 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B16107923 : Blo 826349 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B1329679 : Blo 826349 1329679 := bstep (se 1 (by rfl) ⟨997259, by rfl⟩ : syracuseStep 1329679 = 1994519) B1994519
theorem B6277661 : Blo 826349 6277661 := bstep (se 3 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 6277661 = 2354123) B2354123
theorem B1395319 : Blo 826349 1395319 := bstep (se 1 (by rfl) ⟨1046489, by rfl⟩ : syracuseStep 1395319 = 2092979) B2092979
theorem B1395515 : Blo 826349 1395515 := bstep (se 1 (by rfl) ⟨1046636, by rfl⟩ : syracuseStep 1395515 = 2093273) B2093273
theorem B9456587 : Blo 826349 9456587 := bstep (se 1 (by rfl) ⟨7092440, by rfl⟩ : syracuseStep 9456587 = 14184881) B14184881
theorem B3984349 : Blo 826349 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B1395913 : Blo 826349 1395913 := bstep (se 2 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 1395913 = 1046935) B1046935
theorem B2018849 : Blo 826349 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B5983787 : Blo 826349 5983787 := bstep (se 1 (by rfl) ⟨4487840, by rfl⟩ : syracuseStep 5983787 = 8975681) B8975681
theorem B1396615 : Blo 826349 1396615 := bstep (se 1 (by rfl) ⟨1047461, by rfl⟩ : syracuseStep 1396615 = 2094923) B2094923
theorem B2838419 : Blo 826349 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B4706333 : Blo 826349 4706333 := bstep (se 3 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 4706333 = 1764875) B1764875
theorem B1397263 : Blo 826349 1397263 := bstep (se 1 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 1397263 = 2095895) B2095895
theorem B4477463 : Blo 826349 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B15946307 : Blo 826349 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B1135291 : Blo 826349 1135291 := bstep (se 1 (by rfl) ⟨851468, by rfl⟩ : syracuseStep 1135291 = 1702937) B1702937
theorem B4707017 : Blo 826349 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B1987361 : Blo 826349 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B9065483 : Blo 826349 9065483 := bstep (se 1 (by rfl) ⟨6799112, by rfl⟩ : syracuseStep 9065483 = 13598225) B13598225
theorem B1397803 : Blo 826349 1397803 := bstep (se 1 (by rfl) ⟨1048352, by rfl⟩ : syracuseStep 1397803 = 2096705) B2096705
theorem B1397945 : Blo 826349 1397945 := bstep (se 2 (by rfl) ⟨524229, by rfl⟩ : syracuseStep 1397945 = 1048459) B1048459
theorem B37344797 : Blo 826349 37344797 := bstep (se 3 (by rfl) ⟨7002149, by rfl⟩ : syracuseStep 37344797 = 14004299) B14004299
theorem B10639025 : Blo 826349 10639025 := bstep (se 2 (by rfl) ⟨3989634, by rfl⟩ : syracuseStep 10639025 = 7979269) B7979269
theorem B841487 : Blo 826349 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B23844725 : Blo 826349 23844725 := bstep (se 5 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 23844725 = 2235443) B2235443
theorem B1398647 : Blo 826349 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B17946521 : Blo 826349 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B2513015 : Blo 826349 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B1399099 : Blo 826349 1399099 := bstep (se 1 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 1399099 = 2098649) B2098649
theorem B1988983 : Blo 826349 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B4708793 : Blo 826349 4708793 := bstep (se 2 (by rfl) ⟨1765797, by rfl⟩ : syracuseStep 4708793 = 3531595) B3531595
theorem B9066937 : Blo 826349 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B1399241 : Blo 826349 1399241 := bstep (se 2 (by rfl) ⟨524715, by rfl⟩ : syracuseStep 1399241 = 1049431) B1049431
theorem B6282035 : Blo 826349 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B5299033 : Blo 826349 5299033 := bstep (se 2 (by rfl) ⟨1987137, by rfl⟩ : syracuseStep 5299033 = 3974275) B3974275
theorem B1596449 : Blo 826349 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B1399943 : Blo 826349 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B8969453 : Blo 826349 8969453 := bstep (se 3 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 8969453 = 3363545) B3363545
theorem B1990003 : Blo 826349 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B3988883 : Blo 826349 3988883 := bstep (se 1 (by rfl) ⟨2991662, by rfl⟩ : syracuseStep 3988883 = 5983325) B5983325
theorem B48455171 : Blo 826349 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B1400591 : Blo 826349 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B7069477 : Blo 826349 7069477 := bstep (se 4 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 7069477 = 1325527) B1325527
theorem B1007759 : Blo 826349 1007759 := bstep (se 1 (by rfl) ⟨755819, by rfl⟩ : syracuseStep 1007759 = 1511639) B1511639
theorem B3137737 : Blo 826349 3137737 := bstep (se 2 (by rfl) ⟨1176651, by rfl⟩ : syracuseStep 3137737 = 2353303) B2353303
theorem B1401131 : Blo 826349 1401131 := bstep (se 1 (by rfl) ⟨1050848, by rfl⟩ : syracuseStep 1401131 = 2101697) B2101697
theorem B4710707 : Blo 826349 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B1859975 : Blo 826349 1859975 := bstep (se 1 (by rfl) ⟨1394981, by rfl⟩ : syracuseStep 1859975 = 2789963) B2789963
theorem B1860155 : Blo 826349 1860155 := bstep (se 1 (by rfl) ⟨1395116, by rfl⟩ : syracuseStep 1860155 = 2790233) B2790233
theorem B7955009 : Blo 826349 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B6709837 : Blo 826349 6709837 := bstep (se 3 (by rfl) ⟨1258094, by rfl⟩ : syracuseStep 6709837 = 2516189) B2516189
theorem B1860281 : Blo 826349 1860281 := bstep (se 2 (by rfl) ⟨697605, by rfl⟩ : syracuseStep 1860281 = 1395211) B1395211
theorem B943111 : Blo 826349 943111 := bstep (se 1 (by rfl) ⟨707333, by rfl⟩ : syracuseStep 943111 = 1414667) B1414667
theorem B1860623 : Blo 826349 1860623 := bstep (se 1 (by rfl) ⟨1395467, by rfl⟩ : syracuseStep 1860623 = 2790935) B2790935
theorem B1860641 : Blo 826349 1860641 := bstep (se 2 (by rfl) ⟨697740, by rfl⟩ : syracuseStep 1860641 = 1395481) B1395481
theorem B1893419 : Blo 826349 1893419 := bstep (se 1 (by rfl) ⟨1420064, by rfl⟩ : syracuseStep 1893419 = 2840129) B2840129
theorem B11920517 : Blo 826349 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B15099169 : Blo 826349 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B1860983 : Blo 826349 1860983 := bstep (se 1 (by rfl) ⟨1395737, by rfl⟩ : syracuseStep 1860983 = 2791475) B2791475
theorem B4187537 : Blo 826349 4187537 := bstep (se 2 (by rfl) ⟨1570326, by rfl⟩ : syracuseStep 4187537 = 3140653) B3140653
theorem B1861163 : Blo 826349 1861163 := bstep (se 1 (by rfl) ⟨1395872, by rfl⟩ : syracuseStep 1861163 = 2791745) B2791745
theorem B1992251 : Blo 826349 1992251 := bstep (se 1 (by rfl) ⟨1494188, by rfl⟩ : syracuseStep 1992251 = 2988377) B2988377
theorem B4712165 : Blo 826349 4712165 := bstep (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) B883531
theorem B7071461 : Blo 826349 7071461 := bstep (se 4 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 7071461 = 1325899) B1325899
theorem B5957491 : Blo 826349 5957491 := bstep (se 1 (by rfl) ⟨4468118, by rfl⟩ : syracuseStep 5957491 = 8936237) B8936237
theorem B1861523 : Blo 826349 1861523 := bstep (se 1 (by rfl) ⟨1396142, by rfl⟩ : syracuseStep 1861523 = 2792285) B2792285
theorem B1861577 : Blo 826349 1861577 := bstep (se 2 (by rfl) ⟨698091, by rfl⟩ : syracuseStep 1861577 = 1396183) B1396183
theorem B4483343 : Blo 826349 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B3139955 : Blo 826349 3139955 := bstep (se 1 (by rfl) ⟨2354966, by rfl⟩ : syracuseStep 3139955 = 4709933) B4709933
theorem B1993079 : Blo 826349 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B4712849 : Blo 826349 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B6449629 : Blo 826349 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B1239611 : Blo 826349 1239611 := bstep (se 1 (by rfl) ⟨929708, by rfl⟩ : syracuseStep 1239611 = 1859417) B1859417
theorem B1239671 : Blo 826349 1239671 := bstep (se 1 (by rfl) ⟨929753, by rfl⟩ : syracuseStep 1239671 = 1859507) B1859507
theorem B1862279 : Blo 826349 1862279 := bstep (se 1 (by rfl) ⟨1396709, by rfl⟩ : syracuseStep 1862279 = 2793419) B2793419
theorem B1239695 : Blo 826349 1239695 := bstep (se 1 (by rfl) ⟨929771, by rfl⟩ : syracuseStep 1239695 = 1859543) B1859543
theorem B1239737 : Blo 826349 1239737 := bstep (se 2 (by rfl) ⟨464901, by rfl⟩ : syracuseStep 1239737 = 929803) B929803
theorem B1239815 : Blo 826349 1239815 := bstep (se 1 (by rfl) ⟨929861, by rfl⟩ : syracuseStep 1239815 = 1859723) B1859723
theorem B2353931 : Blo 826349 2353931 := bstep (se 1 (by rfl) ⟨1765448, by rfl⟩ : syracuseStep 2353931 = 3530897) B3530897
theorem B1239851 : Blo 826349 1239851 := bstep (se 1 (by rfl) ⟨929888, by rfl⟩ : syracuseStep 1239851 = 1859777) B1859777
theorem B1862459 : Blo 826349 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B1239881 : Blo 826349 1239881 := bstep (se 2 (by rfl) ⟨464955, by rfl⟩ : syracuseStep 1239881 = 929911) B929911
theorem B1862585 : Blo 826349 1862585 := bstep (se 2 (by rfl) ⟨698469, by rfl⟩ : syracuseStep 1862585 = 1396939) B1396939
theorem B1239995 : Blo 826349 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B2091977 : Blo 826349 2091977 := bstep (se 2 (by rfl) ⟨784491, by rfl⟩ : syracuseStep 2091977 = 1568983) B1568983
theorem B1993673 : Blo 826349 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B1240055 : Blo 826349 1240055 := bstep (se 1 (by rfl) ⟨930041, by rfl⟩ : syracuseStep 1240055 = 1860083) B1860083
theorem B1240079 : Blo 826349 1240079 := bstep (se 1 (by rfl) ⟨930059, by rfl⟩ : syracuseStep 1240079 = 1860119) B1860119
theorem B1240121 : Blo 826349 1240121 := bstep (se 2 (by rfl) ⟨465045, by rfl⟩ : syracuseStep 1240121 = 930091) B930091
theorem B1240199 : Blo 826349 1240199 := bstep (se 1 (by rfl) ⟨930149, by rfl⟩ : syracuseStep 1240199 = 1860299) B1860299
theorem B1240235 : Blo 826349 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B1240265 : Blo 826349 1240265 := bstep (se 2 (by rfl) ⟨465099, by rfl⟩ : syracuseStep 1240265 = 930199) B930199
theorem B1862927 : Blo 826349 1862927 := bstep (se 1 (by rfl) ⟨1397195, by rfl⟩ : syracuseStep 1862927 = 2794391) B2794391
theorem B1862945 : Blo 826349 1862945 := bstep (se 2 (by rfl) ⟨698604, by rfl⟩ : syracuseStep 1862945 = 1397209) B1397209
theorem B2092331 : Blo 826349 2092331 := bstep (se 1 (by rfl) ⟨1569248, by rfl⟩ : syracuseStep 2092331 = 3138497) B3138497
theorem B1240379 : Blo 826349 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B1240439 : Blo 826349 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B1240463 : Blo 826349 1240463 := bstep (se 1 (by rfl) ⟨930347, by rfl⟩ : syracuseStep 1240463 = 1860695) B1860695
theorem B2354579 : Blo 826349 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B4713875 : Blo 826349 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B1240505 : Blo 826349 1240505 := bstep (se 2 (by rfl) ⟨465189, by rfl⟩ : syracuseStep 1240505 = 930379) B930379
theorem B4189643 : Blo 826349 4189643 := bstep (se 1 (by rfl) ⟨3142232, by rfl⟩ : syracuseStep 4189643 = 6284465) B6284465
theorem B1240583 : Blo 826349 1240583 := bstep (se 1 (by rfl) ⟨930437, by rfl⟩ : syracuseStep 1240583 = 1860875) B1860875
theorem B1240619 : Blo 826349 1240619 := bstep (se 1 (by rfl) ⟨930464, by rfl⟩ : syracuseStep 1240619 = 1860929) B1860929
theorem B7958083 : Blo 826349 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B1240649 : Blo 826349 1240649 := bstep (se 2 (by rfl) ⟨465243, by rfl⟩ : syracuseStep 1240649 = 930487) B930487
theorem B2354807 : Blo 826349 2354807 := bstep (se 1 (by rfl) ⟨1766105, by rfl⟩ : syracuseStep 2354807 = 3532211) B3532211
theorem B1863287 : Blo 826349 1863287 := bstep (se 1 (by rfl) ⟨1397465, by rfl⟩ : syracuseStep 1863287 = 2794931) B2794931
theorem B1240763 : Blo 826349 1240763 := bstep (se 1 (by rfl) ⟨930572, by rfl⟩ : syracuseStep 1240763 = 1861145) B1861145
theorem B1240823 : Blo 826349 1240823 := bstep (se 1 (by rfl) ⟨930617, by rfl⟩ : syracuseStep 1240823 = 1861235) B1861235
theorem B1240847 : Blo 826349 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B4189967 : Blo 826349 4189967 := bstep (se 1 (by rfl) ⟨3142475, by rfl⟩ : syracuseStep 4189967 = 6284951) B6284951
theorem B1863467 : Blo 826349 1863467 := bstep (se 1 (by rfl) ⟨1397600, by rfl⟩ : syracuseStep 1863467 = 2795201) B2795201
theorem B1994539 : Blo 826349 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B1240889 : Blo 826349 1240889 := bstep (se 2 (by rfl) ⟨465333, by rfl⟩ : syracuseStep 1240889 = 930667) B930667
theorem B1240967 : Blo 826349 1240967 := bstep (se 1 (by rfl) ⟨930725, by rfl⟩ : syracuseStep 1240967 = 1861451) B1861451
theorem B1241003 : Blo 826349 1241003 := bstep (se 1 (by rfl) ⟨930752, by rfl⟩ : syracuseStep 1241003 = 1861505) B1861505
theorem B1241033 : Blo 826349 1241033 := bstep (se 2 (by rfl) ⟨465387, by rfl⟩ : syracuseStep 1241033 = 930775) B930775
theorem B1568801 : Blo 826349 1568801 := bstep (se 2 (by rfl) ⟨588300, by rfl⟩ : syracuseStep 1568801 = 1176601) B1176601
theorem B2125867 : Blo 826349 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B10612781 : Blo 826349 10612781 := bstep (se 3 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 10612781 = 3979793) B3979793
theorem B1241147 : Blo 826349 1241147 := bstep (se 1 (by rfl) ⟨930860, by rfl⟩ : syracuseStep 1241147 = 1861721) B1861721
theorem B1241207 : Blo 826349 1241207 := bstep (se 1 (by rfl) ⟨930905, by rfl⟩ : syracuseStep 1241207 = 1861811) B1861811
theorem B1241231 : Blo 826349 1241231 := bstep (se 1 (by rfl) ⟨930923, by rfl⟩ : syracuseStep 1241231 = 1861847) B1861847
theorem B1863827 : Blo 826349 1863827 := bstep (se 1 (by rfl) ⟨1397870, by rfl⟩ : syracuseStep 1863827 = 2795741) B2795741
theorem B4485293 : Blo 826349 4485293 := bstep (se 3 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 4485293 = 1681985) B1681985
theorem B1241273 : Blo 826349 1241273 := bstep (se 2 (by rfl) ⟨465477, by rfl⟩ : syracuseStep 1241273 = 930955) B930955
theorem B1863881 : Blo 826349 1863881 := bstep (se 2 (by rfl) ⟨698955, by rfl⟩ : syracuseStep 1863881 = 1397911) B1397911
theorem B1241351 : Blo 826349 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B2093323 : Blo 826349 2093323 := bstep (se 1 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 2093323 = 3139985) B3139985
theorem B1241387 : Blo 826349 1241387 := bstep (se 1 (by rfl) ⟨931040, by rfl⟩ : syracuseStep 1241387 = 1862081) B1862081
theorem B1241417 : Blo 826349 1241417 := bstep (se 2 (by rfl) ⟨465531, by rfl⟩ : syracuseStep 1241417 = 931063) B931063
theorem B4780433 : Blo 826349 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B2093465 : Blo 826349 2093465 := bstep (se 2 (by rfl) ⟨785049, by rfl⟩ : syracuseStep 2093465 = 1570099) B1570099
theorem B1241531 : Blo 826349 1241531 := bstep (se 1 (by rfl) ⟨931148, by rfl⟩ : syracuseStep 1241531 = 1862297) B1862297
theorem B3142097 : Blo 826349 3142097 := bstep (se 2 (by rfl) ⟨1178286, by rfl⟩ : syracuseStep 3142097 = 2356573) B2356573
theorem B1241591 : Blo 826349 1241591 := bstep (se 1 (by rfl) ⟨931193, by rfl⟩ : syracuseStep 1241591 = 1862387) B1862387
theorem B1241615 : Blo 826349 1241615 := bstep (se 1 (by rfl) ⟨931211, by rfl⟩ : syracuseStep 1241615 = 1862423) B1862423
theorem B1241657 : Blo 826349 1241657 := bstep (se 2 (by rfl) ⟨465621, by rfl⟩ : syracuseStep 1241657 = 931243) B931243
theorem B2093627 : Blo 826349 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B1241735 : Blo 826349 1241735 := bstep (se 1 (by rfl) ⟨931301, by rfl⟩ : syracuseStep 1241735 = 1862603) B1862603
theorem B1077895 : Blo 826349 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B1241771 : Blo 826349 1241771 := bstep (se 1 (by rfl) ⟨931328, by rfl⟩ : syracuseStep 1241771 = 1862657) B1862657
theorem B31847093 : Blo 826349 31847093 := bstep (se 5 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 31847093 = 2985665) B2985665
theorem B1241801 : Blo 826349 1241801 := bstep (se 2 (by rfl) ⟨465675, by rfl⟩ : syracuseStep 1241801 = 931351) B931351
theorem B3142415 : Blo 826349 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B1241915 : Blo 826349 1241915 := bstep (se 1 (by rfl) ⟨931436, by rfl⟩ : syracuseStep 1241915 = 1862873) B1862873
theorem B1241975 : Blo 826349 1241975 := bstep (se 1 (by rfl) ⟨931481, by rfl⟩ : syracuseStep 1241975 = 1862963) B1862963
theorem B1864583 : Blo 826349 1864583 := bstep (se 1 (by rfl) ⟨1398437, by rfl⟩ : syracuseStep 1864583 = 2796875) B2796875
theorem B1241999 : Blo 826349 1241999 := bstep (se 1 (by rfl) ⟨931499, by rfl⟩ : syracuseStep 1241999 = 1862999) B1862999
theorem B2093971 : Blo 826349 2093971 := bstep (se 1 (by rfl) ⟨1570478, by rfl⟩ : syracuseStep 2093971 = 3140957) B3140957
theorem B1242041 : Blo 826349 1242041 := bstep (se 2 (by rfl) ⟨465765, by rfl⟩ : syracuseStep 1242041 = 931531) B931531
theorem B1242119 : Blo 826349 1242119 := bstep (se 1 (by rfl) ⟨931589, by rfl⟩ : syracuseStep 1242119 = 1863179) B1863179
theorem B2094113 : Blo 826349 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B1242155 : Blo 826349 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B1864763 : Blo 826349 1864763 := bstep (se 1 (by rfl) ⟨1398572, by rfl⟩ : syracuseStep 1864763 = 2797145) B2797145
theorem B1242185 : Blo 826349 1242185 := bstep (se 2 (by rfl) ⟨465819, by rfl⟩ : syracuseStep 1242185 = 931639) B931639
theorem B1864889 : Blo 826349 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B1242299 : Blo 826349 1242299 := bstep (se 1 (by rfl) ⟨931724, by rfl⟩ : syracuseStep 1242299 = 1863449) B1863449
theorem B4191425 : Blo 826349 4191425 := bstep (se 2 (by rfl) ⟨1571784, by rfl⟩ : syracuseStep 4191425 = 3143569) B3143569
theorem B1242359 : Blo 826349 1242359 := bstep (se 1 (by rfl) ⟨931769, by rfl⟩ : syracuseStep 1242359 = 1863539) B1863539
theorem B1242383 : Blo 826349 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B8516897 : Blo 826349 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1242425 : Blo 826349 1242425 := bstep (se 2 (by rfl) ⟨465909, by rfl⟩ : syracuseStep 1242425 = 931819) B931819
theorem B3536243 : Blo 826349 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1242503 : Blo 826349 1242503 := bstep (se 1 (by rfl) ⟨931877, by rfl⟩ : syracuseStep 1242503 = 1863755) B1863755
theorem B1242539 : Blo 826349 1242539 := bstep (se 1 (by rfl) ⟨931904, by rfl⟩ : syracuseStep 1242539 = 1863809) B1863809
theorem B1242569 : Blo 826349 1242569 := bstep (se 2 (by rfl) ⟨465963, by rfl⟩ : syracuseStep 1242569 = 931927) B931927
theorem B1865231 : Blo 826349 1865231 := bstep (se 1 (by rfl) ⟨1398923, by rfl⟩ : syracuseStep 1865231 = 2797847) B2797847
theorem B1865249 : Blo 826349 1865249 := bstep (se 2 (by rfl) ⟨699468, by rfl⟩ : syracuseStep 1865249 = 1398937) B1398937
theorem B1242683 : Blo 826349 1242683 := bstep (se 1 (by rfl) ⟨932012, by rfl⟩ : syracuseStep 1242683 = 1864025) B1864025
theorem B1046135 : Blo 826349 1046135 := bstep (se 1 (by rfl) ⟨784601, by rfl⟩ : syracuseStep 1046135 = 1569203) B1569203
theorem B1242743 : Blo 826349 1242743 := bstep (se 1 (by rfl) ⟨932057, by rfl⟩ : syracuseStep 1242743 = 1864115) B1864115
theorem B1242767 : Blo 826349 1242767 := bstep (se 1 (by rfl) ⟨932075, by rfl⟩ : syracuseStep 1242767 = 1864151) B1864151
theorem B1242809 : Blo 826349 1242809 := bstep (se 2 (by rfl) ⟨466053, by rfl⟩ : syracuseStep 1242809 = 932107) B932107
theorem B3536585 : Blo 826349 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B1242887 : Blo 826349 1242887 := bstep (se 1 (by rfl) ⟨932165, by rfl⟩ : syracuseStep 1242887 = 1864331) B1864331
theorem B1046287 : Blo 826349 1046287 := bstep (se 1 (by rfl) ⟨784715, by rfl⟩ : syracuseStep 1046287 = 1569431) B1569431
theorem B1242923 : Blo 826349 1242923 := bstep (se 1 (by rfl) ⟨932192, by rfl⟩ : syracuseStep 1242923 = 1864385) B1864385
theorem B1242953 : Blo 826349 1242953 := bstep (se 2 (by rfl) ⟨466107, by rfl⟩ : syracuseStep 1242953 = 932215) B932215
theorem B1865591 : Blo 826349 1865591 := bstep (se 1 (by rfl) ⟨1399193, by rfl⟩ : syracuseStep 1865591 = 2798387) B2798387
theorem B1570745 : Blo 826349 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B1046459 : Blo 826349 1046459 := bstep (se 1 (by rfl) ⟨784844, by rfl⟩ : syracuseStep 1046459 = 1569689) B1569689
theorem B1243067 : Blo 826349 1243067 := bstep (se 1 (by rfl) ⟨932300, by rfl⟩ : syracuseStep 1243067 = 1864601) B1864601
theorem B1243127 : Blo 826349 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B2095105 : Blo 826349 2095105 := bstep (se 2 (by rfl) ⟨785664, by rfl⟩ : syracuseStep 2095105 = 1571329) B1571329
theorem B4782091 : Blo 826349 4782091 := bstep (se 1 (by rfl) ⟨3586568, by rfl⟩ : syracuseStep 4782091 = 7173137) B7173137
theorem B1243151 : Blo 826349 1243151 := bstep (se 1 (by rfl) ⟨932363, by rfl⟩ : syracuseStep 1243151 = 1864727) B1864727
theorem B1865771 : Blo 826349 1865771 := bstep (se 1 (by rfl) ⟨1399328, by rfl⟩ : syracuseStep 1865771 = 2798657) B2798657
theorem B1243193 : Blo 826349 1243193 := bstep (se 2 (by rfl) ⟨466197, by rfl⟩ : syracuseStep 1243193 = 932395) B932395
theorem B1243271 : Blo 826349 1243271 := bstep (se 1 (by rfl) ⟨932453, by rfl⟩ : syracuseStep 1243271 = 1864907) B1864907
theorem B1243307 : Blo 826349 1243307 := bstep (se 1 (by rfl) ⟨932480, by rfl⟩ : syracuseStep 1243307 = 1864961) B1864961
theorem B13433033 : Blo 826349 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B1243337 : Blo 826349 1243337 := bstep (se 2 (by rfl) ⟨466251, by rfl⟩ : syracuseStep 1243337 = 932503) B932503
theorem B16152817 : Blo 826349 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1243451 : Blo 826349 1243451 := bstep (se 1 (by rfl) ⟨932588, by rfl⟩ : syracuseStep 1243451 = 1865177) B1865177
theorem B1243511 : Blo 826349 1243511 := bstep (se 1 (by rfl) ⟨932633, by rfl⟩ : syracuseStep 1243511 = 1865267) B1865267
theorem B1243535 : Blo 826349 1243535 := bstep (se 1 (by rfl) ⟨932651, by rfl⟩ : syracuseStep 1243535 = 1865303) B1865303
theorem B6289811 : Blo 826349 6289811 := bstep (se 1 (by rfl) ⟨4717358, by rfl⟩ : syracuseStep 6289811 = 9434717) B9434717
theorem B1866131 : Blo 826349 1866131 := bstep (se 1 (by rfl) ⟨1399598, by rfl⟩ : syracuseStep 1866131 = 2799197) B2799197
theorem B1243577 : Blo 826349 1243577 := bstep (se 2 (by rfl) ⟨466341, by rfl⟩ : syracuseStep 1243577 = 932683) B932683
theorem B1866185 : Blo 826349 1866185 := bstep (se 2 (by rfl) ⟨699819, by rfl⟩ : syracuseStep 1866185 = 1399639) B1399639
theorem B4192721 : Blo 826349 4192721 := bstep (se 2 (by rfl) ⟨1572270, by rfl⟩ : syracuseStep 4192721 = 3144541) B3144541
theorem B1243655 : Blo 826349 1243655 := bstep (se 1 (by rfl) ⟨932741, by rfl⟩ : syracuseStep 1243655 = 1865483) B1865483
theorem B1178155 : Blo 826349 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B1243691 : Blo 826349 1243691 := bstep (se 1 (by rfl) ⟨932768, by rfl⟩ : syracuseStep 1243691 = 1865537) B1865537
theorem B1243721 : Blo 826349 1243721 := bstep (se 2 (by rfl) ⟨466395, by rfl⟩ : syracuseStep 1243721 = 932791) B932791
theorem B2095703 : Blo 826349 2095703 := bstep (se 1 (by rfl) ⟨1571777, by rfl⟩ : syracuseStep 2095703 = 3143555) B3143555
theorem B883343 : Blo 826349 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B1243835 : Blo 826349 1243835 := bstep (se 1 (by rfl) ⟨932876, by rfl⟩ : syracuseStep 1243835 = 1865753) B1865753
theorem B1243895 : Blo 826349 1243895 := bstep (se 1 (by rfl) ⟨932921, by rfl⟩ : syracuseStep 1243895 = 1865843) B1865843
theorem B1178383 : Blo 826349 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B2358031 : Blo 826349 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B1243919 : Blo 826349 1243919 := bstep (se 1 (by rfl) ⟨932939, by rfl⟩ : syracuseStep 1243919 = 1865879) B1865879
theorem B2095915 : Blo 826349 2095915 := bstep (se 1 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 2095915 = 3143873) B3143873
theorem B1243961 : Blo 826349 1243961 := bstep (se 2 (by rfl) ⟨466485, by rfl⟩ : syracuseStep 1243961 = 932971) B932971
theorem B1047431 : Blo 826349 1047431 := bstep (se 1 (by rfl) ⟨785573, by rfl⟩ : syracuseStep 1047431 = 1571147) B1571147
theorem B1244039 : Blo 826349 1244039 := bstep (se 1 (by rfl) ⟨933029, by rfl⟩ : syracuseStep 1244039 = 1866059) B1866059
theorem B1244075 : Blo 826349 1244075 := bstep (se 1 (by rfl) ⟨933056, by rfl⟩ : syracuseStep 1244075 = 1866113) B1866113
theorem B2096057 : Blo 826349 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B1244105 : Blo 826349 1244105 := bstep (se 2 (by rfl) ⟨466539, by rfl⟩ : syracuseStep 1244105 = 933079) B933079
theorem B2358305 : Blo 826349 2358305 := bstep (se 2 (by rfl) ⟨884364, by rfl⟩ : syracuseStep 2358305 = 1768729) B1768729
theorem B1571899 : Blo 826349 1571899 := bstep (se 1 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 1571899 = 2357849) B2357849
theorem B1244219 : Blo 826349 1244219 := bstep (se 1 (by rfl) ⟨933164, by rfl⟩ : syracuseStep 1244219 = 1866329) B1866329
theorem B1244279 : Blo 826349 1244279 := bstep (se 1 (by rfl) ⟨933209, by rfl⟩ : syracuseStep 1244279 = 1866419) B1866419
theorem B1178759 : Blo 826349 1178759 := bstep (se 1 (by rfl) ⟨884069, by rfl⟩ : syracuseStep 1178759 = 1768139) B1768139
theorem B1866887 : Blo 826349 1866887 := bstep (se 1 (by rfl) ⟨1400165, by rfl⟩ : syracuseStep 1866887 = 2800331) B2800331
theorem B1244303 : Blo 826349 1244303 := bstep (se 1 (by rfl) ⟨933227, by rfl⟩ : syracuseStep 1244303 = 1866455) B1866455
theorem B1244345 : Blo 826349 1244345 := bstep (se 2 (by rfl) ⟨466629, by rfl⟩ : syracuseStep 1244345 = 933259) B933259
theorem B1244423 : Blo 826349 1244423 := bstep (se 1 (by rfl) ⟨933317, by rfl⟩ : syracuseStep 1244423 = 1866635) B1866635
theorem B1244459 : Blo 826349 1244459 := bstep (se 1 (by rfl) ⟨933344, by rfl⟩ : syracuseStep 1244459 = 1866689) B1866689
theorem B1867067 : Blo 826349 1867067 := bstep (se 1 (by rfl) ⟨1400300, by rfl⟩ : syracuseStep 1867067 = 2800601) B2800601
theorem B1244489 : Blo 826349 1244489 := bstep (se 2 (by rfl) ⟨466683, by rfl⟩ : syracuseStep 1244489 = 933367) B933367
theorem B1867193 : Blo 826349 1867193 := bstep (se 2 (by rfl) ⟨700197, by rfl⟩ : syracuseStep 1867193 = 1400395) B1400395
theorem B1244603 : Blo 826349 1244603 := bstep (se 1 (by rfl) ⟨933452, by rfl⟩ : syracuseStep 1244603 = 1866905) B1866905
theorem B1244663 : Blo 826349 1244663 := bstep (se 1 (by rfl) ⟨933497, by rfl⟩ : syracuseStep 1244663 = 1866995) B1866995
theorem B2981387 : Blo 826349 2981387 := bstep (se 1 (by rfl) ⟨2236040, by rfl⟩ : syracuseStep 2981387 = 4472081) B4472081
theorem B1048079 : Blo 826349 1048079 := bstep (se 1 (by rfl) ⟨786059, by rfl⟩ : syracuseStep 1048079 = 1572119) B1572119
theorem B1244687 : Blo 826349 1244687 := bstep (se 1 (by rfl) ⟨933515, by rfl⟩ : syracuseStep 1244687 = 1867031) B1867031
theorem B1572385 : Blo 826349 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B1244729 : Blo 826349 1244729 := bstep (se 2 (by rfl) ⟨466773, by rfl⟩ : syracuseStep 1244729 = 933547) B933547
theorem B1244807 : Blo 826349 1244807 := bstep (se 1 (by rfl) ⟨933605, by rfl⟩ : syracuseStep 1244807 = 1867211) B1867211
theorem B1244843 : Blo 826349 1244843 := bstep (se 1 (by rfl) ⟨933632, by rfl⟩ : syracuseStep 1244843 = 1867265) B1867265
theorem B1244873 : Blo 826349 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B3538703 : Blo 826349 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B1867535 : Blo 826349 1867535 := bstep (se 1 (by rfl) ⟨1400651, by rfl⟩ : syracuseStep 1867535 = 2801303) B2801303
theorem B1769249 : Blo 826349 1769249 := bstep (se 2 (by rfl) ⟨663468, by rfl⟩ : syracuseStep 1769249 = 1326937) B1326937
theorem B1867553 : Blo 826349 1867553 := bstep (se 2 (by rfl) ⟨700332, by rfl⟩ : syracuseStep 1867553 = 1400665) B1400665
theorem B884539 : Blo 826349 884539 := bstep (se 1 (by rfl) ⟨663404, by rfl⟩ : syracuseStep 884539 = 1326809) B1326809
theorem B1244987 : Blo 826349 1244987 := bstep (se 1 (by rfl) ⟨933740, by rfl⟩ : syracuseStep 1244987 = 1867481) B1867481
theorem B1245047 : Blo 826349 1245047 := bstep (se 1 (by rfl) ⟨933785, by rfl⟩ : syracuseStep 1245047 = 1867571) B1867571
theorem B1245071 : Blo 826349 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B2097049 : Blo 826349 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B1245113 : Blo 826349 1245113 := bstep (se 2 (by rfl) ⟨466917, by rfl⟩ : syracuseStep 1245113 = 933835) B933835
theorem B1572871 : Blo 826349 1572871 := bstep (se 1 (by rfl) ⟨1179653, by rfl⟩ : syracuseStep 1572871 = 2359307) B2359307
theorem B1278031 : Blo 826349 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B1245263 : Blo 826349 1245263 := bstep (se 1 (by rfl) ⟨933947, by rfl⟩ : syracuseStep 1245263 = 1867895) B1867895
theorem B4718681 : Blo 826349 4718681 := bstep (se 2 (by rfl) ⟨1769505, by rfl⟩ : syracuseStep 4718681 = 3539011) B3539011
theorem B2097323 : Blo 826349 2097323 := bstep (se 1 (by rfl) ⟨1572992, by rfl⟩ : syracuseStep 2097323 = 3145985) B3145985
theorem B1245383 : Blo 826349 1245383 := bstep (se 1 (by rfl) ⟨934037, by rfl⟩ : syracuseStep 1245383 = 1868075) B1868075
theorem B4194665 : Blo 826349 4194665 := bstep (se 2 (by rfl) ⟨1572999, by rfl⟩ : syracuseStep 4194665 = 3145999) B3145999
theorem B2687357 : Blo 826349 2687357 := bstep (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) B1007759
theorem B1049051 : Blo 826349 1049051 := bstep (se 1 (by rfl) ⟨786788, by rfl⟩ : syracuseStep 1049051 = 1573577) B1573577
theorem B3146273 : Blo 826349 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B885287 : Blo 826349 885287 := bstep (se 1 (by rfl) ⟨663965, by rfl⟩ : syracuseStep 885287 = 1327931) B1327931
theorem B53609111 : Blo 826349 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B8946449 : Blo 826349 8946449 := bstep (se 2 (by rfl) ⟨3354918, by rfl⟩ : syracuseStep 8946449 = 6709837) B6709837
theorem B5964617 : Blo 826349 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B1049527 : Blo 826349 1049527 := bstep (se 1 (by rfl) ⟨787145, by rfl⟩ : syracuseStep 1049527 = 1574291) B1574291
theorem B3539969 : Blo 826349 3539969 := bstep (se 2 (by rfl) ⟨1327488, by rfl⟩ : syracuseStep 3539969 = 2654977) B2654977
theorem B3146759 : Blo 826349 3146759 := bstep (se 1 (by rfl) ⟨2360069, by rfl⟩ : syracuseStep 3146759 = 4720139) B4720139
theorem B2098183 : Blo 826349 2098183 := bstep (se 1 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 2098183 = 3147275) B3147275
theorem B3408911 : Blo 826349 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B2983159 : Blo 826349 2983159 := bstep (se 1 (by rfl) ⟨2237369, by rfl⟩ : syracuseStep 2983159 = 4474739) B4474739
theorem B6292727 : Blo 826349 6292727 := bstep (se 1 (by rfl) ⟨4719545, by rfl⟩ : syracuseStep 6292727 = 9439091) B9439091
theorem B7079183 : Blo 826349 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B3147245 : Blo 826349 3147245 := bstep (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) B1180217
theorem B2983463 : Blo 826349 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B2098811 : Blo 826349 2098811 := bstep (se 1 (by rfl) ⟨1574108, by rfl⟩ : syracuseStep 2098811 = 3148217) B3148217
theorem B6293213 : Blo 826349 6293213 := bstep (se 3 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 6293213 = 2359955) B2359955
theorem B2099105 : Blo 826349 2099105 := bstep (se 2 (by rfl) ⟨787164, by rfl⟩ : syracuseStep 2099105 = 1574329) B1574329
theorem B1575035 : Blo 826349 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B3147929 : Blo 826349 3147929 := bstep (se 2 (by rfl) ⟨1180473, by rfl⟩ : syracuseStep 3147929 = 2360947) B2360947
theorem B1050823 : Blo 826349 1050823 := bstep (se 1 (by rfl) ⟨788117, by rfl⟩ : syracuseStep 1050823 = 1576235) B1576235
theorem B1575263 : Blo 826349 1575263 := bstep (se 1 (by rfl) ⟨1181447, by rfl⟩ : syracuseStep 1575263 = 2362895) B2362895
theorem B1575521 : Blo 826349 1575521 := bstep (se 2 (by rfl) ⟨590820, by rfl⟩ : syracuseStep 1575521 = 1181641) B1181641
theorem B1575787 : Blo 826349 1575787 := bstep (se 1 (by rfl) ⟨1181840, by rfl⟩ : syracuseStep 1575787 = 2363681) B2363681
theorem B2984975 : Blo 826349 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B3148915 : Blo 826349 3148915 := bstep (se 1 (by rfl) ⟨2361686, by rfl⟩ : syracuseStep 3148915 = 4723373) B4723373
theorem B9440549 : Blo 826349 9440549 := bstep (se 4 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 9440549 = 1770103) B1770103
theorem B3313021 : Blo 826349 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B2100775 : Blo 826349 2100775 := bstep (se 1 (by rfl) ⟨1575581, by rfl⟩ : syracuseStep 2100775 = 3151163) B3151163
theorem B1773179 : Blo 826349 1773179 := bstep (se 1 (by rfl) ⟨1329884, by rfl⟩ : syracuseStep 1773179 = 2659769) B2659769
theorem B3149675 : Blo 826349 3149675 := bstep (se 1 (by rfl) ⟨2362256, by rfl⟩ : syracuseStep 3149675 = 4724513) B4724513
theorem B2101099 : Blo 826349 2101099 := bstep (se 1 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 2101099 = 3151649) B3151649
theorem B15896483 : Blo 826349 15896483 := bstep (se 1 (by rfl) ⟨11922362, by rfl⟩ : syracuseStep 15896483 = 23844725) B23844725
theorem B11964347 : Blo 826349 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B5312465 : Blo 826349 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B1675343 : Blo 826349 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1675513 : Blo 826349 1675513 := bstep (se 2 (by rfl) ⟨628317, by rfl⟩ : syracuseStep 1675513 = 1256635) B1256635
theorem B2789693 : Blo 826349 2789693 := bstep (se 3 (by rfl) ⟨523067, by rfl⟩ : syracuseStep 2789693 = 1046135) B1046135
theorem B2101747 : Blo 826349 2101747 := bstep (se 1 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 2101747 = 3152621) B3152621
theorem B331321873 : Blo 826349 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B2659385 : Blo 826349 2659385 := bstep (se 2 (by rfl) ⟨997269, by rfl⟩ : syracuseStep 2659385 = 1994539) B1994539
theorem B2790557 : Blo 826349 2790557 := bstep (se 3 (by rfl) ⟨523229, by rfl⟩ : syracuseStep 2790557 = 1046459) B1046459
theorem B2987165 : Blo 826349 2987165 := bstep (se 3 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 2987165 = 1120187) B1120187
theorem B5969315 : Blo 826349 5969315 := bstep (se 1 (by rfl) ⟨4476986, by rfl⟩ : syracuseStep 5969315 = 8953973) B8953973
theorem B5969371 : Blo 826349 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B2791097 : Blo 826349 2791097 := bstep (se 2 (by rfl) ⟨1046661, by rfl⟩ : syracuseStep 2791097 = 2093323) B2093323
theorem B8722235 : Blo 826349 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B1513721 : Blo 826349 1513721 := bstep (se 2 (by rfl) ⟨567645, by rfl⟩ : syracuseStep 1513721 = 1135291) B1135291
theorem B2791691 : Blo 826349 2791691 := bstep (se 1 (by rfl) ⟨2093768, by rfl⟩ : syracuseStep 2791691 = 4187537) B4187537
theorem B2234753 : Blo 826349 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B2791961 : Blo 826349 2791961 := bstep (se 2 (by rfl) ⟨1046985, by rfl⟩ : syracuseStep 2791961 = 2093971) B2093971
theorem B1120891 : Blo 826349 1120891 := bstep (se 1 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 1120891 = 1681337) B1681337
theorem B4201145 : Blo 826349 4201145 := bstep (se 2 (by rfl) ⟨1575429, by rfl⟩ : syracuseStep 4201145 = 3150859) B3150859
theorem B2988895 : Blo 826349 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B826407 : Blo 826349 826407 := bstep (se 1 (by rfl) ⟨619805, by rfl⟩ : syracuseStep 826407 = 1239611) B1239611
theorem B826447 : Blo 826349 826447 := bstep (se 1 (by rfl) ⟨619835, by rfl⟩ : syracuseStep 826447 = 1239671) B1239671
theorem B826463 : Blo 826349 826463 := bstep (se 1 (by rfl) ⟨619847, by rfl⟩ : syracuseStep 826463 = 1239695) B1239695
theorem B826491 : Blo 826349 826491 := bstep (se 1 (by rfl) ⟨619868, by rfl⟩ : syracuseStep 826491 = 1239737) B1239737
theorem B826543 : Blo 826349 826543 := bstep (se 1 (by rfl) ⟨619907, by rfl⟩ : syracuseStep 826543 = 1239815) B1239815
theorem B826567 : Blo 826349 826567 := bstep (se 1 (by rfl) ⟨619925, by rfl⟩ : syracuseStep 826567 = 1239851) B1239851
theorem B826587 : Blo 826349 826587 := bstep (se 1 (by rfl) ⟨619940, by rfl⟩ : syracuseStep 826587 = 1239881) B1239881
theorem B10591505 : Blo 826349 10591505 := bstep (se 2 (by rfl) ⟨3971814, by rfl⟩ : syracuseStep 10591505 = 7943629) B7943629
theorem B826663 : Blo 826349 826663 := bstep (se 1 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 826663 = 1239995) B1239995
theorem B826703 : Blo 826349 826703 := bstep (se 1 (by rfl) ⟨620027, by rfl⟩ : syracuseStep 826703 = 1240055) B1240055
theorem B826719 : Blo 826349 826719 := bstep (se 1 (by rfl) ⟨620039, by rfl⟩ : syracuseStep 826719 = 1240079) B1240079
theorem B826747 : Blo 826349 826747 := bstep (se 1 (by rfl) ⟨620060, by rfl⟩ : syracuseStep 826747 = 1240121) B1240121
theorem B6299045 : Blo 826349 6299045 := bstep (se 4 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 6299045 = 1181071) B1181071
theorem B826799 : Blo 826349 826799 := bstep (se 1 (by rfl) ⟨620099, by rfl⟩ : syracuseStep 826799 = 1240199) B1240199
theorem B826823 : Blo 826349 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B826843 : Blo 826349 826843 := bstep (se 1 (by rfl) ⟨620132, by rfl⟩ : syracuseStep 826843 = 1240265) B1240265
theorem B826919 : Blo 826349 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B826959 : Blo 826349 826959 := bstep (se 1 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 826959 = 1240439) B1240439
theorem B826975 : Blo 826349 826975 := bstep (se 1 (by rfl) ⟨620231, by rfl⟩ : syracuseStep 826975 = 1240463) B1240463
theorem B827003 : Blo 826349 827003 := bstep (se 1 (by rfl) ⟨620252, by rfl⟩ : syracuseStep 827003 = 1240505) B1240505
theorem B2793095 : Blo 826349 2793095 := bstep (se 1 (by rfl) ⟨2094821, by rfl⟩ : syracuseStep 2793095 = 4189643) B4189643
theorem B827055 : Blo 826349 827055 := bstep (se 1 (by rfl) ⟨620291, by rfl⟩ : syracuseStep 827055 = 1240583) B1240583
theorem B2793149 : Blo 826349 2793149 := bstep (se 3 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 2793149 = 1047431) B1047431
theorem B827079 : Blo 826349 827079 := bstep (se 1 (by rfl) ⟨620309, by rfl⟩ : syracuseStep 827079 = 1240619) B1240619
theorem B4726471 : Blo 826349 4726471 := bstep (se 1 (by rfl) ⟨3544853, by rfl⟩ : syracuseStep 4726471 = 7089707) B7089707
theorem B827099 : Blo 826349 827099 := bstep (se 1 (by rfl) ⟨620324, by rfl⟩ : syracuseStep 827099 = 1240649) B1240649
theorem B827175 : Blo 826349 827175 := bstep (se 1 (by rfl) ⟨620381, by rfl⟩ : syracuseStep 827175 = 1240763) B1240763
theorem B827215 : Blo 826349 827215 := bstep (se 1 (by rfl) ⟨620411, by rfl⟩ : syracuseStep 827215 = 1240823) B1240823
theorem B827231 : Blo 826349 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B2793311 : Blo 826349 2793311 := bstep (se 1 (by rfl) ⟨2094983, by rfl⟩ : syracuseStep 2793311 = 4189967) B4189967
theorem B5316461 : Blo 826349 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B827259 : Blo 826349 827259 := bstep (se 1 (by rfl) ⟨620444, by rfl⟩ : syracuseStep 827259 = 1240889) B1240889
theorem B827311 : Blo 826349 827311 := bstep (se 1 (by rfl) ⟨620483, by rfl⟩ : syracuseStep 827311 = 1240967) B1240967
theorem B827335 : Blo 826349 827335 := bstep (se 1 (by rfl) ⟨620501, by rfl⟩ : syracuseStep 827335 = 1241003) B1241003
theorem B827355 : Blo 826349 827355 := bstep (se 1 (by rfl) ⟨620516, by rfl⟩ : syracuseStep 827355 = 1241033) B1241033
theorem B2793473 : Blo 826349 2793473 := bstep (se 2 (by rfl) ⟨1047552, by rfl⟩ : syracuseStep 2793473 = 2095105) B2095105
theorem B827431 : Blo 826349 827431 := bstep (se 1 (by rfl) ⟨620573, by rfl⟩ : syracuseStep 827431 = 1241147) B1241147
theorem B827471 : Blo 826349 827471 := bstep (se 1 (by rfl) ⟨620603, by rfl⟩ : syracuseStep 827471 = 1241207) B1241207
theorem B827487 : Blo 826349 827487 := bstep (se 1 (by rfl) ⟨620615, by rfl⟩ : syracuseStep 827487 = 1241231) B1241231
theorem B2990195 : Blo 826349 2990195 := bstep (se 1 (by rfl) ⟨2242646, by rfl⟩ : syracuseStep 2990195 = 4485293) B4485293
theorem B827515 : Blo 826349 827515 := bstep (se 1 (by rfl) ⟨620636, by rfl⟩ : syracuseStep 827515 = 1241273) B1241273
theorem B827567 : Blo 826349 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B827591 : Blo 826349 827591 := bstep (se 1 (by rfl) ⟨620693, by rfl⟩ : syracuseStep 827591 = 1241387) B1241387
theorem B827611 : Blo 826349 827611 := bstep (se 1 (by rfl) ⟨620708, by rfl⟩ : syracuseStep 827611 = 1241417) B1241417
theorem B3186955 : Blo 826349 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B827687 : Blo 826349 827687 := bstep (se 1 (by rfl) ⟨620765, by rfl⟩ : syracuseStep 827687 = 1241531) B1241531
theorem B21537089 : Blo 826349 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B827727 : Blo 826349 827727 := bstep (se 1 (by rfl) ⟨620795, by rfl⟩ : syracuseStep 827727 = 1241591) B1241591
theorem B827743 : Blo 826349 827743 := bstep (se 1 (by rfl) ⟨620807, by rfl⟩ : syracuseStep 827743 = 1241615) B1241615
theorem B827771 : Blo 826349 827771 := bstep (se 1 (by rfl) ⟨620828, by rfl⟩ : syracuseStep 827771 = 1241657) B1241657
theorem B827823 : Blo 826349 827823 := bstep (se 1 (by rfl) ⟨620867, by rfl⟩ : syracuseStep 827823 = 1241735) B1241735
theorem B827847 : Blo 826349 827847 := bstep (se 1 (by rfl) ⟨620885, by rfl⟩ : syracuseStep 827847 = 1241771) B1241771
theorem B827867 : Blo 826349 827867 := bstep (se 1 (by rfl) ⟨620900, by rfl⟩ : syracuseStep 827867 = 1241801) B1241801
theorem B10625539 : Blo 826349 10625539 := bstep (se 1 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 10625539 = 15938309) B15938309
theorem B827943 : Blo 826349 827943 := bstep (se 1 (by rfl) ⟨620957, by rfl⟩ : syracuseStep 827943 = 1241915) B1241915
theorem B4792891 : Blo 826349 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B827983 : Blo 826349 827983 := bstep (se 1 (by rfl) ⟨620987, by rfl⟩ : syracuseStep 827983 = 1241975) B1241975
theorem B827999 : Blo 826349 827999 := bstep (se 1 (by rfl) ⟨620999, by rfl⟩ : syracuseStep 827999 = 1241999) B1241999
theorem B828027 : Blo 826349 828027 := bstep (se 1 (by rfl) ⟨621020, by rfl⟩ : syracuseStep 828027 = 1242041) B1242041
theorem B828079 : Blo 826349 828079 := bstep (se 1 (by rfl) ⟨621059, by rfl⟩ : syracuseStep 828079 = 1242119) B1242119
theorem B828103 : Blo 826349 828103 := bstep (se 1 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 828103 = 1242155) B1242155
theorem B828123 : Blo 826349 828123 := bstep (se 1 (by rfl) ⟨621092, by rfl⟩ : syracuseStep 828123 = 1242185) B1242185
theorem B828199 : Blo 826349 828199 := bstep (se 1 (by rfl) ⟨621149, by rfl⟩ : syracuseStep 828199 = 1242299) B1242299
theorem B2794283 : Blo 826349 2794283 := bstep (se 1 (by rfl) ⟨2095712, by rfl⟩ : syracuseStep 2794283 = 4191425) B4191425
theorem B828239 : Blo 826349 828239 := bstep (se 1 (by rfl) ⟨621179, by rfl⟩ : syracuseStep 828239 = 1242359) B1242359
theorem B828255 : Blo 826349 828255 := bstep (se 1 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 828255 = 1242383) B1242383
theorem B5677931 : Blo 826349 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B828283 : Blo 826349 828283 := bstep (se 1 (by rfl) ⟨621212, by rfl⟩ : syracuseStep 828283 = 1242425) B1242425
theorem B828335 : Blo 826349 828335 := bstep (se 1 (by rfl) ⟨621251, by rfl⟩ : syracuseStep 828335 = 1242503) B1242503
theorem B828359 : Blo 826349 828359 := bstep (se 1 (by rfl) ⟨621269, by rfl⟩ : syracuseStep 828359 = 1242539) B1242539
theorem B828379 : Blo 826349 828379 := bstep (se 1 (by rfl) ⟨621284, by rfl⟩ : syracuseStep 828379 = 1242569) B1242569
theorem B828455 : Blo 826349 828455 := bstep (se 1 (by rfl) ⟨621341, by rfl⟩ : syracuseStep 828455 = 1242683) B1242683
theorem B2794553 : Blo 826349 2794553 := bstep (se 2 (by rfl) ⟨1047957, by rfl⟩ : syracuseStep 2794553 = 2095915) B2095915
theorem B6366275 : Blo 826349 6366275 := bstep (se 1 (by rfl) ⟨4774706, by rfl⟩ : syracuseStep 6366275 = 9549413) B9549413
theorem B828495 : Blo 826349 828495 := bstep (se 1 (by rfl) ⟨621371, by rfl⟩ : syracuseStep 828495 = 1242743) B1242743
theorem B828511 : Blo 826349 828511 := bstep (se 1 (by rfl) ⟨621383, by rfl⟩ : syracuseStep 828511 = 1242767) B1242767
theorem B828539 : Blo 826349 828539 := bstep (se 1 (by rfl) ⟨621404, by rfl⟩ : syracuseStep 828539 = 1242809) B1242809
theorem B828591 : Blo 826349 828591 := bstep (se 1 (by rfl) ⟨621443, by rfl⟩ : syracuseStep 828591 = 1242887) B1242887
theorem B828615 : Blo 826349 828615 := bstep (se 1 (by rfl) ⟨621461, by rfl⟩ : syracuseStep 828615 = 1242923) B1242923
theorem B828635 : Blo 826349 828635 := bstep (se 1 (by rfl) ⟨621476, by rfl⟩ : syracuseStep 828635 = 1242953) B1242953
theorem B828711 : Blo 826349 828711 := bstep (se 1 (by rfl) ⟨621533, by rfl⟩ : syracuseStep 828711 = 1243067) B1243067
theorem B828751 : Blo 826349 828751 := bstep (se 1 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 828751 = 1243127) B1243127
theorem B828767 : Blo 826349 828767 := bstep (se 1 (by rfl) ⟨621575, by rfl⟩ : syracuseStep 828767 = 1243151) B1243151
theorem B828795 : Blo 826349 828795 := bstep (se 1 (by rfl) ⟨621596, by rfl⟩ : syracuseStep 828795 = 1243193) B1243193
theorem B2794877 : Blo 826349 2794877 := bstep (se 3 (by rfl) ⟨524039, by rfl⟩ : syracuseStep 2794877 = 1048079) B1048079
theorem B5383597 : Blo 826349 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B828847 : Blo 826349 828847 := bstep (se 1 (by rfl) ⟨621635, by rfl⟩ : syracuseStep 828847 = 1243271) B1243271
theorem B828871 : Blo 826349 828871 := bstep (se 1 (by rfl) ⟨621653, by rfl⟩ : syracuseStep 828871 = 1243307) B1243307
theorem B8955355 : Blo 826349 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B828891 : Blo 826349 828891 := bstep (se 1 (by rfl) ⟨621668, by rfl⟩ : syracuseStep 828891 = 1243337) B1243337
theorem B828967 : Blo 826349 828967 := bstep (se 1 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 828967 = 1243451) B1243451
theorem B829007 : Blo 826349 829007 := bstep (se 1 (by rfl) ⟨621755, by rfl⟩ : syracuseStep 829007 = 1243511) B1243511
theorem B829023 : Blo 826349 829023 := bstep (se 1 (by rfl) ⟨621767, by rfl⟩ : syracuseStep 829023 = 1243535) B1243535
theorem B8496737 : Blo 826349 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B829051 : Blo 826349 829051 := bstep (se 1 (by rfl) ⟨621788, by rfl⟩ : syracuseStep 829051 = 1243577) B1243577
theorem B2795147 : Blo 826349 2795147 := bstep (se 1 (by rfl) ⟨2096360, by rfl⟩ : syracuseStep 2795147 = 4192721) B4192721
theorem B829103 : Blo 826349 829103 := bstep (se 1 (by rfl) ⟨621827, by rfl⟩ : syracuseStep 829103 = 1243655) B1243655
theorem B829127 : Blo 826349 829127 := bstep (se 1 (by rfl) ⟨621845, by rfl⟩ : syracuseStep 829127 = 1243691) B1243691
theorem B829147 : Blo 826349 829147 := bstep (se 1 (by rfl) ⟨621860, by rfl⟩ : syracuseStep 829147 = 1243721) B1243721
theorem B11970341 : Blo 826349 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B829223 : Blo 826349 829223 := bstep (se 1 (by rfl) ⟨621917, by rfl⟩ : syracuseStep 829223 = 1243835) B1243835
theorem B10626875 : Blo 826349 10626875 := bstep (se 1 (by rfl) ⟨7970156, by rfl⟩ : syracuseStep 10626875 = 15940313) B15940313
theorem B7087931 : Blo 826349 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B829263 : Blo 826349 829263 := bstep (se 1 (by rfl) ⟨621947, by rfl⟩ : syracuseStep 829263 = 1243895) B1243895
theorem B829279 : Blo 826349 829279 := bstep (se 1 (by rfl) ⟨621959, by rfl⟩ : syracuseStep 829279 = 1243919) B1243919
theorem B829307 : Blo 826349 829307 := bstep (se 1 (by rfl) ⟨621980, by rfl⟩ : syracuseStep 829307 = 1243961) B1243961
theorem B829359 : Blo 826349 829359 := bstep (se 1 (by rfl) ⟨622019, by rfl⟩ : syracuseStep 829359 = 1244039) B1244039
theorem B829383 : Blo 826349 829383 := bstep (se 1 (by rfl) ⟨622037, by rfl⟩ : syracuseStep 829383 = 1244075) B1244075
theorem B829403 : Blo 826349 829403 := bstep (se 1 (by rfl) ⟨622052, by rfl⟩ : syracuseStep 829403 = 1244105) B1244105
theorem B3352583 : Blo 826349 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B5318693 : Blo 826349 5318693 := bstep (se 4 (by rfl) ⟨498627, by rfl⟩ : syracuseStep 5318693 = 997255) B997255
theorem B829479 : Blo 826349 829479 := bstep (se 1 (by rfl) ⟨622109, by rfl⟩ : syracuseStep 829479 = 1244219) B1244219
theorem B829519 : Blo 826349 829519 := bstep (se 1 (by rfl) ⟨622139, by rfl⟩ : syracuseStep 829519 = 1244279) B1244279
theorem B829535 : Blo 826349 829535 := bstep (se 1 (by rfl) ⟨622151, by rfl⟩ : syracuseStep 829535 = 1244303) B1244303
theorem B829563 : Blo 826349 829563 := bstep (se 1 (by rfl) ⟨622172, by rfl⟩ : syracuseStep 829563 = 1244345) B1244345
theorem B2828459 : Blo 826349 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B829615 : Blo 826349 829615 := bstep (se 1 (by rfl) ⟨622211, by rfl⟩ : syracuseStep 829615 = 1244423) B1244423
theorem B829639 : Blo 826349 829639 := bstep (se 1 (by rfl) ⟨622229, by rfl⟩ : syracuseStep 829639 = 1244459) B1244459
theorem B829659 : Blo 826349 829659 := bstep (se 1 (by rfl) ⟨622244, by rfl⟩ : syracuseStep 829659 = 1244489) B1244489
theorem B11938049 : Blo 826349 11938049 := bstep (se 2 (by rfl) ⟨4476768, by rfl⟩ : syracuseStep 11938049 = 8953537) B8953537
theorem B829735 : Blo 826349 829735 := bstep (se 1 (by rfl) ⟨622301, by rfl⟩ : syracuseStep 829735 = 1244603) B1244603
theorem B829775 : Blo 826349 829775 := bstep (se 1 (by rfl) ⟨622331, by rfl⟩ : syracuseStep 829775 = 1244663) B1244663
theorem B829791 : Blo 826349 829791 := bstep (se 1 (by rfl) ⟨622343, by rfl⟩ : syracuseStep 829791 = 1244687) B1244687
theorem B829819 : Blo 826349 829819 := bstep (se 1 (by rfl) ⟨622364, by rfl⟩ : syracuseStep 829819 = 1244729) B1244729
theorem B829871 : Blo 826349 829871 := bstep (se 1 (by rfl) ⟨622403, by rfl⟩ : syracuseStep 829871 = 1244807) B1244807
theorem B829895 : Blo 826349 829895 := bstep (se 1 (by rfl) ⟨622421, by rfl⟩ : syracuseStep 829895 = 1244843) B1244843
theorem B829915 : Blo 826349 829915 := bstep (se 1 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 829915 = 1244873) B1244873
theorem B2796065 : Blo 826349 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B829991 : Blo 826349 829991 := bstep (se 1 (by rfl) ⟨622493, by rfl⟩ : syracuseStep 829991 = 1244987) B1244987
theorem B830031 : Blo 826349 830031 := bstep (se 1 (by rfl) ⟨622523, by rfl⟩ : syracuseStep 830031 = 1245047) B1245047
theorem B830047 : Blo 826349 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B830075 : Blo 826349 830075 := bstep (se 1 (by rfl) ⟨622556, by rfl⟩ : syracuseStep 830075 = 1245113) B1245113
theorem B830127 : Blo 826349 830127 := bstep (se 1 (by rfl) ⟨622595, by rfl⟩ : syracuseStep 830127 = 1245191) B1245191
theorem B830151 : Blo 826349 830151 := bstep (se 1 (by rfl) ⟨622613, by rfl⟩ : syracuseStep 830151 = 1245227) B1245227
theorem B830171 : Blo 826349 830171 := bstep (se 1 (by rfl) ⟨622628, by rfl⟩ : syracuseStep 830171 = 1245257) B1245257
theorem B2796281 : Blo 826349 2796281 := bstep (se 2 (by rfl) ⟨1048605, by rfl⟩ : syracuseStep 2796281 = 2097211) B2097211
theorem B830247 : Blo 826349 830247 := bstep (se 1 (by rfl) ⟨622685, by rfl⟩ : syracuseStep 830247 = 1245371) B1245371
theorem B830287 : Blo 826349 830287 := bstep (se 1 (by rfl) ⟨622715, by rfl⟩ : syracuseStep 830287 = 1245431) B1245431
theorem B830303 : Blo 826349 830303 := bstep (se 1 (by rfl) ⟨622727, by rfl⟩ : syracuseStep 830303 = 1245455) B1245455
theorem B830331 : Blo 826349 830331 := bstep (se 1 (by rfl) ⟨622748, by rfl⟩ : syracuseStep 830331 = 1245497) B1245497
theorem B2796551 : Blo 826349 2796551 := bstep (se 1 (by rfl) ⟨2097413, by rfl⟩ : syracuseStep 2796551 = 4194827) B4194827
theorem B2796659 : Blo 826349 2796659 := bstep (se 1 (by rfl) ⟨2097494, by rfl⟩ : syracuseStep 2796659 = 4194989) B4194989
theorem B2796929 : Blo 826349 2796929 := bstep (se 2 (by rfl) ⟨1048848, by rfl⟩ : syracuseStep 2796929 = 2097697) B2097697
theorem B21507763 : Blo 826349 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B6205177 : Blo 826349 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B3354463 : Blo 826349 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B1257481 : Blo 826349 1257481 := bstep (se 2 (by rfl) ⟨471555, by rfl⟩ : syracuseStep 1257481 = 943111) B943111
theorem B43135091 : Blo 826349 43135091 := bstep (se 1 (by rfl) ⟨32351318, by rfl⟩ : syracuseStep 43135091 = 64702637) B64702637
theorem B2797739 : Blo 826349 2797739 := bstep (se 1 (by rfl) ⟨2098304, by rfl⟩ : syracuseStep 2797739 = 4196609) B4196609
theorem B20132225 : Blo 826349 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B930343 : Blo 826349 930343 := bstep (se 1 (by rfl) ⟨697757, by rfl⟩ : syracuseStep 930343 = 1395515) B1395515
theorem B6304391 : Blo 826349 6304391 := bstep (se 1 (by rfl) ⟨4728293, by rfl⟩ : syracuseStep 6304391 = 9456587) B9456587
theorem B2798279 : Blo 826349 2798279 := bstep (se 1 (by rfl) ⟨2098709, by rfl⟩ : syracuseStep 2798279 = 4197419) B4197419
theorem B7943321 : Blo 826349 7943321 := bstep (se 2 (by rfl) ⟨2978745, by rfl⟩ : syracuseStep 7943321 = 5957491) B5957491
theorem B7091621 : Blo 826349 7091621 := bstep (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) B1329679
theorem B2799143 : Blo 826349 2799143 := bstep (se 1 (by rfl) ⟨2099357, by rfl⟩ : syracuseStep 2799143 = 4198715) B4198715
theorem B2799251 : Blo 826349 2799251 := bstep (se 1 (by rfl) ⟨2099438, by rfl⟩ : syracuseStep 2799251 = 4198877) B4198877
theorem B10630871 : Blo 826349 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B3192605 : Blo 826349 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B1324907 : Blo 826349 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B2799467 : Blo 826349 2799467 := bstep (se 1 (by rfl) ⟨2099600, by rfl⟩ : syracuseStep 2799467 = 4199201) B4199201
theorem B2799521 : Blo 826349 2799521 := bstep (se 2 (by rfl) ⟨1049820, by rfl⟩ : syracuseStep 2799521 = 2099641) B2099641
theorem B8599505 : Blo 826349 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B6043655 : Blo 826349 6043655 := bstep (se 1 (by rfl) ⟨4532741, by rfl⟩ : syracuseStep 6043655 = 9065483) B9065483
theorem B931963 : Blo 826349 931963 := bstep (se 1 (by rfl) ⟨698972, by rfl⟩ : syracuseStep 931963 = 1397945) B1397945
theorem B1489259 : Blo 826349 1489259 := bstep (se 1 (by rfl) ⟨1116944, by rfl⟩ : syracuseStep 1489259 = 2233889) B2233889
theorem B7092683 : Blo 826349 7092683 := bstep (se 1 (by rfl) ⟨5319512, by rfl⟩ : syracuseStep 7092683 = 10639025) B10639025
theorem B2800115 : Blo 826349 2800115 := bstep (se 1 (by rfl) ⟨2100086, by rfl⟩ : syracuseStep 2800115 = 4200173) B4200173
theorem B932431 : Blo 826349 932431 := bstep (se 1 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 932431 = 1398647) B1398647
theorem B1489655 : Blo 826349 1489655 := bstep (se 1 (by rfl) ⟨1117241, by rfl⟩ : syracuseStep 1489655 = 2234483) B2234483
theorem B932827 : Blo 826349 932827 := bstep (se 1 (by rfl) ⟨699620, by rfl⟩ : syracuseStep 932827 = 1399241) B1399241
theorem B2800655 : Blo 826349 2800655 := bstep (se 1 (by rfl) ⟨2100491, by rfl⟩ : syracuseStep 2800655 = 4200983) B4200983
theorem B2243965 : Blo 826349 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B933295 : Blo 826349 933295 := bstep (se 1 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 933295 = 1399943) B1399943
theorem B5979635 : Blo 826349 5979635 := bstep (se 1 (by rfl) ⟨4484726, by rfl⟩ : syracuseStep 5979635 = 8969453) B8969453
theorem B2801249 : Blo 826349 2801249 := bstep (se 2 (by rfl) ⟨1050468, by rfl⟩ : syracuseStep 2801249 = 2100937) B2100937
theorem B933727 : Blo 826349 933727 := bstep (se 1 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 933727 = 1400591) B1400591
theorem B2834489 : Blo 826349 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B934087 : Blo 826349 934087 := bstep (se 1 (by rfl) ⟨700565, by rfl⟩ : syracuseStep 934087 = 1401131) B1401131
theorem B3195451 : Blo 826349 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B1262279 : Blo 826349 1262279 := bstep (se 1 (by rfl) ⟨946709, by rfl⟩ : syracuseStep 1262279 = 1893419) B1893419
theorem B7947011 : Blo 826349 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B1328167 : Blo 826349 1328167 := bstep (se 1 (by rfl) ⟨996125, by rfl⟩ : syracuseStep 1328167 = 1992251) B1992251
theorem B16106845 : Blo 826349 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B1328719 : Blo 826349 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B1394651 : Blo 826349 1394651 := bstep (se 1 (by rfl) ⟨1045988, by rfl⟩ : syracuseStep 1394651 = 2091977) B2091977
theorem B1394887 : Blo 826349 1394887 := bstep (se 1 (by rfl) ⟨1046165, by rfl⟩ : syracuseStep 1394887 = 2092331) B2092331
theorem B1395049 : Blo 826349 1395049 := bstep (se 2 (by rfl) ⟨523143, by rfl⟩ : syracuseStep 1395049 = 1046287) B1046287
theorem B6376121 : Blo 826349 6376121 := bstep (se 2 (by rfl) ⟨2391045, by rfl⟩ : syracuseStep 6376121 = 4782091) B4782091
theorem B1395643 : Blo 826349 1395643 := bstep (se 1 (by rfl) ⟨1046732, by rfl⟩ : syracuseStep 1395643 = 2093465) B2093465
theorem B1395751 : Blo 826349 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B1396075 : Blo 826349 1396075 := bstep (se 1 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 1396075 = 2094113) B2094113
theorem B10637021 : Blo 826349 10637021 := bstep (se 3 (by rfl) ⟨1994441, by rfl⟩ : syracuseStep 10637021 = 3988883) B3988883
theorem B7065377 : Blo 826349 7065377 := bstep (se 2 (by rfl) ⟨2649516, by rfl⟩ : syracuseStep 7065377 = 5299033) B5299033
theorem B839975 : Blo 826349 839975 := bstep (se 1 (by rfl) ⟨629981, by rfl⟩ : syracuseStep 839975 = 1259963) B1259963
theorem B3985793 : Blo 826349 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B1397135 : Blo 826349 1397135 := bstep (se 1 (by rfl) ⟨1047851, by rfl⟩ : syracuseStep 1397135 = 2095703) B2095703
theorem B1495559 : Blo 826349 1495559 := bstep (se 1 (by rfl) ⟨1121669, by rfl⟩ : syracuseStep 1495559 = 2243339) B2243339
theorem B1397371 : Blo 826349 1397371 := bstep (se 1 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 1397371 = 2096057) B2096057
theorem B7263233 : Blo 826349 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B1987591 : Blo 826349 1987591 := bstep (se 1 (by rfl) ⟨1490693, by rfl⟩ : syracuseStep 1987591 = 2981387) B2981387
theorem B9425969 : Blo 826349 9425969 := bstep (se 2 (by rfl) ⟨3534738, by rfl⟩ : syracuseStep 9425969 = 7069477) B7069477
theorem B2151481 : Blo 826349 2151481 := bstep (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) B1613611
theorem B1398235 : Blo 826349 1398235 := bstep (se 1 (by rfl) ⟨1048676, by rfl⟩ : syracuseStep 1398235 = 2097353) B2097353
theorem B4183649 : Blo 826349 4183649 := bstep (se 2 (by rfl) ⟨1568868, by rfl⟩ : syracuseStep 4183649 = 3137737) B3137737
theorem B3364487 : Blo 826349 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B841511 : Blo 826349 841511 := bstep (se 1 (by rfl) ⟨631133, by rfl⟩ : syracuseStep 841511 = 1262267) B1262267
theorem B1398863 : Blo 826349 1398863 := bstep (se 1 (by rfl) ⟨1049147, by rfl⟩ : syracuseStep 1398863 = 2098295) B2098295
theorem B49109579 : Blo 826349 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B1399727 : Blo 826349 1399727 := bstep (se 1 (by rfl) ⟨1049795, by rfl⟩ : syracuseStep 1399727 = 2099591) B2099591
theorem B10738615 : Blo 826349 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B4185107 : Blo 826349 4185107 := bstep (se 1 (by rfl) ⟨3138830, by rfl⟩ : syracuseStep 4185107 = 6277661) B6277661
theorem B1400159 : Blo 826349 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B10608317 : Blo 826349 10608317 := bstep (se 3 (by rfl) ⟨1989059, by rfl⟩ : syracuseStep 10608317 = 3978119) B3978119
theorem B3989191 : Blo 826349 3989191 := bstep (se 1 (by rfl) ⟨2991893, by rfl⟩ : syracuseStep 3989191 = 5983787) B5983787
theorem B11951887 : Blo 826349 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1859435 : Blo 826349 1859435 := bstep (se 1 (by rfl) ⟨1394576, by rfl⟩ : syracuseStep 1859435 = 2789153) B2789153
theorem B21520247 : Blo 826349 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B1400719 : Blo 826349 1400719 := bstep (se 1 (by rfl) ⟨1050539, by rfl⟩ : syracuseStep 1400719 = 2101079) B2101079
theorem B1859489 : Blo 826349 1859489 := bstep (se 2 (by rfl) ⟨697308, by rfl⟩ : syracuseStep 1859489 = 1394617) B1394617
theorem B1892279 : Blo 826349 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B7954361 : Blo 826349 7954361 := bstep (se 2 (by rfl) ⟨2982885, by rfl⟩ : syracuseStep 7954361 = 5965771) B5965771
theorem B3137555 : Blo 826349 3137555 := bstep (se 1 (by rfl) ⟨2353166, by rfl⟩ : syracuseStep 3137555 = 4706333) B4706333
theorem B6283493 : Blo 826349 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B1859831 : Blo 826349 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B3138011 : Blo 826349 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B1860425 : Blo 826349 1860425 := bstep (se 2 (by rfl) ⟨697659, by rfl⟩ : syracuseStep 1860425 = 1395319) B1395319
theorem B24896531 : Blo 826349 24896531 := bstep (se 1 (by rfl) ⟨18672398, by rfl⟩ : syracuseStep 24896531 = 37344797) B37344797
theorem B1861217 : Blo 826349 1861217 := bstep (se 2 (by rfl) ⟨697956, by rfl⟩ : syracuseStep 1861217 = 1395913) B1395913
theorem B3139195 : Blo 826349 3139195 := bstep (se 1 (by rfl) ⟨2354396, by rfl⟩ : syracuseStep 3139195 = 4708793) B4708793
theorem B6383393 : Blo 826349 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B2647903 : Blo 826349 2647903 := bstep (se 1 (by rfl) ⟨1985927, by rfl⟩ : syracuseStep 2647903 = 3971855) B3971855
theorem B4188023 : Blo 826349 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B1861559 : Blo 826349 1861559 := bstep (se 1 (by rfl) ⟨1396169, by rfl⟩ : syracuseStep 1861559 = 2792339) B2792339
theorem B10610777 : Blo 826349 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B17885285 : Blo 826349 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B32303447 : Blo 826349 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B26896819 : Blo 826349 26896819 := bstep (se 1 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 26896819 = 40345229) B40345229
theorem B1862153 : Blo 826349 1862153 := bstep (se 2 (by rfl) ⟨698307, by rfl⟩ : syracuseStep 1862153 = 1396615) B1396615
theorem B1862495 : Blo 826349 1862495 := bstep (se 1 (by rfl) ⟨1396871, by rfl⟩ : syracuseStep 1862495 = 2793743) B2793743
theorem B3140471 : Blo 826349 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B1239983 : Blo 826349 1239983 := bstep (se 1 (by rfl) ⟨929987, by rfl⟩ : syracuseStep 1239983 = 1859975) B1859975
theorem B2649095 : Blo 826349 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B1240073 : Blo 826349 1240073 := bstep (se 2 (by rfl) ⟨465027, by rfl⟩ : syracuseStep 1240073 = 930055) B930055
theorem B2649107 : Blo 826349 2649107 := bstep (se 1 (by rfl) ⟨1986830, by rfl⟩ : syracuseStep 2649107 = 3973661) B3973661
theorem B1862675 : Blo 826349 1862675 := bstep (se 1 (by rfl) ⟨1397006, by rfl⟩ : syracuseStep 1862675 = 2794013) B2794013
theorem B1240103 : Blo 826349 1240103 := bstep (se 1 (by rfl) ⟨930077, by rfl⟩ : syracuseStep 1240103 = 1860155) B1860155
theorem B5303339 : Blo 826349 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B1240187 : Blo 826349 1240187 := bstep (se 1 (by rfl) ⟨930140, by rfl⟩ : syracuseStep 1240187 = 1860281) B1860281
theorem B1240313 : Blo 826349 1240313 := bstep (se 2 (by rfl) ⟨465117, by rfl⟩ : syracuseStep 1240313 = 930235) B930235
theorem B14511395 : Blo 826349 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B1240415 : Blo 826349 1240415 := bstep (se 1 (by rfl) ⟨930311, by rfl⟩ : syracuseStep 1240415 = 1860623) B1860623
theorem B1863017 : Blo 826349 1863017 := bstep (se 2 (by rfl) ⟨698631, by rfl⟩ : syracuseStep 1863017 = 1397263) B1397263
theorem B1240427 : Blo 826349 1240427 := bstep (se 1 (by rfl) ⟨930320, by rfl⟩ : syracuseStep 1240427 = 1860641) B1860641
theorem B1437193 : Blo 826349 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B1240655 : Blo 826349 1240655 := bstep (se 1 (by rfl) ⟨930491, by rfl⟩ : syracuseStep 1240655 = 1860983) B1860983
theorem B1240775 : Blo 826349 1240775 := bstep (se 1 (by rfl) ⟨930581, by rfl⟩ : syracuseStep 1240775 = 1861163) B1861163
theorem B3141443 : Blo 826349 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B4714307 : Blo 826349 4714307 := bstep (se 1 (by rfl) ⟨3535730, by rfl⟩ : syracuseStep 4714307 = 7071461) B7071461
theorem B1240937 : Blo 826349 1240937 := bstep (se 2 (by rfl) ⟨465351, by rfl⟩ : syracuseStep 1240937 = 930703) B930703
theorem B1241015 : Blo 826349 1241015 := bstep (se 1 (by rfl) ⟨930761, by rfl⟩ : syracuseStep 1241015 = 1861523) B1861523
theorem B1863611 : Blo 826349 1863611 := bstep (se 1 (by rfl) ⟨1397708, by rfl⟩ : syracuseStep 1863611 = 2795417) B2795417
theorem B1241051 : Blo 826349 1241051 := bstep (se 1 (by rfl) ⟨930788, by rfl⟩ : syracuseStep 1241051 = 1861577) B1861577
theorem B1863737 : Blo 826349 1863737 := bstep (se 2 (by rfl) ⟨698901, by rfl⟩ : syracuseStep 1863737 = 1397803) B1397803
theorem B2093303 : Blo 826349 2093303 := bstep (se 1 (by rfl) ⟨1569977, by rfl⟩ : syracuseStep 2093303 = 3139955) B3139955
theorem B3141899 : Blo 826349 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B2355581 : Blo 826349 2355581 := bstep (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) B883343
theorem B1864079 : Blo 826349 1864079 := bstep (se 1 (by rfl) ⟨1398059, by rfl⟩ : syracuseStep 1864079 = 2796119) B2796119
theorem B1241519 : Blo 826349 1241519 := bstep (se 1 (by rfl) ⟨931139, by rfl⟩ : syracuseStep 1241519 = 1862279) B1862279
theorem B1569287 : Blo 826349 1569287 := bstep (se 1 (by rfl) ⟨1176965, by rfl⟩ : syracuseStep 1569287 = 2353931) B2353931
theorem B1241609 : Blo 826349 1241609 := bstep (se 2 (by rfl) ⟨465603, by rfl⟩ : syracuseStep 1241609 = 931207) B931207
theorem B1241639 : Blo 826349 1241639 := bstep (se 1 (by rfl) ⟨931229, by rfl⟩ : syracuseStep 1241639 = 1862459) B1862459
theorem B2650747 : Blo 826349 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B1241723 : Blo 826349 1241723 := bstep (se 1 (by rfl) ⟨931292, by rfl⟩ : syracuseStep 1241723 = 1862585) B1862585
theorem B1864403 : Blo 826349 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B1241849 : Blo 826349 1241849 := bstep (se 2 (by rfl) ⟨465693, by rfl⟩ : syracuseStep 1241849 = 931387) B931387
theorem B7959313 : Blo 826349 7959313 := bstep (se 2 (by rfl) ⟨2984742, by rfl⟩ : syracuseStep 7959313 = 5969485) B5969485
theorem B1241951 : Blo 826349 1241951 := bstep (se 1 (by rfl) ⟨931463, by rfl⟩ : syracuseStep 1241951 = 1862927) B1862927
theorem B1241963 : Blo 826349 1241963 := bstep (se 1 (by rfl) ⟨931472, by rfl⟩ : syracuseStep 1241963 = 1862945) B1862945
theorem B1569719 : Blo 826349 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B3142583 : Blo 826349 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B21787715 : Blo 826349 21787715 := bstep (se 1 (by rfl) ⟨16340786, by rfl⟩ : syracuseStep 21787715 = 32681573) B32681573
theorem B1569871 : Blo 826349 1569871 := bstep (se 1 (by rfl) ⟨1177403, by rfl⟩ : syracuseStep 1569871 = 2354807) B2354807
theorem B1242191 : Blo 826349 1242191 := bstep (se 1 (by rfl) ⟨931643, by rfl⟩ : syracuseStep 1242191 = 1863287) B1863287
theorem B1242311 : Blo 826349 1242311 := bstep (se 1 (by rfl) ⟨931733, by rfl⟩ : syracuseStep 1242311 = 1863467) B1863467
theorem B1242473 : Blo 826349 1242473 := bstep (se 2 (by rfl) ⟨465927, by rfl⟩ : syracuseStep 1242473 = 931855) B931855
theorem B1045867 : Blo 826349 1045867 := bstep (se 1 (by rfl) ⟨784400, by rfl⟩ : syracuseStep 1045867 = 1568801) B1568801
theorem B7075187 : Blo 826349 7075187 := bstep (se 1 (by rfl) ⟨5306390, by rfl⟩ : syracuseStep 7075187 = 10612781) B10612781
theorem B12776869 : Blo 826349 12776869 := bstep (se 4 (by rfl) ⟨1197831, by rfl⟩ : syracuseStep 12776869 = 2395663) B2395663
theorem B4257197 : Blo 826349 4257197 := bstep (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) B1596449
theorem B1242551 : Blo 826349 1242551 := bstep (se 1 (by rfl) ⟨931913, by rfl⟩ : syracuseStep 1242551 = 1863827) B1863827
theorem B1242587 : Blo 826349 1242587 := bstep (se 1 (by rfl) ⟨931940, by rfl⟩ : syracuseStep 1242587 = 1863881) B1863881
theorem B1865339 : Blo 826349 1865339 := bstep (se 1 (by rfl) ⟨1399004, by rfl⟩ : syracuseStep 1865339 = 2798009) B2798009
theorem B2094731 : Blo 826349 2094731 := bstep (se 1 (by rfl) ⟨1571048, by rfl⟩ : syracuseStep 2094731 = 3142097) B3142097
theorem B3143357 : Blo 826349 3143357 := bstep (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) B1178759
theorem B16971457 : Blo 826349 16971457 := bstep (se 2 (by rfl) ⟨6364296, by rfl⟩ : syracuseStep 16971457 = 12728593) B12728593
theorem B1865465 : Blo 826349 1865465 := bstep (se 2 (by rfl) ⟨699549, by rfl⟩ : syracuseStep 1865465 = 1399099) B1399099
theorem B21231395 : Blo 826349 21231395 := bstep (se 1 (by rfl) ⟨15923546, by rfl⟩ : syracuseStep 21231395 = 31847093) B31847093
theorem B2651977 : Blo 826349 2651977 := bstep (se 2 (by rfl) ⟨994491, by rfl⟩ : syracuseStep 2651977 = 1988983) B1988983
theorem B2094943 : Blo 826349 2094943 := bstep (se 1 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 2094943 = 3142415) B3142415
theorem B12089249 : Blo 826349 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B1243055 : Blo 826349 1243055 := bstep (se 1 (by rfl) ⟨932291, by rfl⟩ : syracuseStep 1243055 = 1864583) B1864583
theorem B1865735 : Blo 826349 1865735 := bstep (se 1 (by rfl) ⟨1399301, by rfl⟩ : syracuseStep 1865735 = 2798603) B2798603
theorem B1243145 : Blo 826349 1243145 := bstep (se 2 (by rfl) ⟨466179, by rfl⟩ : syracuseStep 1243145 = 932359) B932359
theorem B1243175 : Blo 826349 1243175 := bstep (se 1 (by rfl) ⟨932381, by rfl⟩ : syracuseStep 1243175 = 1864763) B1864763
theorem B1865807 : Blo 826349 1865807 := bstep (se 1 (by rfl) ⟨1399355, by rfl⟩ : syracuseStep 1865807 = 2798711) B2798711
theorem B1243259 : Blo 826349 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B2357495 : Blo 826349 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B1243385 : Blo 826349 1243385 := bstep (se 2 (by rfl) ⟨466269, by rfl⟩ : syracuseStep 1243385 = 932539) B932539
theorem B1243487 : Blo 826349 1243487 := bstep (se 1 (by rfl) ⟨932615, by rfl⟩ : syracuseStep 1243487 = 1865231) B1865231
theorem B1571177 : Blo 826349 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B3144041 : Blo 826349 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B1243499 : Blo 826349 1243499 := bstep (se 1 (by rfl) ⟨932624, by rfl⟩ : syracuseStep 1243499 = 1865249) B1865249
theorem B1079735 : Blo 826349 1079735 := bstep (se 1 (by rfl) ⟨809801, by rfl⟩ : syracuseStep 1079735 = 1619603) B1619603
theorem B2357723 : Blo 826349 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B1866203 : Blo 826349 1866203 := bstep (se 1 (by rfl) ⟨1399652, by rfl⟩ : syracuseStep 1866203 = 2799305) B2799305
theorem B1243727 : Blo 826349 1243727 := bstep (se 1 (by rfl) ⟨932795, by rfl⟩ : syracuseStep 1243727 = 1865591) B1865591
theorem B1047163 : Blo 826349 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B1243847 : Blo 826349 1243847 := bstep (se 1 (by rfl) ⟨932885, by rfl⟩ : syracuseStep 1243847 = 1865771) B1865771
theorem B2095865 : Blo 826349 2095865 := bstep (se 2 (by rfl) ⟨785949, by rfl⟩ : syracuseStep 2095865 = 1571899) B1571899
theorem B1244009 : Blo 826349 1244009 := bstep (se 2 (by rfl) ⟨466503, by rfl⟩ : syracuseStep 1244009 = 933007) B933007
theorem B1866671 : Blo 826349 1866671 := bstep (se 1 (by rfl) ⟨1400003, by rfl⟩ : syracuseStep 1866671 = 2800007) B2800007
theorem B4193207 : Blo 826349 4193207 := bstep (se 1 (by rfl) ⟨3144905, by rfl⟩ : syracuseStep 4193207 = 6289811) B6289811
theorem B1244087 : Blo 826349 1244087 := bstep (se 1 (by rfl) ⟨933065, by rfl⟩ : syracuseStep 1244087 = 1866131) B1866131
theorem B2128823 : Blo 826349 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B1244123 : Blo 826349 1244123 := bstep (se 1 (by rfl) ⟨933092, by rfl⟩ : syracuseStep 1244123 = 1866185) B1866185
theorem B4717541 : Blo 826349 4717541 := bstep (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) B884539
theorem B2653337 : Blo 826349 2653337 := bstep (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) B1990003
theorem B1866923 : Blo 826349 1866923 := bstep (se 1 (by rfl) ⟨1400192, by rfl⟩ : syracuseStep 1866923 = 2800385) B2800385
theorem B1572203 : Blo 826349 1572203 := bstep (se 1 (by rfl) ⟨1179152, by rfl⟩ : syracuseStep 1572203 = 2358305) B2358305
theorem B2096513 : Blo 826349 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B4717997 : Blo 826349 4717997 := bstep (se 3 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 4717997 = 1769249) B1769249
theorem B1244591 : Blo 826349 1244591 := bstep (se 1 (by rfl) ⟨933443, by rfl⟩ : syracuseStep 1244591 = 1866887) B1866887
theorem B2522611 : Blo 826349 2522611 := bstep (se 1 (by rfl) ⟨1891958, by rfl⟩ : syracuseStep 2522611 = 3783917) B3783917
theorem B1244681 : Blo 826349 1244681 := bstep (se 2 (by rfl) ⟨466755, by rfl⟩ : syracuseStep 1244681 = 933511) B933511
theorem B1244711 : Blo 826349 1244711 := bstep (se 1 (by rfl) ⟨933533, by rfl⟩ : syracuseStep 1244711 = 1867067) B1867067
theorem B1244795 : Blo 826349 1244795 := bstep (se 1 (by rfl) ⟨933596, by rfl⟩ : syracuseStep 1244795 = 1867193) B1867193
theorem B1867463 : Blo 826349 1867463 := bstep (se 1 (by rfl) ⟨1400597, by rfl⟩ : syracuseStep 1867463 = 2801195) B2801195
theorem B1244921 : Blo 826349 1244921 := bstep (se 2 (by rfl) ⟨466845, by rfl⟩ : syracuseStep 1244921 = 933691) B933691
theorem B8060705 : Blo 826349 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B2359135 : Blo 826349 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B1245023 : Blo 826349 1245023 := bstep (se 1 (by rfl) ⟨933767, by rfl⟩ : syracuseStep 1245023 = 1867535) B1867535
theorem B1245035 : Blo 826349 1245035 := bstep (se 1 (by rfl) ⟨933776, by rfl⟩ : syracuseStep 1245035 = 1867553) B1867553
theorem B2097161 : Blo 826349 2097161 := bstep (se 2 (by rfl) ⟨786435, by rfl⟩ : syracuseStep 2097161 = 1572871) B1572871
theorem B3145787 : Blo 826349 3145787 := bstep (se 1 (by rfl) ⟨2359340, by rfl⟩ : syracuseStep 3145787 = 4718681) B4718681
theorem B1704041 : Blo 826349 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B1245449 : Blo 826349 1245449 := bstep (se 2 (by rfl) ⟨467043, by rfl⟩ : syracuseStep 1245449 = 934087) B934087
theorem B2097515 : Blo 826349 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B5964299 : Blo 826349 5964299 := bstep (se 1 (by rfl) ⟨4473224, by rfl⟩ : syracuseStep 5964299 = 8946449) B8946449
theorem B2359979 : Blo 826349 2359979 := bstep (se 1 (by rfl) ⟨1769984, by rfl⟩ : syracuseStep 2359979 = 3539969) B3539969
theorem B2097839 : Blo 826349 2097839 := bstep (se 1 (by rfl) ⟨1573379, by rfl⟩ : syracuseStep 2097839 = 3146759) B3146759
theorem B6390521 : Blo 826349 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B4260601 : Blo 826349 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B4195151 : Blo 826349 4195151 := bstep (se 1 (by rfl) ⟨3146363, by rfl⟩ : syracuseStep 4195151 = 6292727) B6292727
theorem B4719455 : Blo 826349 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B2098163 : Blo 826349 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B4195475 : Blo 826349 4195475 := bstep (se 1 (by rfl) ⟨3146606, by rfl⟩ : syracuseStep 4195475 = 6293213) B6293213
theorem B1050023 : Blo 826349 1050023 := bstep (se 1 (by rfl) ⟨787517, by rfl⟩ : syracuseStep 1050023 = 1575035) B1575035
theorem B2098619 : Blo 826349 2098619 := bstep (se 1 (by rfl) ⟨1573964, by rfl⟩ : syracuseStep 2098619 = 3147929) B3147929
theorem B2360765 : Blo 826349 2360765 := bstep (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) B885287
theorem B1050175 : Blo 826349 1050175 := bstep (se 1 (by rfl) ⟨787631, by rfl⟩ : syracuseStep 1050175 = 1575263) B1575263
theorem B1050347 : Blo 826349 1050347 := bstep (se 1 (by rfl) ⟨787760, by rfl⟩ : syracuseStep 1050347 = 1575521) B1575521
theorem B7178129 : Blo 826349 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1771625 : Blo 826349 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B6293699 : Blo 826349 6293699 := bstep (se 1 (by rfl) ⟨4720274, by rfl⟩ : syracuseStep 6293699 = 9440549) B9440549
theorem B1182119 : Blo 826349 1182119 := bstep (se 1 (by rfl) ⟨886589, by rfl⟩ : syracuseStep 1182119 = 1773179) B1773179
theorem B2099783 : Blo 826349 2099783 := bstep (se 1 (by rfl) ⟨1574837, by rfl⟩ : syracuseStep 2099783 = 3149675) B3149675
theorem B3541643 : Blo 826349 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B66390749 : Blo 826349 66390749 := bstep (se 3 (by rfl) ⟨12448265, by rfl⟩ : syracuseStep 66390749 = 24896531) B24896531
theorem B58100573 : Blo 826349 58100573 := bstep (se 3 (by rfl) ⟨10893857, by rfl⟩ : syracuseStep 58100573 = 21787715) B21787715
theorem B2657195 : Blo 826349 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B7965773 : Blo 826349 7965773 := bstep (se 3 (by rfl) ⟨1493582, by rfl⟩ : syracuseStep 7965773 = 2987165) B2987165
theorem B1772923 : Blo 826349 1772923 := bstep (se 1 (by rfl) ⟨1329692, by rfl⟩ : syracuseStep 1772923 = 2659385) B2659385
theorem B2789099 : Blo 826349 2789099 := bstep (se 1 (by rfl) ⟨2091824, by rfl⟩ : syracuseStep 2789099 = 4183649) B4183649
theorem B2101049 : Blo 826349 2101049 := bstep (se 2 (by rfl) ⟨787893, by rfl⟩ : syracuseStep 2101049 = 1575787) B1575787
theorem B4198553 : Blo 826349 4198553 := bstep (se 2 (by rfl) ⟨1574457, by rfl⟩ : syracuseStep 4198553 = 3148915) B3148915
theorem B32739719 : Blo 826349 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B2790071 : Blo 826349 2790071 := bstep (se 1 (by rfl) ⟨2092553, by rfl⟩ : syracuseStep 2790071 = 4185107) B4185107
theorem B28677017 : Blo 826349 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B4199363 : Blo 826349 4199363 := bstep (se 1 (by rfl) ⟨3149522, by rfl⟩ : syracuseStep 4199363 = 6299045) B6299045
theorem B3544307 : Blo 826349 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B1676641 : Blo 826349 1676641 := bstep (se 2 (by rfl) ⟨628740, by rfl⟩ : syracuseStep 1676641 = 1257481) B1257481
theorem B7083557 : Blo 826349 7083557 := bstep (se 4 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 7083557 = 1328167) B1328167
theorem B14358059 : Blo 826349 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B2234017 : Blo 826349 2234017 := bstep (se 2 (by rfl) ⟨837756, by rfl⟩ : syracuseStep 2234017 = 1675513) B1675513
theorem B7084583 : Blo 826349 7084583 := bstep (se 1 (by rfl) ⟨5313437, by rfl⟩ : syracuseStep 7084583 = 10626875) B10626875
theorem B4725287 : Blo 826349 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B2792015 : Blo 826349 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B2235055 : Blo 826349 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B3545795 : Blo 826349 3545795 := bstep (se 1 (by rfl) ⟨2659346, by rfl⟩ : syracuseStep 3545795 = 5318693) B5318693
theorem B21535631 : Blo 826349 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B826655 : Blo 826349 826655 := bstep (se 1 (by rfl) ⟨619991, by rfl⟩ : syracuseStep 826655 = 1239983) B1239983
theorem B826715 : Blo 826349 826715 := bstep (se 1 (by rfl) ⟨620036, by rfl⟩ : syracuseStep 826715 = 1240073) B1240073
theorem B826735 : Blo 826349 826735 := bstep (se 1 (by rfl) ⟨620051, by rfl⟩ : syracuseStep 826735 = 1240103) B1240103
theorem B826791 : Blo 826349 826791 := bstep (se 1 (by rfl) ⟨620093, by rfl⟩ : syracuseStep 826791 = 1240187) B1240187
theorem B826875 : Blo 826349 826875 := bstep (se 1 (by rfl) ⟨620156, by rfl⟩ : syracuseStep 826875 = 1240313) B1240313
theorem B9674263 : Blo 826349 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B826943 : Blo 826349 826943 := bstep (se 1 (by rfl) ⟨620207, by rfl⟩ : syracuseStep 826943 = 1240415) B1240415
theorem B826951 : Blo 826349 826951 := bstep (se 1 (by rfl) ⟨620213, by rfl⟩ : syracuseStep 826951 = 1240427) B1240427
theorem B827103 : Blo 826349 827103 := bstep (se 1 (by rfl) ⟨620327, by rfl⟩ : syracuseStep 827103 = 1240655) B1240655
theorem B2793257 : Blo 826349 2793257 := bstep (se 2 (by rfl) ⟨1047471, by rfl⟩ : syracuseStep 2793257 = 2094943) B2094943
theorem B827183 : Blo 826349 827183 := bstep (se 1 (by rfl) ⟨620387, by rfl⟩ : syracuseStep 827183 = 1240775) B1240775
theorem B827291 : Blo 826349 827291 := bstep (se 1 (by rfl) ⟨620468, by rfl⟩ : syracuseStep 827291 = 1240937) B1240937
theorem B827343 : Blo 826349 827343 := bstep (se 1 (by rfl) ⟨620507, by rfl⟩ : syracuseStep 827343 = 1241015) B1241015
theorem B827367 : Blo 826349 827367 := bstep (se 1 (by rfl) ⟨620525, by rfl⟩ : syracuseStep 827367 = 1241051) B1241051
theorem B827679 : Blo 826349 827679 := bstep (se 1 (by rfl) ⟨620759, by rfl⟩ : syracuseStep 827679 = 1241519) B1241519
theorem B827739 : Blo 826349 827739 := bstep (se 1 (by rfl) ⟨620804, by rfl⟩ : syracuseStep 827739 = 1241609) B1241609
theorem B827759 : Blo 826349 827759 := bstep (se 1 (by rfl) ⟨620819, by rfl⟩ : syracuseStep 827759 = 1241639) B1241639
theorem B827815 : Blo 826349 827815 := bstep (se 1 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 827815 = 1241723) B1241723
theorem B4202927 : Blo 826349 4202927 := bstep (se 1 (by rfl) ⟨3152195, by rfl⟩ : syracuseStep 4202927 = 6304391) B6304391
theorem B827899 : Blo 826349 827899 := bstep (se 1 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 827899 = 1241849) B1241849
theorem B827967 : Blo 826349 827967 := bstep (se 1 (by rfl) ⟨620975, by rfl⟩ : syracuseStep 827967 = 1241951) B1241951
theorem B827975 : Blo 826349 827975 := bstep (se 1 (by rfl) ⟨620981, by rfl⟩ : syracuseStep 827975 = 1241963) B1241963
theorem B828127 : Blo 826349 828127 := bstep (se 1 (by rfl) ⟨621095, by rfl⟩ : syracuseStep 828127 = 1242191) B1242191
theorem B828207 : Blo 826349 828207 := bstep (se 1 (by rfl) ⟨621155, by rfl⟩ : syracuseStep 828207 = 1242311) B1242311
theorem B828315 : Blo 826349 828315 := bstep (se 1 (by rfl) ⟨621236, by rfl⟩ : syracuseStep 828315 = 1242473) B1242473
theorem B4727747 : Blo 826349 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B828367 : Blo 826349 828367 := bstep (se 1 (by rfl) ⟨621275, by rfl⟩ : syracuseStep 828367 = 1242551) B1242551
theorem B828391 : Blo 826349 828391 := bstep (se 1 (by rfl) ⟨621293, by rfl⟩ : syracuseStep 828391 = 1242587) B1242587
theorem B7087247 : Blo 826349 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B828703 : Blo 826349 828703 := bstep (se 1 (by rfl) ⟨621527, by rfl⟩ : syracuseStep 828703 = 1243055) B1243055
theorem B828763 : Blo 826349 828763 := bstep (se 1 (by rfl) ⟨621572, by rfl⟩ : syracuseStep 828763 = 1243145) B1243145
theorem B828783 : Blo 826349 828783 := bstep (se 1 (by rfl) ⟨621587, by rfl⟩ : syracuseStep 828783 = 1243175) B1243175
theorem B828839 : Blo 826349 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B828923 : Blo 826349 828923 := bstep (se 1 (by rfl) ⟨621692, by rfl⟩ : syracuseStep 828923 = 1243385) B1243385
theorem B828991 : Blo 826349 828991 := bstep (se 1 (by rfl) ⟨621743, by rfl⟩ : syracuseStep 828991 = 1243487) B1243487
theorem B992839 : Blo 826349 992839 := bstep (se 1 (by rfl) ⟨744629, by rfl⟩ : syracuseStep 992839 = 1489259) B1489259
theorem B828999 : Blo 826349 828999 := bstep (se 1 (by rfl) ⟨621749, by rfl⟩ : syracuseStep 828999 = 1243499) B1243499
theorem B4728455 : Blo 826349 4728455 := bstep (se 1 (by rfl) ⟨3546341, by rfl⟩ : syracuseStep 4728455 = 7092683) B7092683
theorem B829151 : Blo 826349 829151 := bstep (se 1 (by rfl) ⟨621863, by rfl⟩ : syracuseStep 829151 = 1243727) B1243727
theorem B829231 : Blo 826349 829231 := bstep (se 1 (by rfl) ⟨621923, by rfl⟩ : syracuseStep 829231 = 1243847) B1243847
theorem B993103 : Blo 826349 993103 := bstep (se 1 (by rfl) ⟨744827, by rfl⟩ : syracuseStep 993103 = 1489655) B1489655
theorem B2991953 : Blo 826349 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B829339 : Blo 826349 829339 := bstep (se 1 (by rfl) ⟨622004, by rfl⟩ : syracuseStep 829339 = 1244009) B1244009
theorem B2795471 : Blo 826349 2795471 := bstep (se 1 (by rfl) ⟨2096603, by rfl⟩ : syracuseStep 2795471 = 4193207) B4193207
theorem B829391 : Blo 826349 829391 := bstep (se 1 (by rfl) ⟨622043, by rfl⟩ : syracuseStep 829391 = 1244087) B1244087
theorem B1419215 : Blo 826349 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B829415 : Blo 826349 829415 := bstep (se 1 (by rfl) ⟨622061, by rfl⟩ : syracuseStep 829415 = 1244123) B1244123
theorem B6301961 : Blo 826349 6301961 := bstep (se 2 (by rfl) ⟨2363235, by rfl⟩ : syracuseStep 6301961 = 4726471) B4726471
theorem B5318921 : Blo 826349 5318921 := bstep (se 2 (by rfl) ⟨1994595, by rfl⟩ : syracuseStep 5318921 = 3989191) B3989191
theorem B829727 : Blo 826349 829727 := bstep (se 1 (by rfl) ⟨622295, by rfl⟩ : syracuseStep 829727 = 1244591) B1244591
theorem B57387325 : Blo 826349 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B829787 : Blo 826349 829787 := bstep (se 1 (by rfl) ⟨622340, by rfl⟩ : syracuseStep 829787 = 1244681) B1244681
theorem B15935849 : Blo 826349 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B829807 : Blo 826349 829807 := bstep (se 1 (by rfl) ⟨622355, by rfl⟩ : syracuseStep 829807 = 1244711) B1244711
theorem B829863 : Blo 826349 829863 := bstep (se 1 (by rfl) ⟨622397, by rfl⟩ : syracuseStep 829863 = 1244795) B1244795
theorem B829947 : Blo 826349 829947 := bstep (se 1 (by rfl) ⟨622460, by rfl⟩ : syracuseStep 829947 = 1244921) B1244921
theorem B830015 : Blo 826349 830015 := bstep (se 1 (by rfl) ⟨622511, by rfl⟩ : syracuseStep 830015 = 1245023) B1245023
theorem B830023 : Blo 826349 830023 := bstep (se 1 (by rfl) ⟨622517, by rfl⟩ : syracuseStep 830023 = 1245035) B1245035
theorem B830175 : Blo 826349 830175 := bstep (se 1 (by rfl) ⟨622631, by rfl⟩ : syracuseStep 830175 = 1245263) B1245263
theorem B830255 : Blo 826349 830255 := bstep (se 1 (by rfl) ⟨622691, by rfl⟩ : syracuseStep 830255 = 1245383) B1245383
theorem B4467581 : Blo 826349 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B2796443 : Blo 826349 2796443 := bstep (se 1 (by rfl) ⟨2097332, by rfl⟩ : syracuseStep 2796443 = 4194665) B4194665
theorem B3976411 : Blo 826349 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B14167385 : Blo 826349 14167385 := bstep (se 2 (by rfl) ⟨5312769, by rfl⟩ : syracuseStep 14167385 = 10625539) B10625539
theorem B2272607 : Blo 826349 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B2239933 : Blo 826349 2239933 := bstep (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) B839975
theorem B2797469 : Blo 826349 2797469 := bstep (se 3 (by rfl) ⟨524525, by rfl⟩ : syracuseStep 2797469 = 1049051) B1049051
theorem B929767 : Blo 826349 929767 := bstep (se 1 (by rfl) ⟨697325, by rfl⟩ : syracuseStep 929767 = 1394651) B1394651
theorem B2797577 : Blo 826349 2797577 := bstep (se 2 (by rfl) ⟨1049091, by rfl⟩ : syracuseStep 2797577 = 2098183) B2098183
theorem B3977545 : Blo 826349 3977545 := bstep (se 2 (by rfl) ⟨1491579, by rfl⟩ : syracuseStep 3977545 = 2983159) B2983159
theorem B21475793 : Blo 826349 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B11940473 : Blo 826349 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B7091347 : Blo 826349 7091347 := bstep (se 1 (by rfl) ⟨5318510, by rfl⟩ : syracuseStep 7091347 = 10637021) B10637021
theorem B10597655 : Blo 826349 10597655 := bstep (se 1 (by rfl) ⟨7948241, by rfl⟩ : syracuseStep 10597655 = 15896483) B15896483
theorem B7976231 : Blo 826349 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B931423 : Blo 826349 931423 := bstep (se 1 (by rfl) ⟨698567, by rfl⟩ : syracuseStep 931423 = 1397135) B1397135
theorem B997039 : Blo 826349 997039 := bstep (se 1 (by rfl) ⟨747779, by rfl⟩ : syracuseStep 997039 = 1495559) B1495559
theorem B35862425 : Blo 826349 35862425 := bstep (se 2 (by rfl) ⟨13448409, by rfl⟩ : syracuseStep 35862425 = 26896819) B26896819
theorem B3979543 : Blo 826349 3979543 := bstep (se 1 (by rfl) ⟨2984657, by rfl⟩ : syracuseStep 3979543 = 5969315) B5969315
theorem B2242991 : Blo 826349 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B5814823 : Blo 826349 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B932575 : Blo 826349 932575 := bstep (se 1 (by rfl) ⟨699431, by rfl⟩ : syracuseStep 932575 = 1398863) B1398863
theorem B1489835 : Blo 826349 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B2800763 : Blo 826349 2800763 := bstep (se 1 (by rfl) ⟨2100572, by rfl⟩ : syracuseStep 2800763 = 4201145) B4201145
theorem B933151 : Blo 826349 933151 := bstep (se 1 (by rfl) ⟨699863, by rfl⟩ : syracuseStep 933151 = 1399727) B1399727
theorem B1916257 : Blo 826349 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B2801033 : Blo 826349 2801033 := bstep (se 2 (by rfl) ⟨1050387, by rfl⟩ : syracuseStep 2801033 = 2100775) B2100775
theorem B2244029 : Blo 826349 2244029 := bstep (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) B841511
theorem B7061003 : Blo 826349 7061003 := bstep (se 1 (by rfl) ⟨5295752, by rfl⟩ : syracuseStep 7061003 = 10591505) B10591505
theorem B933439 : Blo 826349 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B4472617 : Blo 826349 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B2801465 : Blo 826349 2801465 := bstep (se 2 (by rfl) ⟨1050549, by rfl⟩ : syracuseStep 2801465 = 2101099) B2101099
theorem B3785287 : Blo 826349 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B2802329 : Blo 826349 2802329 := bstep (se 2 (by rfl) ⟨1050873, by rfl⟩ : syracuseStep 2802329 = 2101747) B2101747
theorem B441762497 : Blo 826349 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B4244183 : Blo 826349 4244183 := bstep (se 1 (by rfl) ⟨3183137, by rfl⟩ : syracuseStep 4244183 = 6366275) B6366275
theorem B7980227 : Blo 826349 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B2868641 : Blo 826349 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B1885639 : Blo 826349 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B1394489 : Blo 826349 1394489 := bstep (se 2 (by rfl) ⟨522933, by rfl⟩ : syracuseStep 1394489 = 1045867) B1045867
theorem B22628609 : Blo 826349 22628609 := bstep (se 2 (by rfl) ⟨8485728, by rfl⟩ : syracuseStep 22628609 = 16971457) B16971457
theorem B28756727 : Blo 826349 28756727 := bstep (se 1 (by rfl) ⟨21567545, by rfl⟩ : syracuseStep 28756727 = 43135091) B43135091
theorem B1395535 : Blo 826349 1395535 := bstep (se 1 (by rfl) ⟨1046651, by rfl⟩ : syracuseStep 1395535 = 2093303) B2093303
theorem B13421483 : Blo 826349 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B5295547 : Blo 826349 5295547 := bstep (se 1 (by rfl) ⟨3971660, by rfl⟩ : syracuseStep 5295547 = 7943321) B7943321
theorem B1396217 : Blo 826349 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B1494521 : Blo 826349 1494521 := bstep (se 2 (by rfl) ⟨560445, by rfl⟩ : syracuseStep 1494521 = 1120891) B1120891
theorem B2838131 : Blo 826349 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B1396487 : Blo 826349 1396487 := bstep (se 1 (by rfl) ⟨1047365, by rfl⟩ : syracuseStep 1396487 = 2094731) B2094731
theorem B3985193 : Blo 826349 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B1397243 : Blo 826349 1397243 := bstep (se 1 (by rfl) ⟨1047932, by rfl⟩ : syracuseStep 1397243 = 2095865) B2095865
theorem B3363481 : Blo 826349 3363481 := bstep (se 2 (by rfl) ⟨1261305, by rfl⟩ : syracuseStep 3363481 = 2522611) B2522611
theorem B1397675 : Blo 826349 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B3986423 : Blo 826349 3986423 := bstep (se 1 (by rfl) ⟨2989817, by rfl⟩ : syracuseStep 3986423 = 5979635) B5979635
theorem B1889659 : Blo 826349 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B1398215 : Blo 826349 1398215 := bstep (se 1 (by rfl) ⟨1048661, by rfl⟩ : syracuseStep 1398215 = 2097323) B2097323
theorem B1791571 : Blo 826349 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B4249273 : Blo 826349 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B35739407 : Blo 826349 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B841519 : Blo 826349 841519 := bstep (se 1 (by rfl) ⟨631139, by rfl⟩ : syracuseStep 841519 = 1262279) B1262279
theorem B6281549 : Blo 826349 6281549 := bstep (se 3 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 6281549 = 2355581) B2355581
theorem B1988975 : Blo 826349 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B1399207 : Blo 826349 1399207 := bstep (se 1 (by rfl) ⟨1049405, by rfl⟩ : syracuseStep 1399207 = 2098811) B2098811
theorem B1399369 : Blo 826349 1399369 := bstep (se 2 (by rfl) ⟨524763, by rfl⟩ : syracuseStep 1399369 = 1049527) B1049527
theorem B1399403 : Blo 826349 1399403 := bstep (se 1 (by rfl) ⟨1049552, by rfl⟩ : syracuseStep 1399403 = 2099105) B2099105
theorem B4250747 : Blo 826349 4250747 := bstep (se 1 (by rfl) ⟨3188060, by rfl⟩ : syracuseStep 4250747 = 6376121) B6376121
theorem B21192029 : Blo 826349 21192029 := bstep (se 3 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 21192029 = 7947011) B7947011
theorem B1989983 : Blo 826349 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B4185593 : Blo 826349 4185593 := bstep (se 2 (by rfl) ⟨1569597, by rfl⟩ : syracuseStep 4185593 = 3139195) B3139195
theorem B3530537 : Blo 826349 3530537 := bstep (se 2 (by rfl) ⟨1323951, by rfl⟩ : syracuseStep 3530537 = 2647903) B2647903
theorem B4185917 : Blo 826349 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B4710251 : Blo 826349 4710251 := bstep (se 1 (by rfl) ⟨3532688, by rfl⟩ : syracuseStep 4710251 = 7065377) B7065377
theorem B1859795 : Blo 826349 1859795 := bstep (se 1 (by rfl) ⟨1394846, by rfl⟩ : syracuseStep 1859795 = 2789693) B2789693
theorem B1859849 : Blo 826349 1859849 := bstep (se 2 (by rfl) ⟨697443, by rfl⟩ : syracuseStep 1859849 = 1394887) B1394887
theorem B1401097 : Blo 826349 1401097 := bstep (se 2 (by rfl) ⟨525411, by rfl⟩ : syracuseStep 1401097 = 1050823) B1050823
theorem B1860065 : Blo 826349 1860065 := bstep (se 2 (by rfl) ⟨697524, by rfl⟩ : syracuseStep 1860065 = 1395049) B1395049
theorem B4842155 : Blo 826349 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B6283979 : Blo 826349 6283979 := bstep (se 1 (by rfl) ⟨4712984, by rfl⟩ : syracuseStep 6283979 = 9425969) B9425969
theorem B1860371 : Blo 826349 1860371 := bstep (se 1 (by rfl) ⟨1395278, by rfl⟩ : syracuseStep 1860371 = 2790557) B2790557
theorem B1860731 : Blo 826349 1860731 := bstep (se 1 (by rfl) ⟨1395548, by rfl⟩ : syracuseStep 1860731 = 2791097) B2791097
theorem B1860857 : Blo 826349 1860857 := bstep (se 2 (by rfl) ⟨697821, by rfl⟩ : syracuseStep 1860857 = 1395643) B1395643
theorem B1861001 : Blo 826349 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B1009147 : Blo 826349 1009147 := bstep (se 1 (by rfl) ⟨756860, by rfl⟩ : syracuseStep 1009147 = 1513721) B1513721
theorem B1861127 : Blo 826349 1861127 := bstep (se 1 (by rfl) ⟨1395845, by rfl⟩ : syracuseStep 1861127 = 2791691) B2791691
theorem B1861307 : Blo 826349 1861307 := bstep (se 1 (by rfl) ⟨1395980, by rfl⟩ : syracuseStep 1861307 = 2791961) B2791961
theorem B1861433 : Blo 826349 1861433 := bstep (se 2 (by rfl) ⟨698037, by rfl⟩ : syracuseStep 1861433 = 1396075) B1396075
theorem B4417361 : Blo 826349 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B1862063 : Blo 826349 1862063 := bstep (se 1 (by rfl) ⟨1396547, by rfl⟩ : syracuseStep 1862063 = 2793095) B2793095
theorem B1862099 : Blo 826349 1862099 := bstep (se 1 (by rfl) ⟨1396574, by rfl⟩ : syracuseStep 1862099 = 2793149) B2793149
theorem B7072211 : Blo 826349 7072211 := bstep (se 1 (by rfl) ⟨5304158, by rfl⟩ : syracuseStep 7072211 = 10608317) B10608317
theorem B22932013 : Blo 826349 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B1862207 : Blo 826349 1862207 := bstep (se 1 (by rfl) ⟨1396655, by rfl⟩ : syracuseStep 1862207 = 2793311) B2793311
theorem B1239623 : Blo 826349 1239623 := bstep (se 1 (by rfl) ⟨929717, by rfl⟩ : syracuseStep 1239623 = 1859435) B1859435
theorem B1239659 : Blo 826349 1239659 := bstep (se 1 (by rfl) ⟨929744, by rfl⟩ : syracuseStep 1239659 = 1859489) B1859489
theorem B5302907 : Blo 826349 5302907 := bstep (se 1 (by rfl) ⟨3977180, by rfl⟩ : syracuseStep 5302907 = 7954361) B7954361
theorem B1862315 : Blo 826349 1862315 := bstep (se 1 (by rfl) ⟨1396736, by rfl⟩ : syracuseStep 1862315 = 2793473) B2793473
theorem B2091703 : Blo 826349 2091703 := bstep (se 1 (by rfl) ⟨1568777, by rfl⟩ : syracuseStep 2091703 = 3137555) B3137555
theorem B16116413 : Blo 826349 16116413 := bstep (se 3 (by rfl) ⟨3021827, by rfl⟩ : syracuseStep 16116413 = 6043655) B6043655
theorem B1993463 : Blo 826349 1993463 := bstep (se 1 (by rfl) ⟨1495097, by rfl⟩ : syracuseStep 1993463 = 2990195) B2990195
theorem B4188995 : Blo 826349 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B1239887 : Blo 826349 1239887 := bstep (se 1 (by rfl) ⟨929915, by rfl⟩ : syracuseStep 1239887 = 1859831) B1859831
theorem B2092007 : Blo 826349 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B1862855 : Blo 826349 1862855 := bstep (se 1 (by rfl) ⟨1397141, by rfl⟩ : syracuseStep 1862855 = 2794283) B2794283
theorem B1240283 : Blo 826349 1240283 := bstep (se 1 (by rfl) ⟨930212, by rfl⟩ : syracuseStep 1240283 = 1860425) B1860425
theorem B1863035 : Blo 826349 1863035 := bstep (se 1 (by rfl) ⟨1397276, by rfl⟩ : syracuseStep 1863035 = 2794553) B2794553
theorem B1240457 : Blo 826349 1240457 := bstep (se 2 (by rfl) ⟨465171, by rfl⟩ : syracuseStep 1240457 = 930343) B930343
theorem B3534329 : Blo 826349 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B1863161 : Blo 826349 1863161 := bstep (se 2 (by rfl) ⟨698685, by rfl⟩ : syracuseStep 1863161 = 1397371) B1397371
theorem B1863251 : Blo 826349 1863251 := bstep (se 1 (by rfl) ⟨1397438, by rfl⟩ : syracuseStep 1863251 = 2794877) B2794877
theorem B4189805 : Blo 826349 4189805 := bstep (se 3 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 4189805 = 1571177) B1571177
theorem B10612417 : Blo 826349 10612417 := bstep (se 2 (by rfl) ⟨3979656, by rfl⟩ : syracuseStep 10612417 = 7959313) B7959313
theorem B1240811 : Blo 826349 1240811 := bstep (se 1 (by rfl) ⟨930608, by rfl⟩ : syracuseStep 1240811 = 1861217) B1861217
theorem B5664491 : Blo 826349 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B1863431 : Blo 826349 1863431 := bstep (se 1 (by rfl) ⟨1397573, by rfl⟩ : syracuseStep 1863431 = 2795147) B2795147
theorem B2879293 : Blo 826349 2879293 := bstep (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) B1079735
theorem B4255595 : Blo 826349 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B1241039 : Blo 826349 1241039 := bstep (se 1 (by rfl) ⟨930779, by rfl⟩ : syracuseStep 1241039 = 1861559) B1861559
theorem B2650121 : Blo 826349 2650121 := bstep (se 2 (by rfl) ⟨993795, by rfl⟩ : syracuseStep 2650121 = 1987591) B1987591
theorem B7073851 : Blo 826349 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B11923523 : Blo 826349 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B2093161 : Blo 826349 2093161 := bstep (se 2 (by rfl) ⟨784935, by rfl⟩ : syracuseStep 2093161 = 1569871) B1569871
theorem B7958699 : Blo 826349 7958699 := bstep (se 1 (by rfl) ⟨5969024, by rfl⟩ : syracuseStep 7958699 = 11938049) B11938049
theorem B1241435 : Blo 826349 1241435 := bstep (se 1 (by rfl) ⟨931076, by rfl⟩ : syracuseStep 1241435 = 1862153) B1862153
theorem B1864043 : Blo 826349 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B1864187 : Blo 826349 1864187 := bstep (se 1 (by rfl) ⟨1398140, by rfl⟩ : syracuseStep 1864187 = 2796281) B2796281
theorem B17035825 : Blo 826349 17035825 := bstep (se 2 (by rfl) ⟨6388434, by rfl⟩ : syracuseStep 17035825 = 12776869) B12776869
theorem B1241663 : Blo 826349 1241663 := bstep (se 1 (by rfl) ⟨931247, by rfl⟩ : syracuseStep 1241663 = 1862495) B1862495
theorem B2093647 : Blo 826349 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B7959161 : Blo 826349 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B1864313 : Blo 826349 1864313 := bstep (se 2 (by rfl) ⟨699117, by rfl⟩ : syracuseStep 1864313 = 1398235) B1398235
theorem B1766063 : Blo 826349 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B1864367 : Blo 826349 1864367 := bstep (se 1 (by rfl) ⟨1398275, by rfl⟩ : syracuseStep 1864367 = 2796551) B2796551
theorem B1766071 : Blo 826349 1766071 := bstep (se 1 (by rfl) ⟨1324553, by rfl⟩ : syracuseStep 1766071 = 2649107) B2649107
theorem B1241783 : Blo 826349 1241783 := bstep (se 1 (by rfl) ⟨931337, by rfl⟩ : syracuseStep 1241783 = 1862675) B1862675
theorem B3535559 : Blo 826349 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B1864439 : Blo 826349 1864439 := bstep (se 1 (by rfl) ⟨1398329, by rfl⟩ : syracuseStep 1864439 = 2796659) B2796659
theorem B1242011 : Blo 826349 1242011 := bstep (se 1 (by rfl) ⟨931508, by rfl⟩ : syracuseStep 1242011 = 1863017) B1863017
theorem B1864619 : Blo 826349 1864619 := bstep (se 1 (by rfl) ⟨1398464, by rfl⟩ : syracuseStep 1864619 = 2796929) B2796929
theorem B3535969 : Blo 826349 3535969 := bstep (se 2 (by rfl) ⟨1325988, by rfl⟩ : syracuseStep 3535969 = 2651977) B2651977
theorem B2094295 : Blo 826349 2094295 := bstep (se 1 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 2094295 = 3141443) B3141443
theorem B3142871 : Blo 826349 3142871 := bstep (se 1 (by rfl) ⟨2357153, by rfl⟩ : syracuseStep 3142871 = 4714307) B4714307
theorem B1242407 : Blo 826349 1242407 := bstep (se 1 (by rfl) ⟨931805, by rfl⟩ : syracuseStep 1242407 = 1863611) B1863611
theorem B1242491 : Blo 826349 1242491 := bstep (se 1 (by rfl) ⟨931868, by rfl⟩ : syracuseStep 1242491 = 1863737) B1863737
theorem B1865159 : Blo 826349 1865159 := bstep (se 1 (by rfl) ⟨1398869, by rfl⟩ : syracuseStep 1865159 = 2797739) B2797739
theorem B1242617 : Blo 826349 1242617 := bstep (se 2 (by rfl) ⟨465981, by rfl⟩ : syracuseStep 1242617 = 931963) B931963
theorem B2094599 : Blo 826349 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B1242719 : Blo 826349 1242719 := bstep (se 1 (by rfl) ⟨932039, by rfl⟩ : syracuseStep 1242719 = 1864079) B1864079
theorem B1046191 : Blo 826349 1046191 := bstep (se 1 (by rfl) ⟨784643, by rfl⟩ : syracuseStep 1046191 = 1569287) B1569287
theorem B1865519 : Blo 826349 1865519 := bstep (se 1 (by rfl) ⟨1399139, by rfl⟩ : syracuseStep 1865519 = 2798279) B2798279
theorem B1242935 : Blo 826349 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B2095055 : Blo 826349 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B1243241 : Blo 826349 1243241 := bstep (se 2 (by rfl) ⟨466215, by rfl⟩ : syracuseStep 1243241 = 932431) B932431
theorem B4716791 : Blo 826349 4716791 := bstep (se 1 (by rfl) ⟨3537593, by rfl⟩ : syracuseStep 4716791 = 7075187) B7075187
theorem B1866095 : Blo 826349 1866095 := bstep (se 1 (by rfl) ⟨1399571, by rfl⟩ : syracuseStep 1866095 = 2799143) B2799143
theorem B1243559 : Blo 826349 1243559 := bstep (se 1 (by rfl) ⟨932669, by rfl⟩ : syracuseStep 1243559 = 1865339) B1865339
theorem B1866167 : Blo 826349 1866167 := bstep (se 1 (by rfl) ⟨1399625, by rfl⟩ : syracuseStep 1866167 = 2799251) B2799251
theorem B2095571 : Blo 826349 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B1243643 : Blo 826349 1243643 := bstep (se 1 (by rfl) ⟨932732, by rfl⟩ : syracuseStep 1243643 = 1865465) B1865465
theorem B2128403 : Blo 826349 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B14154263 : Blo 826349 14154263 := bstep (se 1 (by rfl) ⟨10615697, by rfl⟩ : syracuseStep 14154263 = 21231395) B21231395
theorem B883271 : Blo 826349 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B14318153 : Blo 826349 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B1866311 : Blo 826349 1866311 := bstep (se 1 (by rfl) ⟨1399733, by rfl⟩ : syracuseStep 1866311 = 2799467) B2799467
theorem B8059499 : Blo 826349 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B1866347 : Blo 826349 1866347 := bstep (se 1 (by rfl) ⟨1399760, by rfl⟩ : syracuseStep 1866347 = 2799521) B2799521
theorem B1243769 : Blo 826349 1243769 := bstep (se 2 (by rfl) ⟨466413, by rfl⟩ : syracuseStep 1243769 = 932827) B932827
theorem B33094277 : Blo 826349 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B1243823 : Blo 826349 1243823 := bstep (se 1 (by rfl) ⟨932867, by rfl⟩ : syracuseStep 1243823 = 1865735) B1865735
theorem B1243871 : Blo 826349 1243871 := bstep (se 1 (by rfl) ⟨932903, by rfl⟩ : syracuseStep 1243871 = 1865807) B1865807
theorem B1571663 : Blo 826349 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B2096027 : Blo 826349 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B1571815 : Blo 826349 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B1244135 : Blo 826349 1244135 := bstep (se 1 (by rfl) ⟨933101, by rfl⟩ : syracuseStep 1244135 = 1866203) B1866203
theorem B1866743 : Blo 826349 1866743 := bstep (se 1 (by rfl) ⟨1400057, by rfl⟩ : syracuseStep 1866743 = 2800115) B2800115
theorem B1244393 : Blo 826349 1244393 := bstep (se 2 (by rfl) ⟨466647, by rfl⟩ : syracuseStep 1244393 = 933295) B933295
theorem B1244447 : Blo 826349 1244447 := bstep (se 1 (by rfl) ⟨933335, by rfl⟩ : syracuseStep 1244447 = 1866671) B1866671
theorem B3145027 : Blo 826349 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B1867103 : Blo 826349 1867103 := bstep (se 1 (by rfl) ⟨1400327, by rfl⟩ : syracuseStep 1867103 = 2800655) B2800655
theorem B1768891 : Blo 826349 1768891 := bstep (se 1 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 1768891 = 2653337) B2653337
theorem B1244615 : Blo 826349 1244615 := bstep (se 1 (by rfl) ⟨933461, by rfl⟩ : syracuseStep 1244615 = 1866923) B1866923
theorem B1048135 : Blo 826349 1048135 := bstep (se 1 (by rfl) ⟨786101, by rfl⟩ : syracuseStep 1048135 = 1572203) B1572203
theorem B3145331 : Blo 826349 3145331 := bstep (se 1 (by rfl) ⟨2358998, by rfl⟩ : syracuseStep 3145331 = 4717997) B4717997
theorem B1867499 : Blo 826349 1867499 := bstep (se 1 (by rfl) ⟨1400624, by rfl⟩ : syracuseStep 1867499 = 2801249) B2801249
theorem B3145513 : Blo 826349 3145513 := bstep (se 2 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 3145513 = 2359135) B2359135
theorem B1244969 : Blo 826349 1244969 := bstep (se 2 (by rfl) ⟨466863, by rfl⟩ : syracuseStep 1244969 = 933727) B933727
theorem B1244975 : Blo 826349 1244975 := bstep (se 1 (by rfl) ⟨933731, by rfl⟩ : syracuseStep 1244975 = 1867463) B1867463
theorem B5046077 : Blo 826349 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B1867625 : Blo 826349 1867625 := bstep (se 2 (by rfl) ⟨700359, by rfl⟩ : syracuseStep 1867625 = 1400719) B1400719
theorem B5373803 : Blo 826349 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B2097191 : Blo 826349 2097191 := bstep (se 1 (by rfl) ⟨1572893, by rfl⟩ : syracuseStep 2097191 = 3145787) B3145787
theorem B1868129 : Blo 826349 1868129 := bstep (se 2 (by rfl) ⟨700548, by rfl⟩ : syracuseStep 1868129 = 1401097) B1401097
theorem B1868219 : Blo 826349 1868219 := bstep (se 1 (by rfl) ⟨1401164, by rfl⟩ : syracuseStep 1868219 = 2802329) B2802329
theorem B1573319 : Blo 826349 1573319 := bstep (se 1 (by rfl) ⟨1179989, by rfl⟩ : syracuseStep 1573319 = 2359979) B2359979
theorem B4260347 : Blo 826349 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B3146303 : Blo 826349 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B5047049 : Blo 826349 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B1573843 : Blo 826349 1573843 := bstep (se 1 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 1573843 = 2360765) B2360765
theorem B4785419 : Blo 826349 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B1181083 : Blo 826349 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B4195799 : Blo 826349 4195799 := bstep (se 1 (by rfl) ⟨3146849, by rfl⟩ : syracuseStep 4195799 = 6293699) B6293699
theorem B2361095 : Blo 826349 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B19171151 : Blo 826349 19171151 := bstep (se 1 (by rfl) ⟨14378363, by rfl⟩ : syracuseStep 19171151 = 28756727) B28756727
theorem B38733715 : Blo 826349 38733715 := bstep (se 1 (by rfl) ⟨29050286, by rfl⟩ : syracuseStep 38733715 = 58100573) B58100573
theorem B8947655 : Blo 826349 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B1771463 : Blo 826349 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B1345529 : Blo 826349 1345529 := bstep (se 2 (by rfl) ⟨504573, by rfl⟩ : syracuseStep 1345529 = 1009147) B1009147
theorem B5310515 : Blo 826349 5310515 := bstep (se 1 (by rfl) ⟨3982886, by rfl⟩ : syracuseStep 5310515 = 7965773) B7965773
theorem B2656795 : Blo 826349 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B76516433 : Blo 826349 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B2657615 : Blo 826349 2657615 := bstep (se 1 (by rfl) ⟨1993211, by rfl⟩ : syracuseStep 2657615 = 3986423) B3986423
theorem B30576017 : Blo 826349 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B2362871 : Blo 826349 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B2788937 : Blo 826349 2788937 := bstep (se 2 (by rfl) ⟨1045851, by rfl⟩ : syracuseStep 2788937 = 2091703) B2091703
theorem B4722371 : Blo 826349 4722371 := bstep (se 1 (by rfl) ⟨3541778, by rfl⟩ : syracuseStep 4722371 = 7083557) B7083557
theorem B9572039 : Blo 826349 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B23826271 : Blo 826349 23826271 := bstep (se 1 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 23826271 = 35739407) B35739407
theorem B4723055 : Blo 826349 4723055 := bstep (se 1 (by rfl) ⟨3542291, by rfl⟩ : syracuseStep 4723055 = 7084583) B7084583
theorem B3150191 : Blo 826349 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B2363863 : Blo 826349 2363863 := bstep (se 1 (by rfl) ⟨1772897, by rfl⟩ : syracuseStep 2363863 = 3545795) B3545795
theorem B2363897 : Blo 826349 2363897 := bstep (se 2 (by rfl) ⟨886461, by rfl⟩ : syracuseStep 2363897 = 1772923) B1772923
theorem B2986577 : Blo 826349 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B14357087 : Blo 826349 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B14128019 : Blo 826349 14128019 := bstep (se 1 (by rfl) ⟨10596014, by rfl⟩ : syracuseStep 14128019 = 21192029) B21192029
theorem B2790395 : Blo 826349 2790395 := bstep (se 1 (by rfl) ⟨2092796, by rfl⟩ : syracuseStep 2790395 = 4185593) B4185593
theorem B3839057 : Blo 826349 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B2790611 : Blo 826349 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B2790881 : Blo 826349 2790881 := bstep (se 2 (by rfl) ⟨1046580, by rfl⟩ : syracuseStep 2790881 = 2093161) B2093161
theorem B3151831 : Blo 826349 3151831 := bstep (se 1 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 3151831 = 4727747) B4727747
theorem B22714433 : Blo 826349 22714433 := bstep (se 2 (by rfl) ⟨8517912, by rfl⟩ : syracuseStep 22714433 = 17035825) B17035825
theorem B4724831 : Blo 826349 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B2791529 : Blo 826349 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B3152303 : Blo 826349 3152303 := bstep (se 1 (by rfl) ⟨2364227, by rfl⟩ : syracuseStep 3152303 = 4728455) B4728455
theorem B3152317 : Blo 826349 3152317 := bstep (se 3 (by rfl) ⟨591059, by rfl⟩ : syracuseStep 3152317 = 1182119) B1182119
theorem B5675741 : Blo 826349 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B4201307 : Blo 826349 4201307 := bstep (se 1 (by rfl) ⟨3150980, by rfl⟩ : syracuseStep 4201307 = 6301961) B6301961
theorem B3545947 : Blo 826349 3545947 := bstep (se 1 (by rfl) ⟨2659460, by rfl⟩ : syracuseStep 3545947 = 5318921) B5318921
theorem B10623899 : Blo 826349 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B2792393 : Blo 826349 2792393 := bstep (se 2 (by rfl) ⟨1047147, by rfl⟩ : syracuseStep 2792393 = 2094295) B2094295
theorem B826415 : Blo 826349 826415 := bstep (se 1 (by rfl) ⟨619811, by rfl⟩ : syracuseStep 826415 = 1239623) B1239623
theorem B826439 : Blo 826349 826439 := bstep (se 1 (by rfl) ⟨619829, by rfl⟩ : syracuseStep 826439 = 1239659) B1239659
theorem B2235521 : Blo 826349 2235521 := bstep (se 2 (by rfl) ⟨838320, by rfl⟩ : syracuseStep 2235521 = 1676641) B1676641
theorem B2792663 : Blo 826349 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B826591 : Blo 826349 826591 := bstep (se 1 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 826591 = 1239887) B1239887
theorem B171908405 : Blo 826349 171908405 := bstep (se 5 (by rfl) ⟨8058206, by rfl⟩ : syracuseStep 171908405 = 16116413) B16116413
theorem B826855 : Blo 826349 826855 := bstep (se 1 (by rfl) ⟨620141, by rfl⟩ : syracuseStep 826855 = 1240283) B1240283
theorem B9444923 : Blo 826349 9444923 := bstep (se 1 (by rfl) ⟨7083692, by rfl⟩ : syracuseStep 9444923 = 14167385) B14167385
theorem B1515071 : Blo 826349 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B826971 : Blo 826349 826971 := bstep (se 1 (by rfl) ⟨620228, by rfl⟩ : syracuseStep 826971 = 1240457) B1240457
theorem B2793203 : Blo 826349 2793203 := bstep (se 1 (by rfl) ⟨2094902, by rfl⟩ : syracuseStep 2793203 = 4189805) B4189805
theorem B827207 : Blo 826349 827207 := bstep (se 1 (by rfl) ⟨620405, by rfl⟩ : syracuseStep 827207 = 1240811) B1240811
theorem B3776327 : Blo 826349 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B827359 : Blo 826349 827359 := bstep (se 1 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 827359 = 1241039) B1241039
theorem B827623 : Blo 826349 827623 := bstep (se 1 (by rfl) ⟨620717, by rfl⟩ : syracuseStep 827623 = 1241435) B1241435
theorem B827775 : Blo 826349 827775 := bstep (se 1 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 827775 = 1241663) B1241663
theorem B827855 : Blo 826349 827855 := bstep (se 1 (by rfl) ⟨620891, by rfl⟩ : syracuseStep 827855 = 1241783) B1241783
theorem B828007 : Blo 826349 828007 := bstep (se 1 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 828007 = 1242011) B1242011
theorem B828271 : Blo 826349 828271 := bstep (se 1 (by rfl) ⟨621203, by rfl⟩ : syracuseStep 828271 = 1242407) B1242407
theorem B5317487 : Blo 826349 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B828327 : Blo 826349 828327 := bstep (se 1 (by rfl) ⟨621245, by rfl⟩ : syracuseStep 828327 = 1242491) B1242491
theorem B828411 : Blo 826349 828411 := bstep (se 1 (by rfl) ⟨621308, by rfl⟩ : syracuseStep 828411 = 1242617) B1242617
theorem B828479 : Blo 826349 828479 := bstep (se 1 (by rfl) ⟨621359, by rfl⟩ : syracuseStep 828479 = 1242719) B1242719
theorem B828623 : Blo 826349 828623 := bstep (se 1 (by rfl) ⟨621467, by rfl⟩ : syracuseStep 828623 = 1242935) B1242935
theorem B828827 : Blo 826349 828827 := bstep (se 1 (by rfl) ⟨621620, by rfl⟩ : syracuseStep 828827 = 1243241) B1243241
theorem B829039 : Blo 826349 829039 := bstep (se 1 (by rfl) ⟨621779, by rfl⟩ : syracuseStep 829039 = 1243559) B1243559
theorem B829095 : Blo 826349 829095 := bstep (se 1 (by rfl) ⟨621821, by rfl⟩ : syracuseStep 829095 = 1243643) B1243643
theorem B9545435 : Blo 826349 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B829179 : Blo 826349 829179 := bstep (se 1 (by rfl) ⟨621884, by rfl⟩ : syracuseStep 829179 = 1243769) B1243769
theorem B22062851 : Blo 826349 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B829215 : Blo 826349 829215 := bstep (se 1 (by rfl) ⟨621911, by rfl⟩ : syracuseStep 829215 = 1243823) B1243823
theorem B829247 : Blo 826349 829247 := bstep (se 1 (by rfl) ⟨621935, by rfl⟩ : syracuseStep 829247 = 1243871) B1243871
theorem B993223 : Blo 826349 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B829423 : Blo 826349 829423 := bstep (se 1 (by rfl) ⟨622067, by rfl⟩ : syracuseStep 829423 = 1244135) B1244135
theorem B829595 : Blo 826349 829595 := bstep (se 1 (by rfl) ⟨622196, by rfl⟩ : syracuseStep 829595 = 1244393) B1244393
theorem B829631 : Blo 826349 829631 := bstep (se 1 (by rfl) ⟨622223, by rfl⟩ : syracuseStep 829631 = 1244447) B1244447
theorem B14330141 : Blo 826349 14330141 := bstep (se 3 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 14330141 = 5373803) B5373803
theorem B829743 : Blo 826349 829743 := bstep (se 1 (by rfl) ⟨622307, by rfl⟩ : syracuseStep 829743 = 1244615) B1244615
theorem B829979 : Blo 826349 829979 := bstep (se 1 (by rfl) ⟨622484, by rfl⟩ : syracuseStep 829979 = 1244969) B1244969
theorem B829983 : Blo 826349 829983 := bstep (se 1 (by rfl) ⟨622487, by rfl⟩ : syracuseStep 829983 = 1244975) B1244975
theorem B830299 : Blo 826349 830299 := bstep (se 1 (by rfl) ⟨622724, by rfl⟩ : syracuseStep 830299 = 1245449) B1245449
theorem B3976199 : Blo 826349 3976199 := bstep (se 1 (by rfl) ⟨2982149, by rfl⟩ : syracuseStep 3976199 = 5964299) B5964299
theorem B2829455 : Blo 826349 2829455 := bstep (se 1 (by rfl) ⟨2122091, by rfl⟩ : syracuseStep 2829455 = 4244183) B4244183
theorem B2796767 : Blo 826349 2796767 := bstep (se 1 (by rfl) ⟨2097575, by rfl⟩ : syracuseStep 2796767 = 4195151) B4195151
theorem B2796983 : Blo 826349 2796983 := bstep (se 1 (by rfl) ⟨2097737, by rfl⟩ : syracuseStep 2796983 = 4195475) B4195475
theorem B5320151 : Blo 826349 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B1912427 : Blo 826349 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B5680801 : Blo 826349 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B929659 : Blo 826349 929659 := bstep (se 1 (by rfl) ⟨697244, by rfl⟩ : syracuseStep 929659 = 1394489) B1394489
theorem B15085739 : Blo 826349 15085739 := bstep (se 1 (by rfl) ⟨11314304, by rfl⟩ : syracuseStep 15085739 = 22628609) B22628609
theorem B1323785 : Blo 826349 1323785 := bstep (se 2 (by rfl) ⟨496419, by rfl⟩ : syracuseStep 1323785 = 992839) B992839
theorem B930811 : Blo 826349 930811 := bstep (se 1 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 930811 = 1396217) B1396217
theorem B996347 : Blo 826349 996347 := bstep (se 1 (by rfl) ⟨747260, by rfl⟩ : syracuseStep 996347 = 1494521) B1494521
theorem B930991 : Blo 826349 930991 := bstep (se 1 (by rfl) ⟨698243, by rfl⟩ : syracuseStep 930991 = 1396487) B1396487
theorem B2799035 : Blo 826349 2799035 := bstep (se 1 (by rfl) ⟨2099276, by rfl⟩ : syracuseStep 2799035 = 4198553) B4198553
theorem B931495 : Blo 826349 931495 := bstep (se 1 (by rfl) ⟨698621, by rfl⟩ : syracuseStep 931495 = 1397243) B1397243
theorem B931783 : Blo 826349 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B2799575 : Blo 826349 2799575 := bstep (se 1 (by rfl) ⟨2099681, by rfl⟩ : syracuseStep 2799575 = 4199363) B4199363
theorem B932143 : Blo 826349 932143 := bstep (se 1 (by rfl) ⟨699107, by rfl⟩ : syracuseStep 932143 = 1398215) B1398215
theorem B2800061 : Blo 826349 2800061 := bstep (se 3 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 2800061 = 1050023) B1050023
theorem B349223669 : Blo 826349 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B1325983 : Blo 826349 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B932935 : Blo 826349 932935 := bstep (se 1 (by rfl) ⟨699701, by rfl⟩ : syracuseStep 932935 = 1399403) B1399403
theorem B7060729 : Blo 826349 7060729 := bstep (se 2 (by rfl) ⟨2647773, by rfl⟩ : syracuseStep 7060729 = 5295547) B5295547
theorem B2800925 : Blo 826349 2800925 := bstep (se 3 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 2800925 = 1050347) B1050347
theorem B2833831 : Blo 826349 2833831 := bstep (se 1 (by rfl) ⟨2125373, by rfl⟩ : syracuseStep 2833831 = 4250747) B4250747
theorem B1326655 : Blo 826349 1326655 := bstep (se 1 (by rfl) ⟨994991, by rfl⟩ : syracuseStep 1326655 = 1989983) B1989983
theorem B3784573 : Blo 826349 3784573 := bstep (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) B1419215
theorem B2801951 : Blo 826349 2801951 := bstep (se 1 (by rfl) ⟨2101463, by rfl⟩ : syracuseStep 2801951 = 4202927) B4202927
theorem B3228103 : Blo 826349 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B5981309 : Blo 826349 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B9455129 : Blo 826349 9455129 := bstep (se 2 (by rfl) ⟨3545673, by rfl⟩ : syracuseStep 9455129 = 7091347) B7091347
theorem B1328975 : Blo 826349 1328975 := bstep (se 1 (by rfl) ⟨996731, by rfl⟩ : syracuseStep 1328975 = 1993463) B1993463
theorem B10078181 : Blo 826349 10078181 := bstep (se 4 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 10078181 = 1889659) B1889659
theorem B1394671 : Blo 826349 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B1394921 : Blo 826349 1394921 := bstep (se 2 (by rfl) ⟨523095, by rfl⟩ : syracuseStep 1394921 = 1046191) B1046191
theorem B1329385 : Blo 826349 1329385 := bstep (se 2 (by rfl) ⟨498519, by rfl⟩ : syracuseStep 1329385 = 997039) B997039
theorem B2837063 : Blo 826349 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B7949015 : Blo 826349 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B7753097 : Blo 826349 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B7065103 : Blo 826349 7065103 := bstep (se 1 (by rfl) ⟨5298827, by rfl⟩ : syracuseStep 7065103 = 10597655) B10597655
theorem B1396399 : Blo 826349 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B5984077 : Blo 826349 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B23908283 : Blo 826349 23908283 := bstep (se 1 (by rfl) ⟨17931212, by rfl⟩ : syracuseStep 23908283 = 35862425) B35862425
theorem B1396703 : Blo 826349 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B1397047 : Blo 826349 1397047 := bstep (se 1 (by rfl) ⟨1047785, by rfl⟩ : syracuseStep 1397047 = 2095571) B2095571
theorem B5296549 : Blo 826349 5296549 := bstep (se 4 (by rfl) ⟨496551, by rfl⟩ : syracuseStep 5296549 = 993103) B993103
theorem B1397351 : Blo 826349 1397351 := bstep (se 1 (by rfl) ⟨1048013, by rfl⟩ : syracuseStep 1397351 = 2096027) B2096027
theorem B12899017 : Blo 826349 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B1397513 : Blo 826349 1397513 := bstep (se 2 (by rfl) ⟨524067, by rfl⟩ : syracuseStep 1397513 = 1048135) B1048135
theorem B4707335 : Blo 826349 4707335 := bstep (se 1 (by rfl) ⟨3530501, by rfl⟩ : syracuseStep 4707335 = 7061003) B7061003
theorem B3364051 : Blo 826349 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B1398107 : Blo 826349 1398107 := bstep (se 1 (by rfl) ⟨1048580, by rfl⟩ : syracuseStep 1398107 = 2097161) B2097161
theorem B1136027 : Blo 826349 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B1398343 : Blo 826349 1398343 := bstep (se 1 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 1398343 = 2097515) B2097515
theorem B1398559 : Blo 826349 1398559 := bstep (se 1 (by rfl) ⟨1048919, by rfl⟩ : syracuseStep 1398559 = 2097839) B2097839
theorem B294508331 : Blo 826349 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B1398775 : Blo 826349 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B1399079 : Blo 826349 1399079 := bstep (se 1 (by rfl) ⟨1049309, by rfl⟩ : syracuseStep 1399079 = 2098619) B2098619
theorem B1399855 : Blo 826349 1399855 := bstep (se 1 (by rfl) ⟨1049891, by rfl⟩ : syracuseStep 1399855 = 2099783) B2099783
theorem B4709501 : Blo 826349 4709501 := bstep (se 3 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 4709501 = 1766063) B1766063
theorem B44260499 : Blo 826349 44260499 := bstep (se 1 (by rfl) ⟨33195374, by rfl⟩ : syracuseStep 44260499 = 66390749) B66390749
theorem B2514185 : Blo 826349 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B1400233 : Blo 826349 1400233 := bstep (se 2 (by rfl) ⟨525087, by rfl⟩ : syracuseStep 1400233 = 1050175) B1050175
theorem B76472045 : Blo 826349 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B1892087 : Blo 826349 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B1859399 : Blo 826349 1859399 := bstep (se 1 (by rfl) ⟨1394549, by rfl⟩ : syracuseStep 1859399 = 2789099) B2789099
theorem B1400699 : Blo 826349 1400699 := bstep (se 1 (by rfl) ⟨1050524, by rfl⟩ : syracuseStep 1400699 = 2101049) B2101049
theorem B1860047 : Blo 826349 1860047 := bstep (se 1 (by rfl) ⟨1395035, by rfl⟩ : syracuseStep 1860047 = 2790071) B2790071
theorem B1860713 : Blo 826349 1860713 := bstep (se 2 (by rfl) ⟨697767, by rfl⟩ : syracuseStep 1860713 = 1395535) B1395535
theorem B4187699 : Blo 826349 4187699 := bstep (se 1 (by rfl) ⟨3140774, by rfl⟩ : syracuseStep 4187699 = 6281549) B6281549
theorem B5301881 : Blo 826349 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B1861343 : Blo 826349 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B14149889 : Blo 826349 14149889 := bstep (se 2 (by rfl) ⟨5306208, by rfl⟩ : syracuseStep 14149889 = 10612417) B10612417
theorem B2353691 : Blo 826349 2353691 := bstep (se 1 (by rfl) ⟨1765268, by rfl⟩ : syracuseStep 2353691 = 3530537) B3530537
theorem B1862171 : Blo 826349 1862171 := bstep (se 1 (by rfl) ⟨1396628, by rfl⟩ : syracuseStep 1862171 = 2793257) B2793257
theorem B3140167 : Blo 826349 3140167 := bstep (se 1 (by rfl) ⟨2355125, by rfl⟩ : syracuseStep 3140167 = 4710251) B4710251
theorem B1239689 : Blo 826349 1239689 := bstep (se 2 (by rfl) ⟨464883, by rfl⟩ : syracuseStep 1239689 = 929767) B929767
theorem B9431801 : Blo 826349 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B1239863 : Blo 826349 1239863 := bstep (se 1 (by rfl) ⟨929897, by rfl⟩ : syracuseStep 1239863 = 1859795) B1859795
theorem B1239899 : Blo 826349 1239899 := bstep (se 1 (by rfl) ⟨929924, by rfl⟩ : syracuseStep 1239899 = 1859849) B1859849
theorem B1240043 : Blo 826349 1240043 := bstep (se 1 (by rfl) ⟨930032, by rfl⟩ : syracuseStep 1240043 = 1860065) B1860065
theorem B5303393 : Blo 826349 5303393 := bstep (se 2 (by rfl) ⟨1988772, by rfl⟩ : syracuseStep 5303393 = 3977545) B3977545
theorem B4189319 : Blo 826349 4189319 := bstep (se 1 (by rfl) ⟨3141989, by rfl⟩ : syracuseStep 4189319 = 6283979) B6283979
theorem B1240247 : Blo 826349 1240247 := bstep (se 1 (by rfl) ⟨930185, by rfl⟩ : syracuseStep 1240247 = 1860371) B1860371
theorem B1240487 : Blo 826349 1240487 := bstep (se 1 (by rfl) ⟨930365, by rfl⟩ : syracuseStep 1240487 = 1860731) B1860731
theorem B1240571 : Blo 826349 1240571 := bstep (se 1 (by rfl) ⟨930428, by rfl⟩ : syracuseStep 1240571 = 1860857) B1860857
theorem B4484641 : Blo 826349 4484641 := bstep (se 2 (by rfl) ⟨1681740, by rfl⟩ : syracuseStep 4484641 = 3363481) B3363481
theorem B2354761 : Blo 826349 2354761 := bstep (se 2 (by rfl) ⟨883035, by rfl⟩ : syracuseStep 2354761 = 1766071) B1766071
theorem B1240667 : Blo 826349 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B1240751 : Blo 826349 1240751 := bstep (se 1 (by rfl) ⟨930563, by rfl⟩ : syracuseStep 1240751 = 1861127) B1861127
theorem B1240871 : Blo 826349 1240871 := bstep (se 1 (by rfl) ⟨930653, by rfl⟩ : syracuseStep 1240871 = 1861307) B1861307
theorem B1240955 : Blo 826349 1240955 := bstep (se 1 (by rfl) ⟨930716, by rfl⟩ : syracuseStep 1240955 = 1861433) B1861433
theorem B2944907 : Blo 826349 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B1994635 : Blo 826349 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B1863647 : Blo 826349 1863647 := bstep (se 1 (by rfl) ⟨1397735, by rfl⟩ : syracuseStep 1863647 = 2795471) B2795471
theorem B4714625 : Blo 826349 4714625 := bstep (se 2 (by rfl) ⟨1767984, by rfl⟩ : syracuseStep 4714625 = 3535969) B3535969
theorem B2355389 : Blo 826349 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B1241375 : Blo 826349 1241375 := bstep (se 1 (by rfl) ⟨931031, by rfl⟩ : syracuseStep 1241375 = 1862063) B1862063
theorem B1241399 : Blo 826349 1241399 := bstep (se 1 (by rfl) ⟨931049, by rfl⟩ : syracuseStep 1241399 = 1862099) B1862099
theorem B4714807 : Blo 826349 4714807 := bstep (se 1 (by rfl) ⟨3536105, by rfl⟩ : syracuseStep 4714807 = 7072211) B7072211
theorem B1241471 : Blo 826349 1241471 := bstep (se 1 (by rfl) ⟨931103, by rfl⟩ : syracuseStep 1241471 = 1862207) B1862207
theorem B3535271 : Blo 826349 3535271 := bstep (se 1 (by rfl) ⟨2651453, by rfl⟩ : syracuseStep 3535271 = 5302907) B5302907
theorem B1241543 : Blo 826349 1241543 := bstep (se 1 (by rfl) ⟨931157, by rfl⟩ : syracuseStep 1241543 = 1862315) B1862315
theorem B2978387 : Blo 826349 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B1864295 : Blo 826349 1864295 := bstep (se 1 (by rfl) ⟨1398221, by rfl⟩ : syracuseStep 1864295 = 2796443) B2796443
theorem B2388761 : Blo 826349 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B1241897 : Blo 826349 1241897 := bstep (se 2 (by rfl) ⟨465711, by rfl⟩ : syracuseStep 1241897 = 931423) B931423
theorem B1241903 : Blo 826349 1241903 := bstep (se 1 (by rfl) ⟨931427, by rfl⟩ : syracuseStep 1241903 = 1862855) B1862855
theorem B4191101 : Blo 826349 4191101 := bstep (se 3 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 4191101 = 1571663) B1571663
theorem B2978689 : Blo 826349 2978689 := bstep (se 2 (by rfl) ⟨1117008, by rfl⟩ : syracuseStep 2978689 = 2234017) B2234017
theorem B5665697 : Blo 826349 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B1242023 : Blo 826349 1242023 := bstep (se 1 (by rfl) ⟨931517, by rfl⟩ : syracuseStep 1242023 = 1863035) B1863035
theorem B2356219 : Blo 826349 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B1242107 : Blo 826349 1242107 := bstep (se 1 (by rfl) ⟨931580, by rfl⟩ : syracuseStep 1242107 = 1863161) B1863161
theorem B1242167 : Blo 826349 1242167 := bstep (se 1 (by rfl) ⟨931625, by rfl⟩ : syracuseStep 1242167 = 1863251) B1863251
theorem B1242287 : Blo 826349 1242287 := bstep (se 1 (by rfl) ⟨931715, by rfl⟩ : syracuseStep 1242287 = 1863431) B1863431
theorem B1864979 : Blo 826349 1864979 := bstep (se 1 (by rfl) ⟨1398734, by rfl⟩ : syracuseStep 1864979 = 2797469) B2797469
theorem B1865051 : Blo 826349 1865051 := bstep (se 1 (by rfl) ⟨1398788, by rfl⟩ : syracuseStep 1865051 = 2797577) B2797577
theorem B1766747 : Blo 826349 1766747 := bstep (se 1 (by rfl) ⟨1325060, by rfl⟩ : syracuseStep 1766747 = 2650121) B2650121
theorem B5305799 : Blo 826349 5305799 := bstep (se 1 (by rfl) ⟨3979349, by rfl⟩ : syracuseStep 5305799 = 7958699) B7958699
theorem B1242695 : Blo 826349 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B14317195 : Blo 826349 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B1242791 : Blo 826349 1242791 := bstep (se 1 (by rfl) ⟨932093, by rfl⟩ : syracuseStep 1242791 = 1864187) B1864187
theorem B5306057 : Blo 826349 5306057 := bstep (se 2 (by rfl) ⟨1989771, by rfl⟩ : syracuseStep 5306057 = 3979543) B3979543
theorem B5306107 : Blo 826349 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B7960315 : Blo 826349 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B1242875 : Blo 826349 1242875 := bstep (se 1 (by rfl) ⟨932156, by rfl⟩ : syracuseStep 1242875 = 1864313) B1864313
theorem B1242911 : Blo 826349 1242911 := bstep (se 1 (by rfl) ⟨932183, by rfl⟩ : syracuseStep 1242911 = 1864367) B1864367
theorem B2357039 : Blo 826349 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B1242959 : Blo 826349 1242959 := bstep (se 1 (by rfl) ⟨932219, by rfl⟩ : syracuseStep 1242959 = 1864439) B1864439
theorem B1865609 : Blo 826349 1865609 := bstep (se 2 (by rfl) ⟨699603, by rfl⟩ : syracuseStep 1865609 = 1399207) B1399207
theorem B1243079 : Blo 826349 1243079 := bstep (se 1 (by rfl) ⟨932309, by rfl⟩ : syracuseStep 1243079 = 1864619) B1864619
theorem B1865825 : Blo 826349 1865825 := bstep (se 2 (by rfl) ⟨699684, by rfl⟩ : syracuseStep 1865825 = 1399369) B1399369
theorem B2095247 : Blo 826349 2095247 := bstep (se 1 (by rfl) ⟨1571435, by rfl⟩ : syracuseStep 2095247 = 3142871) B3142871
theorem B2980073 : Blo 826349 2980073 := bstep (se 2 (by rfl) ⟨1117527, by rfl⟩ : syracuseStep 2980073 = 2235055) B2235055
theorem B1243433 : Blo 826349 1243433 := bstep (se 2 (by rfl) ⟨466287, by rfl⟩ : syracuseStep 1243433 = 932575) B932575
theorem B1243439 : Blo 826349 1243439 := bstep (se 1 (by rfl) ⟨932579, by rfl⟩ : syracuseStep 1243439 = 1865159) B1865159
theorem B1243679 : Blo 826349 1243679 := bstep (se 1 (by rfl) ⟨932759, by rfl⟩ : syracuseStep 1243679 = 1865519) B1865519
theorem B2095753 : Blo 826349 2095753 := bstep (se 2 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 2095753 = 1571815) B1571815
theorem B3144527 : Blo 826349 3144527 := bstep (se 1 (by rfl) ⟨2358395, by rfl⟩ : syracuseStep 3144527 = 4716791) B4716791
theorem B1244063 : Blo 826349 1244063 := bstep (se 1 (by rfl) ⟨933047, by rfl⟩ : syracuseStep 1244063 = 1866095) B1866095
theorem B4488101 : Blo 826349 4488101 := bstep (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) B841519
theorem B1244111 : Blo 826349 1244111 := bstep (se 1 (by rfl) ⟨933083, by rfl⟩ : syracuseStep 1244111 = 1866167) B1866167
theorem B9436175 : Blo 826349 9436175 := bstep (se 1 (by rfl) ⟨7077131, by rfl⟩ : syracuseStep 9436175 = 14154263) B14154263
theorem B1244201 : Blo 826349 1244201 := bstep (se 2 (by rfl) ⟨466575, by rfl⟩ : syracuseStep 1244201 = 933151) B933151
theorem B1244207 : Blo 826349 1244207 := bstep (se 1 (by rfl) ⟨933155, by rfl⟩ : syracuseStep 1244207 = 1866311) B1866311
theorem B5372999 : Blo 826349 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B1244231 : Blo 826349 1244231 := bstep (se 1 (by rfl) ⟨933173, by rfl⟩ : syracuseStep 1244231 = 1866347) B1866347
theorem B4193369 : Blo 826349 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B2555009 : Blo 826349 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B2358521 : Blo 826349 2358521 := bstep (se 2 (by rfl) ⟨884445, by rfl⟩ : syracuseStep 2358521 = 1768891) B1768891
theorem B1244495 : Blo 826349 1244495 := bstep (se 1 (by rfl) ⟨933371, by rfl⟩ : syracuseStep 1244495 = 1866743) B1866743
theorem B1867175 : Blo 826349 1867175 := bstep (se 1 (by rfl) ⟨1400381, by rfl⟩ : syracuseStep 1867175 = 2800763) B2800763
theorem B1244585 : Blo 826349 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B1244735 : Blo 826349 1244735 := bstep (se 1 (by rfl) ⟨933551, by rfl⟩ : syracuseStep 1244735 = 1867103) B1867103
theorem B1867355 : Blo 826349 1867355 := bstep (se 1 (by rfl) ⟨1400516, by rfl⟩ : syracuseStep 1867355 = 2801033) B2801033
theorem B5963489 : Blo 826349 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B4194017 : Blo 826349 4194017 := bstep (se 2 (by rfl) ⟨1572756, by rfl⟩ : syracuseStep 4194017 = 3145513) B3145513
theorem B2096887 : Blo 826349 2096887 := bstep (se 1 (by rfl) ⟨1572665, by rfl⟩ : syracuseStep 2096887 = 3145331) B3145331
theorem B1244999 : Blo 826349 1244999 := bstep (se 1 (by rfl) ⟨933749, by rfl⟩ : syracuseStep 1244999 = 1867499) B1867499
theorem B1867643 : Blo 826349 1867643 := bstep (se 1 (by rfl) ⟨1400732, by rfl⟩ : syracuseStep 1867643 = 2801465) B2801465
theorem B1245083 : Blo 826349 1245083 := bstep (se 1 (by rfl) ⟨933812, by rfl⟩ : syracuseStep 1245083 = 1867625) B1867625
theorem B1867967 : Blo 826349 1867967 := bstep (se 1 (by rfl) ⟨1400975, by rfl⟩ : syracuseStep 1867967 = 2801951) B2801951
theorem B1245419 : Blo 826349 1245419 := bstep (se 1 (by rfl) ⟨934064, by rfl⟩ : syracuseStep 1245419 = 1868129) B1868129
theorem B1245479 : Blo 826349 1245479 := bstep (se 1 (by rfl) ⟨934109, by rfl⟩ : syracuseStep 1245479 = 1868219) B1868219
theorem B1048879 : Blo 826349 1048879 := bstep (se 1 (by rfl) ⟨786659, by rfl⟩ : syracuseStep 1048879 = 1573319) B1573319
theorem B2097535 : Blo 826349 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B1574063 : Blo 826349 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B885983 : Blo 826349 885983 := bstep (se 1 (by rfl) ⟨664487, by rfl⟩ : syracuseStep 885983 = 1328975) B1328975
theorem B12780767 : Blo 826349 12780767 := bstep (se 1 (by rfl) ⟨9585575, by rfl⟩ : syracuseStep 12780767 = 19171151) B19171151
theorem B2098457 : Blo 826349 2098457 := bstep (se 2 (by rfl) ⟨786921, by rfl⟩ : syracuseStep 2098457 = 1573843) B1573843
theorem B5965103 : Blo 826349 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B1180975 : Blo 826349 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B6718787 : Blo 826349 6718787 := bstep (se 1 (by rfl) ⟨5039090, by rfl⟩ : syracuseStep 6718787 = 10078181) B10078181
theorem B3540343 : Blo 826349 3540343 := bstep (se 1 (by rfl) ⟨2655257, by rfl⟩ : syracuseStep 3540343 = 5310515) B5310515
theorem B1574777 : Blo 826349 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B20384011 : Blo 826349 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B3148247 : Blo 826349 3148247 := bstep (se 1 (by rfl) ⟨2361185, by rfl⟩ : syracuseStep 3148247 = 4722371) B4722371
theorem B2656925 : Blo 826349 2656925 := bstep (se 3 (by rfl) ⟨498173, by rfl⟩ : syracuseStep 2656925 = 996347) B996347
theorem B3148703 : Blo 826349 3148703 := bstep (se 1 (by rfl) ⟨2361527, by rfl⟩ : syracuseStep 3148703 = 4723055) B4723055
theorem B2100127 : Blo 826349 2100127 := bstep (se 1 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 2100127 = 3150191) B3150191
theorem B1772513 : Blo 826349 1772513 := bstep (se 2 (by rfl) ⟨664692, by rfl⟩ : syracuseStep 1772513 = 1329385) B1329385
theorem B1575931 : Blo 826349 1575931 := bstep (se 1 (by rfl) ⟨1181948, by rfl⟩ : syracuseStep 1575931 = 2363897) B2363897
theorem B9571391 : Blo 826349 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B3542393 : Blo 826349 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B2559371 : Blo 826349 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B15142955 : Blo 826349 15142955 := bstep (se 1 (by rfl) ⟨11357216, by rfl⟩ : syracuseStep 15142955 = 22714433) B22714433
theorem B3149887 : Blo 826349 3149887 := bstep (se 1 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 3149887 = 4724831) B4724831
theorem B2101535 : Blo 826349 2101535 := bstep (se 1 (by rfl) ⟨1576151, by rfl⟩ : syracuseStep 2101535 = 3152303) B3152303
theorem B7082599 : Blo 826349 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B1676123 : Blo 826349 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B7574401 : Blo 826349 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B6296615 : Blo 826349 6296615 := bstep (se 1 (by rfl) ⟨4722461, by rfl⟩ : syracuseStep 6296615 = 9444923) B9444923
theorem B2659513 : Blo 826349 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B3544991 : Blo 826349 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B3151817 : Blo 826349 3151817 := bstep (se 2 (by rfl) ⟨1181931, by rfl⟩ : syracuseStep 3151817 = 2363863) B2363863
theorem B2791799 : Blo 826349 2791799 := bstep (se 1 (by rfl) ⟨2093849, by rfl⟩ : syracuseStep 2791799 = 4187699) B4187699
theorem B6363623 : Blo 826349 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B3971585 : Blo 826349 3971585 := bstep (se 2 (by rfl) ⟨1489344, by rfl⟩ : syracuseStep 3971585 = 2978689) B2978689
theorem B826459 : Blo 826349 826459 := bstep (se 1 (by rfl) ⟨619844, by rfl⟩ : syracuseStep 826459 = 1239689) B1239689
theorem B826575 : Blo 826349 826575 := bstep (se 1 (by rfl) ⟨619931, by rfl⟩ : syracuseStep 826575 = 1239863) B1239863
theorem B826599 : Blo 826349 826599 := bstep (se 1 (by rfl) ⟨619949, by rfl⟩ : syracuseStep 826599 = 1239899) B1239899
theorem B826695 : Blo 826349 826695 := bstep (se 1 (by rfl) ⟨620021, by rfl⟩ : syracuseStep 826695 = 1240043) B1240043
theorem B2792879 : Blo 826349 2792879 := bstep (se 1 (by rfl) ⟨2094659, by rfl⟩ : syracuseStep 2792879 = 4189319) B4189319
theorem B826831 : Blo 826349 826831 := bstep (se 1 (by rfl) ⟨620123, by rfl⟩ : syracuseStep 826831 = 1240247) B1240247
theorem B15113765 : Blo 826349 15113765 := bstep (se 4 (by rfl) ⟨1416915, by rfl⟩ : syracuseStep 15113765 = 2833831) B2833831
theorem B826991 : Blo 826349 826991 := bstep (se 1 (by rfl) ⟨620243, by rfl⟩ : syracuseStep 826991 = 1240487) B1240487
theorem B3546767 : Blo 826349 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B827047 : Blo 826349 827047 := bstep (se 1 (by rfl) ⟨620285, by rfl⟩ : syracuseStep 827047 = 1240571) B1240571
theorem B827111 : Blo 826349 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B827167 : Blo 826349 827167 := bstep (se 1 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 827167 = 1240751) B1240751
theorem B827247 : Blo 826349 827247 := bstep (se 1 (by rfl) ⟨620435, by rfl⟩ : syracuseStep 827247 = 1240871) B1240871
theorem B827303 : Blo 826349 827303 := bstep (se 1 (by rfl) ⟨620477, by rfl⟩ : syracuseStep 827303 = 1240955) B1240955
theorem B4202441 : Blo 826349 4202441 := bstep (se 2 (by rfl) ⟨1575915, by rfl⟩ : syracuseStep 4202441 = 3151831) B3151831
theorem B827583 : Blo 826349 827583 := bstep (se 1 (by rfl) ⟨620687, by rfl⟩ : syracuseStep 827583 = 1241375) B1241375
theorem B827599 : Blo 826349 827599 := bstep (se 1 (by rfl) ⟨620699, by rfl⟩ : syracuseStep 827599 = 1241399) B1241399
theorem B827647 : Blo 826349 827647 := bstep (se 1 (by rfl) ⟨620735, by rfl⟩ : syracuseStep 827647 = 1241471) B1241471
theorem B827695 : Blo 826349 827695 := bstep (se 1 (by rfl) ⟨620771, by rfl⟩ : syracuseStep 827695 = 1241543) B1241543
theorem B827931 : Blo 826349 827931 := bstep (se 1 (by rfl) ⟨620948, by rfl⟩ : syracuseStep 827931 = 1241897) B1241897
theorem B827935 : Blo 826349 827935 := bstep (se 1 (by rfl) ⟨620951, by rfl⟩ : syracuseStep 827935 = 1241903) B1241903
theorem B4203089 : Blo 826349 4203089 := bstep (se 2 (by rfl) ⟨1576158, by rfl⟩ : syracuseStep 4203089 = 3152317) B3152317
theorem B2794067 : Blo 826349 2794067 := bstep (se 1 (by rfl) ⟨2095550, by rfl⟩ : syracuseStep 2794067 = 4191101) B4191101
theorem B3777131 : Blo 826349 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B828015 : Blo 826349 828015 := bstep (se 1 (by rfl) ⟨621011, by rfl⟩ : syracuseStep 828015 = 1242023) B1242023
theorem B828071 : Blo 826349 828071 := bstep (se 1 (by rfl) ⟨621053, by rfl⟩ : syracuseStep 828071 = 1242107) B1242107
theorem B828111 : Blo 826349 828111 := bstep (se 1 (by rfl) ⟨621083, by rfl⟩ : syracuseStep 828111 = 1242167) B1242167
theorem B828191 : Blo 826349 828191 := bstep (se 1 (by rfl) ⟨621143, by rfl⟩ : syracuseStep 828191 = 1242287) B1242287
theorem B2794337 : Blo 826349 2794337 := bstep (se 2 (by rfl) ⟨1047876, by rfl⟩ : syracuseStep 2794337 = 2095753) B2095753
theorem B7086973 : Blo 826349 7086973 := bstep (se 3 (by rfl) ⟨1328807, by rfl⟩ : syracuseStep 7086973 = 2657615) B2657615
theorem B828463 : Blo 826349 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B828527 : Blo 826349 828527 := bstep (se 1 (by rfl) ⟨621395, by rfl⟩ : syracuseStep 828527 = 1242791) B1242791
theorem B4727929 : Blo 826349 4727929 := bstep (se 2 (by rfl) ⟨1772973, by rfl⟩ : syracuseStep 4727929 = 3545947) B3545947
theorem B828583 : Blo 826349 828583 := bstep (se 1 (by rfl) ⟨621437, by rfl⟩ : syracuseStep 828583 = 1242875) B1242875
theorem B828607 : Blo 826349 828607 := bstep (se 1 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 828607 = 1242911) B1242911
theorem B828639 : Blo 826349 828639 := bstep (se 1 (by rfl) ⟨621479, by rfl⟩ : syracuseStep 828639 = 1242959) B1242959
theorem B828719 : Blo 826349 828719 := bstep (se 1 (by rfl) ⟨621539, by rfl⟩ : syracuseStep 828719 = 1243079) B1243079
theorem B6300989 : Blo 826349 6300989 := bstep (se 3 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 6300989 = 2362871) B2362871
theorem B4040189 : Blo 826349 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B828955 : Blo 826349 828955 := bstep (se 1 (by rfl) ⟨621716, by rfl⟩ : syracuseStep 828955 = 1243433) B1243433
theorem B828959 : Blo 826349 828959 := bstep (se 1 (by rfl) ⟨621719, by rfl⟩ : syracuseStep 828959 = 1243439) B1243439
theorem B9414305 : Blo 826349 9414305 := bstep (se 2 (by rfl) ⟨3530364, by rfl⟩ : syracuseStep 9414305 = 7060729) B7060729
theorem B829119 : Blo 826349 829119 := bstep (se 1 (by rfl) ⟨621839, by rfl⟩ : syracuseStep 829119 = 1243679) B1243679
theorem B829375 : Blo 826349 829375 := bstep (se 1 (by rfl) ⟨622031, by rfl⟩ : syracuseStep 829375 = 1244063) B1244063
theorem B2992067 : Blo 826349 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B829407 : Blo 826349 829407 := bstep (se 1 (by rfl) ⟨622055, by rfl⟩ : syracuseStep 829407 = 1244111) B1244111
theorem B829467 : Blo 826349 829467 := bstep (se 1 (by rfl) ⟨622100, by rfl⟩ : syracuseStep 829467 = 1244201) B1244201
theorem B829471 : Blo 826349 829471 := bstep (se 1 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 829471 = 1244207) B1244207
theorem B3581999 : Blo 826349 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B829487 : Blo 826349 829487 := bstep (se 1 (by rfl) ⟨622115, by rfl⟩ : syracuseStep 829487 = 1244231) B1244231
theorem B2795579 : Blo 826349 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B206579813 : Blo 826349 206579813 := bstep (se 4 (by rfl) ⟨19366857, by rfl⟩ : syracuseStep 206579813 = 38733715) B38733715
theorem B829663 : Blo 826349 829663 := bstep (se 1 (by rfl) ⟨622247, by rfl⟩ : syracuseStep 829663 = 1244495) B1244495
theorem B829723 : Blo 826349 829723 := bstep (se 1 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 829723 = 1244585) B1244585
theorem B2795849 : Blo 826349 2795849 := bstep (se 2 (by rfl) ⟨1048443, by rfl⟩ : syracuseStep 2795849 = 2096887) B2096887
theorem B829823 : Blo 826349 829823 := bstep (se 1 (by rfl) ⟨622367, by rfl⟩ : syracuseStep 829823 = 1244735) B1244735
theorem B3975659 : Blo 826349 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B2796011 : Blo 826349 2796011 := bstep (se 1 (by rfl) ⟨2097008, by rfl⟩ : syracuseStep 2796011 = 4194017) B4194017
theorem B829999 : Blo 826349 829999 := bstep (se 1 (by rfl) ⟨622499, by rfl⟩ : syracuseStep 829999 = 1244999) B1244999
theorem B830055 : Blo 826349 830055 := bstep (se 1 (by rfl) ⟨622541, by rfl⟩ : syracuseStep 830055 = 1245083) B1245083
theorem B4304137 : Blo 826349 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B3190279 : Blo 826349 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B2797199 : Blo 826349 2797199 := bstep (se 1 (by rfl) ⟨2097899, by rfl⟩ : syracuseStep 2797199 = 4195799) B4195799
theorem B6303419 : Blo 826349 6303419 := bstep (se 1 (by rfl) ⟨4727564, by rfl⟩ : syracuseStep 6303419 = 9455129) B9455129
theorem B897019 : Blo 826349 897019 := bstep (se 1 (by rfl) ⟨672764, by rfl⟩ : syracuseStep 897019 = 1345529) B1345529
theorem B929947 : Blo 826349 929947 := bstep (se 1 (by rfl) ⟨697460, by rfl⟩ : syracuseStep 929947 = 1394921) B1394921
theorem B1324297 : Blo 826349 1324297 := bstep (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) B993223
theorem B15938855 : Blo 826349 15938855 := bstep (se 1 (by rfl) ⟨11954141, by rfl⟩ : syracuseStep 15938855 = 23908283) B23908283
theorem B931135 : Blo 826349 931135 := bstep (se 1 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 931135 = 1396703) B1396703
theorem B931567 : Blo 826349 931567 := bstep (se 1 (by rfl) ⟨698675, by rfl⟩ : syracuseStep 931567 = 1397351) B1397351
theorem B931675 : Blo 826349 931675 := bstep (se 1 (by rfl) ⟨698756, by rfl⟩ : syracuseStep 931675 = 1397513) B1397513
theorem B9418679 : Blo 826349 9418679 := bstep (se 1 (by rfl) ⟨7064009, by rfl⟩ : syracuseStep 9418679 = 14128019) B14128019
theorem B932071 : Blo 826349 932071 := bstep (se 1 (by rfl) ⟨699053, by rfl⟩ : syracuseStep 932071 = 1398107) B1398107
theorem B3029405 : Blo 826349 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B932719 : Blo 826349 932719 := bstep (se 1 (by rfl) ⟨699539, by rfl⟩ : syracuseStep 932719 = 1399079) B1399079
theorem B3783827 : Blo 826349 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B2800871 : Blo 826349 2800871 := bstep (se 1 (by rfl) ⟨2100653, by rfl⟩ : syracuseStep 2800871 = 4201307) B4201307
theorem B9420137 : Blo 826349 9420137 := bstep (se 2 (by rfl) ⟨3532551, by rfl⟩ : syracuseStep 9420137 = 7065103) B7065103
theorem B5979521 : Blo 826349 5979521 := bstep (se 2 (by rfl) ⟨2242320, by rfl⟩ : syracuseStep 5979521 = 4484641) B4484641
theorem B1490347 : Blo 826349 1490347 := bstep (se 1 (by rfl) ⟨1117760, by rfl⟩ : syracuseStep 1490347 = 2235521) B2235521
theorem B29506999 : Blo 826349 29506999 := bstep (se 1 (by rfl) ⟨22130249, by rfl⟩ : syracuseStep 29506999 = 44260499) B44260499
theorem B114605603 : Blo 826349 114605603 := bstep (se 1 (by rfl) ⟨85954202, by rfl⟩ : syracuseStep 114605603 = 171908405) B171908405
theorem B7978769 : Blo 826349 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B31768361 : Blo 826349 31768361 := bstep (se 2 (by rfl) ⟨11913135, by rfl⟩ : syracuseStep 31768361 = 23826271) B23826271
theorem B1261391 : Blo 826349 1261391 := bstep (se 1 (by rfl) ⟨946043, by rfl⟩ : syracuseStep 1261391 = 1892087) B1892087
theorem B933799 : Blo 826349 933799 := bstep (se 1 (by rfl) ⟨700349, by rfl⟩ : syracuseStep 933799 = 1400699) B1400699
theorem B7062065 : Blo 826349 7062065 := bstep (se 2 (by rfl) ⟨2648274, by rfl⟩ : syracuseStep 7062065 = 5296549) B5296549
theorem B9553427 : Blo 826349 9553427 := bstep (se 1 (by rfl) ⟨7165070, by rfl⟩ : syracuseStep 9553427 = 14330141) B14330141
theorem B1886303 : Blo 826349 1886303 := bstep (se 1 (by rfl) ⟨1414727, by rfl⟩ : syracuseStep 1886303 = 2829455) B2829455
theorem B19089593 : Blo 826349 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B1985591 : Blo 826349 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B1592507 : Blo 826349 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B1396831 : Blo 826349 1396831 := bstep (se 1 (by rfl) ⟨1047623, by rfl⟩ : syracuseStep 1396831 = 2095247) B2095247
theorem B1986715 : Blo 826349 1986715 := bstep (se 1 (by rfl) ⟨1490036, by rfl⟩ : syracuseStep 1986715 = 2980073) B2980073
theorem B1398127 : Blo 826349 1398127 := bstep (se 1 (by rfl) ⟨1048595, by rfl⟩ : syracuseStep 1398127 = 2097191) B2097191
theorem B2840231 : Blo 826349 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B3987539 : Blo 826349 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B5299343 : Blo 826349 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B13458797 : Blo 826349 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B51010955 : Blo 826349 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B5168731 : Blo 826349 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B1859291 : Blo 826349 1859291 := bstep (se 1 (by rfl) ⟨1394468, by rfl⟩ : syracuseStep 1859291 = 2788937) B2788937
theorem B6381359 : Blo 826349 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B1859561 : Blo 826349 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B1991051 : Blo 826349 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B1860263 : Blo 826349 1860263 := bstep (se 1 (by rfl) ⟨1395197, by rfl⟩ : syracuseStep 1860263 = 2790395) B2790395
theorem B3138223 : Blo 826349 3138223 := bstep (se 1 (by rfl) ⟨2353667, by rfl⟩ : syracuseStep 3138223 = 4707335) B4707335
theorem B4186889 : Blo 826349 4186889 := bstep (se 2 (by rfl) ⟨1570083, by rfl⟩ : syracuseStep 4186889 = 3140167) B3140167
theorem B1860407 : Blo 826349 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B1860587 : Blo 826349 1860587 := bstep (se 1 (by rfl) ⟨1395440, by rfl⟩ : syracuseStep 1860587 = 2790881) B2790881
theorem B196338887 : Blo 826349 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B1861019 : Blo 826349 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B1861595 : Blo 826349 1861595 := bstep (se 1 (by rfl) ⟨1396196, by rfl⟩ : syracuseStep 1861595 = 2792393) B2792393
theorem B3139667 : Blo 826349 3139667 := bstep (se 1 (by rfl) ⟨2354750, by rfl⟩ : syracuseStep 3139667 = 4709501) B4709501
theorem B3139681 : Blo 826349 3139681 := bstep (se 2 (by rfl) ⟨1177380, by rfl⟩ : syracuseStep 3139681 = 2354761) B2354761
theorem B6285437 : Blo 826349 6285437 := bstep (se 3 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 6285437 = 2357039) B2357039
theorem B1861775 : Blo 826349 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B1861865 : Blo 826349 1861865 := bstep (se 2 (by rfl) ⟨698199, by rfl⟩ : syracuseStep 1861865 = 1396399) B1396399
theorem B50981363 : Blo 826349 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B1862135 : Blo 826349 1862135 := bstep (se 1 (by rfl) ⟨1396601, by rfl⟩ : syracuseStep 1862135 = 2793203) B2793203
theorem B1239545 : Blo 826349 1239545 := bstep (se 2 (by rfl) ⟨464829, by rfl⟩ : syracuseStep 1239545 = 929659) B929659
theorem B1239599 : Blo 826349 1239599 := bstep (se 1 (by rfl) ⟨929699, by rfl⟩ : syracuseStep 1239599 = 1859399) B1859399
theorem B2517551 : Blo 826349 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B1240031 : Blo 826349 1240031 := bstep (se 1 (by rfl) ⟨930023, by rfl⟩ : syracuseStep 1240031 = 1860047) B1860047
theorem B6286409 : Blo 826349 6286409 := bstep (se 2 (by rfl) ⟨2357403, by rfl⟩ : syracuseStep 6286409 = 4714807) B4714807
theorem B1862729 : Blo 826349 1862729 := bstep (se 2 (by rfl) ⟨698523, by rfl⟩ : syracuseStep 1862729 = 1397047) B1397047
theorem B1240475 : Blo 826349 1240475 := bstep (se 1 (by rfl) ⟨930356, by rfl⟩ : syracuseStep 1240475 = 1860713) B1860713
theorem B17198689 : Blo 826349 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B3534587 : Blo 826349 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B1240895 : Blo 826349 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B14708567 : Blo 826349 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1241081 : Blo 826349 1241081 := bstep (se 2 (by rfl) ⟨465405, by rfl⟩ : syracuseStep 1241081 = 930811) B930811
theorem B3141625 : Blo 826349 3141625 := bstep (se 2 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 3141625 = 2356219) B2356219
theorem B9433259 : Blo 826349 9433259 := bstep (se 1 (by rfl) ⟨7074944, by rfl⟩ : syracuseStep 9433259 = 14149889) B14149889
theorem B7565501 : Blo 826349 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B1241321 : Blo 826349 1241321 := bstep (se 2 (by rfl) ⟨465495, by rfl⟩ : syracuseStep 1241321 = 930991) B930991
theorem B4485401 : Blo 826349 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B1569127 : Blo 826349 1569127 := bstep (se 1 (by rfl) ⟨1176845, by rfl⟩ : syracuseStep 1569127 = 2353691) B2353691
theorem B1241447 : Blo 826349 1241447 := bstep (se 1 (by rfl) ⟨931085, by rfl⟩ : syracuseStep 1241447 = 1862171) B1862171
theorem B6287867 : Blo 826349 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B2650799 : Blo 826349 2650799 := bstep (se 1 (by rfl) ⟨1988099, by rfl⟩ : syracuseStep 2650799 = 3976199) B3976199
theorem B3535595 : Blo 826349 3535595 := bstep (se 1 (by rfl) ⟨2651696, by rfl⟩ : syracuseStep 3535595 = 5303393) B5303393
theorem B1864457 : Blo 826349 1864457 := bstep (se 2 (by rfl) ⟨699171, by rfl⟩ : syracuseStep 1864457 = 1398343) B1398343
theorem B1864511 : Blo 826349 1864511 := bstep (se 1 (by rfl) ⟨1398383, by rfl⟩ : syracuseStep 1864511 = 2796767) B2796767
theorem B1241993 : Blo 826349 1241993 := bstep (se 2 (by rfl) ⟨465747, by rfl⟩ : syracuseStep 1241993 = 931495) B931495
theorem B1864655 : Blo 826349 1864655 := bstep (se 1 (by rfl) ⟨1398491, by rfl⟩ : syracuseStep 1864655 = 2796983) B2796983
theorem B7074809 : Blo 826349 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B10613753 : Blo 826349 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B1864745 : Blo 826349 1864745 := bstep (se 2 (by rfl) ⟨699279, by rfl⟩ : syracuseStep 1864745 = 1398559) B1398559
theorem B1274951 : Blo 826349 1274951 := bstep (se 1 (by rfl) ⟨956213, by rfl⟩ : syracuseStep 1274951 = 1912427) B1912427
theorem B1963271 : Blo 826349 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B1242377 : Blo 826349 1242377 := bstep (se 2 (by rfl) ⟨465891, by rfl⟩ : syracuseStep 1242377 = 931783) B931783
theorem B1242431 : Blo 826349 1242431 := bstep (se 1 (by rfl) ⟨931823, by rfl⟩ : syracuseStep 1242431 = 1863647) B1863647
theorem B1865033 : Blo 826349 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B3143083 : Blo 826349 3143083 := bstep (se 1 (by rfl) ⟨2357312, by rfl⟩ : syracuseStep 3143083 = 4714625) B4714625
theorem B10057159 : Blo 826349 10057159 := bstep (se 1 (by rfl) ⟨7542869, by rfl⟩ : syracuseStep 10057159 = 15085739) B15085739
theorem B1570259 : Blo 826349 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B2356847 : Blo 826349 2356847 := bstep (se 1 (by rfl) ⟨1767635, by rfl⟩ : syracuseStep 2356847 = 3535271) B3535271
theorem B1242857 : Blo 826349 1242857 := bstep (se 2 (by rfl) ⟨466071, by rfl⟩ : syracuseStep 1242857 = 932143) B932143
theorem B1242863 : Blo 826349 1242863 := bstep (se 1 (by rfl) ⟨932147, by rfl⟩ : syracuseStep 1242863 = 1864295) B1864295
theorem B882523 : Blo 826349 882523 := bstep (se 1 (by rfl) ⟨661892, by rfl⟩ : syracuseStep 882523 = 1323785) B1323785
theorem B1243319 : Blo 826349 1243319 := bstep (se 1 (by rfl) ⟨932489, by rfl⟩ : syracuseStep 1243319 = 1864979) B1864979
theorem B1243367 : Blo 826349 1243367 := bstep (se 1 (by rfl) ⟨932525, by rfl⟩ : syracuseStep 1243367 = 1865051) B1865051
theorem B1177831 : Blo 826349 1177831 := bstep (se 1 (by rfl) ⟨883373, by rfl⟩ : syracuseStep 1177831 = 1766747) B1766747
theorem B1866023 : Blo 826349 1866023 := bstep (se 1 (by rfl) ⟨1399517, by rfl⟩ : syracuseStep 1866023 = 2799035) B2799035
theorem B3537199 : Blo 826349 3537199 := bstep (se 1 (by rfl) ⟨2652899, by rfl⟩ : syracuseStep 3537199 = 5305799) B5305799
theorem B3537371 : Blo 826349 3537371 := bstep (se 1 (by rfl) ⟨2653028, by rfl⟩ : syracuseStep 3537371 = 5306057) B5306057
theorem B1767977 : Blo 826349 1767977 := bstep (se 2 (by rfl) ⟨662991, by rfl⟩ : syracuseStep 1767977 = 1325983) B1325983
theorem B1243739 : Blo 826349 1243739 := bstep (se 1 (by rfl) ⟨932804, by rfl⟩ : syracuseStep 1243739 = 1865609) B1865609
theorem B1866383 : Blo 826349 1866383 := bstep (se 1 (by rfl) ⟨1399787, by rfl⟩ : syracuseStep 1866383 = 2799575) B2799575
theorem B1866473 : Blo 826349 1866473 := bstep (se 2 (by rfl) ⟨699927, by rfl⟩ : syracuseStep 1866473 = 1399855) B1399855
theorem B1243883 : Blo 826349 1243883 := bstep (se 1 (by rfl) ⟨932912, by rfl⟩ : syracuseStep 1243883 = 1865825) B1865825
theorem B1243913 : Blo 826349 1243913 := bstep (se 2 (by rfl) ⟨466467, by rfl⟩ : syracuseStep 1243913 = 932935) B932935
theorem B1866707 : Blo 826349 1866707 := bstep (se 1 (by rfl) ⟨1400030, by rfl⟩ : syracuseStep 1866707 = 2800061) B2800061
theorem B232815779 : Blo 826349 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B2096351 : Blo 826349 2096351 := bstep (se 1 (by rfl) ⟨1572263, by rfl⟩ : syracuseStep 2096351 = 3144527) B3144527
theorem B1866977 : Blo 826349 1866977 := bstep (se 2 (by rfl) ⟨700116, by rfl⟩ : syracuseStep 1866977 = 1400233) B1400233
theorem B6290783 : Blo 826349 6290783 := bstep (se 1 (by rfl) ⟨4718087, by rfl⟩ : syracuseStep 6290783 = 9436175) B9436175
theorem B1768873 : Blo 826349 1768873 := bstep (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) B1326655
theorem B1703339 : Blo 826349 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B1572347 : Blo 826349 1572347 := bstep (se 1 (by rfl) ⟨1179260, by rfl⟩ : syracuseStep 1572347 = 2358521) B2358521
theorem B1867283 : Blo 826349 1867283 := bstep (se 1 (by rfl) ⟨1400462, by rfl⟩ : syracuseStep 1867283 = 2800925) B2800925
theorem B1244783 : Blo 826349 1244783 := bstep (se 1 (by rfl) ⟨933587, by rfl⟩ : syracuseStep 1244783 = 1867175) B1867175
theorem B1244903 : Blo 826349 1244903 := bstep (se 1 (by rfl) ⟨933677, by rfl⟩ : syracuseStep 1244903 = 1867355) B1867355
theorem B5046097 : Blo 826349 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B1245095 : Blo 826349 1245095 := bstep (se 1 (by rfl) ⟨933821, by rfl⟩ : syracuseStep 1245095 = 1867643) B1867643
theorem B1245311 : Blo 826349 1245311 := bstep (se 1 (by rfl) ⟨933983, by rfl⟩ : syracuseStep 1245311 = 1867967) B1867967
theorem B1049375 : Blo 826349 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B8520511 : Blo 826349 8520511 := bstep (se 1 (by rfl) ⟨6390383, by rfl⟩ : syracuseStep 8520511 = 12780767) B12780767
theorem B1049851 : Blo 826349 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B2098831 : Blo 826349 2098831 := bstep (se 1 (by rfl) ⟨1574123, by rfl⟩ : syracuseStep 2098831 = 3148247) B3148247
theorem B1574633 : Blo 826349 1574633 := bstep (se 2 (by rfl) ⟨590487, by rfl⟩ : syracuseStep 1574633 = 1180975) B1180975
theorem B1771283 : Blo 826349 1771283 := bstep (se 1 (by rfl) ⟨1328462, by rfl⟩ : syracuseStep 1771283 = 2656925) B2656925
theorem B4720457 : Blo 826349 4720457 := bstep (se 2 (by rfl) ⟨1770171, by rfl⟩ : syracuseStep 4720457 = 3540343) B3540343
theorem B2099135 : Blo 826349 2099135 := bstep (se 1 (by rfl) ⟨1574351, by rfl⟩ : syracuseStep 2099135 = 3148703) B3148703
theorem B1181675 : Blo 826349 1181675 := bstep (se 1 (by rfl) ⟨886256, by rfl⟩ : syracuseStep 1181675 = 1772513) B1772513
theorem B1117415 : Blo 826349 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B2362621 : Blo 826349 2362621 := bstep (se 3 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 2362621 = 885983) B885983
theorem B4197743 : Blo 826349 4197743 := bstep (se 1 (by rfl) ⟨3148307, by rfl⟩ : syracuseStep 4197743 = 6296615) B6296615
theorem B2363327 : Blo 826349 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B2101211 : Blo 826349 2101211 := bstep (se 1 (by rfl) ⟨1575908, by rfl⟩ : syracuseStep 2101211 = 3151817) B3151817
theorem B2101241 : Blo 826349 2101241 := bstep (se 2 (by rfl) ⟨787965, by rfl⟩ : syracuseStep 2101241 = 1575931) B1575931
theorem B2658359 : Blo 826349 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B5738849 : Blo 826349 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B7573949 : Blo 826349 7573949 := bstep (se 3 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 7573949 = 2840231) B2840231
theorem B4199849 : Blo 826349 4199849 := bstep (se 2 (by rfl) ⟨1574943, by rfl⟩ : syracuseStep 4199849 = 3149887) B3149887
theorem B2791259 : Blo 826349 2791259 := bstep (se 1 (by rfl) ⟨2093444, by rfl⟩ : syracuseStep 2791259 = 4186889) B4186889
theorem B9443465 : Blo 826349 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B4200659 : Blo 826349 4200659 := bstep (se 1 (by rfl) ⟨3150494, by rfl⟩ : syracuseStep 4200659 = 6300989) B6300989
theorem B2693459 : Blo 826349 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B10099201 : Blo 826349 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B3546017 : Blo 826349 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B33987575 : Blo 826349 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B826363 : Blo 826349 826363 := bstep (se 1 (by rfl) ⟨619772, by rfl⟩ : syracuseStep 826363 = 1239545) B1239545
theorem B826399 : Blo 826349 826399 := bstep (se 1 (by rfl) ⟨619799, by rfl⟩ : syracuseStep 826399 = 1239599) B1239599
theorem B1678367 : Blo 826349 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B13409545 : Blo 826349 13409545 := bstep (se 2 (by rfl) ⟨5028579, by rfl⟩ : syracuseStep 13409545 = 10057159) B10057159
theorem B826687 : Blo 826349 826687 := bstep (se 1 (by rfl) ⟨620015, by rfl⟩ : syracuseStep 826687 = 1240031) B1240031
theorem B826983 : Blo 826349 826983 := bstep (se 1 (by rfl) ⟨620237, by rfl⟩ : syracuseStep 826983 = 1240475) B1240475
theorem B4202279 : Blo 826349 4202279 := bstep (se 1 (by rfl) ⟨3151709, by rfl⟩ : syracuseStep 4202279 = 6303419) B6303419
theorem B827263 : Blo 826349 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B9805711 : Blo 826349 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B827387 : Blo 826349 827387 := bstep (se 1 (by rfl) ⟨620540, by rfl⟩ : syracuseStep 827387 = 1241081) B1241081
theorem B827547 : Blo 826349 827547 := bstep (se 1 (by rfl) ⟨620660, by rfl⟩ : syracuseStep 827547 = 1241321) B1241321
theorem B2990267 : Blo 826349 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B827631 : Blo 826349 827631 := bstep (se 1 (by rfl) ⟨620723, by rfl⟩ : syracuseStep 827631 = 1241447) B1241447
theorem B827995 : Blo 826349 827995 := bstep (se 1 (by rfl) ⟨620996, by rfl⟩ : syracuseStep 827995 = 1241993) B1241993
theorem B828251 : Blo 826349 828251 := bstep (se 1 (by rfl) ⟨621188, by rfl⟩ : syracuseStep 828251 = 1242377) B1242377
theorem B10625903 : Blo 826349 10625903 := bstep (se 1 (by rfl) ⟨7969427, by rfl⟩ : syracuseStep 10625903 = 15938855) B15938855
theorem B828287 : Blo 826349 828287 := bstep (se 1 (by rfl) ⟨621215, by rfl⟩ : syracuseStep 828287 = 1242431) B1242431
theorem B9446381 : Blo 826349 9446381 := bstep (se 3 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 9446381 = 3542393) B3542393
theorem B6824989 : Blo 826349 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B828571 : Blo 826349 828571 := bstep (se 1 (by rfl) ⟨621428, by rfl⟩ : syracuseStep 828571 = 1242857) B1242857
theorem B828575 : Blo 826349 828575 := bstep (se 1 (by rfl) ⟨621431, by rfl⟩ : syracuseStep 828575 = 1242863) B1242863
theorem B828879 : Blo 826349 828879 := bstep (se 1 (by rfl) ⟨621659, by rfl⟩ : syracuseStep 828879 = 1243319) B1243319
theorem B828911 : Blo 826349 828911 := bstep (se 1 (by rfl) ⟨621683, by rfl⟩ : syracuseStep 828911 = 1243367) B1243367
theorem B829159 : Blo 826349 829159 := bstep (se 1 (by rfl) ⟨621869, by rfl⟩ : syracuseStep 829159 = 1243739) B1243739
theorem B829255 : Blo 826349 829255 := bstep (se 1 (by rfl) ⟨621941, by rfl⟩ : syracuseStep 829255 = 1243883) B1243883
theorem B829275 : Blo 826349 829275 := bstep (se 1 (by rfl) ⟨621956, by rfl⟩ : syracuseStep 829275 = 1243913) B1243913
theorem B6891641 : Blo 826349 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B829855 : Blo 826349 829855 := bstep (se 1 (by rfl) ⟨622391, by rfl⟩ : syracuseStep 829855 = 1244783) B1244783
theorem B6728129 : Blo 826349 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B829935 : Blo 826349 829935 := bstep (se 1 (by rfl) ⟨622451, by rfl⟩ : syracuseStep 829935 = 1244903) B1244903
theorem B5319179 : Blo 826349 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B21178907 : Blo 826349 21178907 := bstep (se 1 (by rfl) ⟨15884180, by rfl⟩ : syracuseStep 21178907 = 31768361) B31768361
theorem B830063 : Blo 826349 830063 := bstep (se 1 (by rfl) ⟨622547, by rfl⟩ : syracuseStep 830063 = 1245095) B1245095
theorem B40381213 : Blo 826349 40381213 := bstep (se 3 (by rfl) ⟨7571477, by rfl⟩ : syracuseStep 40381213 = 15142955) B15142955
theorem B830279 : Blo 826349 830279 := bstep (se 1 (by rfl) ⟨622709, by rfl⟩ : syracuseStep 830279 = 1245419) B1245419
theorem B830319 : Blo 826349 830319 := bstep (se 1 (by rfl) ⟨622739, by rfl⟩ : syracuseStep 830319 = 1245479) B1245479
theorem B2796713 : Blo 826349 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B6368951 : Blo 826349 6368951 := bstep (se 1 (by rfl) ⟨4776713, by rfl⟩ : syracuseStep 6368951 = 9553427) B9553427
theorem B9449297 : Blo 826349 9449297 := bstep (se 2 (by rfl) ⟨3543486, by rfl⟩ : syracuseStep 9449297 = 7086973) B7086973
theorem B1257535 : Blo 826349 1257535 := bstep (se 1 (by rfl) ⟨943151, by rfl⟩ : syracuseStep 1257535 = 1886303) B1886303
theorem B12726395 : Blo 826349 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B6303905 : Blo 826349 6303905 := bstep (se 2 (by rfl) ⟨2363964, by rfl⟩ : syracuseStep 6303905 = 4727929) B4727929
theorem B27178681 : Blo 826349 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B15906941 : Blo 826349 15906941 := bstep (se 3 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 15906941 = 5965103) B5965103
theorem B2800169 : Blo 826349 2800169 := bstep (se 2 (by rfl) ⟨1050063, by rfl⟩ : syracuseStep 2800169 = 2100127) B2100127
theorem B10075843 : Blo 826349 10075843 := bstep (se 1 (by rfl) ⟨7556882, by rfl⟩ : syracuseStep 10075843 = 15113765) B15113765
theorem B2801627 : Blo 826349 2801627 := bstep (se 1 (by rfl) ⟨2101220, by rfl⟩ : syracuseStep 2801627 = 4202441) B4202441
theorem B1327367 : Blo 826349 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B550879501 : Blo 826349 550879501 := bstep (se 3 (by rfl) ⟨103289906, by rfl⟩ : syracuseStep 550879501 = 206579813) B206579813
theorem B2802059 : Blo 826349 2802059 := bstep (se 1 (by rfl) ⟨2101544, by rfl⟩ : syracuseStep 2802059 = 4203089) B4203089
theorem B130892591 : Blo 826349 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B8078413 : Blo 826349 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B6276203 : Blo 826349 6276203 := bstep (se 1 (by rfl) ⟨4707152, by rfl⟩ : syracuseStep 6276203 = 9414305) B9414305
theorem B5294909 : Blo 826349 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B4246685 : Blo 826349 4246685 := bstep (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) B1592507
theorem B6279119 : Blo 826349 6279119 := bstep (se 1 (by rfl) ⟨4709339, by rfl⟩ : syracuseStep 6279119 = 9418679) B9418679
theorem B9458045 : Blo 826349 9458045 := bstep (se 3 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 9458045 = 3546767) B3546767
theorem B1987129 : Blo 826349 1987129 := bstep (se 2 (by rfl) ⟨745173, by rfl⟩ : syracuseStep 1987129 = 1490347) B1490347
theorem B39342665 : Blo 826349 39342665 := bstep (se 2 (by rfl) ⟨14753499, by rfl⟩ : syracuseStep 39342665 = 29506999) B29506999
theorem B155210519 : Blo 826349 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1397567 : Blo 826349 1397567 := bstep (se 1 (by rfl) ⟨1048175, by rfl⟩ : syracuseStep 1397567 = 2096351) B2096351
theorem B3363709 : Blo 826349 3363709 := bstep (se 3 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 3363709 = 1261391) B1261391
theorem B6280091 : Blo 826349 6280091 := bstep (se 1 (by rfl) ⟨4710068, by rfl⟩ : syracuseStep 6280091 = 9420137) B9420137
theorem B3986347 : Blo 826349 3986347 := bstep (se 1 (by rfl) ⟨2989760, by rfl⟩ : syracuseStep 3986347 = 5979521) B5979521
theorem B1135559 : Blo 826349 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B76403735 : Blo 826349 76403735 := bstep (se 1 (by rfl) ⟨57302801, by rfl⟩ : syracuseStep 76403735 = 114605603) B114605603
theorem B4708043 : Blo 826349 4708043 := bstep (se 1 (by rfl) ⟨3531032, by rfl⟩ : syracuseStep 4708043 = 7062065) B7062065
theorem B1398505 : Blo 826349 1398505 := bstep (se 2 (by rfl) ⟨524439, by rfl⟩ : syracuseStep 1398505 = 1048879) B1048879
theorem B1398971 : Blo 826349 1398971 := bstep (se 1 (by rfl) ⟨1049228, by rfl⟩ : syracuseStep 1398971 = 2098457) B2098457
theorem B4479191 : Blo 826349 4479191 := bstep (se 1 (by rfl) ⟨3359393, by rfl⟩ : syracuseStep 4479191 = 6718787) B6718787
theorem B4184297 : Blo 826349 4184297 := bstep (se 2 (by rfl) ⟨1569111, by rfl⟩ : syracuseStep 4184297 = 3138223) B3138223
theorem B6380927 : Blo 826349 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B4186241 : Blo 826349 4186241 := bstep (se 2 (by rfl) ⟨1569840, by rfl⟩ : syracuseStep 4186241 = 3139681) B3139681
theorem B1401023 : Blo 826349 1401023 := bstep (se 1 (by rfl) ⟨1050767, by rfl⟩ : syracuseStep 1401023 = 2101535) B2101535
theorem B1861199 : Blo 826349 1861199 := bstep (se 1 (by rfl) ⟨1395899, by rfl⟩ : syracuseStep 1861199 = 2791799) B2791799
theorem B2647723 : Blo 826349 2647723 := bstep (se 1 (by rfl) ⟨1985792, by rfl⟩ : syracuseStep 2647723 = 3971585) B3971585
theorem B4253705 : Blo 826349 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B3532895 : Blo 826349 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B22931585 : Blo 826349 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B8972531 : Blo 826349 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B34007303 : Blo 826349 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B1861919 : Blo 826349 1861919 := bstep (se 1 (by rfl) ⟨1396439, by rfl⟩ : syracuseStep 1861919 = 2792879) B2792879
theorem B1239527 : Blo 826349 1239527 := bstep (se 1 (by rfl) ⟨929645, by rfl⟩ : syracuseStep 1239527 = 1859291) B1859291
theorem B4254239 : Blo 826349 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B1239707 : Blo 826349 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B4188833 : Blo 826349 4188833 := bstep (se 2 (by rfl) ⟨1570812, by rfl⟩ : syracuseStep 4188833 = 3141625) B3141625
theorem B1862441 : Blo 826349 1862441 := bstep (se 2 (by rfl) ⟨698415, by rfl⟩ : syracuseStep 1862441 = 1396831) B1396831
theorem B1239929 : Blo 826349 1239929 := bstep (se 2 (by rfl) ⟨464973, by rfl⟩ : syracuseStep 1239929 = 929947) B929947
theorem B2648953 : Blo 826349 2648953 := bstep (se 2 (by rfl) ⟨993357, by rfl⟩ : syracuseStep 2648953 = 1986715) B1986715
theorem B1862711 : Blo 826349 1862711 := bstep (se 1 (by rfl) ⟨1397033, by rfl⟩ : syracuseStep 1862711 = 2794067) B2794067
theorem B2518087 : Blo 826349 2518087 := bstep (se 1 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 2518087 = 3777131) B3777131
theorem B1240175 : Blo 826349 1240175 := bstep (se 1 (by rfl) ⟨930131, by rfl⟩ : syracuseStep 1240175 = 1860263) B1860263
theorem B2092169 : Blo 826349 2092169 := bstep (se 2 (by rfl) ⟨784563, by rfl⟩ : syracuseStep 2092169 = 1569127) B1569127
theorem B1240271 : Blo 826349 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B1862891 : Blo 826349 1862891 := bstep (se 1 (by rfl) ⟨1397168, by rfl⟩ : syracuseStep 1862891 = 2794337) B2794337
theorem B1240391 : Blo 826349 1240391 := bstep (se 1 (by rfl) ⟨930293, by rfl⟩ : syracuseStep 1240391 = 1860587) B1860587
theorem B1240679 : Blo 826349 1240679 := bstep (se 1 (by rfl) ⟨930509, by rfl⟩ : syracuseStep 1240679 = 1861019) B1861019
theorem B16969661 : Blo 826349 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B1994711 : Blo 826349 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B1241063 : Blo 826349 1241063 := bstep (se 1 (by rfl) ⟨930797, by rfl⟩ : syracuseStep 1241063 = 1861595) B1861595
theorem B2387999 : Blo 826349 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B1863719 : Blo 826349 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B2093111 : Blo 826349 2093111 := bstep (se 1 (by rfl) ⟨1569833, by rfl⟩ : syracuseStep 2093111 = 3139667) B3139667
theorem B4190291 : Blo 826349 4190291 := bstep (se 1 (by rfl) ⟨3142718, by rfl⟩ : syracuseStep 4190291 = 6285437) B6285437
theorem B1241183 : Blo 826349 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B1241243 : Blo 826349 1241243 := bstep (se 1 (by rfl) ⟨930932, by rfl⟩ : syracuseStep 1241243 = 1861865) B1861865
theorem B1863899 : Blo 826349 1863899 := bstep (se 1 (by rfl) ⟨1397924, by rfl⟩ : syracuseStep 1863899 = 2795849) B2795849
theorem B2650439 : Blo 826349 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B1864007 : Blo 826349 1864007 := bstep (se 1 (by rfl) ⟨1398005, by rfl⟩ : syracuseStep 1864007 = 2796011) B2796011
theorem B1241423 : Blo 826349 1241423 := bstep (se 1 (by rfl) ⟨931067, by rfl⟩ : syracuseStep 1241423 = 1862135) B1862135
theorem B1765729 : Blo 826349 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B1241513 : Blo 826349 1241513 := bstep (se 2 (by rfl) ⟨465567, by rfl⟩ : syracuseStep 1241513 = 931135) B931135
theorem B1864169 : Blo 826349 1864169 := bstep (se 2 (by rfl) ⟨699063, by rfl⟩ : syracuseStep 1864169 = 1398127) B1398127
theorem B4190777 : Blo 826349 4190777 := bstep (se 2 (by rfl) ⟨1571541, by rfl⟩ : syracuseStep 4190777 = 3143083) B3143083
theorem B4190939 : Blo 826349 4190939 := bstep (se 1 (by rfl) ⟨3143204, by rfl⟩ : syracuseStep 4190939 = 6286409) B6286409
theorem B1241819 : Blo 826349 1241819 := bstep (se 1 (by rfl) ⟨931364, by rfl⟩ : syracuseStep 1241819 = 1862729) B1862729
theorem B1242089 : Blo 826349 1242089 := bstep (se 2 (by rfl) ⟨465783, by rfl⟩ : syracuseStep 1242089 = 931567) B931567
theorem B1864799 : Blo 826349 1864799 := bstep (se 1 (by rfl) ⟨1398599, by rfl⟩ : syracuseStep 1864799 = 2797199) B2797199
theorem B1176697 : Blo 826349 1176697 := bstep (se 2 (by rfl) ⟨441261, by rfl⟩ : syracuseStep 1176697 = 882523) B882523
theorem B1242233 : Blo 826349 1242233 := bstep (se 2 (by rfl) ⟨465837, by rfl⟩ : syracuseStep 1242233 = 931675) B931675
theorem B2356391 : Blo 826349 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B6288839 : Blo 826349 6288839 := bstep (se 1 (by rfl) ⟨4716629, by rfl⟩ : syracuseStep 6288839 = 9433259) B9433259
theorem B5043667 : Blo 826349 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B1570441 : Blo 826349 1570441 := bstep (se 2 (by rfl) ⟨588915, by rfl⟩ : syracuseStep 1570441 = 1177831) B1177831
theorem B1242761 : Blo 826349 1242761 := bstep (se 2 (by rfl) ⟨466035, by rfl⟩ : syracuseStep 1242761 = 932071) B932071
theorem B4191911 : Blo 826349 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B4716265 : Blo 826349 4716265 := bstep (se 2 (by rfl) ⟨1768599, by rfl⟩ : syracuseStep 4716265 = 3537199) B3537199
theorem B1767199 : Blo 826349 1767199 := bstep (se 1 (by rfl) ⟨1325399, by rfl⟩ : syracuseStep 1767199 = 2650799) B2650799
theorem B2357063 : Blo 826349 2357063 := bstep (se 1 (by rfl) ⟨1767797, by rfl⟩ : syracuseStep 2357063 = 3535595) B3535595
theorem B1242971 : Blo 826349 1242971 := bstep (se 1 (by rfl) ⟨932228, by rfl⟩ : syracuseStep 1242971 = 1864457) B1864457
theorem B1243007 : Blo 826349 1243007 := bstep (se 1 (by rfl) ⟨932255, by rfl⟩ : syracuseStep 1243007 = 1864511) B1864511
theorem B1243103 : Blo 826349 1243103 := bstep (se 1 (by rfl) ⟨932327, by rfl⟩ : syracuseStep 1243103 = 1864655) B1864655
theorem B4716539 : Blo 826349 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B7075835 : Blo 826349 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B1243163 : Blo 826349 1243163 := bstep (se 1 (by rfl) ⟨932372, by rfl⟩ : syracuseStep 1243163 = 1864745) B1864745
theorem B849967 : Blo 826349 849967 := bstep (se 1 (by rfl) ⟨637475, by rfl⟩ : syracuseStep 849967 = 1274951) B1274951
theorem B1308847 : Blo 826349 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B1243355 : Blo 826349 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B1046839 : Blo 826349 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B1571231 : Blo 826349 1571231 := bstep (se 1 (by rfl) ⟨1178423, by rfl⟩ : syracuseStep 1571231 = 2356847) B2356847
theorem B1243625 : Blo 826349 1243625 := bstep (se 2 (by rfl) ⟨466359, by rfl⟩ : syracuseStep 1243625 = 932719) B932719
theorem B1244015 : Blo 826349 1244015 := bstep (se 1 (by rfl) ⟨933011, by rfl⟩ : syracuseStep 1244015 = 1866023) B1866023
theorem B2358247 : Blo 826349 2358247 := bstep (se 1 (by rfl) ⟨1768685, by rfl⟩ : syracuseStep 2358247 = 3537371) B3537371
theorem B1178651 : Blo 826349 1178651 := bstep (se 1 (by rfl) ⟨883988, by rfl⟩ : syracuseStep 1178651 = 1767977) B1767977
theorem B1244255 : Blo 826349 1244255 := bstep (se 1 (by rfl) ⟨933191, by rfl⟩ : syracuseStep 1244255 = 1866383) B1866383
theorem B1244315 : Blo 826349 1244315 := bstep (se 1 (by rfl) ⟨933236, by rfl⟩ : syracuseStep 1244315 = 1866473) B1866473
theorem B2358497 : Blo 826349 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B1244471 : Blo 826349 1244471 := bstep (se 1 (by rfl) ⟨933353, by rfl⟩ : syracuseStep 1244471 = 1866707) B1866707
theorem B2522551 : Blo 826349 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1244651 : Blo 826349 1244651 := bstep (se 1 (by rfl) ⟨933488, by rfl⟩ : syracuseStep 1244651 = 1866977) B1866977
theorem B1867247 : Blo 826349 1867247 := bstep (se 1 (by rfl) ⟨1400435, by rfl⟩ : syracuseStep 1867247 = 2800871) B2800871
theorem B4193855 : Blo 826349 4193855 := bstep (se 1 (by rfl) ⟨3145391, by rfl⟩ : syracuseStep 4193855 = 6290783) B6290783
theorem B1048231 : Blo 826349 1048231 := bstep (se 1 (by rfl) ⟨786173, by rfl⟩ : syracuseStep 1048231 = 1572347) B1572347
theorem B1244855 : Blo 826349 1244855 := bstep (se 1 (by rfl) ⟨933641, by rfl⟩ : syracuseStep 1244855 = 1867283) B1867283
theorem B1245065 : Blo 826349 1245065 := bstep (se 2 (by rfl) ⟨466899, by rfl⟩ : syracuseStep 1245065 = 933799) B933799
theorem B19136405 : Blo 826349 19136405 := bstep (se 6 (by rfl) ⟨448509, by rfl⟩ : syracuseStep 19136405 = 897019) B897019
theorem B1868039 : Blo 826349 1868039 := bstep (se 1 (by rfl) ⟨1401029, by rfl⟩ : syracuseStep 1868039 = 2802059) B2802059
theorem B3539645 : Blo 826349 3539645 := bstep (se 3 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 3539645 = 1327367) B1327367
theorem B1049755 : Blo 826349 1049755 := bstep (se 1 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 1049755 = 1574633) B1574633
theorem B1180855 : Blo 826349 1180855 := bstep (se 1 (by rfl) ⟨885641, by rfl⟩ : syracuseStep 1180855 = 1771283) B1771283
theorem B3146971 : Blo 826349 3146971 := bstep (se 1 (by rfl) ⟨2360228, by rfl⟩ : syracuseStep 3146971 = 4720457) B4720457
theorem B413894717 : Blo 826349 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B349046909 : Blo 826349 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B1575551 : Blo 826349 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B5049299 : Blo 826349 5049299 := bstep (se 1 (by rfl) ⟨3786974, by rfl⟩ : syracuseStep 5049299 = 7573949) B7573949
theorem B53841617 : Blo 826349 53841617 := bstep (se 2 (by rfl) ⟨20190606, by rfl⟩ : syracuseStep 53841617 = 40381213) B40381213
theorem B6295643 : Blo 826349 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B2986127 : Blo 826349 2986127 := bstep (se 1 (by rfl) ⟨2239595, by rfl⟩ : syracuseStep 2986127 = 4479191) B4479191
theorem B2789531 : Blo 826349 2789531 := bstep (se 1 (by rfl) ⟨2092148, by rfl⟩ : syracuseStep 2789531 = 4184297) B4184297
theorem B3150161 : Blo 826349 3150161 := bstep (se 2 (by rfl) ⟨1181310, by rfl⟩ : syracuseStep 3150161 = 2362621) B2362621
theorem B2364011 : Blo 826349 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B3151133 : Blo 826349 3151133 := bstep (se 3 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 3151133 = 1181675) B1181675
theorem B1676713 : Blo 826349 1676713 := bstep (se 2 (by rfl) ⟨628767, by rfl⟩ : syracuseStep 1676713 = 1257535) B1257535
theorem B2790827 : Blo 826349 2790827 := bstep (se 1 (by rfl) ⟨2093120, by rfl⟩ : syracuseStep 2790827 = 4186241) B4186241
theorem B7083935 : Blo 826349 7083935 := bstep (se 1 (by rfl) ⟨5312951, by rfl⟩ : syracuseStep 7083935 = 10625903) B10625903
theorem B6297587 : Blo 826349 6297587 := bstep (se 1 (by rfl) ⟨4723190, by rfl⟩ : syracuseStep 6297587 = 9446381) B9446381
theorem B7182557 : Blo 826349 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B5315129 : Blo 826349 5315129 := bstep (se 2 (by rfl) ⟨1993173, by rfl⟩ : syracuseStep 5315129 = 3986347) B3986347
theorem B4594427 : Blo 826349 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B11344637 : Blo 826349 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B826351 : Blo 826349 826351 := bstep (se 1 (by rfl) ⟨619763, by rfl⟩ : syracuseStep 826351 = 1239527) B1239527
theorem B3546119 : Blo 826349 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B826471 : Blo 826349 826471 := bstep (se 1 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 826471 = 1239707) B1239707
theorem B2792555 : Blo 826349 2792555 := bstep (se 1 (by rfl) ⟨2094416, by rfl⟩ : syracuseStep 2792555 = 4188833) B4188833
theorem B826619 : Blo 826349 826619 := bstep (se 1 (by rfl) ⟨619964, by rfl⟩ : syracuseStep 826619 = 1239929) B1239929
theorem B6724889 : Blo 826349 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B826783 : Blo 826349 826783 := bstep (se 1 (by rfl) ⟨620087, by rfl⟩ : syracuseStep 826783 = 1240175) B1240175
theorem B826847 : Blo 826349 826847 := bstep (se 1 (by rfl) ⟨620135, by rfl⟩ : syracuseStep 826847 = 1240271) B1240271
theorem B826927 : Blo 826349 826927 := bstep (se 1 (by rfl) ⟨620195, by rfl⟩ : syracuseStep 826927 = 1240391) B1240391
theorem B827119 : Blo 826349 827119 := bstep (se 1 (by rfl) ⟨620339, by rfl⟩ : syracuseStep 827119 = 1240679) B1240679
theorem B6299531 : Blo 826349 6299531 := bstep (se 1 (by rfl) ⟨4724648, by rfl⟩ : syracuseStep 6299531 = 9449297) B9449297
theorem B11313107 : Blo 826349 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B827375 : Blo 826349 827375 := bstep (se 1 (by rfl) ⟨620531, by rfl⟩ : syracuseStep 827375 = 1241063) B1241063
theorem B2793527 : Blo 826349 2793527 := bstep (se 1 (by rfl) ⟨2095145, by rfl⟩ : syracuseStep 2793527 = 4190291) B4190291
theorem B827455 : Blo 826349 827455 := bstep (se 1 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 827455 = 1241183) B1241183
theorem B827495 : Blo 826349 827495 := bstep (se 1 (by rfl) ⟨620621, by rfl⟩ : syracuseStep 827495 = 1241243) B1241243
theorem B4202603 : Blo 826349 4202603 := bstep (se 1 (by rfl) ⟨3151952, by rfl⟩ : syracuseStep 4202603 = 6303905) B6303905
theorem B827615 : Blo 826349 827615 := bstep (se 1 (by rfl) ⟨620711, by rfl⟩ : syracuseStep 827615 = 1241423) B1241423
theorem B1745129 : Blo 826349 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B827675 : Blo 826349 827675 := bstep (se 1 (by rfl) ⟨620756, by rfl⟩ : syracuseStep 827675 = 1241513) B1241513
theorem B2793851 : Blo 826349 2793851 := bstep (se 1 (by rfl) ⟨2095388, by rfl⟩ : syracuseStep 2793851 = 4190777) B4190777
theorem B2793959 : Blo 826349 2793959 := bstep (se 1 (by rfl) ⟨2095469, by rfl⟩ : syracuseStep 2793959 = 4190939) B4190939
theorem B827879 : Blo 826349 827879 := bstep (se 1 (by rfl) ⟨620909, by rfl⟩ : syracuseStep 827879 = 1241819) B1241819
theorem B828059 : Blo 826349 828059 := bstep (se 1 (by rfl) ⟨621044, by rfl⟩ : syracuseStep 828059 = 1242089) B1242089
theorem B828155 : Blo 826349 828155 := bstep (se 1 (by rfl) ⟨621116, by rfl⟩ : syracuseStep 828155 = 1242233) B1242233
theorem B828507 : Blo 826349 828507 := bstep (se 1 (by rfl) ⟨621380, by rfl⟩ : syracuseStep 828507 = 1242761) B1242761
theorem B2794607 : Blo 826349 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B828647 : Blo 826349 828647 := bstep (se 1 (by rfl) ⟨621485, by rfl⟩ : syracuseStep 828647 = 1242971) B1242971
theorem B828671 : Blo 826349 828671 := bstep (se 1 (by rfl) ⟨621503, by rfl⟩ : syracuseStep 828671 = 1243007) B1243007
theorem B828735 : Blo 826349 828735 := bstep (se 1 (by rfl) ⟨621551, by rfl⟩ : syracuseStep 828735 = 1243103) B1243103
theorem B828775 : Blo 826349 828775 := bstep (se 1 (by rfl) ⟨621581, by rfl⟩ : syracuseStep 828775 = 1243163) B1243163
theorem B828903 : Blo 826349 828903 := bstep (se 1 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 828903 = 1243355) B1243355
theorem B829083 : Blo 826349 829083 := bstep (se 1 (by rfl) ⟨621812, by rfl⟩ : syracuseStep 829083 = 1243625) B1243625
theorem B829343 : Blo 826349 829343 := bstep (se 1 (by rfl) ⟨622007, by rfl⟩ : syracuseStep 829343 = 1244015) B1244015
theorem B829503 : Blo 826349 829503 := bstep (se 1 (by rfl) ⟨622127, by rfl⟩ : syracuseStep 829503 = 1244255) B1244255
theorem B829543 : Blo 826349 829543 := bstep (se 1 (by rfl) ⟨622157, by rfl⟩ : syracuseStep 829543 = 1244315) B1244315
theorem B829647 : Blo 826349 829647 := bstep (se 1 (by rfl) ⟨622235, by rfl⟩ : syracuseStep 829647 = 1244471) B1244471
theorem B829767 : Blo 826349 829767 := bstep (se 1 (by rfl) ⟨622325, by rfl⟩ : syracuseStep 829767 = 1244651) B1244651
theorem B2795903 : Blo 826349 2795903 := bstep (se 1 (by rfl) ⟨2096927, by rfl⟩ : syracuseStep 2795903 = 4193855) B4193855
theorem B829903 : Blo 826349 829903 := bstep (se 1 (by rfl) ⟨622427, by rfl⟩ : syracuseStep 829903 = 1244855) B1244855
theorem B5319229 : Blo 826349 5319229 := bstep (se 3 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 5319229 = 1994711) B1994711
theorem B830043 : Blo 826349 830043 := bstep (se 1 (by rfl) ⟨622532, by rfl⟩ : syracuseStep 830043 = 1245065) B1245065
theorem B12757603 : Blo 826349 12757603 := bstep (se 1 (by rfl) ⟨9568202, by rfl⟩ : syracuseStep 12757603 = 19136405) B19136405
theorem B6367997 : Blo 826349 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B830207 : Blo 826349 830207 := bstep (se 1 (by rfl) ⟨622655, by rfl⟩ : syracuseStep 830207 = 1245311) B1245311
theorem B7088957 : Blo 826349 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B4533157 : Blo 826349 4533157 := bstep (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) B849967
theorem B734506001 : Blo 826349 734506001 := bstep (se 2 (by rfl) ⟨275439750, by rfl⟩ : syracuseStep 734506001 = 550879501) B550879501
theorem B9417221 : Blo 826349 9417221 := bstep (se 4 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 9417221 = 1765729) B1765729
theorem B2798333 : Blo 826349 2798333 := bstep (se 3 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 2798333 = 1049375) B1049375
theorem B2831123 : Blo 826349 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B2798441 : Blo 826349 2798441 := bstep (se 2 (by rfl) ⟨1049415, by rfl⟩ : syracuseStep 2798441 = 2098831) B2098831
theorem B2798495 : Blo 826349 2798495 := bstep (se 1 (by rfl) ⟨2098871, by rfl⟩ : syracuseStep 2798495 = 4197743) B4197743
theorem B3028157 : Blo 826349 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B6305363 : Blo 826349 6305363 := bstep (se 1 (by rfl) ⟨4729022, by rfl⟩ : syracuseStep 6305363 = 9458045) B9458045
theorem B931711 : Blo 826349 931711 := bstep (se 1 (by rfl) ⟨698783, by rfl⟩ : syracuseStep 931711 = 1397567) B1397567
theorem B50935823 : Blo 826349 50935823 := bstep (se 1 (by rfl) ⟨38201867, by rfl⟩ : syracuseStep 50935823 = 76403735) B76403735
theorem B2799899 : Blo 826349 2799899 := bstep (se 1 (by rfl) ⟨2099924, by rfl⟩ : syracuseStep 2799899 = 4199849) B4199849
theorem B3357449 : Blo 826349 3357449 := bstep (se 2 (by rfl) ⟨1259043, by rfl⟩ : syracuseStep 3357449 = 2518087) B2518087
theorem B932647 : Blo 826349 932647 := bstep (se 1 (by rfl) ⟨699485, by rfl⟩ : syracuseStep 932647 = 1398971) B1398971
theorem B2800439 : Blo 826349 2800439 := bstep (se 1 (by rfl) ⟨2100329, by rfl⟩ : syracuseStep 2800439 = 4200659) B4200659
theorem B22658383 : Blo 826349 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B2801519 : Blo 826349 2801519 := bstep (se 1 (by rfl) ⟨2101139, by rfl⟩ : syracuseStep 2801519 = 4202279) B4202279
theorem B934015 : Blo 826349 934015 := bstep (se 1 (by rfl) ⟨700511, by rfl⟩ : syracuseStep 934015 = 1401023) B1401023
theorem B6275717 : Blo 826349 6275717 := bstep (se 4 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 6275717 = 1176697) B1176697
theorem B2835803 : Blo 826349 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B15287723 : Blo 826349 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B5981687 : Blo 826349 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B1394779 : Blo 826349 1394779 := bstep (se 1 (by rfl) ⟨1046084, by rfl⟩ : syracuseStep 1394779 = 2092169) B2092169
theorem B4245967 : Blo 826349 4245967 := bstep (se 1 (by rfl) ⟨3184475, by rfl⟩ : syracuseStep 4245967 = 6368951) B6368951
theorem B1395407 : Blo 826349 1395407 := bstep (se 1 (by rfl) ⟨1046555, by rfl⟩ : syracuseStep 1395407 = 2093111) B2093111
theorem B4475645 : Blo 826349 4475645 := bstep (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) B1678367
theorem B1395785 : Blo 826349 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B10604627 : Blo 826349 10604627 := bstep (se 1 (by rfl) ⟨7953470, by rfl⟩ : syracuseStep 10604627 = 15906941) B15906941
theorem B17879393 : Blo 826349 17879393 := bstep (se 2 (by rfl) ⟨6704772, by rfl⟩ : syracuseStep 17879393 = 13409545) B13409545
theorem B3363401 : Blo 826349 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B1397641 : Blo 826349 1397641 := bstep (se 2 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 1397641 = 1048231) B1048231
theorem B4184135 : Blo 826349 4184135 := bstep (se 1 (by rfl) ⟨3138101, by rfl⟩ : syracuseStep 4184135 = 6276203) B6276203
theorem B7067837 : Blo 826349 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B11360681 : Blo 826349 11360681 := bstep (se 2 (by rfl) ⟨4260255, by rfl⟩ : syracuseStep 11360681 = 8520511) B8520511
theorem B1399423 : Blo 826349 1399423 := bstep (se 1 (by rfl) ⟨1049567, by rfl⟩ : syracuseStep 1399423 = 2099135) B2099135
theorem B9099985 : Blo 826349 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B10771217 : Blo 826349 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B104913773 : Blo 826349 104913773 := bstep (se 3 (by rfl) ⟨19671332, by rfl⟩ : syracuseStep 104913773 = 39342665) B39342665
theorem B1399801 : Blo 826349 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B3529939 : Blo 826349 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B3530297 : Blo 826349 3530297 := bstep (se 2 (by rfl) ⟨1323861, by rfl⟩ : syracuseStep 3530297 = 2647723) B2647723
theorem B4186079 : Blo 826349 4186079 := bstep (se 1 (by rfl) ⟨3139559, by rfl⟩ : syracuseStep 4186079 = 6279119) B6279119
theorem B1400807 : Blo 826349 1400807 := bstep (se 1 (by rfl) ⟨1050605, by rfl⟩ : syracuseStep 1400807 = 2101211) B2101211
theorem B1400827 : Blo 826349 1400827 := bstep (se 1 (by rfl) ⟨1050620, by rfl⟩ : syracuseStep 1400827 = 2101241) B2101241
theorem B3825899 : Blo 826349 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B4186727 : Blo 826349 4186727 := bstep (se 1 (by rfl) ⟨3140045, by rfl⟩ : syracuseStep 4186727 = 6280091) B6280091
theorem B3138695 : Blo 826349 3138695 := bstep (se 1 (by rfl) ⟨2354021, by rfl⟩ : syracuseStep 3138695 = 4708043) B4708043
theorem B3531937 : Blo 826349 3531937 := bstep (se 2 (by rfl) ⟨1324476, by rfl⟩ : syracuseStep 3531937 = 2648953) B2648953
theorem B1860839 : Blo 826349 1860839 := bstep (se 1 (by rfl) ⟨1395629, by rfl⟩ : syracuseStep 1860839 = 2791259) B2791259
theorem B4253951 : Blo 826349 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B1993511 : Blo 826349 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B2649505 : Blo 826349 2649505 := bstep (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) B1987129
theorem B1240799 : Blo 826349 1240799 := bstep (se 1 (by rfl) ⟨930599, by rfl⟩ : syracuseStep 1240799 = 1861199) B1861199
theorem B4484945 : Blo 826349 4484945 := bstep (se 2 (by rfl) ⟨1681854, by rfl⟩ : syracuseStep 4484945 = 3363709) B3363709
theorem B2355263 : Blo 826349 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B22671535 : Blo 826349 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B1241279 : Blo 826349 1241279 := bstep (se 1 (by rfl) ⟨930959, by rfl⟩ : syracuseStep 1241279 = 1861919) B1861919
theorem B4485419 : Blo 826349 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B14119271 : Blo 826349 14119271 := bstep (se 1 (by rfl) ⟨10589453, by rfl⟩ : syracuseStep 14119271 = 21178907) B21178907
theorem B1241627 : Blo 826349 1241627 := bstep (se 1 (by rfl) ⟨931220, by rfl⟩ : syracuseStep 1241627 = 1862441) B1862441
theorem B1241807 : Blo 826349 1241807 := bstep (se 1 (by rfl) ⟨931355, by rfl⟩ : syracuseStep 1241807 = 1862711) B1862711
theorem B1864475 : Blo 826349 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B1241927 : Blo 826349 1241927 := bstep (se 1 (by rfl) ⟨931445, by rfl⟩ : syracuseStep 1241927 = 1862891) B1862891
theorem B2093921 : Blo 826349 2093921 := bstep (se 2 (by rfl) ⟨785220, by rfl⟩ : syracuseStep 2093921 = 1570441) B1570441
theorem B36238241 : Blo 826349 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B6288353 : Blo 826349 6288353 := bstep (se 2 (by rfl) ⟨2358132, by rfl⟩ : syracuseStep 6288353 = 4716265) B4716265
theorem B1864673 : Blo 826349 1864673 := bstep (se 2 (by rfl) ⟨699252, by rfl⟩ : syracuseStep 1864673 = 1398505) B1398505
theorem B2356265 : Blo 826349 2356265 := bstep (se 2 (by rfl) ⟨883599, by rfl⟩ : syracuseStep 2356265 = 1767199) B1767199
theorem B1242479 : Blo 826349 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B3143069 : Blo 826349 3143069 := bstep (se 3 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 3143069 = 1178651) B1178651
theorem B8484263 : Blo 826349 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B1242599 : Blo 826349 1242599 := bstep (se 1 (by rfl) ⟨931949, by rfl⟩ : syracuseStep 1242599 = 1863899) B1863899
theorem B1242671 : Blo 826349 1242671 := bstep (se 1 (by rfl) ⟨932003, by rfl⟩ : syracuseStep 1242671 = 1864007) B1864007
theorem B1242779 : Blo 826349 1242779 := bstep (se 1 (by rfl) ⟨932084, by rfl⟩ : syracuseStep 1242779 = 1864169) B1864169
theorem B6289325 : Blo 826349 6289325 := bstep (se 3 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 6289325 = 2358497) B2358497
theorem B2979773 : Blo 826349 2979773 := bstep (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) B1117415
theorem B13465601 : Blo 826349 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B1243199 : Blo 826349 1243199 := bstep (se 1 (by rfl) ⟨932399, by rfl⟩ : syracuseStep 1243199 = 1864799) B1864799
theorem B1570927 : Blo 826349 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B4192559 : Blo 826349 4192559 := bstep (se 1 (by rfl) ⟨3144419, by rfl⟩ : syracuseStep 4192559 = 6288839) B6288839
theorem B1571375 : Blo 826349 1571375 := bstep (se 1 (by rfl) ⟨1178531, by rfl⟩ : syracuseStep 1571375 = 2357063) B2357063
theorem B3144329 : Blo 826349 3144329 := bstep (se 2 (by rfl) ⟨1179123, by rfl⟩ : syracuseStep 3144329 = 2358247) B2358247
theorem B3144359 : Blo 826349 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B4717223 : Blo 826349 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B1047487 : Blo 826349 1047487 := bstep (se 1 (by rfl) ⟨785615, by rfl⟩ : syracuseStep 1047487 = 1571231) B1571231
theorem B1866779 : Blo 826349 1866779 := bstep (se 1 (by rfl) ⟨1400084, by rfl⟩ : syracuseStep 1866779 = 2800169) B2800169
theorem B13434457 : Blo 826349 13434457 := bstep (se 2 (by rfl) ⟨5037921, by rfl⟩ : syracuseStep 13434457 = 10075843) B10075843
theorem B1244831 : Blo 826349 1244831 := bstep (se 1 (by rfl) ⟨933623, by rfl⟩ : syracuseStep 1244831 = 1867247) B1867247
theorem B13074281 : Blo 826349 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B1867751 : Blo 826349 1867751 := bstep (se 1 (by rfl) ⟨1400813, by rfl⟩ : syracuseStep 1867751 = 2801627) B2801627
theorem B1245353 : Blo 826349 1245353 := bstep (se 2 (by rfl) ⟨467007, by rfl⟩ : syracuseStep 1245353 = 934015) B934015
theorem B1245359 : Blo 826349 1245359 := bstep (se 1 (by rfl) ⟨934019, by rfl⟩ : syracuseStep 1245359 = 1868039) B1868039
theorem B2359763 : Blo 826349 2359763 := bstep (se 1 (by rfl) ⟨1769822, by rfl⟩ : syracuseStep 2359763 = 3539645) B3539645
theorem B4653677 : Blo 826349 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B10191815 : Blo 826349 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B1574473 : Blo 826349 1574473 := bstep (se 2 (by rfl) ⟨590427, by rfl⟩ : syracuseStep 1574473 = 1180855) B1180855
theorem B4195961 : Blo 826349 4195961 := bstep (se 2 (by rfl) ⟨1573485, by rfl⟩ : syracuseStep 4195961 = 3146971) B3146971
theorem B2983763 : Blo 826349 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B4197095 : Blo 826349 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B2100107 : Blo 826349 2100107 := bstep (se 1 (by rfl) ⟨1575080, by rfl⟩ : syracuseStep 2100107 = 3150161) B3150161
theorem B1576007 : Blo 826349 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B17010137 : Blo 826349 17010137 := bstep (se 2 (by rfl) ⟨6378801, by rfl⟩ : syracuseStep 17010137 = 12757603) B12757603
theorem B2100755 : Blo 826349 2100755 := bstep (se 1 (by rfl) ⟨1575566, by rfl⟩ : syracuseStep 2100755 = 3151133) B3151133
theorem B4722623 : Blo 826349 4722623 := bstep (se 1 (by rfl) ⟨3541967, by rfl⟩ : syracuseStep 4722623 = 7083935) B7083935
theorem B4198391 : Blo 826349 4198391 := bstep (se 1 (by rfl) ⟨3148793, by rfl⟩ : syracuseStep 4198391 = 6297587) B6297587
theorem B2789423 : Blo 826349 2789423 := bstep (se 1 (by rfl) ⟨2092067, by rfl⟩ : syracuseStep 2789423 = 4184135) B4184135
theorem B4788371 : Blo 826349 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B7573787 : Blo 826349 7573787 := bstep (se 1 (by rfl) ⟨5680340, by rfl⟩ : syracuseStep 7573787 = 11360681) B11360681
theorem B3543419 : Blo 826349 3543419 := bstep (se 1 (by rfl) ⟨2657564, by rfl⟩ : syracuseStep 3543419 = 5315129) B5315129
theorem B7180811 : Blo 826349 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B2364079 : Blo 826349 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B4199687 : Blo 826349 4199687 := bstep (se 1 (by rfl) ⟨3149765, by rfl⟩ : syracuseStep 4199687 = 6299531) B6299531
theorem B7542071 : Blo 826349 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B2790719 : Blo 826349 2790719 := bstep (se 1 (by rfl) ⟨2093039, by rfl⟩ : syracuseStep 2790719 = 4186079) B4186079
theorem B2791151 : Blo 826349 2791151 := bstep (se 1 (by rfl) ⟨2093363, by rfl⟩ : syracuseStep 2791151 = 4186727) B4186727
theorem B4201469 : Blo 826349 4201469 := bstep (se 3 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 4201469 = 1575551) B1575551
theorem B4725971 : Blo 826349 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B2235617 : Blo 826349 2235617 := bstep (se 2 (by rfl) ⟨838356, by rfl⟩ : syracuseStep 2235617 = 1676713) B1676713
theorem B16981325 : Blo 826349 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B5316029 : Blo 826349 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B827199 : Blo 826349 827199 := bstep (se 1 (by rfl) ⟨620399, by rfl⟩ : syracuseStep 827199 = 1240799) B1240799
theorem B2989963 : Blo 826349 2989963 := bstep (se 1 (by rfl) ⟨2242472, by rfl⟩ : syracuseStep 2989963 = 4484945) B4484945
theorem B827519 : Blo 826349 827519 := bstep (se 1 (by rfl) ⟨620639, by rfl⟩ : syracuseStep 827519 = 1241279) B1241279
theorem B2990279 : Blo 826349 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B9412847 : Blo 826349 9412847 := bstep (se 1 (by rfl) ⟨7059635, by rfl⟩ : syracuseStep 9412847 = 14119271) B14119271
theorem B827751 : Blo 826349 827751 := bstep (se 1 (by rfl) ⟨620813, by rfl⟩ : syracuseStep 827751 = 1241627) B1241627
theorem B827871 : Blo 826349 827871 := bstep (se 1 (by rfl) ⟨620903, by rfl⟩ : syracuseStep 827871 = 1241807) B1241807
theorem B827951 : Blo 826349 827951 := bstep (se 1 (by rfl) ⟨620963, by rfl⟩ : syracuseStep 827951 = 1241927) B1241927
theorem B24158827 : Blo 826349 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B828319 : Blo 826349 828319 := bstep (se 1 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 828319 = 1242479) B1242479
theorem B12133313 : Blo 826349 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B828399 : Blo 826349 828399 := bstep (se 1 (by rfl) ⟨621299, by rfl⟩ : syracuseStep 828399 = 1242599) B1242599
theorem B828447 : Blo 826349 828447 := bstep (se 1 (by rfl) ⟨621335, by rfl⟩ : syracuseStep 828447 = 1242671) B1242671
theorem B4203575 : Blo 826349 4203575 := bstep (se 1 (by rfl) ⟨3152681, by rfl⟩ : syracuseStep 4203575 = 6305363) B6305363
theorem B828519 : Blo 826349 828519 := bstep (se 1 (by rfl) ⟨621389, by rfl⟩ : syracuseStep 828519 = 1242779) B1242779
theorem B33957215 : Blo 826349 33957215 := bstep (se 1 (by rfl) ⟨25467911, by rfl⟩ : syracuseStep 33957215 = 50935823) B50935823
theorem B828799 : Blo 826349 828799 := bstep (se 1 (by rfl) ⟨621599, by rfl⟩ : syracuseStep 828799 = 1243199) B1243199
theorem B2795039 : Blo 826349 2795039 := bstep (se 1 (by rfl) ⟨2096279, by rfl⟩ : syracuseStep 2795039 = 4192559) B4192559
theorem B2238299 : Blo 826349 2238299 := bstep (se 1 (by rfl) ⟨1678724, by rfl⟩ : syracuseStep 2238299 = 3357449) B3357449
theorem B829887 : Blo 826349 829887 := bstep (se 1 (by rfl) ⟨622415, by rfl⟩ : syracuseStep 829887 = 1244831) B1244831
theorem B232697939 : Blo 826349 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B930271 : Blo 826349 930271 := bstep (se 1 (by rfl) ⟨697703, by rfl⟩ : syracuseStep 930271 = 1395407) B1395407
theorem B930523 : Blo 826349 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B7549661 : Blo 826349 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B35894411 : Blo 826349 35894411 := bstep (se 1 (by rfl) ⟨26920808, by rfl⟩ : syracuseStep 35894411 = 53841617) B53841617
theorem B7092305 : Blo 826349 7092305 := bstep (se 2 (by rfl) ⟨2659614, by rfl⟩ : syracuseStep 7092305 = 5319229) B5319229
theorem B3062951 : Blo 826349 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B4476320981 : Blo 826349 4476320981 := bstep (se 7 (by rfl) ⟨52456886, by rfl⟩ : syracuseStep 4476320981 = 104913773) B104913773
theorem B933871 : Blo 826349 933871 := bstep (se 1 (by rfl) ⟨700403, by rfl⟩ : syracuseStep 933871 = 1400807) B1400807
theorem B2801735 : Blo 826349 2801735 := bstep (se 1 (by rfl) ⟨2101301, by rfl⟩ : syracuseStep 2801735 = 4202603) B4202603
theorem B30228713 : Blo 826349 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B2835967 : Blo 826349 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B489670667 : Blo 826349 489670667 := bstep (se 1 (by rfl) ⟨367253000, by rfl⟩ : syracuseStep 489670667 = 734506001) B734506001
theorem B6278147 : Blo 826349 6278147 := bstep (se 1 (by rfl) ⟨4708610, by rfl⟩ : syracuseStep 6278147 = 9417221) B9417221
theorem B1395947 : Blo 826349 1395947 := bstep (se 1 (by rfl) ⟨1046960, by rfl⟩ : syracuseStep 1395947 = 2093921) B2093921
theorem B2018771 : Blo 826349 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B5656175 : Blo 826349 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B1396649 : Blo 826349 1396649 := bstep (se 2 (by rfl) ⟨523743, by rfl⟩ : syracuseStep 1396649 = 1047487) B1047487
theorem B1986515 : Blo 826349 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B4706585 : Blo 826349 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B17912609 : Blo 826349 17912609 := bstep (se 2 (by rfl) ⟨6717228, by rfl⟩ : syracuseStep 17912609 = 13434457) B13434457
theorem B4183811 : Blo 826349 4183811 := bstep (se 1 (by rfl) ⟨3137858, by rfl⟩ : syracuseStep 4183811 = 6275717) B6275717
theorem B1890535 : Blo 826349 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B3987791 : Blo 826349 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B275929811 : Blo 826349 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B8969069 : Blo 826349 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B1399673 : Blo 826349 1399673 := bstep (se 2 (by rfl) ⟨524877, by rfl⟩ : syracuseStep 1399673 = 1049755) B1049755
theorem B4709249 : Blo 826349 4709249 := bstep (se 2 (by rfl) ⟨1765968, by rfl⟩ : syracuseStep 4709249 = 3531937) B3531937
theorem B7069751 : Blo 826349 7069751 := bstep (se 1 (by rfl) ⟨5302313, by rfl⟩ : syracuseStep 7069751 = 10604627) B10604627
theorem B1990751 : Blo 826349 1990751 := bstep (se 1 (by rfl) ⟨1493063, by rfl⟩ : syracuseStep 1990751 = 2986127) B2986127
theorem B1859687 : Blo 826349 1859687 := bstep (se 1 (by rfl) ⟨1394765, by rfl⟩ : syracuseStep 1859687 = 2789531) B2789531
theorem B1859705 : Blo 826349 1859705 := bstep (se 2 (by rfl) ⟨697389, by rfl⟩ : syracuseStep 1859705 = 1394779) B1394779
theorem B11919595 : Blo 826349 11919595 := bstep (se 1 (by rfl) ⟨8939696, by rfl⟩ : syracuseStep 11919595 = 17879393) B17879393
theorem B5661289 : Blo 826349 5661289 := bstep (se 2 (by rfl) ⟨2122983, by rfl⟩ : syracuseStep 5661289 = 4245967) B4245967
theorem B1860551 : Blo 826349 1860551 := bstep (se 1 (by rfl) ⟨1395413, by rfl⟩ : syracuseStep 1860551 = 2790827) B2790827
theorem B4711891 : Blo 826349 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B7563091 : Blo 826349 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B3532673 : Blo 826349 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B1861703 : Blo 826349 1861703 := bstep (se 1 (by rfl) ⟨1396277, by rfl⟩ : syracuseStep 1861703 = 2792555) B2792555
theorem B4483259 : Blo 826349 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B24176837 : Blo 826349 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B2353531 : Blo 826349 2353531 := bstep (se 1 (by rfl) ⟨1765148, by rfl⟩ : syracuseStep 2353531 = 3530297) B3530297
theorem B1862351 : Blo 826349 1862351 := bstep (se 1 (by rfl) ⟨1396763, by rfl⟩ : syracuseStep 1862351 = 2793527) B2793527
theorem B2550599 : Blo 826349 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B1862567 : Blo 826349 1862567 := bstep (se 1 (by rfl) ⟨1396925, by rfl⟩ : syracuseStep 1862567 = 2793851) B2793851
theorem B1862639 : Blo 826349 1862639 := bstep (se 1 (by rfl) ⟨1396979, by rfl⟩ : syracuseStep 1862639 = 2793959) B2793959
theorem B1863071 : Blo 826349 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B2092463 : Blo 826349 2092463 := bstep (se 1 (by rfl) ⟨1569347, by rfl⟩ : syracuseStep 2092463 = 3138695) B3138695
theorem B1240559 : Blo 826349 1240559 := bstep (se 1 (by rfl) ⟨930419, by rfl⟩ : syracuseStep 1240559 = 1860839) B1860839
theorem B1863521 : Blo 826349 1863521 := bstep (se 2 (by rfl) ⟨698820, by rfl⟩ : syracuseStep 1863521 = 1397641) B1397641
theorem B1863935 : Blo 826349 1863935 := bstep (se 1 (by rfl) ⟨1397951, by rfl⟩ : syracuseStep 1863935 = 2795903) B2795903
theorem B1242281 : Blo 826349 1242281 := bstep (se 2 (by rfl) ⟨465855, by rfl⟩ : syracuseStep 1242281 = 931711) B931711
theorem B13464797 : Blo 826349 13464797 := bstep (se 3 (by rfl) ⟨2524649, by rfl⟩ : syracuseStep 13464797 = 5049299) B5049299
theorem B1570175 : Blo 826349 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B2094569 : Blo 826349 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B1865555 : Blo 826349 1865555 := bstep (se 1 (by rfl) ⟨1399166, by rfl⟩ : syracuseStep 1865555 = 2798333) B2798333
theorem B1242983 : Blo 826349 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B1865627 : Blo 826349 1865627 := bstep (se 1 (by rfl) ⟨1399220, by rfl⟩ : syracuseStep 1865627 = 2798441) B2798441
theorem B1865663 : Blo 826349 1865663 := bstep (se 1 (by rfl) ⟨1399247, by rfl⟩ : syracuseStep 1865663 = 2798495) B2798495
theorem B4192235 : Blo 826349 4192235 := bstep (se 1 (by rfl) ⟨3144176, by rfl⟩ : syracuseStep 4192235 = 6288353) B6288353
theorem B1243115 : Blo 826349 1243115 := bstep (se 1 (by rfl) ⟨932336, by rfl⟩ : syracuseStep 1243115 = 1864673) B1864673
theorem B1570843 : Blo 826349 1570843 := bstep (se 1 (by rfl) ⟨1178132, by rfl⟩ : syracuseStep 1570843 = 2356265) B2356265
theorem B1865897 : Blo 826349 1865897 := bstep (se 2 (by rfl) ⟨699711, by rfl⟩ : syracuseStep 1865897 = 1399423) B1399423
theorem B2095379 : Blo 826349 2095379 := bstep (se 1 (by rfl) ⟨1571534, by rfl⟩ : syracuseStep 2095379 = 3143069) B3143069
theorem B1243529 : Blo 826349 1243529 := bstep (se 2 (by rfl) ⟨466323, by rfl⟩ : syracuseStep 1243529 = 932647) B932647
theorem B4192883 : Blo 826349 4192883 := bstep (se 1 (by rfl) ⟨3144662, by rfl⟩ : syracuseStep 4192883 = 6289325) B6289325
theorem B1866401 : Blo 826349 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B8977067 : Blo 826349 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B1866599 : Blo 826349 1866599 := bstep (se 1 (by rfl) ⟨1399949, by rfl⟩ : syracuseStep 1866599 = 2799899) B2799899
theorem B1047583 : Blo 826349 1047583 := bstep (se 1 (by rfl) ⟨785687, by rfl⟩ : syracuseStep 1047583 = 1571375) B1571375
theorem B2096219 : Blo 826349 2096219 := bstep (se 1 (by rfl) ⟨1572164, by rfl⟩ : syracuseStep 2096219 = 3144329) B3144329
theorem B30211177 : Blo 826349 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B2096239 : Blo 826349 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B3144815 : Blo 826349 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B1866959 : Blo 826349 1866959 := bstep (se 1 (by rfl) ⟨1400219, by rfl⟩ : syracuseStep 1866959 = 2800439) B2800439
theorem B1244519 : Blo 826349 1244519 := bstep (se 1 (by rfl) ⟨933389, by rfl⟩ : syracuseStep 1244519 = 1866779) B1866779
theorem B8716187 : Blo 826349 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B1867679 : Blo 826349 1867679 := bstep (se 1 (by rfl) ⟨1400759, by rfl⟩ : syracuseStep 1867679 = 2801519) B2801519
theorem B1245167 : Blo 826349 1245167 := bstep (se 1 (by rfl) ⟨933875, by rfl⟩ : syracuseStep 1245167 = 1867751) B1867751
theorem B1867769 : Blo 826349 1867769 := bstep (se 2 (by rfl) ⟨700413, by rfl⟩ : syracuseStep 1867769 = 1400827) B1400827
theorem B1867823 : Blo 826349 1867823 := bstep (se 1 (by rfl) ⟨1400867, by rfl⟩ : syracuseStep 1867823 = 2801735) B2801735
theorem B20152475 : Blo 826349 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B620527837 : Blo 826349 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B5308669 : Blo 826349 5308669 := bstep (se 3 (by rfl) ⟨995375, by rfl⟩ : syracuseStep 5308669 = 1990751) B1990751
theorem B1573175 : Blo 826349 1573175 := bstep (se 1 (by rfl) ⟨1179881, by rfl⟩ : syracuseStep 1573175 = 2359763) B2359763
theorem B15892793 : Blo 826349 15892793 := bstep (se 2 (by rfl) ⟨5959797, by rfl⟩ : syracuseStep 15892793 = 11919595) B11919595
theorem B32211769 : Blo 826349 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B1050671 : Blo 826349 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B2099297 : Blo 826349 2099297 := bstep (se 2 (by rfl) ⟨787236, by rfl⟩ : syracuseStep 2099297 = 1574473) B1574473
theorem B1345847 : Blo 826349 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B11340091 : Blo 826349 11340091 := bstep (se 1 (by rfl) ⟨8505068, by rfl⟩ : syracuseStep 11340091 = 17010137) B17010137
theorem B3770783 : Blo 826349 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B3148415 : Blo 826349 3148415 := bstep (se 1 (by rfl) ⟨2361311, by rfl⟩ : syracuseStep 3148415 = 4722623) B4722623
theorem B5049191 : Blo 826349 5049191 := bstep (se 1 (by rfl) ⟨3786893, by rfl⟩ : syracuseStep 5049191 = 7573787) B7573787
theorem B2362279 : Blo 826349 2362279 := bstep (se 1 (by rfl) ⟨1771709, by rfl⟩ : syracuseStep 2362279 = 3543419) B3543419
theorem B4787207 : Blo 826349 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B2789207 : Blo 826349 2789207 := bstep (se 1 (by rfl) ⟨2091905, by rfl⟩ : syracuseStep 2789207 = 4183811) B4183811
theorem B2658527 : Blo 826349 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B3150647 : Blo 826349 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B3544019 : Blo 826349 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B3152105 : Blo 826349 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B2988839 : Blo 826349 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B827039 : Blo 826349 827039 := bstep (se 1 (by rfl) ⟨620279, by rfl⟩ : syracuseStep 827039 = 1240559) B1240559
theorem B23929607 : Blo 826349 23929607 := bstep (se 1 (by rfl) ⟨17947205, by rfl⟩ : syracuseStep 23929607 = 35894411) B35894411
theorem B828187 : Blo 826349 828187 := bstep (se 1 (by rfl) ⟨621140, by rfl⟩ : syracuseStep 828187 = 1242281) B1242281
theorem B828655 : Blo 826349 828655 := bstep (se 1 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 828655 = 1242983) B1242983
theorem B2794823 : Blo 826349 2794823 := bstep (se 1 (by rfl) ⟨2096117, by rfl⟩ : syracuseStep 2794823 = 4192235) B4192235
theorem B828743 : Blo 826349 828743 := bstep (se 1 (by rfl) ⟨621557, by rfl⟩ : syracuseStep 828743 = 1243115) B1243115
theorem B4728203 : Blo 826349 4728203 := bstep (se 1 (by rfl) ⟨3546152, by rfl⟩ : syracuseStep 4728203 = 7092305) B7092305
theorem B40281569 : Blo 826349 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B2794985 : Blo 826349 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B829019 : Blo 826349 829019 := bstep (se 1 (by rfl) ⟨621764, by rfl⟩ : syracuseStep 829019 = 1243529) B1243529
theorem B2795255 : Blo 826349 2795255 := bstep (se 1 (by rfl) ⟨2096441, by rfl⟩ : syracuseStep 2795255 = 4192883) B4192883
theorem B2041967 : Blo 826349 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B829679 : Blo 826349 829679 := bstep (se 1 (by rfl) ⟨622259, by rfl⟩ : syracuseStep 829679 = 1244519) B1244519
theorem B5810791 : Blo 826349 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B830111 : Blo 826349 830111 := bstep (se 1 (by rfl) ⟨622583, by rfl⟩ : syracuseStep 830111 = 1245167) B1245167
theorem B830235 : Blo 826349 830235 := bstep (se 1 (by rfl) ⟨622676, by rfl⟩ : syracuseStep 830235 = 1245353) B1245353
theorem B830239 : Blo 826349 830239 := bstep (se 1 (by rfl) ⟨622679, by rfl⟩ : syracuseStep 830239 = 1245359) B1245359
theorem B6794543 : Blo 826349 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B7548385 : Blo 826349 7548385 := bstep (se 2 (by rfl) ⟨2830644, by rfl⟩ : syracuseStep 7548385 = 5661289) B5661289
theorem B2797307 : Blo 826349 2797307 := bstep (se 1 (by rfl) ⟨2097980, by rfl⟩ : syracuseStep 2797307 = 4195961) B4195961
theorem B326447111 : Blo 826349 326447111 := bstep (se 1 (by rfl) ⟨244835333, by rfl⟩ : syracuseStep 326447111 = 489670667) B489670667
theorem B2798063 : Blo 826349 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B3781289 : Blo 826349 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B930631 : Blo 826349 930631 := bstep (se 1 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 930631 = 1395947) B1395947
theorem B931099 : Blo 826349 931099 := bstep (se 1 (by rfl) ⟨698324, by rfl⟩ : syracuseStep 931099 = 1396649) B1396649
theorem B1324343 : Blo 826349 1324343 := bstep (se 1 (by rfl) ⟨993257, by rfl⟩ : syracuseStep 1324343 = 1986515) B1986515
theorem B2798927 : Blo 826349 2798927 := bstep (se 1 (by rfl) ⟨2099195, by rfl⟩ : syracuseStep 2798927 = 4198391) B4198391
theorem B3192247 : Blo 826349 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B11941739 : Blo 826349 11941739 := bstep (se 1 (by rfl) ⟨8956304, by rfl⟩ : syracuseStep 11941739 = 17912609) B17912609
theorem B2799791 : Blo 826349 2799791 := bstep (se 1 (by rfl) ⟨2099843, by rfl⟩ : syracuseStep 2799791 = 4199687) B4199687
theorem B5028047 : Blo 826349 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B5979379 : Blo 826349 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B933115 : Blo 826349 933115 := bstep (se 1 (by rfl) ⟨699836, by rfl⟩ : syracuseStep 933115 = 1399673) B1399673
theorem B2800979 : Blo 826349 2800979 := bstep (se 1 (by rfl) ⟨2100734, by rfl⟩ : syracuseStep 2800979 = 4201469) B4201469
theorem B1490411 : Blo 826349 1490411 := bstep (se 1 (by rfl) ⟨1117808, by rfl⟩ : syracuseStep 1490411 = 2235617) B2235617
theorem B11320883 : Blo 826349 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B6275231 : Blo 826349 6275231 := bstep (se 1 (by rfl) ⟨4706423, by rfl⟩ : syracuseStep 6275231 = 9412847) B9412847
theorem B64471565 : Blo 826349 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B2802383 : Blo 826349 2802383 := bstep (se 1 (by rfl) ⟨2101787, by rfl⟩ : syracuseStep 2802383 = 4203575) B4203575
theorem B1492199 : Blo 826349 1492199 := bstep (se 1 (by rfl) ⟨1119149, by rfl⟩ : syracuseStep 1492199 = 2238299) B2238299
theorem B1394975 : Blo 826349 1394975 := bstep (se 1 (by rfl) ⟨1046231, by rfl⟩ : syracuseStep 1394975 = 2092463) B2092463
theorem B5033107 : Blo 826349 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B1396379 : Blo 826349 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1396777 : Blo 826349 1396777 := bstep (se 2 (by rfl) ⟨523791, by rfl⟩ : syracuseStep 1396777 = 1047583) B1047583
theorem B1396919 : Blo 826349 1396919 := bstep (se 1 (by rfl) ⟨1047689, by rfl⟩ : syracuseStep 1396919 = 2095379) B2095379
theorem B5984711 : Blo 826349 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B1397479 : Blo 826349 1397479 := bstep (se 1 (by rfl) ⟨1048109, by rfl⟩ : syracuseStep 1397479 = 2096219) B2096219
theorem B3986617 : Blo 826349 3986617 := bstep (se 2 (by rfl) ⟨1494981, by rfl⟩ : syracuseStep 3986617 = 2989963) B2989963
theorem B12409805 : Blo 826349 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B1400071 : Blo 826349 1400071 := bstep (se 1 (by rfl) ⟨1050053, by rfl⟩ : syracuseStep 1400071 = 2100107) B2100107
theorem B6282521 : Blo 826349 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B4185431 : Blo 826349 4185431 := bstep (se 1 (by rfl) ⟨3139073, by rfl⟩ : syracuseStep 4185431 = 6278147) B6278147
theorem B1400503 : Blo 826349 1400503 := bstep (se 1 (by rfl) ⟨1050377, by rfl⟩ : syracuseStep 1400503 = 2100755) B2100755
theorem B10084121 : Blo 826349 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B1859615 : Blo 826349 1859615 := bstep (se 1 (by rfl) ⟨1394711, by rfl⟩ : syracuseStep 1859615 = 2789423) B2789423
theorem B3137723 : Blo 826349 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B3138041 : Blo 826349 3138041 := bstep (se 2 (by rfl) ⟨1176765, by rfl⟩ : syracuseStep 3138041 = 2353531) B2353531
theorem B35906125 : Blo 826349 35906125 := bstep (se 3 (by rfl) ⟨6732398, by rfl⟩ : syracuseStep 35906125 = 13464797) B13464797
theorem B1860479 : Blo 826349 1860479 := bstep (se 1 (by rfl) ⟨1395359, by rfl⟩ : syracuseStep 1860479 = 2790719) B2790719
theorem B1860767 : Blo 826349 1860767 := bstep (se 1 (by rfl) ⟨1395575, by rfl⟩ : syracuseStep 1860767 = 2791151) B2791151
theorem B183953207 : Blo 826349 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B3139499 : Blo 826349 3139499 := bstep (se 1 (by rfl) ⟨2354624, by rfl⟩ : syracuseStep 3139499 = 4709249) B4709249
theorem B7956701 : Blo 826349 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B4713167 : Blo 826349 4713167 := bstep (se 1 (by rfl) ⟨3534875, by rfl⟩ : syracuseStep 4713167 = 7069751) B7069751
theorem B1239791 : Blo 826349 1239791 := bstep (se 1 (by rfl) ⟨929843, by rfl⟩ : syracuseStep 1239791 = 1859687) B1859687
theorem B1239803 : Blo 826349 1239803 := bstep (se 1 (by rfl) ⟨929852, by rfl⟩ : syracuseStep 1239803 = 1859705) B1859705
theorem B1993519 : Blo 826349 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B1240361 : Blo 826349 1240361 := bstep (se 2 (by rfl) ⟨465135, by rfl⟩ : syracuseStep 1240361 = 930271) B930271
theorem B8088875 : Blo 826349 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B1240367 : Blo 826349 1240367 := bstep (se 1 (by rfl) ⟨930275, by rfl⟩ : syracuseStep 1240367 = 1860551) B1860551
theorem B22638143 : Blo 826349 22638143 := bstep (se 1 (by rfl) ⟨16978607, by rfl⟩ : syracuseStep 22638143 = 33957215) B33957215
theorem B1240697 : Blo 826349 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B1863359 : Blo 826349 1863359 := bstep (se 1 (by rfl) ⟨1397519, by rfl⟩ : syracuseStep 1863359 = 2795039) B2795039
theorem B2355115 : Blo 826349 2355115 := bstep (se 1 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 2355115 = 3532673) B3532673
theorem B1241135 : Blo 826349 1241135 := bstep (se 1 (by rfl) ⟨930851, by rfl⟩ : syracuseStep 1241135 = 1861703) B1861703
theorem B1241567 : Blo 826349 1241567 := bstep (se 1 (by rfl) ⟨931175, by rfl⟩ : syracuseStep 1241567 = 1862351) B1862351
theorem B1700399 : Blo 826349 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B1241711 : Blo 826349 1241711 := bstep (se 1 (by rfl) ⟨931283, by rfl⟩ : syracuseStep 1241711 = 1862567) B1862567
theorem B1241759 : Blo 826349 1241759 := bstep (se 1 (by rfl) ⟨931319, by rfl⟩ : syracuseStep 1241759 = 1862639) B1862639
theorem B1242047 : Blo 826349 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B1242347 : Blo 826349 1242347 := bstep (se 1 (by rfl) ⟨931760, by rfl⟩ : syracuseStep 1242347 = 1863521) B1863521
theorem B2094457 : Blo 826349 2094457 := bstep (se 2 (by rfl) ⟨785421, by rfl⟩ : syracuseStep 2094457 = 1570843) B1570843
theorem B1242623 : Blo 826349 1242623 := bstep (se 1 (by rfl) ⟨931967, by rfl⟩ : syracuseStep 1242623 = 1863935) B1863935
theorem B2520713 : Blo 826349 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B1046783 : Blo 826349 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B1243703 : Blo 826349 1243703 := bstep (se 1 (by rfl) ⟨932777, by rfl⟩ : syracuseStep 1243703 = 1865555) B1865555
theorem B1243751 : Blo 826349 1243751 := bstep (se 1 (by rfl) ⟨932813, by rfl⟩ : syracuseStep 1243751 = 1865627) B1865627
theorem B1243775 : Blo 826349 1243775 := bstep (se 1 (by rfl) ⟨932831, by rfl⟩ : syracuseStep 1243775 = 1865663) B1865663
theorem B1243931 : Blo 826349 1243931 := bstep (se 1 (by rfl) ⟨932948, by rfl⟩ : syracuseStep 1243931 = 1865897) B1865897
theorem B1244267 : Blo 826349 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B1244399 : Blo 826349 1244399 := bstep (se 1 (by rfl) ⟨933299, by rfl⟩ : syracuseStep 1244399 = 1866599) B1866599
theorem B2096543 : Blo 826349 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B1244639 : Blo 826349 1244639 := bstep (se 1 (by rfl) ⟨933479, by rfl⟩ : syracuseStep 1244639 = 1866959) B1866959
theorem B2984213987 : Blo 826349 2984213987 := bstep (se 1 (by rfl) ⟨2238160490, by rfl⟩ : syracuseStep 2984213987 = 4476320981) B4476320981
theorem B1245119 : Blo 826349 1245119 := bstep (se 1 (by rfl) ⟨933839, by rfl⟩ : syracuseStep 1245119 = 1867679) B1867679
theorem B1245161 : Blo 826349 1245161 := bstep (se 2 (by rfl) ⟨466935, by rfl⟩ : syracuseStep 1245161 = 933871) B933871
theorem B1245179 : Blo 826349 1245179 := bstep (se 1 (by rfl) ⟨933884, by rfl⟩ : syracuseStep 1245179 = 1867769) B1867769
theorem B1245215 : Blo 826349 1245215 := bstep (se 1 (by rfl) ⟨933911, by rfl⟩ : syracuseStep 1245215 = 1867823) B1867823
theorem B13434983 : Blo 826349 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B1048783 : Blo 826349 1048783 := bstep (se 1 (by rfl) ⟨786587, by rfl⟩ : syracuseStep 1048783 = 1573175) B1573175
theorem B7078225 : Blo 826349 7078225 := bstep (se 2 (by rfl) ⟨2654334, by rfl⟩ : syracuseStep 7078225 = 5308669) B5308669
theorem B1868255 : Blo 826349 1868255 := bstep (se 1 (by rfl) ⟨1401191, by rfl⟩ : syracuseStep 1868255 = 2802383) B2802383
theorem B47874833 : Blo 826349 47874833 := bstep (se 2 (by rfl) ⟨17953062, by rfl⟩ : syracuseStep 47874833 = 35906125) B35906125
theorem B2098943 : Blo 826349 2098943 := bstep (se 1 (by rfl) ⟨1574207, by rfl⟩ : syracuseStep 2098943 = 3148415) B3148415
theorem B1772351 : Blo 826349 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B2100431 : Blo 826349 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B14355701 : Blo 826349 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B2362679 : Blo 826349 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B2658025 : Blo 826349 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B3149705 : Blo 826349 3149705 := bstep (se 2 (by rfl) ⟨1181139, by rfl⟩ : syracuseStep 3149705 = 2362279) B2362279
theorem B2101403 : Blo 826349 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B10064513 : Blo 826349 10064513 := bstep (se 2 (by rfl) ⟨3774192, by rfl⟩ : syracuseStep 10064513 = 7548385) B7548385
theorem B2790287 : Blo 826349 2790287 := bstep (se 1 (by rfl) ⟨2092715, by rfl⟩ : syracuseStep 2790287 = 4185431) B4185431
theorem B6722747 : Blo 826349 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B5445245 : Blo 826349 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B2791421 : Blo 826349 2791421 := bstep (se 3 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 2791421 = 1046783) B1046783
theorem B26843237 : Blo 826349 26843237 := bstep (se 4 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 26843237 = 5033107) B5033107
theorem B3152135 : Blo 826349 3152135 := bstep (se 1 (by rfl) ⟨2364101, by rfl⟩ : syracuseStep 3152135 = 4728203) B4728203
theorem B5315489 : Blo 826349 5315489 := bstep (se 2 (by rfl) ⟨1993308, by rfl⟩ : syracuseStep 5315489 = 3986617) B3986617
theorem B826527 : Blo 826349 826527 := bstep (se 1 (by rfl) ⟨619895, by rfl⟩ : syracuseStep 826527 = 1239791) B1239791
theorem B2792609 : Blo 826349 2792609 := bstep (se 2 (by rfl) ⟨1047228, by rfl⟩ : syracuseStep 2792609 = 2094457) B2094457
theorem B826535 : Blo 826349 826535 := bstep (se 1 (by rfl) ⟨619901, by rfl⟩ : syracuseStep 826535 = 1239803) B1239803
theorem B826907 : Blo 826349 826907 := bstep (se 1 (by rfl) ⟨620180, by rfl⟩ : syracuseStep 826907 = 1240361) B1240361
theorem B4529695 : Blo 826349 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B826911 : Blo 826349 826911 := bstep (se 1 (by rfl) ⟨620183, by rfl⟩ : syracuseStep 826911 = 1240367) B1240367
theorem B827131 : Blo 826349 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B827423 : Blo 826349 827423 := bstep (se 1 (by rfl) ⟨620567, by rfl⟩ : syracuseStep 827423 = 1241135) B1241135
theorem B827711 : Blo 826349 827711 := bstep (se 1 (by rfl) ⟨620783, by rfl⟩ : syracuseStep 827711 = 1241567) B1241567
theorem B827807 : Blo 826349 827807 := bstep (se 1 (by rfl) ⟨620855, by rfl⟩ : syracuseStep 827807 = 1241711) B1241711
theorem B827839 : Blo 826349 827839 := bstep (se 1 (by rfl) ⟨620879, by rfl⟩ : syracuseStep 827839 = 1241759) B1241759
theorem B828031 : Blo 826349 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B828231 : Blo 826349 828231 := bstep (se 1 (by rfl) ⟨621173, by rfl⟩ : syracuseStep 828231 = 1242347) B1242347
theorem B828415 : Blo 826349 828415 := bstep (se 1 (by rfl) ⟨621311, by rfl⟩ : syracuseStep 828415 = 1242623) B1242623
theorem B1680475 : Blo 826349 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B3974429 : Blo 826349 3974429 := bstep (se 3 (by rfl) ⟨745205, by rfl⟩ : syracuseStep 3974429 = 1490411) B1490411
theorem B3352031 : Blo 826349 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B7972505 : Blo 826349 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B829135 : Blo 826349 829135 := bstep (se 1 (by rfl) ⟨621851, by rfl⟩ : syracuseStep 829135 = 1243703) B1243703
theorem B829167 : Blo 826349 829167 := bstep (se 1 (by rfl) ⟨621875, by rfl⟩ : syracuseStep 829167 = 1243751) B1243751
theorem B829183 : Blo 826349 829183 := bstep (se 1 (by rfl) ⟨621887, by rfl⟩ : syracuseStep 829183 = 1243775) B1243775
theorem B829287 : Blo 826349 829287 := bstep (se 1 (by rfl) ⟨621965, by rfl⟩ : syracuseStep 829287 = 1243931) B1243931
theorem B829511 : Blo 826349 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B829599 : Blo 826349 829599 := bstep (se 1 (by rfl) ⟨622199, by rfl⟩ : syracuseStep 829599 = 1244399) B1244399
theorem B829759 : Blo 826349 829759 := bstep (se 1 (by rfl) ⟨622319, by rfl⟩ : syracuseStep 829759 = 1244639) B1244639
theorem B7547255 : Blo 826349 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B830079 : Blo 826349 830079 := bstep (se 1 (by rfl) ⟨622559, by rfl⟩ : syracuseStep 830079 = 1245119) B1245119
theorem B830107 : Blo 826349 830107 := bstep (se 1 (by rfl) ⟨622580, by rfl⟩ : syracuseStep 830107 = 1245161) B1245161
theorem B830119 : Blo 826349 830119 := bstep (se 1 (by rfl) ⟨622589, by rfl⟩ : syracuseStep 830119 = 1245179) B1245179
theorem B10595195 : Blo 826349 10595195 := bstep (se 1 (by rfl) ⟨7946396, by rfl⟩ : syracuseStep 10595195 = 15892793) B15892793
theorem B827370449 : Blo 826349 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B994799 : Blo 826349 994799 := bstep (se 1 (by rfl) ⟨746099, by rfl⟩ : syracuseStep 994799 = 1492199) B1492199
theorem B929983 : Blo 826349 929983 := bstep (se 1 (by rfl) ⟨697487, by rfl⟩ : syracuseStep 929983 = 1394975) B1394975
theorem B3191471 : Blo 826349 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B930919 : Blo 826349 930919 := bstep (se 1 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 930919 = 1396379) B1396379
theorem B931279 : Blo 826349 931279 := bstep (se 1 (by rfl) ⟨698459, by rfl⟩ : syracuseStep 931279 = 1396919) B1396919
theorem B15120121 : Blo 826349 15120121 := bstep (se 2 (by rfl) ⟨5670045, by rfl⟩ : syracuseStep 15120121 = 11340091) B11340091
theorem B7747721 : Blo 826349 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B2801789 : Blo 826349 2801789 := bstep (se 3 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 2801789 = 1050671) B1050671
theorem B26854379 : Blo 826349 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B122635471 : Blo 826349 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B5392583 : Blo 826349 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B15092095 : Blo 826349 15092095 := bstep (se 1 (by rfl) ⟨11319071, by rfl⟩ : syracuseStep 15092095 = 22638143) B22638143
theorem B217631407 : Blo 826349 217631407 := bstep (se 1 (by rfl) ⟨163223555, by rfl⟩ : syracuseStep 217631407 = 326447111) B326447111
theorem B1133599 : Blo 826349 1133599 := bstep (se 1 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 1133599 = 1700399) B1700399
theorem B1397695 : Blo 826349 1397695 := bstep (se 1 (by rfl) ⟨1048271, by rfl⟩ : syracuseStep 1397695 = 2096543) B2096543
theorem B4183487 : Blo 826349 4183487 := bstep (se 1 (by rfl) ⟨3137615, by rfl⟩ : syracuseStep 4183487 = 6275231) B6275231
theorem B42981043 : Blo 826349 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B42949025 : Blo 826349 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B1399531 : Blo 826349 1399531 := bstep (se 1 (by rfl) ⟨1049648, by rfl⟩ : syracuseStep 1399531 = 2099297) B2099297
theorem B2513855 : Blo 826349 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B10083437 : Blo 826349 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B3366127 : Blo 826349 3366127 := bstep (se 1 (by rfl) ⟨2524595, by rfl⟩ : syracuseStep 3366127 = 5049191) B5049191
theorem B1859471 : Blo 826349 1859471 := bstep (se 1 (by rfl) ⟨1394603, by rfl⟩ : syracuseStep 1859471 = 2789207) B2789207
theorem B3989807 : Blo 826349 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B1992559 : Blo 826349 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B4188347 : Blo 826349 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B3140153 : Blo 826349 3140153 := bstep (se 2 (by rfl) ⟨1177557, by rfl⟩ : syracuseStep 3140153 = 2355115) B2355115
theorem B1239743 : Blo 826349 1239743 := bstep (se 1 (by rfl) ⟨929807, by rfl⟩ : syracuseStep 1239743 = 1859615) B1859615
theorem B1862369 : Blo 826349 1862369 := bstep (se 2 (by rfl) ⟨698388, by rfl⟩ : syracuseStep 1862369 = 1396777) B1396777
theorem B2091815 : Blo 826349 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B2092027 : Blo 826349 2092027 := bstep (se 1 (by rfl) ⟨1569020, by rfl⟩ : syracuseStep 2092027 = 3138041) B3138041
theorem B15953071 : Blo 826349 15953071 := bstep (se 1 (by rfl) ⟨11964803, by rfl⟩ : syracuseStep 15953071 = 23929607) B23929607
theorem B1240319 : Blo 826349 1240319 := bstep (se 1 (by rfl) ⟨930239, by rfl⟩ : syracuseStep 1240319 = 1860479) B1860479
theorem B1240511 : Blo 826349 1240511 := bstep (se 1 (by rfl) ⟨930383, by rfl⟩ : syracuseStep 1240511 = 1860767) B1860767
theorem B1863215 : Blo 826349 1863215 := bstep (se 1 (by rfl) ⟨1397411, by rfl⟩ : syracuseStep 1863215 = 2794823) B2794823
theorem B1863305 : Blo 826349 1863305 := bstep (se 2 (by rfl) ⟨698739, by rfl⟩ : syracuseStep 1863305 = 1397479) B1397479
theorem B1863323 : Blo 826349 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B1240841 : Blo 826349 1240841 := bstep (se 2 (by rfl) ⟨465315, by rfl⟩ : syracuseStep 1240841 = 930631) B930631
theorem B1863503 : Blo 826349 1863503 := bstep (se 1 (by rfl) ⟨1397627, by rfl⟩ : syracuseStep 1863503 = 2795255) B2795255
theorem B2092999 : Blo 826349 2092999 := bstep (se 1 (by rfl) ⟨1569749, by rfl⟩ : syracuseStep 2092999 = 3139499) B3139499
theorem B5304467 : Blo 826349 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B1241465 : Blo 826349 1241465 := bstep (se 2 (by rfl) ⟨465549, by rfl⟩ : syracuseStep 1241465 = 931099) B931099
theorem B3142111 : Blo 826349 3142111 := bstep (se 1 (by rfl) ⟨2356583, by rfl⟩ : syracuseStep 3142111 = 4713167) B4713167
theorem B4256329 : Blo 826349 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B1242239 : Blo 826349 1242239 := bstep (se 1 (by rfl) ⟨931679, by rfl⟩ : syracuseStep 1242239 = 1863359) B1863359
theorem B1864871 : Blo 826349 1864871 := bstep (se 1 (by rfl) ⟨1398653, by rfl⟩ : syracuseStep 1864871 = 2797307) B2797307
theorem B33092813 : Blo 826349 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B1865375 : Blo 826349 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B882895 : Blo 826349 882895 := bstep (se 1 (by rfl) ⟨662171, by rfl⟩ : syracuseStep 882895 = 1324343) B1324343
theorem B1865951 : Blo 826349 1865951 := bstep (se 1 (by rfl) ⟨1399463, by rfl⟩ : syracuseStep 1865951 = 2798927) B2798927
theorem B7961159 : Blo 826349 7961159 := bstep (se 1 (by rfl) ⟨5970869, by rfl⟩ : syracuseStep 7961159 = 11941739) B11941739
theorem B1866527 : Blo 826349 1866527 := bstep (se 1 (by rfl) ⟨1399895, by rfl⟩ : syracuseStep 1866527 = 2799791) B2799791
theorem B1244153 : Blo 826349 1244153 := bstep (se 2 (by rfl) ⟨466557, by rfl⟩ : syracuseStep 1244153 = 933115) B933115
theorem B1866761 : Blo 826349 1866761 := bstep (se 2 (by rfl) ⟨700035, by rfl⟩ : syracuseStep 1866761 = 1400071) B1400071
theorem B1867319 : Blo 826349 1867319 := bstep (se 1 (by rfl) ⟨1400489, by rfl⟩ : syracuseStep 1867319 = 2800979) B2800979
theorem B1867337 : Blo 826349 1867337 := bstep (se 2 (by rfl) ⟨700251, by rfl⟩ : syracuseStep 1867337 = 1400503) B1400503
theorem B1989475991 : Blo 826349 1989475991 := bstep (se 1 (by rfl) ⟨1492106993, by rfl⟩ : syracuseStep 1989475991 = 2984213987) B2984213987
theorem B1867859 : Blo 826349 1867859 := bstep (se 1 (by rfl) ⟨1400894, by rfl⟩ : syracuseStep 1867859 = 2801789) B2801789
theorem B1245503 : Blo 826349 1245503 := bstep (se 1 (by rfl) ⟨934127, by rfl⟩ : syracuseStep 1245503 = 1868255) B1868255
theorem B9437633 : Blo 826349 9437633 := bstep (se 2 (by rfl) ⟨3539112, by rfl⟩ : syracuseStep 9437633 = 7078225) B7078225
theorem B31916555 : Blo 826349 31916555 := bstep (se 1 (by rfl) ⟨23937416, by rfl⟩ : syracuseStep 31916555 = 47874833) B47874833
theorem B163513961 : Blo 826349 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B1181567 : Blo 826349 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B9570467 : Blo 826349 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B1575119 : Blo 826349 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B2656745 : Blo 826349 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B2099803 : Blo 826349 2099803 := bstep (se 1 (by rfl) ⟨1574852, by rfl⟩ : syracuseStep 2099803 = 3149705) B3149705
theorem B20122793 : Blo 826349 20122793 := bstep (se 2 (by rfl) ⟨7546047, by rfl⟩ : syracuseStep 20122793 = 15092095) B15092095
theorem B88247501 : Blo 826349 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2788991 : Blo 826349 2788991 := bstep (se 1 (by rfl) ⟨2091743, by rfl⟩ : syracuseStep 2788991 = 4183487) B4183487
theorem B2789369 : Blo 826349 2789369 := bstep (se 2 (by rfl) ⟨1046013, by rfl⟩ : syracuseStep 2789369 = 2092027) B2092027
theorem B1511465 : Blo 826349 1511465 := bstep (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) B1133599
theorem B17895491 : Blo 826349 17895491 := bstep (se 1 (by rfl) ⟨13421618, by rfl⟩ : syracuseStep 17895491 = 26843237) B26843237
theorem B2101423 : Blo 826349 2101423 := bstep (se 1 (by rfl) ⟨1576067, by rfl⟩ : syracuseStep 2101423 = 3152135) B3152135
theorem B21270761 : Blo 826349 21270761 := bstep (se 2 (by rfl) ⟨7976535, by rfl⟩ : syracuseStep 21270761 = 15953071) B15953071
theorem B14520653 : Blo 826349 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B3543659 : Blo 826349 3543659 := bstep (se 1 (by rfl) ⟨2657744, by rfl⟩ : syracuseStep 3543659 = 5315489) B5315489
theorem B1675903 : Blo 826349 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B6722291 : Blo 826349 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B2790665 : Blo 826349 2790665 := bstep (se 2 (by rfl) ⟨1046499, by rfl⟩ : syracuseStep 2790665 = 2092999) B2092999
theorem B2659871 : Blo 826349 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B5675105 : Blo 826349 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B2234687 : Blo 826349 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B5315003 : Blo 826349 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B2792231 : Blo 826349 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B826495 : Blo 826349 826495 := bstep (se 1 (by rfl) ⟨619871, by rfl⟩ : syracuseStep 826495 = 1239743) B1239743
theorem B826879 : Blo 826349 826879 := bstep (se 1 (by rfl) ⟨620159, by rfl⟩ : syracuseStep 826879 = 1240319) B1240319
theorem B827007 : Blo 826349 827007 := bstep (se 1 (by rfl) ⟨620255, by rfl⟩ : syracuseStep 827007 = 1240511) B1240511
theorem B20160161 : Blo 826349 20160161 := bstep (se 2 (by rfl) ⟨7560060, by rfl⟩ : syracuseStep 20160161 = 15120121) B15120121
theorem B827227 : Blo 826349 827227 := bstep (se 1 (by rfl) ⟨620420, by rfl⟩ : syracuseStep 827227 = 1240841) B1240841
theorem B827643 : Blo 826349 827643 := bstep (se 1 (by rfl) ⟨620732, by rfl⟩ : syracuseStep 827643 = 1241465) B1241465
theorem B828159 : Blo 826349 828159 := bstep (se 1 (by rfl) ⟨621119, by rfl⟩ : syracuseStep 828159 = 1242239) B1242239
theorem B829435 : Blo 826349 829435 := bstep (se 1 (by rfl) ⟨622076, by rfl⟩ : syracuseStep 829435 = 1244153) B1244153
theorem B6039593 : Blo 826349 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B830143 : Blo 826349 830143 := bstep (se 1 (by rfl) ⟨622607, by rfl⟩ : syracuseStep 830143 = 1245215) B1245215
theorem B8956655 : Blo 826349 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B17902919 : Blo 826349 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B2240633 : Blo 826349 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B290175209 : Blo 826349 290175209 := bstep (se 2 (by rfl) ⟨108815703, by rfl⟩ : syracuseStep 290175209 = 217631407) B217631407
theorem B5031503 : Blo 826349 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B1394543 : Blo 826349 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B7063463 : Blo 826349 7063463 := bstep (se 1 (by rfl) ⟨5297597, by rfl⟩ : syracuseStep 7063463 = 10595195) B10595195
theorem B14176133 : Blo 826349 14176133 := bstep (se 4 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 14176133 = 2658025) B2658025
theorem B5165147 : Blo 826349 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B1398377 : Blo 826349 1398377 := bstep (se 2 (by rfl) ⟨524391, by rfl⟩ : syracuseStep 1398377 = 1048783) B1048783
theorem B1399295 : Blo 826349 1399295 := bstep (se 1 (by rfl) ⟨1049471, by rfl⟩ : syracuseStep 1399295 = 2098943) B2098943
theorem B3595055 : Blo 826349 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B1400287 : Blo 826349 1400287 := bstep (se 1 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 1400287 = 2100431) B2100431
theorem B1400935 : Blo 826349 1400935 := bstep (se 1 (by rfl) ⟨1050701, by rfl⟩ : syracuseStep 1400935 = 2101403) B2101403
theorem B6709675 : Blo 826349 6709675 := bstep (se 1 (by rfl) ⟨5032256, by rfl⟩ : syracuseStep 6709675 = 10064513) B10064513
theorem B1860191 : Blo 826349 1860191 := bstep (se 1 (by rfl) ⟨1395143, by rfl⟩ : syracuseStep 1860191 = 2790287) B2790287
theorem B4481831 : Blo 826349 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B1860947 : Blo 826349 1860947 := bstep (se 1 (by rfl) ⟨1395710, by rfl⟩ : syracuseStep 1860947 = 2791421) B2791421
theorem B28632683 : Blo 826349 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B1861739 : Blo 826349 1861739 := bstep (se 1 (by rfl) ⟨1396304, by rfl⟩ : syracuseStep 1861739 = 2792609) B2792609
theorem B1239647 : Blo 826349 1239647 := bstep (se 1 (by rfl) ⟨929735, by rfl⟩ : syracuseStep 1239647 = 1859471) B1859471
theorem B1239977 : Blo 826349 1239977 := bstep (se 2 (by rfl) ⟨464991, by rfl⟩ : syracuseStep 1239977 = 929983) B929983
theorem B4189481 : Blo 826349 4189481 := bstep (se 2 (by rfl) ⟨1571055, by rfl⟩ : syracuseStep 4189481 = 3142111) B3142111
theorem B2649619 : Blo 826349 2649619 := bstep (se 1 (by rfl) ⟨1987214, by rfl⟩ : syracuseStep 2649619 = 3974429) B3974429
theorem B1863593 : Blo 826349 1863593 := bstep (se 2 (by rfl) ⟨698847, by rfl⟩ : syracuseStep 1863593 = 1397695) B1397695
theorem B1241225 : Blo 826349 1241225 := bstep (se 2 (by rfl) ⟨465459, by rfl⟩ : syracuseStep 1241225 = 930919) B930919
theorem B2093435 : Blo 826349 2093435 := bstep (se 1 (by rfl) ⟨1570076, by rfl⟩ : syracuseStep 2093435 = 3140153) B3140153
theorem B1241579 : Blo 826349 1241579 := bstep (se 1 (by rfl) ⟨931184, by rfl⟩ : syracuseStep 1241579 = 1862369) B1862369
theorem B1241705 : Blo 826349 1241705 := bstep (se 2 (by rfl) ⟨465639, by rfl⟩ : syracuseStep 1241705 = 931279) B931279
theorem B551580299 : Blo 826349 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B57308057 : Blo 826349 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B1242143 : Blo 826349 1242143 := bstep (se 1 (by rfl) ⟨931607, by rfl⟩ : syracuseStep 1242143 = 1863215) B1863215
theorem B1242203 : Blo 826349 1242203 := bstep (se 1 (by rfl) ⟨931652, by rfl⟩ : syracuseStep 1242203 = 1863305) B1863305
theorem B1242215 : Blo 826349 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B1242335 : Blo 826349 1242335 := bstep (se 1 (by rfl) ⟨931751, by rfl⟩ : syracuseStep 1242335 = 1863503) B1863503
theorem B3536311 : Blo 826349 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B1177193 : Blo 826349 1177193 := bstep (se 2 (by rfl) ⟨441447, by rfl⟩ : syracuseStep 1177193 = 882895) B882895
theorem B2127647 : Blo 826349 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B1243247 : Blo 826349 1243247 := bstep (se 1 (by rfl) ⟨932435, by rfl⟩ : syracuseStep 1243247 = 1864871) B1864871
theorem B1866041 : Blo 826349 1866041 := bstep (se 2 (by rfl) ⟨699765, by rfl⟩ : syracuseStep 1866041 = 1399531) B1399531
theorem B1243583 : Blo 826349 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B2652797 : Blo 826349 2652797 := bstep (se 3 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 2652797 = 994799) B994799
theorem B1243967 : Blo 826349 1243967 := bstep (se 1 (by rfl) ⟨932975, by rfl⟩ : syracuseStep 1243967 = 1865951) B1865951
theorem B4488169 : Blo 826349 4488169 := bstep (se 2 (by rfl) ⟨1683063, by rfl⟩ : syracuseStep 4488169 = 3366127) B3366127
theorem B5307439 : Blo 826349 5307439 := bstep (se 1 (by rfl) ⟨3980579, by rfl⟩ : syracuseStep 5307439 = 7961159) B7961159
theorem B1244351 : Blo 826349 1244351 := bstep (se 1 (by rfl) ⟨933263, by rfl⟩ : syracuseStep 1244351 = 1866527) B1866527
theorem B1244507 : Blo 826349 1244507 := bstep (se 1 (by rfl) ⟨933380, by rfl⟩ : syracuseStep 1244507 = 1866761) B1866761
theorem B1244879 : Blo 826349 1244879 := bstep (se 1 (by rfl) ⟨933659, by rfl⟩ : syracuseStep 1244879 = 1867319) B1867319
theorem B1244891 : Blo 826349 1244891 := bstep (se 1 (by rfl) ⟨933668, by rfl⟩ : syracuseStep 1244891 = 1867337) B1867337
theorem B1326317327 : Blo 826349 1326317327 := bstep (se 1 (by rfl) ⟨994737995, by rfl⟩ : syracuseStep 1326317327 = 1989475991) B1989475991
theorem B1245239 : Blo 826349 1245239 := bstep (se 1 (by rfl) ⟨933929, by rfl⟩ : syracuseStep 1245239 = 1867859) B1867859
theorem B4030573 : Blo 826349 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B1867913 : Blo 826349 1867913 := bstep (se 2 (by rfl) ⟨700467, by rfl⟩ : syracuseStep 1867913 = 1400935) B1400935
theorem B6291755 : Blo 826349 6291755 := bstep (se 1 (by rfl) ⟨4718816, by rfl⟩ : syracuseStep 6291755 = 9437633) B9437633
theorem B8946233 : Blo 826349 8946233 := bstep (se 2 (by rfl) ⟨3354837, by rfl⟩ : syracuseStep 8946233 = 6709675) B6709675
theorem B1050079 : Blo 826349 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B1771163 : Blo 826349 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B17926109 : Blo 826349 17926109 := bstep (se 3 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 17926109 = 6722291) B6722291
theorem B11930327 : Blo 826349 11930327 := bstep (se 1 (by rfl) ⟨8947745, by rfl⟩ : syracuseStep 11930327 = 17895491) B17895491
theorem B2362439 : Blo 826349 2362439 := bstep (se 1 (by rfl) ⟨1771829, by rfl⟩ : syracuseStep 2362439 = 3543659) B3543659
theorem B1773247 : Blo 826349 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B3543335 : Blo 826349 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B5673725 : Blo 826349 5673725 := bstep (se 3 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 5673725 = 2127647) B2127647
theorem B3150845 : Blo 826349 3150845 := bstep (se 3 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 3150845 = 1181567) B1181567
theorem B13440107 : Blo 826349 13440107 := bstep (se 1 (by rfl) ⟨10080080, by rfl⟩ : syracuseStep 13440107 = 20160161) B20160161
theorem B2987887 : Blo 826349 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2234537 : Blo 826349 2234537 := bstep (se 2 (by rfl) ⟨837951, by rfl⟩ : syracuseStep 2234537 = 1675903) B1675903
theorem B826431 : Blo 826349 826431 := bstep (se 1 (by rfl) ⟨619823, by rfl⟩ : syracuseStep 826431 = 1239647) B1239647
theorem B5971103 : Blo 826349 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B826651 : Blo 826349 826651 := bstep (se 1 (by rfl) ⟨619988, by rfl⟩ : syracuseStep 826651 = 1239977) B1239977
theorem B2792987 : Blo 826349 2792987 := bstep (se 1 (by rfl) ⟨2094740, by rfl⟩ : syracuseStep 2792987 = 4189481) B4189481
theorem B11935279 : Blo 826349 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B827483 : Blo 826349 827483 := bstep (se 1 (by rfl) ⟨620612, by rfl⟩ : syracuseStep 827483 = 1241225) B1241225
theorem B827719 : Blo 826349 827719 := bstep (se 1 (by rfl) ⟨620789, by rfl⟩ : syracuseStep 827719 = 1241579) B1241579
theorem B827803 : Blo 826349 827803 := bstep (se 1 (by rfl) ⟨620852, by rfl⟩ : syracuseStep 827803 = 1241705) B1241705
theorem B38347253 : Blo 826349 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B828095 : Blo 826349 828095 := bstep (se 1 (by rfl) ⟨621071, by rfl⟩ : syracuseStep 828095 = 1242143) B1242143
theorem B828135 : Blo 826349 828135 := bstep (se 1 (by rfl) ⟨621101, by rfl⟩ : syracuseStep 828135 = 1242203) B1242203
theorem B828143 : Blo 826349 828143 := bstep (se 1 (by rfl) ⟨621107, by rfl⟩ : syracuseStep 828143 = 1242215) B1242215
theorem B828223 : Blo 826349 828223 := bstep (se 1 (by rfl) ⟨621167, by rfl⟩ : syracuseStep 828223 = 1242335) B1242335
theorem B828831 : Blo 826349 828831 := bstep (se 1 (by rfl) ⟨621623, by rfl⟩ : syracuseStep 828831 = 1243247) B1243247
theorem B829055 : Blo 826349 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B829311 : Blo 826349 829311 := bstep (se 1 (by rfl) ⟨621983, by rfl⟩ : syracuseStep 829311 = 1243967) B1243967
theorem B829567 : Blo 826349 829567 := bstep (se 1 (by rfl) ⟨622175, by rfl⟩ : syracuseStep 829567 = 1244351) B1244351
theorem B829671 : Blo 826349 829671 := bstep (se 1 (by rfl) ⟨622253, by rfl⟩ : syracuseStep 829671 = 1244507) B1244507
theorem B829919 : Blo 826349 829919 := bstep (se 1 (by rfl) ⟨622439, by rfl⟩ : syracuseStep 829919 = 1244879) B1244879
theorem B829927 : Blo 826349 829927 := bstep (se 1 (by rfl) ⟨622445, by rfl⟩ : syracuseStep 829927 = 1244891) B1244891
theorem B830335 : Blo 826349 830335 := bstep (se 1 (by rfl) ⟨622751, by rfl⟩ : syracuseStep 830335 = 1245503) B1245503
theorem B13773725 : Blo 826349 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B5975021 : Blo 826349 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B21277703 : Blo 826349 21277703 := bstep (se 1 (by rfl) ⟨15958277, by rfl⟩ : syracuseStep 21277703 = 31916555) B31916555
theorem B3354335 : Blo 826349 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B929695 : Blo 826349 929695 := bstep (se 1 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 929695 = 1394543) B1394543
theorem B13415195 : Blo 826349 13415195 := bstep (se 1 (by rfl) ⟨10061396, by rfl⟩ : syracuseStep 13415195 = 20122793) B20122793
theorem B58831667 : Blo 826349 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B9450755 : Blo 826349 9450755 := bstep (se 1 (by rfl) ⟨7088066, by rfl⟩ : syracuseStep 9450755 = 14176133) B14176133
theorem B9680435 : Blo 826349 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B2799737 : Blo 826349 2799737 := bstep (se 2 (by rfl) ⟨1049901, by rfl⟩ : syracuseStep 2799737 = 2099803) B2099803
theorem B932251 : Blo 826349 932251 := bstep (se 1 (by rfl) ⟨699188, by rfl⟩ : syracuseStep 932251 = 1398377) B1398377
theorem B932863 : Blo 826349 932863 := bstep (se 1 (by rfl) ⟨699647, by rfl⟩ : syracuseStep 932863 = 1399295) B1399295
theorem B2801897 : Blo 826349 2801897 := bstep (se 2 (by rfl) ⟨1050711, by rfl⟩ : syracuseStep 2801897 = 2101423) B2101423
theorem B19088455 : Blo 826349 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B1395623 : Blo 826349 1395623 := bstep (se 1 (by rfl) ⟨1046717, by rfl⟩ : syracuseStep 1395623 = 2093435) B2093435
theorem B5984225 : Blo 826349 5984225 := bstep (se 2 (by rfl) ⟨2244084, by rfl⟩ : syracuseStep 5984225 = 4488169) B4488169
theorem B193450139 : Blo 826349 193450139 := bstep (se 1 (by rfl) ⟨145087604, by rfl⟩ : syracuseStep 193450139 = 290175209) B290175209
theorem B109009307 : Blo 826349 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B4708975 : Blo 826349 4708975 := bstep (se 1 (by rfl) ⟨3531731, by rfl⟩ : syracuseStep 4708975 = 7063463) B7063463
theorem B6380311 : Blo 826349 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B1859327 : Blo 826349 1859327 := bstep (se 1 (by rfl) ⟨1394495, by rfl⟩ : syracuseStep 1859327 = 2788991) B2788991
theorem B1859579 : Blo 826349 1859579 := bstep (se 1 (by rfl) ⟨1394684, by rfl⟩ : syracuseStep 1859579 = 2789369) B2789369
theorem B14180507 : Blo 826349 14180507 := bstep (se 1 (by rfl) ⟨10635380, by rfl⟩ : syracuseStep 14180507 = 21270761) B21270761
theorem B1860443 : Blo 826349 1860443 := bstep (se 1 (by rfl) ⟨1395332, by rfl⟩ : syracuseStep 1860443 = 2790665) B2790665
theorem B3139181 : Blo 826349 3139181 := bstep (se 3 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 3139181 = 1177193) B1177193
theorem B1861487 : Blo 826349 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B3532825 : Blo 826349 3532825 := bstep (se 2 (by rfl) ⟨1324809, by rfl⟩ : syracuseStep 3532825 = 2649619) B2649619
theorem B15133613 : Blo 826349 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B1240127 : Blo 826349 1240127 := bstep (se 1 (by rfl) ⟨930095, by rfl⟩ : syracuseStep 1240127 = 1860191) B1860191
theorem B5959165 : Blo 826349 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B1240631 : Blo 826349 1240631 := bstep (se 1 (by rfl) ⟨930473, by rfl⟩ : syracuseStep 1240631 = 1860947) B1860947
theorem B4026395 : Blo 826349 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B1241159 : Blo 826349 1241159 := bstep (se 1 (by rfl) ⟨930869, by rfl⟩ : syracuseStep 1241159 = 1861739) B1861739
theorem B7074125 : Blo 826349 7074125 := bstep (se 3 (by rfl) ⟨1326398, by rfl⟩ : syracuseStep 7074125 = 2652797) B2652797
theorem B4715081 : Blo 826349 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B1242395 : Blo 826349 1242395 := bstep (se 1 (by rfl) ⟨931796, by rfl⟩ : syracuseStep 1242395 = 1863593) B1863593
theorem B367720199 : Blo 826349 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B38205371 : Blo 826349 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B7076585 : Blo 826349 7076585 := bstep (se 2 (by rfl) ⟨2653719, by rfl⟩ : syracuseStep 7076585 = 5307439) B5307439
theorem B1244027 : Blo 826349 1244027 := bstep (se 1 (by rfl) ⟨933020, by rfl⟩ : syracuseStep 1244027 = 1866041) B1866041
theorem B1867049 : Blo 826349 1867049 := bstep (se 2 (by rfl) ⟨700143, by rfl⟩ : syracuseStep 1867049 = 1400287) B1400287
theorem B884211551 : Blo 826349 884211551 := bstep (se 1 (by rfl) ⟨663158663, by rfl⟩ : syracuseStep 884211551 = 1326317327) B1326317327
theorem B1245275 : Blo 826349 1245275 := bstep (se 1 (by rfl) ⟨933956, by rfl⟩ : syracuseStep 1245275 = 1867913) B1867913
theorem B5374097 : Blo 826349 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B1867931 : Blo 826349 1867931 := bstep (se 1 (by rfl) ⟨1400948, by rfl⟩ : syracuseStep 1867931 = 2801897) B2801897
theorem B4194503 : Blo 826349 4194503 := bstep (se 1 (by rfl) ⟨3145877, by rfl⟩ : syracuseStep 4194503 = 6291755) B6291755
theorem B5964155 : Blo 826349 5964155 := bstep (se 1 (by rfl) ⟨4473116, by rfl⟩ : syracuseStep 5964155 = 8946233) B8946233
theorem B1180775 : Blo 826349 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B1574959 : Blo 826349 1574959 := bstep (se 1 (by rfl) ⟨1181219, by rfl⟩ : syracuseStep 1574959 = 2362439) B2362439
theorem B2362223 : Blo 826349 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B2100563 : Blo 826349 2100563 := bstep (se 1 (by rfl) ⟨1575422, by rfl⟩ : syracuseStep 2100563 = 3150845) B3150845
theorem B2364329 : Blo 826349 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B25564835 : Blo 826349 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B9182483 : Blo 826349 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B826751 : Blo 826349 826751 := bstep (se 1 (by rfl) ⟨620063, by rfl⟩ : syracuseStep 826751 = 1240127) B1240127
theorem B827087 : Blo 826349 827087 := bstep (se 1 (by rfl) ⟨620315, by rfl⟩ : syracuseStep 827087 = 1240631) B1240631
theorem B2236223 : Blo 826349 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B827439 : Blo 826349 827439 := bstep (se 1 (by rfl) ⟨620579, by rfl⟩ : syracuseStep 827439 = 1241159) B1241159
theorem B6300503 : Blo 826349 6300503 := bstep (se 1 (by rfl) ⟨4725377, by rfl⟩ : syracuseStep 6300503 = 9450755) B9450755
theorem B828263 : Blo 826349 828263 := bstep (se 1 (by rfl) ⟨621197, by rfl⟩ : syracuseStep 828263 = 1242395) B1242395
theorem B245146799 : Blo 826349 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B25470247 : Blo 826349 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B829351 : Blo 826349 829351 := bstep (se 1 (by rfl) ⟨622013, by rfl⟩ : syracuseStep 829351 = 1244027) B1244027
theorem B589474367 : Blo 826349 589474367 := bstep (se 1 (by rfl) ⟨442105775, by rfl⟩ : syracuseStep 589474367 = 884211551) B884211551
theorem B830159 : Blo 826349 830159 := bstep (se 1 (by rfl) ⟨622619, by rfl⟩ : syracuseStep 830159 = 1245239) B1245239
theorem B930415 : Blo 826349 930415 := bstep (se 1 (by rfl) ⟨697811, by rfl⟩ : syracuseStep 930415 = 1395623) B1395623
theorem B3782483 : Blo 826349 3782483 := bstep (se 1 (by rfl) ⟨2836862, by rfl⟩ : syracuseStep 3782483 = 5673725) B5673725
theorem B8960071 : Blo 826349 8960071 := bstep (se 1 (by rfl) ⟨6720053, by rfl⟩ : syracuseStep 8960071 = 13440107) B13440107
theorem B1489691 : Blo 826349 1489691 := bstep (se 1 (by rfl) ⟨1117268, by rfl⟩ : syracuseStep 1489691 = 2234537) B2234537
theorem B7945553 : Blo 826349 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B3980735 : Blo 826349 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B9453671 : Blo 826349 9453671 := bstep (se 1 (by rfl) ⟨7090253, by rfl⟩ : syracuseStep 9453671 = 14180507) B14180507
theorem B3983347 : Blo 826349 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B40356301 : Blo 826349 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B3983849 : Blo 826349 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B6278633 : Blo 826349 6278633 := bstep (se 2 (by rfl) ⟨2354487, by rfl⟩ : syracuseStep 6278633 = 4708975) B4708975
theorem B8507081 : Blo 826349 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B15913705 : Blo 826349 15913705 := bstep (se 2 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 15913705 = 11935279) B11935279
theorem B11950739 : Blo 826349 11950739 := bstep (se 1 (by rfl) ⟨8963054, by rfl⟩ : syracuseStep 11950739 = 17926109) B17926109
theorem B25451273 : Blo 826349 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B7953551 : Blo 826349 7953551 := bstep (se 1 (by rfl) ⟨5965163, by rfl⟩ : syracuseStep 7953551 = 11930327) B11930327
theorem B1400105 : Blo 826349 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B3989483 : Blo 826349 3989483 := bstep (se 1 (by rfl) ⟨2992112, by rfl⟩ : syracuseStep 3989483 = 5984225) B5984225
theorem B4710433 : Blo 826349 4710433 := bstep (se 2 (by rfl) ⟨1766412, by rfl⟩ : syracuseStep 4710433 = 3532825) B3532825
theorem B128966759 : Blo 826349 128966759 := bstep (se 1 (by rfl) ⟨96725069, by rfl⟩ : syracuseStep 128966759 = 193450139) B193450139
theorem B72672871 : Blo 826349 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B1861991 : Blo 826349 1861991 := bstep (se 1 (by rfl) ⟨1396493, by rfl⟩ : syracuseStep 1861991 = 2792987) B2792987
theorem B1239551 : Blo 826349 1239551 := bstep (se 1 (by rfl) ⟨929663, by rfl⟩ : syracuseStep 1239551 = 1859327) B1859327
theorem B1239593 : Blo 826349 1239593 := bstep (se 2 (by rfl) ⟨464847, by rfl⟩ : syracuseStep 1239593 = 929695) B929695
theorem B1239719 : Blo 826349 1239719 := bstep (se 1 (by rfl) ⟨929789, by rfl⟩ : syracuseStep 1239719 = 1859579) B1859579
theorem B1240295 : Blo 826349 1240295 := bstep (se 1 (by rfl) ⟨930221, by rfl⟩ : syracuseStep 1240295 = 1860443) B1860443
theorem B2092787 : Blo 826349 2092787 := bstep (se 1 (by rfl) ⟨1569590, by rfl⟩ : syracuseStep 2092787 = 3139181) B3139181
theorem B1240991 : Blo 826349 1240991 := bstep (se 1 (by rfl) ⟨930743, by rfl⟩ : syracuseStep 1240991 = 1861487) B1861487
theorem B14185135 : Blo 826349 14185135 := bstep (se 1 (by rfl) ⟨10638851, by rfl⟩ : syracuseStep 14185135 = 21277703) B21277703
theorem B2684263 : Blo 826349 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B4716083 : Blo 826349 4716083 := bstep (se 1 (by rfl) ⟨3537062, by rfl⟩ : syracuseStep 4716083 = 7074125) B7074125
theorem B3143387 : Blo 826349 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B8943463 : Blo 826349 8943463 := bstep (se 1 (by rfl) ⟨6707597, by rfl⟩ : syracuseStep 8943463 = 13415195) B13415195
theorem B39221111 : Blo 826349 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B1243001 : Blo 826349 1243001 := bstep (se 2 (by rfl) ⟨466125, by rfl⟩ : syracuseStep 1243001 = 932251) B932251
theorem B6453623 : Blo 826349 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B1243817 : Blo 826349 1243817 := bstep (se 2 (by rfl) ⟨466431, by rfl⟩ : syracuseStep 1243817 = 932863) B932863
theorem B1866491 : Blo 826349 1866491 := bstep (se 1 (by rfl) ⟨1399868, by rfl⟩ : syracuseStep 1866491 = 2799737) B2799737
theorem B4717723 : Blo 826349 4717723 := bstep (se 1 (by rfl) ⟨3538292, by rfl⟩ : syracuseStep 4717723 = 7076585) B7076585
theorem B1244699 : Blo 826349 1244699 := bstep (se 1 (by rfl) ⟨933524, by rfl⟩ : syracuseStep 1244699 = 1867049) B1867049
theorem B1245287 : Blo 826349 1245287 := bstep (se 1 (by rfl) ⟨933965, by rfl⟩ : syracuseStep 1245287 = 1867931) B1867931
theorem B2655899 : Blo 826349 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1574815 : Blo 826349 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B96897161 : Blo 826349 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B5671387 : Blo 826349 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B2099945 : Blo 826349 2099945 := bstep (se 2 (by rfl) ⟨787479, by rfl⟩ : syracuseStep 2099945 = 1574959) B1574959
theorem B3148733 : Blo 826349 3148733 := bstep (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) B1180775
theorem B53808401 : Blo 826349 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B17043223 : Blo 826349 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B7967159 : Blo 826349 7967159 := bstep (se 1 (by rfl) ⟨5975369, by rfl⟩ : syracuseStep 7967159 = 11950739) B11950739
theorem B2659655 : Blo 826349 2659655 := bstep (se 1 (by rfl) ⟨1994741, by rfl⟩ : syracuseStep 2659655 = 3989483) B3989483
theorem B4200335 : Blo 826349 4200335 := bstep (se 1 (by rfl) ⟨3150251, by rfl⟩ : syracuseStep 4200335 = 6300503) B6300503
theorem B18913513 : Blo 826349 18913513 := bstep (se 2 (by rfl) ⟨7092567, by rfl⟩ : syracuseStep 18913513 = 14185135) B14185135
theorem B826367 : Blo 826349 826367 := bstep (se 1 (by rfl) ⟨619775, by rfl⟩ : syracuseStep 826367 = 1239551) B1239551
theorem B826395 : Blo 826349 826395 := bstep (se 1 (by rfl) ⟨619796, by rfl⟩ : syracuseStep 826395 = 1239593) B1239593
theorem B826479 : Blo 826349 826479 := bstep (se 1 (by rfl) ⟨619859, by rfl⟩ : syracuseStep 826479 = 1239719) B1239719
theorem B3579017 : Blo 826349 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B67870061 : Blo 826349 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B3972509 : Blo 826349 3972509 := bstep (se 3 (by rfl) ⟨744845, by rfl⟩ : syracuseStep 3972509 = 1489691) B1489691
theorem B826863 : Blo 826349 826863 := bstep (se 1 (by rfl) ⟨620147, by rfl⟩ : syracuseStep 826863 = 1240295) B1240295
theorem B827327 : Blo 826349 827327 := bstep (se 1 (by rfl) ⟨620495, by rfl⟩ : syracuseStep 827327 = 1240991) B1240991
theorem B828667 : Blo 826349 828667 := bstep (se 1 (by rfl) ⟨621500, by rfl⟩ : syracuseStep 828667 = 1243001) B1243001
theorem B4302415 : Blo 826349 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B829211 : Blo 826349 829211 := bstep (se 1 (by rfl) ⟨621908, by rfl⟩ : syracuseStep 829211 = 1243817) B1243817
theorem B829799 : Blo 826349 829799 := bstep (se 1 (by rfl) ⟨622349, by rfl⟩ : syracuseStep 829799 = 1244699) B1244699
theorem B21244517 : Blo 826349 21244517 := bstep (se 4 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 21244517 = 3983347) B3983347
theorem B830183 : Blo 826349 830183 := bstep (se 1 (by rfl) ⟨622637, by rfl⟩ : syracuseStep 830183 = 1245275) B1245275
theorem B6302447 : Blo 826349 6302447 := bstep (se 1 (by rfl) ⟨4726835, by rfl⟩ : syracuseStep 6302447 = 9453671) B9453671
theorem B3582731 : Blo 826349 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B2796335 : Blo 826349 2796335 := bstep (se 1 (by rfl) ⟨2097251, by rfl⟩ : syracuseStep 2796335 = 4194503) B4194503
theorem B3976103 : Blo 826349 3976103 := bstep (se 1 (by rfl) ⟨2982077, by rfl⟩ : syracuseStep 3976103 = 5964155) B5964155
theorem B33960329 : Blo 826349 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B6304877 : Blo 826349 6304877 := bstep (se 3 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 6304877 = 2364329) B2364329
theorem B933403 : Blo 826349 933403 := bstep (se 1 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 933403 = 1400105) B1400105
theorem B1490815 : Blo 826349 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B163431199 : Blo 826349 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B21218273 : Blo 826349 21218273 := bstep (se 2 (by rfl) ⟨7956852, by rfl⟩ : syracuseStep 21218273 = 15913705) B15913705
theorem B1395191 : Blo 826349 1395191 := bstep (se 1 (by rfl) ⟨1046393, by rfl⟩ : syracuseStep 1395191 = 2092787) B2092787
theorem B11946761 : Blo 826349 11946761 := bstep (se 2 (by rfl) ⟨4480035, by rfl⟩ : syracuseStep 11946761 = 8960071) B8960071
theorem B5297035 : Blo 826349 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B6280577 : Blo 826349 6280577 := bstep (se 2 (by rfl) ⟨2355216, by rfl⟩ : syracuseStep 6280577 = 4710433) B4710433
theorem B1400375 : Blo 826349 1400375 := bstep (se 1 (by rfl) ⟨1050281, by rfl⟩ : syracuseStep 1400375 = 2100563) B2100563
theorem B4185755 : Blo 826349 4185755 := bstep (se 1 (by rfl) ⟨3139316, by rfl⟩ : syracuseStep 4185755 = 6278633) B6278633
theorem B5302367 : Blo 826349 5302367 := bstep (se 1 (by rfl) ⟨3976775, by rfl⟩ : syracuseStep 5302367 = 7953551) B7953551
theorem B6121655 : Blo 826349 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B85977839 : Blo 826349 85977839 := bstep (se 1 (by rfl) ⟨64483379, by rfl⟩ : syracuseStep 85977839 = 128966759) B128966759
theorem B1240553 : Blo 826349 1240553 := bstep (se 2 (by rfl) ⟨465207, by rfl⟩ : syracuseStep 1240553 = 930415) B930415
theorem B1241327 : Blo 826349 1241327 := bstep (se 1 (by rfl) ⟨930995, by rfl⟩ : syracuseStep 1241327 = 1861991) B1861991
theorem B392982911 : Blo 826349 392982911 := bstep (se 1 (by rfl) ⟨294737183, by rfl⟩ : syracuseStep 392982911 = 589474367) B589474367
theorem B11924617 : Blo 826349 11924617 := bstep (se 2 (by rfl) ⟨4471731, by rfl⟩ : syracuseStep 11924617 = 8943463) B8943463
theorem B3144055 : Blo 826349 3144055 := bstep (se 1 (by rfl) ⟨2358041, by rfl⟩ : syracuseStep 3144055 = 4716083) B4716083
theorem B2095591 : Blo 826349 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B2521655 : Blo 826349 2521655 := bstep (se 1 (by rfl) ⟨1891241, by rfl⟩ : syracuseStep 2521655 = 3782483) B3782483
theorem B26147407 : Blo 826349 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B6290297 : Blo 826349 6290297 := bstep (se 2 (by rfl) ⟨2358861, by rfl⟩ : syracuseStep 6290297 = 4717723) B4717723
theorem B1244327 : Blo 826349 1244327 := bstep (se 1 (by rfl) ⟨933245, by rfl⟩ : syracuseStep 1244327 = 1866491) B1866491
theorem B2653823 : Blo 826349 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B217908265 : Blo 826349 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1770599 : Blo 826349 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B38176181 : Blo 826349 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B7964507 : Blo 826349 7964507 := bstep (se 1 (by rfl) ⟨5973380, by rfl⟩ : syracuseStep 7964507 = 11946761) B11946761
theorem B2099155 : Blo 826349 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B5736553 : Blo 826349 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B2099753 : Blo 826349 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B5311439 : Blo 826349 5311439 := bstep (se 1 (by rfl) ⟨3983579, by rfl⟩ : syracuseStep 5311439 = 7967159) B7967159
theorem B1773103 : Blo 826349 1773103 := bstep (se 1 (by rfl) ⟨1329827, by rfl⟩ : syracuseStep 1773103 = 2659655) B2659655
theorem B2790503 : Blo 826349 2790503 := bstep (se 1 (by rfl) ⟨2092877, by rfl⟩ : syracuseStep 2790503 = 4185755) B4185755
theorem B15899489 : Blo 826349 15899489 := bstep (se 2 (by rfl) ⟨5962308, by rfl⟩ : syracuseStep 15899489 = 11924617) B11924617
theorem B14163011 : Blo 826349 14163011 := bstep (se 1 (by rfl) ⟨10622258, by rfl⟩ : syracuseStep 14163011 = 21244517) B21244517
theorem B57318559 : Blo 826349 57318559 := bstep (se 1 (by rfl) ⟨42988919, by rfl⟩ : syracuseStep 57318559 = 85977839) B85977839
theorem B4201631 : Blo 826349 4201631 := bstep (se 1 (by rfl) ⟨3151223, by rfl⟩ : syracuseStep 4201631 = 6302447) B6302447
theorem B827035 : Blo 826349 827035 := bstep (se 1 (by rfl) ⟨620276, by rfl⟩ : syracuseStep 827035 = 1240553) B1240553
theorem B827551 : Blo 826349 827551 := bstep (se 1 (by rfl) ⟨620663, by rfl⟩ : syracuseStep 827551 = 1241327) B1241327
theorem B261988607 : Blo 826349 261988607 := bstep (se 1 (by rfl) ⟨196491455, by rfl⟩ : syracuseStep 261988607 = 392982911) B392982911
theorem B2794121 : Blo 826349 2794121 := bstep (se 2 (by rfl) ⟨1047795, by rfl⟩ : syracuseStep 2794121 = 2095591) B2095591
theorem B4203251 : Blo 826349 4203251 := bstep (se 1 (by rfl) ⟨3152438, by rfl⟩ : syracuseStep 4203251 = 6304877) B6304877
theorem B1681103 : Blo 826349 1681103 := bstep (se 1 (by rfl) ⟨1260827, by rfl⟩ : syracuseStep 1681103 = 2521655) B2521655
theorem B829551 : Blo 826349 829551 := bstep (se 1 (by rfl) ⟨622163, by rfl⟩ : syracuseStep 829551 = 1244327) B1244327
theorem B830191 : Blo 826349 830191 := bstep (se 1 (by rfl) ⟨622643, by rfl⟩ : syracuseStep 830191 = 1245287) B1245287
theorem B930127 : Blo 826349 930127 := bstep (se 1 (by rfl) ⟨697595, by rfl⟩ : syracuseStep 930127 = 1395191) B1395191
theorem B2800223 : Blo 826349 2800223 := bstep (se 1 (by rfl) ⟨2100167, by rfl⟩ : syracuseStep 2800223 = 4200335) B4200335
theorem B22724297 : Blo 826349 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B933583 : Blo 826349 933583 := bstep (se 1 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 933583 = 1400375) B1400375
theorem B258392429 : Blo 826349 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B7062713 : Blo 826349 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B4081103 : Blo 826349 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B25218017 : Blo 826349 25218017 := bstep (se 2 (by rfl) ⟨9456756, by rfl⟩ : syracuseStep 25218017 = 18913513) B18913513
theorem B1987753 : Blo 826349 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B14145515 : Blo 826349 14145515 := bstep (se 1 (by rfl) ⟨10609136, by rfl⟩ : syracuseStep 14145515 = 21218273) B21218273
theorem B1399963 : Blo 826349 1399963 := bstep (se 1 (by rfl) ⟨1049972, by rfl⟩ : syracuseStep 1399963 = 2099945) B2099945
theorem B35872267 : Blo 826349 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B7561849 : Blo 826349 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B4187051 : Blo 826349 4187051 := bstep (se 1 (by rfl) ⟨3140288, by rfl⟩ : syracuseStep 4187051 = 6280577) B6280577
theorem B45246707 : Blo 826349 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B2648339 : Blo 826349 2648339 := bstep (se 1 (by rfl) ⟨1986254, by rfl⟩ : syracuseStep 2648339 = 3972509) B3972509
theorem B3534911 : Blo 826349 3534911 := bstep (se 1 (by rfl) ⟨2651183, by rfl⟩ : syracuseStep 3534911 = 5302367) B5302367
theorem B2388487 : Blo 826349 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B1864223 : Blo 826349 1864223 := bstep (se 1 (by rfl) ⟨1398167, by rfl⟩ : syracuseStep 1864223 = 2796335) B2796335
theorem B2650735 : Blo 826349 2650735 := bstep (se 1 (by rfl) ⟨1988051, by rfl⟩ : syracuseStep 2650735 = 3976103) B3976103
theorem B22640219 : Blo 826349 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B4192073 : Blo 826349 4192073 := bstep (se 2 (by rfl) ⟨1572027, by rfl⟩ : syracuseStep 4192073 = 3144055) B3144055
theorem B34863209 : Blo 826349 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B4193531 : Blo 826349 4193531 := bstep (se 1 (by rfl) ⟨3145148, by rfl⟩ : syracuseStep 4193531 = 6290297) B6290297
theorem B1244537 : Blo 826349 1244537 := bstep (se 2 (by rfl) ⟨466701, by rfl⟩ : syracuseStep 1244537 = 933403) B933403
theorem B1769215 : Blo 826349 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B172261619 : Blo 826349 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B2720735 : Blo 826349 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B5309671 : Blo 826349 5309671 := bstep (se 1 (by rfl) ⟨3982253, by rfl⟩ : syracuseStep 5309671 = 7964507) B7964507
theorem B3540959 : Blo 826349 3540959 := bstep (se 1 (by rfl) ⟨2655719, by rfl⟩ : syracuseStep 3540959 = 5311439) B5311439
theorem B16812011 : Blo 826349 16812011 := bstep (se 1 (by rfl) ⟨12609008, by rfl⟩ : syracuseStep 16812011 = 25218017) B25218017
theorem B4721597 : Blo 826349 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B9442007 : Blo 826349 9442007 := bstep (se 1 (by rfl) ⟨7081505, by rfl⟩ : syracuseStep 9442007 = 14163011) B14163011
theorem B2364137 : Blo 826349 2364137 := bstep (se 2 (by rfl) ⟨886551, by rfl⟩ : syracuseStep 2364137 = 1773103) B1773103
theorem B2791367 : Blo 826349 2791367 := bstep (se 1 (by rfl) ⟨2093525, by rfl⟩ : syracuseStep 2791367 = 4187051) B4187051
theorem B3184649 : Blo 826349 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B305698981 : Blo 826349 305698981 := bstep (se 4 (by rfl) ⟨28659279, by rfl⟩ : syracuseStep 305698981 = 57318559) B57318559
theorem B1120735 : Blo 826349 1120735 := bstep (se 1 (by rfl) ⟨840551, by rfl⟩ : syracuseStep 1120735 = 1681103) B1681103
theorem B2794715 : Blo 826349 2794715 := bstep (se 1 (by rfl) ⟨2096036, by rfl⟩ : syracuseStep 2794715 = 4192073) B4192073
theorem B23242139 : Blo 826349 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B2795687 : Blo 826349 2795687 := bstep (se 1 (by rfl) ⟨2096765, by rfl⟩ : syracuseStep 2795687 = 4193531) B4193531
theorem B829691 : Blo 826349 829691 := bstep (se 1 (by rfl) ⟨622268, by rfl⟩ : syracuseStep 829691 = 1244537) B1244537
theorem B15149531 : Blo 826349 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B2798873 : Blo 826349 2798873 := bstep (se 2 (by rfl) ⟨1049577, by rfl⟩ : syracuseStep 2798873 = 2099155) B2099155
theorem B10599659 : Blo 826349 10599659 := bstep (se 1 (by rfl) ⟨7949744, by rfl⟩ : syracuseStep 10599659 = 15899489) B15899489
theorem B2801087 : Blo 826349 2801087 := bstep (se 1 (by rfl) ⟨2100815, by rfl⟩ : syracuseStep 2801087 = 4201631) B4201631
theorem B2802167 : Blo 826349 2802167 := bstep (se 1 (by rfl) ⟨2101625, by rfl⟩ : syracuseStep 2802167 = 4203251) B4203251
theorem B30164471 : Blo 826349 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B15093479 : Blo 826349 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B47829689 : Blo 826349 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B698636285 : Blo 826349 698636285 := bstep (se 3 (by rfl) ⟨130994303, by rfl⟩ : syracuseStep 698636285 = 261988607) B261988607
theorem B4708475 : Blo 826349 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B10082465 : Blo 826349 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B25450787 : Blo 826349 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B290544353 : Blo 826349 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B1399835 : Blo 826349 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B122379797 : Blo 826349 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B1860335 : Blo 826349 1860335 := bstep (se 1 (by rfl) ⟨1395251, by rfl⟩ : syracuseStep 1860335 = 2790503) B2790503
theorem B9430343 : Blo 826349 9430343 := bstep (se 1 (by rfl) ⟨7072757, by rfl⟩ : syracuseStep 9430343 = 14145515) B14145515
theorem B1862747 : Blo 826349 1862747 := bstep (se 1 (by rfl) ⟨1397060, by rfl⟩ : syracuseStep 1862747 = 2794121) B2794121
theorem B1240169 : Blo 826349 1240169 := bstep (se 2 (by rfl) ⟨465063, by rfl⟩ : syracuseStep 1240169 = 930127) B930127
theorem B3534313 : Blo 826349 3534313 := bstep (se 2 (by rfl) ⟨1325367, by rfl⟩ : syracuseStep 3534313 = 2650735) B2650735
theorem B1765559 : Blo 826349 1765559 := bstep (se 1 (by rfl) ⟨1324169, by rfl⟩ : syracuseStep 1765559 = 2648339) B2648339
theorem B2650337 : Blo 826349 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B2356607 : Blo 826349 2356607 := bstep (se 1 (by rfl) ⟨1767455, by rfl⟩ : syracuseStep 2356607 = 3534911) B3534911
theorem B1242815 : Blo 826349 1242815 := bstep (se 1 (by rfl) ⟨932111, by rfl⟩ : syracuseStep 1242815 = 1864223) B1864223
theorem B1866617 : Blo 826349 1866617 := bstep (se 2 (by rfl) ⟨699981, by rfl⟩ : syracuseStep 1866617 = 1399963) B1399963
theorem B1866815 : Blo 826349 1866815 := bstep (se 1 (by rfl) ⟨1400111, by rfl⟩ : syracuseStep 1866815 = 2800223) B2800223
theorem B1244777 : Blo 826349 1244777 := bstep (se 2 (by rfl) ⟨466791, by rfl⟩ : syracuseStep 1244777 = 933583) B933583
theorem B2358953 : Blo 826349 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B1868111 : Blo 826349 1868111 := bstep (se 1 (by rfl) ⟨1401083, by rfl⟩ : syracuseStep 1868111 = 2802167) B2802167
theorem B2360639 : Blo 826349 2360639 := bstep (se 1 (by rfl) ⟨1770479, by rfl⟩ : syracuseStep 2360639 = 3540959) B3540959
theorem B11208007 : Blo 826349 11208007 := bstep (se 1 (by rfl) ⟨8406005, by rfl⟩ : syracuseStep 11208007 = 16812011) B16812011
theorem B7079561 : Blo 826349 7079561 := bstep (se 2 (by rfl) ⟨2654835, by rfl⟩ : syracuseStep 7079561 = 5309671) B5309671
theorem B3147731 : Blo 826349 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B10062319 : Blo 826349 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B31886459 : Blo 826349 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B6294671 : Blo 826349 6294671 := bstep (se 1 (by rfl) ⟨4721003, by rfl⟩ : syracuseStep 6294671 = 9442007) B9442007
theorem B1576091 : Blo 826349 1576091 := bstep (se 1 (by rfl) ⟨1182068, by rfl⟩ : syracuseStep 1576091 = 2364137) B2364137
theorem B6721643 : Blo 826349 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B193696235 : Blo 826349 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B10099687 : Blo 826349 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B826779 : Blo 826349 826779 := bstep (se 1 (by rfl) ⟨620084, by rfl⟩ : syracuseStep 826779 = 1240169) B1240169
theorem B828543 : Blo 826349 828543 := bstep (se 1 (by rfl) ⟨621407, by rfl⟩ : syracuseStep 828543 = 1242815) B1242815
theorem B829851 : Blo 826349 829851 := bstep (se 1 (by rfl) ⟨622388, by rfl⟩ : syracuseStep 829851 = 1244777) B1244777
theorem B1813823 : Blo 826349 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B5977253 : Blo 826349 5977253 := bstep (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) B1120735
theorem B933223 : Blo 826349 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B7066439 : Blo 826349 7066439 := bstep (se 1 (by rfl) ⟨5299829, by rfl⟩ : syracuseStep 7066439 = 10599659) B10599659
theorem B114841079 : Blo 826349 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B20109647 : Blo 826349 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B1860911 : Blo 826349 1860911 := bstep (se 1 (by rfl) ⟨1395683, by rfl⟩ : syracuseStep 1860911 = 2791367) B2791367
theorem B465757523 : Blo 826349 465757523 := bstep (se 1 (by rfl) ⟨349318142, by rfl⟩ : syracuseStep 465757523 = 698636285) B698636285
theorem B2123099 : Blo 826349 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B3138983 : Blo 826349 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B16967191 : Blo 826349 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B4712417 : Blo 826349 4712417 := bstep (se 2 (by rfl) ⟨1767156, by rfl⟩ : syracuseStep 4712417 = 3534313) B3534313
theorem B81586531 : Blo 826349 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B1240223 : Blo 826349 1240223 := bstep (se 1 (by rfl) ⟨930167, by rfl⟩ : syracuseStep 1240223 = 1860335) B1860335
theorem B1863143 : Blo 826349 1863143 := bstep (se 1 (by rfl) ⟨1397357, by rfl⟩ : syracuseStep 1863143 = 2794715) B2794715
theorem B6286895 : Blo 826349 6286895 := bstep (se 1 (by rfl) ⟨4715171, by rfl⟩ : syracuseStep 6286895 = 9430343) B9430343
theorem B15494759 : Blo 826349 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B1863791 : Blo 826349 1863791 := bstep (se 1 (by rfl) ⟨1397843, by rfl⟩ : syracuseStep 1863791 = 2795687) B2795687
theorem B1241831 : Blo 826349 1241831 := bstep (se 1 (by rfl) ⟨931373, by rfl⟩ : syracuseStep 1241831 = 1862747) B1862747
theorem B1177039 : Blo 826349 1177039 := bstep (se 1 (by rfl) ⟨882779, by rfl⟩ : syracuseStep 1177039 = 1765559) B1765559
theorem B1766891 : Blo 826349 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B407598641 : Blo 826349 407598641 := bstep (se 2 (by rfl) ⟨152849490, by rfl⟩ : syracuseStep 407598641 = 305698981) B305698981
theorem B1865915 : Blo 826349 1865915 := bstep (se 1 (by rfl) ⟨1399436, by rfl⟩ : syracuseStep 1865915 = 2798873) B2798873
theorem B1571071 : Blo 826349 1571071 := bstep (se 1 (by rfl) ⟨1178303, by rfl⟩ : syracuseStep 1571071 = 2356607) B2356607
theorem B1244411 : Blo 826349 1244411 := bstep (se 1 (by rfl) ⟨933308, by rfl⟩ : syracuseStep 1244411 = 1866617) B1866617
theorem B1244543 : Blo 826349 1244543 := bstep (se 1 (by rfl) ⟨933407, by rfl⟩ : syracuseStep 1244543 = 1866815) B1866815
theorem B1867391 : Blo 826349 1867391 := bstep (se 1 (by rfl) ⟨1400543, by rfl⟩ : syracuseStep 1867391 = 2801087) B2801087
theorem B1572635 : Blo 826349 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B1245407 : Blo 826349 1245407 := bstep (se 1 (by rfl) ⟨934055, by rfl⟩ : syracuseStep 1245407 = 1868111) B1868111
theorem B1573759 : Blo 826349 1573759 := bstep (se 1 (by rfl) ⟨1180319, by rfl⟩ : syracuseStep 1573759 = 2360639) B2360639
theorem B4719707 : Blo 826349 4719707 := bstep (se 1 (by rfl) ⟨3539780, by rfl⟩ : syracuseStep 4719707 = 7079561) B7079561
theorem B2098487 : Blo 826349 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B14944009 : Blo 826349 14944009 := bstep (se 2 (by rfl) ⟨5604003, by rfl⟩ : syracuseStep 14944009 = 11208007) B11208007
theorem B4196447 : Blo 826349 4196447 := bstep (se 1 (by rfl) ⟨3147335, by rfl⟩ : syracuseStep 4196447 = 6294671) B6294671
theorem B1050727 : Blo 826349 1050727 := bstep (se 1 (by rfl) ⟨788045, by rfl⟩ : syracuseStep 1050727 = 1576091) B1576091
theorem B13406431 : Blo 826349 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B1415399 : Blo 826349 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B826815 : Blo 826349 826815 := bstep (se 1 (by rfl) ⟨620111, by rfl⟩ : syracuseStep 826815 = 1240223) B1240223
theorem B10329839 : Blo 826349 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B827887 : Blo 826349 827887 := bstep (se 1 (by rfl) ⟨620915, by rfl⟩ : syracuseStep 827887 = 1241831) B1241831
theorem B829607 : Blo 826349 829607 := bstep (se 1 (by rfl) ⟨622205, by rfl⟩ : syracuseStep 829607 = 1244411) B1244411
theorem B829695 : Blo 826349 829695 := bstep (se 1 (by rfl) ⟨622271, by rfl⟩ : syracuseStep 829695 = 1244543) B1244543
theorem B22622921 : Blo 826349 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B13416425 : Blo 826349 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B76560719 : Blo 826349 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B3984835 : Blo 826349 3984835 := bstep (se 1 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 3984835 = 5977253) B5977253
theorem B271732427 : Blo 826349 271732427 := bstep (se 1 (by rfl) ⟨203799320, by rfl⟩ : syracuseStep 271732427 = 407598641) B407598641
theorem B21257639 : Blo 826349 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B4481095 : Blo 826349 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B129130823 : Blo 826349 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B108782041 : Blo 826349 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B4710959 : Blo 826349 4710959 := bstep (se 1 (by rfl) ⟨3533219, by rfl⟩ : syracuseStep 4710959 = 7066439) B7066439
theorem B4711709 : Blo 826349 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B1240607 : Blo 826349 1240607 := bstep (se 1 (by rfl) ⟨930455, by rfl⟩ : syracuseStep 1240607 = 1860911) B1860911
theorem B310505015 : Blo 826349 310505015 := bstep (se 1 (by rfl) ⟨232878761, by rfl⟩ : syracuseStep 310505015 = 465757523) B465757523
theorem B2092655 : Blo 826349 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B3141611 : Blo 826349 3141611 := bstep (se 1 (by rfl) ⟨2356208, by rfl⟩ : syracuseStep 3141611 = 4712417) B4712417
theorem B1569385 : Blo 826349 1569385 := bstep (se 2 (by rfl) ⟨588519, by rfl⟩ : syracuseStep 1569385 = 1177039) B1177039
theorem B1209215 : Blo 826349 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B1242095 : Blo 826349 1242095 := bstep (se 1 (by rfl) ⟨931571, by rfl⟩ : syracuseStep 1242095 = 1863143) B1863143
theorem B4191263 : Blo 826349 4191263 := bstep (se 1 (by rfl) ⟨3143447, by rfl⟩ : syracuseStep 4191263 = 6286895) B6286895
theorem B1242527 : Blo 826349 1242527 := bstep (se 1 (by rfl) ⟨931895, by rfl⟩ : syracuseStep 1242527 = 1863791) B1863791
theorem B2094761 : Blo 826349 2094761 := bstep (se 2 (by rfl) ⟨785535, by rfl⟩ : syracuseStep 2094761 = 1571071) B1571071
theorem B13466249 : Blo 826349 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B1243943 : Blo 826349 1243943 := bstep (se 1 (by rfl) ⟨932957, by rfl⟩ : syracuseStep 1243943 = 1865915) B1865915
theorem B1244297 : Blo 826349 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B4193693 : Blo 826349 4193693 := bstep (se 3 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 4193693 = 1572635) B1572635
theorem B1244927 : Blo 826349 1244927 := bstep (se 1 (by rfl) ⟨933695, by rfl⟩ : syracuseStep 1244927 = 1867391) B1867391
theorem B3146471 : Blo 826349 3146471 := bstep (se 1 (by rfl) ⟨2359853, by rfl⟩ : syracuseStep 3146471 = 4719707) B4719707
theorem B2098345 : Blo 826349 2098345 := bstep (se 2 (by rfl) ⟨786879, by rfl⟩ : syracuseStep 2098345 = 1573759) B1573759
theorem B19925345 : Blo 826349 19925345 := bstep (se 2 (by rfl) ⟨7472004, by rfl⟩ : syracuseStep 19925345 = 14944009) B14944009
theorem B5313113 : Blo 826349 5313113 := bstep (se 2 (by rfl) ⟨1992417, by rfl⟩ : syracuseStep 5313113 = 3984835) B3984835
theorem B6886559 : Blo 826349 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B86087215 : Blo 826349 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B3774397 : Blo 826349 3774397 := bstep (se 3 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 3774397 = 1415399) B1415399
theorem B827071 : Blo 826349 827071 := bstep (se 1 (by rfl) ⟨620303, by rfl⟩ : syracuseStep 827071 = 1240607) B1240607
theorem B15081947 : Blo 826349 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B828063 : Blo 826349 828063 := bstep (se 1 (by rfl) ⟨621047, by rfl⟩ : syracuseStep 828063 = 1242095) B1242095
theorem B2794175 : Blo 826349 2794175 := bstep (se 1 (by rfl) ⟨2095631, by rfl⟩ : syracuseStep 2794175 = 4191263) B4191263
theorem B828351 : Blo 826349 828351 := bstep (se 1 (by rfl) ⟨621263, by rfl⟩ : syracuseStep 828351 = 1242527) B1242527
theorem B829295 : Blo 826349 829295 := bstep (se 1 (by rfl) ⟨621971, by rfl⟩ : syracuseStep 829295 = 1243943) B1243943
theorem B829531 : Blo 826349 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B2795795 : Blo 826349 2795795 := bstep (se 1 (by rfl) ⟨2096846, by rfl⟩ : syracuseStep 2795795 = 4193693) B4193693
theorem B829951 : Blo 826349 829951 := bstep (se 1 (by rfl) ⟨622463, by rfl⟩ : syracuseStep 829951 = 1244927) B1244927
theorem B5974793 : Blo 826349 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B830271 : Blo 826349 830271 := bstep (se 1 (by rfl) ⟨622703, by rfl⟩ : syracuseStep 830271 = 1245407) B1245407
theorem B145042721 : Blo 826349 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B2797631 : Blo 826349 2797631 := bstep (se 1 (by rfl) ⟨2098223, by rfl⟩ : syracuseStep 2797631 = 4196447) B4196447
theorem B3224573 : Blo 826349 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B181154951 : Blo 826349 181154951 := bstep (se 1 (by rfl) ⟨135866213, by rfl⟩ : syracuseStep 181154951 = 271732427) B271732427
theorem B14171759 : Blo 826349 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B17875241 : Blo 826349 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B204161917 : Blo 826349 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B1395103 : Blo 826349 1395103 := bstep (se 1 (by rfl) ⟨1046327, by rfl⟩ : syracuseStep 1395103 = 2092655) B2092655
theorem B1396507 : Blo 826349 1396507 := bstep (se 1 (by rfl) ⟨1047380, by rfl⟩ : syracuseStep 1396507 = 2094761) B2094761
theorem B1398991 : Blo 826349 1398991 := bstep (se 1 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 1398991 = 2098487) B2098487
theorem B1400969 : Blo 826349 1400969 := bstep (se 2 (by rfl) ⟨525363, by rfl⟩ : syracuseStep 1400969 = 1050727) B1050727
theorem B3140639 : Blo 826349 3140639 := bstep (se 1 (by rfl) ⟨2355479, by rfl⟩ : syracuseStep 3140639 = 4710959) B4710959
theorem B2092513 : Blo 826349 2092513 := bstep (se 2 (by rfl) ⟨784692, by rfl⟩ : syracuseStep 2092513 = 1569385) B1569385
theorem B3141139 : Blo 826349 3141139 := bstep (se 1 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 3141139 = 4711709) B4711709
theorem B2094407 : Blo 826349 2094407 := bstep (se 1 (by rfl) ⟨1570805, by rfl⟩ : syracuseStep 2094407 = 3141611) B3141611
theorem B8944283 : Blo 826349 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B828013373 : Blo 826349 828013373 := bstep (se 3 (by rfl) ⟨155252507, by rfl⟩ : syracuseStep 828013373 = 310505015) B310505015
theorem B8977499 : Blo 826349 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B2097647 : Blo 826349 2097647 := bstep (se 1 (by rfl) ⟨1573235, by rfl⟩ : syracuseStep 2097647 = 3146471) B3146471
theorem B3542075 : Blo 826349 3542075 := bstep (se 1 (by rfl) ⟨2656556, by rfl⟩ : syracuseStep 3542075 = 5313113) B5313113
theorem B2790017 : Blo 826349 2790017 := bstep (se 2 (by rfl) ⟨1046256, by rfl⟩ : syracuseStep 2790017 = 2092513) B2092513
theorem B9447839 : Blo 826349 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B272215889 : Blo 826349 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B2797793 : Blo 826349 2797793 := bstep (se 2 (by rfl) ⟨1049172, by rfl⟩ : syracuseStep 2797793 = 2098345) B2098345
theorem B13283563 : Blo 826349 13283563 := bstep (se 1 (by rfl) ⟨9962672, by rfl⟩ : syracuseStep 13283563 = 19925345) B19925345
theorem B18364157 : Blo 826349 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B933979 : Blo 826349 933979 := bstep (se 1 (by rfl) ⟨700484, by rfl⟩ : syracuseStep 933979 = 1400969) B1400969
theorem B3983195 : Blo 826349 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B5032529 : Blo 826349 5032529 := bstep (se 2 (by rfl) ⟨1887198, by rfl⟩ : syracuseStep 5032529 = 3774397) B3774397
theorem B2149715 : Blo 826349 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B120769967 : Blo 826349 120769967 := bstep (se 1 (by rfl) ⟨90577475, by rfl⟩ : syracuseStep 120769967 = 181154951) B181154951
theorem B1396271 : Blo 826349 1396271 := bstep (se 1 (by rfl) ⟨1047203, by rfl⟩ : syracuseStep 1396271 = 2094407) B2094407
theorem B5984999 : Blo 826349 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B11916827 : Blo 826349 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B1860137 : Blo 826349 1860137 := bstep (se 2 (by rfl) ⟨697551, by rfl⟩ : syracuseStep 1860137 = 1395103) B1395103
theorem B4188185 : Blo 826349 4188185 := bstep (se 2 (by rfl) ⟨1570569, by rfl⟩ : syracuseStep 4188185 = 3141139) B3141139
theorem B1862009 : Blo 826349 1862009 := bstep (se 2 (by rfl) ⟨698253, by rfl⟩ : syracuseStep 1862009 = 1396507) B1396507
theorem B10054631 : Blo 826349 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B1862783 : Blo 826349 1862783 := bstep (se 1 (by rfl) ⟨1397087, by rfl⟩ : syracuseStep 1862783 = 2794175) B2794175
theorem B1863863 : Blo 826349 1863863 := bstep (se 1 (by rfl) ⟨1397897, by rfl⟩ : syracuseStep 1863863 = 2795795) B2795795
theorem B23851421 : Blo 826349 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B2093759 : Blo 826349 2093759 := bstep (se 1 (by rfl) ⟨1570319, by rfl⟩ : syracuseStep 2093759 = 3140639) B3140639
theorem B114782953 : Blo 826349 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B96695147 : Blo 826349 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B1865087 : Blo 826349 1865087 := bstep (se 1 (by rfl) ⟨1398815, by rfl⟩ : syracuseStep 1865087 = 2797631) B2797631
theorem B1865321 : Blo 826349 1865321 := bstep (se 2 (by rfl) ⟨699495, by rfl⟩ : syracuseStep 1865321 = 1398991) B1398991
theorem B552008915 : Blo 826349 552008915 := bstep (se 1 (by rfl) ⟨414006686, by rfl⟩ : syracuseStep 552008915 = 828013373) B828013373
theorem B1245305 : Blo 826349 1245305 := bstep (se 2 (by rfl) ⟨466989, by rfl⟩ : syracuseStep 1245305 = 933979) B933979
theorem B2655463 : Blo 826349 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B2361383 : Blo 826349 2361383 := bstep (se 1 (by rfl) ⟨1771037, by rfl⟩ : syracuseStep 2361383 = 3542075) B3542075
theorem B257853725 : Blo 826349 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B80513311 : Blo 826349 80513311 := bstep (se 1 (by rfl) ⟨60384983, by rfl⟩ : syracuseStep 80513311 = 120769967) B120769967
theorem B2792123 : Blo 826349 2792123 := bstep (se 1 (by rfl) ⟨2094092, by rfl⟩ : syracuseStep 2792123 = 4188185) B4188185
theorem B6298559 : Blo 826349 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B181477259 : Blo 826349 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B15900947 : Blo 826349 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B3355019 : Blo 826349 3355019 := bstep (se 1 (by rfl) ⟨2516264, by rfl⟩ : syracuseStep 3355019 = 5032529) B5032529
theorem B930847 : Blo 826349 930847 := bstep (se 1 (by rfl) ⟨698135, by rfl⟩ : syracuseStep 930847 = 1396271) B1396271
theorem B7944551 : Blo 826349 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B17711417 : Blo 826349 17711417 := bstep (se 2 (by rfl) ⟨6641781, by rfl⟩ : syracuseStep 17711417 = 13283563) B13283563
theorem B153043937 : Blo 826349 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B6703087 : Blo 826349 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B1395839 : Blo 826349 1395839 := bstep (se 1 (by rfl) ⟨1046879, by rfl⟩ : syracuseStep 1395839 = 2093759) B2093759
theorem B12242771 : Blo 826349 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B368005943 : Blo 826349 368005943 := bstep (se 1 (by rfl) ⟨276004457, by rfl⟩ : syracuseStep 368005943 = 552008915) B552008915
theorem B1398431 : Blo 826349 1398431 := bstep (se 1 (by rfl) ⟨1048823, by rfl⟩ : syracuseStep 1398431 = 2097647) B2097647
theorem B1433143 : Blo 826349 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B1860011 : Blo 826349 1860011 := bstep (se 1 (by rfl) ⟨1395008, by rfl⟩ : syracuseStep 1860011 = 2790017) B2790017
theorem B3989999 : Blo 826349 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B1240091 : Blo 826349 1240091 := bstep (se 1 (by rfl) ⟨930068, by rfl⟩ : syracuseStep 1240091 = 1860137) B1860137
theorem B1241339 : Blo 826349 1241339 := bstep (se 1 (by rfl) ⟨931004, by rfl⟩ : syracuseStep 1241339 = 1862009) B1862009
theorem B1241855 : Blo 826349 1241855 := bstep (se 1 (by rfl) ⟨931391, by rfl⟩ : syracuseStep 1241855 = 1862783) B1862783
theorem B1242575 : Blo 826349 1242575 := bstep (se 1 (by rfl) ⟨931931, by rfl⟩ : syracuseStep 1242575 = 1863863) B1863863
theorem B1865195 : Blo 826349 1865195 := bstep (se 1 (by rfl) ⟨1398896, by rfl⟩ : syracuseStep 1865195 = 2797793) B2797793
theorem B1243391 : Blo 826349 1243391 := bstep (se 1 (by rfl) ⟨932543, by rfl⟩ : syracuseStep 1243391 = 1865087) B1865087
theorem B1243547 : Blo 826349 1243547 := bstep (se 1 (by rfl) ⟨932660, by rfl⟩ : syracuseStep 1243547 = 1865321) B1865321
theorem B1574255 : Blo 826349 1574255 := bstep (se 1 (by rfl) ⟨1180691, by rfl⟩ : syracuseStep 1574255 = 2361383) B2361383
theorem B171902483 : Blo 826349 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B3540617 : Blo 826349 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B8161847 : Blo 826349 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B107351081 : Blo 826349 107351081 := bstep (se 2 (by rfl) ⟨40256655, by rfl⟩ : syracuseStep 107351081 = 80513311) B80513311
theorem B245337295 : Blo 826349 245337295 := bstep (se 1 (by rfl) ⟨184002971, by rfl⟩ : syracuseStep 245337295 = 368005943) B368005943
theorem B4199039 : Blo 826349 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B120984839 : Blo 826349 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B826727 : Blo 826349 826727 := bstep (se 1 (by rfl) ⟨620045, by rfl⟩ : syracuseStep 826727 = 1240091) B1240091
theorem B827559 : Blo 826349 827559 := bstep (se 1 (by rfl) ⟨620669, by rfl⟩ : syracuseStep 827559 = 1241339) B1241339
theorem B2236679 : Blo 826349 2236679 := bstep (se 1 (by rfl) ⟨1677509, by rfl⟩ : syracuseStep 2236679 = 3355019) B3355019
theorem B7643429 : Blo 826349 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B827903 : Blo 826349 827903 := bstep (se 1 (by rfl) ⟨620927, by rfl⟩ : syracuseStep 827903 = 1241855) B1241855
theorem B828383 : Blo 826349 828383 := bstep (se 1 (by rfl) ⟨621287, by rfl⟩ : syracuseStep 828383 = 1242575) B1242575
theorem B828927 : Blo 826349 828927 := bstep (se 1 (by rfl) ⟨621695, by rfl⟩ : syracuseStep 828927 = 1243391) B1243391
theorem B829031 : Blo 826349 829031 := bstep (se 1 (by rfl) ⟨621773, by rfl⟩ : syracuseStep 829031 = 1243547) B1243547
theorem B830203 : Blo 826349 830203 := bstep (se 1 (by rfl) ⟨622652, by rfl⟩ : syracuseStep 830203 = 1245305) B1245305
theorem B47230445 : Blo 826349 47230445 := bstep (se 3 (by rfl) ⟨8855708, by rfl⟩ : syracuseStep 47230445 = 17711417) B17711417
theorem B930559 : Blo 826349 930559 := bstep (se 1 (by rfl) ⟨697919, by rfl⟩ : syracuseStep 930559 = 1395839) B1395839
theorem B932287 : Blo 826349 932287 := bstep (se 1 (by rfl) ⟨699215, by rfl⟩ : syracuseStep 932287 = 1398431) B1398431
theorem B10600631 : Blo 826349 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B5296367 : Blo 826349 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B102029291 : Blo 826349 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B10639997 : Blo 826349 10639997 := bstep (se 3 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 10639997 = 3989999) B3989999
theorem B8937449 : Blo 826349 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B1861415 : Blo 826349 1861415 := bstep (se 1 (by rfl) ⟨1396061, by rfl⟩ : syracuseStep 1861415 = 2792123) B2792123
theorem B1240007 : Blo 826349 1240007 := bstep (se 1 (by rfl) ⟨930005, by rfl⟩ : syracuseStep 1240007 = 1860011) B1860011
theorem B1241129 : Blo 826349 1241129 := bstep (se 2 (by rfl) ⟨465423, by rfl⟩ : syracuseStep 1241129 = 930847) B930847
theorem B1243463 : Blo 826349 1243463 := bstep (se 1 (by rfl) ⟨932597, by rfl⟩ : syracuseStep 1243463 = 1865195) B1865195
theorem B14123645 : Blo 826349 14123645 := bstep (se 3 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 14123645 = 5296367) B5296367
theorem B1049503 : Blo 826349 1049503 := bstep (se 1 (by rfl) ⟨787127, by rfl⟩ : syracuseStep 1049503 = 1574255) B1574255
theorem B2360411 : Blo 826349 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B5441231 : Blo 826349 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B71567387 : Blo 826349 71567387 := bstep (se 1 (by rfl) ⟨53675540, by rfl⟩ : syracuseStep 71567387 = 107351081) B107351081
theorem B826671 : Blo 826349 826671 := bstep (se 1 (by rfl) ⟨620003, by rfl⟩ : syracuseStep 826671 = 1240007) B1240007
theorem B827419 : Blo 826349 827419 := bstep (se 1 (by rfl) ⟨620564, by rfl⟩ : syracuseStep 827419 = 1241129) B1241129
theorem B828975 : Blo 826349 828975 := bstep (se 1 (by rfl) ⟨621731, by rfl⟩ : syracuseStep 828975 = 1243463) B1243463
theorem B114601655 : Blo 826349 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B2799359 : Blo 826349 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B80656559 : Blo 826349 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B7093331 : Blo 826349 7093331 := bstep (se 1 (by rfl) ⟨5319998, by rfl⟩ : syracuseStep 7093331 = 10639997) B10639997
theorem B1491119 : Blo 826349 1491119 := bstep (se 1 (by rfl) ⟨1118339, by rfl⟩ : syracuseStep 1491119 = 2236679) B2236679
theorem B5095619 : Blo 826349 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B7067087 : Blo 826349 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B68019527 : Blo 826349 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B327116393 : Blo 826349 327116393 := bstep (se 2 (by rfl) ⟨122668647, by rfl⟩ : syracuseStep 327116393 = 245337295) B245337295
theorem B5958299 : Blo 826349 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B1240745 : Blo 826349 1240745 := bstep (se 2 (by rfl) ⟨465279, by rfl⟩ : syracuseStep 1240745 = 930559) B930559
theorem B1240943 : Blo 826349 1240943 := bstep (se 1 (by rfl) ⟨930707, by rfl⟩ : syracuseStep 1240943 = 1861415) B1861415
theorem B31486963 : Blo 826349 31486963 := bstep (se 1 (by rfl) ⟨23615222, by rfl⟩ : syracuseStep 31486963 = 47230445) B47230445
theorem B1243049 : Blo 826349 1243049 := bstep (se 2 (by rfl) ⟨466143, by rfl⟩ : syracuseStep 1243049 = 932287) B932287
theorem B1573607 : Blo 826349 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B47711591 : Blo 826349 47711591 := bstep (se 1 (by rfl) ⟨35783693, by rfl⟩ : syracuseStep 47711591 = 71567387) B71567387
theorem B218077595 : Blo 826349 218077595 := bstep (se 1 (by rfl) ⟨163558196, by rfl⟩ : syracuseStep 218077595 = 327116393) B327116393
theorem B41982617 : Blo 826349 41982617 := bstep (se 2 (by rfl) ⟨15743481, by rfl⟩ : syracuseStep 41982617 = 31486963) B31486963
theorem B827163 : Blo 826349 827163 := bstep (se 1 (by rfl) ⟨620372, by rfl⟩ : syracuseStep 827163 = 1240745) B1240745
theorem B827295 : Blo 826349 827295 := bstep (se 1 (by rfl) ⟨620471, by rfl⟩ : syracuseStep 827295 = 1240943) B1240943
theorem B828699 : Blo 826349 828699 := bstep (se 1 (by rfl) ⟨621524, by rfl⟩ : syracuseStep 828699 = 1243049) B1243049
theorem B4728887 : Blo 826349 4728887 := bstep (se 1 (by rfl) ⟨3546665, by rfl⟩ : syracuseStep 4728887 = 7093331) B7093331
theorem B994079 : Blo 826349 994079 := bstep (se 1 (by rfl) ⟨745559, by rfl⟩ : syracuseStep 994079 = 1491119) B1491119
theorem B9415763 : Blo 826349 9415763 := bstep (se 1 (by rfl) ⟨7061822, by rfl⟩ : syracuseStep 9415763 = 14123645) B14123645
theorem B76401103 : Blo 826349 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B3397079 : Blo 826349 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B3627487 : Blo 826349 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B1399337 : Blo 826349 1399337 := bstep (se 2 (by rfl) ⟨524751, by rfl⟩ : syracuseStep 1399337 = 1049503) B1049503
theorem B4711391 : Blo 826349 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B45346351 : Blo 826349 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B15888797 : Blo 826349 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B1866239 : Blo 826349 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B53771039 : Blo 826349 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B4196285 : Blo 826349 4196285 := bstep (se 3 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 4196285 = 1573607) B1573607
theorem B2264719 : Blo 826349 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B27988411 : Blo 826349 27988411 := bstep (se 1 (by rfl) ⟨20991308, by rfl⟩ : syracuseStep 27988411 = 41982617) B41982617
theorem B60461801 : Blo 826349 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B3152591 : Blo 826349 3152591 := bstep (se 1 (by rfl) ⟨2364443, by rfl⟩ : syracuseStep 3152591 = 4728887) B4728887
theorem B10592531 : Blo 826349 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B19346597 : Blo 826349 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B932891 : Blo 826349 932891 := bstep (se 1 (by rfl) ⟨699668, by rfl⟩ : syracuseStep 932891 = 1399337) B1399337
theorem B6277175 : Blo 826349 6277175 := bstep (se 1 (by rfl) ⟨4707881, by rfl⟩ : syracuseStep 6277175 = 9415763) B9415763
theorem B31807727 : Blo 826349 31807727 := bstep (se 1 (by rfl) ⟨23855795, by rfl⟩ : syracuseStep 31807727 = 47711591) B47711591
theorem B101868137 : Blo 826349 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B145385063 : Blo 826349 145385063 := bstep (se 1 (by rfl) ⟨109038797, by rfl⟩ : syracuseStep 145385063 = 218077595) B218077595
theorem B3140927 : Blo 826349 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B2650877 : Blo 826349 2650877 := bstep (se 3 (by rfl) ⟨497039, by rfl⟩ : syracuseStep 2650877 = 994079) B994079
theorem B1244159 : Blo 826349 1244159 := bstep (se 1 (by rfl) ⟨933119, by rfl⟩ : syracuseStep 1244159 = 1866239) B1866239
theorem B35847359 : Blo 826349 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B40307867 : Blo 826349 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B21205151 : Blo 826349 21205151 := bstep (se 1 (by rfl) ⟨15903863, by rfl⟩ : syracuseStep 21205151 = 31807727) B31807727
theorem B2101727 : Blo 826349 2101727 := bstep (se 1 (by rfl) ⟨1576295, by rfl⟩ : syracuseStep 2101727 = 3152591) B3152591
theorem B3019625 : Blo 826349 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B829439 : Blo 826349 829439 := bstep (se 1 (by rfl) ⟨622079, by rfl⟩ : syracuseStep 829439 = 1244159) B1244159
theorem B23898239 : Blo 826349 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B2797523 : Blo 826349 2797523 := bstep (se 1 (by rfl) ⟨2098142, by rfl⟩ : syracuseStep 2797523 = 4196285) B4196285
theorem B7061687 : Blo 826349 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B67912091 : Blo 826349 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B12897731 : Blo 826349 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B4184783 : Blo 826349 4184783 := bstep (se 1 (by rfl) ⟨3138587, by rfl⟩ : syracuseStep 4184783 = 6277175) B6277175
theorem B37317881 : Blo 826349 37317881 := bstep (se 2 (by rfl) ⟨13994205, by rfl⟩ : syracuseStep 37317881 = 27988411) B27988411
theorem B96923375 : Blo 826349 96923375 := bstep (se 1 (by rfl) ⟨72692531, by rfl⟩ : syracuseStep 96923375 = 145385063) B145385063
theorem B2093951 : Blo 826349 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B2487709 : Blo 826349 2487709 := bstep (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) B932891
theorem B1767251 : Blo 826349 1767251 := bstep (se 1 (by rfl) ⟨1325438, by rfl⟩ : syracuseStep 1767251 = 2650877) B2650877
theorem B26871911 : Blo 826349 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B2789855 : Blo 826349 2789855 := bstep (se 1 (by rfl) ⟨2092391, by rfl⟩ : syracuseStep 2789855 = 4184783) B4184783
theorem B15932159 : Blo 826349 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B3316945 : Blo 826349 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B24878587 : Blo 826349 24878587 := bstep (se 1 (by rfl) ⟨18658940, by rfl⟩ : syracuseStep 24878587 = 37317881) B37317881
theorem B8598487 : Blo 826349 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B14136767 : Blo 826349 14136767 := bstep (se 1 (by rfl) ⟨10602575, by rfl⟩ : syracuseStep 14136767 = 21205151) B21205151
theorem B2013083 : Blo 826349 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B1395967 : Blo 826349 1395967 := bstep (se 1 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 1395967 = 2093951) B2093951
theorem B4707791 : Blo 826349 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B45274727 : Blo 826349 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B1401151 : Blo 826349 1401151 := bstep (se 1 (by rfl) ⟨1050863, by rfl⟩ : syracuseStep 1401151 = 2101727) B2101727
theorem B64615583 : Blo 826349 64615583 := bstep (se 1 (by rfl) ⟨48461687, by rfl⟩ : syracuseStep 64615583 = 96923375) B96923375
theorem B1865015 : Blo 826349 1865015 := bstep (se 1 (by rfl) ⟨1398761, by rfl⟩ : syracuseStep 1865015 = 2797523) B2797523
theorem B1178167 : Blo 826349 1178167 := bstep (se 1 (by rfl) ⟨883625, by rfl⟩ : syracuseStep 1178167 = 1767251) B1767251
theorem B1868201 : Blo 826349 1868201 := bstep (se 2 (by rfl) ⟨700575, by rfl⟩ : syracuseStep 1868201 = 1401151) B1401151
theorem B10621439 : Blo 826349 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B33171449 : Blo 826349 33171449 := bstep (se 2 (by rfl) ⟨12439293, by rfl⟩ : syracuseStep 33171449 = 24878587) B24878587
theorem B120732605 : Blo 826349 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B43077055 : Blo 826349 43077055 := bstep (se 1 (by rfl) ⟨32307791, by rfl⟩ : syracuseStep 43077055 = 64615583) B64615583
theorem B9424511 : Blo 826349 9424511 := bstep (se 1 (by rfl) ⟨7068383, by rfl⟩ : syracuseStep 9424511 = 14136767) B14136767
theorem B17914607 : Blo 826349 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B1859903 : Blo 826349 1859903 := bstep (se 1 (by rfl) ⟨1394927, by rfl⟩ : syracuseStep 1859903 = 2789855) B2789855
theorem B3138527 : Blo 826349 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B1861289 : Blo 826349 1861289 := bstep (se 2 (by rfl) ⟨697983, by rfl⟩ : syracuseStep 1861289 = 1395967) B1395967
theorem B11464649 : Blo 826349 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B1570889 : Blo 826349 1570889 := bstep (se 2 (by rfl) ⟨589083, by rfl⟩ : syracuseStep 1570889 = 1178167) B1178167
theorem B1243343 : Blo 826349 1243343 := bstep (se 1 (by rfl) ⟨932507, by rfl⟩ : syracuseStep 1243343 = 1865015) B1865015
theorem B1342055 : Blo 826349 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B4422593 : Blo 826349 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B1245467 : Blo 826349 1245467 := bstep (se 1 (by rfl) ⟨934100, by rfl⟩ : syracuseStep 1245467 = 1868201) B1868201
theorem B7080959 : Blo 826349 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B3578813 : Blo 826349 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B7643099 : Blo 826349 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B828895 : Blo 826349 828895 := bstep (se 1 (by rfl) ⟨621671, by rfl⟩ : syracuseStep 828895 = 1243343) B1243343
theorem B80488403 : Blo 826349 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B11943071 : Blo 826349 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B88457197 : Blo 826349 88457197 := bstep (se 3 (by rfl) ⟨16585724, by rfl⟩ : syracuseStep 88457197 = 33171449) B33171449
theorem B6283007 : Blo 826349 6283007 := bstep (se 1 (by rfl) ⟨4712255, by rfl⟩ : syracuseStep 6283007 = 9424511) B9424511
theorem B57436073 : Blo 826349 57436073 := bstep (se 2 (by rfl) ⟨21538527, by rfl⟩ : syracuseStep 57436073 = 43077055) B43077055
theorem B1239935 : Blo 826349 1239935 := bstep (se 1 (by rfl) ⟨929951, by rfl⟩ : syracuseStep 1239935 = 1859903) B1859903
theorem B2092351 : Blo 826349 2092351 := bstep (se 1 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 2092351 = 3138527) B3138527
theorem B1240859 : Blo 826349 1240859 := bstep (se 1 (by rfl) ⟨930644, by rfl⟩ : syracuseStep 1240859 = 1861289) B1861289
theorem B1047259 : Blo 826349 1047259 := bstep (se 1 (by rfl) ⟨785444, by rfl⟩ : syracuseStep 1047259 = 1570889) B1570889
theorem B2948395 : Blo 826349 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B4720639 : Blo 826349 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B2789801 : Blo 826349 2789801 := bstep (se 2 (by rfl) ⟨1046175, by rfl⟩ : syracuseStep 2789801 = 2092351) B2092351
theorem B826623 : Blo 826349 826623 := bstep (se 1 (by rfl) ⟨619967, by rfl⟩ : syracuseStep 826623 = 1239935) B1239935
theorem B827239 : Blo 826349 827239 := bstep (se 1 (by rfl) ⟨620429, by rfl⟩ : syracuseStep 827239 = 1240859) B1240859
theorem B117942929 : Blo 826349 117942929 := bstep (se 2 (by rfl) ⟨44228598, by rfl⟩ : syracuseStep 117942929 = 88457197) B88457197
theorem B830311 : Blo 826349 830311 := bstep (se 1 (by rfl) ⟨622733, by rfl⟩ : syracuseStep 830311 = 1245467) B1245467
theorem B5095399 : Blo 826349 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B38290715 : Blo 826349 38290715 := bstep (se 1 (by rfl) ⟨28718036, by rfl⟩ : syracuseStep 38290715 = 57436073) B57436073
theorem B53658935 : Blo 826349 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B1396345 : Blo 826349 1396345 := bstep (se 2 (by rfl) ⟨523629, by rfl⟩ : syracuseStep 1396345 = 1047259) B1047259
theorem B2385875 : Blo 826349 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B4188671 : Blo 826349 4188671 := bstep (se 1 (by rfl) ⟨3141503, by rfl⟩ : syracuseStep 4188671 = 6283007) B6283007
theorem B3931193 : Blo 826349 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B7962047 : Blo 826349 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B25527143 : Blo 826349 25527143 := bstep (se 1 (by rfl) ⟨19145357, by rfl⟩ : syracuseStep 25527143 = 38290715) B38290715
theorem B6294185 : Blo 826349 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B6362333 : Blo 826349 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B2792447 : Blo 826349 2792447 := bstep (se 1 (by rfl) ⟨2094335, by rfl⟩ : syracuseStep 2792447 = 4188671) B4188671
theorem B6793865 : Blo 826349 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B78628619 : Blo 826349 78628619 := bstep (se 1 (by rfl) ⟨58971464, by rfl⟩ : syracuseStep 78628619 = 117942929) B117942929
theorem B35772623 : Blo 826349 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B1859867 : Blo 826349 1859867 := bstep (se 1 (by rfl) ⟨1394900, by rfl⟩ : syracuseStep 1859867 = 2789801) B2789801
theorem B1861793 : Blo 826349 1861793 := bstep (se 2 (by rfl) ⟨698172, by rfl⟩ : syracuseStep 1861793 = 1396345) B1396345
theorem B10483181 : Blo 826349 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B5308031 : Blo 826349 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B4196123 : Blo 826349 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B4529243 : Blo 826349 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B6988787 : Blo 826349 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B17018095 : Blo 826349 17018095 := bstep (se 1 (by rfl) ⟨12763571, by rfl⟩ : syracuseStep 17018095 = 25527143) B25527143
theorem B4241555 : Blo 826349 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B52419079 : Blo 826349 52419079 := bstep (se 1 (by rfl) ⟨39314309, by rfl⟩ : syracuseStep 52419079 = 78628619) B78628619
theorem B23848415 : Blo 826349 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B1861631 : Blo 826349 1861631 := bstep (se 1 (by rfl) ⟨1396223, by rfl⟩ : syracuseStep 1861631 = 2792447) B2792447
theorem B1239911 : Blo 826349 1239911 := bstep (se 1 (by rfl) ⟨929933, by rfl⟩ : syracuseStep 1239911 = 1859867) B1859867
theorem B1241195 : Blo 826349 1241195 := bstep (se 1 (by rfl) ⟨930896, by rfl⟩ : syracuseStep 1241195 = 1861793) B1861793
theorem B3538687 : Blo 826349 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B4659191 : Blo 826349 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B15898943 : Blo 826349 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B826607 : Blo 826349 826607 := bstep (se 1 (by rfl) ⟨619955, by rfl⟩ : syracuseStep 826607 = 1239911) B1239911
theorem B827463 : Blo 826349 827463 := bstep (se 1 (by rfl) ⟨620597, by rfl⟩ : syracuseStep 827463 = 1241195) B1241195
theorem B2827703 : Blo 826349 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B2797415 : Blo 826349 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B22690793 : Blo 826349 22690793 := bstep (se 2 (by rfl) ⟨8509047, by rfl⟩ : syracuseStep 22690793 = 17018095) B17018095
theorem B12077981 : Blo 826349 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B1241087 : Blo 826349 1241087 := bstep (se 1 (by rfl) ⟨930815, by rfl⟩ : syracuseStep 1241087 = 1861631) B1861631
theorem B69892105 : Blo 826349 69892105 := bstep (se 2 (by rfl) ⟨26209539, by rfl⟩ : syracuseStep 69892105 = 52419079) B52419079
theorem B4718249 : Blo 826349 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B827391 : Blo 826349 827391 := bstep (se 1 (by rfl) ⟨620543, by rfl⟩ : syracuseStep 827391 = 1241087) B1241087
theorem B10599295 : Blo 826349 10599295 := bstep (se 1 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 10599295 = 15898943) B15898943
theorem B1885135 : Blo 826349 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B15127195 : Blo 826349 15127195 := bstep (se 1 (by rfl) ⟨11345396, by rfl⟩ : syracuseStep 15127195 = 22690793) B22690793
theorem B8051987 : Blo 826349 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B3106127 : Blo 826349 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B1864943 : Blo 826349 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B93189473 : Blo 826349 93189473 := bstep (se 2 (by rfl) ⟨34946052, by rfl⟩ : syracuseStep 93189473 = 69892105) B69892105
theorem B3145499 : Blo 826349 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B14132393 : Blo 826349 14132393 := bstep (se 2 (by rfl) ⟨5299647, by rfl⟩ : syracuseStep 14132393 = 10599295) B10599295
theorem B20169593 : Blo 826349 20169593 := bstep (se 2 (by rfl) ⟨7563597, by rfl⟩ : syracuseStep 20169593 = 15127195) B15127195
theorem B2513513 : Blo 826349 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B8283005 : Blo 826349 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B5367991 : Blo 826349 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B1243295 : Blo 826349 1243295 := bstep (se 1 (by rfl) ⟨932471, by rfl⟩ : syracuseStep 1243295 = 1864943) B1864943
theorem B62126315 : Blo 826349 62126315 := bstep (se 1 (by rfl) ⟨46594736, by rfl⟩ : syracuseStep 62126315 = 93189473) B93189473
theorem B2096999 : Blo 826349 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B1675675 : Blo 826349 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B828863 : Blo 826349 828863 := bstep (se 1 (by rfl) ⟨621647, by rfl⟩ : syracuseStep 828863 = 1243295) B1243295
theorem B13446395 : Blo 826349 13446395 := bstep (se 1 (by rfl) ⟨10084796, by rfl⟩ : syracuseStep 13446395 = 20169593) B20169593
theorem B7157321 : Blo 826349 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B5522003 : Blo 826349 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B9421595 : Blo 826349 9421595 := bstep (se 1 (by rfl) ⟨7066196, by rfl⟩ : syracuseStep 9421595 = 14132393) B14132393
theorem B1397999 : Blo 826349 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B41417543 : Blo 826349 41417543 := bstep (se 1 (by rfl) ⟨31063157, by rfl⟩ : syracuseStep 41417543 = 62126315) B62126315
theorem B2234233 : Blo 826349 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B3681335 : Blo 826349 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B931999 : Blo 826349 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B8964263 : Blo 826349 8964263 := bstep (se 1 (by rfl) ⟨6723197, by rfl⟩ : syracuseStep 8964263 = 13446395) B13446395
theorem B4771547 : Blo 826349 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B27611695 : Blo 826349 27611695 := bstep (se 1 (by rfl) ⟨20708771, by rfl⟩ : syracuseStep 27611695 = 41417543) B41417543
theorem B6281063 : Blo 826349 6281063 := bstep (se 1 (by rfl) ⟨4710797, by rfl⟩ : syracuseStep 6281063 = 9421595) B9421595
theorem B3181031 : Blo 826349 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B5976175 : Blo 826349 5976175 := bstep (se 1 (by rfl) ⟨4482131, by rfl⟩ : syracuseStep 5976175 = 8964263) B8964263
theorem B36815593 : Blo 826349 36815593 := bstep (se 2 (by rfl) ⟨13805847, by rfl⟩ : syracuseStep 36815593 = 27611695) B27611695
theorem B4187375 : Blo 826349 4187375 := bstep (se 1 (by rfl) ⟨3140531, by rfl⟩ : syracuseStep 4187375 = 6281063) B6281063
theorem B2454223 : Blo 826349 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B2978977 : Blo 826349 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B1242665 : Blo 826349 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B49087457 : Blo 826349 49087457 := bstep (se 2 (by rfl) ⟨18407796, by rfl⟩ : syracuseStep 49087457 = 36815593) B36815593
theorem B7968233 : Blo 826349 7968233 := bstep (se 2 (by rfl) ⟨2988087, by rfl⟩ : syracuseStep 7968233 = 5976175) B5976175
theorem B2791583 : Blo 826349 2791583 := bstep (se 1 (by rfl) ⟨2093687, by rfl⟩ : syracuseStep 2791583 = 4187375) B4187375
theorem B3971969 : Blo 826349 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B828443 : Blo 826349 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B2120687 : Blo 826349 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B3272297 : Blo 826349 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B5312155 : Blo 826349 5312155 := bstep (se 1 (by rfl) ⟨3984116, by rfl⟩ : syracuseStep 5312155 = 7968233) B7968233
theorem B1413791 : Blo 826349 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B8726125 : Blo 826349 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B32724971 : Blo 826349 32724971 := bstep (se 1 (by rfl) ⟨24543728, by rfl⟩ : syracuseStep 32724971 = 49087457) B49087457
theorem B1861055 : Blo 826349 1861055 := bstep (se 1 (by rfl) ⟨1395791, by rfl⟩ : syracuseStep 1861055 = 2791583) B2791583
theorem B2647979 : Blo 826349 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B11634833 : Blo 826349 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B7082873 : Blo 826349 7082873 := bstep (se 2 (by rfl) ⟨2656077, by rfl⟩ : syracuseStep 7082873 = 5312155) B5312155
theorem B942527 : Blo 826349 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B21816647 : Blo 826349 21816647 := bstep (se 1 (by rfl) ⟨16362485, by rfl⟩ : syracuseStep 21816647 = 32724971) B32724971
theorem B1240703 : Blo 826349 1240703 := bstep (se 1 (by rfl) ⟨930527, by rfl⟩ : syracuseStep 1240703 = 1861055) B1861055
theorem B1765319 : Blo 826349 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B4721915 : Blo 826349 4721915 := bstep (se 1 (by rfl) ⟨3541436, by rfl⟩ : syracuseStep 4721915 = 7082873) B7082873
theorem B827135 : Blo 826349 827135 := bstep (se 1 (by rfl) ⟨620351, by rfl⟩ : syracuseStep 827135 = 1240703) B1240703
theorem B4707517 : Blo 826349 4707517 := bstep (se 3 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 4707517 = 1765319) B1765319
theorem B2513405 : Blo 826349 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B7756555 : Blo 826349 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B14544431 : Blo 826349 14544431 := bstep (se 1 (by rfl) ⟨10908323, by rfl⟩ : syracuseStep 14544431 = 21816647) B21816647
theorem B3147943 : Blo 826349 3147943 := bstep (se 1 (by rfl) ⟨2360957, by rfl⟩ : syracuseStep 3147943 = 4721915) B4721915
theorem B1675603 : Blo 826349 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B6276689 : Blo 826349 6276689 := bstep (se 2 (by rfl) ⟨2353758, by rfl⟩ : syracuseStep 6276689 = 4707517) B4707517
theorem B10342073 : Blo 826349 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B9696287 : Blo 826349 9696287 := bstep (se 1 (by rfl) ⟨7272215, by rfl⟩ : syracuseStep 9696287 = 14544431) B14544431
theorem B25856765 : Blo 826349 25856765 := bstep (se 3 (by rfl) ⟨4848143, by rfl⟩ : syracuseStep 25856765 = 9696287) B9696287
theorem B4197257 : Blo 826349 4197257 := bstep (se 2 (by rfl) ⟨1573971, by rfl⟩ : syracuseStep 4197257 = 3147943) B3147943
theorem B2234137 : Blo 826349 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B6894715 : Blo 826349 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B4184459 : Blo 826349 4184459 := bstep (se 1 (by rfl) ⟨3138344, by rfl⟩ : syracuseStep 4184459 = 6276689) B6276689
theorem B17237843 : Blo 826349 17237843 := bstep (se 1 (by rfl) ⟨12928382, by rfl⟩ : syracuseStep 17237843 = 25856765) B25856765
theorem B2789639 : Blo 826349 2789639 := bstep (se 1 (by rfl) ⟨2092229, by rfl⟩ : syracuseStep 2789639 = 4184459) B4184459
theorem B2798171 : Blo 826349 2798171 := bstep (se 1 (by rfl) ⟨2098628, by rfl⟩ : syracuseStep 2798171 = 4197257) B4197257
theorem B9192953 : Blo 826349 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B2978849 : Blo 826349 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B6128635 : Blo 826349 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B1985899 : Blo 826349 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B11491895 : Blo 826349 11491895 := bstep (se 1 (by rfl) ⟨8618921, by rfl⟩ : syracuseStep 11491895 = 17237843) B17237843
theorem B1859759 : Blo 826349 1859759 := bstep (se 1 (by rfl) ⟨1394819, by rfl⟩ : syracuseStep 1859759 = 2789639) B2789639
theorem B1865447 : Blo 826349 1865447 := bstep (se 1 (by rfl) ⟨1399085, by rfl⟩ : syracuseStep 1865447 = 2798171) B2798171
theorem B8171513 : Blo 826349 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B7661263 : Blo 826349 7661263 := bstep (se 1 (by rfl) ⟨5745947, by rfl⟩ : syracuseStep 7661263 = 11491895) B11491895
theorem B2647865 : Blo 826349 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B1239839 : Blo 826349 1239839 := bstep (se 1 (by rfl) ⟨929879, by rfl⟩ : syracuseStep 1239839 = 1859759) B1859759
theorem B1243631 : Blo 826349 1243631 := bstep (se 1 (by rfl) ⟨932723, by rfl⟩ : syracuseStep 1243631 = 1865447) B1865447
theorem B826559 : Blo 826349 826559 := bstep (se 1 (by rfl) ⟨619919, by rfl⟩ : syracuseStep 826559 = 1239839) B1239839
theorem B5447675 : Blo 826349 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B829087 : Blo 826349 829087 := bstep (se 1 (by rfl) ⟨621815, by rfl⟩ : syracuseStep 829087 = 1243631) B1243631
theorem B10215017 : Blo 826349 10215017 := bstep (se 2 (by rfl) ⟨3830631, by rfl⟩ : syracuseStep 10215017 = 7661263) B7661263
theorem B1765243 : Blo 826349 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B14527133 : Blo 826349 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B6810011 : Blo 826349 6810011 := bstep (se 1 (by rfl) ⟨5107508, by rfl⟩ : syracuseStep 6810011 = 10215017) B10215017
theorem B2353657 : Blo 826349 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B4540007 : Blo 826349 4540007 := bstep (se 1 (by rfl) ⟨3405005, by rfl⟩ : syracuseStep 4540007 = 6810011) B6810011
theorem B9684755 : Blo 826349 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B3138209 : Blo 826349 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B6456503 : Blo 826349 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B12106685 : Blo 826349 12106685 := bstep (se 3 (by rfl) ⟨2270003, by rfl⟩ : syracuseStep 12106685 = 4540007) B4540007
theorem B2092139 : Blo 826349 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B8071123 : Blo 826349 8071123 := bstep (se 1 (by rfl) ⟨6053342, by rfl⟩ : syracuseStep 8071123 = 12106685) B12106685
theorem B4304335 : Blo 826349 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B1394759 : Blo 826349 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B5739113 : Blo 826349 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B929839 : Blo 826349 929839 := bstep (se 1 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 929839 = 1394759) B1394759
theorem B10761497 : Blo 826349 10761497 := bstep (se 2 (by rfl) ⟨4035561, by rfl⟩ : syracuseStep 10761497 = 8071123) B8071123
theorem B3826075 : Blo 826349 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B1239785 : Blo 826349 1239785 := bstep (se 2 (by rfl) ⟨464919, by rfl⟩ : syracuseStep 1239785 = 929839) B929839
theorem B7174331 : Blo 826349 7174331 := bstep (se 1 (by rfl) ⟨5380748, by rfl⟩ : syracuseStep 7174331 = 10761497) B10761497
theorem B826523 : Blo 826349 826523 := bstep (se 1 (by rfl) ⟨619892, by rfl⟩ : syracuseStep 826523 = 1239785) B1239785
theorem B5101433 : Blo 826349 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B4782887 : Blo 826349 4782887 := bstep (se 1 (by rfl) ⟨3587165, by rfl⟩ : syracuseStep 4782887 = 7174331) B7174331
theorem B3188591 : Blo 826349 3188591 := bstep (se 1 (by rfl) ⟨2391443, by rfl⟩ : syracuseStep 3188591 = 4782887) B4782887
theorem B3400955 : Blo 826349 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B2267303 : Blo 826349 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B2125727 : Blo 826349 2125727 := bstep (se 1 (by rfl) ⟨1594295, by rfl⟩ : syracuseStep 2125727 = 3188591) B3188591
theorem B24184565 : Blo 826349 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B1417151 : Blo 826349 1417151 := bstep (se 1 (by rfl) ⟨1062863, by rfl⟩ : syracuseStep 1417151 = 2125727) B2125727
theorem B16123043 : Blo 826349 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B944767 : Blo 826349 944767 := bstep (se 1 (by rfl) ⟨708575, by rfl⟩ : syracuseStep 944767 = 1417151) B1417151
theorem B10748695 : Blo 826349 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B5038757 : Blo 826349 5038757 := bstep (se 4 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 5038757 = 944767) B944767
theorem B14331593 : Blo 826349 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B3359171 : Blo 826349 3359171 := bstep (se 1 (by rfl) ⟨2519378, by rfl⟩ : syracuseStep 3359171 = 5038757) B5038757
theorem B2239447 : Blo 826349 2239447 := bstep (se 1 (by rfl) ⟨1679585, by rfl⟩ : syracuseStep 2239447 = 3359171) B3359171
theorem B9554395 : Blo 826349 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B2985929 : Blo 826349 2985929 := bstep (se 2 (by rfl) ⟨1119723, by rfl⟩ : syracuseStep 2985929 = 2239447) B2239447
theorem B12739193 : Blo 826349 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B8492795 : Blo 826349 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B1990619 : Blo 826349 1990619 := bstep (se 1 (by rfl) ⟨1492964, by rfl⟩ : syracuseStep 1990619 = 2985929) B2985929
theorem B1327079 : Blo 826349 1327079 := bstep (se 1 (by rfl) ⟨995309, by rfl⟩ : syracuseStep 1327079 = 1990619) B1990619
theorem B5661863 : Blo 826349 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B3774575 : Blo 826349 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B884719 : Blo 826349 884719 := bstep (se 1 (by rfl) ⟨663539, by rfl⟩ : syracuseStep 884719 = 1327079) B1327079
theorem B2516383 : Blo 826349 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B1179625 : Blo 826349 1179625 := bstep (se 2 (by rfl) ⟨442359, by rfl⟩ : syracuseStep 1179625 = 884719) B884719
theorem B3355177 : Blo 826349 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B1572833 : Blo 826349 1572833 := bstep (se 2 (by rfl) ⟨589812, by rfl⟩ : syracuseStep 1572833 = 1179625) B1179625
theorem B4473569 : Blo 826349 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B1048555 : Blo 826349 1048555 := bstep (se 1 (by rfl) ⟨786416, by rfl⟩ : syracuseStep 1048555 = 1572833) B1572833
theorem B11929517 : Blo 826349 11929517 := bstep (se 3 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 11929517 = 4473569) B4473569
theorem B1398073 : Blo 826349 1398073 := bstep (se 2 (by rfl) ⟨524277, by rfl⟩ : syracuseStep 1398073 = 1048555) B1048555
theorem B7953011 : Blo 826349 7953011 := bstep (se 1 (by rfl) ⟨5964758, by rfl⟩ : syracuseStep 7953011 = 11929517) B11929517
theorem B1864097 : Blo 826349 1864097 := bstep (se 2 (by rfl) ⟨699036, by rfl⟩ : syracuseStep 1864097 = 1398073) B1398073
theorem B5302007 : Blo 826349 5302007 := bstep (se 1 (by rfl) ⟨3976505, by rfl⟩ : syracuseStep 5302007 = 7953011) B7953011
theorem B1242731 : Blo 826349 1242731 := bstep (se 1 (by rfl) ⟨932048, by rfl⟩ : syracuseStep 1242731 = 1864097) B1864097
theorem B828487 : Blo 826349 828487 := bstep (se 1 (by rfl) ⟨621365, by rfl⟩ : syracuseStep 828487 = 1242731) B1242731
theorem B3534671 : Blo 826349 3534671 := bstep (se 1 (by rfl) ⟨2651003, by rfl⟩ : syracuseStep 3534671 = 5302007) B5302007
theorem B2356447 : Blo 826349 2356447 := bstep (se 1 (by rfl) ⟨1767335, by rfl⟩ : syracuseStep 2356447 = 3534671) B3534671
theorem B3141929 : Blo 826349 3141929 := bstep (se 2 (by rfl) ⟨1178223, by rfl⟩ : syracuseStep 3141929 = 2356447) B2356447
theorem B2094619 : Blo 826349 2094619 := bstep (se 1 (by rfl) ⟨1570964, by rfl⟩ : syracuseStep 2094619 = 3141929) B3141929
theorem B2792825 : Blo 826349 2792825 := bstep (se 2 (by rfl) ⟨1047309, by rfl⟩ : syracuseStep 2792825 = 2094619) B2094619
theorem B1861883 : Blo 826349 1861883 := bstep (se 1 (by rfl) ⟨1396412, by rfl⟩ : syracuseStep 1861883 = 2792825) B2792825
theorem B1241255 : Blo 826349 1241255 := bstep (se 1 (by rfl) ⟨930941, by rfl⟩ : syracuseStep 1241255 = 1861883) B1861883
theorem B827503 : Blo 826349 827503 := bstep (se 1 (by rfl) ⟨620627, by rfl⟩ : syracuseStep 827503 = 1241255) B1241255

theorem C0 (j : ℕ) (h1 : 206587 ≤ j) (h2 : j ≤ 207286) : Blo 826349 (4 * j + 3) := by
  interval_cases j
  · exact B826351
  · exact B826355
  · exact B826359
  · exact B826363
  · exact B826367
  · exact B826371
  · exact B826375
  · exact B826379
  · exact B826383
  · exact B826387
  · exact B826391
  · exact B826395
  · exact B826399
  · exact B826403
  · exact B826407
  · exact B826411
  · exact B826415
  · exact B826419
  · exact B826423
  · exact B826427
  · exact B826431
  · exact B826435
  · exact B826439
  · exact B826443
  · exact B826447
  · exact B826451
  · exact B826455
  · exact B826459
  · exact B826463
  · exact B826467
  · exact B826471
  · exact B826475
  · exact B826479
  · exact B826483
  · exact B826487
  · exact B826491
  · exact B826495
  · exact B826499
  · exact B826503
  · exact B826507
  · exact B826511
  · exact B826515
  · exact B826519
  · exact B826523
  · exact B826527
  · exact B826531
  · exact B826535
  · exact B826539
  · exact B826543
  · exact B826547
  · exact B826551
  · exact B826555
  · exact B826559
  · exact B826563
  · exact B826567
  · exact B826571
  · exact B826575
  · exact B826579
  · exact B826583
  · exact B826587
  · exact B826591
  · exact B826595
  · exact B826599
  · exact B826603
  · exact B826607
  · exact B826611
  · exact B826615
  · exact B826619
  · exact B826623
  · exact B826627
  · exact B826631
  · exact B826635
  · exact B826639
  · exact B826643
  · exact B826647
  · exact B826651
  · exact B826655
  · exact B826659
  · exact B826663
  · exact B826667
  · exact B826671
  · exact B826675
  · exact B826679
  · exact B826683
  · exact B826687
  · exact B826691
  · exact B826695
  · exact B826699
  · exact B826703
  · exact B826707
  · exact B826711
  · exact B826715
  · exact B826719
  · exact B826723
  · exact B826727
  · exact B826731
  · exact B826735
  · exact B826739
  · exact B826743
  · exact B826747
  · exact B826751
  · exact B826755
  · exact B826759
  · exact B826763
  · exact B826767
  · exact B826771
  · exact B826775
  · exact B826779
  · exact B826783
  · exact B826787
  · exact B826791
  · exact B826795
  · exact B826799
  · exact B826803
  · exact B826807
  · exact B826811
  · exact B826815
  · exact B826819
  · exact B826823
  · exact B826827
  · exact B826831
  · exact B826835
  · exact B826839
  · exact B826843
  · exact B826847
  · exact B826851
  · exact B826855
  · exact B826859
  · exact B826863
  · exact B826867
  · exact B826871
  · exact B826875
  · exact B826879
  · exact B826883
  · exact B826887
  · exact B826891
  · exact B826895
  · exact B826899
  · exact B826903
  · exact B826907
  · exact B826911
  · exact B826915
  · exact B826919
  · exact B826923
  · exact B826927
  · exact B826931
  · exact B826935
  · exact B826939
  · exact B826943
  · exact B826947
  · exact B826951
  · exact B826955
  · exact B826959
  · exact B826963
  · exact B826967
  · exact B826971
  · exact B826975
  · exact B826979
  · exact B826983
  · exact B826987
  · exact B826991
  · exact B826995
  · exact B826999
  · exact B827003
  · exact B827007
  · exact B827011
  · exact B827015
  · exact B827019
  · exact B827023
  · exact B827027
  · exact B827031
  · exact B827035
  · exact B827039
  · exact B827043
  · exact B827047
  · exact B827051
  · exact B827055
  · exact B827059
  · exact B827063
  · exact B827067
  · exact B827071
  · exact B827075
  · exact B827079
  · exact B827083
  · exact B827087
  · exact B827091
  · exact B827095
  · exact B827099
  · exact B827103
  · exact B827107
  · exact B827111
  · exact B827115
  · exact B827119
  · exact B827123
  · exact B827127
  · exact B827131
  · exact B827135
  · exact B827139
  · exact B827143
  · exact B827147
  · exact B827151
  · exact B827155
  · exact B827159
  · exact B827163
  · exact B827167
  · exact B827171
  · exact B827175
  · exact B827179
  · exact B827183
  · exact B827187
  · exact B827191
  · exact B827195
  · exact B827199
  · exact B827203
  · exact B827207
  · exact B827211
  · exact B827215
  · exact B827219
  · exact B827223
  · exact B827227
  · exact B827231
  · exact B827235
  · exact B827239
  · exact B827243
  · exact B827247
  · exact B827251
  · exact B827255
  · exact B827259
  · exact B827263
  · exact B827267
  · exact B827271
  · exact B827275
  · exact B827279
  · exact B827283
  · exact B827287
  · exact B827291
  · exact B827295
  · exact B827299
  · exact B827303
  · exact B827307
  · exact B827311
  · exact B827315
  · exact B827319
  · exact B827323
  · exact B827327
  · exact B827331
  · exact B827335
  · exact B827339
  · exact B827343
  · exact B827347
  · exact B827351
  · exact B827355
  · exact B827359
  · exact B827363
  · exact B827367
  · exact B827371
  · exact B827375
  · exact B827379
  · exact B827383
  · exact B827387
  · exact B827391
  · exact B827395
  · exact B827399
  · exact B827403
  · exact B827407
  · exact B827411
  · exact B827415
  · exact B827419
  · exact B827423
  · exact B827427
  · exact B827431
  · exact B827435
  · exact B827439
  · exact B827443
  · exact B827447
  · exact B827451
  · exact B827455
  · exact B827459
  · exact B827463
  · exact B827467
  · exact B827471
  · exact B827475
  · exact B827479
  · exact B827483
  · exact B827487
  · exact B827491
  · exact B827495
  · exact B827499
  · exact B827503
  · exact B827507
  · exact B827511
  · exact B827515
  · exact B827519
  · exact B827523
  · exact B827527
  · exact B827531
  · exact B827535
  · exact B827539
  · exact B827543
  · exact B827547
  · exact B827551
  · exact B827555
  · exact B827559
  · exact B827563
  · exact B827567
  · exact B827571
  · exact B827575
  · exact B827579
  · exact B827583
  · exact B827587
  · exact B827591
  · exact B827595
  · exact B827599
  · exact B827603
  · exact B827607
  · exact B827611
  · exact B827615
  · exact B827619
  · exact B827623
  · exact B827627
  · exact B827631
  · exact B827635
  · exact B827639
  · exact B827643
  · exact B827647
  · exact B827651
  · exact B827655
  · exact B827659
  · exact B827663
  · exact B827667
  · exact B827671
  · exact B827675
  · exact B827679
  · exact B827683
  · exact B827687
  · exact B827691
  · exact B827695
  · exact B827699
  · exact B827703
  · exact B827707
  · exact B827711
  · exact B827715
  · exact B827719
  · exact B827723
  · exact B827727
  · exact B827731
  · exact B827735
  · exact B827739
  · exact B827743
  · exact B827747
  · exact B827751
  · exact B827755
  · exact B827759
  · exact B827763
  · exact B827767
  · exact B827771
  · exact B827775
  · exact B827779
  · exact B827783
  · exact B827787
  · exact B827791
  · exact B827795
  · exact B827799
  · exact B827803
  · exact B827807
  · exact B827811
  · exact B827815
  · exact B827819
  · exact B827823
  · exact B827827
  · exact B827831
  · exact B827835
  · exact B827839
  · exact B827843
  · exact B827847
  · exact B827851
  · exact B827855
  · exact B827859
  · exact B827863
  · exact B827867
  · exact B827871
  · exact B827875
  · exact B827879
  · exact B827883
  · exact B827887
  · exact B827891
  · exact B827895
  · exact B827899
  · exact B827903
  · exact B827907
  · exact B827911
  · exact B827915
  · exact B827919
  · exact B827923
  · exact B827927
  · exact B827931
  · exact B827935
  · exact B827939
  · exact B827943
  · exact B827947
  · exact B827951
  · exact B827955
  · exact B827959
  · exact B827963
  · exact B827967
  · exact B827971
  · exact B827975
  · exact B827979
  · exact B827983
  · exact B827987
  · exact B827991
  · exact B827995
  · exact B827999
  · exact B828003
  · exact B828007
  · exact B828011
  · exact B828015
  · exact B828019
  · exact B828023
  · exact B828027
  · exact B828031
  · exact B828035
  · exact B828039
  · exact B828043
  · exact B828047
  · exact B828051
  · exact B828055
  · exact B828059
  · exact B828063
  · exact B828067
  · exact B828071
  · exact B828075
  · exact B828079
  · exact B828083
  · exact B828087
  · exact B828091
  · exact B828095
  · exact B828099
  · exact B828103
  · exact B828107
  · exact B828111
  · exact B828115
  · exact B828119
  · exact B828123
  · exact B828127
  · exact B828131
  · exact B828135
  · exact B828139
  · exact B828143
  · exact B828147
  · exact B828151
  · exact B828155
  · exact B828159
  · exact B828163
  · exact B828167
  · exact B828171
  · exact B828175
  · exact B828179
  · exact B828183
  · exact B828187
  · exact B828191
  · exact B828195
  · exact B828199
  · exact B828203
  · exact B828207
  · exact B828211
  · exact B828215
  · exact B828219
  · exact B828223
  · exact B828227
  · exact B828231
  · exact B828235
  · exact B828239
  · exact B828243
  · exact B828247
  · exact B828251
  · exact B828255
  · exact B828259
  · exact B828263
  · exact B828267
  · exact B828271
  · exact B828275
  · exact B828279
  · exact B828283
  · exact B828287
  · exact B828291
  · exact B828295
  · exact B828299
  · exact B828303
  · exact B828307
  · exact B828311
  · exact B828315
  · exact B828319
  · exact B828323
  · exact B828327
  · exact B828331
  · exact B828335
  · exact B828339
  · exact B828343
  · exact B828347
  · exact B828351
  · exact B828355
  · exact B828359
  · exact B828363
  · exact B828367
  · exact B828371
  · exact B828375
  · exact B828379
  · exact B828383
  · exact B828387
  · exact B828391
  · exact B828395
  · exact B828399
  · exact B828403
  · exact B828407
  · exact B828411
  · exact B828415
  · exact B828419
  · exact B828423
  · exact B828427
  · exact B828431
  · exact B828435
  · exact B828439
  · exact B828443
  · exact B828447
  · exact B828451
  · exact B828455
  · exact B828459
  · exact B828463
  · exact B828467
  · exact B828471
  · exact B828475
  · exact B828479
  · exact B828483
  · exact B828487
  · exact B828491
  · exact B828495
  · exact B828499
  · exact B828503
  · exact B828507
  · exact B828511
  · exact B828515
  · exact B828519
  · exact B828523
  · exact B828527
  · exact B828531
  · exact B828535
  · exact B828539
  · exact B828543
  · exact B828547
  · exact B828551
  · exact B828555
  · exact B828559
  · exact B828563
  · exact B828567
  · exact B828571
  · exact B828575
  · exact B828579
  · exact B828583
  · exact B828587
  · exact B828591
  · exact B828595
  · exact B828599
  · exact B828603
  · exact B828607
  · exact B828611
  · exact B828615
  · exact B828619
  · exact B828623
  · exact B828627
  · exact B828631
  · exact B828635
  · exact B828639
  · exact B828643
  · exact B828647
  · exact B828651
  · exact B828655
  · exact B828659
  · exact B828663
  · exact B828667
  · exact B828671
  · exact B828675
  · exact B828679
  · exact B828683
  · exact B828687
  · exact B828691
  · exact B828695
  · exact B828699
  · exact B828703
  · exact B828707
  · exact B828711
  · exact B828715
  · exact B828719
  · exact B828723
  · exact B828727
  · exact B828731
  · exact B828735
  · exact B828739
  · exact B828743
  · exact B828747
  · exact B828751
  · exact B828755
  · exact B828759
  · exact B828763
  · exact B828767
  · exact B828771
  · exact B828775
  · exact B828779
  · exact B828783
  · exact B828787
  · exact B828791
  · exact B828795
  · exact B828799
  · exact B828803
  · exact B828807
  · exact B828811
  · exact B828815
  · exact B828819
  · exact B828823
  · exact B828827
  · exact B828831
  · exact B828835
  · exact B828839
  · exact B828843
  · exact B828847
  · exact B828851
  · exact B828855
  · exact B828859
  · exact B828863
  · exact B828867
  · exact B828871
  · exact B828875
  · exact B828879
  · exact B828883
  · exact B828887
  · exact B828891
  · exact B828895
  · exact B828899
  · exact B828903
  · exact B828907
  · exact B828911
  · exact B828915
  · exact B828919
  · exact B828923
  · exact B828927
  · exact B828931
  · exact B828935
  · exact B828939
  · exact B828943
  · exact B828947
  · exact B828951
  · exact B828955
  · exact B828959
  · exact B828963
  · exact B828967
  · exact B828971
  · exact B828975
  · exact B828979
  · exact B828983
  · exact B828987
  · exact B828991
  · exact B828995
  · exact B828999
  · exact B829003
  · exact B829007
  · exact B829011
  · exact B829015
  · exact B829019
  · exact B829023
  · exact B829027
  · exact B829031
  · exact B829035
  · exact B829039
  · exact B829043
  · exact B829047
  · exact B829051
  · exact B829055
  · exact B829059
  · exact B829063
  · exact B829067
  · exact B829071
  · exact B829075
  · exact B829079
  · exact B829083
  · exact B829087
  · exact B829091
  · exact B829095
  · exact B829099
  · exact B829103
  · exact B829107
  · exact B829111
  · exact B829115
  · exact B829119
  · exact B829123
  · exact B829127
  · exact B829131
  · exact B829135
  · exact B829139
  · exact B829143
  · exact B829147

theorem C1 (j : ℕ) (h1 : 207287 ≤ j) (h2 : j ≤ 207586) : Blo 826349 (4 * j + 3) := by
  interval_cases j
  · exact B829151
  · exact B829155
  · exact B829159
  · exact B829163
  · exact B829167
  · exact B829171
  · exact B829175
  · exact B829179
  · exact B829183
  · exact B829187
  · exact B829191
  · exact B829195
  · exact B829199
  · exact B829203
  · exact B829207
  · exact B829211
  · exact B829215
  · exact B829219
  · exact B829223
  · exact B829227
  · exact B829231
  · exact B829235
  · exact B829239
  · exact B829243
  · exact B829247
  · exact B829251
  · exact B829255
  · exact B829259
  · exact B829263
  · exact B829267
  · exact B829271
  · exact B829275
  · exact B829279
  · exact B829283
  · exact B829287
  · exact B829291
  · exact B829295
  · exact B829299
  · exact B829303
  · exact B829307
  · exact B829311
  · exact B829315
  · exact B829319
  · exact B829323
  · exact B829327
  · exact B829331
  · exact B829335
  · exact B829339
  · exact B829343
  · exact B829347
  · exact B829351
  · exact B829355
  · exact B829359
  · exact B829363
  · exact B829367
  · exact B829371
  · exact B829375
  · exact B829379
  · exact B829383
  · exact B829387
  · exact B829391
  · exact B829395
  · exact B829399
  · exact B829403
  · exact B829407
  · exact B829411
  · exact B829415
  · exact B829419
  · exact B829423
  · exact B829427
  · exact B829431
  · exact B829435
  · exact B829439
  · exact B829443
  · exact B829447
  · exact B829451
  · exact B829455
  · exact B829459
  · exact B829463
  · exact B829467
  · exact B829471
  · exact B829475
  · exact B829479
  · exact B829483
  · exact B829487
  · exact B829491
  · exact B829495
  · exact B829499
  · exact B829503
  · exact B829507
  · exact B829511
  · exact B829515
  · exact B829519
  · exact B829523
  · exact B829527
  · exact B829531
  · exact B829535
  · exact B829539
  · exact B829543
  · exact B829547
  · exact B829551
  · exact B829555
  · exact B829559
  · exact B829563
  · exact B829567
  · exact B829571
  · exact B829575
  · exact B829579
  · exact B829583
  · exact B829587
  · exact B829591
  · exact B829595
  · exact B829599
  · exact B829603
  · exact B829607
  · exact B829611
  · exact B829615
  · exact B829619
  · exact B829623
  · exact B829627
  · exact B829631
  · exact B829635
  · exact B829639
  · exact B829643
  · exact B829647
  · exact B829651
  · exact B829655
  · exact B829659
  · exact B829663
  · exact B829667
  · exact B829671
  · exact B829675
  · exact B829679
  · exact B829683
  · exact B829687
  · exact B829691
  · exact B829695
  · exact B829699
  · exact B829703
  · exact B829707
  · exact B829711
  · exact B829715
  · exact B829719
  · exact B829723
  · exact B829727
  · exact B829731
  · exact B829735
  · exact B829739
  · exact B829743
  · exact B829747
  · exact B829751
  · exact B829755
  · exact B829759
  · exact B829763
  · exact B829767
  · exact B829771
  · exact B829775
  · exact B829779
  · exact B829783
  · exact B829787
  · exact B829791
  · exact B829795
  · exact B829799
  · exact B829803
  · exact B829807
  · exact B829811
  · exact B829815
  · exact B829819
  · exact B829823
  · exact B829827
  · exact B829831
  · exact B829835
  · exact B829839
  · exact B829843
  · exact B829847
  · exact B829851
  · exact B829855
  · exact B829859
  · exact B829863
  · exact B829867
  · exact B829871
  · exact B829875
  · exact B829879
  · exact B829883
  · exact B829887
  · exact B829891
  · exact B829895
  · exact B829899
  · exact B829903
  · exact B829907
  · exact B829911
  · exact B829915
  · exact B829919
  · exact B829923
  · exact B829927
  · exact B829931
  · exact B829935
  · exact B829939
  · exact B829943
  · exact B829947
  · exact B829951
  · exact B829955
  · exact B829959
  · exact B829963
  · exact B829967
  · exact B829971
  · exact B829975
  · exact B829979
  · exact B829983
  · exact B829987
  · exact B829991
  · exact B829995
  · exact B829999
  · exact B830003
  · exact B830007
  · exact B830011
  · exact B830015
  · exact B830019
  · exact B830023
  · exact B830027
  · exact B830031
  · exact B830035
  · exact B830039
  · exact B830043
  · exact B830047
  · exact B830051
  · exact B830055
  · exact B830059
  · exact B830063
  · exact B830067
  · exact B830071
  · exact B830075
  · exact B830079
  · exact B830083
  · exact B830087
  · exact B830091
  · exact B830095
  · exact B830099
  · exact B830103
  · exact B830107
  · exact B830111
  · exact B830115
  · exact B830119
  · exact B830123
  · exact B830127
  · exact B830131
  · exact B830135
  · exact B830139
  · exact B830143
  · exact B830147
  · exact B830151
  · exact B830155
  · exact B830159
  · exact B830163
  · exact B830167
  · exact B830171
  · exact B830175
  · exact B830179
  · exact B830183
  · exact B830187
  · exact B830191
  · exact B830195
  · exact B830199
  · exact B830203
  · exact B830207
  · exact B830211
  · exact B830215
  · exact B830219
  · exact B830223
  · exact B830227
  · exact B830231
  · exact B830235
  · exact B830239
  · exact B830243
  · exact B830247
  · exact B830251
  · exact B830255
  · exact B830259
  · exact B830263
  · exact B830267
  · exact B830271
  · exact B830275
  · exact B830279
  · exact B830283
  · exact B830287
  · exact B830291
  · exact B830295
  · exact B830299
  · exact B830303
  · exact B830307
  · exact B830311
  · exact B830315
  · exact B830319
  · exact B830323
  · exact B830327
  · exact B830331
  · exact B830335
  · exact B830339
  · exact B830343
  · exact B830347

theorem solution (m : ℕ) (hlo : 826349 ≤ m) (hhi : m ≤ 830349) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 206587 ≤ j := by omega
    have hj2 : j ≤ 207586 := by omega
    have hb : Blo 826349 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 207287 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
