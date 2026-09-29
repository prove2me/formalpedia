-- Prove2me | solution 1 for syracuse_descends_range_622298_626298
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:35.202919+00:00
-- url     : https://prove2.me/submissions/72b56bae-5290-489f-8cea-1c6c412746b0

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


theorem B1409093 : Blo 622298 1409093 := bbase (se 4 (by rfl) ⟨132102, by rfl⟩ : syracuseStep 1409093 = 264205) (by norm_num)
theorem B1441901 : Blo 622298 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B1409165 : Blo 622298 1409165 := bbase (se 3 (by rfl) ⟨264218, by rfl⟩ : syracuseStep 1409165 = 528437) (by norm_num)
theorem B950717 : Blo 622298 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B6095477 : Blo 622298 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B787745 : Blo 622298 787745 := bbase (se 2 (by rfl) ⟨295404, by rfl⟩ : syracuseStep 787745 = 590809) (by norm_num)
theorem B1901909 : Blo 622298 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B787801 : Blo 622298 787801 := bbase (se 2 (by rfl) ⟨295425, by rfl⟩ : syracuseStep 787801 = 590851) (by norm_num)
theorem B951733 : Blo 622298 951733 := bbase (se 5 (by rfl) ⟨44612, by rfl⟩ : syracuseStep 951733 = 89225) (by norm_num)
theorem B787897 : Blo 622298 787897 := bbase (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) (by norm_num)
theorem B1705445 : Blo 622298 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B2033189 : Blo 622298 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B1050205 : Blo 622298 1050205 := bbase (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) (by norm_num)
theorem B788069 : Blo 622298 788069 := bbase (se 4 (by rfl) ⟨73881, by rfl⟩ : syracuseStep 788069 = 147763) (by norm_num)
theorem B788125 : Blo 622298 788125 := bbase (se 3 (by rfl) ⟨147773, by rfl⟩ : syracuseStep 788125 = 295547) (by norm_num)
theorem B1050293 : Blo 622298 1050293 := bbase (se 5 (by rfl) ⟨49232, by rfl⟩ : syracuseStep 1050293 = 98465) (by norm_num)
theorem B1181405 : Blo 622298 1181405 := bbase (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) (by norm_num)
theorem B788221 : Blo 622298 788221 := bbase (se 3 (by rfl) ⟨147791, by rfl⟩ : syracuseStep 788221 = 295583) (by norm_num)
theorem B2000645 : Blo 622298 2000645 := bbase (se 4 (by rfl) ⟨187560, by rfl⟩ : syracuseStep 2000645 = 375121) (by norm_num)
theorem B1050421 : Blo 622298 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B1181557 : Blo 622298 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B6096757 : Blo 622298 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B1050509 : Blo 622298 1050509 := bbase (se 3 (by rfl) ⟨196970, by rfl⟩ : syracuseStep 1050509 = 393941) (by norm_num)
theorem B788393 : Blo 622298 788393 := bbase (se 2 (by rfl) ⟨295647, by rfl⟩ : syracuseStep 788393 = 591295) (by norm_num)
theorem B3213269 : Blo 622298 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B788449 : Blo 622298 788449 := bbase (se 2 (by rfl) ⟨295668, by rfl⟩ : syracuseStep 788449 = 591337) (by norm_num)
theorem B1050637 : Blo 622298 1050637 := bbase (se 3 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 1050637 = 393989) (by norm_num)
theorem B9635861 : Blo 622298 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B788545 : Blo 622298 788545 := bbase (se 2 (by rfl) ⟨295704, by rfl⟩ : syracuseStep 788545 = 591409) (by norm_num)
theorem B1050725 : Blo 622298 1050725 := bbase (se 4 (by rfl) ⟨98505, by rfl⟩ : syracuseStep 1050725 = 197011) (by norm_num)
theorem B1181861 : Blo 622298 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B1050853 : Blo 622298 1050853 := bbase (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) (by norm_num)
theorem B788717 : Blo 622298 788717 := bbase (se 3 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 788717 = 295769) (by norm_num)
theorem B1575197 : Blo 622298 1575197 := bbase (se 3 (by rfl) ⟨295349, by rfl⟩ : syracuseStep 1575197 = 590699) (by norm_num)
theorem B788773 : Blo 622298 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B1050941 : Blo 622298 1050941 := bbase (se 3 (by rfl) ⟨197051, by rfl⟩ : syracuseStep 1050941 = 394103) (by norm_num)
theorem B887125 : Blo 622298 887125 := bbase (se 10 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 887125 = 2599) (by norm_num)
theorem B788869 : Blo 622298 788869 := bbase (se 4 (by rfl) ⟨73956, by rfl⟩ : syracuseStep 788869 = 147913) (by norm_num)
theorem B1051069 : Blo 622298 1051069 := bbase (se 3 (by rfl) ⟨197075, by rfl⟩ : syracuseStep 1051069 = 394151) (by norm_num)
theorem B1575389 : Blo 622298 1575389 := bbase (se 3 (by rfl) ⟨295385, by rfl⟩ : syracuseStep 1575389 = 590771) (by norm_num)
theorem B1051157 : Blo 622298 1051157 := bbase (se 6 (by rfl) ⟨24636, by rfl⟩ : syracuseStep 1051157 = 49273) (by norm_num)
theorem B789041 : Blo 622298 789041 := bbase (se 2 (by rfl) ⟨295890, by rfl⟩ : syracuseStep 789041 = 591781) (by norm_num)
theorem B789097 : Blo 622298 789097 := bbase (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) (by norm_num)
theorem B1051285 : Blo 622298 1051285 := bbase (se 6 (by rfl) ⟨24639, by rfl⟩ : syracuseStep 1051285 = 49279) (by norm_num)
theorem B789193 : Blo 622298 789193 := bbase (se 2 (by rfl) ⟨295947, by rfl⟩ : syracuseStep 789193 = 591895) (by norm_num)
theorem B1051373 : Blo 622298 1051373 := bbase (se 3 (by rfl) ⟨197132, by rfl⟩ : syracuseStep 1051373 = 394265) (by norm_num)
theorem B1575733 : Blo 622298 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B1051501 : Blo 622298 1051501 := bbase (se 3 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 1051501 = 394313) (by norm_num)
theorem B1772405 : Blo 622298 1772405 := bbase (se 5 (by rfl) ⟨83081, by rfl⟩ : syracuseStep 1772405 = 166163) (by norm_num)
theorem B789365 : Blo 622298 789365 := bbase (se 5 (by rfl) ⟨37001, by rfl⟩ : syracuseStep 789365 = 74003) (by norm_num)
theorem B1182613 : Blo 622298 1182613 := bbase (se 6 (by rfl) ⟨27717, by rfl⟩ : syracuseStep 1182613 = 55435) (by norm_num)
theorem B1575845 : Blo 622298 1575845 := bbase (se 4 (by rfl) ⟨147735, by rfl⟩ : syracuseStep 1575845 = 295471) (by norm_num)
theorem B887717 : Blo 622298 887717 := bbase (se 4 (by rfl) ⟨83223, by rfl⟩ : syracuseStep 887717 = 166447) (by norm_num)
theorem B789421 : Blo 622298 789421 := bbase (se 3 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 789421 = 296033) (by norm_num)
theorem B3476405 : Blo 622298 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B1051589 : Blo 622298 1051589 := bbase (se 4 (by rfl) ⟨98586, by rfl⟩ : syracuseStep 1051589 = 197173) (by norm_num)
theorem B887797 : Blo 622298 887797 := bbase (se 5 (by rfl) ⟨41615, by rfl⟩ : syracuseStep 887797 = 83231) (by norm_num)
theorem B2001925 : Blo 622298 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B789517 : Blo 622298 789517 := bbase (se 3 (by rfl) ⟨148034, by rfl⟩ : syracuseStep 789517 = 296069) (by norm_num)
theorem B1182757 : Blo 622298 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B1051717 : Blo 622298 1051717 := bbase (se 4 (by rfl) ⟨98598, by rfl⟩ : syracuseStep 1051717 = 197197) (by norm_num)
theorem B1576037 : Blo 622298 1576037 := bbase (se 4 (by rfl) ⟨147753, by rfl⟩ : syracuseStep 1576037 = 295507) (by norm_num)
theorem B887917 : Blo 622298 887917 := bbase (se 3 (by rfl) ⟨166484, by rfl⟩ : syracuseStep 887917 = 332969) (by norm_num)
theorem B1051805 : Blo 622298 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B789689 : Blo 622298 789689 := bbase (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) (by norm_num)
theorem B1182917 : Blo 622298 1182917 := bbase (se 4 (by rfl) ⟨110898, by rfl⟩ : syracuseStep 1182917 = 221797) (by norm_num)
theorem B888013 : Blo 622298 888013 := bbase (se 3 (by rfl) ⟨166502, by rfl⟩ : syracuseStep 888013 = 333005) (by norm_num)
theorem B2100437 : Blo 622298 2100437 := bbase (se 7 (by rfl) ⟨24614, by rfl⟩ : syracuseStep 2100437 = 49229) (by norm_num)
theorem B2526421 : Blo 622298 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B789745 : Blo 622298 789745 := bbase (se 2 (by rfl) ⟨296154, by rfl⟩ : syracuseStep 789745 = 592309) (by norm_num)
theorem B1051933 : Blo 622298 1051933 := bbase (se 3 (by rfl) ⟨197237, by rfl⟩ : syracuseStep 1051933 = 394475) (by norm_num)
theorem B1772837 : Blo 622298 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B1215797 : Blo 622298 1215797 := bbase (se 5 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 1215797 = 113981) (by norm_num)
theorem B789841 : Blo 622298 789841 := bbase (se 2 (by rfl) ⟨296190, by rfl⟩ : syracuseStep 789841 = 592381) (by norm_num)
theorem B1183061 : Blo 622298 1183061 := bbase (se 11 (by rfl) ⟨866, by rfl⟩ : syracuseStep 1183061 = 1733) (by norm_num)
theorem B1052021 : Blo 622298 1052021 := bbase (se 5 (by rfl) ⟨49313, by rfl⟩ : syracuseStep 1052021 = 98627) (by norm_num)
theorem B1576381 : Blo 622298 1576381 := bbase (se 3 (by rfl) ⟨295571, by rfl⟩ : syracuseStep 1576381 = 591143) (by norm_num)
theorem B1052149 : Blo 622298 1052149 := bbase (se 5 (by rfl) ⟨49319, by rfl⟩ : syracuseStep 1052149 = 98639) (by norm_num)
theorem B790013 : Blo 622298 790013 := bbase (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) (by norm_num)
theorem B1576493 : Blo 622298 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B790069 : Blo 622298 790069 := bbase (se 5 (by rfl) ⟨37034, by rfl⟩ : syracuseStep 790069 = 74069) (by norm_num)
theorem B1052237 : Blo 622298 1052237 := bbase (se 3 (by rfl) ⟨197294, by rfl⟩ : syracuseStep 1052237 = 394589) (by norm_num)
theorem B1183349 : Blo 622298 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B2100869 : Blo 622298 2100869 := bbase (se 4 (by rfl) ⟨196956, by rfl⟩ : syracuseStep 2100869 = 393913) (by norm_num)
theorem B790165 : Blo 622298 790165 := bbase (se 6 (by rfl) ⟨18519, by rfl⟩ : syracuseStep 790165 = 37039) (by norm_num)
theorem B888509 : Blo 622298 888509 := bbase (se 3 (by rfl) ⟨166595, by rfl⟩ : syracuseStep 888509 = 333191) (by norm_num)
theorem B1052365 : Blo 622298 1052365 := bbase (se 3 (by rfl) ⟨197318, by rfl⟩ : syracuseStep 1052365 = 394637) (by norm_num)
theorem B1576685 : Blo 622298 1576685 := bbase (se 3 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 1576685 = 591257) (by norm_num)
theorem B1183501 : Blo 622298 1183501 := bbase (se 3 (by rfl) ⟨221906, by rfl⟩ : syracuseStep 1183501 = 443813) (by norm_num)
theorem B1052453 : Blo 622298 1052453 := bbase (se 4 (by rfl) ⟨98667, by rfl⟩ : syracuseStep 1052453 = 197335) (by norm_num)
theorem B790337 : Blo 622298 790337 := bbase (se 2 (by rfl) ⟨296376, by rfl⟩ : syracuseStep 790337 = 592753) (by norm_num)
theorem B790393 : Blo 622298 790393 := bbase (se 2 (by rfl) ⟨296397, by rfl⟩ : syracuseStep 790393 = 592795) (by norm_num)
theorem B2658197 : Blo 622298 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B1052581 : Blo 622298 1052581 := bbase (se 4 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 1052581 = 197359) (by norm_num)
theorem B790489 : Blo 622298 790489 := bbase (se 2 (by rfl) ⟨296433, by rfl⟩ : syracuseStep 790489 = 592867) (by norm_num)
theorem B1052669 : Blo 622298 1052669 := bbase (se 3 (by rfl) ⟨197375, by rfl⟩ : syracuseStep 1052669 = 394751) (by norm_num)
theorem B1773589 : Blo 622298 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B2101301 : Blo 622298 2101301 := bbase (se 5 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 2101301 = 196997) (by norm_num)
theorem B4755509 : Blo 622298 4755509 := bbase (se 5 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 4755509 = 445829) (by norm_num)
theorem B1183805 : Blo 622298 1183805 := bbase (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) (by norm_num)
theorem B1577029 : Blo 622298 1577029 := bbase (se 4 (by rfl) ⟨147846, by rfl⟩ : syracuseStep 1577029 = 295693) (by norm_num)
theorem B2854997 : Blo 622298 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B1052797 : Blo 622298 1052797 := bbase (se 3 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 1052797 = 394799) (by norm_num)
theorem B2363525 : Blo 622298 2363525 := bbase (se 4 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 2363525 = 443161) (by norm_num)
theorem B790661 : Blo 622298 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B1577141 : Blo 622298 1577141 := bbase (se 5 (by rfl) ⟨73928, by rfl⟩ : syracuseStep 1577141 = 147857) (by norm_num)
theorem B790717 : Blo 622298 790717 := bbase (se 3 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 790717 = 296519) (by norm_num)
theorem B1052885 : Blo 622298 1052885 := bbase (se 7 (by rfl) ⟨12338, by rfl⟩ : syracuseStep 1052885 = 24677) (by norm_num)
theorem B889061 : Blo 622298 889061 := bbase (se 4 (by rfl) ⟨83349, by rfl⟩ : syracuseStep 889061 = 166699) (by norm_num)
theorem B790813 : Blo 622298 790813 := bbase (se 3 (by rfl) ⟨148277, by rfl⟩ : syracuseStep 790813 = 296555) (by norm_num)
theorem B2003285 : Blo 622298 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B1053013 : Blo 622298 1053013 := bbase (se 10 (by rfl) ⟨1542, by rfl⟩ : syracuseStep 1053013 = 3085) (by norm_num)
theorem B1577333 : Blo 622298 1577333 := bbase (se 5 (by rfl) ⟨73937, by rfl⟩ : syracuseStep 1577333 = 147875) (by norm_num)
theorem B2363813 : Blo 622298 2363813 := bbase (se 4 (by rfl) ⟨221607, by rfl⟩ : syracuseStep 2363813 = 443215) (by norm_num)
theorem B1053101 : Blo 622298 1053101 := bbase (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) (by norm_num)
theorem B790985 : Blo 622298 790985 := bbase (se 2 (by rfl) ⟨296619, by rfl⟩ : syracuseStep 790985 = 593239) (by norm_num)
theorem B2003413 : Blo 622298 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B2101733 : Blo 622298 2101733 := bbase (se 4 (by rfl) ⟨197037, by rfl⟩ : syracuseStep 2101733 = 394075) (by norm_num)
theorem B791041 : Blo 622298 791041 := bbase (se 2 (by rfl) ⟨296640, by rfl⟩ : syracuseStep 791041 = 593281) (by norm_num)
theorem B1053229 : Blo 622298 1053229 := bbase (se 3 (by rfl) ⟨197480, by rfl⟩ : syracuseStep 1053229 = 394961) (by norm_num)
theorem B791137 : Blo 622298 791137 := bbase (se 2 (by rfl) ⟨296676, by rfl⟩ : syracuseStep 791137 = 593353) (by norm_num)
theorem B1053317 : Blo 622298 1053317 := bbase (se 4 (by rfl) ⟨98748, by rfl⟩ : syracuseStep 1053317 = 197497) (by norm_num)
theorem B1217173 : Blo 622298 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1577677 : Blo 622298 1577677 := bbase (se 3 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 1577677 = 591629) (by norm_num)
theorem B2888405 : Blo 622298 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B2003669 : Blo 622298 2003669 := bbase (se 7 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 2003669 = 46961) (by norm_num)
theorem B1053445 : Blo 622298 1053445 := bbase (se 4 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 1053445 = 197521) (by norm_num)
theorem B791309 : Blo 622298 791309 := bbase (se 3 (by rfl) ⟨148370, by rfl⟩ : syracuseStep 791309 = 296741) (by norm_num)
theorem B1184557 : Blo 622298 1184557 := bbase (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) (by norm_num)
theorem B1577789 : Blo 622298 1577789 := bbase (se 3 (by rfl) ⟨295835, by rfl⟩ : syracuseStep 1577789 = 591671) (by norm_num)
theorem B791365 : Blo 622298 791365 := bbase (se 4 (by rfl) ⟨74190, by rfl⟩ : syracuseStep 791365 = 148381) (by norm_num)
theorem B1053533 : Blo 622298 1053533 := bbase (se 3 (by rfl) ⟨197537, by rfl⟩ : syracuseStep 1053533 = 395075) (by norm_num)
theorem B2102165 : Blo 622298 2102165 := bbase (se 6 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 2102165 = 98539) (by norm_num)
theorem B791461 : Blo 622298 791461 := bbase (se 4 (by rfl) ⟨74199, by rfl⟩ : syracuseStep 791461 = 148399) (by norm_num)
theorem B1184701 : Blo 622298 1184701 := bbase (se 3 (by rfl) ⟨222131, by rfl⟩ : syracuseStep 1184701 = 444263) (by norm_num)
theorem B889813 : Blo 622298 889813 := bbase (se 7 (by rfl) ⟨10427, by rfl⟩ : syracuseStep 889813 = 20855) (by norm_num)
theorem B1053661 : Blo 622298 1053661 := bbase (se 3 (by rfl) ⟨197561, by rfl⟩ : syracuseStep 1053661 = 395123) (by norm_num)
theorem B1577981 : Blo 622298 1577981 := bbase (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) (by norm_num)
theorem B1053749 : Blo 622298 1053749 := bbase (se 5 (by rfl) ⟨49394, by rfl⟩ : syracuseStep 1053749 = 98789) (by norm_num)
theorem B791633 : Blo 622298 791633 := bbase (se 2 (by rfl) ⟨296862, by rfl⟩ : syracuseStep 791633 = 593725) (by norm_num)
theorem B1184861 : Blo 622298 1184861 := bbase (se 3 (by rfl) ⟨222161, by rfl⟩ : syracuseStep 1184861 = 444323) (by norm_num)
theorem B2135173 : Blo 622298 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B791689 : Blo 622298 791689 := bbase (se 2 (by rfl) ⟨296883, by rfl⟩ : syracuseStep 791689 = 593767) (by norm_num)
theorem B1053877 : Blo 622298 1053877 := bbase (se 5 (by rfl) ⟨49400, by rfl⟩ : syracuseStep 1053877 = 98801) (by norm_num)
theorem B3151061 : Blo 622298 3151061 := bbase (se 7 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 3151061 = 73853) (by norm_num)
theorem B791785 : Blo 622298 791785 := bbase (se 2 (by rfl) ⟨296919, by rfl⟩ : syracuseStep 791785 = 593839) (by norm_num)
theorem B1185005 : Blo 622298 1185005 := bbase (se 3 (by rfl) ⟨222188, by rfl⟩ : syracuseStep 1185005 = 444377) (by norm_num)
theorem B1053965 : Blo 622298 1053965 := bbase (se 3 (by rfl) ⟨197618, by rfl⟩ : syracuseStep 1053965 = 395237) (by norm_num)
theorem B2102597 : Blo 622298 2102597 := bbase (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) (by norm_num)
theorem B1578325 : Blo 622298 1578325 := bbase (se 14 (by rfl) ⟨144, by rfl⟩ : syracuseStep 1578325 = 289) (by norm_num)
theorem B1054093 : Blo 622298 1054093 := bbase (se 3 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 1054093 = 395285) (by norm_num)
theorem B791957 : Blo 622298 791957 := bbase (se 6 (by rfl) ⟨18561, by rfl⟩ : syracuseStep 791957 = 37123) (by norm_num)
theorem B1578437 : Blo 622298 1578437 := bbase (se 4 (by rfl) ⟨147978, by rfl⟩ : syracuseStep 1578437 = 295957) (by norm_num)
theorem B792013 : Blo 622298 792013 := bbase (se 3 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 792013 = 297005) (by norm_num)
theorem B1054181 : Blo 622298 1054181 := bbase (se 4 (by rfl) ⟨98829, by rfl⟩ : syracuseStep 1054181 = 197659) (by norm_num)
theorem B1185293 : Blo 622298 1185293 := bbase (se 3 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 1185293 = 444485) (by norm_num)
theorem B792109 : Blo 622298 792109 := bbase (se 3 (by rfl) ⟨148520, by rfl⟩ : syracuseStep 792109 = 297041) (by norm_num)
theorem B2364997 : Blo 622298 2364997 := bbase (se 4 (by rfl) ⟨221718, by rfl⟩ : syracuseStep 2364997 = 443437) (by norm_num)
theorem B1054309 : Blo 622298 1054309 := bbase (se 4 (by rfl) ⟨98841, by rfl⟩ : syracuseStep 1054309 = 197683) (by norm_num)
theorem B1578629 : Blo 622298 1578629 := bbase (se 4 (by rfl) ⟨147996, by rfl⟩ : syracuseStep 1578629 = 295993) (by norm_num)
theorem B1185445 : Blo 622298 1185445 := bbase (se 4 (by rfl) ⟨111135, by rfl⟩ : syracuseStep 1185445 = 222271) (by norm_num)
theorem B1054397 : Blo 622298 1054397 := bbase (se 3 (by rfl) ⟨197699, by rfl⟩ : syracuseStep 1054397 = 395399) (by norm_num)
theorem B792281 : Blo 622298 792281 := bbase (se 2 (by rfl) ⟨297105, by rfl⟩ : syracuseStep 792281 = 594211) (by norm_num)
theorem B890605 : Blo 622298 890605 := bbase (se 3 (by rfl) ⟨166988, by rfl⟩ : syracuseStep 890605 = 333977) (by norm_num)
theorem B2103029 : Blo 622298 2103029 := bbase (se 5 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 2103029 = 197159) (by norm_num)
theorem B792337 : Blo 622298 792337 := bbase (se 2 (by rfl) ⟨297126, by rfl⟩ : syracuseStep 792337 = 594253) (by norm_num)
theorem B1054525 : Blo 622298 1054525 := bbase (se 3 (by rfl) ⟨197723, by rfl⟩ : syracuseStep 1054525 = 395447) (by norm_num)
theorem B792433 : Blo 622298 792433 := bbase (se 2 (by rfl) ⟨297162, by rfl⟩ : syracuseStep 792433 = 594325) (by norm_num)
theorem B2365301 : Blo 622298 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B1054613 : Blo 622298 1054613 := bbase (se 6 (by rfl) ⟨24717, by rfl⟩ : syracuseStep 1054613 = 49435) (by norm_num)
theorem B1185749 : Blo 622298 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B1578973 : Blo 622298 1578973 := bbase (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) (by norm_num)
theorem B4003829 : Blo 622298 4003829 := bbase (se 5 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 4003829 = 375359) (by norm_num)
theorem B1054741 : Blo 622298 1054741 := bbase (se 6 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 1054741 = 49441) (by norm_num)
theorem B792605 : Blo 622298 792605 := bbase (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) (by norm_num)
theorem B890941 : Blo 622298 890941 := bbase (se 3 (by rfl) ⟨167051, by rfl⟩ : syracuseStep 890941 = 334103) (by norm_num)
theorem B1579085 : Blo 622298 1579085 := bbase (se 3 (by rfl) ⟨296078, by rfl⟩ : syracuseStep 1579085 = 592157) (by norm_num)
theorem B1054829 : Blo 622298 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B3381365 : Blo 622298 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B2103461 : Blo 622298 2103461 := bbase (se 4 (by rfl) ⟨197199, by rfl⟩ : syracuseStep 2103461 = 394399) (by norm_num)
theorem B1054957 : Blo 622298 1054957 := bbase (se 3 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 1054957 = 395609) (by norm_num)
theorem B1579277 : Blo 622298 1579277 := bbase (se 3 (by rfl) ⟨296114, by rfl⟩ : syracuseStep 1579277 = 592229) (by norm_num)
theorem B891157 : Blo 622298 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B1055045 : Blo 622298 1055045 := bbase (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) (by norm_num)
theorem B1055173 : Blo 622298 1055173 := bbase (se 4 (by rfl) ⟨98922, by rfl⟩ : syracuseStep 1055173 = 197845) (by norm_num)
theorem B3152357 : Blo 622298 3152357 := bbase (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) (by norm_num)
theorem B1055261 : Blo 622298 1055261 := bbase (se 3 (by rfl) ⟨197861, by rfl⟩ : syracuseStep 1055261 = 395723) (by norm_num)
theorem B2103893 : Blo 622298 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B1579621 : Blo 622298 1579621 := bbase (se 4 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 1579621 = 296179) (by norm_num)
theorem B891533 : Blo 622298 891533 := bbase (se 3 (by rfl) ⟨167162, by rfl⟩ : syracuseStep 891533 = 334325) (by norm_num)
theorem B1055389 : Blo 622298 1055389 := bbase (se 3 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 1055389 = 395771) (by norm_num)
theorem B1186501 : Blo 622298 1186501 := bbase (se 4 (by rfl) ⟨111234, by rfl⟩ : syracuseStep 1186501 = 222469) (by norm_num)
theorem B1579733 : Blo 622298 1579733 := bbase (se 7 (by rfl) ⟨18512, by rfl⟩ : syracuseStep 1579733 = 37025) (by norm_num)
theorem B1055477 : Blo 622298 1055477 := bbase (se 5 (by rfl) ⟨49475, by rfl⟩ : syracuseStep 1055477 = 98951) (by norm_num)
theorem B1776437 : Blo 622298 1776437 := bbase (se 5 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 1776437 = 166541) (by norm_num)
theorem B1186645 : Blo 622298 1186645 := bbase (se 9 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 1186645 = 6953) (by norm_num)
theorem B1055605 : Blo 622298 1055605 := bbase (se 5 (by rfl) ⟨49481, by rfl⟩ : syracuseStep 1055605 = 98963) (by norm_num)
theorem B1579925 : Blo 622298 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B1055693 : Blo 622298 1055693 := bbase (se 3 (by rfl) ⟨197942, by rfl⟩ : syracuseStep 1055693 = 395885) (by norm_num)
theorem B1186805 : Blo 622298 1186805 := bbase (se 5 (by rfl) ⟨55631, by rfl⟩ : syracuseStep 1186805 = 111263) (by norm_num)
theorem B2104325 : Blo 622298 2104325 := bbase (se 4 (by rfl) ⟨197280, by rfl⟩ : syracuseStep 2104325 = 394561) (by norm_num)
theorem B1055821 : Blo 622298 1055821 := bbase (se 3 (by rfl) ⟨197966, by rfl⟩ : syracuseStep 1055821 = 395933) (by norm_num)
theorem B2006117 : Blo 622298 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B1186949 : Blo 622298 1186949 := bbase (se 4 (by rfl) ⟨111276, by rfl⟩ : syracuseStep 1186949 = 222553) (by norm_num)
theorem B1055909 : Blo 622298 1055909 := bbase (se 4 (by rfl) ⟨98991, by rfl⟩ : syracuseStep 1055909 = 197983) (by norm_num)
theorem B1580269 : Blo 622298 1580269 := bbase (se 3 (by rfl) ⟨296300, by rfl⟩ : syracuseStep 1580269 = 592601) (by norm_num)
theorem B1056037 : Blo 622298 1056037 := bbase (se 4 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 1056037 = 198007) (by norm_num)
theorem B1580381 : Blo 622298 1580381 := bbase (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) (by norm_num)
theorem B1056125 : Blo 622298 1056125 := bbase (se 3 (by rfl) ⟨198023, by rfl⟩ : syracuseStep 1056125 = 396047) (by norm_num)
theorem B1121701 : Blo 622298 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B1187237 : Blo 622298 1187237 := bbase (se 4 (by rfl) ⟨111303, by rfl⟩ : syracuseStep 1187237 = 222607) (by norm_num)
theorem B2104757 : Blo 622298 2104757 := bbase (se 5 (by rfl) ⟨98660, by rfl⟩ : syracuseStep 2104757 = 197321) (by norm_num)
theorem B1056253 : Blo 622298 1056253 := bbase (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) (by norm_num)
theorem B1580573 : Blo 622298 1580573 := bbase (se 3 (by rfl) ⟨296357, by rfl⟩ : syracuseStep 1580573 = 592715) (by norm_num)
theorem B1187389 : Blo 622298 1187389 := bbase (se 3 (by rfl) ⟨222635, by rfl⟩ : syracuseStep 1187389 = 445271) (by norm_num)
theorem B1056341 : Blo 622298 1056341 := bbase (se 8 (by rfl) ⟨6189, by rfl⟩ : syracuseStep 1056341 = 12379) (by norm_num)
theorem B2530997 : Blo 622298 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1056469 : Blo 622298 1056469 := bbase (se 7 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 1056469 = 24761) (by norm_num)
theorem B3153653 : Blo 622298 3153653 := bbase (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) (by norm_num)
theorem B1056557 : Blo 622298 1056557 := bbase (se 3 (by rfl) ⟨198104, by rfl⟩ : syracuseStep 1056557 = 396209) (by norm_num)
theorem B3383093 : Blo 622298 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B2105189 : Blo 622298 2105189 := bbase (se 4 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 2105189 = 394723) (by norm_num)
theorem B1187693 : Blo 622298 1187693 := bbase (se 3 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 1187693 = 445385) (by norm_num)
theorem B1580917 : Blo 622298 1580917 := bbase (se 5 (by rfl) ⟨74105, by rfl⟩ : syracuseStep 1580917 = 148211) (by norm_num)
theorem B2138021 : Blo 622298 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B1056685 : Blo 622298 1056685 := bbase (se 3 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 1056685 = 396257) (by norm_num)
theorem B2367413 : Blo 622298 2367413 := bbase (se 5 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 2367413 = 221945) (by norm_num)
theorem B1777621 : Blo 622298 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B1581029 : Blo 622298 1581029 := bbase (se 4 (by rfl) ⟨148221, by rfl⟩ : syracuseStep 1581029 = 296443) (by norm_num)
theorem B1056773 : Blo 622298 1056773 := bbase (se 4 (by rfl) ⟨99072, by rfl⟩ : syracuseStep 1056773 = 198145) (by norm_num)
theorem B2662469 : Blo 622298 2662469 := bbase (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) (by norm_num)
theorem B1777781 : Blo 622298 1777781 := bbase (se 5 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 1777781 = 166667) (by norm_num)
theorem B1581221 : Blo 622298 1581221 := bbase (se 4 (by rfl) ⟨148239, by rfl⟩ : syracuseStep 1581221 = 296479) (by norm_num)
theorem B2367701 : Blo 622298 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B1122581 : Blo 622298 1122581 := bbase (se 6 (by rfl) ⟨26310, by rfl⟩ : syracuseStep 1122581 = 52621) (by norm_num)
theorem B2105621 : Blo 622298 2105621 := bbase (se 6 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 2105621 = 98701) (by norm_num)
theorem B12165461 : Blo 622298 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B1778021 : Blo 622298 1778021 := bbase (se 4 (by rfl) ⟨166689, by rfl⟩ : syracuseStep 1778021 = 333379) (by norm_num)
theorem B1122797 : Blo 622298 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B1581565 : Blo 622298 1581565 := bbase (se 3 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 1581565 = 593087) (by norm_num)
theorem B1778213 : Blo 622298 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B1188445 : Blo 622298 1188445 := bbase (se 3 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 1188445 = 445667) (by norm_num)
theorem B1581677 : Blo 622298 1581677 := bbase (se 3 (by rfl) ⟨296564, by rfl⟩ : syracuseStep 1581677 = 593129) (by norm_num)
theorem B1122941 : Blo 622298 1122941 := bbase (se 3 (by rfl) ⟨210551, by rfl⟩ : syracuseStep 1122941 = 421103) (by norm_num)
theorem B2106053 : Blo 622298 2106053 := bbase (se 4 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 2106053 = 394885) (by norm_num)
theorem B1123021 : Blo 622298 1123021 := bbase (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) (by norm_num)
theorem B959197 : Blo 622298 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B1188589 : Blo 622298 1188589 := bbase (se 3 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 1188589 = 445721) (by norm_num)
theorem B1581869 : Blo 622298 1581869 := bbase (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) (by norm_num)
theorem B1188749 : Blo 622298 1188749 := bbase (se 3 (by rfl) ⟨222890, by rfl⟩ : syracuseStep 1188749 = 445781) (by norm_num)
theorem B2139061 : Blo 622298 2139061 := bbase (se 5 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 2139061 = 200537) (by norm_num)
theorem B3154949 : Blo 622298 3154949 := bbase (se 4 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 3154949 = 591553) (by norm_num)
theorem B1188893 : Blo 622298 1188893 := bbase (se 3 (by rfl) ⟨222917, by rfl⟩ : syracuseStep 1188893 = 445835) (by norm_num)
theorem B664609 : Blo 622298 664609 := bbase (se 2 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 664609 = 498457) (by norm_num)
theorem B631841 : Blo 622298 631841 := bbase (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) (by norm_num)
theorem B631849 : Blo 622298 631849 := bbase (se 2 (by rfl) ⟨236943, by rfl⟩ : syracuseStep 631849 = 473887) (by norm_num)
theorem B631865 : Blo 622298 631865 := bbase (se 2 (by rfl) ⟨236949, by rfl⟩ : syracuseStep 631865 = 473899) (by norm_num)
theorem B2106485 : Blo 622298 2106485 := bbase (se 5 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 2106485 = 197483) (by norm_num)
theorem B4007029 : Blo 622298 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B1582213 : Blo 622298 1582213 := bbase (se 4 (by rfl) ⟨148332, by rfl⟩ : syracuseStep 1582213 = 296665) (by norm_num)
theorem B2598101 : Blo 622298 2598101 := bbase (se 7 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 2598101 = 60893) (by norm_num)
theorem B1582325 : Blo 622298 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B1353053 : Blo 622298 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B2368885 : Blo 622298 2368885 := bbase (se 5 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 2368885 = 222083) (by norm_num)
theorem B2991509 : Blo 622298 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B1582517 : Blo 622298 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B665053 : Blo 622298 665053 := bbase (se 3 (by rfl) ⟨124697, by rfl⟩ : syracuseStep 665053 = 249395) (by norm_num)
theorem B1779205 : Blo 622298 1779205 := bbase (se 4 (by rfl) ⟨166800, by rfl⟩ : syracuseStep 1779205 = 333601) (by norm_num)
theorem B2106917 : Blo 622298 2106917 := bbase (se 4 (by rfl) ⟨197523, by rfl⟩ : syracuseStep 2106917 = 395047) (by norm_num)
theorem B665173 : Blo 622298 665173 := bbase (se 8 (by rfl) ⟨3897, by rfl⟩ : syracuseStep 665173 = 7795) (by norm_num)
theorem B2369189 : Blo 622298 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B1582861 : Blo 622298 1582861 := bbase (se 3 (by rfl) ⟨296786, by rfl⟩ : syracuseStep 1582861 = 593573) (by norm_num)
theorem B2664245 : Blo 622298 2664245 := bbase (se 5 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 2664245 = 249773) (by norm_num)
theorem B665425 : Blo 622298 665425 := bbase (se 2 (by rfl) ⟨249534, by rfl⟩ : syracuseStep 665425 = 499069) (by norm_num)
theorem B665429 : Blo 622298 665429 := bbase (se 9 (by rfl) ⟨1949, by rfl⟩ : syracuseStep 665429 = 3899) (by norm_num)
theorem B1582973 : Blo 622298 1582973 := bbase (se 3 (by rfl) ⟨296807, by rfl⟩ : syracuseStep 1582973 = 593615) (by norm_num)
theorem B632773 : Blo 622298 632773 := bbase (se 4 (by rfl) ⟨59322, by rfl⟩ : syracuseStep 632773 = 118645) (by norm_num)
theorem B2107349 : Blo 622298 2107349 := bbase (se 7 (by rfl) ⟨24695, by rfl⟩ : syracuseStep 2107349 = 49391) (by norm_num)
theorem B2664485 : Blo 622298 2664485 := bbase (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) (by norm_num)
theorem B1583165 : Blo 622298 1583165 := bbase (se 3 (by rfl) ⟨296843, by rfl⟩ : syracuseStep 1583165 = 593687) (by norm_num)
theorem B13674581 : Blo 622298 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B2992261 : Blo 622298 2992261 := bbase (se 4 (by rfl) ⟨280524, by rfl⟩ : syracuseStep 2992261 = 561049) (by norm_num)
theorem B3549365 : Blo 622298 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B2140373 : Blo 622298 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B3156245 : Blo 622298 3156245 := bbase (se 6 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 3156245 = 147949) (by norm_num)
theorem B2107781 : Blo 622298 2107781 := bbase (se 4 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 2107781 = 395209) (by norm_num)
theorem B665993 : Blo 622298 665993 := bbase (se 2 (by rfl) ⟨249747, by rfl⟩ : syracuseStep 665993 = 499495) (by norm_num)
theorem B1583509 : Blo 622298 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B1583621 : Blo 622298 1583621 := bbase (se 4 (by rfl) ⟨148464, by rfl⟩ : syracuseStep 1583621 = 296929) (by norm_num)
theorem B666181 : Blo 622298 666181 := bbase (se 4 (by rfl) ⟨62454, by rfl⟩ : syracuseStep 666181 = 124909) (by norm_num)
theorem B1780309 : Blo 622298 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B1583813 : Blo 622298 1583813 := bbase (se 4 (by rfl) ⟨148482, by rfl⟩ : syracuseStep 1583813 = 296965) (by norm_num)
theorem B2108213 : Blo 622298 2108213 := bbase (se 5 (by rfl) ⟨98822, by rfl⟩ : syracuseStep 2108213 = 197645) (by norm_num)
theorem B961373 : Blo 622298 961373 := bbase (se 3 (by rfl) ⟨180257, by rfl⟩ : syracuseStep 961373 = 360515) (by norm_num)
theorem B1354733 : Blo 622298 1354733 := bbase (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) (by norm_num)
theorem B1518581 : Blo 622298 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B1584157 : Blo 622298 1584157 := bbase (se 3 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 1584157 = 594059) (by norm_num)
theorem B633917 : Blo 622298 633917 := bbase (se 3 (by rfl) ⟨118859, by rfl⟩ : syracuseStep 633917 = 237719) (by norm_num)
theorem B1584269 : Blo 622298 1584269 := bbase (se 3 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 1584269 = 594101) (by norm_num)
theorem B2108645 : Blo 622298 2108645 := bbase (se 4 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 2108645 = 395371) (by norm_num)
theorem B1584461 : Blo 622298 1584461 := bbase (se 3 (by rfl) ⟨297086, by rfl⟩ : syracuseStep 1584461 = 594173) (by norm_num)
theorem B667001 : Blo 622298 667001 := bbase (se 2 (by rfl) ⟨250125, by rfl⟩ : syracuseStep 667001 = 500251) (by norm_num)
theorem B1519069 : Blo 622298 1519069 := bbase (se 3 (by rfl) ⟨284825, by rfl⟩ : syracuseStep 1519069 = 569651) (by norm_num)
theorem B3157541 : Blo 622298 3157541 := bbase (se 4 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 3157541 = 592039) (by norm_num)
theorem B12136085 : Blo 622298 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B2109077 : Blo 622298 2109077 := bbase (se 6 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 2109077 = 98863) (by norm_num)
theorem B1584805 : Blo 622298 1584805 := bbase (se 4 (by rfl) ⟨148575, by rfl⟩ : syracuseStep 1584805 = 297151) (by norm_num)
theorem B700105 : Blo 622298 700105 := bbase (se 2 (by rfl) ⟨262539, by rfl⟩ : syracuseStep 700105 = 525079) (by norm_num)
theorem B2371301 : Blo 622298 2371301 := bbase (se 4 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 2371301 = 444619) (by norm_num)
theorem B700141 : Blo 622298 700141 := bbase (se 3 (by rfl) ⟨131276, by rfl⟩ : syracuseStep 700141 = 262553) (by norm_num)
theorem B700177 : Blo 622298 700177 := bbase (se 2 (by rfl) ⟨262566, by rfl⟩ : syracuseStep 700177 = 525133) (by norm_num)
theorem B1421077 : Blo 622298 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B1584917 : Blo 622298 1584917 := bbase (se 6 (by rfl) ⟨37146, by rfl⟩ : syracuseStep 1584917 = 74293) (by norm_num)
theorem B700213 : Blo 622298 700213 := bbase (se 5 (by rfl) ⟨32822, by rfl⟩ : syracuseStep 700213 = 65645) (by norm_num)
theorem B667445 : Blo 622298 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B700249 : Blo 622298 700249 := bbase (se 2 (by rfl) ⟨262593, by rfl⟩ : syracuseStep 700249 = 525187) (by norm_num)
theorem B700285 : Blo 622298 700285 := bbase (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) (by norm_num)
theorem B700321 : Blo 622298 700321 := bbase (se 2 (by rfl) ⟨262620, by rfl⟩ : syracuseStep 700321 = 525241) (by norm_num)
theorem B700357 : Blo 622298 700357 := bbase (se 4 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 700357 = 131317) (by norm_num)
theorem B1585109 : Blo 622298 1585109 := bbase (se 7 (by rfl) ⟨18575, by rfl⟩ : syracuseStep 1585109 = 37151) (by norm_num)
theorem B700393 : Blo 622298 700393 := bbase (se 2 (by rfl) ⟨262647, by rfl⟩ : syracuseStep 700393 = 525295) (by norm_num)
theorem B2371589 : Blo 622298 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B700429 : Blo 622298 700429 := bbase (se 3 (by rfl) ⟨131330, by rfl⟩ : syracuseStep 700429 = 262661) (by norm_num)
theorem B1126429 : Blo 622298 1126429 := bbase (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) (by norm_num)
theorem B667693 : Blo 622298 667693 := bbase (se 3 (by rfl) ⟨125192, by rfl⟩ : syracuseStep 667693 = 250385) (by norm_num)
theorem B700465 : Blo 622298 700465 := bbase (se 2 (by rfl) ⟨262674, by rfl⟩ : syracuseStep 700465 = 525349) (by norm_num)
theorem B1781813 : Blo 622298 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B2109509 : Blo 622298 2109509 := bbase (se 4 (by rfl) ⟨197766, by rfl⟩ : syracuseStep 2109509 = 395533) (by norm_num)
theorem B700501 : Blo 622298 700501 := bbase (se 8 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 700501 = 8209) (by norm_num)
theorem B1421405 : Blo 622298 1421405 := bbase (se 3 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 1421405 = 533027) (by norm_num)
theorem B700537 : Blo 622298 700537 := bbase (se 2 (by rfl) ⟨262701, by rfl⟩ : syracuseStep 700537 = 525403) (by norm_num)
theorem B700573 : Blo 622298 700573 := bbase (se 3 (by rfl) ⟨131357, by rfl⟩ : syracuseStep 700573 = 262715) (by norm_num)
theorem B700609 : Blo 622298 700609 := bbase (se 2 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 700609 = 525457) (by norm_num)
theorem B798925 : Blo 622298 798925 := bbase (se 3 (by rfl) ⟨149798, by rfl⟩ : syracuseStep 798925 = 299597) (by norm_num)
theorem B700645 : Blo 622298 700645 := bbase (se 4 (by rfl) ⟨65685, by rfl⟩ : syracuseStep 700645 = 131371) (by norm_num)
theorem B700681 : Blo 622298 700681 := bbase (se 2 (by rfl) ⟨262755, by rfl⟩ : syracuseStep 700681 = 525511) (by norm_num)
theorem B2666773 : Blo 622298 2666773 := bbase (se 6 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 2666773 = 125005) (by norm_num)
theorem B700717 : Blo 622298 700717 := bbase (se 3 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 700717 = 262769) (by norm_num)
theorem B700753 : Blo 622298 700753 := bbase (se 2 (by rfl) ⟨262782, by rfl⟩ : syracuseStep 700753 = 525565) (by norm_num)
theorem B13873493 : Blo 622298 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B700789 : Blo 622298 700789 := bbase (se 5 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 700789 = 65699) (by norm_num)
theorem B700825 : Blo 622298 700825 := bbase (se 2 (by rfl) ⟨262809, by rfl⟩ : syracuseStep 700825 = 525619) (by norm_num)
theorem B799141 : Blo 622298 799141 := bbase (se 4 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 799141 = 149839) (by norm_num)
theorem B700861 : Blo 622298 700861 := bbase (se 3 (by rfl) ⟨131411, by rfl⟩ : syracuseStep 700861 = 262823) (by norm_num)
theorem B668125 : Blo 622298 668125 := bbase (se 3 (by rfl) ⟨125273, by rfl⟩ : syracuseStep 668125 = 250547) (by norm_num)
theorem B700897 : Blo 622298 700897 := bbase (se 2 (by rfl) ⟨262836, by rfl⟩ : syracuseStep 700897 = 525673) (by norm_num)
theorem B2109941 : Blo 622298 2109941 := bbase (se 5 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 2109941 = 197807) (by norm_num)
theorem B700933 : Blo 622298 700933 := bbase (se 4 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 700933 = 131425) (by norm_num)
theorem B668197 : Blo 622298 668197 := bbase (se 4 (by rfl) ⟨62643, by rfl⟩ : syracuseStep 668197 = 125287) (by norm_num)
theorem B700969 : Blo 622298 700969 := bbase (se 2 (by rfl) ⟨262863, by rfl⟩ : syracuseStep 700969 = 525727) (by norm_num)
theorem B701005 : Blo 622298 701005 := bbase (se 3 (by rfl) ⟨131438, by rfl⟩ : syracuseStep 701005 = 262877) (by norm_num)
theorem B701041 : Blo 622298 701041 := bbase (se 2 (by rfl) ⟨262890, by rfl⟩ : syracuseStep 701041 = 525781) (by norm_num)
theorem B701077 : Blo 622298 701077 := bbase (se 6 (by rfl) ⟨16431, by rfl⟩ : syracuseStep 701077 = 32863) (by norm_num)
theorem B701113 : Blo 622298 701113 := bbase (se 2 (by rfl) ⟨262917, by rfl⟩ : syracuseStep 701113 = 525835) (by norm_num)
theorem B701149 : Blo 622298 701149 := bbase (se 3 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 701149 = 262931) (by norm_num)
theorem B701185 : Blo 622298 701185 := bbase (se 2 (by rfl) ⟨262944, by rfl⟩ : syracuseStep 701185 = 525889) (by norm_num)
theorem B701221 : Blo 622298 701221 := bbase (se 4 (by rfl) ⟨65739, by rfl⟩ : syracuseStep 701221 = 131479) (by norm_num)
theorem B3158837 : Blo 622298 3158837 := bbase (se 5 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 3158837 = 296141) (by norm_num)
theorem B701257 : Blo 622298 701257 := bbase (se 2 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 701257 = 525943) (by norm_num)
theorem B701293 : Blo 622298 701293 := bbase (se 3 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 701293 = 262985) (by norm_num)
theorem B701329 : Blo 622298 701329 := bbase (se 2 (by rfl) ⟨262998, by rfl⟩ : syracuseStep 701329 = 525997) (by norm_num)
theorem B668569 : Blo 622298 668569 := bbase (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) (by norm_num)
theorem B1422245 : Blo 622298 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B2110373 : Blo 622298 2110373 := bbase (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) (by norm_num)
theorem B701365 : Blo 622298 701365 := bbase (se 5 (by rfl) ⟨32876, by rfl⟩ : syracuseStep 701365 = 65753) (by norm_num)
theorem B701401 : Blo 622298 701401 := bbase (se 2 (by rfl) ⟨263025, by rfl⟩ : syracuseStep 701401 = 526051) (by norm_num)
theorem B799741 : Blo 622298 799741 := bbase (se 3 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 799741 = 299903) (by norm_num)
theorem B701437 : Blo 622298 701437 := bbase (se 3 (by rfl) ⟨131519, by rfl⟩ : syracuseStep 701437 = 263039) (by norm_num)
theorem B701473 : Blo 622298 701473 := bbase (se 2 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 701473 = 526105) (by norm_num)
theorem B701509 : Blo 622298 701509 := bbase (se 4 (by rfl) ⟨65766, by rfl⟩ : syracuseStep 701509 = 131533) (by norm_num)
theorem B1127525 : Blo 622298 1127525 := bbase (se 4 (by rfl) ⟨105705, by rfl⟩ : syracuseStep 1127525 = 211411) (by norm_num)
theorem B701545 : Blo 622298 701545 := bbase (se 2 (by rfl) ⟨263079, by rfl⟩ : syracuseStep 701545 = 526159) (by norm_num)
theorem B898189 : Blo 622298 898189 := bbase (se 3 (by rfl) ⟨168410, by rfl⟩ : syracuseStep 898189 = 336821) (by norm_num)
theorem B701581 : Blo 622298 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B2372773 : Blo 622298 2372773 := bbase (se 4 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 2372773 = 444895) (by norm_num)
theorem B701617 : Blo 622298 701617 := bbase (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) (by norm_num)
theorem B701653 : Blo 622298 701653 := bbase (se 7 (by rfl) ⟨8222, by rfl⟩ : syracuseStep 701653 = 16445) (by norm_num)
theorem B701689 : Blo 622298 701689 := bbase (se 2 (by rfl) ⟨263133, by rfl⟩ : syracuseStep 701689 = 526267) (by norm_num)
theorem B4732181 : Blo 622298 4732181 := bbase (se 6 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 4732181 = 221821) (by norm_num)
theorem B701725 : Blo 622298 701725 := bbase (se 3 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 701725 = 263147) (by norm_num)
theorem B701761 : Blo 622298 701761 := bbase (se 2 (by rfl) ⟨263160, by rfl⟩ : syracuseStep 701761 = 526321) (by norm_num)
theorem B800069 : Blo 622298 800069 := bbase (se 4 (by rfl) ⟨75006, by rfl⟩ : syracuseStep 800069 = 150013) (by norm_num)
theorem B2110805 : Blo 622298 2110805 := bbase (se 13 (by rfl) ⟨386, by rfl⟩ : syracuseStep 2110805 = 773) (by norm_num)
theorem B701797 : Blo 622298 701797 := bbase (se 4 (by rfl) ⟨65793, by rfl⟩ : syracuseStep 701797 = 131587) (by norm_num)
theorem B701833 : Blo 622298 701833 := bbase (se 2 (by rfl) ⟨263187, by rfl⟩ : syracuseStep 701833 = 526375) (by norm_num)
theorem B701869 : Blo 622298 701869 := bbase (se 3 (by rfl) ⟨131600, by rfl⟩ : syracuseStep 701869 = 263201) (by norm_num)
theorem B701905 : Blo 622298 701905 := bbase (se 2 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 701905 = 526429) (by norm_num)
theorem B2373077 : Blo 622298 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B701941 : Blo 622298 701941 := bbase (se 5 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 701941 = 65807) (by norm_num)
theorem B701977 : Blo 622298 701977 := bbase (se 2 (by rfl) ⟨263241, by rfl⟩ : syracuseStep 701977 = 526483) (by norm_num)
theorem B702013 : Blo 622298 702013 := bbase (se 3 (by rfl) ⟨131627, by rfl⟩ : syracuseStep 702013 = 263255) (by norm_num)
theorem B702049 : Blo 622298 702049 := bbase (se 2 (by rfl) ⟨263268, by rfl⟩ : syracuseStep 702049 = 526537) (by norm_num)
theorem B996965 : Blo 622298 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B1783397 : Blo 622298 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B702085 : Blo 622298 702085 := bbase (se 4 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 702085 = 131641) (by norm_num)
theorem B702121 : Blo 622298 702121 := bbase (se 2 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 702121 = 526591) (by norm_num)
theorem B702157 : Blo 622298 702157 := bbase (se 3 (by rfl) ⟨131654, by rfl⟩ : syracuseStep 702157 = 263309) (by norm_num)
theorem B2668261 : Blo 622298 2668261 := bbase (se 4 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 2668261 = 500299) (by norm_num)
theorem B702193 : Blo 622298 702193 := bbase (se 2 (by rfl) ⟨263322, by rfl⟩ : syracuseStep 702193 = 526645) (by norm_num)
theorem B2668277 : Blo 622298 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B2111237 : Blo 622298 2111237 := bbase (se 4 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 2111237 = 395857) (by norm_num)
theorem B702229 : Blo 622298 702229 := bbase (se 6 (by rfl) ⟨16458, by rfl⟩ : syracuseStep 702229 = 32917) (by norm_num)
theorem B702265 : Blo 622298 702265 := bbase (se 2 (by rfl) ⟨263349, by rfl⟩ : syracuseStep 702265 = 526699) (by norm_num)
theorem B702301 : Blo 622298 702301 := bbase (se 3 (by rfl) ⟨131681, by rfl⟩ : syracuseStep 702301 = 263363) (by norm_num)
theorem B1423229 : Blo 622298 1423229 := bbase (se 3 (by rfl) ⟨266855, by rfl⟩ : syracuseStep 1423229 = 533711) (by norm_num)
theorem B702337 : Blo 622298 702337 := bbase (se 2 (by rfl) ⟨263376, by rfl⟩ : syracuseStep 702337 = 526753) (by norm_num)
theorem B702373 : Blo 622298 702373 := bbase (se 4 (by rfl) ⟨65847, by rfl⟩ : syracuseStep 702373 = 131695) (by norm_num)
theorem B702409 : Blo 622298 702409 := bbase (se 2 (by rfl) ⟨263403, by rfl⟩ : syracuseStep 702409 = 526807) (by norm_num)
theorem B702445 : Blo 622298 702445 := bbase (se 3 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 702445 = 263417) (by norm_num)
theorem B702481 : Blo 622298 702481 := bbase (se 2 (by rfl) ⟨263430, by rfl⟩ : syracuseStep 702481 = 526861) (by norm_num)
theorem B702517 : Blo 622298 702517 := bbase (se 5 (by rfl) ⟨32930, by rfl⟩ : syracuseStep 702517 = 65861) (by norm_num)
theorem B3160133 : Blo 622298 3160133 := bbase (se 4 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 3160133 = 592525) (by norm_num)
theorem B702553 : Blo 622298 702553 := bbase (se 2 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 702553 = 526915) (by norm_num)
theorem B997477 : Blo 622298 997477 := bbase (se 4 (by rfl) ⟨93513, by rfl⟩ : syracuseStep 997477 = 187027) (by norm_num)
theorem B702589 : Blo 622298 702589 := bbase (se 3 (by rfl) ⟨131735, by rfl⟩ : syracuseStep 702589 = 263471) (by norm_num)
theorem B4503701 : Blo 622298 4503701 := bbase (se 6 (by rfl) ⟨105555, by rfl⟩ : syracuseStep 4503701 = 211111) (by norm_num)
theorem B702625 : Blo 622298 702625 := bbase (se 2 (by rfl) ⟨263484, by rfl⟩ : syracuseStep 702625 = 526969) (by norm_num)
theorem B2111669 : Blo 622298 2111669 := bbase (se 5 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 2111669 = 197969) (by norm_num)
theorem B702661 : Blo 622298 702661 := bbase (se 4 (by rfl) ⟨65874, by rfl⟩ : syracuseStep 702661 = 131749) (by norm_num)
theorem B702697 : Blo 622298 702697 := bbase (se 2 (by rfl) ⟨263511, by rfl⟩ : syracuseStep 702697 = 527023) (by norm_num)
theorem B702733 : Blo 622298 702733 := bbase (se 3 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 702733 = 263525) (by norm_num)
theorem B702769 : Blo 622298 702769 := bbase (se 2 (by rfl) ⟨263538, by rfl⟩ : syracuseStep 702769 = 527077) (by norm_num)
theorem B702805 : Blo 622298 702805 := bbase (se 10 (by rfl) ⟨1029, by rfl⟩ : syracuseStep 702805 = 2059) (by norm_num)
theorem B702841 : Blo 622298 702841 := bbase (se 2 (by rfl) ⟨263565, by rfl⟩ : syracuseStep 702841 = 527131) (by norm_num)
theorem B702877 : Blo 622298 702877 := bbase (se 3 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 702877 = 263579) (by norm_num)
theorem B702913 : Blo 622298 702913 := bbase (se 2 (by rfl) ⟨263592, by rfl⟩ : syracuseStep 702913 = 527185) (by norm_num)
theorem B1423813 : Blo 622298 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B702949 : Blo 622298 702949 := bbase (se 4 (by rfl) ⟨65901, by rfl⟩ : syracuseStep 702949 = 131803) (by norm_num)
theorem B702985 : Blo 622298 702985 := bbase (se 2 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 702985 = 527239) (by norm_num)
theorem B7191061 : Blo 622298 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B997933 : Blo 622298 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B703021 : Blo 622298 703021 := bbase (se 3 (by rfl) ⟨131816, by rfl⟩ : syracuseStep 703021 = 263633) (by norm_num)
theorem B703057 : Blo 622298 703057 := bbase (se 2 (by rfl) ⟨263646, by rfl⟩ : syracuseStep 703057 = 527293) (by norm_num)
theorem B2112101 : Blo 622298 2112101 := bbase (se 4 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 2112101 = 396019) (by norm_num)
theorem B703093 : Blo 622298 703093 := bbase (se 5 (by rfl) ⟨32957, by rfl⟩ : syracuseStep 703093 = 65915) (by norm_num)
theorem B703129 : Blo 622298 703129 := bbase (se 2 (by rfl) ⟨263673, by rfl⟩ : syracuseStep 703129 = 527347) (by norm_num)
theorem B703165 : Blo 622298 703165 := bbase (se 3 (by rfl) ⟨131843, by rfl⟩ : syracuseStep 703165 = 263687) (by norm_num)
theorem B703201 : Blo 622298 703201 := bbase (se 2 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 703201 = 527401) (by norm_num)
theorem B703237 : Blo 622298 703237 := bbase (se 4 (by rfl) ⟨65928, by rfl⟩ : syracuseStep 703237 = 131857) (by norm_num)
theorem B703273 : Blo 622298 703273 := bbase (se 2 (by rfl) ⟨263727, by rfl⟩ : syracuseStep 703273 = 527455) (by norm_num)
theorem B703309 : Blo 622298 703309 := bbase (se 3 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 703309 = 263741) (by norm_num)
theorem B703345 : Blo 622298 703345 := bbase (se 2 (by rfl) ⟨263754, by rfl⟩ : syracuseStep 703345 = 527509) (by norm_num)
theorem B1424269 : Blo 622298 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B703381 : Blo 622298 703381 := bbase (se 6 (by rfl) ⟨16485, by rfl⟩ : syracuseStep 703381 = 32971) (by norm_num)
theorem B2702261 : Blo 622298 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B703417 : Blo 622298 703417 := bbase (se 2 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 703417 = 527563) (by norm_num)
theorem B703453 : Blo 622298 703453 := bbase (se 3 (by rfl) ⟨131897, by rfl⟩ : syracuseStep 703453 = 263795) (by norm_num)
theorem B703489 : Blo 622298 703489 := bbase (se 2 (by rfl) ⟨263808, by rfl⟩ : syracuseStep 703489 = 527617) (by norm_num)
theorem B2112533 : Blo 622298 2112533 := bbase (se 6 (by rfl) ⟨49512, by rfl⟩ : syracuseStep 2112533 = 99025) (by norm_num)
theorem B703525 : Blo 622298 703525 := bbase (se 4 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 703525 = 131911) (by norm_num)
theorem B703561 : Blo 622298 703561 := bbase (se 2 (by rfl) ⟨263835, by rfl⟩ : syracuseStep 703561 = 527671) (by norm_num)
theorem B703597 : Blo 622298 703597 := bbase (se 3 (by rfl) ⟨131924, by rfl⟩ : syracuseStep 703597 = 263849) (by norm_num)
theorem B703633 : Blo 622298 703633 := bbase (se 2 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 703633 = 527725) (by norm_num)
theorem B703669 : Blo 622298 703669 := bbase (se 5 (by rfl) ⟨32984, by rfl⟩ : syracuseStep 703669 = 65969) (by norm_num)
theorem B998605 : Blo 622298 998605 := bbase (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) (by norm_num)
theorem B703705 : Blo 622298 703705 := bbase (se 2 (by rfl) ⟨263889, by rfl⟩ : syracuseStep 703705 = 527779) (by norm_num)
theorem B703741 : Blo 622298 703741 := bbase (se 3 (by rfl) ⟨131951, by rfl⟩ : syracuseStep 703741 = 263903) (by norm_num)
theorem B703777 : Blo 622298 703777 := bbase (se 2 (by rfl) ⟨263916, by rfl⟩ : syracuseStep 703777 = 527833) (by norm_num)
theorem B703813 : Blo 622298 703813 := bbase (se 4 (by rfl) ⟨65982, by rfl⟩ : syracuseStep 703813 = 131965) (by norm_num)
theorem B7585109 : Blo 622298 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B3161429 : Blo 622298 3161429 := bbase (se 11 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 3161429 = 4631) (by norm_num)
theorem B703849 : Blo 622298 703849 := bbase (se 2 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 703849 = 527887) (by norm_num)
theorem B703885 : Blo 622298 703885 := bbase (se 3 (by rfl) ⟨131978, by rfl⟩ : syracuseStep 703885 = 263957) (by norm_num)
theorem B703921 : Blo 622298 703921 := bbase (se 2 (by rfl) ⟨263970, by rfl⟩ : syracuseStep 703921 = 527941) (by norm_num)
theorem B2244037 : Blo 622298 2244037 := bbase (se 4 (by rfl) ⟨210378, by rfl⟩ : syracuseStep 2244037 = 420757) (by norm_num)
theorem B2112965 : Blo 622298 2112965 := bbase (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) (by norm_num)
theorem B703957 : Blo 622298 703957 := bbase (se 7 (by rfl) ⟨8249, by rfl⟩ : syracuseStep 703957 = 16499) (by norm_num)
theorem B703993 : Blo 622298 703993 := bbase (se 2 (by rfl) ⟨263997, by rfl⟩ : syracuseStep 703993 = 527995) (by norm_num)
theorem B2375189 : Blo 622298 2375189 := bbase (se 6 (by rfl) ⟨55668, by rfl⟩ : syracuseStep 2375189 = 111337) (by norm_num)
theorem B704029 : Blo 622298 704029 := bbase (se 3 (by rfl) ⟨132005, by rfl⟩ : syracuseStep 704029 = 264011) (by norm_num)
theorem B704065 : Blo 622298 704065 := bbase (se 2 (by rfl) ⟨264024, by rfl⟩ : syracuseStep 704065 = 528049) (by norm_num)
theorem B933461 : Blo 622298 933461 := bbase (se 8 (by rfl) ⟨5469, by rfl⟩ : syracuseStep 933461 = 10939) (by norm_num)
theorem B704101 : Blo 622298 704101 := bbase (se 4 (by rfl) ⟨66009, by rfl⟩ : syracuseStep 704101 = 132019) (by norm_num)
theorem B933485 : Blo 622298 933485 := bbase (se 3 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 933485 = 350057) (by norm_num)
theorem B999029 : Blo 622298 999029 := bbase (se 5 (by rfl) ⟨46829, by rfl⟩ : syracuseStep 999029 = 93659) (by norm_num)
theorem B933509 : Blo 622298 933509 := bbase (se 4 (by rfl) ⟨87516, by rfl⟩ : syracuseStep 933509 = 175033) (by norm_num)
theorem B704137 : Blo 622298 704137 := bbase (se 2 (by rfl) ⟨264051, by rfl⟩ : syracuseStep 704137 = 528103) (by norm_num)
theorem B933533 : Blo 622298 933533 := bbase (se 3 (by rfl) ⟨175037, by rfl⟩ : syracuseStep 933533 = 350075) (by norm_num)
theorem B802477 : Blo 622298 802477 := bbase (se 3 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 802477 = 300929) (by norm_num)
theorem B704173 : Blo 622298 704173 := bbase (se 3 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 704173 = 264065) (by norm_num)
theorem B933557 : Blo 622298 933557 := bbase (se 5 (by rfl) ⟨43760, by rfl⟩ : syracuseStep 933557 = 87521) (by norm_num)
theorem B933581 : Blo 622298 933581 := bbase (se 3 (by rfl) ⟨175046, by rfl⟩ : syracuseStep 933581 = 350093) (by norm_num)
theorem B704209 : Blo 622298 704209 := bbase (se 2 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 704209 = 528157) (by norm_num)
theorem B24592085 : Blo 622298 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B933605 : Blo 622298 933605 := bbase (se 4 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 933605 = 175051) (by norm_num)
theorem B704245 : Blo 622298 704245 := bbase (se 5 (by rfl) ⟨33011, by rfl⟩ : syracuseStep 704245 = 66023) (by norm_num)
theorem B933629 : Blo 622298 933629 := bbase (se 3 (by rfl) ⟨175055, by rfl⟩ : syracuseStep 933629 = 350111) (by norm_num)
theorem B1687301 : Blo 622298 1687301 := bbase (se 4 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 1687301 = 316369) (by norm_num)
theorem B933653 : Blo 622298 933653 := bbase (se 6 (by rfl) ⟨21882, by rfl⟩ : syracuseStep 933653 = 43765) (by norm_num)
theorem B704281 : Blo 622298 704281 := bbase (se 2 (by rfl) ⟨264105, by rfl⟩ : syracuseStep 704281 = 528211) (by norm_num)
theorem B933677 : Blo 622298 933677 := bbase (se 3 (by rfl) ⟨175064, by rfl⟩ : syracuseStep 933677 = 350129) (by norm_num)
theorem B4570933 : Blo 622298 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B2375477 : Blo 622298 2375477 := bbase (se 5 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 2375477 = 222701) (by norm_num)
theorem B704317 : Blo 622298 704317 := bbase (se 3 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 704317 = 264119) (by norm_num)
theorem B933701 : Blo 622298 933701 := bbase (se 4 (by rfl) ⟨87534, by rfl⟩ : syracuseStep 933701 = 175069) (by norm_num)
theorem B933725 : Blo 622298 933725 := bbase (se 3 (by rfl) ⟨175073, by rfl⟩ : syracuseStep 933725 = 350147) (by norm_num)
theorem B704353 : Blo 622298 704353 := bbase (se 2 (by rfl) ⟨264132, by rfl⟩ : syracuseStep 704353 = 528265) (by norm_num)
theorem B933749 : Blo 622298 933749 := bbase (se 5 (by rfl) ⟨43769, by rfl⟩ : syracuseStep 933749 = 87539) (by norm_num)
theorem B2113397 : Blo 622298 2113397 := bbase (se 5 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 2113397 = 198131) (by norm_num)
theorem B704389 : Blo 622298 704389 := bbase (se 4 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 704389 = 132073) (by norm_num)
theorem B933773 : Blo 622298 933773 := bbase (se 3 (by rfl) ⟨175082, by rfl⟩ : syracuseStep 933773 = 350165) (by norm_num)
theorem B999317 : Blo 622298 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B933797 : Blo 622298 933797 := bbase (se 4 (by rfl) ⟨87543, by rfl⟩ : syracuseStep 933797 = 175087) (by norm_num)
theorem B704425 : Blo 622298 704425 := bbase (se 2 (by rfl) ⟨264159, by rfl⟩ : syracuseStep 704425 = 528319) (by norm_num)
theorem B933821 : Blo 622298 933821 := bbase (se 3 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 933821 = 350183) (by norm_num)
theorem B2670533 : Blo 622298 2670533 := bbase (se 4 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 2670533 = 500725) (by norm_num)
theorem B704461 : Blo 622298 704461 := bbase (se 3 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 704461 = 264173) (by norm_num)
theorem B1425365 : Blo 622298 1425365 := bbase (se 7 (by rfl) ⟨16703, by rfl⟩ : syracuseStep 1425365 = 33407) (by norm_num)
theorem B933845 : Blo 622298 933845 := bbase (se 7 (by rfl) ⟨10943, by rfl⟩ : syracuseStep 933845 = 21887) (by norm_num)
theorem B933869 : Blo 622298 933869 := bbase (se 3 (by rfl) ⟨175100, by rfl⟩ : syracuseStep 933869 = 350201) (by norm_num)
theorem B704497 : Blo 622298 704497 := bbase (se 2 (by rfl) ⟨264186, by rfl⟩ : syracuseStep 704497 = 528373) (by norm_num)
theorem B933893 : Blo 622298 933893 := bbase (se 4 (by rfl) ⟨87552, by rfl⟩ : syracuseStep 933893 = 175105) (by norm_num)
theorem B704533 : Blo 622298 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B933917 : Blo 622298 933917 := bbase (se 3 (by rfl) ⟨175109, by rfl⟩ : syracuseStep 933917 = 350219) (by norm_num)
theorem B933941 : Blo 622298 933941 := bbase (se 5 (by rfl) ⟨43778, by rfl⟩ : syracuseStep 933941 = 87557) (by norm_num)
theorem B704569 : Blo 622298 704569 := bbase (se 2 (by rfl) ⟨264213, by rfl⟩ : syracuseStep 704569 = 528427) (by norm_num)
theorem B802877 : Blo 622298 802877 := bbase (se 3 (by rfl) ⟨150539, by rfl⟩ : syracuseStep 802877 = 301079) (by norm_num)
theorem B933965 : Blo 622298 933965 := bbase (se 3 (by rfl) ⟨175118, by rfl⟩ : syracuseStep 933965 = 350237) (by norm_num)
theorem B933989 : Blo 622298 933989 := bbase (se 4 (by rfl) ⟨87561, by rfl⟩ : syracuseStep 933989 = 175123) (by norm_num)
theorem B934013 : Blo 622298 934013 := bbase (se 3 (by rfl) ⟨175127, by rfl⟩ : syracuseStep 934013 = 350255) (by norm_num)
theorem B934037 : Blo 622298 934037 := bbase (se 6 (by rfl) ⟨21891, by rfl⟩ : syracuseStep 934037 = 43783) (by norm_num)
theorem B1425557 : Blo 622298 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B2244773 : Blo 622298 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B934061 : Blo 622298 934061 := bbase (se 3 (by rfl) ⟨175136, by rfl⟩ : syracuseStep 934061 = 350273) (by norm_num)
theorem B5062837 : Blo 622298 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B934085 : Blo 622298 934085 := bbase (se 4 (by rfl) ⟨87570, by rfl⟩ : syracuseStep 934085 = 175141) (by norm_num)
theorem B934109 : Blo 622298 934109 := bbase (se 3 (by rfl) ⟨175145, by rfl⟩ : syracuseStep 934109 = 350291) (by norm_num)
theorem B934133 : Blo 622298 934133 := bbase (se 5 (by rfl) ⟨43787, by rfl⟩ : syracuseStep 934133 = 87575) (by norm_num)
theorem B934157 : Blo 622298 934157 := bbase (se 3 (by rfl) ⟨175154, by rfl⟩ : syracuseStep 934157 = 350309) (by norm_num)
theorem B934181 : Blo 622298 934181 := bbase (se 4 (by rfl) ⟨87579, by rfl⟩ : syracuseStep 934181 = 175159) (by norm_num)
theorem B934205 : Blo 622298 934205 := bbase (se 3 (by rfl) ⟨175163, by rfl⟩ : syracuseStep 934205 = 350327) (by norm_num)
theorem B934229 : Blo 622298 934229 := bbase (se 10 (by rfl) ⟨1368, by rfl⟩ : syracuseStep 934229 = 2737) (by norm_num)
theorem B934253 : Blo 622298 934253 := bbase (se 3 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 934253 = 350345) (by norm_num)
theorem B934277 : Blo 622298 934277 := bbase (se 4 (by rfl) ⟨87588, by rfl⟩ : syracuseStep 934277 = 175177) (by norm_num)
theorem B934301 : Blo 622298 934301 := bbase (se 3 (by rfl) ⟨175181, by rfl⟩ : syracuseStep 934301 = 350363) (by norm_num)
theorem B934325 : Blo 622298 934325 := bbase (se 5 (by rfl) ⟨43796, by rfl⟩ : syracuseStep 934325 = 87593) (by norm_num)
theorem B934349 : Blo 622298 934349 := bbase (se 3 (by rfl) ⟨175190, by rfl⟩ : syracuseStep 934349 = 350381) (by norm_num)
theorem B934373 : Blo 622298 934373 := bbase (se 4 (by rfl) ⟨87597, by rfl⟩ : syracuseStep 934373 = 175195) (by norm_num)
theorem B934397 : Blo 622298 934397 := bbase (se 3 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 934397 = 350399) (by norm_num)
theorem B3195413 : Blo 622298 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B934421 : Blo 622298 934421 := bbase (se 6 (by rfl) ⟨21900, by rfl⟩ : syracuseStep 934421 = 43801) (by norm_num)
theorem B934445 : Blo 622298 934445 := bbase (se 3 (by rfl) ⟨175208, by rfl⟩ : syracuseStep 934445 = 350417) (by norm_num)
theorem B934469 : Blo 622298 934469 := bbase (se 4 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 934469 = 175213) (by norm_num)
theorem B934493 : Blo 622298 934493 := bbase (se 3 (by rfl) ⟨175217, by rfl⟩ : syracuseStep 934493 = 350435) (by norm_num)
theorem B3162725 : Blo 622298 3162725 := bbase (se 4 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 3162725 = 593011) (by norm_num)
theorem B934517 : Blo 622298 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B1688197 : Blo 622298 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B934541 : Blo 622298 934541 := bbase (se 3 (by rfl) ⟨175226, by rfl⟩ : syracuseStep 934541 = 350453) (by norm_num)
theorem B934565 : Blo 622298 934565 := bbase (se 4 (by rfl) ⟨87615, by rfl⟩ : syracuseStep 934565 = 175231) (by norm_num)
theorem B1000117 : Blo 622298 1000117 := bbase (se 5 (by rfl) ⟨46880, by rfl⟩ : syracuseStep 1000117 = 93761) (by norm_num)
theorem B934589 : Blo 622298 934589 := bbase (se 3 (by rfl) ⟨175235, by rfl⟩ : syracuseStep 934589 = 350471) (by norm_num)
theorem B934613 : Blo 622298 934613 := bbase (se 7 (by rfl) ⟨10952, by rfl⟩ : syracuseStep 934613 = 21905) (by norm_num)
theorem B934637 : Blo 622298 934637 := bbase (se 3 (by rfl) ⟨175244, by rfl⟩ : syracuseStep 934637 = 350489) (by norm_num)
theorem B934661 : Blo 622298 934661 := bbase (se 4 (by rfl) ⟨87624, by rfl⟩ : syracuseStep 934661 = 175249) (by norm_num)
theorem B2999045 : Blo 622298 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B934685 : Blo 622298 934685 := bbase (se 3 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 934685 = 350507) (by norm_num)
theorem B934709 : Blo 622298 934709 := bbase (se 5 (by rfl) ⟨43814, by rfl⟩ : syracuseStep 934709 = 87629) (by norm_num)
theorem B934733 : Blo 622298 934733 := bbase (se 3 (by rfl) ⟨175262, by rfl⟩ : syracuseStep 934733 = 350525) (by norm_num)
theorem B2245477 : Blo 622298 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B934757 : Blo 622298 934757 := bbase (se 4 (by rfl) ⟨87633, by rfl⟩ : syracuseStep 934757 = 175267) (by norm_num)
theorem B934781 : Blo 622298 934781 := bbase (se 3 (by rfl) ⟨175271, by rfl⟩ : syracuseStep 934781 = 350543) (by norm_num)
theorem B934805 : Blo 622298 934805 := bbase (se 6 (by rfl) ⟨21909, by rfl⟩ : syracuseStep 934805 = 43819) (by norm_num)
theorem B934829 : Blo 622298 934829 := bbase (se 3 (by rfl) ⟨175280, by rfl⟩ : syracuseStep 934829 = 350561) (by norm_num)
theorem B934853 : Blo 622298 934853 := bbase (se 4 (by rfl) ⟨87642, by rfl⟩ : syracuseStep 934853 = 175285) (by norm_num)
theorem B2376661 : Blo 622298 2376661 := bbase (se 7 (by rfl) ⟨27851, by rfl⟩ : syracuseStep 2376661 = 55703) (by norm_num)
theorem B934877 : Blo 622298 934877 := bbase (se 3 (by rfl) ⟨175289, by rfl⟩ : syracuseStep 934877 = 350579) (by norm_num)
theorem B934901 : Blo 622298 934901 := bbase (se 5 (by rfl) ⟨43823, by rfl⟩ : syracuseStep 934901 = 87647) (by norm_num)
theorem B934925 : Blo 622298 934925 := bbase (se 3 (by rfl) ⟨175298, by rfl⟩ : syracuseStep 934925 = 350597) (by norm_num)
theorem B934949 : Blo 622298 934949 := bbase (se 4 (by rfl) ⟨87651, by rfl⟩ : syracuseStep 934949 = 175303) (by norm_num)
theorem B934973 : Blo 622298 934973 := bbase (se 3 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 934973 = 350615) (by norm_num)
theorem B934997 : Blo 622298 934997 := bbase (se 8 (by rfl) ⟨5478, by rfl⟩ : syracuseStep 934997 = 10957) (by norm_num)
theorem B935021 : Blo 622298 935021 := bbase (se 3 (by rfl) ⟨175316, by rfl⟩ : syracuseStep 935021 = 350633) (by norm_num)
theorem B935045 : Blo 622298 935045 := bbase (se 4 (by rfl) ⟨87660, by rfl⟩ : syracuseStep 935045 = 175321) (by norm_num)
theorem B935069 : Blo 622298 935069 := bbase (se 3 (by rfl) ⟨175325, by rfl⟩ : syracuseStep 935069 = 350651) (by norm_num)
theorem B935093 : Blo 622298 935093 := bbase (se 5 (by rfl) ⟨43832, by rfl⟩ : syracuseStep 935093 = 87665) (by norm_num)
theorem B935117 : Blo 622298 935117 := bbase (se 3 (by rfl) ⟨175334, by rfl⟩ : syracuseStep 935117 = 350669) (by norm_num)
theorem B1000669 : Blo 622298 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B935141 : Blo 622298 935141 := bbase (se 4 (by rfl) ⟨87669, by rfl⟩ : syracuseStep 935141 = 175339) (by norm_num)
theorem B935165 : Blo 622298 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B2376965 : Blo 622298 2376965 := bbase (se 4 (by rfl) ⟨222840, by rfl⟩ : syracuseStep 2376965 = 445681) (by norm_num)
theorem B935189 : Blo 622298 935189 := bbase (se 6 (by rfl) ⟨21918, by rfl⟩ : syracuseStep 935189 = 43837) (by norm_num)
theorem B935213 : Blo 622298 935213 := bbase (se 3 (by rfl) ⟨175352, by rfl⟩ : syracuseStep 935213 = 350705) (by norm_num)
theorem B935237 : Blo 622298 935237 := bbase (se 4 (by rfl) ⟨87678, by rfl⟩ : syracuseStep 935237 = 175357) (by norm_num)
theorem B935261 : Blo 622298 935261 := bbase (se 3 (by rfl) ⟨175361, by rfl⟩ : syracuseStep 935261 = 350723) (by norm_num)
theorem B935285 : Blo 622298 935285 := bbase (se 5 (by rfl) ⟨43841, by rfl⟩ : syracuseStep 935285 = 87683) (by norm_num)
theorem B935309 : Blo 622298 935309 := bbase (se 3 (by rfl) ⟨175370, by rfl⟩ : syracuseStep 935309 = 350741) (by norm_num)
theorem B935333 : Blo 622298 935333 := bbase (se 4 (by rfl) ⟨87687, by rfl⟩ : syracuseStep 935333 = 175375) (by norm_num)
theorem B935357 : Blo 622298 935357 := bbase (se 3 (by rfl) ⟨175379, by rfl⟩ : syracuseStep 935357 = 350759) (by norm_num)
theorem B935381 : Blo 622298 935381 := bbase (se 7 (by rfl) ⟨10961, by rfl⟩ : syracuseStep 935381 = 21923) (by norm_num)
theorem B1000925 : Blo 622298 1000925 := bbase (se 3 (by rfl) ⟨187673, by rfl⟩ : syracuseStep 1000925 = 375347) (by norm_num)
theorem B935405 : Blo 622298 935405 := bbase (se 3 (by rfl) ⟨175388, by rfl⟩ : syracuseStep 935405 = 350777) (by norm_num)
theorem B935429 : Blo 622298 935429 := bbase (se 4 (by rfl) ⟨87696, by rfl⟩ : syracuseStep 935429 = 175393) (by norm_num)
theorem B935453 : Blo 622298 935453 := bbase (se 3 (by rfl) ⟨175397, by rfl⟩ : syracuseStep 935453 = 350795) (by norm_num)
theorem B935477 : Blo 622298 935477 := bbase (se 5 (by rfl) ⟨43850, by rfl⟩ : syracuseStep 935477 = 87701) (by norm_num)
theorem B935501 : Blo 622298 935501 := bbase (se 3 (by rfl) ⟨175406, by rfl⟩ : syracuseStep 935501 = 350813) (by norm_num)
theorem B935525 : Blo 622298 935525 := bbase (se 4 (by rfl) ⟨87705, by rfl⟩ : syracuseStep 935525 = 175411) (by norm_num)
theorem B935549 : Blo 622298 935549 := bbase (se 3 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 935549 = 350831) (by norm_num)
theorem B935573 : Blo 622298 935573 := bbase (se 6 (by rfl) ⟨21927, by rfl⟩ : syracuseStep 935573 = 43855) (by norm_num)
theorem B935597 : Blo 622298 935597 := bbase (se 3 (by rfl) ⟨175424, by rfl⟩ : syracuseStep 935597 = 350849) (by norm_num)
theorem B935621 : Blo 622298 935621 := bbase (se 4 (by rfl) ⟨87714, by rfl⟩ : syracuseStep 935621 = 175429) (by norm_num)
theorem B14436053 : Blo 622298 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B935645 : Blo 622298 935645 := bbase (se 3 (by rfl) ⟨175433, by rfl⟩ : syracuseStep 935645 = 350867) (by norm_num)
theorem B935669 : Blo 622298 935669 := bbase (se 5 (by rfl) ⟨43859, by rfl⟩ : syracuseStep 935669 = 87719) (by norm_num)
theorem B935693 : Blo 622298 935693 := bbase (se 3 (by rfl) ⟨175442, by rfl⟩ : syracuseStep 935693 = 350885) (by norm_num)
theorem B7096085 : Blo 622298 7096085 := bbase (se 6 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 7096085 = 332629) (by norm_num)
theorem B935717 : Blo 622298 935717 := bbase (se 4 (by rfl) ⟨87723, by rfl⟩ : syracuseStep 935717 = 175447) (by norm_num)
theorem B935741 : Blo 622298 935741 := bbase (se 3 (by rfl) ⟨175451, by rfl⟩ : syracuseStep 935741 = 350903) (by norm_num)
theorem B935765 : Blo 622298 935765 := bbase (se 9 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 935765 = 5483) (by norm_num)
theorem B2705237 : Blo 622298 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B935789 : Blo 622298 935789 := bbase (se 3 (by rfl) ⟨175460, by rfl⟩ : syracuseStep 935789 = 350921) (by norm_num)
theorem B3164021 : Blo 622298 3164021 := bbase (se 5 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 3164021 = 296627) (by norm_num)
theorem B935813 : Blo 622298 935813 := bbase (se 4 (by rfl) ⟨87732, by rfl⟩ : syracuseStep 935813 = 175465) (by norm_num)
theorem B935837 : Blo 622298 935837 := bbase (se 3 (by rfl) ⟨175469, by rfl⟩ : syracuseStep 935837 = 350939) (by norm_num)
theorem B935861 : Blo 622298 935861 := bbase (se 5 (by rfl) ⟨43868, by rfl⟩ : syracuseStep 935861 = 87737) (by norm_num)
theorem B935885 : Blo 622298 935885 := bbase (se 3 (by rfl) ⟨175478, by rfl⟩ : syracuseStep 935885 = 350957) (by norm_num)
theorem B935909 : Blo 622298 935909 := bbase (se 4 (by rfl) ⟨87741, by rfl⟩ : syracuseStep 935909 = 175483) (by norm_num)
theorem B935933 : Blo 622298 935933 := bbase (se 3 (by rfl) ⟨175487, by rfl⟩ : syracuseStep 935933 = 350975) (by norm_num)
theorem B935957 : Blo 622298 935957 := bbase (se 6 (by rfl) ⟨21936, by rfl⟩ : syracuseStep 935957 = 43873) (by norm_num)
theorem B935981 : Blo 622298 935981 := bbase (se 3 (by rfl) ⟨175496, by rfl⟩ : syracuseStep 935981 = 350993) (by norm_num)
theorem B3557429 : Blo 622298 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B936005 : Blo 622298 936005 := bbase (se 4 (by rfl) ⟨87750, by rfl⟩ : syracuseStep 936005 = 175501) (by norm_num)
theorem B936029 : Blo 622298 936029 := bbase (se 3 (by rfl) ⟨175505, by rfl⟩ : syracuseStep 936029 = 351011) (by norm_num)
theorem B936053 : Blo 622298 936053 := bbase (se 5 (by rfl) ⟨43877, by rfl⟩ : syracuseStep 936053 = 87755) (by norm_num)
theorem B936077 : Blo 622298 936077 := bbase (se 3 (by rfl) ⟨175514, by rfl⟩ : syracuseStep 936077 = 351029) (by norm_num)
theorem B1001629 : Blo 622298 1001629 := bbase (se 3 (by rfl) ⟨187805, by rfl⟩ : syracuseStep 1001629 = 375611) (by norm_num)
theorem B936101 : Blo 622298 936101 := bbase (se 4 (by rfl) ⟨87759, by rfl⟩ : syracuseStep 936101 = 175519) (by norm_num)
theorem B936125 : Blo 622298 936125 := bbase (se 3 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 936125 = 351047) (by norm_num)
theorem B936149 : Blo 622298 936149 := bbase (se 7 (by rfl) ⟨10970, by rfl⟩ : syracuseStep 936149 = 21941) (by norm_num)
theorem B1329389 : Blo 622298 1329389 := bbase (se 3 (by rfl) ⟨249260, by rfl⟩ : syracuseStep 1329389 = 498521) (by norm_num)
theorem B936173 : Blo 622298 936173 := bbase (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) (by norm_num)
theorem B1427701 : Blo 622298 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B936197 : Blo 622298 936197 := bbase (se 4 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 936197 = 175537) (by norm_num)
theorem B936221 : Blo 622298 936221 := bbase (se 3 (by rfl) ⟨175541, by rfl⟩ : syracuseStep 936221 = 351083) (by norm_num)
theorem B936245 : Blo 622298 936245 := bbase (se 5 (by rfl) ⟨43886, by rfl⟩ : syracuseStep 936245 = 87773) (by norm_num)
theorem B936269 : Blo 622298 936269 := bbase (se 3 (by rfl) ⟨175550, by rfl⟩ : syracuseStep 936269 = 351101) (by norm_num)
theorem B1329509 : Blo 622298 1329509 := bbase (se 4 (by rfl) ⟨124641, by rfl⟩ : syracuseStep 1329509 = 249283) (by norm_num)
theorem B936293 : Blo 622298 936293 := bbase (se 4 (by rfl) ⟨87777, by rfl⟩ : syracuseStep 936293 = 175555) (by norm_num)
theorem B936317 : Blo 622298 936317 := bbase (se 3 (by rfl) ⟨175559, by rfl⟩ : syracuseStep 936317 = 351119) (by norm_num)
theorem B936341 : Blo 622298 936341 := bbase (se 6 (by rfl) ⟨21945, by rfl⟩ : syracuseStep 936341 = 43891) (by norm_num)
theorem B936365 : Blo 622298 936365 := bbase (se 3 (by rfl) ⟨175568, by rfl⟩ : syracuseStep 936365 = 351137) (by norm_num)
theorem B1296821 : Blo 622298 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B936389 : Blo 622298 936389 := bbase (se 4 (by rfl) ⟨87786, by rfl⟩ : syracuseStep 936389 = 175573) (by norm_num)
theorem B936413 : Blo 622298 936413 := bbase (se 3 (by rfl) ⟨175577, by rfl⟩ : syracuseStep 936413 = 351155) (by norm_num)
theorem B936437 : Blo 622298 936437 := bbase (se 5 (by rfl) ⟨43895, by rfl⟩ : syracuseStep 936437 = 87791) (by norm_num)
theorem B936461 : Blo 622298 936461 := bbase (se 3 (by rfl) ⟨175586, by rfl⟩ : syracuseStep 936461 = 351173) (by norm_num)
theorem B936485 : Blo 622298 936485 := bbase (se 4 (by rfl) ⟨87795, by rfl⟩ : syracuseStep 936485 = 175591) (by norm_num)
theorem B936509 : Blo 622298 936509 := bbase (se 3 (by rfl) ⟨175595, by rfl⟩ : syracuseStep 936509 = 351191) (by norm_num)
theorem B1002053 : Blo 622298 1002053 := bbase (se 4 (by rfl) ⟨93942, by rfl⟩ : syracuseStep 1002053 = 187885) (by norm_num)
theorem B936533 : Blo 622298 936533 := bbase (se 8 (by rfl) ⟨5487, by rfl⟩ : syracuseStep 936533 = 10975) (by norm_num)
theorem B936557 : Blo 622298 936557 := bbase (se 3 (by rfl) ⟨175604, by rfl⟩ : syracuseStep 936557 = 351209) (by norm_num)
theorem B936581 : Blo 622298 936581 := bbase (se 4 (by rfl) ⟨87804, by rfl⟩ : syracuseStep 936581 = 175609) (by norm_num)
theorem B1067669 : Blo 622298 1067669 := bbase (se 6 (by rfl) ⟨25023, by rfl⟩ : syracuseStep 1067669 = 50047) (by norm_num)
theorem B936605 : Blo 622298 936605 := bbase (se 3 (by rfl) ⟨175613, by rfl⟩ : syracuseStep 936605 = 351227) (by norm_num)
theorem B936629 : Blo 622298 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B936653 : Blo 622298 936653 := bbase (se 3 (by rfl) ⟨175622, by rfl⟩ : syracuseStep 936653 = 351245) (by norm_num)
theorem B936677 : Blo 622298 936677 := bbase (se 4 (by rfl) ⟨87813, by rfl⟩ : syracuseStep 936677 = 175627) (by norm_num)
theorem B936701 : Blo 622298 936701 := bbase (se 3 (by rfl) ⟨175631, by rfl⟩ : syracuseStep 936701 = 351263) (by norm_num)
theorem B1428229 : Blo 622298 1428229 := bbase (se 4 (by rfl) ⟨133896, by rfl⟩ : syracuseStep 1428229 = 267793) (by norm_num)
theorem B936725 : Blo 622298 936725 := bbase (se 6 (by rfl) ⟨21954, by rfl⟩ : syracuseStep 936725 = 43909) (by norm_num)
theorem B936749 : Blo 622298 936749 := bbase (se 3 (by rfl) ⟨175640, by rfl⟩ : syracuseStep 936749 = 351281) (by norm_num)
theorem B936773 : Blo 622298 936773 := bbase (se 4 (by rfl) ⟨87822, by rfl⟩ : syracuseStep 936773 = 175645) (by norm_num)
theorem B936797 : Blo 622298 936797 := bbase (se 3 (by rfl) ⟨175649, by rfl⟩ : syracuseStep 936797 = 351299) (by norm_num)
theorem B1002341 : Blo 622298 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B936821 : Blo 622298 936821 := bbase (se 5 (by rfl) ⟨43913, by rfl⟩ : syracuseStep 936821 = 87827) (by norm_num)
theorem B936845 : Blo 622298 936845 := bbase (se 3 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 936845 = 351317) (by norm_num)
theorem B936869 : Blo 622298 936869 := bbase (se 4 (by rfl) ⟨87831, by rfl⟩ : syracuseStep 936869 = 175663) (by norm_num)
theorem B936893 : Blo 622298 936893 := bbase (se 3 (by rfl) ⟨175667, by rfl⟩ : syracuseStep 936893 = 351335) (by norm_num)
theorem B936917 : Blo 622298 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B1330141 : Blo 622298 1330141 := bbase (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) (by norm_num)
theorem B936941 : Blo 622298 936941 := bbase (se 3 (by rfl) ⟨175676, by rfl⟩ : syracuseStep 936941 = 351353) (by norm_num)
theorem B936965 : Blo 622298 936965 := bbase (se 4 (by rfl) ⟨87840, by rfl⟩ : syracuseStep 936965 = 175681) (by norm_num)
theorem B936989 : Blo 622298 936989 := bbase (se 3 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 936989 = 351371) (by norm_num)
theorem B937013 : Blo 622298 937013 := bbase (se 5 (by rfl) ⟨43922, by rfl⟩ : syracuseStep 937013 = 87845) (by norm_num)
theorem B1002565 : Blo 622298 1002565 := bbase (se 4 (by rfl) ⟨93990, by rfl⟩ : syracuseStep 1002565 = 187981) (by norm_num)
theorem B937037 : Blo 622298 937037 := bbase (se 3 (by rfl) ⟨175694, by rfl⟩ : syracuseStep 937037 = 351389) (by norm_num)
theorem B937061 : Blo 622298 937061 := bbase (se 4 (by rfl) ⟨87849, by rfl⟩ : syracuseStep 937061 = 175699) (by norm_num)
theorem B937085 : Blo 622298 937085 := bbase (se 3 (by rfl) ⟨175703, by rfl⟩ : syracuseStep 937085 = 351407) (by norm_num)
theorem B3165317 : Blo 622298 3165317 := bbase (se 4 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 3165317 = 593497) (by norm_num)
theorem B937109 : Blo 622298 937109 := bbase (se 6 (by rfl) ⟨21963, by rfl⟩ : syracuseStep 937109 = 43927) (by norm_num)
theorem B937133 : Blo 622298 937133 := bbase (se 3 (by rfl) ⟨175712, by rfl⟩ : syracuseStep 937133 = 351425) (by norm_num)
theorem B937157 : Blo 622298 937157 := bbase (se 4 (by rfl) ⟨87858, by rfl⟩ : syracuseStep 937157 = 175717) (by norm_num)
theorem B3558613 : Blo 622298 3558613 := bbase (se 7 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 3558613 = 83405) (by norm_num)
theorem B937181 : Blo 622298 937181 := bbase (se 3 (by rfl) ⟨175721, by rfl⟩ : syracuseStep 937181 = 351443) (by norm_num)
theorem B937205 : Blo 622298 937205 := bbase (se 5 (by rfl) ⟨43931, by rfl⟩ : syracuseStep 937205 = 87863) (by norm_num)
theorem B937229 : Blo 622298 937229 := bbase (se 3 (by rfl) ⟨175730, by rfl⟩ : syracuseStep 937229 = 351461) (by norm_num)
theorem B937253 : Blo 622298 937253 := bbase (se 4 (by rfl) ⟨87867, by rfl⟩ : syracuseStep 937253 = 175735) (by norm_num)
theorem B937277 : Blo 622298 937277 := bbase (se 3 (by rfl) ⟨175739, by rfl⟩ : syracuseStep 937277 = 351479) (by norm_num)
theorem B937301 : Blo 622298 937301 := bbase (se 11 (by rfl) ⟨686, by rfl⟩ : syracuseStep 937301 = 1373) (by norm_num)
theorem B937325 : Blo 622298 937325 := bbase (se 3 (by rfl) ⟨175748, by rfl⟩ : syracuseStep 937325 = 351497) (by norm_num)
theorem B937349 : Blo 622298 937349 := bbase (se 4 (by rfl) ⟨87876, by rfl⟩ : syracuseStep 937349 = 175753) (by norm_num)
theorem B937373 : Blo 622298 937373 := bbase (se 3 (by rfl) ⟨175757, by rfl⟩ : syracuseStep 937373 = 351515) (by norm_num)
theorem B937397 : Blo 622298 937397 := bbase (se 5 (by rfl) ⟨43940, by rfl⟩ : syracuseStep 937397 = 87881) (by norm_num)
theorem B937421 : Blo 622298 937421 := bbase (se 3 (by rfl) ⟨175766, by rfl⟩ : syracuseStep 937421 = 351533) (by norm_num)
theorem B937445 : Blo 622298 937445 := bbase (se 4 (by rfl) ⟨87885, by rfl⟩ : syracuseStep 937445 = 175771) (by norm_num)
theorem B937469 : Blo 622298 937469 := bbase (se 3 (by rfl) ⟨175775, by rfl⟩ : syracuseStep 937469 = 351551) (by norm_num)
theorem B937493 : Blo 622298 937493 := bbase (se 6 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 937493 = 43945) (by norm_num)
theorem B937517 : Blo 622298 937517 := bbase (se 3 (by rfl) ⟨175784, by rfl⟩ : syracuseStep 937517 = 351569) (by norm_num)
theorem B937541 : Blo 622298 937541 := bbase (se 4 (by rfl) ⟨87894, by rfl⟩ : syracuseStep 937541 = 175789) (by norm_num)
theorem B937565 : Blo 622298 937565 := bbase (se 3 (by rfl) ⟨175793, by rfl⟩ : syracuseStep 937565 = 351587) (by norm_num)
theorem B937589 : Blo 622298 937589 := bbase (se 5 (by rfl) ⟨43949, by rfl⟩ : syracuseStep 937589 = 87899) (by norm_num)
theorem B937613 : Blo 622298 937613 := bbase (se 3 (by rfl) ⟨175802, by rfl⟩ : syracuseStep 937613 = 351605) (by norm_num)
theorem B937637 : Blo 622298 937637 := bbase (se 4 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 937637 = 175807) (by norm_num)
theorem B937661 : Blo 622298 937661 := bbase (se 3 (by rfl) ⟨175811, by rfl⟩ : syracuseStep 937661 = 351623) (by norm_num)
theorem B937685 : Blo 622298 937685 := bbase (se 7 (by rfl) ⟨10988, by rfl⟩ : syracuseStep 937685 = 21977) (by norm_num)
theorem B937709 : Blo 622298 937709 := bbase (se 3 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 937709 = 351641) (by norm_num)
theorem B937733 : Blo 622298 937733 := bbase (se 4 (by rfl) ⟨87912, by rfl⟩ : syracuseStep 937733 = 175825) (by norm_num)
theorem B937757 : Blo 622298 937757 := bbase (se 3 (by rfl) ⟨175829, by rfl⟩ : syracuseStep 937757 = 351659) (by norm_num)
theorem B937781 : Blo 622298 937781 := bbase (se 5 (by rfl) ⟨43958, by rfl⟩ : syracuseStep 937781 = 87917) (by norm_num)
theorem B937805 : Blo 622298 937805 := bbase (se 3 (by rfl) ⟨175838, by rfl⟩ : syracuseStep 937805 = 351677) (by norm_num)
theorem B1331029 : Blo 622298 1331029 := bbase (se 9 (by rfl) ⟨3899, by rfl⟩ : syracuseStep 1331029 = 7799) (by norm_num)
theorem B3002197 : Blo 622298 3002197 := bbase (se 9 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 3002197 = 17591) (by norm_num)
theorem B937829 : Blo 622298 937829 := bbase (se 4 (by rfl) ⟨87921, by rfl⟩ : syracuseStep 937829 = 175843) (by norm_num)
theorem B937853 : Blo 622298 937853 := bbase (se 3 (by rfl) ⟨175847, by rfl⟩ : syracuseStep 937853 = 351695) (by norm_num)
theorem B2674565 : Blo 622298 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B642961 : Blo 622298 642961 := bbase (se 2 (by rfl) ⟨241110, by rfl⟩ : syracuseStep 642961 = 482221) (by norm_num)
theorem B937877 : Blo 622298 937877 := bbase (se 6 (by rfl) ⟨21981, by rfl⟩ : syracuseStep 937877 = 43963) (by norm_num)
theorem B937901 : Blo 622298 937901 := bbase (se 3 (by rfl) ⟨175856, by rfl⟩ : syracuseStep 937901 = 351713) (by norm_num)
theorem B937925 : Blo 622298 937925 := bbase (se 4 (by rfl) ⟨87930, by rfl⟩ : syracuseStep 937925 = 175861) (by norm_num)
theorem B1331149 : Blo 622298 1331149 := bbase (se 3 (by rfl) ⟨249590, by rfl⟩ : syracuseStep 1331149 = 499181) (by norm_num)
theorem B937949 : Blo 622298 937949 := bbase (se 3 (by rfl) ⟨175865, by rfl⟩ : syracuseStep 937949 = 351731) (by norm_num)
theorem B937973 : Blo 622298 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B937997 : Blo 622298 937997 := bbase (se 3 (by rfl) ⟨175874, by rfl⟩ : syracuseStep 937997 = 351749) (by norm_num)
theorem B938021 : Blo 622298 938021 := bbase (se 4 (by rfl) ⟨87939, by rfl⟩ : syracuseStep 938021 = 175879) (by norm_num)
theorem B938045 : Blo 622298 938045 := bbase (se 3 (by rfl) ⟨175883, by rfl⟩ : syracuseStep 938045 = 351767) (by norm_num)
theorem B938069 : Blo 622298 938069 := bbase (se 8 (by rfl) ⟨5496, by rfl⟩ : syracuseStep 938069 = 10993) (by norm_num)
theorem B938093 : Blo 622298 938093 := bbase (se 3 (by rfl) ⟨175892, by rfl⟩ : syracuseStep 938093 = 351785) (by norm_num)
theorem B938117 : Blo 622298 938117 := bbase (se 4 (by rfl) ⟨87948, by rfl⟩ : syracuseStep 938117 = 175897) (by norm_num)
theorem B938141 : Blo 622298 938141 := bbase (se 3 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 938141 = 351803) (by norm_num)
theorem B938165 : Blo 622298 938165 := bbase (se 5 (by rfl) ⟨43976, by rfl⟩ : syracuseStep 938165 = 87953) (by norm_num)
theorem B1331405 : Blo 622298 1331405 := bbase (se 3 (by rfl) ⟨249638, by rfl⟩ : syracuseStep 1331405 = 499277) (by norm_num)
theorem B938189 : Blo 622298 938189 := bbase (se 3 (by rfl) ⟨175910, by rfl⟩ : syracuseStep 938189 = 351821) (by norm_num)
theorem B938213 : Blo 622298 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B938237 : Blo 622298 938237 := bbase (se 3 (by rfl) ⟨175919, by rfl⟩ : syracuseStep 938237 = 351839) (by norm_num)
theorem B938261 : Blo 622298 938261 := bbase (se 6 (by rfl) ⟨21990, by rfl⟩ : syracuseStep 938261 = 43981) (by norm_num)
theorem B938285 : Blo 622298 938285 := bbase (se 3 (by rfl) ⟨175928, by rfl⟩ : syracuseStep 938285 = 351857) (by norm_num)
theorem B938309 : Blo 622298 938309 := bbase (se 4 (by rfl) ⟨87966, by rfl⟩ : syracuseStep 938309 = 175933) (by norm_num)
theorem B938333 : Blo 622298 938333 := bbase (se 3 (by rfl) ⟨175937, by rfl⟩ : syracuseStep 938333 = 351875) (by norm_num)
theorem B938357 : Blo 622298 938357 := bbase (se 5 (by rfl) ⟨43985, by rfl⟩ : syracuseStep 938357 = 87971) (by norm_num)
theorem B676237 : Blo 622298 676237 := bbase (se 3 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 676237 = 253589) (by norm_num)
theorem B938381 : Blo 622298 938381 := bbase (se 3 (by rfl) ⟨175946, by rfl⟩ : syracuseStep 938381 = 351893) (by norm_num)
theorem B3166613 : Blo 622298 3166613 := bbase (se 6 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 3166613 = 148435) (by norm_num)
theorem B938405 : Blo 622298 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B938429 : Blo 622298 938429 := bbase (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) (by norm_num)
theorem B938453 : Blo 622298 938453 := bbase (se 7 (by rfl) ⟨10997, by rfl⟩ : syracuseStep 938453 = 21995) (by norm_num)
theorem B938477 : Blo 622298 938477 := bbase (se 3 (by rfl) ⟨175964, by rfl⟩ : syracuseStep 938477 = 351929) (by norm_num)
theorem B938501 : Blo 622298 938501 := bbase (se 4 (by rfl) ⟨87984, by rfl⟩ : syracuseStep 938501 = 175969) (by norm_num)
theorem B938525 : Blo 622298 938525 := bbase (se 3 (by rfl) ⟨175973, by rfl⟩ : syracuseStep 938525 = 351947) (by norm_num)
theorem B938549 : Blo 622298 938549 := bbase (se 5 (by rfl) ⟨43994, by rfl⟩ : syracuseStep 938549 = 87989) (by norm_num)
theorem B938573 : Blo 622298 938573 := bbase (se 3 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 938573 = 351965) (by norm_num)
theorem B938597 : Blo 622298 938597 := bbase (se 4 (by rfl) ⟨87993, by rfl⟩ : syracuseStep 938597 = 175987) (by norm_num)
theorem B938621 : Blo 622298 938621 := bbase (se 3 (by rfl) ⟨175991, by rfl⟩ : syracuseStep 938621 = 351983) (by norm_num)
theorem B938645 : Blo 622298 938645 := bbase (se 6 (by rfl) ⟨21999, by rfl⟩ : syracuseStep 938645 = 43999) (by norm_num)
theorem B938669 : Blo 622298 938669 := bbase (se 3 (by rfl) ⟨176000, by rfl⟩ : syracuseStep 938669 = 352001) (by norm_num)
theorem B938693 : Blo 622298 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B938717 : Blo 622298 938717 := bbase (se 3 (by rfl) ⟨176009, by rfl⟩ : syracuseStep 938717 = 352019) (by norm_num)
theorem B1921781 : Blo 622298 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B938741 : Blo 622298 938741 := bbase (se 5 (by rfl) ⟨44003, by rfl⟩ : syracuseStep 938741 = 88007) (by norm_num)
theorem B938765 : Blo 622298 938765 := bbase (se 3 (by rfl) ⟨176018, by rfl⟩ : syracuseStep 938765 = 352037) (by norm_num)
theorem B938789 : Blo 622298 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B938813 : Blo 622298 938813 := bbase (se 3 (by rfl) ⟨176027, by rfl⟩ : syracuseStep 938813 = 352055) (by norm_num)
theorem B938837 : Blo 622298 938837 := bbase (se 9 (by rfl) ⟨2750, by rfl⟩ : syracuseStep 938837 = 5501) (by norm_num)
theorem B1495901 : Blo 622298 1495901 := bbase (se 3 (by rfl) ⟨280481, by rfl⟩ : syracuseStep 1495901 = 560963) (by norm_num)
theorem B938861 : Blo 622298 938861 := bbase (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) (by norm_num)
theorem B4739957 : Blo 622298 4739957 := bbase (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) (by norm_num)
theorem B938885 : Blo 622298 938885 := bbase (se 4 (by rfl) ⟨88020, by rfl⟩ : syracuseStep 938885 = 176041) (by norm_num)
theorem B938909 : Blo 622298 938909 := bbase (se 3 (by rfl) ⟨176045, by rfl⟩ : syracuseStep 938909 = 352091) (by norm_num)
theorem B938933 : Blo 622298 938933 := bbase (se 5 (by rfl) ⟨44012, by rfl⟩ : syracuseStep 938933 = 88025) (by norm_num)
theorem B938957 : Blo 622298 938957 := bbase (se 3 (by rfl) ⟨176054, by rfl⟩ : syracuseStep 938957 = 352109) (by norm_num)
theorem B938981 : Blo 622298 938981 := bbase (se 4 (by rfl) ⟨88029, by rfl⟩ : syracuseStep 938981 = 176059) (by norm_num)
theorem B939005 : Blo 622298 939005 := bbase (se 3 (by rfl) ⟨176063, by rfl⟩ : syracuseStep 939005 = 352127) (by norm_num)
theorem B939029 : Blo 622298 939029 := bbase (se 6 (by rfl) ⟨22008, by rfl⟩ : syracuseStep 939029 = 44017) (by norm_num)
theorem B939053 : Blo 622298 939053 := bbase (se 3 (by rfl) ⟨176072, by rfl⟩ : syracuseStep 939053 = 352145) (by norm_num)
theorem B1332293 : Blo 622298 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B939077 : Blo 622298 939077 := bbase (se 4 (by rfl) ⟨88038, by rfl⟩ : syracuseStep 939077 = 176077) (by norm_num)
theorem B939101 : Blo 622298 939101 := bbase (se 3 (by rfl) ⟨176081, by rfl⟩ : syracuseStep 939101 = 352163) (by norm_num)
theorem B939125 : Blo 622298 939125 := bbase (se 5 (by rfl) ⟨44021, by rfl⟩ : syracuseStep 939125 = 88043) (by norm_num)
theorem B1070213 : Blo 622298 1070213 := bbase (se 4 (by rfl) ⟨100332, by rfl⟩ : syracuseStep 1070213 = 200665) (by norm_num)
theorem B939149 : Blo 622298 939149 := bbase (se 3 (by rfl) ⟨176090, by rfl⟩ : syracuseStep 939149 = 352181) (by norm_num)
theorem B3560597 : Blo 622298 3560597 := bbase (se 6 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 3560597 = 166903) (by norm_num)
theorem B939173 : Blo 622298 939173 := bbase (se 4 (by rfl) ⟨88047, by rfl⟩ : syracuseStep 939173 = 176095) (by norm_num)
theorem B939197 : Blo 622298 939197 := bbase (se 3 (by rfl) ⟨176099, by rfl⟩ : syracuseStep 939197 = 352199) (by norm_num)
theorem B939221 : Blo 622298 939221 := bbase (se 7 (by rfl) ⟨11006, by rfl⟩ : syracuseStep 939221 = 22013) (by norm_num)
theorem B1496285 : Blo 622298 1496285 := bbase (se 3 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 1496285 = 561107) (by norm_num)
theorem B939245 : Blo 622298 939245 := bbase (se 3 (by rfl) ⟨176108, by rfl⟩ : syracuseStep 939245 = 352217) (by norm_num)
theorem B939269 : Blo 622298 939269 := bbase (se 4 (by rfl) ⟨88056, by rfl⟩ : syracuseStep 939269 = 176113) (by norm_num)
theorem B4510997 : Blo 622298 4510997 := bbase (se 6 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 4510997 = 211453) (by norm_num)
theorem B939293 : Blo 622298 939293 := bbase (se 3 (by rfl) ⟨176117, by rfl⟩ : syracuseStep 939293 = 352235) (by norm_num)
theorem B1332533 : Blo 622298 1332533 := bbase (se 5 (by rfl) ⟨62462, by rfl⟩ : syracuseStep 1332533 = 124925) (by norm_num)
theorem B939317 : Blo 622298 939317 := bbase (se 5 (by rfl) ⟨44030, by rfl⟩ : syracuseStep 939317 = 88061) (by norm_num)
theorem B939341 : Blo 622298 939341 := bbase (se 3 (by rfl) ⟨176126, by rfl⟩ : syracuseStep 939341 = 352253) (by norm_num)
theorem B939365 : Blo 622298 939365 := bbase (se 4 (by rfl) ⟨88065, by rfl⟩ : syracuseStep 939365 = 176131) (by norm_num)
theorem B939389 : Blo 622298 939389 := bbase (se 3 (by rfl) ⟨176135, by rfl⟩ : syracuseStep 939389 = 352271) (by norm_num)
theorem B939413 : Blo 622298 939413 := bbase (se 6 (by rfl) ⟨22017, by rfl⟩ : syracuseStep 939413 = 44035) (by norm_num)
theorem B1496485 : Blo 622298 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B939437 : Blo 622298 939437 := bbase (se 3 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 939437 = 352289) (by norm_num)
theorem B2840021 : Blo 622298 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B3167909 : Blo 622298 3167909 := bbase (se 4 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 3167909 = 593983) (by norm_num)
theorem B1201837 : Blo 622298 1201837 := bbase (se 3 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 1201837 = 450689) (by norm_num)
theorem B1333037 : Blo 622298 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B1333045 : Blo 622298 1333045 := bbase (se 5 (by rfl) ⟨62486, by rfl⟩ : syracuseStep 1333045 = 124973) (by norm_num)
theorem B1366021 : Blo 622298 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B1268093 : Blo 622298 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B5986709 : Blo 622298 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B1268141 : Blo 622298 1268141 := bbase (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) (by norm_num)
theorem B3201589 : Blo 622298 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B6085205 : Blo 622298 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B842357 : Blo 622298 842357 := bbase (se 5 (by rfl) ⟨39485, by rfl⟩ : syracuseStep 842357 = 78971) (by norm_num)
theorem B3005333 : Blo 622298 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B1334173 : Blo 622298 1334173 := bbase (se 3 (by rfl) ⟨250157, by rfl⟩ : syracuseStep 1334173 = 500315) (by norm_num)
theorem B3169205 : Blo 622298 3169205 := bbase (se 5 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 3169205 = 297113) (by norm_num)
theorem B4283317 : Blo 622298 4283317 := bbase (se 5 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 4283317 = 401561) (by norm_num)
theorem B1498061 : Blo 622298 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B1334549 : Blo 622298 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B3562805 : Blo 622298 3562805 := bbase (se 5 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 3562805 = 334013) (by norm_num)
theorem B1400237 : Blo 622298 1400237 := bbase (se 3 (by rfl) ⟨262544, by rfl⟩ : syracuseStep 1400237 = 525089) (by norm_num)
theorem B1400309 : Blo 622298 1400309 := bbase (se 5 (by rfl) ⟨65639, by rfl⟩ : syracuseStep 1400309 = 131279) (by norm_num)
theorem B1269245 : Blo 622298 1269245 := bbase (se 3 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 1269245 = 475967) (by norm_num)
theorem B843277 : Blo 622298 843277 := bbase (se 3 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 843277 = 316229) (by norm_num)
theorem B1400381 : Blo 622298 1400381 := bbase (se 3 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 1400381 = 525143) (by norm_num)
theorem B1400453 : Blo 622298 1400453 := bbase (se 4 (by rfl) ⟨131292, by rfl⟩ : syracuseStep 1400453 = 262585) (by norm_num)
theorem B1400525 : Blo 622298 1400525 := bbase (se 3 (by rfl) ⟨262598, by rfl⟩ : syracuseStep 1400525 = 525197) (by norm_num)
theorem B1236709 : Blo 622298 1236709 := bbase (se 4 (by rfl) ⟨115941, by rfl⟩ : syracuseStep 1236709 = 231883) (by norm_num)
theorem B1400597 : Blo 622298 1400597 := bbase (se 6 (by rfl) ⟨32826, by rfl⟩ : syracuseStep 1400597 = 65653) (by norm_num)
theorem B1400669 : Blo 622298 1400669 := bbase (se 3 (by rfl) ⟨262625, by rfl⟩ : syracuseStep 1400669 = 525251) (by norm_num)
theorem B1400741 : Blo 622298 1400741 := bbase (se 4 (by rfl) ⟨131319, by rfl⟩ : syracuseStep 1400741 = 262639) (by norm_num)
theorem B1400813 : Blo 622298 1400813 := bbase (se 3 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 1400813 = 525305) (by norm_num)
theorem B1400885 : Blo 622298 1400885 := bbase (se 5 (by rfl) ⟨65666, by rfl⟩ : syracuseStep 1400885 = 131333) (by norm_num)
theorem B1400957 : Blo 622298 1400957 := bbase (se 3 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 1400957 = 525359) (by norm_num)
theorem B1401029 : Blo 622298 1401029 := bbase (se 4 (by rfl) ⟨131346, by rfl⟩ : syracuseStep 1401029 = 262693) (by norm_num)
theorem B3170501 : Blo 622298 3170501 := bbase (se 4 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 3170501 = 594469) (by norm_num)
theorem B1401101 : Blo 622298 1401101 := bbase (se 3 (by rfl) ⟨262706, by rfl⟩ : syracuseStep 1401101 = 525413) (by norm_num)
theorem B1401173 : Blo 622298 1401173 := bbase (se 10 (by rfl) ⟨2052, by rfl⟩ : syracuseStep 1401173 = 4105) (by norm_num)
theorem B1499485 : Blo 622298 1499485 := bbase (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) (by norm_num)
theorem B2318725 : Blo 622298 2318725 := bbase (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) (by norm_num)
theorem B1401245 : Blo 622298 1401245 := bbase (se 3 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 1401245 = 525467) (by norm_num)
theorem B1401317 : Blo 622298 1401317 := bbase (se 4 (by rfl) ⟨131373, by rfl⟩ : syracuseStep 1401317 = 262747) (by norm_num)
theorem B10641941 : Blo 622298 10641941 := bbase (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) (by norm_num)
theorem B1401389 : Blo 622298 1401389 := bbase (se 3 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 1401389 = 525521) (by norm_num)
theorem B1401461 : Blo 622298 1401461 := bbase (se 5 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 1401461 = 131387) (by norm_num)
theorem B1401533 : Blo 622298 1401533 := bbase (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) (by norm_num)
theorem B1401605 : Blo 622298 1401605 := bbase (se 4 (by rfl) ⟨131400, by rfl⟩ : syracuseStep 1401605 = 262801) (by norm_num)
theorem B1401677 : Blo 622298 1401677 := bbase (se 3 (by rfl) ⟨262814, by rfl⟩ : syracuseStep 1401677 = 525629) (by norm_num)
theorem B2253653 : Blo 622298 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1336189 : Blo 622298 1336189 := bbase (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) (by norm_num)
theorem B1401749 : Blo 622298 1401749 := bbase (se 6 (by rfl) ⟨32853, by rfl⟩ : syracuseStep 1401749 = 65707) (by norm_num)
theorem B1369037 : Blo 622298 1369037 := bbase (se 3 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 1369037 = 513389) (by norm_num)
theorem B2253781 : Blo 622298 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B1401821 : Blo 622298 1401821 := bbase (se 3 (by rfl) ⟨262841, by rfl⟩ : syracuseStep 1401821 = 525683) (by norm_num)
theorem B1500157 : Blo 622298 1500157 := bbase (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) (by norm_num)
theorem B1401893 : Blo 622298 1401893 := bbase (se 4 (by rfl) ⟨131427, by rfl⟩ : syracuseStep 1401893 = 262855) (by norm_num)
theorem B844877 : Blo 622298 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1401965 : Blo 622298 1401965 := bbase (se 3 (by rfl) ⟨262868, by rfl⟩ : syracuseStep 1401965 = 525737) (by norm_num)
theorem B1402037 : Blo 622298 1402037 := bbase (se 5 (by rfl) ⟨65720, by rfl⟩ : syracuseStep 1402037 = 131441) (by norm_num)
theorem B1500389 : Blo 622298 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B1402109 : Blo 622298 1402109 := bbase (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) (by norm_num)
theorem B1500437 : Blo 622298 1500437 := bbase (se 6 (by rfl) ⟨35166, by rfl⟩ : syracuseStep 1500437 = 70333) (by norm_num)
theorem B1402181 : Blo 622298 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1402253 : Blo 622298 1402253 := bbase (se 3 (by rfl) ⟨262922, by rfl⟩ : syracuseStep 1402253 = 525845) (by norm_num)
theorem B1402325 : Blo 622298 1402325 := bbase (se 7 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 1402325 = 32867) (by norm_num)
theorem B1402397 : Blo 622298 1402397 := bbase (se 3 (by rfl) ⟨262949, by rfl⟩ : syracuseStep 1402397 = 525899) (by norm_num)
theorem B779825 : Blo 622298 779825 := bbase (se 2 (by rfl) ⟨292434, by rfl⟩ : syracuseStep 779825 = 584869) (by norm_num)
theorem B1402469 : Blo 622298 1402469 := bbase (se 4 (by rfl) ⟨131481, by rfl⟩ : syracuseStep 1402469 = 262963) (by norm_num)
theorem B3008117 : Blo 622298 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B1402541 : Blo 622298 1402541 := bbase (se 3 (by rfl) ⟨262976, by rfl⟩ : syracuseStep 1402541 = 525953) (by norm_num)
theorem B1402613 : Blo 622298 1402613 := bbase (se 5 (by rfl) ⟨65747, by rfl⟩ : syracuseStep 1402613 = 131495) (by norm_num)
theorem B1337077 : Blo 622298 1337077 := bbase (se 5 (by rfl) ⟨62675, by rfl⟩ : syracuseStep 1337077 = 125351) (by norm_num)
theorem B1402685 : Blo 622298 1402685 := bbase (se 3 (by rfl) ⟨263003, by rfl⟩ : syracuseStep 1402685 = 526007) (by norm_num)
theorem B1402757 : Blo 622298 1402757 := bbase (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) (by norm_num)
theorem B1402829 : Blo 622298 1402829 := bbase (se 3 (by rfl) ⟨263030, by rfl⟩ : syracuseStep 1402829 = 526061) (by norm_num)
theorem B1402901 : Blo 622298 1402901 := bbase (se 6 (by rfl) ⟨32880, by rfl⟩ : syracuseStep 1402901 = 65761) (by norm_num)
theorem B1402973 : Blo 622298 1402973 := bbase (se 3 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 1402973 = 526115) (by norm_num)
theorem B1403045 : Blo 622298 1403045 := bbase (se 4 (by rfl) ⟨131535, by rfl⟩ : syracuseStep 1403045 = 263071) (by norm_num)
theorem B1337573 : Blo 622298 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1403117 : Blo 622298 1403117 := bbase (se 3 (by rfl) ⟨263084, by rfl⟩ : syracuseStep 1403117 = 526169) (by norm_num)
theorem B1403189 : Blo 622298 1403189 := bbase (se 5 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 1403189 = 131549) (by norm_num)
theorem B1403261 : Blo 622298 1403261 := bbase (se 3 (by rfl) ⟨263111, by rfl⟩ : syracuseStep 1403261 = 526223) (by norm_num)
theorem B3467669 : Blo 622298 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B846229 : Blo 622298 846229 := bbase (se 6 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 846229 = 39667) (by norm_num)
theorem B1403333 : Blo 622298 1403333 := bbase (se 4 (by rfl) ⟨131562, by rfl⟩ : syracuseStep 1403333 = 263125) (by norm_num)
theorem B1403405 : Blo 622298 1403405 := bbase (se 3 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 1403405 = 526277) (by norm_num)
theorem B1403477 : Blo 622298 1403477 := bbase (se 8 (by rfl) ⟨8223, by rfl⟩ : syracuseStep 1403477 = 16447) (by norm_num)
theorem B846445 : Blo 622298 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B1501829 : Blo 622298 1501829 := bbase (se 4 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 1501829 = 281593) (by norm_num)
theorem B1403549 : Blo 622298 1403549 := bbase (se 3 (by rfl) ⟨263165, by rfl⟩ : syracuseStep 1403549 = 526331) (by norm_num)
theorem B5335733 : Blo 622298 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B1403621 : Blo 622298 1403621 := bbase (se 4 (by rfl) ⟨131589, by rfl⟩ : syracuseStep 1403621 = 263179) (by norm_num)
theorem B1403693 : Blo 622298 1403693 := bbase (se 3 (by rfl) ⟨263192, by rfl⟩ : syracuseStep 1403693 = 526385) (by norm_num)
theorem B1502021 : Blo 622298 1502021 := bbase (se 4 (by rfl) ⟨140814, by rfl⟩ : syracuseStep 1502021 = 281629) (by norm_num)
theorem B1403765 : Blo 622298 1403765 := bbase (se 5 (by rfl) ⟨65801, by rfl⟩ : syracuseStep 1403765 = 131603) (by norm_num)
theorem B2845621 : Blo 622298 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B1403837 : Blo 622298 1403837 := bbase (se 3 (by rfl) ⟨263219, by rfl⟩ : syracuseStep 1403837 = 526439) (by norm_num)
theorem B1600469 : Blo 622298 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B2255845 : Blo 622298 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B748541 : Blo 622298 748541 := bbase (se 3 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 748541 = 280703) (by norm_num)
theorem B1403909 : Blo 622298 1403909 := bbase (se 4 (by rfl) ⟨131616, by rfl⟩ : syracuseStep 1403909 = 263233) (by norm_num)
theorem B1403981 : Blo 622298 1403981 := bbase (se 3 (by rfl) ⟨263246, by rfl⟩ : syracuseStep 1403981 = 526493) (by norm_num)
theorem B1404053 : Blo 622298 1404053 := bbase (se 6 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 1404053 = 65815) (by norm_num)
theorem B1404125 : Blo 622298 1404125 := bbase (se 3 (by rfl) ⟨263273, by rfl⟩ : syracuseStep 1404125 = 526547) (by norm_num)
theorem B1994021 : Blo 622298 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B1404197 : Blo 622298 1404197 := bbase (se 4 (by rfl) ⟨131643, by rfl⟩ : syracuseStep 1404197 = 263287) (by norm_num)
theorem B3042613 : Blo 622298 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B748873 : Blo 622298 748873 := bbase (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) (by norm_num)
theorem B1404269 : Blo 622298 1404269 := bbase (se 3 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 1404269 = 526601) (by norm_num)
theorem B1011061 : Blo 622298 1011061 := bbase (se 5 (by rfl) ⟨47393, by rfl⟩ : syracuseStep 1011061 = 94787) (by norm_num)
theorem B1404341 : Blo 622298 1404341 := bbase (se 5 (by rfl) ⟨65828, by rfl⟩ : syracuseStep 1404341 = 131657) (by norm_num)
theorem B1404413 : Blo 622298 1404413 := bbase (se 3 (by rfl) ⟨263327, by rfl⟩ : syracuseStep 1404413 = 526655) (by norm_num)
theorem B1404485 : Blo 622298 1404485 := bbase (se 4 (by rfl) ⟨131670, by rfl⟩ : syracuseStep 1404485 = 263341) (by norm_num)
theorem B1404557 : Blo 622298 1404557 := bbase (se 3 (by rfl) ⟨263354, by rfl⟩ : syracuseStep 1404557 = 526709) (by norm_num)
theorem B1404629 : Blo 622298 1404629 := bbase (se 7 (by rfl) ⟨16460, by rfl⟩ : syracuseStep 1404629 = 32921) (by norm_num)
theorem B1404701 : Blo 622298 1404701 := bbase (se 3 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 1404701 = 526763) (by norm_num)
theorem B1404773 : Blo 622298 1404773 := bbase (se 4 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 1404773 = 263395) (by norm_num)
theorem B1404845 : Blo 622298 1404845 := bbase (se 3 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 1404845 = 526817) (by norm_num)
theorem B1896373 : Blo 622298 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1404917 : Blo 622298 1404917 := bbase (se 5 (by rfl) ⟨65855, by rfl⟩ : syracuseStep 1404917 = 131711) (by norm_num)
theorem B1929205 : Blo 622298 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B749569 : Blo 622298 749569 := bbase (se 2 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 749569 = 562177) (by norm_num)
theorem B749617 : Blo 622298 749617 := bbase (se 2 (by rfl) ⟨281106, by rfl⟩ : syracuseStep 749617 = 562213) (by norm_num)
theorem B946237 : Blo 622298 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B1404989 : Blo 622298 1404989 := bbase (se 3 (by rfl) ⟨263435, by rfl⟩ : syracuseStep 1404989 = 526871) (by norm_num)
theorem B1405061 : Blo 622298 1405061 := bbase (se 4 (by rfl) ⟨131724, by rfl⟩ : syracuseStep 1405061 = 263449) (by norm_num)
theorem B1405133 : Blo 622298 1405133 := bbase (se 3 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 1405133 = 526925) (by norm_num)
theorem B1405205 : Blo 622298 1405205 := bbase (se 6 (by rfl) ⟨32934, by rfl⟩ : syracuseStep 1405205 = 65869) (by norm_num)
theorem B1405277 : Blo 622298 1405277 := bbase (se 3 (by rfl) ⟨263489, by rfl⟩ : syracuseStep 1405277 = 526979) (by norm_num)
theorem B1405349 : Blo 622298 1405349 := bbase (se 4 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 1405349 = 263503) (by norm_num)
theorem B4747733 : Blo 622298 4747733 := bbase (se 7 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 4747733 = 111275) (by norm_num)
theorem B1405421 : Blo 622298 1405421 := bbase (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) (by norm_num)
theorem B946741 : Blo 622298 946741 := bbase (se 5 (by rfl) ⟨44378, by rfl⟩ : syracuseStep 946741 = 88757) (by norm_num)
theorem B1405493 : Blo 622298 1405493 := bbase (se 5 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 1405493 = 131765) (by norm_num)
theorem B1405565 : Blo 622298 1405565 := bbase (se 3 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 1405565 = 527087) (by norm_num)
theorem B1405637 : Blo 622298 1405637 := bbase (se 4 (by rfl) ⟨131778, by rfl⟩ : syracuseStep 1405637 = 263557) (by norm_num)
theorem B1405709 : Blo 622298 1405709 := bbase (se 3 (by rfl) ⟨263570, by rfl⟩ : syracuseStep 1405709 = 527141) (by norm_num)
theorem B1504021 : Blo 622298 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B1405781 : Blo 622298 1405781 := bbase (se 9 (by rfl) ⟨4118, by rfl⟩ : syracuseStep 1405781 = 8237) (by norm_num)
theorem B1405853 : Blo 622298 1405853 := bbase (se 3 (by rfl) ⟨263597, by rfl⟩ : syracuseStep 1405853 = 527195) (by norm_num)
theorem B1405925 : Blo 622298 1405925 := bbase (se 4 (by rfl) ⟨131805, by rfl⟩ : syracuseStep 1405925 = 263611) (by norm_num)
theorem B1405997 : Blo 622298 1405997 := bbase (se 3 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 1405997 = 527249) (by norm_num)
theorem B750665 : Blo 622298 750665 := bbase (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) (by norm_num)
theorem B1995877 : Blo 622298 1995877 := bbase (se 4 (by rfl) ⟨187113, by rfl⟩ : syracuseStep 1995877 = 374227) (by norm_num)
theorem B1406069 : Blo 622298 1406069 := bbase (se 5 (by rfl) ⟨65909, by rfl⟩ : syracuseStep 1406069 = 131819) (by norm_num)
theorem B1537165 : Blo 622298 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B3798197 : Blo 622298 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B1406141 : Blo 622298 1406141 := bbase (se 3 (by rfl) ⟨263651, by rfl⟩ : syracuseStep 1406141 = 527303) (by norm_num)
theorem B1406213 : Blo 622298 1406213 := bbase (se 4 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 1406213 = 263665) (by norm_num)
theorem B1406285 : Blo 622298 1406285 := bbase (se 3 (by rfl) ⟨263678, by rfl⟩ : syracuseStep 1406285 = 527357) (by norm_num)
theorem B1504597 : Blo 622298 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B750973 : Blo 622298 750973 := bbase (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) (by norm_num)
theorem B1406357 : Blo 622298 1406357 := bbase (se 6 (by rfl) ⟨32961, by rfl⟩ : syracuseStep 1406357 = 65923) (by norm_num)
theorem B1799605 : Blo 622298 1799605 := bbase (se 5 (by rfl) ⟨84356, by rfl⟩ : syracuseStep 1799605 = 168713) (by norm_num)
theorem B1406429 : Blo 622298 1406429 := bbase (se 3 (by rfl) ⟨263705, by rfl⟩ : syracuseStep 1406429 = 527411) (by norm_num)
theorem B1406501 : Blo 622298 1406501 := bbase (se 4 (by rfl) ⟨131859, by rfl⟩ : syracuseStep 1406501 = 263719) (by norm_num)
theorem B751141 : Blo 622298 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B5338709 : Blo 622298 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B1406573 : Blo 622298 1406573 := bbase (se 3 (by rfl) ⟨263732, by rfl⟩ : syracuseStep 1406573 = 527465) (by norm_num)
theorem B1406645 : Blo 622298 1406645 := bbase (se 5 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 1406645 = 131873) (by norm_num)
theorem B751337 : Blo 622298 751337 := bbase (se 2 (by rfl) ⟨281751, by rfl⟩ : syracuseStep 751337 = 563503) (by norm_num)
theorem B1079021 : Blo 622298 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B1603309 : Blo 622298 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B1406717 : Blo 622298 1406717 := bbase (se 3 (by rfl) ⟨263759, by rfl⟩ : syracuseStep 1406717 = 527519) (by norm_num)
theorem B1406789 : Blo 622298 1406789 := bbase (se 4 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 1406789 = 263773) (by norm_num)
theorem B5699413 : Blo 622298 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B1406861 : Blo 622298 1406861 := bbase (se 3 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 1406861 = 527573) (by norm_num)
theorem B1406933 : Blo 622298 1406933 := bbase (se 7 (by rfl) ⟨16487, by rfl⟩ : syracuseStep 1406933 = 32975) (by norm_num)
theorem B1407005 : Blo 622298 1407005 := bbase (se 3 (by rfl) ⟨263813, by rfl⟩ : syracuseStep 1407005 = 527627) (by norm_num)
theorem B1407077 : Blo 622298 1407077 := bbase (se 4 (by rfl) ⟨131913, by rfl⟩ : syracuseStep 1407077 = 263827) (by norm_num)
theorem B1407149 : Blo 622298 1407149 := bbase (se 3 (by rfl) ⟨263840, by rfl⟩ : syracuseStep 1407149 = 527681) (by norm_num)
theorem B1407221 : Blo 622298 1407221 := bbase (se 5 (by rfl) ⟨65963, by rfl⟩ : syracuseStep 1407221 = 131927) (by norm_num)
theorem B1407293 : Blo 622298 1407293 := bbase (se 3 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 1407293 = 527735) (by norm_num)
theorem B1603925 : Blo 622298 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1407365 : Blo 622298 1407365 := bbase (se 4 (by rfl) ⟨131940, by rfl⟩ : syracuseStep 1407365 = 263881) (by norm_num)
theorem B1997237 : Blo 622298 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B1407437 : Blo 622298 1407437 := bbase (se 3 (by rfl) ⟨263894, by rfl⟩ : syracuseStep 1407437 = 527789) (by norm_num)
theorem B1407509 : Blo 622298 1407509 := bbase (se 6 (by rfl) ⟨32988, by rfl⟩ : syracuseStep 1407509 = 65977) (by norm_num)
theorem B1407581 : Blo 622298 1407581 := bbase (se 3 (by rfl) ⟨263921, by rfl⟩ : syracuseStep 1407581 = 527843) (by norm_num)
theorem B1407653 : Blo 622298 1407653 := bbase (se 4 (by rfl) ⟨131967, by rfl⟩ : syracuseStep 1407653 = 263935) (by norm_num)
theorem B1407725 : Blo 622298 1407725 := bbase (se 3 (by rfl) ⟨263948, by rfl⟩ : syracuseStep 1407725 = 527897) (by norm_num)
theorem B4487957 : Blo 622298 4487957 := bbase (se 6 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 4487957 = 210373) (by norm_num)
theorem B3996469 : Blo 622298 3996469 := bbase (se 5 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 3996469 = 374669) (by norm_num)
theorem B1407797 : Blo 622298 1407797 := bbase (se 5 (by rfl) ⟨65990, by rfl⟩ : syracuseStep 1407797 = 131981) (by norm_num)
theorem B1407869 : Blo 622298 1407869 := bbase (se 3 (by rfl) ⟨263975, by rfl⟩ : syracuseStep 1407869 = 527951) (by norm_num)
theorem B3373973 : Blo 622298 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B1407941 : Blo 622298 1407941 := bbase (se 4 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 1407941 = 263989) (by norm_num)
theorem B1408013 : Blo 622298 1408013 := bbase (se 3 (by rfl) ⟨264002, by rfl⟩ : syracuseStep 1408013 = 528005) (by norm_num)
theorem B22772821 : Blo 622298 22772821 := bbase (se 8 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 22772821 = 266869) (by norm_num)
theorem B1408085 : Blo 622298 1408085 := bbase (se 8 (by rfl) ⟨8250, by rfl⟩ : syracuseStep 1408085 = 16501) (by norm_num)
theorem B1408157 : Blo 622298 1408157 := bbase (se 3 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 1408157 = 528059) (by norm_num)
theorem B1408229 : Blo 622298 1408229 := bbase (se 4 (by rfl) ⟨132021, by rfl⟩ : syracuseStep 1408229 = 264043) (by norm_num)
theorem B1408301 : Blo 622298 1408301 := bbase (se 3 (by rfl) ⟨264056, by rfl⟩ : syracuseStep 1408301 = 528113) (by norm_num)
theorem B1899877 : Blo 622298 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B1408373 : Blo 622298 1408373 := bbase (se 5 (by rfl) ⟨66017, by rfl⟩ : syracuseStep 1408373 = 132035) (by norm_num)
theorem B1408445 : Blo 622298 1408445 := bbase (se 3 (by rfl) ⟨264083, by rfl⟩ : syracuseStep 1408445 = 528167) (by norm_num)
theorem B8977877 : Blo 622298 8977877 := bbase (se 7 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 8977877 = 210419) (by norm_num)
theorem B2883077 : Blo 622298 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B1408517 : Blo 622298 1408517 := bbase (se 4 (by rfl) ⟨132048, by rfl⟩ : syracuseStep 1408517 = 264097) (by norm_num)
theorem B1408589 : Blo 622298 1408589 := bbase (se 3 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 1408589 = 528221) (by norm_num)
theorem B1408661 : Blo 622298 1408661 := bbase (se 6 (by rfl) ⟨33015, by rfl⟩ : syracuseStep 1408661 = 66031) (by norm_num)
theorem B1408733 : Blo 622298 1408733 := bbase (se 3 (by rfl) ⟨264137, by rfl⟩ : syracuseStep 1408733 = 528275) (by norm_num)
theorem B1408805 : Blo 622298 1408805 := bbase (se 4 (by rfl) ⟨132075, by rfl⟩ : syracuseStep 1408805 = 264151) (by norm_num)
theorem B1408877 : Blo 622298 1408877 := bbase (se 3 (by rfl) ⟨264164, by rfl⟩ : syracuseStep 1408877 = 528329) (by norm_num)
theorem B1408949 : Blo 622298 1408949 := bbase (se 5 (by rfl) ⟨66044, by rfl⟩ : syracuseStep 1408949 = 132089) (by norm_num)
theorem B1409021 : Blo 622298 1409021 := bbase (se 3 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 1409021 = 528383) (by norm_num)
theorem B622595 : Blo 622298 622595 := bstep (se 1 (by rfl) ⟨466946, by rfl⟩ : syracuseStep 622595 = 933893) B933893
theorem B622611 : Blo 622298 622611 := bstep (se 1 (by rfl) ⟨466958, by rfl⟩ : syracuseStep 622611 = 933917) B933917
theorem B622627 : Blo 622298 622627 := bstep (se 1 (by rfl) ⟨466970, by rfl⟩ : syracuseStep 622627 = 933941) B933941
theorem B622643 : Blo 622298 622643 := bstep (se 1 (by rfl) ⟨466982, by rfl⟩ : syracuseStep 622643 = 933965) B933965
theorem B622659 : Blo 622298 622659 := bstep (se 1 (by rfl) ⟨466994, by rfl⟩ : syracuseStep 622659 = 933989) B933989
theorem B622675 : Blo 622298 622675 := bstep (se 1 (by rfl) ⟨467006, by rfl⟩ : syracuseStep 622675 = 934013) B934013
theorem B622691 : Blo 622298 622691 := bstep (se 1 (by rfl) ⟨467018, by rfl⟩ : syracuseStep 622691 = 934037) B934037
theorem B622707 : Blo 622298 622707 := bstep (se 1 (by rfl) ⟨467030, by rfl⟩ : syracuseStep 622707 = 934061) B934061
theorem B622723 : Blo 622298 622723 := bstep (se 1 (by rfl) ⟨467042, by rfl⟩ : syracuseStep 622723 = 934085) B934085
theorem B622739 : Blo 622298 622739 := bstep (se 1 (by rfl) ⟨467054, by rfl⟩ : syracuseStep 622739 = 934109) B934109
theorem B622755 : Blo 622298 622755 := bstep (se 1 (by rfl) ⟨467066, by rfl⟩ : syracuseStep 622755 = 934133) B934133
theorem B622771 : Blo 622298 622771 := bstep (se 1 (by rfl) ⟨467078, by rfl⟩ : syracuseStep 622771 = 934157) B934157
theorem B622787 : Blo 622298 622787 := bstep (se 1 (by rfl) ⟨467090, by rfl⟩ : syracuseStep 622787 = 934181) B934181
theorem B622803 : Blo 622298 622803 := bstep (se 1 (by rfl) ⟨467102, by rfl⟩ : syracuseStep 622803 = 934205) B934205
theorem B622819 : Blo 622298 622819 := bstep (se 1 (by rfl) ⟨467114, by rfl⟩ : syracuseStep 622819 = 934229) B934229
theorem B6750449 : Blo 622298 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B622835 : Blo 622298 622835 := bstep (se 1 (by rfl) ⟨467126, by rfl⟩ : syracuseStep 622835 = 934253) B934253
theorem B622851 : Blo 622298 622851 := bstep (se 1 (by rfl) ⟨467138, by rfl⟩ : syracuseStep 622851 = 934277) B934277
theorem B3997957 : Blo 622298 3997957 := bstep (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) B749617
theorem B622867 : Blo 622298 622867 := bstep (se 1 (by rfl) ⟨467150, by rfl⟩ : syracuseStep 622867 = 934301) B934301
theorem B622883 : Blo 622298 622883 := bstep (se 1 (by rfl) ⟨467162, by rfl⟩ : syracuseStep 622883 = 934325) B934325
theorem B622899 : Blo 622298 622899 := bstep (se 1 (by rfl) ⟨467174, by rfl⟩ : syracuseStep 622899 = 934349) B934349
theorem B622915 : Blo 622298 622915 := bstep (se 1 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 622915 = 934373) B934373
theorem B622931 : Blo 622298 622931 := bstep (se 1 (by rfl) ⟨467198, by rfl⟩ : syracuseStep 622931 = 934397) B934397
theorem B2130275 : Blo 622298 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B622947 : Blo 622298 622947 := bstep (se 1 (by rfl) ⟨467210, by rfl⟩ : syracuseStep 622947 = 934421) B934421
theorem B622963 : Blo 622298 622963 := bstep (se 1 (by rfl) ⟨467222, by rfl⟩ : syracuseStep 622963 = 934445) B934445
theorem B622979 : Blo 622298 622979 := bstep (se 1 (by rfl) ⟨467234, by rfl⟩ : syracuseStep 622979 = 934469) B934469
theorem B3801485 : Blo 622298 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B622995 : Blo 622298 622995 := bstep (se 1 (by rfl) ⟨467246, by rfl⟩ : syracuseStep 622995 = 934493) B934493
theorem B623011 : Blo 622298 623011 := bstep (se 1 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 623011 = 934517) B934517
theorem B4063651 : Blo 622298 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B623027 : Blo 622298 623027 := bstep (se 1 (by rfl) ⟨467270, by rfl⟩ : syracuseStep 623027 = 934541) B934541
theorem B623043 : Blo 622298 623043 := bstep (se 1 (by rfl) ⟨467282, by rfl⟩ : syracuseStep 623043 = 934565) B934565
theorem B1999313 : Blo 622298 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B623059 : Blo 622298 623059 := bstep (se 1 (by rfl) ⟨467294, by rfl⟩ : syracuseStep 623059 = 934589) B934589
theorem B623075 : Blo 622298 623075 := bstep (se 1 (by rfl) ⟨467306, by rfl⟩ : syracuseStep 623075 = 934613) B934613
theorem B623091 : Blo 622298 623091 := bstep (se 1 (by rfl) ⟨467318, by rfl⟩ : syracuseStep 623091 = 934637) B934637
theorem B623107 : Blo 622298 623107 := bstep (se 1 (by rfl) ⟨467330, by rfl⟩ : syracuseStep 623107 = 934661) B934661
theorem B1999363 : Blo 622298 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B623123 : Blo 622298 623123 := bstep (se 1 (by rfl) ⟨467342, by rfl⟩ : syracuseStep 623123 = 934685) B934685
theorem B623139 : Blo 622298 623139 := bstep (se 1 (by rfl) ⟨467354, by rfl⟩ : syracuseStep 623139 = 934709) B934709
theorem B623155 : Blo 622298 623155 := bstep (se 1 (by rfl) ⟨467366, by rfl⟩ : syracuseStep 623155 = 934733) B934733
theorem B623171 : Blo 622298 623171 := bstep (se 1 (by rfl) ⟨467378, by rfl⟩ : syracuseStep 623171 = 934757) B934757
theorem B623187 : Blo 622298 623187 := bstep (se 1 (by rfl) ⟨467390, by rfl⟩ : syracuseStep 623187 = 934781) B934781
theorem B623203 : Blo 622298 623203 := bstep (se 1 (by rfl) ⟨467402, by rfl⟩ : syracuseStep 623203 = 934805) B934805
theorem B623219 : Blo 622298 623219 := bstep (se 1 (by rfl) ⟨467414, by rfl⟩ : syracuseStep 623219 = 934829) B934829
theorem B623235 : Blo 622298 623235 := bstep (se 1 (by rfl) ⟨467426, by rfl⟩ : syracuseStep 623235 = 934853) B934853
theorem B623251 : Blo 622298 623251 := bstep (se 1 (by rfl) ⟨467438, by rfl⟩ : syracuseStep 623251 = 934877) B934877
theorem B623267 : Blo 622298 623267 := bstep (se 1 (by rfl) ⟨467450, by rfl⟩ : syracuseStep 623267 = 934901) B934901
theorem B623283 : Blo 622298 623283 := bstep (se 1 (by rfl) ⟨467462, by rfl⟩ : syracuseStep 623283 = 934925) B934925
theorem B623299 : Blo 622298 623299 := bstep (se 1 (by rfl) ⟨467474, by rfl⟩ : syracuseStep 623299 = 934949) B934949
theorem B623315 : Blo 622298 623315 := bstep (se 1 (by rfl) ⟨467486, by rfl⟩ : syracuseStep 623315 = 934973) B934973
theorem B623331 : Blo 622298 623331 := bstep (se 1 (by rfl) ⟨467498, by rfl⟩ : syracuseStep 623331 = 934997) B934997
theorem B623347 : Blo 622298 623347 := bstep (se 1 (by rfl) ⟨467510, by rfl⟩ : syracuseStep 623347 = 935021) B935021
theorem B623363 : Blo 622298 623363 := bstep (se 1 (by rfl) ⟨467522, by rfl⟩ : syracuseStep 623363 = 935045) B935045
theorem B623379 : Blo 622298 623379 := bstep (se 1 (by rfl) ⟨467534, by rfl⟩ : syracuseStep 623379 = 935069) B935069
theorem B623395 : Blo 622298 623395 := bstep (se 1 (by rfl) ⟨467546, by rfl⟩ : syracuseStep 623395 = 935093) B935093
theorem B623411 : Blo 622298 623411 := bstep (se 1 (by rfl) ⟨467558, by rfl⟩ : syracuseStep 623411 = 935117) B935117
theorem B623427 : Blo 622298 623427 := bstep (se 1 (by rfl) ⟨467570, by rfl⟩ : syracuseStep 623427 = 935141) B935141
theorem B5342021 : Blo 622298 5342021 := bstep (se 4 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 5342021 = 1001629) B1001629
theorem B623443 : Blo 622298 623443 := bstep (se 1 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 623443 = 935165) B935165
theorem B623459 : Blo 622298 623459 := bstep (se 1 (by rfl) ⟨467594, by rfl⟩ : syracuseStep 623459 = 935189) B935189
theorem B623475 : Blo 622298 623475 := bstep (se 1 (by rfl) ⟨467606, by rfl⟩ : syracuseStep 623475 = 935213) B935213
theorem B623491 : Blo 622298 623491 := bstep (se 1 (by rfl) ⟨467618, by rfl⟩ : syracuseStep 623491 = 935237) B935237
theorem B623507 : Blo 622298 623507 := bstep (se 1 (by rfl) ⟨467630, by rfl⟩ : syracuseStep 623507 = 935261) B935261
theorem B623523 : Blo 622298 623523 := bstep (se 1 (by rfl) ⟨467642, by rfl⟩ : syracuseStep 623523 = 935285) B935285
theorem B623539 : Blo 622298 623539 := bstep (se 1 (by rfl) ⟨467654, by rfl⟩ : syracuseStep 623539 = 935309) B935309
theorem B623555 : Blo 622298 623555 := bstep (se 1 (by rfl) ⟨467666, by rfl⟩ : syracuseStep 623555 = 935333) B935333
theorem B1278929 : Blo 622298 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B623571 : Blo 622298 623571 := bstep (se 1 (by rfl) ⟨467678, by rfl⟩ : syracuseStep 623571 = 935357) B935357
theorem B623587 : Blo 622298 623587 := bstep (se 1 (by rfl) ⟨467690, by rfl⟩ : syracuseStep 623587 = 935381) B935381
theorem B623603 : Blo 622298 623603 := bstep (se 1 (by rfl) ⟨467702, by rfl⟩ : syracuseStep 623603 = 935405) B935405
theorem B623619 : Blo 622298 623619 := bstep (se 1 (by rfl) ⟨467714, by rfl⟩ : syracuseStep 623619 = 935429) B935429
theorem B623635 : Blo 622298 623635 := bstep (se 1 (by rfl) ⟨467726, by rfl⟩ : syracuseStep 623635 = 935453) B935453
theorem B623651 : Blo 622298 623651 := bstep (se 1 (by rfl) ⟨467738, by rfl⟩ : syracuseStep 623651 = 935477) B935477
theorem B623667 : Blo 622298 623667 := bstep (se 1 (by rfl) ⟨467750, by rfl⟩ : syracuseStep 623667 = 935501) B935501
theorem B623683 : Blo 622298 623683 := bstep (se 1 (by rfl) ⟨467762, by rfl⟩ : syracuseStep 623683 = 935525) B935525
theorem B623699 : Blo 622298 623699 := bstep (se 1 (by rfl) ⟨467774, by rfl⟩ : syracuseStep 623699 = 935549) B935549
theorem B623715 : Blo 622298 623715 := bstep (se 1 (by rfl) ⟨467786, by rfl⟩ : syracuseStep 623715 = 935573) B935573
theorem B623731 : Blo 622298 623731 := bstep (se 1 (by rfl) ⟨467798, by rfl⟩ : syracuseStep 623731 = 935597) B935597
theorem B623747 : Blo 622298 623747 := bstep (se 1 (by rfl) ⟨467810, by rfl⟩ : syracuseStep 623747 = 935621) B935621
theorem B623763 : Blo 622298 623763 := bstep (se 1 (by rfl) ⟨467822, by rfl⟩ : syracuseStep 623763 = 935645) B935645
theorem B623779 : Blo 622298 623779 := bstep (se 1 (by rfl) ⟨467834, by rfl⟩ : syracuseStep 623779 = 935669) B935669
theorem B623795 : Blo 622298 623795 := bstep (se 1 (by rfl) ⟨467846, by rfl⟩ : syracuseStep 623795 = 935693) B935693
theorem B623811 : Blo 622298 623811 := bstep (se 1 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 623811 = 935717) B935717
theorem B623827 : Blo 622298 623827 := bstep (se 1 (by rfl) ⟨467870, by rfl⟩ : syracuseStep 623827 = 935741) B935741
theorem B623843 : Blo 622298 623843 := bstep (se 1 (by rfl) ⟨467882, by rfl⟩ : syracuseStep 623843 = 935765) B935765
theorem B1803491 : Blo 622298 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B2852081 : Blo 622298 2852081 := bstep (se 2 (by rfl) ⟨1069530, by rfl⟩ : syracuseStep 2852081 = 2139061) B2139061
theorem B623859 : Blo 622298 623859 := bstep (se 1 (by rfl) ⟨467894, by rfl⟩ : syracuseStep 623859 = 935789) B935789
theorem B623875 : Blo 622298 623875 := bstep (se 1 (by rfl) ⟨467906, by rfl⟩ : syracuseStep 623875 = 935813) B935813
theorem B623891 : Blo 622298 623891 := bstep (se 1 (by rfl) ⟨467918, by rfl⟩ : syracuseStep 623891 = 935837) B935837
theorem B623907 : Blo 622298 623907 := bstep (se 1 (by rfl) ⟨467930, by rfl⟩ : syracuseStep 623907 = 935861) B935861
theorem B623923 : Blo 622298 623923 := bstep (se 1 (by rfl) ⟨467942, by rfl⟩ : syracuseStep 623923 = 935885) B935885
theorem B623939 : Blo 622298 623939 := bstep (se 1 (by rfl) ⟨467954, by rfl⟩ : syracuseStep 623939 = 935909) B935909
theorem B2000209 : Blo 622298 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B623955 : Blo 622298 623955 := bstep (se 1 (by rfl) ⟨467966, by rfl⟩ : syracuseStep 623955 = 935933) B935933
theorem B623971 : Blo 622298 623971 := bstep (se 1 (by rfl) ⟨467978, by rfl⟩ : syracuseStep 623971 = 935957) B935957
theorem B6423907 : Blo 622298 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B623987 : Blo 622298 623987 := bstep (se 1 (by rfl) ⟨467990, by rfl⟩ : syracuseStep 623987 = 935981) B935981
theorem B886145 : Blo 622298 886145 := bstep (se 2 (by rfl) ⟨332304, by rfl⟩ : syracuseStep 886145 = 664609) B664609
theorem B624003 : Blo 622298 624003 := bstep (se 1 (by rfl) ⟨468002, by rfl⟩ : syracuseStep 624003 = 936005) B936005
theorem B624019 : Blo 622298 624019 := bstep (se 1 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 624019 = 936029) B936029
theorem B624035 : Blo 622298 624035 := bstep (se 1 (by rfl) ⟨468026, by rfl⟩ : syracuseStep 624035 = 936053) B936053
theorem B624051 : Blo 622298 624051 := bstep (se 1 (by rfl) ⟨468038, by rfl⟩ : syracuseStep 624051 = 936077) B936077
theorem B787907 : Blo 622298 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B624067 : Blo 622298 624067 := bstep (se 1 (by rfl) ⟨468050, by rfl⟩ : syracuseStep 624067 = 936101) B936101
theorem B624083 : Blo 622298 624083 := bstep (se 1 (by rfl) ⟨468062, by rfl⟩ : syracuseStep 624083 = 936125) B936125
theorem B624099 : Blo 622298 624099 := bstep (se 1 (by rfl) ⟨468074, by rfl⟩ : syracuseStep 624099 = 936149) B936149
theorem B5342705 : Blo 622298 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B886259 : Blo 622298 886259 := bstep (se 1 (by rfl) ⟨664694, by rfl⟩ : syracuseStep 886259 = 1329389) B1329389
theorem B624115 : Blo 622298 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B624131 : Blo 622298 624131 := bstep (se 1 (by rfl) ⟨468098, by rfl⟩ : syracuseStep 624131 = 936197) B936197
theorem B1050131 : Blo 622298 1050131 := bstep (se 1 (by rfl) ⟨787598, by rfl⟩ : syracuseStep 1050131 = 1575197) B1575197
theorem B624147 : Blo 622298 624147 := bstep (se 1 (by rfl) ⟨468110, by rfl⟩ : syracuseStep 624147 = 936221) B936221
theorem B624163 : Blo 622298 624163 := bstep (se 1 (by rfl) ⟨468122, by rfl⟩ : syracuseStep 624163 = 936245) B936245
theorem B624179 : Blo 622298 624179 := bstep (se 1 (by rfl) ⟨468134, by rfl⟩ : syracuseStep 624179 = 936269) B936269
theorem B886339 : Blo 622298 886339 := bstep (se 1 (by rfl) ⟨664754, by rfl⟩ : syracuseStep 886339 = 1329509) B1329509
theorem B624195 : Blo 622298 624195 := bstep (se 1 (by rfl) ⟨468146, by rfl⟩ : syracuseStep 624195 = 936293) B936293
theorem B624211 : Blo 622298 624211 := bstep (se 1 (by rfl) ⟨468158, by rfl⟩ : syracuseStep 624211 = 936317) B936317
theorem B624227 : Blo 622298 624227 := bstep (se 1 (by rfl) ⟨468170, by rfl⟩ : syracuseStep 624227 = 936341) B936341
theorem B624243 : Blo 622298 624243 := bstep (se 1 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 624243 = 936365) B936365
theorem B624259 : Blo 622298 624259 := bstep (se 1 (by rfl) ⟨468194, by rfl⟩ : syracuseStep 624259 = 936389) B936389
theorem B1050259 : Blo 622298 1050259 := bstep (se 1 (by rfl) ⟨787694, by rfl⟩ : syracuseStep 1050259 = 1575389) B1575389
theorem B624275 : Blo 622298 624275 := bstep (se 1 (by rfl) ⟨468206, by rfl⟩ : syracuseStep 624275 = 936413) B936413
theorem B624291 : Blo 622298 624291 := bstep (se 1 (by rfl) ⟨468218, by rfl⟩ : syracuseStep 624291 = 936437) B936437
theorem B624307 : Blo 622298 624307 := bstep (se 1 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 624307 = 936461) B936461
theorem B624323 : Blo 622298 624323 := bstep (se 1 (by rfl) ⟨468242, by rfl⟩ : syracuseStep 624323 = 936485) B936485
theorem B624339 : Blo 622298 624339 := bstep (se 1 (by rfl) ⟨468254, by rfl⟩ : syracuseStep 624339 = 936509) B936509
theorem B624355 : Blo 622298 624355 := bstep (se 1 (by rfl) ⟨468266, by rfl⟩ : syracuseStep 624355 = 936533) B936533
theorem B624371 : Blo 622298 624371 := bstep (se 1 (by rfl) ⟨468278, by rfl⟩ : syracuseStep 624371 = 936557) B936557
theorem B624387 : Blo 622298 624387 := bstep (se 1 (by rfl) ⟨468290, by rfl⟩ : syracuseStep 624387 = 936581) B936581
theorem B624403 : Blo 622298 624403 := bstep (se 1 (by rfl) ⟨468302, by rfl⟩ : syracuseStep 624403 = 936605) B936605
theorem B1050401 : Blo 622298 1050401 := bstep (se 2 (by rfl) ⟨393900, by rfl⟩ : syracuseStep 1050401 = 787801) B787801
theorem B624419 : Blo 622298 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B624435 : Blo 622298 624435 := bstep (se 1 (by rfl) ⟨468326, by rfl⟩ : syracuseStep 624435 = 936653) B936653
theorem B624451 : Blo 622298 624451 := bstep (se 1 (by rfl) ⟨468338, by rfl⟩ : syracuseStep 624451 = 936677) B936677
theorem B624467 : Blo 622298 624467 := bstep (se 1 (by rfl) ⟨468350, by rfl⟩ : syracuseStep 624467 = 936701) B936701
theorem B624483 : Blo 622298 624483 := bstep (se 1 (by rfl) ⟨468362, by rfl⟩ : syracuseStep 624483 = 936725) B936725
theorem B624499 : Blo 622298 624499 := bstep (se 1 (by rfl) ⟨468374, by rfl⟩ : syracuseStep 624499 = 936749) B936749
theorem B624515 : Blo 622298 624515 := bstep (se 1 (by rfl) ⟨468386, by rfl⟩ : syracuseStep 624515 = 936773) B936773
theorem B624531 : Blo 622298 624531 := bstep (se 1 (by rfl) ⟨468398, by rfl⟩ : syracuseStep 624531 = 936797) B936797
theorem B1050529 : Blo 622298 1050529 := bstep (se 2 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 1050529 = 787897) B787897
theorem B1181603 : Blo 622298 1181603 := bstep (se 1 (by rfl) ⟨886202, by rfl⟩ : syracuseStep 1181603 = 1772405) B1772405
theorem B624547 : Blo 622298 624547 := bstep (se 1 (by rfl) ⟨468410, by rfl⟩ : syracuseStep 624547 = 936821) B936821
theorem B624563 : Blo 622298 624563 := bstep (se 1 (by rfl) ⟨468422, by rfl⟩ : syracuseStep 624563 = 936845) B936845
theorem B1050563 : Blo 622298 1050563 := bstep (se 1 (by rfl) ⟨787922, by rfl⟩ : syracuseStep 1050563 = 1575845) B1575845
theorem B624579 : Blo 622298 624579 := bstep (se 1 (by rfl) ⟨468434, by rfl⟩ : syracuseStep 624579 = 936869) B936869
theorem B624595 : Blo 622298 624595 := bstep (se 1 (by rfl) ⟨468446, by rfl⟩ : syracuseStep 624595 = 936893) B936893
theorem B624611 : Blo 622298 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B624627 : Blo 622298 624627 := bstep (se 1 (by rfl) ⟨468470, by rfl⟩ : syracuseStep 624627 = 936941) B936941
theorem B624643 : Blo 622298 624643 := bstep (se 1 (by rfl) ⟨468482, by rfl⟩ : syracuseStep 624643 = 936965) B936965
theorem B624659 : Blo 622298 624659 := bstep (se 1 (by rfl) ⟨468494, by rfl⟩ : syracuseStep 624659 = 936989) B936989
theorem B624675 : Blo 622298 624675 := bstep (se 1 (by rfl) ⟨468506, by rfl⟩ : syracuseStep 624675 = 937013) B937013
theorem B624691 : Blo 622298 624691 := bstep (se 1 (by rfl) ⟨468518, by rfl⟩ : syracuseStep 624691 = 937037) B937037
theorem B1050691 : Blo 622298 1050691 := bstep (se 1 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 1050691 = 1576037) B1576037
theorem B624707 : Blo 622298 624707 := bstep (se 1 (by rfl) ⟨468530, by rfl⟩ : syracuseStep 624707 = 937061) B937061
theorem B624723 : Blo 622298 624723 := bstep (se 1 (by rfl) ⟨468542, by rfl⟩ : syracuseStep 624723 = 937085) B937085
theorem B624739 : Blo 622298 624739 := bstep (se 1 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 624739 = 937109) B937109
theorem B886897 : Blo 622298 886897 := bstep (se 2 (by rfl) ⟨332586, by rfl⟩ : syracuseStep 886897 = 665173) B665173
theorem B624755 : Blo 622298 624755 := bstep (se 1 (by rfl) ⟨468566, by rfl⟩ : syracuseStep 624755 = 937133) B937133
theorem B788611 : Blo 622298 788611 := bstep (se 1 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 788611 = 1182917) B1182917
theorem B624771 : Blo 622298 624771 := bstep (se 1 (by rfl) ⟨468578, by rfl⟩ : syracuseStep 624771 = 937157) B937157
theorem B624787 : Blo 622298 624787 := bstep (se 1 (by rfl) ⟨468590, by rfl⟩ : syracuseStep 624787 = 937181) B937181
theorem B624803 : Blo 622298 624803 := bstep (se 1 (by rfl) ⟨468602, by rfl⟩ : syracuseStep 624803 = 937205) B937205
theorem B624819 : Blo 622298 624819 := bstep (se 1 (by rfl) ⟨468614, by rfl⟩ : syracuseStep 624819 = 937229) B937229
theorem B1181891 : Blo 622298 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B624835 : Blo 622298 624835 := bstep (se 1 (by rfl) ⟨468626, by rfl⟩ : syracuseStep 624835 = 937253) B937253
theorem B1050833 : Blo 622298 1050833 := bstep (se 2 (by rfl) ⟨394062, by rfl⟩ : syracuseStep 1050833 = 788125) B788125
theorem B624851 : Blo 622298 624851 := bstep (se 1 (by rfl) ⟨468638, by rfl⟩ : syracuseStep 624851 = 937277) B937277
theorem B788707 : Blo 622298 788707 := bstep (se 1 (by rfl) ⟨591530, by rfl⟩ : syracuseStep 788707 = 1183061) B1183061
theorem B624867 : Blo 622298 624867 := bstep (se 1 (by rfl) ⟨468650, by rfl⟩ : syracuseStep 624867 = 937301) B937301
theorem B624883 : Blo 622298 624883 := bstep (se 1 (by rfl) ⟨468662, by rfl⟩ : syracuseStep 624883 = 937325) B937325
theorem B624899 : Blo 622298 624899 := bstep (se 1 (by rfl) ⟨468674, by rfl⟩ : syracuseStep 624899 = 937349) B937349
theorem B624915 : Blo 622298 624915 := bstep (se 1 (by rfl) ⟨468686, by rfl⟩ : syracuseStep 624915 = 937373) B937373
theorem B624931 : Blo 622298 624931 := bstep (se 1 (by rfl) ⟨468698, by rfl⟩ : syracuseStep 624931 = 937397) B937397
theorem B624947 : Blo 622298 624947 := bstep (se 1 (by rfl) ⟨468710, by rfl⟩ : syracuseStep 624947 = 937421) B937421
theorem B624963 : Blo 622298 624963 := bstep (se 1 (by rfl) ⟨468722, by rfl⟩ : syracuseStep 624963 = 937445) B937445
theorem B1050961 : Blo 622298 1050961 := bstep (se 2 (by rfl) ⟨394110, by rfl⟩ : syracuseStep 1050961 = 788221) B788221
theorem B624979 : Blo 622298 624979 := bstep (se 1 (by rfl) ⟨468734, by rfl⟩ : syracuseStep 624979 = 937469) B937469
theorem B624995 : Blo 622298 624995 := bstep (se 1 (by rfl) ⟨468746, by rfl⟩ : syracuseStep 624995 = 937493) B937493
theorem B1050995 : Blo 622298 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B625011 : Blo 622298 625011 := bstep (se 1 (by rfl) ⟨468758, by rfl⟩ : syracuseStep 625011 = 937517) B937517
theorem B625027 : Blo 622298 625027 := bstep (se 1 (by rfl) ⟨468770, by rfl⟩ : syracuseStep 625027 = 937541) B937541
theorem B625043 : Blo 622298 625043 := bstep (se 1 (by rfl) ⟨468782, by rfl⟩ : syracuseStep 625043 = 937565) B937565
theorem B625059 : Blo 622298 625059 := bstep (se 1 (by rfl) ⟨468794, by rfl⟩ : syracuseStep 625059 = 937589) B937589
theorem B625075 : Blo 622298 625075 := bstep (se 1 (by rfl) ⟨468806, by rfl⟩ : syracuseStep 625075 = 937613) B937613
theorem B625091 : Blo 622298 625091 := bstep (se 1 (by rfl) ⟨468818, by rfl⟩ : syracuseStep 625091 = 937637) B937637
theorem B625107 : Blo 622298 625107 := bstep (se 1 (by rfl) ⟨468830, by rfl⟩ : syracuseStep 625107 = 937661) B937661
theorem B625123 : Blo 622298 625123 := bstep (se 1 (by rfl) ⟨468842, by rfl⟩ : syracuseStep 625123 = 937685) B937685
theorem B1575409 : Blo 622298 1575409 := bstep (se 2 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 1575409 = 1181557) B1181557
theorem B8129009 : Blo 622298 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B1051123 : Blo 622298 1051123 := bstep (se 1 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 1051123 = 1576685) B1576685
theorem B625139 : Blo 622298 625139 := bstep (se 1 (by rfl) ⟨468854, by rfl⟩ : syracuseStep 625139 = 937709) B937709
theorem B625155 : Blo 622298 625155 := bstep (se 1 (by rfl) ⟨468866, by rfl⟩ : syracuseStep 625155 = 937733) B937733
theorem B625171 : Blo 622298 625171 := bstep (se 1 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 625171 = 937757) B937757
theorem B625187 : Blo 622298 625187 := bstep (se 1 (by rfl) ⟨468890, by rfl⟩ : syracuseStep 625187 = 937781) B937781
theorem B625203 : Blo 622298 625203 := bstep (se 1 (by rfl) ⟨468902, by rfl⟩ : syracuseStep 625203 = 937805) B937805
theorem B625219 : Blo 622298 625219 := bstep (se 1 (by rfl) ⟨468914, by rfl⟩ : syracuseStep 625219 = 937829) B937829
theorem B625235 : Blo 622298 625235 := bstep (se 1 (by rfl) ⟨468926, by rfl⟩ : syracuseStep 625235 = 937853) B937853
theorem B625251 : Blo 622298 625251 := bstep (se 1 (by rfl) ⟨468938, by rfl⟩ : syracuseStep 625251 = 937877) B937877
theorem B1772131 : Blo 622298 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B625267 : Blo 622298 625267 := bstep (se 1 (by rfl) ⟨468950, by rfl⟩ : syracuseStep 625267 = 937901) B937901
theorem B1051265 : Blo 622298 1051265 := bstep (se 2 (by rfl) ⟨394224, by rfl⟩ : syracuseStep 1051265 = 788449) B788449
theorem B625283 : Blo 622298 625283 := bstep (se 1 (by rfl) ⟨468962, by rfl⟩ : syracuseStep 625283 = 937925) B937925
theorem B625299 : Blo 622298 625299 := bstep (se 1 (by rfl) ⟨468974, by rfl⟩ : syracuseStep 625299 = 937949) B937949
theorem B625315 : Blo 622298 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B625331 : Blo 622298 625331 := bstep (se 1 (by rfl) ⟨468998, by rfl⟩ : syracuseStep 625331 = 937997) B937997
theorem B625347 : Blo 622298 625347 := bstep (se 1 (by rfl) ⟨469010, by rfl⟩ : syracuseStep 625347 = 938021) B938021
theorem B789203 : Blo 622298 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B625363 : Blo 622298 625363 := bstep (se 1 (by rfl) ⟨469022, by rfl⟩ : syracuseStep 625363 = 938045) B938045
theorem B625379 : Blo 622298 625379 := bstep (se 1 (by rfl) ⟨469034, by rfl⟩ : syracuseStep 625379 = 938069) B938069
theorem B1903331 : Blo 622298 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B625395 : Blo 622298 625395 := bstep (se 1 (by rfl) ⟨469046, by rfl⟩ : syracuseStep 625395 = 938093) B938093
theorem B1051393 : Blo 622298 1051393 := bstep (se 2 (by rfl) ⟨394272, by rfl⟩ : syracuseStep 1051393 = 788545) B788545
theorem B1575683 : Blo 622298 1575683 := bstep (se 1 (by rfl) ⟨1181762, by rfl⟩ : syracuseStep 1575683 = 2363525) B2363525
theorem B625411 : Blo 622298 625411 := bstep (se 1 (by rfl) ⟨469058, by rfl⟩ : syracuseStep 625411 = 938117) B938117
theorem B625427 : Blo 622298 625427 := bstep (se 1 (by rfl) ⟨469070, by rfl⟩ : syracuseStep 625427 = 938141) B938141
theorem B1051427 : Blo 622298 1051427 := bstep (se 1 (by rfl) ⟨788570, by rfl⟩ : syracuseStep 1051427 = 1577141) B1577141
theorem B625443 : Blo 622298 625443 := bstep (se 1 (by rfl) ⟨469082, by rfl⟩ : syracuseStep 625443 = 938165) B938165
theorem B625459 : Blo 622298 625459 := bstep (se 1 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 625459 = 938189) B938189
theorem B887603 : Blo 622298 887603 := bstep (se 1 (by rfl) ⟨665702, by rfl⟩ : syracuseStep 887603 = 1331405) B1331405
theorem B625475 : Blo 622298 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B625491 : Blo 622298 625491 := bstep (se 1 (by rfl) ⟨469118, by rfl⟩ : syracuseStep 625491 = 938237) B938237
theorem B625507 : Blo 622298 625507 := bstep (se 1 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 625507 = 938261) B938261
theorem B2001773 : Blo 622298 2001773 := bstep (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) B750665
theorem B625523 : Blo 622298 625523 := bstep (se 1 (by rfl) ⟨469142, by rfl⟩ : syracuseStep 625523 = 938285) B938285
theorem B625539 : Blo 622298 625539 := bstep (se 1 (by rfl) ⟨469154, by rfl⟩ : syracuseStep 625539 = 938309) B938309
theorem B625555 : Blo 622298 625555 := bstep (se 1 (by rfl) ⟨469166, by rfl⟩ : syracuseStep 625555 = 938333) B938333
theorem B1051555 : Blo 622298 1051555 := bstep (se 1 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 1051555 = 1577333) B1577333
theorem B625571 : Blo 622298 625571 := bstep (se 1 (by rfl) ⟨469178, by rfl⟩ : syracuseStep 625571 = 938357) B938357
theorem B625587 : Blo 622298 625587 := bstep (se 1 (by rfl) ⟨469190, by rfl⟩ : syracuseStep 625587 = 938381) B938381
theorem B1575875 : Blo 622298 1575875 := bstep (se 1 (by rfl) ⟨1181906, by rfl⟩ : syracuseStep 1575875 = 2363813) B2363813
theorem B625603 : Blo 622298 625603 := bstep (se 1 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 625603 = 938405) B938405
theorem B625619 : Blo 622298 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B625635 : Blo 622298 625635 := bstep (se 1 (by rfl) ⟨469226, by rfl⟩ : syracuseStep 625635 = 938453) B938453
theorem B1903601 : Blo 622298 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B625651 : Blo 622298 625651 := bstep (se 1 (by rfl) ⟨469238, by rfl⟩ : syracuseStep 625651 = 938477) B938477
theorem B625667 : Blo 622298 625667 := bstep (se 1 (by rfl) ⟨469250, by rfl⟩ : syracuseStep 625667 = 938501) B938501
theorem B2853901 : Blo 622298 2853901 := bstep (se 3 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 2853901 = 1070213) B1070213
theorem B625683 : Blo 622298 625683 := bstep (se 1 (by rfl) ⟨469262, by rfl⟩ : syracuseStep 625683 = 938525) B938525
theorem B625699 : Blo 622298 625699 := bstep (se 1 (by rfl) ⟨469274, by rfl⟩ : syracuseStep 625699 = 938549) B938549
theorem B1051697 : Blo 622298 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B625715 : Blo 622298 625715 := bstep (se 1 (by rfl) ⟨469286, by rfl⟩ : syracuseStep 625715 = 938573) B938573
theorem B625731 : Blo 622298 625731 := bstep (se 1 (by rfl) ⟨469298, by rfl⟩ : syracuseStep 625731 = 938597) B938597
theorem B625747 : Blo 622298 625747 := bstep (se 1 (by rfl) ⟨469310, by rfl⟩ : syracuseStep 625747 = 938621) B938621
theorem B625763 : Blo 622298 625763 := bstep (se 1 (by rfl) ⟨469322, by rfl⟩ : syracuseStep 625763 = 938645) B938645
theorem B1182833 : Blo 622298 1182833 := bstep (se 2 (by rfl) ⟨443562, by rfl⟩ : syracuseStep 1182833 = 887125) B887125
theorem B625779 : Blo 622298 625779 := bstep (se 1 (by rfl) ⟨469334, by rfl⟩ : syracuseStep 625779 = 938669) B938669
theorem B625795 : Blo 622298 625795 := bstep (se 1 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 625795 = 938693) B938693
theorem B625811 : Blo 622298 625811 := bstep (se 1 (by rfl) ⟨469358, by rfl⟩ : syracuseStep 625811 = 938717) B938717
theorem B1281187 : Blo 622298 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B625827 : Blo 622298 625827 := bstep (se 1 (by rfl) ⟨469370, by rfl⟩ : syracuseStep 625827 = 938741) B938741
theorem B1051825 : Blo 622298 1051825 := bstep (se 2 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 1051825 = 788869) B788869
theorem B625843 : Blo 622298 625843 := bstep (se 1 (by rfl) ⟨469382, by rfl⟩ : syracuseStep 625843 = 938765) B938765
theorem B625859 : Blo 622298 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B1051859 : Blo 622298 1051859 := bstep (se 1 (by rfl) ⟨788894, by rfl⟩ : syracuseStep 1051859 = 1577789) B1577789
theorem B625875 : Blo 622298 625875 := bstep (se 1 (by rfl) ⟨469406, by rfl⟩ : syracuseStep 625875 = 938813) B938813
theorem B625891 : Blo 622298 625891 := bstep (se 1 (by rfl) ⟨469418, by rfl⟩ : syracuseStep 625891 = 938837) B938837
theorem B625907 : Blo 622298 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B625923 : Blo 622298 625923 := bstep (se 1 (by rfl) ⟨469442, by rfl⟩ : syracuseStep 625923 = 938885) B938885
theorem B625939 : Blo 622298 625939 := bstep (se 1 (by rfl) ⟨469454, by rfl⟩ : syracuseStep 625939 = 938909) B938909
theorem B625955 : Blo 622298 625955 := bstep (se 1 (by rfl) ⟨469466, by rfl⟩ : syracuseStep 625955 = 938933) B938933
theorem B625971 : Blo 622298 625971 := bstep (se 1 (by rfl) ⟨469478, by rfl⟩ : syracuseStep 625971 = 938957) B938957
theorem B625987 : Blo 622298 625987 := bstep (se 1 (by rfl) ⟨469490, by rfl⟩ : syracuseStep 625987 = 938981) B938981
theorem B1051987 : Blo 622298 1051987 := bstep (se 1 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 1051987 = 1577981) B1577981
theorem B626003 : Blo 622298 626003 := bstep (se 1 (by rfl) ⟨469502, by rfl⟩ : syracuseStep 626003 = 939005) B939005
theorem B626019 : Blo 622298 626019 := bstep (se 1 (by rfl) ⟨469514, by rfl⟩ : syracuseStep 626019 = 939029) B939029
theorem B626035 : Blo 622298 626035 := bstep (se 1 (by rfl) ⟨469526, by rfl⟩ : syracuseStep 626035 = 939053) B939053
theorem B626051 : Blo 622298 626051 := bstep (se 1 (by rfl) ⟨469538, by rfl⟩ : syracuseStep 626051 = 939077) B939077
theorem B789907 : Blo 622298 789907 := bstep (se 1 (by rfl) ⟨592430, by rfl⟩ : syracuseStep 789907 = 1184861) B1184861
theorem B626067 : Blo 622298 626067 := bstep (se 1 (by rfl) ⟨469550, by rfl⟩ : syracuseStep 626067 = 939101) B939101
theorem B626083 : Blo 622298 626083 := bstep (se 1 (by rfl) ⟨469562, by rfl⟩ : syracuseStep 626083 = 939125) B939125
theorem B2100653 : Blo 622298 2100653 := bstep (se 3 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 2100653 = 787745) B787745
theorem B888241 : Blo 622298 888241 := bstep (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) B666181
theorem B626099 : Blo 622298 626099 := bstep (se 1 (by rfl) ⟨469574, by rfl⟩ : syracuseStep 626099 = 939149) B939149
theorem B626115 : Blo 622298 626115 := bstep (se 1 (by rfl) ⟨469586, by rfl⟩ : syracuseStep 626115 = 939173) B939173
theorem B626131 : Blo 622298 626131 := bstep (se 1 (by rfl) ⟨469598, by rfl⟩ : syracuseStep 626131 = 939197) B939197
theorem B1052129 : Blo 622298 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B2100707 : Blo 622298 2100707 := bstep (se 1 (by rfl) ⟨1575530, by rfl⟩ : syracuseStep 2100707 = 3151061) B3151061
theorem B626147 : Blo 622298 626147 := bstep (se 1 (by rfl) ⟨469610, by rfl⟩ : syracuseStep 626147 = 939221) B939221
theorem B790003 : Blo 622298 790003 := bstep (se 1 (by rfl) ⟨592502, by rfl⟩ : syracuseStep 790003 = 1185005) B1185005
theorem B626163 : Blo 622298 626163 := bstep (se 1 (by rfl) ⟨469622, by rfl⟩ : syracuseStep 626163 = 939245) B939245
theorem B626179 : Blo 622298 626179 := bstep (se 1 (by rfl) ⟨469634, by rfl⟩ : syracuseStep 626179 = 939269) B939269
theorem B626195 : Blo 622298 626195 := bstep (se 1 (by rfl) ⟨469646, by rfl⟩ : syracuseStep 626195 = 939293) B939293
theorem B888355 : Blo 622298 888355 := bstep (se 1 (by rfl) ⟨666266, by rfl⟩ : syracuseStep 888355 = 1332533) B1332533
theorem B626211 : Blo 622298 626211 := bstep (se 1 (by rfl) ⟨469658, by rfl⟩ : syracuseStep 626211 = 939317) B939317
theorem B626227 : Blo 622298 626227 := bstep (se 1 (by rfl) ⟨469670, by rfl⟩ : syracuseStep 626227 = 939341) B939341
theorem B626243 : Blo 622298 626243 := bstep (se 1 (by rfl) ⟨469682, by rfl⟩ : syracuseStep 626243 = 939365) B939365
theorem B626259 : Blo 622298 626259 := bstep (se 1 (by rfl) ⟨469694, by rfl⟩ : syracuseStep 626259 = 939389) B939389
theorem B1052257 : Blo 622298 1052257 := bstep (se 2 (by rfl) ⟨394596, by rfl⟩ : syracuseStep 1052257 = 789193) B789193
theorem B626275 : Blo 622298 626275 := bstep (se 1 (by rfl) ⟨469706, by rfl⟩ : syracuseStep 626275 = 939413) B939413
theorem B626291 : Blo 622298 626291 := bstep (se 1 (by rfl) ⟨469718, by rfl⟩ : syracuseStep 626291 = 939437) B939437
theorem B1052291 : Blo 622298 1052291 := bstep (se 1 (by rfl) ⟨789218, by rfl⟩ : syracuseStep 1052291 = 1578437) B1578437
theorem B1904305 : Blo 622298 1904305 := bstep (se 2 (by rfl) ⟨714114, by rfl⟩ : syracuseStep 1904305 = 1428229) B1428229
theorem B2100977 : Blo 622298 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B1052419 : Blo 622298 1052419 := bstep (se 1 (by rfl) ⟨789314, by rfl⟩ : syracuseStep 1052419 = 1578629) B1578629
theorem B1576817 : Blo 622298 1576817 := bstep (se 2 (by rfl) ⟨591306, by rfl⟩ : syracuseStep 1576817 = 1182613) B1182613
theorem B1052561 : Blo 622298 1052561 := bstep (se 2 (by rfl) ⟨394710, by rfl⟩ : syracuseStep 1052561 = 789421) B789421
theorem B1576867 : Blo 622298 1576867 := bstep (se 1 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 1576867 = 2365301) B2365301
theorem B1773521 : Blo 622298 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B790499 : Blo 622298 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B1183729 : Blo 622298 1183729 := bstep (se 2 (by rfl) ⟨443898, by rfl⟩ : syracuseStep 1183729 = 887797) B887797
theorem B1052689 : Blo 622298 1052689 := bstep (se 2 (by rfl) ⟨394758, by rfl⟩ : syracuseStep 1052689 = 789517) B789517
theorem B1577009 : Blo 622298 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B1052723 : Blo 622298 1052723 := bstep (se 1 (by rfl) ⟨789542, by rfl⟩ : syracuseStep 1052723 = 1579085) B1579085
theorem B1183889 : Blo 622298 1183889 := bstep (se 2 (by rfl) ⟨443958, by rfl⟩ : syracuseStep 1183889 = 887917) B887917
theorem B1052851 : Blo 622298 1052851 := bstep (se 1 (by rfl) ⟨789638, by rfl⟩ : syracuseStep 1052851 = 1579277) B1579277
theorem B2101517 : Blo 622298 2101517 := bstep (se 3 (by rfl) ⟨394034, by rfl⟩ : syracuseStep 2101517 = 788069) B788069
theorem B1052993 : Blo 622298 1052993 := bstep (se 2 (by rfl) ⟨394872, by rfl⟩ : syracuseStep 1052993 = 789745) B789745
theorem B2101571 : Blo 622298 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B1053121 : Blo 622298 1053121 := bstep (se 2 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 1053121 = 789841) B789841
theorem B1053155 : Blo 622298 1053155 := bstep (se 1 (by rfl) ⟨789866, by rfl⟩ : syracuseStep 1053155 = 1579733) B1579733
theorem B1184291 : Blo 622298 1184291 := bstep (se 1 (by rfl) ⟨888218, by rfl⟩ : syracuseStep 1184291 = 1776437) B1776437
theorem B3150413 : Blo 622298 3150413 := bstep (se 3 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 3150413 = 1181405) B1181405
theorem B2101841 : Blo 622298 2101841 := bstep (se 2 (by rfl) ⟨788190, by rfl⟩ : syracuseStep 2101841 = 1576381) B1576381
theorem B1053283 : Blo 622298 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B2003555 : Blo 622298 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B791203 : Blo 622298 791203 := bstep (se 1 (by rfl) ⟨593402, by rfl⟩ : syracuseStep 791203 = 1186805) B1186805
theorem B1053425 : Blo 622298 1053425 := bstep (se 2 (by rfl) ⟨395034, by rfl⟩ : syracuseStep 1053425 = 790069) B790069
theorem B791299 : Blo 622298 791299 := bstep (se 1 (by rfl) ⟨593474, by rfl⟩ : syracuseStep 791299 = 1186949) B1186949
theorem B889699 : Blo 622298 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B1053553 : Blo 622298 1053553 := bstep (se 2 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 1053553 = 790165) B790165
theorem B1774477 : Blo 622298 1774477 := bstep (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) B665429
theorem B1053587 : Blo 622298 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B1578001 : Blo 622298 1578001 := bstep (se 2 (by rfl) ⟨591750, by rfl⟩ : syracuseStep 1578001 = 1183501) B1183501
theorem B1053715 : Blo 622298 1053715 := bstep (se 1 (by rfl) ⟨790286, by rfl⟩ : syracuseStep 1053715 = 1580573) B1580573
theorem B2102381 : Blo 622298 2102381 := bstep (se 3 (by rfl) ⟨394196, by rfl⟩ : syracuseStep 2102381 = 788393) B788393
theorem B1774705 : Blo 622298 1774705 := bstep (se 2 (by rfl) ⟨665514, by rfl⟩ : syracuseStep 1774705 = 1331029) B1331029
theorem B4002929 : Blo 622298 4002929 := bstep (se 2 (by rfl) ⟨1501098, by rfl⟩ : syracuseStep 4002929 = 3002197) B3002197
theorem B1053857 : Blo 622298 1053857 := bstep (se 2 (by rfl) ⟨395196, by rfl⟩ : syracuseStep 1053857 = 790393) B790393
theorem B2102435 : Blo 622298 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B2528497 : Blo 622298 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B791795 : Blo 622298 791795 := bstep (se 1 (by rfl) ⟨593846, by rfl⟩ : syracuseStep 791795 = 1187693) B1187693
theorem B1774865 : Blo 622298 1774865 := bstep (se 2 (by rfl) ⟨665574, by rfl⟩ : syracuseStep 1774865 = 1331149) B1331149
theorem B1053985 : Blo 622298 1053985 := bstep (se 2 (by rfl) ⟨395244, by rfl⟩ : syracuseStep 1053985 = 790489) B790489
theorem B1578275 : Blo 622298 1578275 := bstep (se 1 (by rfl) ⟨1183706, by rfl⟩ : syracuseStep 1578275 = 2367413) B2367413
theorem B1054019 : Blo 622298 1054019 := bstep (se 1 (by rfl) ⟨790514, by rfl⟩ : syracuseStep 1054019 = 1581029) B1581029
theorem B2364785 : Blo 622298 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B1774979 : Blo 622298 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B1185187 : Blo 622298 1185187 := bstep (se 1 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 1185187 = 1777781) B1777781
theorem B2102705 : Blo 622298 2102705 := bstep (se 2 (by rfl) ⟨788514, by rfl⟩ : syracuseStep 2102705 = 1577029) B1577029
theorem B1054147 : Blo 622298 1054147 := bstep (se 1 (by rfl) ⟨790610, by rfl⟩ : syracuseStep 1054147 = 1581221) B1581221
theorem B1578467 : Blo 622298 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B1185347 : Blo 622298 1185347 := bstep (se 1 (by rfl) ⟨889010, by rfl⟩ : syracuseStep 1185347 = 1778021) B1778021
theorem B1054289 : Blo 622298 1054289 := bstep (se 2 (by rfl) ⟨395358, by rfl⟩ : syracuseStep 1054289 = 790717) B790717
theorem B1054417 : Blo 622298 1054417 := bstep (se 2 (by rfl) ⟨395406, by rfl⟩ : syracuseStep 1054417 = 790813) B790813
theorem B1054451 : Blo 622298 1054451 := bstep (se 1 (by rfl) ⟨790838, by rfl⟩ : syracuseStep 1054451 = 1581677) B1581677
theorem B1054579 : Blo 622298 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B792499 : Blo 622298 792499 := bstep (se 1 (by rfl) ⟨594374, by rfl⟩ : syracuseStep 792499 = 1188749) B1188749
theorem B2103245 : Blo 622298 2103245 := bstep (se 3 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 2103245 = 788717) B788717
theorem B890833 : Blo 622298 890833 := bstep (se 2 (by rfl) ⟨334062, by rfl⟩ : syracuseStep 890833 = 668125) B668125
theorem B1054721 : Blo 622298 1054721 := bstep (se 2 (by rfl) ⟨395520, by rfl⟩ : syracuseStep 1054721 = 791041) B791041
theorem B2103299 : Blo 622298 2103299 := bstep (se 1 (by rfl) ⟨1577474, by rfl⟩ : syracuseStep 2103299 = 3154949) B3154949
theorem B792595 : Blo 622298 792595 := bstep (se 1 (by rfl) ⟨594446, by rfl⟩ : syracuseStep 792595 = 1188893) B1188893
theorem B890929 : Blo 622298 890929 := bstep (se 2 (by rfl) ⟨334098, by rfl⟩ : syracuseStep 890929 = 668197) B668197
theorem B4790341 : Blo 622298 4790341 := bstep (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) B898189
theorem B8198213 : Blo 622298 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B1054849 : Blo 622298 1054849 := bstep (se 2 (by rfl) ⟨395568, by rfl⟩ : syracuseStep 1054849 = 791137) B791137
theorem B1054883 : Blo 622298 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B2103569 : Blo 622298 2103569 := bstep (se 2 (by rfl) ⟨788838, by rfl⟩ : syracuseStep 2103569 = 1577677) B1577677
theorem B1055011 : Blo 622298 1055011 := bstep (se 1 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 1055011 = 1582517) B1582517
theorem B3381581 : Blo 622298 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B1775981 : Blo 622298 1775981 := bstep (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) B665993
theorem B2005361 : Blo 622298 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B9247117 : Blo 622298 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B1579409 : Blo 622298 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B2005411 : Blo 622298 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B1055153 : Blo 622298 1055153 := bstep (se 2 (by rfl) ⟨395682, by rfl⟩ : syracuseStep 1055153 = 791365) B791365
theorem B1579459 : Blo 622298 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B891425 : Blo 622298 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B1776163 : Blo 622298 1776163 := bstep (se 1 (by rfl) ⟨1332122, by rfl⟩ : syracuseStep 1776163 = 2664245) B2664245
theorem B1055281 : Blo 622298 1055281 := bstep (se 2 (by rfl) ⟨395730, by rfl⟩ : syracuseStep 1055281 = 791461) B791461
theorem B1579601 : Blo 622298 1579601 := bstep (se 2 (by rfl) ⟨592350, by rfl⟩ : syracuseStep 1579601 = 1184701) B1184701
theorem B1055315 : Blo 622298 1055315 := bstep (se 1 (by rfl) ⟨791486, by rfl⟩ : syracuseStep 1055315 = 1582973) B1582973
theorem B1186417 : Blo 622298 1186417 := bstep (se 2 (by rfl) ⟨444906, by rfl⟩ : syracuseStep 1186417 = 889813) B889813
theorem B1776323 : Blo 622298 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B1055443 : Blo 622298 1055443 := bstep (se 1 (by rfl) ⟨791582, by rfl⟩ : syracuseStep 1055443 = 1583165) B1583165
theorem B9116387 : Blo 622298 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B2366243 : Blo 622298 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B2104109 : Blo 622298 2104109 := bstep (se 3 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 2104109 = 789041) B789041
theorem B2661169 : Blo 622298 2661169 := bstep (se 2 (by rfl) ⟨997938, by rfl⟩ : syracuseStep 2661169 = 1995877) B1995877
theorem B1055585 : Blo 622298 1055585 := bstep (se 2 (by rfl) ⟨395844, by rfl⟩ : syracuseStep 1055585 = 791689) B791689
theorem B2104163 : Blo 622298 2104163 := bstep (se 1 (by rfl) ⟨1578122, by rfl⟩ : syracuseStep 2104163 = 3156245) B3156245
theorem B1055713 : Blo 622298 1055713 := bstep (se 2 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 1055713 = 791785) B791785
theorem B1055747 : Blo 622298 1055747 := bstep (se 1 (by rfl) ⟨791810, by rfl⟩ : syracuseStep 1055747 = 1583621) B1583621
theorem B2104433 : Blo 622298 2104433 := bstep (se 2 (by rfl) ⟨789162, by rfl⟩ : syracuseStep 2104433 = 1578325) B1578325
theorem B2006129 : Blo 622298 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B1055875 : Blo 622298 1055875 := bstep (se 1 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 1055875 = 1583813) B1583813
theorem B2399473 : Blo 622298 2399473 := bstep (se 2 (by rfl) ⟨899802, by rfl⟩ : syracuseStep 2399473 = 1799605) B1799605
theorem B1056017 : Blo 622298 1056017 := bstep (se 2 (by rfl) ⟨396006, by rfl⟩ : syracuseStep 1056017 = 792013) B792013
theorem B1056145 : Blo 622298 1056145 := bstep (se 2 (by rfl) ⟨396054, by rfl⟩ : syracuseStep 1056145 = 792109) B792109
theorem B3153329 : Blo 622298 3153329 := bstep (se 2 (by rfl) ⟨1182498, by rfl⟩ : syracuseStep 3153329 = 2364997) B2364997
theorem B1056179 : Blo 622298 1056179 := bstep (se 1 (by rfl) ⟨792134, by rfl⟩ : syracuseStep 1056179 = 1584269) B1584269
theorem B4005389 : Blo 622298 4005389 := bstep (se 3 (by rfl) ⟨751010, by rfl⟩ : syracuseStep 4005389 = 1502021) B1502021
theorem B1580593 : Blo 622298 1580593 := bstep (se 2 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 1580593 = 1185445) B1185445
theorem B1056307 : Blo 622298 1056307 := bstep (se 1 (by rfl) ⟨792230, by rfl⟩ : syracuseStep 1056307 = 1584461) B1584461
theorem B2104973 : Blo 622298 2104973 := bstep (se 3 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 2104973 = 789365) B789365
theorem B2137745 : Blo 622298 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1187473 : Blo 622298 1187473 := bstep (se 2 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 1187473 = 890605) B890605
theorem B1056449 : Blo 622298 1056449 := bstep (se 2 (by rfl) ⟨396168, by rfl⟩ : syracuseStep 1056449 = 792337) B792337
theorem B2105027 : Blo 622298 2105027 := bstep (se 1 (by rfl) ⟨1578770, by rfl⟩ : syracuseStep 2105027 = 3157541) B3157541
theorem B1777393 : Blo 622298 1777393 := bstep (se 2 (by rfl) ⟨666522, by rfl⟩ : syracuseStep 1777393 = 1333045) B1333045
theorem B2367245 : Blo 622298 2367245 := bstep (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) B887717
theorem B1056577 : Blo 622298 1056577 := bstep (se 2 (by rfl) ⟨396216, by rfl⟩ : syracuseStep 1056577 = 792433) B792433
theorem B1580867 : Blo 622298 1580867 := bstep (se 1 (by rfl) ⟨1185650, by rfl⟩ : syracuseStep 1580867 = 2371301) B2371301
theorem B3546949 : Blo 622298 3546949 := bstep (se 4 (by rfl) ⟨332526, by rfl⟩ : syracuseStep 3546949 = 665053) B665053
theorem B1056611 : Blo 622298 1056611 := bstep (se 1 (by rfl) ⟨792458, by rfl⟩ : syracuseStep 1056611 = 1584917) B1584917
theorem B2105297 : Blo 622298 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B1056739 : Blo 622298 1056739 := bstep (se 1 (by rfl) ⟨792554, by rfl⟩ : syracuseStep 1056739 = 1585109) B1585109
theorem B1581059 : Blo 622298 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B1187875 : Blo 622298 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B1187921 : Blo 622298 1187921 := bstep (se 2 (by rfl) ⟨445470, by rfl⟩ : syracuseStep 1187921 = 890941) B890941
theorem B9248995 : Blo 622298 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B1188209 : Blo 622298 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B2105837 : Blo 622298 2105837 := bstep (se 3 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 2105837 = 789689) B789689
theorem B2105891 : Blo 622298 2105891 := bstep (se 1 (by rfl) ⟨1579418, by rfl⟩ : syracuseStep 2105891 = 3158837) B3158837
theorem B7119413 : Blo 622298 7119413 := bstep (se 5 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 7119413 = 667445) B667445
theorem B4268785 : Blo 622298 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B2532131 : Blo 622298 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B2106161 : Blo 622298 2106161 := bstep (se 2 (by rfl) ⟨789810, by rfl⟩ : syracuseStep 2106161 = 1579621) B1579621
theorem B207496021 : Blo 622298 207496021 := bstep (se 9 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 207496021 = 1215797) B1215797
theorem B3154787 : Blo 622298 3154787 := bstep (se 1 (by rfl) ⟨2366090, by rfl⟩ : syracuseStep 3154787 = 4732181) B4732181
theorem B1582001 : Blo 622298 1582001 := bstep (se 2 (by rfl) ⟨593250, by rfl⟩ : syracuseStep 1582001 = 1186501) B1186501
theorem B1582051 : Blo 622298 1582051 := bstep (se 1 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 1582051 = 2373077) B2373077
theorem B1778669 : Blo 622298 1778669 := bstep (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) B667001
theorem B664643 : Blo 622298 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B1188931 : Blo 622298 1188931 := bstep (se 1 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 1188931 = 1783397) B1783397
theorem B1582193 : Blo 622298 1582193 := bstep (se 2 (by rfl) ⟨593322, by rfl⟩ : syracuseStep 1582193 = 1186645) B1186645
theorem B1778851 : Blo 622298 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B1778897 : Blo 622298 1778897 := bstep (se 2 (by rfl) ⟨667086, by rfl⟩ : syracuseStep 1778897 = 1334173) B1334173
theorem B5711089 : Blo 622298 5711089 := bstep (se 2 (by rfl) ⟨2141658, by rfl⟩ : syracuseStep 5711089 = 4283317) B4283317
theorem B2106701 : Blo 622298 2106701 := bstep (se 3 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 2106701 = 790013) B790013
theorem B2106755 : Blo 622298 2106755 := bstep (se 1 (by rfl) ⟨1580066, by rfl⟩ : syracuseStep 2106755 = 3160133) B3160133
theorem B3155597 : Blo 622298 3155597 := bstep (se 3 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 3155597 = 1183349) B1183349
theorem B2107025 : Blo 622298 2107025 := bstep (se 2 (by rfl) ⟨790134, by rfl⟩ : syracuseStep 2107025 = 1580269) B1580269
theorem B3548933 : Blo 622298 3548933 := bstep (se 4 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 3548933 = 665425) B665425
theorem B2533169 : Blo 622298 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B2369357 : Blo 622298 2369357 := bstep (se 3 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 2369357 = 888509) B888509
theorem B2991971 : Blo 622298 2991971 := bstep (se 1 (by rfl) ⟨2243978, by rfl⟩ : syracuseStep 2991971 = 4487957) B4487957
theorem B2992049 : Blo 622298 2992049 := bstep (se 2 (by rfl) ⟨1122018, by rfl⟩ : syracuseStep 2992049 = 2244037) B2244037
theorem B1124369 : Blo 622298 1124369 := bstep (se 2 (by rfl) ⟨421638, by rfl⟩ : syracuseStep 1124369 = 843277) B843277
theorem B1583185 : Blo 622298 1583185 := bstep (se 2 (by rfl) ⟨593694, by rfl⟩ : syracuseStep 1583185 = 1187389) B1187389
theorem B9021581 : Blo 622298 9021581 := bstep (se 3 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 9021581 = 3383093) B3383093
theorem B2107565 : Blo 622298 2107565 := bstep (se 3 (by rfl) ⟨395168, by rfl⟩ : syracuseStep 2107565 = 790337) B790337
theorem B5056739 : Blo 622298 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B2107619 : Blo 622298 2107619 := bstep (se 1 (by rfl) ⟨1580714, by rfl⟩ : syracuseStep 2107619 = 3161429) B3161429
theorem B1648945 : Blo 622298 1648945 := bstep (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) B1236709
theorem B1583459 : Blo 622298 1583459 := bstep (se 1 (by rfl) ⟨1187594, by rfl⟩ : syracuseStep 1583459 = 2375189) B2375189
theorem B2664845 : Blo 622298 2664845 := bstep (se 3 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 2664845 = 999317) B999317
theorem B666019 : Blo 622298 666019 := bstep (se 1 (by rfl) ⟨499514, by rfl⟩ : syracuseStep 666019 = 999029) B999029
theorem B16394723 : Blo 622298 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B2107889 : Blo 622298 2107889 := bstep (se 2 (by rfl) ⟨790458, by rfl⟩ : syracuseStep 2107889 = 1580917) B1580917
theorem B1124867 : Blo 622298 1124867 := bstep (se 1 (by rfl) ⟨843650, by rfl⟩ : syracuseStep 1124867 = 1687301) B1687301
theorem B1583651 : Blo 622298 1583651 := bstep (se 1 (by rfl) ⟨1187738, by rfl⟩ : syracuseStep 1583651 = 2375477) B2375477
theorem B2370161 : Blo 622298 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B1780355 : Blo 622298 1780355 := bstep (se 1 (by rfl) ⟨1335266, by rfl⟩ : syracuseStep 1780355 = 2670533) B2670533
theorem B6007621 : Blo 622298 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B2141005 : Blo 622298 2141005 := bstep (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) B802877
theorem B3845069 : Blo 622298 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B2108429 : Blo 622298 2108429 := bstep (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) B790661
theorem B2108483 : Blo 622298 2108483 := bstep (se 1 (by rfl) ⟨1581362, by rfl⟩ : syracuseStep 2108483 = 3162725) B3162725
theorem B5319877 : Blo 622298 5319877 := bstep (se 4 (by rfl) ⟨498738, by rfl⟩ : syracuseStep 5319877 = 997477) B997477
theorem B2370829 : Blo 622298 2370829 := bstep (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) B889061
theorem B2108753 : Blo 622298 2108753 := bstep (se 2 (by rfl) ⟨790782, by rfl⟩ : syracuseStep 2108753 = 1581565) B1581565
theorem B1584593 : Blo 622298 1584593 := bstep (se 2 (by rfl) ⟨594222, by rfl⟩ : syracuseStep 1584593 = 1188445) B1188445
theorem B1584643 : Blo 622298 1584643 := bstep (se 1 (by rfl) ⟨1188482, by rfl⟩ : syracuseStep 1584643 = 2376965) B2376965
theorem B1584785 : Blo 622298 1584785 := bstep (se 2 (by rfl) ⟨594294, by rfl⟩ : syracuseStep 1584785 = 1188589) B1188589
theorem B667283 : Blo 622298 667283 := bstep (se 1 (by rfl) ⟨500462, by rfl⟩ : syracuseStep 667283 = 1000925) B1000925
theorem B1355459 : Blo 622298 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B700195 : Blo 622298 700195 := bstep (se 1 (by rfl) ⟨525146, by rfl⟩ : syracuseStep 700195 = 1050293) B1050293
theorem B2993969 : Blo 622298 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B2535245 : Blo 622298 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B1781585 : Blo 622298 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B4730723 : Blo 622298 4730723 := bstep (se 1 (by rfl) ⟨3548042, by rfl⟩ : syracuseStep 4730723 = 7096085) B7096085
theorem B2109293 : Blo 622298 2109293 := bstep (se 3 (by rfl) ⟨395492, by rfl⟩ : syracuseStep 2109293 = 790985) B790985
theorem B2109347 : Blo 622298 2109347 := bstep (se 1 (by rfl) ⟨1582010, by rfl⟩ : syracuseStep 2109347 = 3164021) B3164021
theorem B700339 : Blo 622298 700339 := bstep (se 1 (by rfl) ⟨525254, by rfl⟩ : syracuseStep 700339 = 1050509) B1050509
theorem B2142179 : Blo 622298 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B2371619 : Blo 622298 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B700483 : Blo 622298 700483 := bstep (se 1 (by rfl) ⟨525362, by rfl⟩ : syracuseStep 700483 = 1050725) B1050725
theorem B2109617 : Blo 622298 2109617 := bstep (se 2 (by rfl) ⟨791106, by rfl⟩ : syracuseStep 2109617 = 1582213) B1582213
theorem B700627 : Blo 622298 700627 := bstep (se 1 (by rfl) ⟨525470, by rfl⟩ : syracuseStep 700627 = 1050941) B1050941
theorem B2994509 : Blo 622298 2994509 := bstep (se 3 (by rfl) ⟨561470, by rfl⟩ : syracuseStep 2994509 = 1122941) B1122941
theorem B700771 : Blo 622298 700771 := bstep (se 1 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 700771 = 1051157) B1051157
theorem B668035 : Blo 622298 668035 := bstep (se 1 (by rfl) ⟨501026, by rfl⟩ : syracuseStep 668035 = 1002053) B1002053
theorem B3158513 : Blo 622298 3158513 := bstep (se 2 (by rfl) ⟨1184442, by rfl⟩ : syracuseStep 3158513 = 2368885) B2368885
theorem B700915 : Blo 622298 700915 := bstep (se 1 (by rfl) ⟨525686, by rfl⟩ : syracuseStep 700915 = 1051373) B1051373
theorem B701059 : Blo 622298 701059 := bstep (se 1 (by rfl) ⟨525794, by rfl⟩ : syracuseStep 701059 = 1051589) B1051589
theorem B2372273 : Blo 622298 2372273 := bstep (se 2 (by rfl) ⟨889602, by rfl⟩ : syracuseStep 2372273 = 1779205) B1779205
theorem B12366533 : Blo 622298 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B2110157 : Blo 622298 2110157 := bstep (se 3 (by rfl) ⟨395654, by rfl⟩ : syracuseStep 2110157 = 791309) B791309
theorem B2110211 : Blo 622298 2110211 := bstep (se 1 (by rfl) ⟨1582658, by rfl⟩ : syracuseStep 2110211 = 3165317) B3165317
theorem B701203 : Blo 622298 701203 := bstep (se 1 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 701203 = 1051805) B1051805
theorem B701347 : Blo 622298 701347 := bstep (se 1 (by rfl) ⟨526010, by rfl⟩ : syracuseStep 701347 = 1052021) B1052021
theorem B2110481 : Blo 622298 2110481 := bstep (se 2 (by rfl) ⟨791430, by rfl⟩ : syracuseStep 2110481 = 1582861) B1582861
theorem B701491 : Blo 622298 701491 := bstep (se 1 (by rfl) ⟨526118, by rfl⟩ : syracuseStep 701491 = 1052237) B1052237
theorem B701635 : Blo 622298 701635 := bstep (se 1 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 701635 = 1052453) B1052453
theorem B1783043 : Blo 622298 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B701779 : Blo 622298 701779 := bstep (se 1 (by rfl) ⟨526334, by rfl⟩ : syracuseStep 701779 = 1052669) B1052669
theorem B1684909 : Blo 622298 1684909 := bstep (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) B631841
theorem B38352325 : Blo 622298 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B701923 : Blo 622298 701923 := bstep (se 1 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 701923 = 1052885) B1052885
theorem B1684973 : Blo 622298 1684973 := bstep (se 3 (by rfl) ⟨315932, by rfl⟩ : syracuseStep 1684973 = 631865) B631865
theorem B3552781 : Blo 622298 3552781 := bstep (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) B1332293
theorem B2111021 : Blo 622298 2111021 := bstep (se 3 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 2111021 = 791633) B791633
theorem B2111075 : Blo 622298 2111075 := bstep (se 1 (by rfl) ⟨1583306, by rfl⟩ : syracuseStep 2111075 = 3166613) B3166613
theorem B702067 : Blo 622298 702067 := bstep (se 1 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 702067 = 1053101) B1053101
theorem B702211 : Blo 622298 702211 := bstep (se 1 (by rfl) ⟨526658, by rfl⟩ : syracuseStep 702211 = 1053317) B1053317
theorem B2111345 : Blo 622298 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B1128305 : Blo 622298 1128305 := bstep (se 2 (by rfl) ⟨423114, by rfl⟩ : syracuseStep 1128305 = 846229) B846229
theorem B997267 : Blo 622298 997267 := bstep (se 1 (by rfl) ⟨747950, by rfl⟩ : syracuseStep 997267 = 1495901) B1495901
theorem B702355 : Blo 622298 702355 := bstep (se 1 (by rfl) ⟨526766, by rfl⟩ : syracuseStep 702355 = 1053533) B1053533
theorem B3159971 : Blo 622298 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B702499 : Blo 622298 702499 := bstep (se 1 (by rfl) ⟨526874, by rfl⟩ : syracuseStep 702499 = 1053749) B1053749
theorem B8534069 : Blo 622298 8534069 := bstep (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) B800069
theorem B2373731 : Blo 622298 2373731 := bstep (se 1 (by rfl) ⟨1780298, by rfl⟩ : syracuseStep 2373731 = 3560597) B3560597
theorem B2373745 : Blo 622298 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B1128593 : Blo 622298 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B997523 : Blo 622298 997523 := bstep (se 1 (by rfl) ⟨748142, by rfl⟩ : syracuseStep 997523 = 1496285) B1496285
theorem B702643 : Blo 622298 702643 := bstep (se 1 (by rfl) ⟨526982, by rfl⟩ : syracuseStep 702643 = 1053965) B1053965
theorem B702787 : Blo 622298 702787 := bstep (se 1 (by rfl) ⟨527090, by rfl⟩ : syracuseStep 702787 = 1054181) B1054181
theorem B2111885 : Blo 622298 2111885 := bstep (se 3 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 2111885 = 791957) B791957
theorem B2111939 : Blo 622298 2111939 := bstep (se 1 (by rfl) ⟨1583954, by rfl⟩ : syracuseStep 2111939 = 3167909) B3167909
theorem B702931 : Blo 622298 702931 := bstep (se 1 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 702931 = 1054397) B1054397
theorem B703075 : Blo 622298 703075 := bstep (se 1 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 703075 = 1054613) B1054613
theorem B2669219 : Blo 622298 2669219 := bstep (se 1 (by rfl) ⟨2001914, by rfl⟩ : syracuseStep 2669219 = 4003829) B4003829
theorem B3160781 : Blo 622298 3160781 := bstep (se 3 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 3160781 = 1185293) B1185293
theorem B2112209 : Blo 622298 2112209 := bstep (se 2 (by rfl) ⟨792078, by rfl⟩ : syracuseStep 2112209 = 1584157) B1584157
theorem B703219 : Blo 622298 703219 := bstep (se 1 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 703219 = 1054829) B1054829
theorem B2079533 : Blo 622298 2079533 := bstep (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) B779825
theorem B703363 : Blo 622298 703363 := bstep (se 1 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 703363 = 1055045) B1055045
theorem B703507 : Blo 622298 703507 := bstep (se 1 (by rfl) ⟨527630, by rfl⟩ : syracuseStep 703507 = 1055261) B1055261
theorem B998497 : Blo 622298 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B703651 : Blo 622298 703651 := bstep (se 1 (by rfl) ⟨527738, by rfl⟩ : syracuseStep 703651 = 1055477) B1055477
theorem B2112749 : Blo 622298 2112749 := bstep (se 3 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 2112749 = 792281) B792281
theorem B2112803 : Blo 622298 2112803 := bstep (se 1 (by rfl) ⟨1584602, by rfl⟩ : syracuseStep 2112803 = 3169205) B3169205
theorem B703795 : Blo 622298 703795 := bstep (se 1 (by rfl) ⟨527846, by rfl⟩ : syracuseStep 703795 = 1055693) B1055693
theorem B703939 : Blo 622298 703939 := bstep (se 1 (by rfl) ⟨527954, by rfl⟩ : syracuseStep 703939 = 1055909) B1055909
theorem B3554765 : Blo 622298 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B2375203 : Blo 622298 2375203 := bstep (se 1 (by rfl) ⟨1781402, by rfl⟩ : syracuseStep 2375203 = 3562805) B3562805
theorem B2113073 : Blo 622298 2113073 := bstep (se 2 (by rfl) ⟨792402, by rfl⟩ : syracuseStep 2113073 = 1584805) B1584805
theorem B704083 : Blo 622298 704083 := bstep (se 1 (by rfl) ⟨528062, by rfl⟩ : syracuseStep 704083 = 1056125) B1056125
theorem B933473 : Blo 622298 933473 := bstep (se 2 (by rfl) ⟨350052, by rfl⟩ : syracuseStep 933473 = 700105) B700105
theorem B933491 : Blo 622298 933491 := bstep (se 1 (by rfl) ⟨700118, by rfl⟩ : syracuseStep 933491 = 1400237) B1400237
theorem B933521 : Blo 622298 933521 := bstep (se 2 (by rfl) ⟨350070, by rfl⟩ : syracuseStep 933521 = 700141) B700141
theorem B933539 : Blo 622298 933539 := bstep (se 1 (by rfl) ⟨700154, by rfl⟩ : syracuseStep 933539 = 1400309) B1400309
theorem B933569 : Blo 622298 933569 := bstep (se 2 (by rfl) ⟨350088, by rfl⟩ : syracuseStep 933569 = 700177) B700177
theorem B933587 : Blo 622298 933587 := bstep (se 1 (by rfl) ⟨700190, by rfl⟩ : syracuseStep 933587 = 1400381) B1400381
theorem B704227 : Blo 622298 704227 := bstep (se 1 (by rfl) ⟨528170, by rfl⟩ : syracuseStep 704227 = 1056341) B1056341
theorem B933617 : Blo 622298 933617 := bstep (se 2 (by rfl) ⟨350106, by rfl⟩ : syracuseStep 933617 = 700213) B700213
theorem B933635 : Blo 622298 933635 := bstep (se 1 (by rfl) ⟨700226, by rfl⟩ : syracuseStep 933635 = 1400453) B1400453
theorem B933665 : Blo 622298 933665 := bstep (se 2 (by rfl) ⟨350124, by rfl⟩ : syracuseStep 933665 = 700249) B700249
theorem B1687331 : Blo 622298 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B933683 : Blo 622298 933683 := bstep (se 1 (by rfl) ⟨700262, by rfl⟩ : syracuseStep 933683 = 1400525) B1400525
theorem B933713 : Blo 622298 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B933731 : Blo 622298 933731 := bstep (se 1 (by rfl) ⟨700298, by rfl⟩ : syracuseStep 933731 = 1400597) B1400597
theorem B704371 : Blo 622298 704371 := bstep (se 1 (by rfl) ⟨528278, by rfl⟩ : syracuseStep 704371 = 1056557) B1056557
theorem B933761 : Blo 622298 933761 := bstep (se 2 (by rfl) ⟨350160, by rfl⟩ : syracuseStep 933761 = 700321) B700321
theorem B933779 : Blo 622298 933779 := bstep (se 1 (by rfl) ⟨700334, by rfl⟩ : syracuseStep 933779 = 1400669) B1400669
theorem B933809 : Blo 622298 933809 := bstep (se 2 (by rfl) ⟨350178, by rfl⟩ : syracuseStep 933809 = 700357) B700357
theorem B933827 : Blo 622298 933827 := bstep (se 1 (by rfl) ⟨700370, by rfl⟩ : syracuseStep 933827 = 1400741) B1400741
theorem B1425347 : Blo 622298 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B933857 : Blo 622298 933857 := bstep (se 2 (by rfl) ⟨350196, by rfl⟩ : syracuseStep 933857 = 700393) B700393
theorem B2572273 : Blo 622298 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B933875 : Blo 622298 933875 := bstep (se 1 (by rfl) ⟨700406, by rfl⟩ : syracuseStep 933875 = 1400813) B1400813
theorem B999425 : Blo 622298 999425 := bstep (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) B749569
theorem B704515 : Blo 622298 704515 := bstep (se 1 (by rfl) ⟨528386, by rfl⟩ : syracuseStep 704515 = 1056773) B1056773
theorem B933905 : Blo 622298 933905 := bstep (se 2 (by rfl) ⟨350214, by rfl⟩ : syracuseStep 933905 = 700429) B700429
theorem B933923 : Blo 622298 933923 := bstep (se 1 (by rfl) ⟨700442, by rfl⟩ : syracuseStep 933923 = 1400885) B1400885
theorem B933953 : Blo 622298 933953 := bstep (se 2 (by rfl) ⟨350232, by rfl⟩ : syracuseStep 933953 = 700465) B700465
theorem B2113613 : Blo 622298 2113613 := bstep (se 3 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 2113613 = 792605) B792605
theorem B1261649 : Blo 622298 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B933971 : Blo 622298 933971 := bstep (se 1 (by rfl) ⟨700478, by rfl⟩ : syracuseStep 933971 = 1400957) B1400957
theorem B934001 : Blo 622298 934001 := bstep (se 2 (by rfl) ⟨350250, by rfl⟩ : syracuseStep 934001 = 700501) B700501
theorem B934019 : Blo 622298 934019 := bstep (se 1 (by rfl) ⟨700514, by rfl⟩ : syracuseStep 934019 = 1401029) B1401029
theorem B2113667 : Blo 622298 2113667 := bstep (se 1 (by rfl) ⟨1585250, by rfl⟩ : syracuseStep 2113667 = 3170501) B3170501
theorem B934049 : Blo 622298 934049 := bstep (se 2 (by rfl) ⟨350268, by rfl⟩ : syracuseStep 934049 = 700537) B700537
theorem B934067 : Blo 622298 934067 := bstep (se 1 (by rfl) ⟨700550, by rfl⟩ : syracuseStep 934067 = 1401101) B1401101
theorem B934097 : Blo 622298 934097 := bstep (se 2 (by rfl) ⟨350286, by rfl⟩ : syracuseStep 934097 = 700573) B700573
theorem B934115 : Blo 622298 934115 := bstep (se 1 (by rfl) ⟨700586, by rfl⟩ : syracuseStep 934115 = 1401173) B1401173
theorem B8110307 : Blo 622298 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B934145 : Blo 622298 934145 := bstep (se 2 (by rfl) ⟨350304, by rfl⟩ : syracuseStep 934145 = 700609) B700609
theorem B1065233 : Blo 622298 1065233 := bstep (se 2 (by rfl) ⟨399462, by rfl⟩ : syracuseStep 1065233 = 798925) B798925
theorem B934163 : Blo 622298 934163 := bstep (se 1 (by rfl) ⟨700622, by rfl⟩ : syracuseStep 934163 = 1401245) B1401245
theorem B934193 : Blo 622298 934193 := bstep (se 2 (by rfl) ⟨350322, by rfl⟩ : syracuseStep 934193 = 700645) B700645
theorem B934211 : Blo 622298 934211 := bstep (se 1 (by rfl) ⟨700658, by rfl⟩ : syracuseStep 934211 = 1401317) B1401317
theorem B934241 : Blo 622298 934241 := bstep (se 2 (by rfl) ⟨350340, by rfl⟩ : syracuseStep 934241 = 700681) B700681
theorem B7094627 : Blo 622298 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B3555697 : Blo 622298 3555697 := bstep (se 2 (by rfl) ⟨1333386, by rfl⟩ : syracuseStep 3555697 = 2666773) B2666773
theorem B934259 : Blo 622298 934259 := bstep (se 1 (by rfl) ⟨700694, by rfl⟩ : syracuseStep 934259 = 1401389) B1401389
theorem B934289 : Blo 622298 934289 := bstep (se 2 (by rfl) ⟨350358, by rfl⟩ : syracuseStep 934289 = 700717) B700717
theorem B934307 : Blo 622298 934307 := bstep (se 1 (by rfl) ⟨700730, by rfl⟩ : syracuseStep 934307 = 1401461) B1401461
theorem B934337 : Blo 622298 934337 := bstep (se 2 (by rfl) ⟨350376, by rfl⟩ : syracuseStep 934337 = 700753) B700753
theorem B934355 : Blo 622298 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B934385 : Blo 622298 934385 := bstep (se 2 (by rfl) ⟨350394, by rfl⟩ : syracuseStep 934385 = 700789) B700789
theorem B934403 : Blo 622298 934403 := bstep (se 1 (by rfl) ⟨700802, by rfl⟩ : syracuseStep 934403 = 1401605) B1401605
theorem B901649 : Blo 622298 901649 := bstep (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) B676237
theorem B934433 : Blo 622298 934433 := bstep (se 2 (by rfl) ⟨350412, by rfl⟩ : syracuseStep 934433 = 700825) B700825
theorem B1065521 : Blo 622298 1065521 := bstep (se 2 (by rfl) ⟨399570, by rfl⟩ : syracuseStep 1065521 = 799141) B799141
theorem B934451 : Blo 622298 934451 := bstep (se 1 (by rfl) ⟨700838, by rfl⟩ : syracuseStep 934451 = 1401677) B1401677
theorem B934481 : Blo 622298 934481 := bstep (se 2 (by rfl) ⟨350430, by rfl⟩ : syracuseStep 934481 = 700861) B700861
theorem B934499 : Blo 622298 934499 := bstep (se 1 (by rfl) ⟨700874, by rfl⟩ : syracuseStep 934499 = 1401749) B1401749
theorem B2671217 : Blo 622298 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B934529 : Blo 622298 934529 := bstep (se 2 (by rfl) ⟨350448, by rfl⟩ : syracuseStep 934529 = 700897) B700897
theorem B934547 : Blo 622298 934547 := bstep (se 1 (by rfl) ⟨700910, by rfl⟩ : syracuseStep 934547 = 1401821) B1401821
theorem B934577 : Blo 622298 934577 := bstep (se 2 (by rfl) ⟨350466, by rfl⟩ : syracuseStep 934577 = 700933) B700933
theorem B934595 : Blo 622298 934595 := bstep (se 1 (by rfl) ⟨700946, by rfl⟩ : syracuseStep 934595 = 1401893) B1401893
theorem B934625 : Blo 622298 934625 := bstep (se 2 (by rfl) ⟨350484, by rfl⟩ : syracuseStep 934625 = 700969) B700969
theorem B1262321 : Blo 622298 1262321 := bstep (se 2 (by rfl) ⟨473370, by rfl⟩ : syracuseStep 1262321 = 946741) B946741
theorem B934643 : Blo 622298 934643 := bstep (se 1 (by rfl) ⟨700982, by rfl⟩ : syracuseStep 934643 = 1401965) B1401965
theorem B934673 : Blo 622298 934673 := bstep (se 2 (by rfl) ⟨350502, by rfl⟩ : syracuseStep 934673 = 701005) B701005
theorem B934691 : Blo 622298 934691 := bstep (se 1 (by rfl) ⟨701018, by rfl⟩ : syracuseStep 934691 = 1402037) B1402037
theorem B934721 : Blo 622298 934721 := bstep (se 2 (by rfl) ⟨350520, by rfl⟩ : syracuseStep 934721 = 701041) B701041
theorem B1000259 : Blo 622298 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B934739 : Blo 622298 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B1000291 : Blo 622298 1000291 := bstep (se 1 (by rfl) ⟨750218, by rfl⟩ : syracuseStep 1000291 = 1500437) B1500437
theorem B934769 : Blo 622298 934769 := bstep (se 2 (by rfl) ⟨350538, by rfl⟩ : syracuseStep 934769 = 701077) B701077
theorem B1622897 : Blo 622298 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B934787 : Blo 622298 934787 := bstep (se 1 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 934787 = 1402181) B1402181
theorem B902035 : Blo 622298 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B934817 : Blo 622298 934817 := bstep (se 2 (by rfl) ⟨350556, by rfl⟩ : syracuseStep 934817 = 701113) B701113
theorem B934835 : Blo 622298 934835 := bstep (se 1 (by rfl) ⟨701126, by rfl⟩ : syracuseStep 934835 = 1402253) B1402253
theorem B934865 : Blo 622298 934865 := bstep (se 2 (by rfl) ⟨350574, by rfl⟩ : syracuseStep 934865 = 701149) B701149
theorem B934883 : Blo 622298 934883 := bstep (se 1 (by rfl) ⟨701162, by rfl⟩ : syracuseStep 934883 = 1402325) B1402325
theorem B934913 : Blo 622298 934913 := bstep (se 2 (by rfl) ⟨350592, by rfl⟩ : syracuseStep 934913 = 701185) B701185
theorem B934931 : Blo 622298 934931 := bstep (se 1 (by rfl) ⟨701198, by rfl⟩ : syracuseStep 934931 = 1402397) B1402397
theorem B934961 : Blo 622298 934961 := bstep (se 2 (by rfl) ⟨350610, by rfl⟩ : syracuseStep 934961 = 701221) B701221
theorem B934979 : Blo 622298 934979 := bstep (se 1 (by rfl) ⟨701234, by rfl⟩ : syracuseStep 934979 = 1402469) B1402469
theorem B4736069 : Blo 622298 4736069 := bstep (se 4 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 4736069 = 888013) B888013
theorem B935009 : Blo 622298 935009 := bstep (se 2 (by rfl) ⟨350628, by rfl⟩ : syracuseStep 935009 = 701257) B701257
theorem B935027 : Blo 622298 935027 := bstep (se 1 (by rfl) ⟨701270, by rfl⟩ : syracuseStep 935027 = 1402541) B1402541
theorem B3458189 : Blo 622298 3458189 := bstep (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) B1296821
theorem B935057 : Blo 622298 935057 := bstep (se 2 (by rfl) ⟨350646, by rfl⟩ : syracuseStep 935057 = 701293) B701293
theorem B935075 : Blo 622298 935075 := bstep (se 1 (by rfl) ⟨701306, by rfl⟩ : syracuseStep 935075 = 1402613) B1402613
theorem B935105 : Blo 622298 935105 := bstep (se 2 (by rfl) ⟨350664, by rfl⟩ : syracuseStep 935105 = 701329) B701329
theorem B935123 : Blo 622298 935123 := bstep (se 1 (by rfl) ⟨701342, by rfl⟩ : syracuseStep 935123 = 1402685) B1402685
theorem B935153 : Blo 622298 935153 := bstep (se 2 (by rfl) ⟨350682, by rfl⟩ : syracuseStep 935153 = 701365) B701365
theorem B935171 : Blo 622298 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B935201 : Blo 622298 935201 := bstep (se 2 (by rfl) ⟨350700, by rfl⟩ : syracuseStep 935201 = 701401) B701401
theorem B935219 : Blo 622298 935219 := bstep (se 1 (by rfl) ⟨701414, by rfl⟩ : syracuseStep 935219 = 1402829) B1402829
theorem B1066321 : Blo 622298 1066321 := bstep (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) B799741
theorem B935249 : Blo 622298 935249 := bstep (se 2 (by rfl) ⟨350718, by rfl⟩ : syracuseStep 935249 = 701437) B701437
theorem B935267 : Blo 622298 935267 := bstep (se 1 (by rfl) ⟨701450, by rfl⟩ : syracuseStep 935267 = 1402901) B1402901
theorem B935297 : Blo 622298 935297 := bstep (se 2 (by rfl) ⟨350736, by rfl⟩ : syracuseStep 935297 = 701473) B701473
theorem B935315 : Blo 622298 935315 := bstep (se 1 (by rfl) ⟨701486, by rfl⟩ : syracuseStep 935315 = 1402973) B1402973
theorem B935345 : Blo 622298 935345 := bstep (se 2 (by rfl) ⟨350754, by rfl⟩ : syracuseStep 935345 = 701509) B701509
theorem B935363 : Blo 622298 935363 := bstep (se 1 (by rfl) ⟨701522, by rfl⟩ : syracuseStep 935363 = 1403045) B1403045
theorem B935393 : Blo 622298 935393 := bstep (se 2 (by rfl) ⟨350772, by rfl⟩ : syracuseStep 935393 = 701545) B701545
theorem B1426915 : Blo 622298 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B935411 : Blo 622298 935411 := bstep (se 1 (by rfl) ⟨701558, by rfl⟩ : syracuseStep 935411 = 1403117) B1403117
theorem B935441 : Blo 622298 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B935459 : Blo 622298 935459 := bstep (se 1 (by rfl) ⟨701594, by rfl⟩ : syracuseStep 935459 = 1403189) B1403189
theorem B3163697 : Blo 622298 3163697 := bstep (se 2 (by rfl) ⟨1186386, by rfl⟩ : syracuseStep 3163697 = 2372773) B2372773
theorem B935489 : Blo 622298 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B935507 : Blo 622298 935507 := bstep (se 1 (by rfl) ⟨701630, by rfl⟩ : syracuseStep 935507 = 1403261) B1403261
theorem B935537 : Blo 622298 935537 := bstep (se 2 (by rfl) ⟨350826, by rfl⟩ : syracuseStep 935537 = 701653) B701653
theorem B935555 : Blo 622298 935555 := bstep (se 1 (by rfl) ⟨701666, by rfl⟩ : syracuseStep 935555 = 1403333) B1403333
theorem B2246285 : Blo 622298 2246285 := bstep (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) B842357
theorem B935585 : Blo 622298 935585 := bstep (se 2 (by rfl) ⟨350844, by rfl⟩ : syracuseStep 935585 = 701689) B701689
theorem B935603 : Blo 622298 935603 := bstep (se 1 (by rfl) ⟨701702, by rfl⟩ : syracuseStep 935603 = 1403405) B1403405
theorem B2377421 : Blo 622298 2377421 := bstep (se 3 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 2377421 = 891533) B891533
theorem B935633 : Blo 622298 935633 := bstep (se 2 (by rfl) ⟨350862, by rfl⟩ : syracuseStep 935633 = 701725) B701725
theorem B935651 : Blo 622298 935651 := bstep (se 1 (by rfl) ⟨701738, by rfl⟩ : syracuseStep 935651 = 1403477) B1403477
theorem B935681 : Blo 622298 935681 := bstep (se 2 (by rfl) ⟨350880, by rfl⟩ : syracuseStep 935681 = 701761) B701761
theorem B1001219 : Blo 622298 1001219 := bstep (se 1 (by rfl) ⟨750914, by rfl⟩ : syracuseStep 1001219 = 1501829) B1501829
theorem B935699 : Blo 622298 935699 := bstep (se 1 (by rfl) ⟨701774, by rfl⟩ : syracuseStep 935699 = 1403549) B1403549
theorem B3557155 : Blo 622298 3557155 := bstep (se 1 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 3557155 = 5335733) B5335733
theorem B935729 : Blo 622298 935729 := bstep (se 2 (by rfl) ⟨350898, by rfl⟩ : syracuseStep 935729 = 701797) B701797
theorem B935747 : Blo 622298 935747 := bstep (se 1 (by rfl) ⟨701810, by rfl⟩ : syracuseStep 935747 = 1403621) B1403621
theorem B1001297 : Blo 622298 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B935777 : Blo 622298 935777 := bstep (se 2 (by rfl) ⟨350916, by rfl⟩ : syracuseStep 935777 = 701833) B701833
theorem B935795 : Blo 622298 935795 := bstep (se 1 (by rfl) ⟨701846, by rfl⟩ : syracuseStep 935795 = 1403693) B1403693
theorem B935825 : Blo 622298 935825 := bstep (se 2 (by rfl) ⟨350934, by rfl⟩ : syracuseStep 935825 = 701869) B701869
theorem B640915 : Blo 622298 640915 := bstep (se 1 (by rfl) ⟨480686, by rfl⟩ : syracuseStep 640915 = 961373) B961373
theorem B935843 : Blo 622298 935843 := bstep (se 1 (by rfl) ⟨701882, by rfl⟩ : syracuseStep 935843 = 1403765) B1403765
theorem B935873 : Blo 622298 935873 := bstep (se 2 (by rfl) ⟨350952, by rfl⟩ : syracuseStep 935873 = 701905) B701905
theorem B5392325 : Blo 622298 5392325 := bstep (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) B1011061
theorem B935891 : Blo 622298 935891 := bstep (se 1 (by rfl) ⟨701918, by rfl⟩ : syracuseStep 935891 = 1403837) B1403837
theorem B1066979 : Blo 622298 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B935921 : Blo 622298 935921 := bstep (se 2 (by rfl) ⟨350970, by rfl⟩ : syracuseStep 935921 = 701941) B701941
theorem B903155 : Blo 622298 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B935939 : Blo 622298 935939 := bstep (se 1 (by rfl) ⟨701954, by rfl⟩ : syracuseStep 935939 = 1403909) B1403909
theorem B935969 : Blo 622298 935969 := bstep (se 2 (by rfl) ⟨350988, by rfl⟩ : syracuseStep 935969 = 701977) B701977
theorem B1001521 : Blo 622298 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B935987 : Blo 622298 935987 := bstep (se 1 (by rfl) ⟨701990, by rfl⟩ : syracuseStep 935987 = 1403981) B1403981
theorem B936017 : Blo 622298 936017 := bstep (se 2 (by rfl) ⟨351006, by rfl⟩ : syracuseStep 936017 = 702013) B702013
theorem B936035 : Blo 622298 936035 := bstep (se 1 (by rfl) ⟨702026, by rfl⟩ : syracuseStep 936035 = 1404053) B1404053
theorem B936065 : Blo 622298 936065 := bstep (se 2 (by rfl) ⟨351024, by rfl⟩ : syracuseStep 936065 = 702049) B702049
theorem B936083 : Blo 622298 936083 := bstep (se 1 (by rfl) ⟨702062, by rfl⟩ : syracuseStep 936083 = 1404125) B1404125
theorem B936113 : Blo 622298 936113 := bstep (se 2 (by rfl) ⟨351042, by rfl⟩ : syracuseStep 936113 = 702085) B702085
theorem B1329347 : Blo 622298 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B936131 : Blo 622298 936131 := bstep (se 1 (by rfl) ⟨702098, by rfl⟩ : syracuseStep 936131 = 1404197) B1404197
theorem B7981253 : Blo 622298 7981253 := bstep (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) B1496485
theorem B936161 : Blo 622298 936161 := bstep (se 2 (by rfl) ⟨351060, by rfl⟩ : syracuseStep 936161 = 702121) B702121
theorem B936179 : Blo 622298 936179 := bstep (se 1 (by rfl) ⟨702134, by rfl⟩ : syracuseStep 936179 = 1404269) B1404269
theorem B2672909 : Blo 622298 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B936209 : Blo 622298 936209 := bstep (se 2 (by rfl) ⟨351078, by rfl⟩ : syracuseStep 936209 = 702157) B702157
theorem B936227 : Blo 622298 936227 := bstep (se 1 (by rfl) ⟨702170, by rfl⟩ : syracuseStep 936227 = 1404341) B1404341
theorem B3557681 : Blo 622298 3557681 := bstep (se 2 (by rfl) ⟨1334130, by rfl⟩ : syracuseStep 3557681 = 2668261) B2668261
theorem B936257 : Blo 622298 936257 := bstep (se 2 (by rfl) ⟨351096, by rfl⟩ : syracuseStep 936257 = 702193) B702193
theorem B936275 : Blo 622298 936275 := bstep (se 1 (by rfl) ⟨702206, by rfl⟩ : syracuseStep 936275 = 1404413) B1404413
theorem B936305 : Blo 622298 936305 := bstep (se 2 (by rfl) ⟨351114, by rfl⟩ : syracuseStep 936305 = 702229) B702229
theorem B936323 : Blo 622298 936323 := bstep (se 1 (by rfl) ⟨702242, by rfl⟩ : syracuseStep 936323 = 1404485) B1404485
theorem B936353 : Blo 622298 936353 := bstep (se 2 (by rfl) ⟨351132, by rfl⟩ : syracuseStep 936353 = 702265) B702265
theorem B936371 : Blo 622298 936371 := bstep (se 1 (by rfl) ⟨702278, by rfl⟩ : syracuseStep 936371 = 1404557) B1404557
theorem B8014261 : Blo 622298 8014261 := bstep (se 5 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 8014261 = 751337) B751337
theorem B936401 : Blo 622298 936401 := bstep (se 2 (by rfl) ⟨351150, by rfl⟩ : syracuseStep 936401 = 702301) B702301
theorem B936419 : Blo 622298 936419 := bstep (se 1 (by rfl) ⟨702314, by rfl⟩ : syracuseStep 936419 = 1404629) B1404629
theorem B936449 : Blo 622298 936449 := bstep (se 2 (by rfl) ⟨351168, by rfl⟩ : syracuseStep 936449 = 702337) B702337
theorem B936467 : Blo 622298 936467 := bstep (se 1 (by rfl) ⟨702350, by rfl⟩ : syracuseStep 936467 = 1404701) B1404701
theorem B936497 : Blo 622298 936497 := bstep (se 2 (by rfl) ⟨351186, by rfl⟩ : syracuseStep 936497 = 702373) B702373
theorem B936515 : Blo 622298 936515 := bstep (se 1 (by rfl) ⟨702386, by rfl⟩ : syracuseStep 936515 = 1404773) B1404773
theorem B936545 : Blo 622298 936545 := bstep (se 2 (by rfl) ⟨351204, by rfl⟩ : syracuseStep 936545 = 702409) B702409
theorem B936563 : Blo 622298 936563 := bstep (se 1 (by rfl) ⟨702422, by rfl⟩ : syracuseStep 936563 = 1404845) B1404845
theorem B936593 : Blo 622298 936593 := bstep (se 2 (by rfl) ⟨351222, by rfl⟩ : syracuseStep 936593 = 702445) B702445
theorem B936611 : Blo 622298 936611 := bstep (se 1 (by rfl) ⟨702458, by rfl⟩ : syracuseStep 936611 = 1404917) B1404917
theorem B1821361 : Blo 622298 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B936641 : Blo 622298 936641 := bstep (se 2 (by rfl) ⟨351240, by rfl⟩ : syracuseStep 936641 = 702481) B702481
theorem B936659 : Blo 622298 936659 := bstep (se 1 (by rfl) ⟨702494, by rfl⟩ : syracuseStep 936659 = 1404989) B1404989
theorem B936689 : Blo 622298 936689 := bstep (se 2 (by rfl) ⟨351258, by rfl⟩ : syracuseStep 936689 = 702517) B702517
theorem B936707 : Blo 622298 936707 := bstep (se 1 (by rfl) ⟨702530, by rfl⟩ : syracuseStep 936707 = 1405061) B1405061
theorem B936737 : Blo 622298 936737 := bstep (se 2 (by rfl) ⟨351276, by rfl⟩ : syracuseStep 936737 = 702553) B702553
theorem B936755 : Blo 622298 936755 := bstep (se 1 (by rfl) ⟨702566, by rfl⟩ : syracuseStep 936755 = 1405133) B1405133
theorem B1690445 : Blo 622298 1690445 := bstep (se 3 (by rfl) ⟨316958, by rfl⟩ : syracuseStep 1690445 = 633917) B633917
theorem B936785 : Blo 622298 936785 := bstep (se 2 (by rfl) ⟨351294, by rfl⟩ : syracuseStep 936785 = 702589) B702589
theorem B936803 : Blo 622298 936803 := bstep (se 1 (by rfl) ⟨702602, by rfl⟩ : syracuseStep 936803 = 1405205) B1405205
theorem B936833 : Blo 622298 936833 := bstep (se 2 (by rfl) ⟨351312, by rfl⟩ : syracuseStep 936833 = 702625) B702625
theorem B936851 : Blo 622298 936851 := bstep (se 1 (by rfl) ⟨702638, by rfl⟩ : syracuseStep 936851 = 1405277) B1405277
theorem B936881 : Blo 622298 936881 := bstep (se 2 (by rfl) ⟨351330, by rfl⟩ : syracuseStep 936881 = 702661) B702661
theorem B936899 : Blo 622298 936899 := bstep (se 1 (by rfl) ⟨702674, by rfl⟩ : syracuseStep 936899 = 1405349) B1405349
theorem B936929 : Blo 622298 936929 := bstep (se 2 (by rfl) ⟨351348, by rfl⟩ : syracuseStep 936929 = 702697) B702697
theorem B3165155 : Blo 622298 3165155 := bstep (se 1 (by rfl) ⟨2373866, by rfl⟩ : syracuseStep 3165155 = 4747733) B4747733
theorem B936947 : Blo 622298 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B936977 : Blo 622298 936977 := bstep (se 2 (by rfl) ⟨351366, by rfl⟩ : syracuseStep 936977 = 702733) B702733
theorem B936995 : Blo 622298 936995 := bstep (se 1 (by rfl) ⟨702746, by rfl⟩ : syracuseStep 936995 = 1405493) B1405493
theorem B937025 : Blo 622298 937025 := bstep (se 2 (by rfl) ⟨351384, by rfl⟩ : syracuseStep 937025 = 702769) B702769
theorem B937043 : Blo 622298 937043 := bstep (se 1 (by rfl) ⟨702782, by rfl⟩ : syracuseStep 937043 = 1405565) B1405565
theorem B937073 : Blo 622298 937073 := bstep (se 2 (by rfl) ⟨351402, by rfl⟩ : syracuseStep 937073 = 702805) B702805
theorem B937091 : Blo 622298 937091 := bstep (se 1 (by rfl) ⟨702818, by rfl⟩ : syracuseStep 937091 = 1405637) B1405637
theorem B937121 : Blo 622298 937121 := bstep (se 2 (by rfl) ⟨351420, by rfl⟩ : syracuseStep 937121 = 702841) B702841
theorem B937139 : Blo 622298 937139 := bstep (se 1 (by rfl) ⟨702854, by rfl⟩ : syracuseStep 937139 = 1405709) B1405709
theorem B937169 : Blo 622298 937169 := bstep (se 2 (by rfl) ⟨351438, by rfl⟩ : syracuseStep 937169 = 702877) B702877
theorem B937187 : Blo 622298 937187 := bstep (se 1 (by rfl) ⟨702890, by rfl⟩ : syracuseStep 937187 = 1405781) B1405781
theorem B937217 : Blo 622298 937217 := bstep (se 2 (by rfl) ⟨351456, by rfl⟩ : syracuseStep 937217 = 702913) B702913
theorem B937235 : Blo 622298 937235 := bstep (se 1 (by rfl) ⟨702926, by rfl⟩ : syracuseStep 937235 = 1405853) B1405853
theorem B937265 : Blo 622298 937265 := bstep (se 2 (by rfl) ⟨351474, by rfl⟩ : syracuseStep 937265 = 702949) B702949
theorem B937283 : Blo 622298 937283 := bstep (se 1 (by rfl) ⟨702962, by rfl⟩ : syracuseStep 937283 = 1405925) B1405925
theorem B937313 : Blo 622298 937313 := bstep (se 2 (by rfl) ⟨351492, by rfl⟩ : syracuseStep 937313 = 702985) B702985
theorem B937331 : Blo 622298 937331 := bstep (se 1 (by rfl) ⟨702998, by rfl⟩ : syracuseStep 937331 = 1405997) B1405997
theorem B1330577 : Blo 622298 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B937361 : Blo 622298 937361 := bstep (se 2 (by rfl) ⟨351510, by rfl⟩ : syracuseStep 937361 = 703021) B703021
theorem B937379 : Blo 622298 937379 := bstep (se 1 (by rfl) ⟨703034, by rfl⟩ : syracuseStep 937379 = 1406069) B1406069
theorem B937409 : Blo 622298 937409 := bstep (se 2 (by rfl) ⟨351528, by rfl⟩ : syracuseStep 937409 = 703057) B703057
theorem B937427 : Blo 622298 937427 := bstep (se 1 (by rfl) ⟨703070, by rfl⟩ : syracuseStep 937427 = 1406141) B1406141
theorem B937457 : Blo 622298 937457 := bstep (se 2 (by rfl) ⟨351546, by rfl⟩ : syracuseStep 937457 = 703093) B703093
theorem B937475 : Blo 622298 937475 := bstep (se 1 (by rfl) ⟨703106, by rfl⟩ : syracuseStep 937475 = 1406213) B1406213
theorem B937505 : Blo 622298 937505 := bstep (se 2 (by rfl) ⟨351564, by rfl⟩ : syracuseStep 937505 = 703129) B703129
theorem B937523 : Blo 622298 937523 := bstep (se 1 (by rfl) ⟨703142, by rfl⟩ : syracuseStep 937523 = 1406285) B1406285
theorem B4279877 : Blo 622298 4279877 := bstep (se 4 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 4279877 = 802477) B802477
theorem B937553 : Blo 622298 937553 := bstep (se 2 (by rfl) ⟨351582, by rfl⟩ : syracuseStep 937553 = 703165) B703165
theorem B937571 : Blo 622298 937571 := bstep (se 1 (by rfl) ⟨703178, by rfl⟩ : syracuseStep 937571 = 1406357) B1406357
theorem B937601 : Blo 622298 937601 := bstep (se 2 (by rfl) ⟨351600, by rfl⟩ : syracuseStep 937601 = 703201) B703201
theorem B937619 : Blo 622298 937619 := bstep (se 1 (by rfl) ⟨703214, by rfl⟩ : syracuseStep 937619 = 1406429) B1406429
theorem B937649 : Blo 622298 937649 := bstep (se 2 (by rfl) ⟨351618, by rfl⟩ : syracuseStep 937649 = 703237) B703237
theorem B937667 : Blo 622298 937667 := bstep (se 1 (by rfl) ⟨703250, by rfl⟩ : syracuseStep 937667 = 1406501) B1406501
theorem B937697 : Blo 622298 937697 := bstep (se 2 (by rfl) ⟨351636, by rfl⟩ : syracuseStep 937697 = 703273) B703273
theorem B3559139 : Blo 622298 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B5328625 : Blo 622298 5328625 := bstep (se 2 (by rfl) ⟨1998234, by rfl⟩ : syracuseStep 5328625 = 3996469) B3996469
theorem B937715 : Blo 622298 937715 := bstep (se 1 (by rfl) ⟨703286, by rfl⟩ : syracuseStep 937715 = 1406573) B1406573
theorem B3165965 : Blo 622298 3165965 := bstep (se 3 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 3165965 = 1187237) B1187237
theorem B937745 : Blo 622298 937745 := bstep (se 2 (by rfl) ⟨351654, by rfl⟩ : syracuseStep 937745 = 703309) B703309
theorem B937763 : Blo 622298 937763 := bstep (se 1 (by rfl) ⟨703322, by rfl⟩ : syracuseStep 937763 = 1406645) B1406645
theorem B937793 : Blo 622298 937793 := bstep (se 2 (by rfl) ⟨351672, by rfl⟩ : syracuseStep 937793 = 703345) B703345
theorem B937811 : Blo 622298 937811 := bstep (se 1 (by rfl) ⟨703358, by rfl⟩ : syracuseStep 937811 = 1406717) B1406717
theorem B937841 : Blo 622298 937841 := bstep (se 2 (by rfl) ⟨351690, by rfl⟩ : syracuseStep 937841 = 703381) B703381
theorem B937859 : Blo 622298 937859 := bstep (se 1 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 937859 = 1406789) B1406789
theorem B937889 : Blo 622298 937889 := bstep (se 2 (by rfl) ⟨351708, by rfl⟩ : syracuseStep 937889 = 703417) B703417
theorem B937907 : Blo 622298 937907 := bstep (se 1 (by rfl) ⟨703430, by rfl⟩ : syracuseStep 937907 = 1406861) B1406861
theorem B7131077 : Blo 622298 7131077 := bstep (se 4 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 7131077 = 1337077) B1337077
theorem B937937 : Blo 622298 937937 := bstep (se 2 (by rfl) ⟨351726, by rfl⟩ : syracuseStep 937937 = 703453) B703453
theorem B937955 : Blo 622298 937955 := bstep (se 1 (by rfl) ⟨703466, by rfl⟩ : syracuseStep 937955 = 1406933) B1406933
theorem B937985 : Blo 622298 937985 := bstep (se 2 (by rfl) ⟨351744, by rfl⟩ : syracuseStep 937985 = 703489) B703489
theorem B938003 : Blo 622298 938003 := bstep (se 1 (by rfl) ⟨703502, by rfl⟩ : syracuseStep 938003 = 1407005) B1407005
theorem B938033 : Blo 622298 938033 := bstep (se 2 (by rfl) ⟨351762, by rfl⟩ : syracuseStep 938033 = 703525) B703525
theorem B938051 : Blo 622298 938051 := bstep (se 1 (by rfl) ⟨703538, by rfl⟩ : syracuseStep 938051 = 1407077) B1407077
theorem B938081 : Blo 622298 938081 := bstep (se 2 (by rfl) ⟨351780, by rfl⟩ : syracuseStep 938081 = 703561) B703561
theorem B3002467 : Blo 622298 3002467 := bstep (se 1 (by rfl) ⟨2251850, by rfl⟩ : syracuseStep 3002467 = 4503701) B4503701
theorem B30363761 : Blo 622298 30363761 := bstep (se 2 (by rfl) ⟨11386410, by rfl⟩ : syracuseStep 30363761 = 22772821) B22772821
theorem B938099 : Blo 622298 938099 := bstep (se 1 (by rfl) ⟨703574, by rfl⟩ : syracuseStep 938099 = 1407149) B1407149
theorem B938129 : Blo 622298 938129 := bstep (se 2 (by rfl) ⟨351798, by rfl⟩ : syracuseStep 938129 = 703597) B703597
theorem B938147 : Blo 622298 938147 := bstep (se 1 (by rfl) ⟨703610, by rfl⟩ : syracuseStep 938147 = 1407221) B1407221
theorem B938177 : Blo 622298 938177 := bstep (se 2 (by rfl) ⟨351816, by rfl⟩ : syracuseStep 938177 = 703633) B703633
theorem B938195 : Blo 622298 938195 := bstep (se 1 (by rfl) ⟨703646, by rfl⟩ : syracuseStep 938195 = 1407293) B1407293
theorem B1069283 : Blo 622298 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B938225 : Blo 622298 938225 := bstep (se 2 (by rfl) ⟨351834, by rfl⟩ : syracuseStep 938225 = 703669) B703669
theorem B938243 : Blo 622298 938243 := bstep (se 1 (by rfl) ⟨703682, by rfl⟩ : syracuseStep 938243 = 1407365) B1407365
theorem B1331473 : Blo 622298 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B938273 : Blo 622298 938273 := bstep (se 2 (by rfl) ⟨351852, by rfl⟩ : syracuseStep 938273 = 703705) B703705
theorem B1331491 : Blo 622298 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B938291 : Blo 622298 938291 := bstep (se 1 (by rfl) ⟨703718, by rfl⟩ : syracuseStep 938291 = 1407437) B1407437
theorem B938321 : Blo 622298 938321 := bstep (se 2 (by rfl) ⟨351870, by rfl⟩ : syracuseStep 938321 = 703741) B703741
theorem B938339 : Blo 622298 938339 := bstep (se 1 (by rfl) ⟨703754, by rfl⟩ : syracuseStep 938339 = 1407509) B1407509
theorem B938369 : Blo 622298 938369 := bstep (se 2 (by rfl) ⟨351888, by rfl⟩ : syracuseStep 938369 = 703777) B703777
theorem B938387 : Blo 622298 938387 := bstep (se 1 (by rfl) ⟨703790, by rfl⟩ : syracuseStep 938387 = 1407581) B1407581
theorem B938417 : Blo 622298 938417 := bstep (se 2 (by rfl) ⟨351906, by rfl⟩ : syracuseStep 938417 = 703813) B703813
theorem B938435 : Blo 622298 938435 := bstep (se 1 (by rfl) ⟨703826, by rfl⟩ : syracuseStep 938435 = 1407653) B1407653
theorem B938465 : Blo 622298 938465 := bstep (se 2 (by rfl) ⟨351924, by rfl⟩ : syracuseStep 938465 = 703849) B703849
theorem B938483 : Blo 622298 938483 := bstep (se 1 (by rfl) ⟨703862, by rfl⟩ : syracuseStep 938483 = 1407725) B1407725
theorem B938513 : Blo 622298 938513 := bstep (se 2 (by rfl) ⟨351942, by rfl⟩ : syracuseStep 938513 = 703885) B703885
theorem B938531 : Blo 622298 938531 := bstep (se 1 (by rfl) ⟨703898, by rfl⟩ : syracuseStep 938531 = 1407797) B1407797
theorem B1495601 : Blo 622298 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B938561 : Blo 622298 938561 := bstep (se 2 (by rfl) ⟨351960, by rfl⟩ : syracuseStep 938561 = 703921) B703921
theorem B938579 : Blo 622298 938579 := bstep (se 1 (by rfl) ⟨703934, by rfl⟩ : syracuseStep 938579 = 1407869) B1407869
theorem B2249315 : Blo 622298 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B938609 : Blo 622298 938609 := bstep (se 2 (by rfl) ⟨351978, by rfl⟩ : syracuseStep 938609 = 703957) B703957
theorem B938627 : Blo 622298 938627 := bstep (se 1 (by rfl) ⟨703970, by rfl⟩ : syracuseStep 938627 = 1407941) B1407941
theorem B938657 : Blo 622298 938657 := bstep (se 2 (by rfl) ⟨351996, by rfl⟩ : syracuseStep 938657 = 703993) B703993
theorem B938675 : Blo 622298 938675 := bstep (se 1 (by rfl) ⟨704006, by rfl⟩ : syracuseStep 938675 = 1408013) B1408013
theorem B938705 : Blo 622298 938705 := bstep (se 2 (by rfl) ⟨352014, by rfl⟩ : syracuseStep 938705 = 704029) B704029
theorem B938723 : Blo 622298 938723 := bstep (se 1 (by rfl) ⟨704042, by rfl⟩ : syracuseStep 938723 = 1408085) B1408085
theorem B938753 : Blo 622298 938753 := bstep (se 2 (by rfl) ⟨352032, by rfl⟩ : syracuseStep 938753 = 704065) B704065
theorem B3429125 : Blo 622298 3429125 := bstep (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) B642961
theorem B938771 : Blo 622298 938771 := bstep (se 1 (by rfl) ⟨704078, by rfl⟩ : syracuseStep 938771 = 1408157) B1408157
theorem B938801 : Blo 622298 938801 := bstep (se 2 (by rfl) ⟨352050, by rfl⟩ : syracuseStep 938801 = 704101) B704101
theorem B938819 : Blo 622298 938819 := bstep (se 1 (by rfl) ⟨704114, by rfl⟩ : syracuseStep 938819 = 1408229) B1408229
theorem B938849 : Blo 622298 938849 := bstep (se 2 (by rfl) ⟨352068, by rfl⟩ : syracuseStep 938849 = 704137) B704137
theorem B938867 : Blo 622298 938867 := bstep (se 1 (by rfl) ⟨704150, by rfl⟩ : syracuseStep 938867 = 1408301) B1408301
theorem B938897 : Blo 622298 938897 := bstep (se 2 (by rfl) ⟨352086, by rfl⟩ : syracuseStep 938897 = 704173) B704173
theorem B938915 : Blo 622298 938915 := bstep (se 1 (by rfl) ⟨704186, by rfl⟩ : syracuseStep 938915 = 1408373) B1408373
theorem B938945 : Blo 622298 938945 := bstep (se 2 (by rfl) ⟨352104, by rfl⟩ : syracuseStep 938945 = 704209) B704209
theorem B938963 : Blo 622298 938963 := bstep (se 1 (by rfl) ⟨704222, by rfl⟩ : syracuseStep 938963 = 1408445) B1408445
theorem B5985251 : Blo 622298 5985251 := bstep (se 1 (by rfl) ⟨4488938, by rfl⟩ : syracuseStep 5985251 = 8977877) B8977877
theorem B938993 : Blo 622298 938993 := bstep (se 2 (by rfl) ⟨352122, by rfl⟩ : syracuseStep 938993 = 704245) B704245
theorem B1922051 : Blo 622298 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B939011 : Blo 622298 939011 := bstep (se 1 (by rfl) ⟨704258, by rfl⟩ : syracuseStep 939011 = 1408517) B1408517
theorem B939041 : Blo 622298 939041 := bstep (se 2 (by rfl) ⟨352140, by rfl⟩ : syracuseStep 939041 = 704281) B704281
theorem B939059 : Blo 622298 939059 := bstep (se 1 (by rfl) ⟨704294, by rfl⟩ : syracuseStep 939059 = 1408589) B1408589
theorem B939089 : Blo 622298 939089 := bstep (se 2 (by rfl) ⟨352158, by rfl⟩ : syracuseStep 939089 = 704317) B704317
theorem B939107 : Blo 622298 939107 := bstep (se 1 (by rfl) ⟨704330, by rfl⟩ : syracuseStep 939107 = 1408661) B1408661
theorem B939137 : Blo 622298 939137 := bstep (se 2 (by rfl) ⟨352176, by rfl⟩ : syracuseStep 939137 = 704353) B704353
theorem B939155 : Blo 622298 939155 := bstep (se 1 (by rfl) ⟨704366, by rfl⟩ : syracuseStep 939155 = 1408733) B1408733
theorem B939185 : Blo 622298 939185 := bstep (se 2 (by rfl) ⟨352194, by rfl⟩ : syracuseStep 939185 = 704389) B704389
theorem B939203 : Blo 622298 939203 := bstep (se 1 (by rfl) ⟨704402, by rfl⟩ : syracuseStep 939203 = 1408805) B1408805
theorem B939233 : Blo 622298 939233 := bstep (se 2 (by rfl) ⟨352212, by rfl⟩ : syracuseStep 939233 = 704425) B704425
theorem B939251 : Blo 622298 939251 := bstep (se 1 (by rfl) ⟨704438, by rfl⟩ : syracuseStep 939251 = 1408877) B1408877
theorem B939281 : Blo 622298 939281 := bstep (se 2 (by rfl) ⟨352230, by rfl⟩ : syracuseStep 939281 = 704461) B704461
theorem B939299 : Blo 622298 939299 := bstep (se 1 (by rfl) ⟨704474, by rfl⟩ : syracuseStep 939299 = 1408949) B1408949
theorem B939329 : Blo 622298 939329 := bstep (se 2 (by rfl) ⟨352248, by rfl⟩ : syracuseStep 939329 = 704497) B704497
theorem B939347 : Blo 622298 939347 := bstep (se 1 (by rfl) ⟨704510, by rfl⟩ : syracuseStep 939347 = 1409021) B1409021
theorem B939377 : Blo 622298 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B939395 : Blo 622298 939395 := bstep (se 1 (by rfl) ⟨704546, by rfl⟩ : syracuseStep 939395 = 1409093) B1409093
theorem B939425 : Blo 622298 939425 := bstep (se 2 (by rfl) ⟨352284, by rfl⟩ : syracuseStep 939425 = 704569) B704569
theorem B939443 : Blo 622298 939443 := bstep (se 1 (by rfl) ⟨704582, by rfl⟩ : syracuseStep 939443 = 1409165) B1409165
theorem B3561029 : Blo 622298 3561029 := bstep (se 4 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 3561029 = 667693) B667693
theorem B5986061 : Blo 622298 5986061 := bstep (se 3 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 5986061 = 2244773) B2244773
theorem B2250929 : Blo 622298 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B1267939 : Blo 622298 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B1497361 : Blo 622298 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B1136963 : Blo 622298 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B9624035 : Blo 622298 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B1333763 : Blo 622298 1333763 := bstep (se 1 (by rfl) ⟨1000322, by rfl⟩ : syracuseStep 1333763 = 2000645) B2000645
theorem B3005041 : Blo 622298 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B3168881 : Blo 622298 3168881 := bstep (se 2 (by rfl) ⟨1188330, by rfl⟩ : syracuseStep 3168881 = 2376661) B2376661
theorem B842465 : Blo 622298 842465 := bstep (se 2 (by rfl) ⟨315924, by rfl⟩ : syracuseStep 842465 = 631849) B631849
theorem B4741901 : Blo 622298 4741901 := bstep (se 3 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 4741901 = 1778213) B1778213
theorem B1334225 : Blo 622298 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B711779 : Blo 622298 711779 := bstep (se 1 (by rfl) ⟨533834, by rfl⟩ : syracuseStep 711779 = 1067669) B1067669
theorem B1400273 : Blo 622298 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B1400291 : Blo 622298 1400291 := bstep (se 1 (by rfl) ⟨1050218, by rfl⟩ : syracuseStep 1400291 = 2100437) B2100437
theorem B1400561 : Blo 622298 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B1400579 : Blo 622298 1400579 := bstep (se 1 (by rfl) ⟨1050434, by rfl⟩ : syracuseStep 1400579 = 2100869) B2100869
theorem B3792653 : Blo 622298 3792653 := bstep (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) B1422245
theorem B1400849 : Blo 622298 1400849 := bstep (se 2 (by rfl) ⟨525318, by rfl⟩ : syracuseStep 1400849 = 1050637) B1050637
theorem B1400867 : Blo 622298 1400867 := bstep (se 1 (by rfl) ⟨1050650, by rfl⟩ : syracuseStep 1400867 = 2101301) B2101301
theorem B3170339 : Blo 622298 3170339 := bstep (se 1 (by rfl) ⟨2377754, by rfl⟩ : syracuseStep 3170339 = 4755509) B4755509
theorem B3989681 : Blo 622298 3989681 := bstep (se 2 (by rfl) ⟨1496130, by rfl⟩ : syracuseStep 3989681 = 2992261) B2992261
theorem B2253005 : Blo 622298 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B1335523 : Blo 622298 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B3006733 : Blo 622298 3006733 := bstep (se 3 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 3006733 = 1127525) B1127525
theorem B1401137 : Blo 622298 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B1401155 : Blo 622298 1401155 := bstep (se 1 (by rfl) ⟨1050866, by rfl⟩ : syracuseStep 1401155 = 2101733) B2101733
theorem B1925603 : Blo 622298 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1335779 : Blo 622298 1335779 := bstep (se 1 (by rfl) ⟨1001834, by rfl⟩ : syracuseStep 1335779 = 2003669) B2003669
theorem B1401425 : Blo 622298 1401425 := bstep (se 2 (by rfl) ⟨525534, by rfl⟩ : syracuseStep 1401425 = 1051069) B1051069
theorem B1401443 : Blo 622298 1401443 := bstep (se 1 (by rfl) ⟨1051082, by rfl⟩ : syracuseStep 1401443 = 2102165) B2102165
theorem B3007331 : Blo 622298 3007331 := bstep (se 1 (by rfl) ⟨2255498, by rfl⟩ : syracuseStep 3007331 = 4510997) B4510997
theorem B1401713 : Blo 622298 1401713 := bstep (se 2 (by rfl) ⟨525642, by rfl⟩ : syracuseStep 1401713 = 1051285) B1051285
theorem B1401731 : Blo 622298 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B5333957 : Blo 622298 5333957 := bstep (se 4 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 5333957 = 1000117) B1000117
theorem B1893347 : Blo 622298 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B1402001 : Blo 622298 1402001 := bstep (se 2 (by rfl) ⟨525750, by rfl⟩ : syracuseStep 1402001 = 1051501) B1051501
theorem B1402019 : Blo 622298 1402019 := bstep (se 1 (by rfl) ⟨1051514, by rfl⟩ : syracuseStep 1402019 = 2103029) B2103029
theorem B3794161 : Blo 622298 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B3007793 : Blo 622298 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B2254243 : Blo 622298 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B1402289 : Blo 622298 1402289 := bstep (se 2 (by rfl) ⟨525858, by rfl⟩ : syracuseStep 1402289 = 1051717) B1051717
theorem B1336753 : Blo 622298 1336753 := bstep (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) B1002565
theorem B1402307 : Blo 622298 1402307 := bstep (se 1 (by rfl) ⟨1051730, by rfl⟩ : syracuseStep 1402307 = 2103461) B2103461
theorem B3991139 : Blo 622298 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B3368561 : Blo 622298 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B4744817 : Blo 622298 4744817 := bstep (se 2 (by rfl) ⟨1779306, by rfl⟩ : syracuseStep 4744817 = 3558613) B3558613
theorem B1402577 : Blo 622298 1402577 := bstep (se 2 (by rfl) ⟨525966, by rfl⟩ : syracuseStep 1402577 = 1051933) B1051933
theorem B1402595 : Blo 622298 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B4056803 : Blo 622298 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B4056817 : Blo 622298 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B13526837 : Blo 622298 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B2025425 : Blo 622298 2025425 := bstep (se 2 (by rfl) ⟨759534, by rfl⟩ : syracuseStep 2025425 = 1519069) B1519069
theorem B1402865 : Blo 622298 1402865 := bstep (se 2 (by rfl) ⟨526074, by rfl⟩ : syracuseStep 1402865 = 1052149) B1052149
theorem B1402883 : Blo 622298 1402883 := bstep (se 1 (by rfl) ⟨1052162, by rfl⟩ : syracuseStep 1402883 = 2104325) B2104325
theorem B1337411 : Blo 622298 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B7596101 : Blo 622298 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B1403153 : Blo 622298 1403153 := bstep (se 2 (by rfl) ⟨526182, by rfl⟩ : syracuseStep 1403153 = 1052365) B1052365
theorem B1403171 : Blo 622298 1403171 := bstep (se 1 (by rfl) ⟨1052378, by rfl⟩ : syracuseStep 1403171 = 2104757) B2104757
theorem B3795277 : Blo 622298 3795277 := bstep (se 3 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 3795277 = 1423229) B1423229
theorem B846163 : Blo 622298 846163 := bstep (se 1 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 846163 = 1269245) B1269245
theorem B1894769 : Blo 622298 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B1403441 : Blo 622298 1403441 := bstep (se 2 (by rfl) ⟨526290, by rfl⟩ : syracuseStep 1403441 = 1052581) B1052581
theorem B1403459 : Blo 622298 1403459 := bstep (se 1 (by rfl) ⟨1052594, by rfl⟩ : syracuseStep 1403459 = 2105189) B2105189
theorem B10676933 : Blo 622298 10676933 := bstep (se 4 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 10676933 = 2001925) B2001925
theorem B1403729 : Blo 622298 1403729 := bstep (se 2 (by rfl) ⟨526398, by rfl⟩ : syracuseStep 1403729 = 1052797) B1052797
theorem B748387 : Blo 622298 748387 := bstep (se 1 (by rfl) ⟨561290, by rfl⟩ : syracuseStep 748387 = 1122581) B1122581
theorem B1403747 : Blo 622298 1403747 := bstep (se 1 (by rfl) ⟨1052810, by rfl⟩ : syracuseStep 1403747 = 2105621) B2105621
theorem B748531 : Blo 622298 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B1404017 : Blo 622298 1404017 := bstep (se 2 (by rfl) ⟨526506, by rfl⟩ : syracuseStep 1404017 = 1053013) B1053013
theorem B1404035 : Blo 622298 1404035 := bstep (se 1 (by rfl) ⟨1053026, by rfl⟩ : syracuseStep 1404035 = 2106053) B2106053
theorem B1502435 : Blo 622298 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B3566861 : Blo 622298 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B912691 : Blo 622298 912691 := bstep (se 1 (by rfl) ⟨684518, by rfl⟩ : syracuseStep 912691 = 1369037) B1369037
theorem B1404305 : Blo 622298 1404305 := bstep (se 2 (by rfl) ⟨526614, by rfl⟩ : syracuseStep 1404305 = 1053229) B1053229
theorem B1404323 : Blo 622298 1404323 := bstep (se 1 (by rfl) ⟨1053242, by rfl⟩ : syracuseStep 1404323 = 2106485) B2106485
theorem B1732067 : Blo 622298 1732067 := bstep (se 1 (by rfl) ⟨1299050, by rfl⟩ : syracuseStep 1732067 = 2598101) B2598101
theorem B1994339 : Blo 622298 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B1404593 : Blo 622298 1404593 := bstep (se 2 (by rfl) ⟨526722, by rfl⟩ : syracuseStep 1404593 = 1053445) B1053445
theorem B1404611 : Blo 622298 1404611 := bstep (se 1 (by rfl) ⟨1053458, by rfl⟩ : syracuseStep 1404611 = 2106917) B2106917
theorem B1404881 : Blo 622298 1404881 := bstep (se 2 (by rfl) ⟨526830, by rfl⟩ : syracuseStep 1404881 = 1053661) B1053661
theorem B1404899 : Blo 622298 1404899 := bstep (se 1 (by rfl) ⟨1053674, by rfl⟩ : syracuseStep 1404899 = 2107349) B2107349
theorem B2846897 : Blo 622298 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B1405169 : Blo 622298 1405169 := bstep (se 2 (by rfl) ⟨526938, by rfl⟩ : syracuseStep 1405169 = 1053877) B1053877
theorem B1405187 : Blo 622298 1405187 := bstep (se 1 (by rfl) ⟨1053890, by rfl⟩ : syracuseStep 1405187 = 2107781) B2107781
theorem B1405457 : Blo 622298 1405457 := bstep (se 2 (by rfl) ⟨527046, by rfl⟩ : syracuseStep 1405457 = 1054093) B1054093
theorem B1405475 : Blo 622298 1405475 := bstep (se 1 (by rfl) ⟨1054106, by rfl⟩ : syracuseStep 1405475 = 2108213) B2108213
theorem B1012387 : Blo 622298 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B1405745 : Blo 622298 1405745 := bstep (se 2 (by rfl) ⟨527154, by rfl⟩ : syracuseStep 1405745 = 1054309) B1054309
theorem B1405763 : Blo 622298 1405763 := bstep (se 1 (by rfl) ⟨1054322, by rfl⟩ : syracuseStep 1405763 = 2108645) B2108645
theorem B1602449 : Blo 622298 1602449 := bstep (se 2 (by rfl) ⟨600918, by rfl⟩ : syracuseStep 1602449 = 1201837) B1201837
theorem B5075909 : Blo 622298 5075909 := bstep (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) B951733
theorem B1406033 : Blo 622298 1406033 := bstep (se 2 (by rfl) ⟨527262, by rfl⟩ : syracuseStep 1406033 = 1054525) B1054525
theorem B8090723 : Blo 622298 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B1406051 : Blo 622298 1406051 := bstep (se 1 (by rfl) ⟨1054538, by rfl⟩ : syracuseStep 1406051 = 2109077) B2109077
theorem B7599217 : Blo 622298 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B7206029 : Blo 622298 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B9270413 : Blo 622298 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B3994829 : Blo 622298 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B1996109 : Blo 622298 1996109 := bstep (se 3 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 1996109 = 748541) B748541
theorem B1406321 : Blo 622298 1406321 := bstep (se 2 (by rfl) ⟨527370, by rfl⟩ : syracuseStep 1406321 = 1054741) B1054741
theorem B1406339 : Blo 622298 1406339 := bstep (se 1 (by rfl) ⟨1054754, by rfl⟩ : syracuseStep 1406339 = 2109509) B2109509
theorem B947603 : Blo 622298 947603 := bstep (se 1 (by rfl) ⟨710702, by rfl⟩ : syracuseStep 947603 = 1421405) B1421405
theorem B1406609 : Blo 622298 1406609 := bstep (se 2 (by rfl) ⟨527478, by rfl⟩ : syracuseStep 1406609 = 1054957) B1054957
theorem B1406627 : Blo 622298 1406627 := bstep (se 1 (by rfl) ⟨1054970, by rfl⟩ : syracuseStep 1406627 = 2109941) B2109941
theorem B1898417 : Blo 622298 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1406897 : Blo 622298 1406897 := bstep (se 2 (by rfl) ⟨527586, by rfl⟩ : syracuseStep 1406897 = 1055173) B1055173
theorem B1406915 : Blo 622298 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B1407185 : Blo 622298 1407185 := bstep (se 2 (by rfl) ⟨527694, by rfl⟩ : syracuseStep 1407185 = 1055389) B1055389
theorem B1407203 : Blo 622298 1407203 := bstep (se 1 (by rfl) ⟨1055402, by rfl⟩ : syracuseStep 1407203 = 2110805) B2110805
theorem B1407473 : Blo 622298 1407473 := bstep (se 2 (by rfl) ⟨527802, by rfl⟩ : syracuseStep 1407473 = 1055605) B1055605
theorem B719347 : Blo 622298 719347 := bstep (se 1 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 719347 = 1079021) B1079021
theorem B1407491 : Blo 622298 1407491 := bstep (se 1 (by rfl) ⟨1055618, by rfl⟩ : syracuseStep 1407491 = 2111237) B2111237
theorem B1407761 : Blo 622298 1407761 := bstep (se 2 (by rfl) ⟨527910, by rfl⟩ : syracuseStep 1407761 = 1055821) B1055821
theorem B1407779 : Blo 622298 1407779 := bstep (se 1 (by rfl) ⟨1055834, by rfl⟩ : syracuseStep 1407779 = 2111669) B2111669
theorem B1408049 : Blo 622298 1408049 := bstep (se 2 (by rfl) ⟨528018, by rfl⟩ : syracuseStep 1408049 = 1056037) B1056037
theorem B1408067 : Blo 622298 1408067 := bstep (se 1 (by rfl) ⟨1056050, by rfl⟩ : syracuseStep 1408067 = 2112101) B2112101
theorem B1408337 : Blo 622298 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1408355 : Blo 622298 1408355 := bstep (se 1 (by rfl) ⟨1056266, by rfl⟩ : syracuseStep 1408355 = 2112533) B2112533
theorem B1408625 : Blo 622298 1408625 := bstep (se 2 (by rfl) ⟨528234, by rfl⟩ : syracuseStep 1408625 = 1056469) B1056469
theorem B1408643 : Blo 622298 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B3374789 : Blo 622298 3374789 := bstep (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) B632773
theorem B622307 : Blo 622298 622307 := bstep (se 1 (by rfl) ⟨466730, by rfl⟩ : syracuseStep 622307 = 933461) B933461
theorem B6094577 : Blo 622298 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B622323 : Blo 622298 622323 := bstep (se 1 (by rfl) ⟨466742, by rfl⟩ : syracuseStep 622323 = 933485) B933485
theorem B622339 : Blo 622298 622339 := bstep (se 1 (by rfl) ⟨466754, by rfl⟩ : syracuseStep 622339 = 933509) B933509
theorem B622355 : Blo 622298 622355 := bstep (se 1 (by rfl) ⟨466766, by rfl⟩ : syracuseStep 622355 = 933533) B933533
theorem B622371 : Blo 622298 622371 := bstep (se 1 (by rfl) ⟨466778, by rfl⟩ : syracuseStep 622371 = 933557) B933557
theorem B622387 : Blo 622298 622387 := bstep (se 1 (by rfl) ⟨466790, by rfl⟩ : syracuseStep 622387 = 933581) B933581
theorem B622403 : Blo 622298 622403 := bstep (se 1 (by rfl) ⟨466802, by rfl⟩ : syracuseStep 622403 = 933605) B933605
theorem B622419 : Blo 622298 622419 := bstep (se 1 (by rfl) ⟨466814, by rfl⟩ : syracuseStep 622419 = 933629) B933629
theorem B622435 : Blo 622298 622435 := bstep (se 1 (by rfl) ⟨466826, by rfl⟩ : syracuseStep 622435 = 933653) B933653
theorem B622451 : Blo 622298 622451 := bstep (se 1 (by rfl) ⟨466838, by rfl⟩ : syracuseStep 622451 = 933677) B933677
theorem B622467 : Blo 622298 622467 := bstep (se 1 (by rfl) ⟨466850, by rfl⟩ : syracuseStep 622467 = 933701) B933701
theorem B1408913 : Blo 622298 1408913 := bstep (se 2 (by rfl) ⟨528342, by rfl⟩ : syracuseStep 1408913 = 1056685) B1056685
theorem B622483 : Blo 622298 622483 := bstep (se 1 (by rfl) ⟨466862, by rfl⟩ : syracuseStep 622483 = 933725) B933725
theorem B622499 : Blo 622298 622499 := bstep (se 1 (by rfl) ⟨466874, by rfl⟩ : syracuseStep 622499 = 933749) B933749
theorem B1408931 : Blo 622298 1408931 := bstep (se 1 (by rfl) ⟨1056698, by rfl⟩ : syracuseStep 1408931 = 2113397) B2113397
theorem B622515 : Blo 622298 622515 := bstep (se 1 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 622515 = 933773) B933773
theorem B622531 : Blo 622298 622531 := bstep (se 1 (by rfl) ⟨466898, by rfl⟩ : syracuseStep 622531 = 933797) B933797
theorem B622547 : Blo 622298 622547 := bstep (se 1 (by rfl) ⟨466910, by rfl⟩ : syracuseStep 622547 = 933821) B933821
theorem B622563 : Blo 622298 622563 := bstep (se 1 (by rfl) ⟨466922, by rfl⟩ : syracuseStep 622563 = 933845) B933845
theorem B950243 : Blo 622298 950243 := bstep (se 1 (by rfl) ⟨712682, by rfl⟩ : syracuseStep 950243 = 1425365) B1425365
theorem B622579 : Blo 622298 622579 := bstep (se 1 (by rfl) ⟨466934, by rfl⟩ : syracuseStep 622579 = 933869) B933869
theorem B622603 : Blo 622298 622603 := bstep (se 1 (by rfl) ⟨466952, by rfl⟩ : syracuseStep 622603 = 933905) B933905
theorem B622615 : Blo 622298 622615 := bstep (se 1 (by rfl) ⟨466961, by rfl⟩ : syracuseStep 622615 = 933923) B933923
theorem B622635 : Blo 622298 622635 := bstep (se 1 (by rfl) ⟨466976, by rfl⟩ : syracuseStep 622635 = 933953) B933953
theorem B1409075 : Blo 622298 1409075 := bstep (se 1 (by rfl) ⟨1056806, by rfl⟩ : syracuseStep 1409075 = 2113613) B2113613
theorem B622647 : Blo 622298 622647 := bstep (se 1 (by rfl) ⟨466985, by rfl⟩ : syracuseStep 622647 = 933971) B933971
theorem B622667 : Blo 622298 622667 := bstep (se 1 (by rfl) ⟨467000, by rfl⟩ : syracuseStep 622667 = 934001) B934001
theorem B622679 : Blo 622298 622679 := bstep (se 1 (by rfl) ⟨467009, by rfl⟩ : syracuseStep 622679 = 934019) B934019
theorem B1409111 : Blo 622298 1409111 := bstep (se 1 (by rfl) ⟨1056833, by rfl⟩ : syracuseStep 1409111 = 2113667) B2113667
theorem B622699 : Blo 622298 622699 := bstep (se 1 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 622699 = 934049) B934049
theorem B622711 : Blo 622298 622711 := bstep (se 1 (by rfl) ⟨467033, by rfl⟩ : syracuseStep 622711 = 934067) B934067
theorem B622731 : Blo 622298 622731 := bstep (se 1 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 622731 = 934097) B934097
theorem B622743 : Blo 622298 622743 := bstep (se 1 (by rfl) ⟨467057, by rfl⟩ : syracuseStep 622743 = 934115) B934115
theorem B622763 : Blo 622298 622763 := bstep (se 1 (by rfl) ⟨467072, by rfl⟩ : syracuseStep 622763 = 934145) B934145
theorem B622775 : Blo 622298 622775 := bstep (se 1 (by rfl) ⟨467081, by rfl⟩ : syracuseStep 622775 = 934163) B934163
theorem B622795 : Blo 622298 622795 := bstep (se 1 (by rfl) ⟨467096, by rfl⟩ : syracuseStep 622795 = 934193) B934193
theorem B622807 : Blo 622298 622807 := bstep (se 1 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 622807 = 934211) B934211
theorem B622827 : Blo 622298 622827 := bstep (se 1 (by rfl) ⟨467120, by rfl⟩ : syracuseStep 622827 = 934241) B934241
theorem B622839 : Blo 622298 622839 := bstep (se 1 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 622839 = 934259) B934259
theorem B4751621 : Blo 622298 4751621 := bstep (se 4 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 4751621 = 890929) B890929
theorem B622859 : Blo 622298 622859 := bstep (se 1 (by rfl) ⟨467144, by rfl⟩ : syracuseStep 622859 = 934289) B934289
theorem B622871 : Blo 622298 622871 := bstep (se 1 (by rfl) ⟨467153, by rfl⟩ : syracuseStep 622871 = 934307) B934307
theorem B622891 : Blo 622298 622891 := bstep (se 1 (by rfl) ⟨467168, by rfl⟩ : syracuseStep 622891 = 934337) B934337
theorem B622903 : Blo 622298 622903 := bstep (se 1 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 622903 = 934355) B934355
theorem B622923 : Blo 622298 622923 := bstep (se 1 (by rfl) ⟨467192, by rfl⟩ : syracuseStep 622923 = 934385) B934385
theorem B622935 : Blo 622298 622935 := bstep (se 1 (by rfl) ⟨467201, by rfl⟩ : syracuseStep 622935 = 934403) B934403
theorem B622955 : Blo 622298 622955 := bstep (se 1 (by rfl) ⟨467216, by rfl⟩ : syracuseStep 622955 = 934433) B934433
theorem B622967 : Blo 622298 622967 := bstep (se 1 (by rfl) ⟨467225, by rfl⟩ : syracuseStep 622967 = 934451) B934451
theorem B622987 : Blo 622298 622987 := bstep (se 1 (by rfl) ⟨467240, by rfl⟩ : syracuseStep 622987 = 934481) B934481
theorem B622999 : Blo 622298 622999 := bstep (se 1 (by rfl) ⟨467249, by rfl⟩ : syracuseStep 622999 = 934499) B934499
theorem B623019 : Blo 622298 623019 := bstep (se 1 (by rfl) ⟨467264, by rfl⟩ : syracuseStep 623019 = 934529) B934529
theorem B623031 : Blo 622298 623031 := bstep (se 1 (by rfl) ⟨467273, by rfl⟩ : syracuseStep 623031 = 934547) B934547
theorem B623051 : Blo 622298 623051 := bstep (se 1 (by rfl) ⟨467288, by rfl⟩ : syracuseStep 623051 = 934577) B934577
theorem B623063 : Blo 622298 623063 := bstep (se 1 (by rfl) ⟨467297, by rfl⟩ : syracuseStep 623063 = 934595) B934595
theorem B623083 : Blo 622298 623083 := bstep (se 1 (by rfl) ⟨467312, by rfl⟩ : syracuseStep 623083 = 934625) B934625
theorem B623095 : Blo 622298 623095 := bstep (se 1 (by rfl) ⟨467321, by rfl⟩ : syracuseStep 623095 = 934643) B934643
theorem B623115 : Blo 622298 623115 := bstep (se 1 (by rfl) ⟨467336, by rfl⟩ : syracuseStep 623115 = 934673) B934673
theorem B623127 : Blo 622298 623127 := bstep (se 1 (by rfl) ⟨467345, by rfl⟩ : syracuseStep 623127 = 934691) B934691
theorem B623147 : Blo 622298 623147 := bstep (se 1 (by rfl) ⟨467360, by rfl⟩ : syracuseStep 623147 = 934721) B934721
theorem B623159 : Blo 622298 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B623179 : Blo 622298 623179 := bstep (se 1 (by rfl) ⟨467384, by rfl⟩ : syracuseStep 623179 = 934769) B934769
theorem B1081931 : Blo 622298 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B623191 : Blo 622298 623191 := bstep (se 1 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 623191 = 934787) B934787
theorem B21627485 : Blo 622298 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B2851421 : Blo 622298 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B623211 : Blo 622298 623211 := bstep (se 1 (by rfl) ⟨467408, by rfl⟩ : syracuseStep 623211 = 934817) B934817
theorem B623223 : Blo 622298 623223 := bstep (se 1 (by rfl) ⟨467417, by rfl⟩ : syracuseStep 623223 = 934835) B934835
theorem B852619 : Blo 622298 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B623243 : Blo 622298 623243 := bstep (se 1 (by rfl) ⟨467432, by rfl⟩ : syracuseStep 623243 = 934865) B934865
theorem B623255 : Blo 622298 623255 := bstep (se 1 (by rfl) ⟨467441, by rfl⟩ : syracuseStep 623255 = 934883) B934883
theorem B623275 : Blo 622298 623275 := bstep (se 1 (by rfl) ⟨467456, by rfl⟩ : syracuseStep 623275 = 934913) B934913
theorem B623287 : Blo 622298 623287 := bstep (se 1 (by rfl) ⟨467465, by rfl⟩ : syracuseStep 623287 = 934931) B934931
theorem B623307 : Blo 622298 623307 := bstep (se 1 (by rfl) ⟨467480, by rfl⟩ : syracuseStep 623307 = 934961) B934961
theorem B623319 : Blo 622298 623319 := bstep (se 1 (by rfl) ⟨467489, by rfl⟩ : syracuseStep 623319 = 934979) B934979
theorem B623339 : Blo 622298 623339 := bstep (se 1 (by rfl) ⟨467504, by rfl⟩ : syracuseStep 623339 = 935009) B935009
theorem B623351 : Blo 622298 623351 := bstep (se 1 (by rfl) ⟨467513, by rfl⟩ : syracuseStep 623351 = 935027) B935027
theorem B623371 : Blo 622298 623371 := bstep (se 1 (by rfl) ⟨467528, by rfl⟩ : syracuseStep 623371 = 935057) B935057
theorem B623383 : Blo 622298 623383 := bstep (se 1 (by rfl) ⟨467537, by rfl⟩ : syracuseStep 623383 = 935075) B935075
theorem B623403 : Blo 622298 623403 := bstep (se 1 (by rfl) ⟨467552, by rfl⟩ : syracuseStep 623403 = 935105) B935105
theorem B623415 : Blo 622298 623415 := bstep (se 1 (by rfl) ⟨467561, by rfl⟩ : syracuseStep 623415 = 935123) B935123
theorem B623435 : Blo 622298 623435 := bstep (se 1 (by rfl) ⟨467576, by rfl⟩ : syracuseStep 623435 = 935153) B935153
theorem B1901387 : Blo 622298 1901387 := bstep (se 1 (by rfl) ⟨1426040, by rfl⟩ : syracuseStep 1901387 = 2852081) B2852081
theorem B623447 : Blo 622298 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B623467 : Blo 622298 623467 := bstep (se 1 (by rfl) ⟨467600, by rfl⟩ : syracuseStep 623467 = 935201) B935201
theorem B623479 : Blo 622298 623479 := bstep (se 1 (by rfl) ⟨467609, by rfl⟩ : syracuseStep 623479 = 935219) B935219
theorem B623499 : Blo 622298 623499 := bstep (se 1 (by rfl) ⟨467624, by rfl⟩ : syracuseStep 623499 = 935249) B935249
theorem B623511 : Blo 622298 623511 := bstep (se 1 (by rfl) ⟨467633, by rfl⟩ : syracuseStep 623511 = 935267) B935267
theorem B623531 : Blo 622298 623531 := bstep (se 1 (by rfl) ⟨467648, by rfl⟩ : syracuseStep 623531 = 935297) B935297
theorem B623543 : Blo 622298 623543 := bstep (se 1 (by rfl) ⟨467657, by rfl⟩ : syracuseStep 623543 = 935315) B935315
theorem B623563 : Blo 622298 623563 := bstep (se 1 (by rfl) ⟨467672, by rfl⟩ : syracuseStep 623563 = 935345) B935345
theorem B623575 : Blo 622298 623575 := bstep (se 1 (by rfl) ⟨467681, by rfl⟩ : syracuseStep 623575 = 935363) B935363
theorem B623595 : Blo 622298 623595 := bstep (se 1 (by rfl) ⟨467696, by rfl⟩ : syracuseStep 623595 = 935393) B935393
theorem B623607 : Blo 622298 623607 := bstep (se 1 (by rfl) ⟨467705, by rfl⟩ : syracuseStep 623607 = 935411) B935411
theorem B623627 : Blo 622298 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B623639 : Blo 622298 623639 := bstep (se 1 (by rfl) ⟨467729, by rfl⟩ : syracuseStep 623639 = 935459) B935459
theorem B623659 : Blo 622298 623659 := bstep (se 1 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 623659 = 935489) B935489
theorem B623671 : Blo 622298 623671 := bstep (se 1 (by rfl) ⟨467753, by rfl⟩ : syracuseStep 623671 = 935507) B935507
theorem B623691 : Blo 622298 623691 := bstep (se 1 (by rfl) ⟨467768, by rfl⟩ : syracuseStep 623691 = 935537) B935537
theorem B623703 : Blo 622298 623703 := bstep (se 1 (by rfl) ⟨467777, by rfl⟩ : syracuseStep 623703 = 935555) B935555
theorem B623723 : Blo 622298 623723 := bstep (se 1 (by rfl) ⟨467792, by rfl⟩ : syracuseStep 623723 = 935585) B935585
theorem B276661361 : Blo 622298 276661361 := bstep (se 2 (by rfl) ⟨103748010, by rfl⟩ : syracuseStep 276661361 = 207496021) B207496021
theorem B623735 : Blo 622298 623735 := bstep (se 1 (by rfl) ⟨467801, by rfl⟩ : syracuseStep 623735 = 935603) B935603
theorem B623755 : Blo 622298 623755 := bstep (se 1 (by rfl) ⟨467816, by rfl⟩ : syracuseStep 623755 = 935633) B935633
theorem B623767 : Blo 622298 623767 := bstep (se 1 (by rfl) ⟨467825, by rfl⟩ : syracuseStep 623767 = 935651) B935651
theorem B623787 : Blo 622298 623787 := bstep (se 1 (by rfl) ⟨467840, by rfl⟩ : syracuseStep 623787 = 935681) B935681
theorem B623799 : Blo 622298 623799 := bstep (se 1 (by rfl) ⟨467849, by rfl⟩ : syracuseStep 623799 = 935699) B935699
theorem B623819 : Blo 622298 623819 := bstep (se 1 (by rfl) ⟨467864, by rfl⟩ : syracuseStep 623819 = 935729) B935729
theorem B623831 : Blo 622298 623831 := bstep (se 1 (by rfl) ⟨467873, by rfl⟩ : syracuseStep 623831 = 935747) B935747
theorem B623851 : Blo 622298 623851 := bstep (se 1 (by rfl) ⟨467888, by rfl⟩ : syracuseStep 623851 = 935777) B935777
theorem B623863 : Blo 622298 623863 := bstep (se 1 (by rfl) ⟨467897, by rfl⟩ : syracuseStep 623863 = 935795) B935795
theorem B623883 : Blo 622298 623883 := bstep (se 1 (by rfl) ⟨467912, by rfl⟩ : syracuseStep 623883 = 935825) B935825
theorem B787735 : Blo 622298 787735 := bstep (se 1 (by rfl) ⟨590801, by rfl⟩ : syracuseStep 787735 = 1181603) B1181603
theorem B623895 : Blo 622298 623895 := bstep (se 1 (by rfl) ⟨467921, by rfl⟩ : syracuseStep 623895 = 935843) B935843
theorem B623915 : Blo 622298 623915 := bstep (se 1 (by rfl) ⟨467936, by rfl⟩ : syracuseStep 623915 = 935873) B935873
theorem B623927 : Blo 622298 623927 := bstep (se 1 (by rfl) ⟨467945, by rfl⟩ : syracuseStep 623927 = 935891) B935891
theorem B623947 : Blo 622298 623947 := bstep (se 1 (by rfl) ⟨467960, by rfl⟩ : syracuseStep 623947 = 935921) B935921
theorem B623959 : Blo 622298 623959 := bstep (se 1 (by rfl) ⟨467969, by rfl⟩ : syracuseStep 623959 = 935939) B935939
theorem B623979 : Blo 622298 623979 := bstep (se 1 (by rfl) ⟨467984, by rfl⟩ : syracuseStep 623979 = 935969) B935969
theorem B623991 : Blo 622298 623991 := bstep (se 1 (by rfl) ⟨467993, by rfl⟩ : syracuseStep 623991 = 935987) B935987
theorem B624011 : Blo 622298 624011 := bstep (se 1 (by rfl) ⟨468008, by rfl⟩ : syracuseStep 624011 = 936017) B936017
theorem B624023 : Blo 622298 624023 := bstep (se 1 (by rfl) ⟨468017, by rfl⟩ : syracuseStep 624023 = 936035) B936035
theorem B624043 : Blo 622298 624043 := bstep (se 1 (by rfl) ⟨468032, by rfl⟩ : syracuseStep 624043 = 936065) B936065
theorem B624055 : Blo 622298 624055 := bstep (se 1 (by rfl) ⟨468041, by rfl⟩ : syracuseStep 624055 = 936083) B936083
theorem B624075 : Blo 622298 624075 := bstep (se 1 (by rfl) ⟨468056, by rfl⟩ : syracuseStep 624075 = 936113) B936113
theorem B886231 : Blo 622298 886231 := bstep (se 1 (by rfl) ⟨664673, by rfl⟩ : syracuseStep 886231 = 1329347) B1329347
theorem B624087 : Blo 622298 624087 := bstep (se 1 (by rfl) ⟨468065, by rfl⟩ : syracuseStep 624087 = 936131) B936131
theorem B624107 : Blo 622298 624107 := bstep (se 1 (by rfl) ⟨468080, by rfl⟩ : syracuseStep 624107 = 936161) B936161
theorem B624119 : Blo 622298 624119 := bstep (se 1 (by rfl) ⟨468089, by rfl⟩ : syracuseStep 624119 = 936179) B936179
theorem B624139 : Blo 622298 624139 := bstep (se 1 (by rfl) ⟨468104, by rfl⟩ : syracuseStep 624139 = 936209) B936209
theorem B624151 : Blo 622298 624151 := bstep (se 1 (by rfl) ⟨468113, by rfl⟩ : syracuseStep 624151 = 936227) B936227
theorem B624171 : Blo 622298 624171 := bstep (se 1 (by rfl) ⟨468128, by rfl⟩ : syracuseStep 624171 = 936257) B936257
theorem B624183 : Blo 622298 624183 := bstep (se 1 (by rfl) ⟨468137, by rfl⟩ : syracuseStep 624183 = 936275) B936275
theorem B624203 : Blo 622298 624203 := bstep (se 1 (by rfl) ⟨468152, by rfl⟩ : syracuseStep 624203 = 936305) B936305
theorem B624215 : Blo 622298 624215 := bstep (se 1 (by rfl) ⟨468161, by rfl⟩ : syracuseStep 624215 = 936323) B936323
theorem B624235 : Blo 622298 624235 := bstep (se 1 (by rfl) ⟨468176, by rfl⟩ : syracuseStep 624235 = 936353) B936353
theorem B624247 : Blo 622298 624247 := bstep (se 1 (by rfl) ⟨468185, by rfl⟩ : syracuseStep 624247 = 936371) B936371
theorem B624267 : Blo 622298 624267 := bstep (se 1 (by rfl) ⟨468200, by rfl⟩ : syracuseStep 624267 = 936401) B936401
theorem B624279 : Blo 622298 624279 := bstep (se 1 (by rfl) ⟨468209, by rfl⟩ : syracuseStep 624279 = 936419) B936419
theorem B624299 : Blo 622298 624299 := bstep (se 1 (by rfl) ⟨468224, by rfl⟩ : syracuseStep 624299 = 936449) B936449
theorem B624311 : Blo 622298 624311 := bstep (se 1 (by rfl) ⟨468233, by rfl⟩ : syracuseStep 624311 = 936467) B936467
theorem B624331 : Blo 622298 624331 := bstep (se 1 (by rfl) ⟨468248, by rfl⟩ : syracuseStep 624331 = 936497) B936497
theorem B624343 : Blo 622298 624343 := bstep (se 1 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 624343 = 936515) B936515
theorem B624363 : Blo 622298 624363 := bstep (se 1 (by rfl) ⟨468272, by rfl⟩ : syracuseStep 624363 = 936545) B936545
theorem B624375 : Blo 622298 624375 := bstep (se 1 (by rfl) ⟨468281, by rfl⟩ : syracuseStep 624375 = 936563) B936563
theorem B624395 : Blo 622298 624395 := bstep (se 1 (by rfl) ⟨468296, by rfl⟩ : syracuseStep 624395 = 936593) B936593
theorem B624407 : Blo 622298 624407 := bstep (se 1 (by rfl) ⟨468305, by rfl⟩ : syracuseStep 624407 = 936611) B936611
theorem B624427 : Blo 622298 624427 := bstep (se 1 (by rfl) ⟨468320, by rfl⟩ : syracuseStep 624427 = 936641) B936641
theorem B624439 : Blo 622298 624439 := bstep (se 1 (by rfl) ⟨468329, by rfl⟩ : syracuseStep 624439 = 936659) B936659
theorem B624459 : Blo 622298 624459 := bstep (se 1 (by rfl) ⟨468344, by rfl⟩ : syracuseStep 624459 = 936689) B936689
theorem B1050455 : Blo 622298 1050455 := bstep (se 1 (by rfl) ⟨787841, by rfl⟩ : syracuseStep 1050455 = 1575683) B1575683
theorem B624471 : Blo 622298 624471 := bstep (se 1 (by rfl) ⟨468353, by rfl⟩ : syracuseStep 624471 = 936707) B936707
theorem B624491 : Blo 622298 624491 := bstep (se 1 (by rfl) ⟨468368, by rfl⟩ : syracuseStep 624491 = 936737) B936737
theorem B624503 : Blo 622298 624503 := bstep (se 1 (by rfl) ⟨468377, by rfl⟩ : syracuseStep 624503 = 936755) B936755
theorem B624523 : Blo 622298 624523 := bstep (se 1 (by rfl) ⟨468392, by rfl⟩ : syracuseStep 624523 = 936785) B936785
theorem B624535 : Blo 622298 624535 := bstep (se 1 (by rfl) ⟨468401, by rfl⟩ : syracuseStep 624535 = 936803) B936803
theorem B624555 : Blo 622298 624555 := bstep (se 1 (by rfl) ⟨468416, by rfl⟩ : syracuseStep 624555 = 936833) B936833
theorem B624567 : Blo 622298 624567 := bstep (se 1 (by rfl) ⟨468425, by rfl⟩ : syracuseStep 624567 = 936851) B936851
theorem B624587 : Blo 622298 624587 := bstep (se 1 (by rfl) ⟨468440, by rfl⟩ : syracuseStep 624587 = 936881) B936881
theorem B1050583 : Blo 622298 1050583 := bstep (se 1 (by rfl) ⟨787937, by rfl⟩ : syracuseStep 1050583 = 1575875) B1575875
theorem B624599 : Blo 622298 624599 := bstep (se 1 (by rfl) ⟨468449, by rfl⟩ : syracuseStep 624599 = 936899) B936899
theorem B624619 : Blo 622298 624619 := bstep (se 1 (by rfl) ⟨468464, by rfl⟩ : syracuseStep 624619 = 936929) B936929
theorem B624631 : Blo 622298 624631 := bstep (se 1 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 624631 = 936947) B936947
theorem B624651 : Blo 622298 624651 := bstep (se 1 (by rfl) ⟨468488, by rfl⟩ : syracuseStep 624651 = 936977) B936977
theorem B624663 : Blo 622298 624663 := bstep (se 1 (by rfl) ⟨468497, by rfl⟩ : syracuseStep 624663 = 936995) B936995
theorem B624683 : Blo 622298 624683 := bstep (se 1 (by rfl) ⟨468512, by rfl⟩ : syracuseStep 624683 = 937025) B937025
theorem B624695 : Blo 622298 624695 := bstep (se 1 (by rfl) ⟨468521, by rfl⟩ : syracuseStep 624695 = 937043) B937043
theorem B788555 : Blo 622298 788555 := bstep (se 1 (by rfl) ⟨591416, by rfl⟩ : syracuseStep 788555 = 1182833) B1182833
theorem B624715 : Blo 622298 624715 := bstep (se 1 (by rfl) ⟨468536, by rfl⟩ : syracuseStep 624715 = 937073) B937073
theorem B624727 : Blo 622298 624727 := bstep (se 1 (by rfl) ⟨468545, by rfl⟩ : syracuseStep 624727 = 937091) B937091
theorem B1181785 : Blo 622298 1181785 := bstep (se 2 (by rfl) ⟨443169, by rfl⟩ : syracuseStep 1181785 = 886339) B886339
theorem B624747 : Blo 622298 624747 := bstep (se 1 (by rfl) ⟨468560, by rfl⟩ : syracuseStep 624747 = 937121) B937121
theorem B624759 : Blo 622298 624759 := bstep (se 1 (by rfl) ⟨468569, by rfl⟩ : syracuseStep 624759 = 937139) B937139
theorem B624779 : Blo 622298 624779 := bstep (se 1 (by rfl) ⟨468584, by rfl⟩ : syracuseStep 624779 = 937169) B937169
theorem B624791 : Blo 622298 624791 := bstep (se 1 (by rfl) ⟨468593, by rfl⟩ : syracuseStep 624791 = 937187) B937187
theorem B624811 : Blo 622298 624811 := bstep (se 1 (by rfl) ⟨468608, by rfl⟩ : syracuseStep 624811 = 937217) B937217
theorem B624823 : Blo 622298 624823 := bstep (se 1 (by rfl) ⟨468617, by rfl⟩ : syracuseStep 624823 = 937235) B937235
theorem B624843 : Blo 622298 624843 := bstep (se 1 (by rfl) ⟨468632, by rfl⟩ : syracuseStep 624843 = 937265) B937265
theorem B624855 : Blo 622298 624855 := bstep (se 1 (by rfl) ⟨468641, by rfl⟩ : syracuseStep 624855 = 937283) B937283
theorem B624875 : Blo 622298 624875 := bstep (se 1 (by rfl) ⟨468656, by rfl⟩ : syracuseStep 624875 = 937313) B937313
theorem B624887 : Blo 622298 624887 := bstep (se 1 (by rfl) ⟨468665, by rfl⟩ : syracuseStep 624887 = 937331) B937331
theorem B887051 : Blo 622298 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B624907 : Blo 622298 624907 := bstep (se 1 (by rfl) ⟨468680, by rfl⟩ : syracuseStep 624907 = 937361) B937361
theorem B624919 : Blo 622298 624919 := bstep (se 1 (by rfl) ⟨468689, by rfl⟩ : syracuseStep 624919 = 937379) B937379
theorem B624939 : Blo 622298 624939 := bstep (se 1 (by rfl) ⟨468704, by rfl⟩ : syracuseStep 624939 = 937409) B937409
theorem B624951 : Blo 622298 624951 := bstep (se 1 (by rfl) ⟨468713, by rfl⟩ : syracuseStep 624951 = 937427) B937427
theorem B5409089 : Blo 622298 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B624971 : Blo 622298 624971 := bstep (se 1 (by rfl) ⟨468728, by rfl⟩ : syracuseStep 624971 = 937457) B937457
theorem B624983 : Blo 622298 624983 := bstep (se 1 (by rfl) ⟨468737, by rfl⟩ : syracuseStep 624983 = 937475) B937475
theorem B625003 : Blo 622298 625003 := bstep (se 1 (by rfl) ⟨468752, by rfl⟩ : syracuseStep 625003 = 937505) B937505
theorem B625015 : Blo 622298 625015 := bstep (se 1 (by rfl) ⟨468761, by rfl⟩ : syracuseStep 625015 = 937523) B937523
theorem B2853251 : Blo 622298 2853251 := bstep (se 1 (by rfl) ⟨2139938, by rfl⟩ : syracuseStep 2853251 = 4279877) B4279877
theorem B625035 : Blo 622298 625035 := bstep (se 1 (by rfl) ⟨468776, by rfl⟩ : syracuseStep 625035 = 937553) B937553
theorem B625047 : Blo 622298 625047 := bstep (se 1 (by rfl) ⟨468785, by rfl⟩ : syracuseStep 625047 = 937571) B937571
theorem B625067 : Blo 622298 625067 := bstep (se 1 (by rfl) ⟨468800, by rfl⟩ : syracuseStep 625067 = 937601) B937601
theorem B625079 : Blo 622298 625079 := bstep (se 1 (by rfl) ⟨468809, by rfl⟩ : syracuseStep 625079 = 937619) B937619
theorem B625099 : Blo 622298 625099 := bstep (se 1 (by rfl) ⟨468824, by rfl⟩ : syracuseStep 625099 = 937649) B937649
theorem B625111 : Blo 622298 625111 := bstep (se 1 (by rfl) ⟨468833, by rfl⟩ : syracuseStep 625111 = 937667) B937667
theorem B625131 : Blo 622298 625131 := bstep (se 1 (by rfl) ⟨468848, by rfl⟩ : syracuseStep 625131 = 937697) B937697
theorem B625143 : Blo 622298 625143 := bstep (se 1 (by rfl) ⟨468857, by rfl⟩ : syracuseStep 625143 = 937715) B937715
theorem B625163 : Blo 622298 625163 := bstep (se 1 (by rfl) ⟨468872, by rfl⟩ : syracuseStep 625163 = 937745) B937745
theorem B625175 : Blo 622298 625175 := bstep (se 1 (by rfl) ⟨468881, by rfl⟩ : syracuseStep 625175 = 937763) B937763
theorem B625195 : Blo 622298 625195 := bstep (se 1 (by rfl) ⟨468896, by rfl⟩ : syracuseStep 625195 = 937793) B937793
theorem B625207 : Blo 622298 625207 := bstep (se 1 (by rfl) ⟨468905, by rfl⟩ : syracuseStep 625207 = 937811) B937811
theorem B1051211 : Blo 622298 1051211 := bstep (se 1 (by rfl) ⟨788408, by rfl⟩ : syracuseStep 1051211 = 1576817) B1576817
theorem B625227 : Blo 622298 625227 := bstep (se 1 (by rfl) ⟨468920, by rfl⟩ : syracuseStep 625227 = 937841) B937841
theorem B625239 : Blo 622298 625239 := bstep (se 1 (by rfl) ⟨468929, by rfl⟩ : syracuseStep 625239 = 937859) B937859
theorem B625259 : Blo 622298 625259 := bstep (se 1 (by rfl) ⟨468944, by rfl⟩ : syracuseStep 625259 = 937889) B937889
theorem B625271 : Blo 622298 625271 := bstep (se 1 (by rfl) ⟨468953, by rfl⟩ : syracuseStep 625271 = 937907) B937907
theorem B4754051 : Blo 622298 4754051 := bstep (se 1 (by rfl) ⟨3565538, by rfl⟩ : syracuseStep 4754051 = 7131077) B7131077
theorem B1182347 : Blo 622298 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B625291 : Blo 622298 625291 := bstep (se 1 (by rfl) ⟨468968, by rfl⟩ : syracuseStep 625291 = 937937) B937937
theorem B625303 : Blo 622298 625303 := bstep (se 1 (by rfl) ⟨468977, by rfl⟩ : syracuseStep 625303 = 937955) B937955
theorem B625323 : Blo 622298 625323 := bstep (se 1 (by rfl) ⟨468992, by rfl⟩ : syracuseStep 625323 = 937985) B937985
theorem B625335 : Blo 622298 625335 := bstep (se 1 (by rfl) ⟨469001, by rfl⟩ : syracuseStep 625335 = 938003) B938003
theorem B1051339 : Blo 622298 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B625355 : Blo 622298 625355 := bstep (se 1 (by rfl) ⟨469016, by rfl⟩ : syracuseStep 625355 = 938033) B938033
theorem B625367 : Blo 622298 625367 := bstep (se 1 (by rfl) ⟨469025, by rfl⟩ : syracuseStep 625367 = 938051) B938051
theorem B625387 : Blo 622298 625387 := bstep (se 1 (by rfl) ⟨469040, by rfl⟩ : syracuseStep 625387 = 938081) B938081
theorem B625399 : Blo 622298 625399 := bstep (se 1 (by rfl) ⟨469049, by rfl⟩ : syracuseStep 625399 = 938099) B938099
theorem B789259 : Blo 622298 789259 := bstep (se 1 (by rfl) ⟨591944, by rfl⟩ : syracuseStep 789259 = 1183889) B1183889
theorem B625419 : Blo 622298 625419 := bstep (se 1 (by rfl) ⟨469064, by rfl⟩ : syracuseStep 625419 = 938129) B938129
theorem B625431 : Blo 622298 625431 := bstep (se 1 (by rfl) ⟨469073, by rfl⟩ : syracuseStep 625431 = 938147) B938147
theorem B625451 : Blo 622298 625451 := bstep (se 1 (by rfl) ⟨469088, by rfl⟩ : syracuseStep 625451 = 938177) B938177
theorem B625463 : Blo 622298 625463 := bstep (se 1 (by rfl) ⟨469097, by rfl⟩ : syracuseStep 625463 = 938195) B938195
theorem B1182529 : Blo 622298 1182529 := bstep (se 2 (by rfl) ⟨443448, by rfl⟩ : syracuseStep 1182529 = 886897) B886897
theorem B625483 : Blo 622298 625483 := bstep (se 1 (by rfl) ⟨469112, by rfl⟩ : syracuseStep 625483 = 938225) B938225
theorem B625495 : Blo 622298 625495 := bstep (se 1 (by rfl) ⟨469121, by rfl⟩ : syracuseStep 625495 = 938243) B938243
theorem B1051481 : Blo 622298 1051481 := bstep (se 2 (by rfl) ⟨394305, by rfl⟩ : syracuseStep 1051481 = 788611) B788611
theorem B1772381 : Blo 622298 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B625515 : Blo 622298 625515 := bstep (se 1 (by rfl) ⟨469136, by rfl⟩ : syracuseStep 625515 = 938273) B938273
theorem B625527 : Blo 622298 625527 := bstep (se 1 (by rfl) ⟨469145, by rfl⟩ : syracuseStep 625527 = 938291) B938291
theorem B625547 : Blo 622298 625547 := bstep (se 1 (by rfl) ⟨469160, by rfl⟩ : syracuseStep 625547 = 938321) B938321
theorem B625559 : Blo 622298 625559 := bstep (se 1 (by rfl) ⟨469169, by rfl⟩ : syracuseStep 625559 = 938339) B938339
theorem B625579 : Blo 622298 625579 := bstep (se 1 (by rfl) ⟨469184, by rfl⟩ : syracuseStep 625579 = 938369) B938369
theorem B625591 : Blo 622298 625591 := bstep (se 1 (by rfl) ⟨469193, by rfl⟩ : syracuseStep 625591 = 938387) B938387
theorem B625611 : Blo 622298 625611 := bstep (se 1 (by rfl) ⟨469208, by rfl⟩ : syracuseStep 625611 = 938417) B938417
theorem B625623 : Blo 622298 625623 := bstep (se 1 (by rfl) ⟨469217, by rfl⟩ : syracuseStep 625623 = 938435) B938435
theorem B1051609 : Blo 622298 1051609 := bstep (se 2 (by rfl) ⟨394353, by rfl⟩ : syracuseStep 1051609 = 788707) B788707
theorem B625643 : Blo 622298 625643 := bstep (se 1 (by rfl) ⟨469232, by rfl⟩ : syracuseStep 625643 = 938465) B938465
theorem B625655 : Blo 622298 625655 := bstep (se 1 (by rfl) ⟨469241, by rfl⟩ : syracuseStep 625655 = 938483) B938483
theorem B625675 : Blo 622298 625675 := bstep (se 1 (by rfl) ⟨469256, by rfl⟩ : syracuseStep 625675 = 938513) B938513
theorem B789527 : Blo 622298 789527 := bstep (se 1 (by rfl) ⟨592145, by rfl⟩ : syracuseStep 789527 = 1184291) B1184291
theorem B625687 : Blo 622298 625687 := bstep (se 1 (by rfl) ⟨469265, by rfl⟩ : syracuseStep 625687 = 938531) B938531
theorem B625707 : Blo 622298 625707 := bstep (se 1 (by rfl) ⟨469280, by rfl⟩ : syracuseStep 625707 = 938561) B938561
theorem B2100275 : Blo 622298 2100275 := bstep (se 1 (by rfl) ⟨1575206, by rfl⟩ : syracuseStep 2100275 = 3150413) B3150413
theorem B625719 : Blo 622298 625719 := bstep (se 1 (by rfl) ⟨469289, by rfl⟩ : syracuseStep 625719 = 938579) B938579
theorem B2198593 : Blo 622298 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B625739 : Blo 622298 625739 := bstep (se 1 (by rfl) ⟨469304, by rfl⟩ : syracuseStep 625739 = 938609) B938609
theorem B625751 : Blo 622298 625751 := bstep (se 1 (by rfl) ⟨469313, by rfl⟩ : syracuseStep 625751 = 938627) B938627
theorem B625771 : Blo 622298 625771 := bstep (se 1 (by rfl) ⟨469328, by rfl⟩ : syracuseStep 625771 = 938657) B938657
theorem B625783 : Blo 622298 625783 := bstep (se 1 (by rfl) ⟨469337, by rfl⟩ : syracuseStep 625783 = 938675) B938675
theorem B625803 : Blo 622298 625803 := bstep (se 1 (by rfl) ⟨469352, by rfl⟩ : syracuseStep 625803 = 938705) B938705
theorem B625815 : Blo 622298 625815 := bstep (se 1 (by rfl) ⟨469361, by rfl⟩ : syracuseStep 625815 = 938723) B938723
theorem B625835 : Blo 622298 625835 := bstep (se 1 (by rfl) ⟨469376, by rfl⟩ : syracuseStep 625835 = 938753) B938753
theorem B625847 : Blo 622298 625847 := bstep (se 1 (by rfl) ⟨469385, by rfl⟩ : syracuseStep 625847 = 938771) B938771
theorem B625867 : Blo 622298 625867 := bstep (se 1 (by rfl) ⟨469400, by rfl⟩ : syracuseStep 625867 = 938801) B938801
theorem B625879 : Blo 622298 625879 := bstep (se 1 (by rfl) ⟨469409, by rfl⟩ : syracuseStep 625879 = 938819) B938819
theorem B888025 : Blo 622298 888025 := bstep (se 2 (by rfl) ⟨333009, by rfl⟩ : syracuseStep 888025 = 666019) B666019
theorem B625899 : Blo 622298 625899 := bstep (se 1 (by rfl) ⟨469424, by rfl⟩ : syracuseStep 625899 = 938849) B938849
theorem B10685681 : Blo 622298 10685681 := bstep (se 2 (by rfl) ⟨4007130, by rfl⟩ : syracuseStep 10685681 = 8014261) B8014261
theorem B625911 : Blo 622298 625911 := bstep (se 1 (by rfl) ⟨469433, by rfl⟩ : syracuseStep 625911 = 938867) B938867
theorem B625931 : Blo 622298 625931 := bstep (se 1 (by rfl) ⟨469448, by rfl⟩ : syracuseStep 625931 = 938897) B938897
theorem B625943 : Blo 622298 625943 := bstep (se 1 (by rfl) ⟨469457, by rfl⟩ : syracuseStep 625943 = 938915) B938915
theorem B625963 : Blo 622298 625963 := bstep (se 1 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 625963 = 938945) B938945
theorem B625975 : Blo 622298 625975 := bstep (se 1 (by rfl) ⟨469481, by rfl⟩ : syracuseStep 625975 = 938963) B938963
theorem B2100545 : Blo 622298 2100545 := bstep (se 2 (by rfl) ⟨787704, by rfl⟩ : syracuseStep 2100545 = 1575409) B1575409
theorem B625995 : Blo 622298 625995 := bstep (se 1 (by rfl) ⟨469496, by rfl⟩ : syracuseStep 625995 = 938993) B938993
theorem B1281367 : Blo 622298 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B626007 : Blo 622298 626007 := bstep (se 1 (by rfl) ⟨469505, by rfl⟩ : syracuseStep 626007 = 939011) B939011
theorem B626027 : Blo 622298 626027 := bstep (se 1 (by rfl) ⟨469520, by rfl⟩ : syracuseStep 626027 = 939041) B939041
theorem B626039 : Blo 622298 626039 := bstep (se 1 (by rfl) ⟨469529, by rfl⟩ : syracuseStep 626039 = 939059) B939059
theorem B626059 : Blo 622298 626059 := bstep (se 1 (by rfl) ⟨469544, by rfl⟩ : syracuseStep 626059 = 939089) B939089
theorem B626071 : Blo 622298 626071 := bstep (se 1 (by rfl) ⟨469553, by rfl⟩ : syracuseStep 626071 = 939107) B939107
theorem B626091 : Blo 622298 626091 := bstep (se 1 (by rfl) ⟨469568, by rfl⟩ : syracuseStep 626091 = 939137) B939137
theorem B626103 : Blo 622298 626103 := bstep (se 1 (by rfl) ⟨469577, by rfl⟩ : syracuseStep 626103 = 939155) B939155
theorem B626123 : Blo 622298 626123 := bstep (se 1 (by rfl) ⟨469592, by rfl⟩ : syracuseStep 626123 = 939185) B939185
theorem B626135 : Blo 622298 626135 := bstep (se 1 (by rfl) ⟨469601, by rfl⟩ : syracuseStep 626135 = 939203) B939203
theorem B2362841 : Blo 622298 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B626155 : Blo 622298 626155 := bstep (se 1 (by rfl) ⟨469616, by rfl⟩ : syracuseStep 626155 = 939233) B939233
theorem B626167 : Blo 622298 626167 := bstep (se 1 (by rfl) ⟨469625, by rfl⟩ : syracuseStep 626167 = 939251) B939251
theorem B1183243 : Blo 622298 1183243 := bstep (se 1 (by rfl) ⟨887432, by rfl⟩ : syracuseStep 1183243 = 1774865) B1774865
theorem B626187 : Blo 622298 626187 := bstep (se 1 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 626187 = 939281) B939281
theorem B1052183 : Blo 622298 1052183 := bstep (se 1 (by rfl) ⟨789137, by rfl⟩ : syracuseStep 1052183 = 1578275) B1578275
theorem B626199 : Blo 622298 626199 := bstep (se 1 (by rfl) ⟨469649, by rfl⟩ : syracuseStep 626199 = 939299) B939299
theorem B626219 : Blo 622298 626219 := bstep (se 1 (by rfl) ⟨469664, by rfl⟩ : syracuseStep 626219 = 939329) B939329
theorem B626231 : Blo 622298 626231 := bstep (se 1 (by rfl) ⟨469673, by rfl⟩ : syracuseStep 626231 = 939347) B939347
theorem B2428481 : Blo 622298 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1576523 : Blo 622298 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B626251 : Blo 622298 626251 := bstep (se 1 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 626251 = 939377) B939377
theorem B1183319 : Blo 622298 1183319 := bstep (se 1 (by rfl) ⟨887489, by rfl⟩ : syracuseStep 1183319 = 1774979) B1774979
theorem B626263 : Blo 622298 626263 := bstep (se 1 (by rfl) ⟨469697, by rfl⟩ : syracuseStep 626263 = 939395) B939395
theorem B626283 : Blo 622298 626283 := bstep (se 1 (by rfl) ⟨469712, by rfl⟩ : syracuseStep 626283 = 939425) B939425
theorem B626295 : Blo 622298 626295 := bstep (se 1 (by rfl) ⟨469721, by rfl⟩ : syracuseStep 626295 = 939443) B939443
theorem B1052311 : Blo 622298 1052311 := bstep (se 1 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 1052311 = 1578467) B1578467
theorem B2363053 : Blo 622298 2363053 := bstep (se 3 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 2363053 = 886145) B886145
theorem B790231 : Blo 622298 790231 := bstep (se 1 (by rfl) ⟨592673, by rfl⟩ : syracuseStep 790231 = 1185347) B1185347
theorem B2854673 : Blo 622298 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B2101085 : Blo 622298 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B2363357 : Blo 622298 2363357 := bstep (se 3 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 2363357 = 886259) B886259
theorem B3805201 : Blo 622298 3805201 := bstep (se 2 (by rfl) ⟨1426950, by rfl⟩ : syracuseStep 3805201 = 2853901) B2853901
theorem B1708249 : Blo 622298 1708249 := bstep (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) B1281187
theorem B1183987 : Blo 622298 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B1052939 : Blo 622298 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B8982829 : Blo 622298 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B889175 : Blo 622298 889175 := bstep (se 1 (by rfl) ⟨666881, by rfl⟩ : syracuseStep 889175 = 1333763) B1333763
theorem B1053067 : Blo 622298 1053067 := bstep (se 1 (by rfl) ⟨789800, by rfl⟩ : syracuseStep 1053067 = 1579601) B1579601
theorem B1216921 : Blo 622298 1216921 := bstep (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) B912691
theorem B1184215 : Blo 622298 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1577495 : Blo 622298 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1053209 : Blo 622298 1053209 := bstep (se 2 (by rfl) ⟨394953, by rfl⟩ : syracuseStep 1053209 = 789907) B789907
theorem B1184321 : Blo 622298 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B889483 : Blo 622298 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B1053337 : Blo 622298 1053337 := bstep (se 2 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 1053337 = 790003) B790003
theorem B1184473 : Blo 622298 1184473 := bstep (se 2 (by rfl) ⟨444177, by rfl⟩ : syracuseStep 1184473 = 888355) B888355
theorem B2102219 : Blo 622298 2102219 := bstep (se 1 (by rfl) ⟨1576664, by rfl⟩ : syracuseStep 2102219 = 3153329) B3153329
theorem B1578163 : Blo 622298 1578163 := bstep (se 1 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 1578163 = 2367245) B2367245
theorem B2528435 : Blo 622298 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B1053911 : Blo 622298 1053911 := bstep (se 1 (by rfl) ⟨790433, by rfl⟩ : syracuseStep 1053911 = 1580867) B1580867
theorem B2102489 : Blo 622298 2102489 := bstep (se 2 (by rfl) ⟨788433, by rfl⟩ : syracuseStep 2102489 = 1576867) B1576867
theorem B1578305 : Blo 622298 1578305 := bstep (se 2 (by rfl) ⟨591864, by rfl⟩ : syracuseStep 1578305 = 1183729) B1183729
theorem B1054039 : Blo 622298 1054039 := bstep (se 1 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 1054039 = 1581059) B1581059
theorem B791947 : Blo 622298 791947 := bstep (se 1 (by rfl) ⟨593960, by rfl⟩ : syracuseStep 791947 = 1187921) B1187921
theorem B2659787 : Blo 622298 2659787 := bstep (se 1 (by rfl) ⟨1994840, by rfl⟩ : syracuseStep 2659787 = 3989681) B3989681
theorem B4003289 : Blo 622298 4003289 := bstep (se 2 (by rfl) ⟨1501233, by rfl⟩ : syracuseStep 4003289 = 3002467) B3002467
theorem B1283735 : Blo 622298 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B890519 : Blo 622298 890519 := bstep (se 1 (by rfl) ⟨667889, by rfl⟩ : syracuseStep 890519 = 1335779) B1335779
theorem B1775297 : Blo 622298 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B1775321 : Blo 622298 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B890713 : Blo 622298 890713 := bstep (se 2 (by rfl) ⟨334017, by rfl⟩ : syracuseStep 890713 = 668035) B668035
theorem B3151709 : Blo 622298 3151709 := bstep (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) B1181891
theorem B2103191 : Blo 622298 2103191 := bstep (se 1 (by rfl) ⟨1577393, by rfl⟩ : syracuseStep 2103191 = 3154787) B3154787
theorem B2004887 : Blo 622298 2004887 := bstep (se 1 (by rfl) ⟨1503665, by rfl⟩ : syracuseStep 2004887 = 3007331) B3007331
theorem B1054667 : Blo 622298 1054667 := bstep (se 1 (by rfl) ⟨791000, by rfl⟩ : syracuseStep 1054667 = 1582001) B1582001
theorem B1185779 : Blo 622298 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B1054795 : Blo 622298 1054795 := bstep (se 1 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 1054795 = 1582193) B1582193
theorem B1185931 : Blo 622298 1185931 := bstep (se 1 (by rfl) ⟨889448, by rfl⟩ : syracuseStep 1185931 = 1778897) B1778897
theorem B2005195 : Blo 622298 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B1349849 : Blo 622298 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B1054937 : Blo 622298 1054937 := bstep (se 2 (by rfl) ⟨395601, by rfl⟩ : syracuseStep 1054937 = 791203) B791203
theorem B1055065 : Blo 622298 1055065 := bstep (se 2 (by rfl) ⟨395649, by rfl⟩ : syracuseStep 1055065 = 791299) B791299
theorem B2660759 : Blo 622298 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B2103731 : Blo 622298 2103731 := bstep (se 1 (by rfl) ⟨1577798, by rfl⟩ : syracuseStep 2103731 = 3155597) B3155597
theorem B1186265 : Blo 622298 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B2365955 : Blo 622298 2365955 := bstep (se 1 (by rfl) ⟨1774466, by rfl⟩ : syracuseStep 2365955 = 3548933) B3548933
theorem B2365969 : Blo 622298 2365969 := bstep (se 2 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 2365969 = 1774477) B1774477
theorem B9017891 : Blo 622298 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B1579571 : Blo 622298 1579571 := bstep (se 1 (by rfl) ⟨1184678, by rfl⟩ : syracuseStep 1579571 = 2369357) B2369357
theorem B1350283 : Blo 622298 1350283 := bstep (se 1 (by rfl) ⟨1012712, by rfl⟩ : syracuseStep 1350283 = 2025425) B2025425
theorem B2104001 : Blo 622298 2104001 := bstep (se 2 (by rfl) ⟨789000, by rfl⟩ : syracuseStep 2104001 = 1578001) B1578001
theorem B2366273 : Blo 622298 2366273 := bstep (se 2 (by rfl) ⟨887352, by rfl⟩ : syracuseStep 2366273 = 1774705) B1774705
theorem B10132289 : Blo 622298 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B1055639 : Blo 622298 1055639 := bstep (se 1 (by rfl) ⟨791729, by rfl⟩ : syracuseStep 1055639 = 1583459) B1583459
theorem B1776563 : Blo 622298 1776563 := bstep (se 1 (by rfl) ⟨1332422, by rfl⟩ : syracuseStep 1776563 = 2664845) B2664845
theorem B1055767 : Blo 622298 1055767 := bstep (se 1 (by rfl) ⟨791825, by rfl⟩ : syracuseStep 1055767 = 1583651) B1583651
theorem B1580107 : Blo 622298 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B1186903 : Blo 622298 1186903 := bstep (se 1 (by rfl) ⟨890177, by rfl⟩ : syracuseStep 1186903 = 1780355) B1780355
theorem B7117955 : Blo 622298 7117955 := bstep (se 1 (by rfl) ⟨5338466, by rfl⟩ : syracuseStep 7117955 = 10676933) B10676933
theorem B1580249 : Blo 622298 1580249 := bstep (se 2 (by rfl) ⟨592593, by rfl⟩ : syracuseStep 1580249 = 1185187) B1185187
theorem B2104541 : Blo 622298 2104541 := bstep (se 3 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 2104541 = 789203) B789203
theorem B2563379 : Blo 622298 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B2366941 : Blo 622298 2366941 := bstep (se 3 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 2366941 = 887603) B887603
theorem B1056395 : Blo 622298 1056395 := bstep (se 1 (by rfl) ⟨792296, by rfl⟩ : syracuseStep 1056395 = 1584593) B1584593
theorem B1154711 : Blo 622298 1154711 := bstep (se 1 (by rfl) ⟨866033, by rfl⟩ : syracuseStep 1154711 = 1732067) B1732067
theorem B1056523 : Blo 622298 1056523 := bstep (se 1 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 1056523 = 1584785) B1584785
theorem B7610213 : Blo 622298 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B1187723 : Blo 622298 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B3153815 : Blo 622298 3153815 := bstep (se 1 (by rfl) ⟨2365361, by rfl⟩ : syracuseStep 3153815 = 4730723) B4730723
theorem B1056665 : Blo 622298 1056665 := bstep (se 2 (by rfl) ⟨396249, by rfl⟩ : syracuseStep 1056665 = 792499) B792499
theorem B1187777 : Blo 622298 1187777 := bstep (se 2 (by rfl) ⟨445416, by rfl⟩ : syracuseStep 1187777 = 890833) B890833
theorem B1581079 : Blo 622298 1581079 := bstep (se 1 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 1581079 = 2371619) B2371619
theorem B1056793 : Blo 622298 1056793 := bstep (se 2 (by rfl) ⟨396297, by rfl⟩ : syracuseStep 1056793 = 792595) B792595
theorem B2105675 : Blo 622298 2105675 := bstep (se 1 (by rfl) ⟨1579256, by rfl⟩ : syracuseStep 2105675 = 3158513) B3158513
theorem B1581515 : Blo 622298 1581515 := bstep (se 1 (by rfl) ⟨1186136, by rfl⟩ : syracuseStep 1581515 = 2372273) B2372273
theorem B12329489 : Blo 622298 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B2105945 : Blo 622298 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B4006493 : Blo 622298 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B3383939 : Blo 622298 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B959129 : Blo 622298 959129 := bstep (se 2 (by rfl) ⟨359673, by rfl⟩ : syracuseStep 959129 = 719347) B719347
theorem B2368217 : Blo 622298 2368217 := bstep (se 2 (by rfl) ⟨888081, by rfl⟩ : syracuseStep 2368217 = 1776163) B1776163
theorem B2663219 : Blo 622298 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B1581889 : Blo 622298 1581889 := bstep (se 2 (by rfl) ⟨593208, by rfl⟩ : syracuseStep 1581889 = 1186417) B1186417
theorem B4006721 : Blo 622298 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B1188695 : Blo 622298 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B631735 : Blo 622298 631735 := bstep (se 1 (by rfl) ⟨473801, by rfl⟩ : syracuseStep 631735 = 947603) B947603
theorem B1123315 : Blo 622298 1123315 := bstep (se 1 (by rfl) ⟨842486, by rfl⟩ : syracuseStep 1123315 = 1684973) B1684973
theorem B3548225 : Blo 622298 3548225 := bstep (se 2 (by rfl) ⟨1330584, by rfl⟩ : syracuseStep 3548225 = 2661169) B2661169
theorem B2106647 : Blo 622298 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B1582487 : Blo 622298 1582487 := bstep (se 1 (by rfl) ⟨1186865, by rfl⟩ : syracuseStep 1582487 = 2373731) B2373731
theorem B665015 : Blo 622298 665015 := bstep (se 1 (by rfl) ⟨498761, by rfl⟩ : syracuseStep 665015 = 997523) B997523
theorem B5318237 : Blo 622298 5318237 := bstep (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) B1994339
theorem B1779421 : Blo 622298 1779421 := bstep (se 3 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 1779421 = 667283) B667283
theorem B1779479 : Blo 622298 1779479 := bstep (se 1 (by rfl) ⟨1334609, by rfl⟩ : syracuseStep 1779479 = 2669219) B2669219
theorem B2107187 : Blo 622298 2107187 := bstep (se 1 (by rfl) ⟨1580390, by rfl⟩ : syracuseStep 2107187 = 3160781) B3160781
theorem B3614557 : Blo 622298 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B1386355 : Blo 622298 1386355 := bstep (se 1 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 1386355 = 2079533) B2079533
theorem B2107457 : Blo 622298 2107457 := bstep (se 2 (by rfl) ⟨790296, by rfl⟩ : syracuseStep 2107457 = 1580593) B1580593
theorem B4499549 : Blo 622298 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B3418213 : Blo 622298 3418213 := bstep (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) B640915
theorem B1583297 : Blo 622298 1583297 := bstep (se 2 (by rfl) ⟨593736, by rfl⟩ : syracuseStep 1583297 = 1187473) B1187473
theorem B2369843 : Blo 622298 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B2369857 : Blo 622298 2369857 := bstep (se 2 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 2369857 = 1777393) B1777393
theorem B10135925 : Blo 622298 10135925 := bstep (se 5 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 10135925 = 950243) B950243
theorem B4729265 : Blo 622298 4729265 := bstep (se 2 (by rfl) ⟨1773474, by rfl⟩ : syracuseStep 4729265 = 3546949) B3546949
theorem B2107997 : Blo 622298 2107997 := bstep (se 3 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 2107997 = 790499) B790499
theorem B2665133 : Blo 622298 2665133 := bstep (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) B999425
theorem B1583833 : Blo 622298 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B4500299 : Blo 622298 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B1420183 : Blo 622298 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B4729751 : Blo 622298 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B2534323 : Blo 622298 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B12331993 : Blo 622298 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B1780697 : Blo 622298 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B4008977 : Blo 622298 4008977 := bstep (se 2 (by rfl) ⟨1503366, by rfl⟩ : syracuseStep 4008977 = 3006733) B3006733
theorem B1780811 : Blo 622298 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B666839 : Blo 622298 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B2665817 : Blo 622298 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B3157379 : Blo 622298 3157379 := bstep (se 1 (by rfl) ⟨2368034, by rfl⟩ : syracuseStep 3157379 = 4736069) B4736069
theorem B2305459 : Blo 622298 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B700087 : Blo 622298 700087 := bstep (se 1 (by rfl) ⟨525065, by rfl⟩ : syracuseStep 700087 = 1050131) B1050131
theorem B2109131 : Blo 622298 2109131 := bstep (se 1 (by rfl) ⟨1581848, by rfl⟩ : syracuseStep 2109131 = 3163697) B3163697
theorem B1584947 : Blo 622298 1584947 := bstep (se 1 (by rfl) ⟨1188710, by rfl⟩ : syracuseStep 1584947 = 2377421) B2377421
theorem B6762341 : Blo 622298 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B700267 : Blo 622298 700267 := bstep (se 1 (by rfl) ⟨525200, by rfl⟩ : syracuseStep 700267 = 1050401) B1050401
theorem B667531 : Blo 622298 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B700375 : Blo 622298 700375 := bstep (se 1 (by rfl) ⟨525281, by rfl⟩ : syracuseStep 700375 = 1050563) B1050563
theorem B2109401 : Blo 622298 2109401 := bstep (se 2 (by rfl) ⟨791025, by rfl⟩ : syracuseStep 2109401 = 1582051) B1582051
theorem B2404397 : Blo 622298 2404397 := bstep (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) B901649
theorem B1585241 : Blo 622298 1585241 := bstep (se 2 (by rfl) ⟨594465, by rfl⟩ : syracuseStep 1585241 = 1188931) B1188931
theorem B5320835 : Blo 622298 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B700555 : Blo 622298 700555 := bstep (se 1 (by rfl) ⟨525416, by rfl⟩ : syracuseStep 700555 = 1050833) B1050833
theorem B1781939 : Blo 622298 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B2371787 : Blo 622298 2371787 := bstep (se 1 (by rfl) ⟨1778840, by rfl⟩ : syracuseStep 2371787 = 3557681) B3557681
theorem B2371801 : Blo 622298 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B700663 : Blo 622298 700663 := bstep (se 1 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 700663 = 1050995) B1050995
theorem B5058881 : Blo 622298 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B7614785 : Blo 622298 7614785 := bstep (se 2 (by rfl) ⟨2855544, by rfl⟩ : syracuseStep 7614785 = 5711089) B5711089
theorem B700843 : Blo 622298 700843 := bstep (se 1 (by rfl) ⟨525632, by rfl⟩ : syracuseStep 700843 = 1051265) B1051265
theorem B1421761 : Blo 622298 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B2666945 : Blo 622298 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B8565209 : Blo 622298 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B700951 : Blo 622298 700951 := bstep (se 1 (by rfl) ⟨525713, by rfl⟩ : syracuseStep 700951 = 1051427) B1051427
theorem B1126963 : Blo 622298 1126963 := bstep (se 1 (by rfl) ⟨845222, by rfl⟩ : syracuseStep 1126963 = 1690445) B1690445
theorem B1782337 : Blo 622298 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B2110103 : Blo 622298 2110103 := bstep (se 1 (by rfl) ⟨1582577, by rfl⟩ : syracuseStep 2110103 = 3165155) B3165155
theorem B701131 : Blo 622298 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B701239 : Blo 622298 701239 := bstep (se 1 (by rfl) ⟨525929, by rfl⟩ : syracuseStep 701239 = 1051859) B1051859
theorem B21672805 : Blo 622298 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B701419 : Blo 622298 701419 := bstep (se 1 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 701419 = 1052129) B1052129
theorem B701527 : Blo 622298 701527 := bstep (se 1 (by rfl) ⟨526145, by rfl⟩ : syracuseStep 701527 = 1052291) B1052291
theorem B2372759 : Blo 622298 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B2110643 : Blo 622298 2110643 := bstep (se 1 (by rfl) ⟨1582982, by rfl⟩ : syracuseStep 2110643 = 3165965) B3165965
theorem B701707 : Blo 622298 701707 := bstep (se 1 (by rfl) ⟨526280, by rfl⟩ : syracuseStep 701707 = 1052561) B1052561
theorem B701815 : Blo 622298 701815 := bstep (se 1 (by rfl) ⟨526361, by rfl⟩ : syracuseStep 701815 = 1052723) B1052723
theorem B2110913 : Blo 622298 2110913 := bstep (se 2 (by rfl) ⟨791592, by rfl⟩ : syracuseStep 2110913 = 1583185) B1583185
theorem B701995 : Blo 622298 701995 := bstep (se 1 (by rfl) ⟨526496, by rfl⟩ : syracuseStep 701995 = 1052993) B1052993
theorem B21575261 : Blo 622298 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B702103 : Blo 622298 702103 := bstep (se 1 (by rfl) ⟨526577, by rfl⟩ : syracuseStep 702103 = 1053155) B1053155
theorem B997067 : Blo 622298 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B5060369 : Blo 622298 5060369 := bstep (se 2 (by rfl) ⟨1897638, by rfl⟩ : syracuseStep 5060369 = 3795277) B3795277
theorem B1128217 : Blo 622298 1128217 := bstep (se 2 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 1128217 = 846163) B846163
theorem B702283 : Blo 622298 702283 := bstep (se 1 (by rfl) ⟨526712, by rfl⟩ : syracuseStep 702283 = 1053425) B1053425
theorem B702391 : Blo 622298 702391 := bstep (se 1 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 702391 = 1053587) B1053587
theorem B2111453 : Blo 622298 2111453 := bstep (se 3 (by rfl) ⟨395897, by rfl⟩ : syracuseStep 2111453 = 791795) B791795
theorem B2668619 : Blo 622298 2668619 := bstep (se 1 (by rfl) ⟨2001464, by rfl⟩ : syracuseStep 2668619 = 4002929) B4002929
theorem B702571 : Blo 622298 702571 := bstep (se 1 (by rfl) ⟨526928, by rfl⟩ : syracuseStep 702571 = 1053857) B1053857
theorem B702679 : Blo 622298 702679 := bstep (se 1 (by rfl) ⟨527009, by rfl⟩ : syracuseStep 702679 = 1054019) B1054019
theorem B2374019 : Blo 622298 2374019 := bstep (se 1 (by rfl) ⟨1780514, by rfl⟩ : syracuseStep 2374019 = 3561029) B3561029
theorem B702859 : Blo 622298 702859 := bstep (se 1 (by rfl) ⟨527144, by rfl⟩ : syracuseStep 702859 = 1054289) B1054289
theorem B8010161 : Blo 622298 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B997849 : Blo 622298 997849 := bstep (se 2 (by rfl) ⟨374193, by rfl⟩ : syracuseStep 997849 = 748387) B748387
theorem B702967 : Blo 622298 702967 := bstep (se 1 (by rfl) ⟨527225, by rfl⟩ : syracuseStep 702967 = 1054451) B1054451
theorem B703147 : Blo 622298 703147 := bstep (se 1 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 703147 = 1054721) B1054721
theorem B703255 : Blo 622298 703255 := bstep (se 1 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 703255 = 1054883) B1054883
theorem B7093169 : Blo 622298 7093169 := bstep (se 2 (by rfl) ⟨2659938, by rfl⟩ : syracuseStep 7093169 = 5319877) B5319877
theorem B703435 : Blo 622298 703435 := bstep (se 1 (by rfl) ⟨527576, by rfl⟩ : syracuseStep 703435 = 1055153) B1055153
theorem B3161105 : Blo 622298 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B703543 : Blo 622298 703543 := bstep (se 1 (by rfl) ⟨527657, by rfl⟩ : syracuseStep 703543 = 1055315) B1055315
theorem B2112587 : Blo 622298 2112587 := bstep (se 1 (by rfl) ⟨1584440, by rfl⟩ : syracuseStep 2112587 = 3168881) B3168881
theorem B6077591 : Blo 622298 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B3161267 : Blo 622298 3161267 := bstep (se 1 (by rfl) ⟨2370950, by rfl⟩ : syracuseStep 3161267 = 4741901) B4741901
theorem B703723 : Blo 622298 703723 := bstep (se 1 (by rfl) ⟨527792, by rfl⟩ : syracuseStep 703723 = 1055585) B1055585
theorem B703831 : Blo 622298 703831 := bstep (se 1 (by rfl) ⟨527873, by rfl⟩ : syracuseStep 703831 = 1055747) B1055747
theorem B2112857 : Blo 622298 2112857 := bstep (se 2 (by rfl) ⟨792321, by rfl⟩ : syracuseStep 2112857 = 1584643) B1584643
theorem B2669917 : Blo 622298 2669917 := bstep (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) B1001219
theorem B704011 : Blo 622298 704011 := bstep (se 1 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 704011 = 1056017) B1056017
theorem B2539073 : Blo 622298 2539073 := bstep (se 2 (by rfl) ⟨952152, by rfl⟩ : syracuseStep 2539073 = 1904305) B1904305
theorem B704119 : Blo 622298 704119 := bstep (se 1 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 704119 = 1056179) B1056179
theorem B933515 : Blo 622298 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B933527 : Blo 622298 933527 := bstep (se 1 (by rfl) ⟨700145, by rfl⟩ : syracuseStep 933527 = 1400291) B1400291
theorem B2670259 : Blo 622298 2670259 := bstep (se 1 (by rfl) ⟨2002694, by rfl⟩ : syracuseStep 2670259 = 4005389) B4005389
theorem B933593 : Blo 622298 933593 := bstep (se 2 (by rfl) ⟨350097, by rfl⟩ : syracuseStep 933593 = 700195) B700195
theorem B1425163 : Blo 622298 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B704299 : Blo 622298 704299 := bstep (se 1 (by rfl) ⟨528224, by rfl⟩ : syracuseStep 704299 = 1056449) B1056449
theorem B5062445 : Blo 622298 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B933707 : Blo 622298 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B933719 : Blo 622298 933719 := bstep (se 1 (by rfl) ⟨700289, by rfl⟩ : syracuseStep 933719 = 1400579) B1400579
theorem B704407 : Blo 622298 704407 := bstep (se 1 (by rfl) ⟨528305, by rfl⟩ : syracuseStep 704407 = 1056611) B1056611
theorem B933785 : Blo 622298 933785 := bstep (se 2 (by rfl) ⟨350169, by rfl⟩ : syracuseStep 933785 = 700339) B700339
theorem B933899 : Blo 622298 933899 := bstep (se 1 (by rfl) ⟨700424, by rfl⟩ : syracuseStep 933899 = 1400849) B1400849
theorem B933911 : Blo 622298 933911 := bstep (se 1 (by rfl) ⟨700433, by rfl⟩ : syracuseStep 933911 = 1400867) B1400867
theorem B2113559 : Blo 622298 2113559 := bstep (se 1 (by rfl) ⟨1585169, by rfl⟩ : syracuseStep 2113559 = 3170339) B3170339
theorem B933977 : Blo 622298 933977 := bstep (se 2 (by rfl) ⟨350241, by rfl⟩ : syracuseStep 933977 = 700483) B700483
theorem B934091 : Blo 622298 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B934103 : Blo 622298 934103 := bstep (se 1 (by rfl) ⟨700577, by rfl⟩ : syracuseStep 934103 = 1401155) B1401155
theorem B934169 : Blo 622298 934169 := bstep (se 2 (by rfl) ⟨350313, by rfl⟩ : syracuseStep 934169 = 700627) B700627
theorem B934283 : Blo 622298 934283 := bstep (se 1 (by rfl) ⟨700712, by rfl⟩ : syracuseStep 934283 = 1401425) B1401425
theorem B934295 : Blo 622298 934295 := bstep (se 1 (by rfl) ⟨700721, by rfl⟩ : syracuseStep 934295 = 1401443) B1401443
theorem B934361 : Blo 622298 934361 := bstep (se 2 (by rfl) ⟨350385, by rfl⟩ : syracuseStep 934361 = 700771) B700771
theorem B1688087 : Blo 622298 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B934475 : Blo 622298 934475 := bstep (se 1 (by rfl) ⟨700856, by rfl⟩ : syracuseStep 934475 = 1401713) B1401713
theorem B934487 : Blo 622298 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B3555971 : Blo 622298 3555971 := bstep (se 1 (by rfl) ⟨2666978, by rfl⟩ : syracuseStep 3555971 = 5333957) B5333957
theorem B1262231 : Blo 622298 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B934553 : Blo 622298 934553 := bstep (se 2 (by rfl) ⟨350457, by rfl⟩ : syracuseStep 934553 = 700915) B700915
theorem B934667 : Blo 622298 934667 := bstep (se 1 (by rfl) ⟨701000, by rfl⟩ : syracuseStep 934667 = 1402001) B1402001
theorem B934679 : Blo 622298 934679 := bstep (se 1 (by rfl) ⟨701009, by rfl⟩ : syracuseStep 934679 = 1402019) B1402019
theorem B934745 : Blo 622298 934745 := bstep (se 2 (by rfl) ⟨350529, by rfl⟩ : syracuseStep 934745 = 701059) B701059
theorem B3031901 : Blo 622298 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B934859 : Blo 622298 934859 := bstep (se 1 (by rfl) ⟨701144, by rfl⟩ : syracuseStep 934859 = 1402289) B1402289
theorem B934871 : Blo 622298 934871 := bstep (se 1 (by rfl) ⟨701153, by rfl⟩ : syracuseStep 934871 = 1402307) B1402307
theorem B934937 : Blo 622298 934937 := bstep (se 2 (by rfl) ⟨350601, by rfl⟩ : syracuseStep 934937 = 701203) B701203
theorem B3163211 : Blo 622298 3163211 := bstep (se 1 (by rfl) ⟨2372408, by rfl⟩ : syracuseStep 3163211 = 4744817) B4744817
theorem B935051 : Blo 622298 935051 := bstep (se 1 (by rfl) ⟨701288, by rfl⟩ : syracuseStep 935051 = 1402577) B1402577
theorem B935063 : Blo 622298 935063 := bstep (se 1 (by rfl) ⟨701297, by rfl⟩ : syracuseStep 935063 = 1402595) B1402595
theorem B2704535 : Blo 622298 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B1688779 : Blo 622298 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B935129 : Blo 622298 935129 := bstep (se 2 (by rfl) ⟨350673, by rfl⟩ : syracuseStep 935129 = 701347) B701347
theorem B21677357 : Blo 622298 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B935243 : Blo 622298 935243 := bstep (se 1 (by rfl) ⟨701432, by rfl⟩ : syracuseStep 935243 = 1402865) B1402865
theorem B935255 : Blo 622298 935255 := bstep (se 1 (by rfl) ⟨701441, by rfl⟩ : syracuseStep 935255 = 1402883) B1402883
theorem B5064067 : Blo 622298 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B935321 : Blo 622298 935321 := bstep (se 2 (by rfl) ⟨350745, by rfl⟩ : syracuseStep 935321 = 701491) B701491
theorem B2377133 : Blo 622298 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B6014387 : Blo 622298 6014387 := bstep (se 1 (by rfl) ⟨4510790, by rfl⟩ : syracuseStep 6014387 = 9021581) B9021581
theorem B935435 : Blo 622298 935435 := bstep (se 1 (by rfl) ⟨701576, by rfl⟩ : syracuseStep 935435 = 1403153) B1403153
theorem B935447 : Blo 622298 935447 := bstep (se 1 (by rfl) ⟨701585, by rfl⟩ : syracuseStep 935447 = 1403171) B1403171
theorem B1263179 : Blo 622298 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B935513 : Blo 622298 935513 := bstep (se 2 (by rfl) ⟨350817, by rfl⟩ : syracuseStep 935513 = 701635) B701635
theorem B10929815 : Blo 622298 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B935627 : Blo 622298 935627 := bstep (se 1 (by rfl) ⟨701720, by rfl⟩ : syracuseStep 935627 = 1403441) B1403441
theorem B935639 : Blo 622298 935639 := bstep (se 1 (by rfl) ⟨701729, by rfl⟩ : syracuseStep 935639 = 1403459) B1403459
theorem B935705 : Blo 622298 935705 := bstep (se 2 (by rfl) ⟨350889, by rfl⟩ : syracuseStep 935705 = 701779) B701779
theorem B935819 : Blo 622298 935819 := bstep (se 1 (by rfl) ⟨701864, by rfl⟩ : syracuseStep 935819 = 1403729) B1403729
theorem B2246545 : Blo 622298 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B935831 : Blo 622298 935831 := bstep (se 1 (by rfl) ⟨701873, by rfl⟩ : syracuseStep 935831 = 1403747) B1403747
theorem B2246573 : Blo 622298 2246573 := bstep (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) B842465
theorem B51136433 : Blo 622298 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B935897 : Blo 622298 935897 := bstep (se 2 (by rfl) ⟨350961, by rfl⟩ : syracuseStep 935897 = 701923) B701923
theorem B4737041 : Blo 622298 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B936011 : Blo 622298 936011 := bstep (se 1 (by rfl) ⟨702008, by rfl⟩ : syracuseStep 936011 = 1404017) B1404017
theorem B936023 : Blo 622298 936023 := bstep (se 1 (by rfl) ⟨702017, by rfl⟩ : syracuseStep 936023 = 1404035) B1404035
theorem B936089 : Blo 622298 936089 := bstep (se 2 (by rfl) ⟨351033, by rfl⟩ : syracuseStep 936089 = 702067) B702067
theorem B2377907 : Blo 622298 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B936203 : Blo 622298 936203 := bstep (se 1 (by rfl) ⟨702152, by rfl⟩ : syracuseStep 936203 = 1404305) B1404305
theorem B936215 : Blo 622298 936215 := bstep (se 1 (by rfl) ⟨702161, by rfl⟩ : syracuseStep 936215 = 1404323) B1404323
theorem B936281 : Blo 622298 936281 := bstep (se 2 (by rfl) ⟨351105, by rfl⟩ : syracuseStep 936281 = 702211) B702211
theorem B936395 : Blo 622298 936395 := bstep (se 1 (by rfl) ⟨702296, by rfl⟩ : syracuseStep 936395 = 1404593) B1404593
theorem B936407 : Blo 622298 936407 := bstep (se 1 (by rfl) ⟨702305, by rfl⟩ : syracuseStep 936407 = 1404611) B1404611
theorem B1329689 : Blo 622298 1329689 := bstep (se 2 (by rfl) ⟨498633, by rfl⟩ : syracuseStep 1329689 = 997267) B997267
theorem B936473 : Blo 622298 936473 := bstep (se 2 (by rfl) ⟨351177, by rfl⟩ : syracuseStep 936473 = 702355) B702355
theorem B1690163 : Blo 622298 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B936587 : Blo 622298 936587 := bstep (se 1 (by rfl) ⟨702440, by rfl⟩ : syracuseStep 936587 = 1404881) B1404881
theorem B936599 : Blo 622298 936599 := bstep (se 1 (by rfl) ⟨702449, by rfl⟩ : syracuseStep 936599 = 1404899) B1404899
theorem B1428119 : Blo 622298 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B936665 : Blo 622298 936665 := bstep (se 2 (by rfl) ⟨351249, by rfl⟩ : syracuseStep 936665 = 702499) B702499
theorem B3164993 : Blo 622298 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B936779 : Blo 622298 936779 := bstep (se 1 (by rfl) ⟨702584, by rfl⟩ : syracuseStep 936779 = 1405169) B1405169
theorem B936791 : Blo 622298 936791 := bstep (se 1 (by rfl) ⟨702593, by rfl⟩ : syracuseStep 936791 = 1405187) B1405187
theorem B936857 : Blo 622298 936857 := bstep (se 2 (by rfl) ⟨351321, by rfl⟩ : syracuseStep 936857 = 702643) B702643
theorem B936971 : Blo 622298 936971 := bstep (se 1 (by rfl) ⟨702728, by rfl⟩ : syracuseStep 936971 = 1405457) B1405457
theorem B936983 : Blo 622298 936983 := bstep (se 1 (by rfl) ⟨702737, by rfl⟩ : syracuseStep 936983 = 1405475) B1405475
theorem B937049 : Blo 622298 937049 := bstep (se 2 (by rfl) ⟨351393, by rfl⟩ : syracuseStep 937049 = 702787) B702787
theorem B8244355 : Blo 622298 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B937163 : Blo 622298 937163 := bstep (se 1 (by rfl) ⟨702872, by rfl⟩ : syracuseStep 937163 = 1405745) B1405745
theorem B937175 : Blo 622298 937175 := bstep (se 1 (by rfl) ⟨702881, by rfl⟩ : syracuseStep 937175 = 1405763) B1405763
theorem B2673881 : Blo 622298 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B1068299 : Blo 622298 1068299 := bstep (se 1 (by rfl) ⟨801224, by rfl⟩ : syracuseStep 1068299 = 1602449) B1602449
theorem B937241 : Blo 622298 937241 := bstep (se 2 (by rfl) ⟨351465, by rfl⟩ : syracuseStep 937241 = 702931) B702931
theorem B937355 : Blo 622298 937355 := bstep (se 1 (by rfl) ⟨703016, by rfl⟩ : syracuseStep 937355 = 1406033) B1406033
theorem B937367 : Blo 622298 937367 := bstep (se 1 (by rfl) ⟨703025, by rfl⟩ : syracuseStep 937367 = 1406051) B1406051
theorem B4804019 : Blo 622298 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B6180275 : Blo 622298 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B937433 : Blo 622298 937433 := bstep (se 2 (by rfl) ⟨351537, by rfl⟩ : syracuseStep 937433 = 703075) B703075
theorem B1330739 : Blo 622298 1330739 := bstep (se 1 (by rfl) ⟨998054, by rfl⟩ : syracuseStep 1330739 = 1996109) B1996109
theorem B937547 : Blo 622298 937547 := bstep (se 1 (by rfl) ⟨703160, by rfl⟩ : syracuseStep 937547 = 1406321) B1406321
theorem B937559 : Blo 622298 937559 := bstep (se 1 (by rfl) ⟨703169, by rfl⟩ : syracuseStep 937559 = 1406339) B1406339
theorem B937625 : Blo 622298 937625 := bstep (se 2 (by rfl) ⟨351609, by rfl⟩ : syracuseStep 937625 = 703219) B703219
theorem B937739 : Blo 622298 937739 := bstep (se 1 (by rfl) ⟨703304, by rfl⟩ : syracuseStep 937739 = 1406609) B1406609
theorem B937751 : Blo 622298 937751 := bstep (se 1 (by rfl) ⟨703313, by rfl⟩ : syracuseStep 937751 = 1406627) B1406627
theorem B937817 : Blo 622298 937817 := bstep (se 2 (by rfl) ⟨351681, by rfl⟩ : syracuseStep 937817 = 703363) B703363
theorem B937931 : Blo 622298 937931 := bstep (se 1 (by rfl) ⟨703448, by rfl⟩ : syracuseStep 937931 = 1406897) B1406897
theorem B937943 : Blo 622298 937943 := bstep (se 1 (by rfl) ⟨703457, by rfl⟩ : syracuseStep 937943 = 1406915) B1406915
theorem B938009 : Blo 622298 938009 := bstep (se 2 (by rfl) ⟨351753, by rfl⟩ : syracuseStep 938009 = 703507) B703507
theorem B5689379 : Blo 622298 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B1331329 : Blo 622298 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B938123 : Blo 622298 938123 := bstep (se 1 (by rfl) ⟨703592, by rfl⟩ : syracuseStep 938123 = 1407185) B1407185
theorem B938135 : Blo 622298 938135 := bstep (se 1 (by rfl) ⟨703601, by rfl⟩ : syracuseStep 938135 = 1407203) B1407203
theorem B938201 : Blo 622298 938201 := bstep (se 2 (by rfl) ⟨351825, by rfl⟩ : syracuseStep 938201 = 703651) B703651
theorem B3199297 : Blo 622298 3199297 := bstep (se 2 (by rfl) ⟨1199736, by rfl⟩ : syracuseStep 3199297 = 2399473) B2399473
theorem B938315 : Blo 622298 938315 := bstep (se 1 (by rfl) ⟨703736, by rfl⟩ : syracuseStep 938315 = 1407473) B1407473
theorem B938327 : Blo 622298 938327 := bstep (se 1 (by rfl) ⟨703745, by rfl⟩ : syracuseStep 938327 = 1407491) B1407491
theorem B938393 : Blo 622298 938393 := bstep (se 2 (by rfl) ⟨351897, by rfl⟩ : syracuseStep 938393 = 703795) B703795
theorem B938507 : Blo 622298 938507 := bstep (se 1 (by rfl) ⟨703880, by rfl⟩ : syracuseStep 938507 = 1407761) B1407761
theorem B8999437 : Blo 622298 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B938519 : Blo 622298 938519 := bstep (se 1 (by rfl) ⟨703889, by rfl⟩ : syracuseStep 938519 = 1407779) B1407779
theorem B938585 : Blo 622298 938585 := bstep (se 2 (by rfl) ⟨351969, by rfl⟩ : syracuseStep 938585 = 703939) B703939
theorem B938699 : Blo 622298 938699 := bstep (se 1 (by rfl) ⟨704024, by rfl⟩ : syracuseStep 938699 = 1408049) B1408049
theorem B938711 : Blo 622298 938711 := bstep (se 1 (by rfl) ⟨704033, by rfl⟩ : syracuseStep 938711 = 1408067) B1408067
theorem B3166937 : Blo 622298 3166937 := bstep (se 2 (by rfl) ⟨1187601, by rfl⟩ : syracuseStep 3166937 = 2375203) B2375203
theorem B938777 : Blo 622298 938777 := bstep (se 2 (by rfl) ⟨352041, by rfl⟩ : syracuseStep 938777 = 704083) B704083
theorem B7983917 : Blo 622298 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B938891 : Blo 622298 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B938903 : Blo 622298 938903 := bstep (se 1 (by rfl) ⟨704177, by rfl⟩ : syracuseStep 938903 = 1408355) B1408355
theorem B938969 : Blo 622298 938969 := bstep (se 2 (by rfl) ⟨352113, by rfl⟩ : syracuseStep 938969 = 704227) B704227
theorem B939083 : Blo 622298 939083 := bstep (se 1 (by rfl) ⟨704312, by rfl⟩ : syracuseStep 939083 = 1408625) B1408625
theorem B939095 : Blo 622298 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B939161 : Blo 622298 939161 := bstep (se 2 (by rfl) ⟨352185, by rfl⟩ : syracuseStep 939161 = 704371) B704371
theorem B939275 : Blo 622298 939275 := bstep (se 1 (by rfl) ⟨704456, by rfl⟩ : syracuseStep 939275 = 1408913) B1408913
theorem B939287 : Blo 622298 939287 := bstep (se 1 (by rfl) ⟨704465, by rfl⟩ : syracuseStep 939287 = 1408931) B1408931
theorem B3429697 : Blo 622298 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B939353 : Blo 622298 939353 := bstep (se 2 (by rfl) ⟨352257, by rfl⟩ : syracuseStep 939353 = 704515) B704515
theorem B841099 : Blo 622298 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B710155 : Blo 622298 710155 := bstep (se 1 (by rfl) ⟨532616, by rfl⟩ : syracuseStep 710155 = 1065233) B1065233
theorem B1332875 : Blo 622298 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B5330609 : Blo 622298 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B4740929 : Blo 622298 4740929 := bstep (se 2 (by rfl) ⟨1777848, by rfl⟩ : syracuseStep 4740929 = 3555697) B3555697
theorem B841547 : Blo 622298 841547 := bstep (se 1 (by rfl) ⟨631160, by rfl⟩ : syracuseStep 841547 = 1262321) B1262321
theorem B3561347 : Blo 622298 3561347 := bstep (se 1 (by rfl) ⟨2671010, by rfl⟩ : syracuseStep 3561347 = 5342021) B5342021
theorem B87447605 : Blo 622298 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B1202327 : Blo 622298 1202327 := bstep (se 1 (by rfl) ⟨901745, by rfl⟩ : syracuseStep 1202327 = 1803491) B1803491
theorem B3168557 : Blo 622298 3168557 := bstep (se 3 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 3168557 = 1188209) B1188209
theorem B5691713 : Blo 622298 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B3561803 : Blo 622298 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B1497523 : Blo 622298 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B1333721 : Blo 622298 1333721 := bstep (se 2 (by rfl) ⟨500145, by rfl⟩ : syracuseStep 1333721 = 1000291) B1000291
theorem B3594883 : Blo 622298 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B2841389 : Blo 622298 2841389 := bstep (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) B1065521
theorem B3005657 : Blo 622298 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B1334515 : Blo 622298 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B1400345 : Blo 622298 1400345 := bstep (se 2 (by rfl) ⟨525129, by rfl⟩ : syracuseStep 1400345 = 1050259) B1050259
theorem B1400435 : Blo 622298 1400435 := bstep (se 1 (by rfl) ⟨1050326, by rfl⟩ : syracuseStep 1400435 = 2100653) B2100653
theorem B1400471 : Blo 622298 1400471 := bstep (se 1 (by rfl) ⟨1050353, by rfl⟩ : syracuseStep 1400471 = 2100707) B2100707
theorem B4742873 : Blo 622298 4742873 := bstep (se 2 (by rfl) ⟨1778577, by rfl⟩ : syracuseStep 4742873 = 3557155) B3557155
theorem B1400651 : Blo 622298 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B1400705 : Blo 622298 1400705 := bstep (se 2 (by rfl) ⟨525264, by rfl⟩ : syracuseStep 1400705 = 1050529) B1050529
theorem B1335361 : Blo 622298 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B20242507 : Blo 622298 20242507 := bstep (se 1 (by rfl) ⟨15181880, by rfl⟩ : syracuseStep 20242507 = 30363761) B30363761
theorem B1400921 : Blo 622298 1400921 := bstep (se 2 (by rfl) ⟨525345, by rfl⟩ : syracuseStep 1400921 = 1050691) B1050691
theorem B1401011 : Blo 622298 1401011 := bstep (se 1 (by rfl) ⟨1050758, by rfl⟩ : syracuseStep 1401011 = 2101517) B2101517
theorem B1401047 : Blo 622298 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B1401227 : Blo 622298 1401227 := bstep (se 1 (by rfl) ⟨1050920, by rfl⟩ : syracuseStep 1401227 = 2101841) B2101841
theorem B1499543 : Blo 622298 1499543 := bstep (se 1 (by rfl) ⟨1124657, by rfl⟩ : syracuseStep 1499543 = 2249315) B2249315
theorem B1335703 : Blo 622298 1335703 := bstep (se 1 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 1335703 = 2003555) B2003555
theorem B1401281 : Blo 622298 1401281 := bstep (se 2 (by rfl) ⟨525480, by rfl⟩ : syracuseStep 1401281 = 1050961) B1050961
theorem B2286083 : Blo 622298 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B3990167 : Blo 622298 3990167 := bstep (se 1 (by rfl) ⟨2992625, by rfl⟩ : syracuseStep 3990167 = 5985251) B5985251
theorem B1401497 : Blo 622298 1401497 := bstep (se 2 (by rfl) ⟨525561, by rfl⟩ : syracuseStep 1401497 = 1051123) B1051123
theorem B1401587 : Blo 622298 1401587 := bstep (se 1 (by rfl) ⟨1051190, by rfl⟩ : syracuseStep 1401587 = 2102381) B2102381
theorem B1401623 : Blo 622298 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B1401803 : Blo 622298 1401803 := bstep (se 1 (by rfl) ⟨1051352, by rfl⟩ : syracuseStep 1401803 = 2102705) B2102705
theorem B1401857 : Blo 622298 1401857 := bstep (se 2 (by rfl) ⟨525696, by rfl⟩ : syracuseStep 1401857 = 1051393) B1051393
theorem B3990707 : Blo 622298 3990707 := bstep (se 1 (by rfl) ⟨2993030, by rfl⟩ : syracuseStep 3990707 = 5986061) B5986061
theorem B1402073 : Blo 622298 1402073 := bstep (se 2 (by rfl) ⟨525777, by rfl⟩ : syracuseStep 1402073 = 1051555) B1051555
theorem B1402163 : Blo 622298 1402163 := bstep (se 1 (by rfl) ⟨1051622, by rfl⟩ : syracuseStep 1402163 = 2103245) B2103245
theorem B1402199 : Blo 622298 1402199 := bstep (se 1 (by rfl) ⟨1051649, by rfl⟩ : syracuseStep 1402199 = 2103299) B2103299
theorem B1500619 : Blo 622298 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B1402379 : Blo 622298 1402379 := bstep (se 1 (by rfl) ⟨1051784, by rfl⟩ : syracuseStep 1402379 = 2103569) B2103569
theorem B2254387 : Blo 622298 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B1402433 : Blo 622298 1402433 := bstep (se 2 (by rfl) ⟨525912, by rfl⟩ : syracuseStep 1402433 = 1051825) B1051825
theorem B1336907 : Blo 622298 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B6416023 : Blo 622298 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B1402649 : Blo 622298 1402649 := bstep (se 2 (by rfl) ⟨525993, by rfl⟩ : syracuseStep 1402649 = 1051987) B1051987
theorem B1402739 : Blo 622298 1402739 := bstep (se 1 (by rfl) ⟨1052054, by rfl⟩ : syracuseStep 1402739 = 2104109) B2104109
theorem B1402775 : Blo 622298 1402775 := bstep (se 1 (by rfl) ⟨1052081, by rfl⟩ : syracuseStep 1402775 = 2104163) B2104163
theorem B1402955 : Blo 622298 1402955 := bstep (se 1 (by rfl) ⟨1052216, by rfl⟩ : syracuseStep 1402955 = 2104433) B2104433
theorem B1337419 : Blo 622298 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B4810853 : Blo 622298 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B1403009 : Blo 622298 1403009 := bstep (se 2 (by rfl) ⟨526128, by rfl⟩ : syracuseStep 1403009 = 1052257) B1052257
theorem B7104833 : Blo 622298 7104833 := bstep (se 2 (by rfl) ⟨2664312, by rfl⟩ : syracuseStep 7104833 = 5328625) B5328625
theorem B1403225 : Blo 622298 1403225 := bstep (se 2 (by rfl) ⟨526209, by rfl⟩ : syracuseStep 1403225 = 1052419) B1052419
theorem B1403315 : Blo 622298 1403315 := bstep (se 1 (by rfl) ⟨1052486, by rfl⟩ : syracuseStep 1403315 = 2104973) B2104973
theorem B1403351 : Blo 622298 1403351 := bstep (se 1 (by rfl) ⟨1052513, by rfl⟩ : syracuseStep 1403351 = 2105027) B2105027
theorem B2845277 : Blo 622298 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B3992165 : Blo 622298 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B1403531 : Blo 622298 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B1403585 : Blo 622298 1403585 := bstep (se 2 (by rfl) ⟨526344, by rfl⟩ : syracuseStep 1403585 = 1052689) B1052689
theorem B1502003 : Blo 622298 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B3566429 : Blo 622298 3566429 := bstep (se 3 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 3566429 = 1337411) B1337411
theorem B1403801 : Blo 622298 1403801 := bstep (se 2 (by rfl) ⟨526425, by rfl⟩ : syracuseStep 1403801 = 1052851) B1052851
theorem B1403891 : Blo 622298 1403891 := bstep (se 1 (by rfl) ⟨1052918, by rfl⟩ : syracuseStep 1403891 = 2105837) B2105837
theorem B1403927 : Blo 622298 1403927 := bstep (se 1 (by rfl) ⟨1052945, by rfl⟩ : syracuseStep 1403927 = 2105891) B2105891
theorem B4746275 : Blo 622298 4746275 := bstep (se 1 (by rfl) ⟨3559706, by rfl⟩ : syracuseStep 4746275 = 7119413) B7119413
theorem B1404107 : Blo 622298 1404107 := bstep (se 1 (by rfl) ⟨1053080, by rfl⟩ : syracuseStep 1404107 = 2106161) B2106161
theorem B1404161 : Blo 622298 1404161 := bstep (se 2 (by rfl) ⟨526560, by rfl⟩ : syracuseStep 1404161 = 1053121) B1053121
theorem B1404377 : Blo 622298 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B1404467 : Blo 622298 1404467 := bstep (se 1 (by rfl) ⟨1053350, by rfl⟩ : syracuseStep 1404467 = 2106701) B2106701
theorem B1404503 : Blo 622298 1404503 := bstep (se 1 (by rfl) ⟨1053377, by rfl⟩ : syracuseStep 1404503 = 2106755) B2106755
theorem B1404683 : Blo 622298 1404683 := bstep (se 1 (by rfl) ⟨1053512, by rfl⟩ : syracuseStep 1404683 = 2107025) B2107025
theorem B1404737 : Blo 622298 1404737 := bstep (se 2 (by rfl) ⟨526776, by rfl⟩ : syracuseStep 1404737 = 1053553) B1053553
theorem B1994647 : Blo 622298 1994647 := bstep (se 1 (by rfl) ⟨1495985, by rfl⟩ : syracuseStep 1994647 = 2991971) B2991971
theorem B1994699 : Blo 622298 1994699 := bstep (se 1 (by rfl) ⟨1496024, by rfl⟩ : syracuseStep 1994699 = 2992049) B2992049
theorem B749579 : Blo 622298 749579 := bstep (se 1 (by rfl) ⟨562184, by rfl⟩ : syracuseStep 749579 = 1124369) B1124369
theorem B1404953 : Blo 622298 1404953 := bstep (se 2 (by rfl) ⟨526857, by rfl⟩ : syracuseStep 1404953 = 1053715) B1053715
theorem B1405043 : Blo 622298 1405043 := bstep (se 1 (by rfl) ⟨1053782, by rfl⟩ : syracuseStep 1405043 = 2107565) B2107565
theorem B3371159 : Blo 622298 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B1405079 : Blo 622298 1405079 := bstep (se 1 (by rfl) ⟨1053809, by rfl⟩ : syracuseStep 1405079 = 2107619) B2107619
theorem B3371329 : Blo 622298 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B1405259 : Blo 622298 1405259 := bstep (se 1 (by rfl) ⟨1053944, by rfl⟩ : syracuseStep 1405259 = 2107889) B2107889
theorem B749911 : Blo 622298 749911 := bstep (se 1 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 749911 = 1124867) B1124867
theorem B1405313 : Blo 622298 1405313 := bstep (se 2 (by rfl) ⟨526992, by rfl⟩ : syracuseStep 1405313 = 1053985) B1053985
theorem B1405529 : Blo 622298 1405529 := bstep (se 2 (by rfl) ⟨527073, by rfl⟩ : syracuseStep 1405529 = 1054147) B1054147
theorem B5075549 : Blo 622298 5075549 := bstep (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) B1903331
theorem B1405619 : Blo 622298 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B1405655 : Blo 622298 1405655 := bstep (se 1 (by rfl) ⟨1054241, by rfl⟩ : syracuseStep 1405655 = 2108483) B2108483
theorem B1405835 : Blo 622298 1405835 := bstep (se 1 (by rfl) ⟨1054376, by rfl⟩ : syracuseStep 1405835 = 2108753) B2108753
theorem B1405889 : Blo 622298 1405889 := bstep (se 2 (by rfl) ⟨527208, by rfl⟩ : syracuseStep 1405889 = 1054417) B1054417
theorem B1406105 : Blo 622298 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B1406195 : Blo 622298 1406195 := bstep (se 1 (by rfl) ⟨1054646, by rfl⟩ : syracuseStep 1406195 = 2109293) B2109293
theorem B1406231 : Blo 622298 1406231 := bstep (se 1 (by rfl) ⟨1054673, by rfl⟩ : syracuseStep 1406231 = 2109347) B2109347
theorem B5076269 : Blo 622298 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B6387121 : Blo 622298 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B1897931 : Blo 622298 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B1406411 : Blo 622298 1406411 := bstep (se 1 (by rfl) ⟨1054808, by rfl⟩ : syracuseStep 1406411 = 2109617) B2109617
theorem B1406465 : Blo 622298 1406465 := bstep (se 2 (by rfl) ⟨527424, by rfl⟩ : syracuseStep 1406465 = 1054849) B1054849
theorem B1996339 : Blo 622298 1996339 := bstep (se 1 (by rfl) ⟨1497254, by rfl⟩ : syracuseStep 1996339 = 2994509) B2994509
theorem B1898077 : Blo 622298 1898077 := bstep (se 3 (by rfl) ⟨355889, by rfl⟩ : syracuseStep 1898077 = 711779) B711779
theorem B1996481 : Blo 622298 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B1406681 : Blo 622298 1406681 := bstep (se 2 (by rfl) ⟨527505, by rfl⟩ : syracuseStep 1406681 = 1055011) B1055011
theorem B1406771 : Blo 622298 1406771 := bstep (se 1 (by rfl) ⟨1055078, by rfl⟩ : syracuseStep 1406771 = 2110157) B2110157
theorem B1406807 : Blo 622298 1406807 := bstep (se 1 (by rfl) ⟨1055105, by rfl⟩ : syracuseStep 1406807 = 2110211) B2110211
theorem B1406987 : Blo 622298 1406987 := bstep (se 1 (by rfl) ⟨1055240, by rfl⟩ : syracuseStep 1406987 = 2110481) B2110481
theorem B1407041 : Blo 622298 1407041 := bstep (se 2 (by rfl) ⟨527640, by rfl⟩ : syracuseStep 1407041 = 1055281) B1055281
theorem B1407257 : Blo 622298 1407257 := bstep (se 2 (by rfl) ⟨527721, by rfl⟩ : syracuseStep 1407257 = 1055443) B1055443
theorem B1407347 : Blo 622298 1407347 := bstep (se 1 (by rfl) ⟨1055510, by rfl⟩ : syracuseStep 1407347 = 2111021) B2111021
theorem B1407383 : Blo 622298 1407383 := bstep (se 1 (by rfl) ⟨1055537, by rfl⟩ : syracuseStep 1407383 = 2111075) B2111075
theorem B1407563 : Blo 622298 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B752203 : Blo 622298 752203 := bstep (se 1 (by rfl) ⟨564152, by rfl⟩ : syracuseStep 752203 = 1128305) B1128305
theorem B1407617 : Blo 622298 1407617 := bstep (se 2 (by rfl) ⟨527856, by rfl⟩ : syracuseStep 1407617 = 1055713) B1055713
theorem B752395 : Blo 622298 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B1407833 : Blo 622298 1407833 := bstep (se 2 (by rfl) ⟨527937, by rfl⟩ : syracuseStep 1407833 = 1055875) B1055875
theorem B1407923 : Blo 622298 1407923 := bstep (se 1 (by rfl) ⟨1055942, by rfl⟩ : syracuseStep 1407923 = 2111885) B2111885
theorem B1407959 : Blo 622298 1407959 := bstep (se 1 (by rfl) ⟨1055969, by rfl⟩ : syracuseStep 1407959 = 2111939) B2111939
theorem B1408139 : Blo 622298 1408139 := bstep (se 1 (by rfl) ⟨1056104, by rfl⟩ : syracuseStep 1408139 = 2112209) B2112209
theorem B1408193 : Blo 622298 1408193 := bstep (se 2 (by rfl) ⟨528072, by rfl⟩ : syracuseStep 1408193 = 1056145) B1056145
theorem B1408409 : Blo 622298 1408409 := bstep (se 2 (by rfl) ⟨528153, by rfl⟩ : syracuseStep 1408409 = 1056307) B1056307
theorem B1408499 : Blo 622298 1408499 := bstep (se 1 (by rfl) ⟨1056374, by rfl⟩ : syracuseStep 1408499 = 2112749) B2112749
theorem B1408535 : Blo 622298 1408535 := bstep (se 1 (by rfl) ⟨1056401, by rfl⟩ : syracuseStep 1408535 = 2112803) B2112803
theorem B1408715 : Blo 622298 1408715 := bstep (se 1 (by rfl) ⟨1056536, by rfl⟩ : syracuseStep 1408715 = 2113073) B2113073
theorem B622315 : Blo 622298 622315 := bstep (se 1 (by rfl) ⟨466736, by rfl⟩ : syracuseStep 622315 = 933473) B933473
theorem B622327 : Blo 622298 622327 := bstep (se 1 (by rfl) ⟨466745, by rfl⟩ : syracuseStep 622327 = 933491) B933491
theorem B1408769 : Blo 622298 1408769 := bstep (se 2 (by rfl) ⟨528288, by rfl⟩ : syracuseStep 1408769 = 1056577) B1056577
theorem B622347 : Blo 622298 622347 := bstep (se 1 (by rfl) ⟨466760, by rfl⟩ : syracuseStep 622347 = 933521) B933521
theorem B622359 : Blo 622298 622359 := bstep (se 1 (by rfl) ⟨466769, by rfl⟩ : syracuseStep 622359 = 933539) B933539
theorem B622379 : Blo 622298 622379 := bstep (se 1 (by rfl) ⟨466784, by rfl⟩ : syracuseStep 622379 = 933569) B933569
theorem B622391 : Blo 622298 622391 := bstep (se 1 (by rfl) ⟨466793, by rfl⟩ : syracuseStep 622391 = 933587) B933587
theorem B622411 : Blo 622298 622411 := bstep (se 1 (by rfl) ⟨466808, by rfl⟩ : syracuseStep 622411 = 933617) B933617
theorem B4063051 : Blo 622298 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B622423 : Blo 622298 622423 := bstep (se 1 (by rfl) ⟨466817, by rfl⟩ : syracuseStep 622423 = 933635) B933635
theorem B622443 : Blo 622298 622443 := bstep (se 1 (by rfl) ⟨466832, by rfl⟩ : syracuseStep 622443 = 933665) B933665
theorem B9633653 : Blo 622298 9633653 := bstep (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) B903155
theorem B622455 : Blo 622298 622455 := bstep (se 1 (by rfl) ⟨466841, by rfl⟩ : syracuseStep 622455 = 933683) B933683
theorem B622475 : Blo 622298 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B622487 : Blo 622298 622487 := bstep (se 1 (by rfl) ⟨466865, by rfl⟩ : syracuseStep 622487 = 933731) B933731
theorem B622507 : Blo 622298 622507 := bstep (se 1 (by rfl) ⟨466880, by rfl⟩ : syracuseStep 622507 = 933761) B933761
theorem B622519 : Blo 622298 622519 := bstep (se 1 (by rfl) ⟨466889, by rfl⟩ : syracuseStep 622519 = 933779) B933779
theorem B622539 : Blo 622298 622539 := bstep (se 1 (by rfl) ⟨466904, by rfl⟩ : syracuseStep 622539 = 933809) B933809
theorem B622551 : Blo 622298 622551 := bstep (se 1 (by rfl) ⟨466913, by rfl⟩ : syracuseStep 622551 = 933827) B933827
theorem B950231 : Blo 622298 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B1408985 : Blo 622298 1408985 := bstep (se 2 (by rfl) ⟨528369, by rfl⟩ : syracuseStep 1408985 = 1056739) B1056739
theorem B622571 : Blo 622298 622571 := bstep (se 1 (by rfl) ⟨466928, by rfl⟩ : syracuseStep 622571 = 933857) B933857
theorem B622583 : Blo 622298 622583 := bstep (se 1 (by rfl) ⟨466937, by rfl⟩ : syracuseStep 622583 = 933875) B933875
theorem B622599 : Blo 622298 622599 := bstep (se 1 (by rfl) ⟨466949, by rfl⟩ : syracuseStep 622599 = 933899) B933899
theorem B622607 : Blo 622298 622607 := bstep (se 1 (by rfl) ⟨466955, by rfl⟩ : syracuseStep 622607 = 933911) B933911
theorem B1409039 : Blo 622298 1409039 := bstep (se 1 (by rfl) ⟨1056779, by rfl⟩ : syracuseStep 1409039 = 2113559) B2113559
theorem B1998877 : Blo 622298 1998877 := bstep (se 3 (by rfl) ⟨374789, by rfl⟩ : syracuseStep 1998877 = 749579) B749579
theorem B1409057 : Blo 622298 1409057 := bstep (se 2 (by rfl) ⟨528396, by rfl⟩ : syracuseStep 1409057 = 1056793) B1056793
theorem B622651 : Blo 622298 622651 := bstep (se 1 (by rfl) ⟨466988, by rfl⟩ : syracuseStep 622651 = 933977) B933977
theorem B622727 : Blo 622298 622727 := bstep (se 1 (by rfl) ⟨467045, by rfl⟩ : syracuseStep 622727 = 934091) B934091
theorem B622735 : Blo 622298 622735 := bstep (se 1 (by rfl) ⟨467051, by rfl⟩ : syracuseStep 622735 = 934103) B934103
theorem B622779 : Blo 622298 622779 := bstep (se 1 (by rfl) ⟨467084, by rfl⟩ : syracuseStep 622779 = 934169) B934169
theorem B622855 : Blo 622298 622855 := bstep (se 1 (by rfl) ⟨467141, by rfl⟩ : syracuseStep 622855 = 934283) B934283
theorem B622863 : Blo 622298 622863 := bstep (se 1 (by rfl) ⟨467147, by rfl⟩ : syracuseStep 622863 = 934295) B934295
theorem B622907 : Blo 622298 622907 := bstep (se 1 (by rfl) ⟨467180, by rfl⟩ : syracuseStep 622907 = 934361) B934361
theorem B622983 : Blo 622298 622983 := bstep (se 1 (by rfl) ⟨467237, by rfl⟩ : syracuseStep 622983 = 934475) B934475
theorem B622991 : Blo 622298 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B14418323 : Blo 622298 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B623035 : Blo 622298 623035 := bstep (se 1 (by rfl) ⟨467276, by rfl⟩ : syracuseStep 623035 = 934553) B934553
theorem B623111 : Blo 622298 623111 := bstep (se 1 (by rfl) ⟨467333, by rfl⟩ : syracuseStep 623111 = 934667) B934667
theorem B623119 : Blo 622298 623119 := bstep (se 1 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 623119 = 934679) B934679
theorem B932774453 : Blo 622298 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B623163 : Blo 622298 623163 := bstep (se 1 (by rfl) ⟨467372, by rfl⟩ : syracuseStep 623163 = 934745) B934745
theorem B623239 : Blo 622298 623239 := bstep (se 1 (by rfl) ⟨467429, by rfl⟩ : syracuseStep 623239 = 934859) B934859
theorem B623247 : Blo 622298 623247 := bstep (se 1 (by rfl) ⟨467435, by rfl⟩ : syracuseStep 623247 = 934871) B934871
theorem B623291 : Blo 622298 623291 := bstep (se 1 (by rfl) ⟨467468, by rfl⟩ : syracuseStep 623291 = 934937) B934937
theorem B623367 : Blo 622298 623367 := bstep (se 1 (by rfl) ⟨467525, by rfl⟩ : syracuseStep 623367 = 935051) B935051
theorem B623375 : Blo 622298 623375 := bstep (se 1 (by rfl) ⟨467531, by rfl⟩ : syracuseStep 623375 = 935063) B935063
theorem B1803023 : Blo 622298 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B623419 : Blo 622298 623419 := bstep (se 1 (by rfl) ⟨467564, by rfl⟩ : syracuseStep 623419 = 935129) B935129
theorem B14451571 : Blo 622298 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B623495 : Blo 622298 623495 := bstep (se 1 (by rfl) ⟨467621, by rfl⟩ : syracuseStep 623495 = 935243) B935243
theorem B623503 : Blo 622298 623503 := bstep (se 1 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 623503 = 935255) B935255
theorem B623547 : Blo 622298 623547 := bstep (se 1 (by rfl) ⟨467660, by rfl⟩ : syracuseStep 623547 = 935321) B935321
theorem B623623 : Blo 622298 623623 := bstep (se 1 (by rfl) ⟨467717, by rfl⟩ : syracuseStep 623623 = 935435) B935435
theorem B623631 : Blo 622298 623631 := bstep (se 1 (by rfl) ⟨467723, by rfl⟩ : syracuseStep 623631 = 935447) B935447
theorem B623675 : Blo 622298 623675 := bstep (se 1 (by rfl) ⟨467756, by rfl⟩ : syracuseStep 623675 = 935513) B935513
theorem B623751 : Blo 622298 623751 := bstep (se 1 (by rfl) ⟨467813, by rfl⟩ : syracuseStep 623751 = 935627) B935627
theorem B623759 : Blo 622298 623759 := bstep (se 1 (by rfl) ⟨467819, by rfl⟩ : syracuseStep 623759 = 935639) B935639
theorem B623803 : Blo 622298 623803 := bstep (se 1 (by rfl) ⟨467852, by rfl⟩ : syracuseStep 623803 = 935705) B935705
theorem B623879 : Blo 622298 623879 := bstep (se 1 (by rfl) ⟨467909, by rfl⟩ : syracuseStep 623879 = 935819) B935819
theorem B623887 : Blo 622298 623887 := bstep (se 1 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 623887 = 935831) B935831
theorem B623931 : Blo 622298 623931 := bstep (se 1 (by rfl) ⟨467948, by rfl⟩ : syracuseStep 623931 = 935897) B935897
theorem B624007 : Blo 622298 624007 := bstep (se 1 (by rfl) ⟨468005, by rfl⟩ : syracuseStep 624007 = 936011) B936011
theorem B624015 : Blo 622298 624015 := bstep (se 1 (by rfl) ⟨468011, by rfl⟩ : syracuseStep 624015 = 936023) B936023
theorem B624059 : Blo 622298 624059 := bstep (se 1 (by rfl) ⟨468044, by rfl⟩ : syracuseStep 624059 = 936089) B936089
theorem B624135 : Blo 622298 624135 := bstep (se 1 (by rfl) ⟨468101, by rfl⟩ : syracuseStep 624135 = 936203) B936203
theorem B624143 : Blo 622298 624143 := bstep (se 1 (by rfl) ⟨468107, by rfl⟩ : syracuseStep 624143 = 936215) B936215
theorem B2885149 : Blo 622298 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B3606059 : Blo 622298 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B624187 : Blo 622298 624187 := bstep (se 1 (by rfl) ⟨468140, by rfl⟩ : syracuseStep 624187 = 936281) B936281
theorem B7603789 : Blo 622298 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B1902167 : Blo 622298 1902167 := bstep (se 1 (by rfl) ⟨1426625, by rfl⟩ : syracuseStep 1902167 = 2853251) B2853251
theorem B624263 : Blo 622298 624263 := bstep (se 1 (by rfl) ⟨468197, by rfl⟩ : syracuseStep 624263 = 936395) B936395
theorem B624271 : Blo 622298 624271 := bstep (se 1 (by rfl) ⟨468203, by rfl⟩ : syracuseStep 624271 = 936407) B936407
theorem B886459 : Blo 622298 886459 := bstep (se 1 (by rfl) ⟨664844, by rfl⟩ : syracuseStep 886459 = 1329689) B1329689
theorem B624315 : Blo 622298 624315 := bstep (se 1 (by rfl) ⟨468236, by rfl⟩ : syracuseStep 624315 = 936473) B936473
theorem B1050313 : Blo 622298 1050313 := bstep (se 2 (by rfl) ⟨393867, by rfl⟩ : syracuseStep 1050313 = 787735) B787735
theorem B788231 : Blo 622298 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B624391 : Blo 622298 624391 := bstep (se 1 (by rfl) ⟨468293, by rfl⟩ : syracuseStep 624391 = 936587) B936587
theorem B624399 : Blo 622298 624399 := bstep (se 1 (by rfl) ⟨468299, by rfl⟩ : syracuseStep 624399 = 936599) B936599
theorem B952079 : Blo 622298 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B624443 : Blo 622298 624443 := bstep (se 1 (by rfl) ⟨468332, by rfl⟩ : syracuseStep 624443 = 936665) B936665
theorem B6752089 : Blo 622298 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B624519 : Blo 622298 624519 := bstep (se 1 (by rfl) ⟨468389, by rfl⟩ : syracuseStep 624519 = 936779) B936779
theorem B624527 : Blo 622298 624527 := bstep (se 1 (by rfl) ⟨468395, by rfl⟩ : syracuseStep 624527 = 936791) B936791
theorem B2000825 : Blo 622298 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B624571 : Blo 622298 624571 := bstep (se 1 (by rfl) ⟨468428, by rfl⟩ : syracuseStep 624571 = 936857) B936857
theorem B1181641 : Blo 622298 1181641 := bstep (se 2 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 1181641 = 886231) B886231
theorem B624647 : Blo 622298 624647 := bstep (se 1 (by rfl) ⟨468485, by rfl⟩ : syracuseStep 624647 = 936971) B936971
theorem B624655 : Blo 622298 624655 := bstep (se 1 (by rfl) ⟨468491, by rfl⟩ : syracuseStep 624655 = 936983) B936983
theorem B624699 : Blo 622298 624699 := bstep (se 1 (by rfl) ⟨468524, by rfl⟩ : syracuseStep 624699 = 937049) B937049
theorem B624775 : Blo 622298 624775 := bstep (se 1 (by rfl) ⟨468581, by rfl⟩ : syracuseStep 624775 = 937163) B937163
theorem B624783 : Blo 622298 624783 := bstep (se 1 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 624783 = 937175) B937175
theorem B624827 : Blo 622298 624827 := bstep (se 1 (by rfl) ⟨468620, by rfl⟩ : syracuseStep 624827 = 937241) B937241
theorem B8554697 : Blo 622298 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B624903 : Blo 622298 624903 := bstep (se 1 (by rfl) ⟨468677, by rfl⟩ : syracuseStep 624903 = 937355) B937355
theorem B624911 : Blo 622298 624911 := bstep (se 1 (by rfl) ⟨468683, by rfl⟩ : syracuseStep 624911 = 937367) B937367
theorem B1575227 : Blo 622298 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B624955 : Blo 622298 624955 := bstep (se 1 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 624955 = 937433) B937433
theorem B887159 : Blo 622298 887159 := bstep (se 1 (by rfl) ⟨665369, by rfl⟩ : syracuseStep 887159 = 1330739) B1330739
theorem B1051015 : Blo 622298 1051015 := bstep (se 1 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 1051015 = 1576523) B1576523
theorem B625031 : Blo 622298 625031 := bstep (se 1 (by rfl) ⟨468773, by rfl⟩ : syracuseStep 625031 = 937547) B937547
theorem B788879 : Blo 622298 788879 := bstep (se 1 (by rfl) ⟨591659, by rfl⟩ : syracuseStep 788879 = 1183319) B1183319
theorem B625039 : Blo 622298 625039 := bstep (se 1 (by rfl) ⟨468779, by rfl⟩ : syracuseStep 625039 = 937559) B937559
theorem B625083 : Blo 622298 625083 := bstep (se 1 (by rfl) ⟨468812, by rfl⟩ : syracuseStep 625083 = 937625) B937625
theorem B4819409 : Blo 622298 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B625159 : Blo 622298 625159 := bstep (se 1 (by rfl) ⟨468869, by rfl⟩ : syracuseStep 625159 = 937739) B937739
theorem B1903115 : Blo 622298 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B625167 : Blo 622298 625167 := bstep (se 1 (by rfl) ⟨468875, by rfl⟩ : syracuseStep 625167 = 937751) B937751
theorem B625211 : Blo 622298 625211 := bstep (se 1 (by rfl) ⟨468908, by rfl⟩ : syracuseStep 625211 = 937817) B937817
theorem B625287 : Blo 622298 625287 := bstep (se 1 (by rfl) ⟨468965, by rfl⟩ : syracuseStep 625287 = 937931) B937931
theorem B625295 : Blo 622298 625295 := bstep (se 1 (by rfl) ⟨468971, by rfl⟩ : syracuseStep 625295 = 937943) B937943
theorem B1575571 : Blo 622298 1575571 := bstep (se 1 (by rfl) ⟨1181678, by rfl⟩ : syracuseStep 1575571 = 2363357) B2363357
theorem B625339 : Blo 622298 625339 := bstep (se 1 (by rfl) ⟨469004, by rfl⟩ : syracuseStep 625339 = 938009) B938009
theorem B625415 : Blo 622298 625415 := bstep (se 1 (by rfl) ⟨469061, by rfl⟩ : syracuseStep 625415 = 938123) B938123
theorem B625423 : Blo 622298 625423 := bstep (se 1 (by rfl) ⟨469067, by rfl⟩ : syracuseStep 625423 = 938135) B938135
theorem B1575713 : Blo 622298 1575713 := bstep (se 2 (by rfl) ⟨590892, by rfl⟩ : syracuseStep 1575713 = 1181785) B1181785
theorem B4557617 : Blo 622298 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B625467 : Blo 622298 625467 := bstep (se 1 (by rfl) ⟨469100, by rfl⟩ : syracuseStep 625467 = 938201) B938201
theorem B625543 : Blo 622298 625543 := bstep (se 1 (by rfl) ⟨469157, by rfl⟩ : syracuseStep 625543 = 938315) B938315
theorem B625551 : Blo 622298 625551 := bstep (se 1 (by rfl) ⟨469163, by rfl⟩ : syracuseStep 625551 = 938327) B938327
theorem B625595 : Blo 622298 625595 := bstep (se 1 (by rfl) ⟨469196, by rfl⟩ : syracuseStep 625595 = 938393) B938393
theorem B625671 : Blo 622298 625671 := bstep (se 1 (by rfl) ⟨469253, by rfl⟩ : syracuseStep 625671 = 938507) B938507
theorem B1051663 : Blo 622298 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B625679 : Blo 622298 625679 := bstep (se 1 (by rfl) ⟨469259, by rfl⟩ : syracuseStep 625679 = 938519) B938519
theorem B625723 : Blo 622298 625723 := bstep (se 1 (by rfl) ⟨469292, by rfl⟩ : syracuseStep 625723 = 938585) B938585
theorem B625799 : Blo 622298 625799 := bstep (se 1 (by rfl) ⟨469349, by rfl⟩ : syracuseStep 625799 = 938699) B938699
theorem B625807 : Blo 622298 625807 := bstep (se 1 (by rfl) ⟨469355, by rfl⟩ : syracuseStep 625807 = 938711) B938711
theorem B625851 : Blo 622298 625851 := bstep (se 1 (by rfl) ⟨469388, by rfl⟩ : syracuseStep 625851 = 938777) B938777
theorem B625927 : Blo 622298 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B625935 : Blo 622298 625935 := bstep (se 1 (by rfl) ⟨469451, by rfl⟩ : syracuseStep 625935 = 938903) B938903
theorem B625979 : Blo 622298 625979 := bstep (se 1 (by rfl) ⟨469484, by rfl⟩ : syracuseStep 625979 = 938969) B938969
theorem B626055 : Blo 622298 626055 := bstep (se 1 (by rfl) ⟨469541, by rfl⟩ : syracuseStep 626055 = 939083) B939083
theorem B626063 : Blo 622298 626063 := bstep (se 1 (by rfl) ⟨469547, by rfl⟩ : syracuseStep 626063 = 939095) B939095
theorem B626107 : Blo 622298 626107 := bstep (se 1 (by rfl) ⟨469580, by rfl⟩ : syracuseStep 626107 = 939161) B939161
theorem B626183 : Blo 622298 626183 := bstep (se 1 (by rfl) ⟨469637, by rfl⟩ : syracuseStep 626183 = 939275) B939275
theorem B626191 : Blo 622298 626191 := bstep (se 1 (by rfl) ⟨469643, by rfl⟩ : syracuseStep 626191 = 939287) B939287
theorem B1052203 : Blo 622298 1052203 := bstep (se 1 (by rfl) ⟨789152, by rfl⟩ : syracuseStep 1052203 = 1578305) B1578305
theorem B626235 : Blo 622298 626235 := bstep (se 1 (by rfl) ⟨469676, by rfl⟩ : syracuseStep 626235 = 939353) B939353
theorem B1773191 : Blo 622298 1773191 := bstep (se 1 (by rfl) ⟨1329893, by rfl⟩ : syracuseStep 1773191 = 2659787) B2659787
theorem B1052345 : Blo 622298 1052345 := bstep (se 2 (by rfl) ⟨394629, by rfl⟩ : syracuseStep 1052345 = 789259) B789259
theorem B1576705 : Blo 622298 1576705 := bstep (se 2 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 1576705 = 1182529) B1182529
theorem B888583 : Blo 622298 888583 := bstep (se 1 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 888583 = 1332875) B1332875
theorem B1183547 : Blo 622298 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B1773373 : Blo 622298 1773373 := bstep (se 3 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 1773373 = 665015) B665015
theorem B2101139 : Blo 622298 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B3379097 : Blo 622298 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B1773839 : Blo 622298 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B1184033 : Blo 622298 1184033 := bstep (se 2 (by rfl) ⟨444012, by rfl⟩ : syracuseStep 1184033 = 888025) B888025
theorem B889147 : Blo 622298 889147 := bstep (se 1 (by rfl) ⟨666860, by rfl⟩ : syracuseStep 889147 = 1333721) B1333721
theorem B1577303 : Blo 622298 1577303 := bstep (se 1 (by rfl) ⟨1182977, by rfl⟩ : syracuseStep 1577303 = 2365955) B2365955
theorem B1053047 : Blo 622298 1053047 := bstep (se 1 (by rfl) ⟨789785, by rfl⟩ : syracuseStep 1053047 = 1579571) B1579571
theorem B1708489 : Blo 622298 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B2658845 : Blo 622298 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B1577515 : Blo 622298 1577515 := bstep (se 1 (by rfl) ⟨1183136, by rfl⟩ : syracuseStep 1577515 = 2366273) B2366273
theorem B6754859 : Blo 622298 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B1184375 : Blo 622298 1184375 := bstep (se 1 (by rfl) ⟨888281, by rfl⟩ : syracuseStep 1184375 = 1776563) B1776563
theorem B1577657 : Blo 622298 1577657 := bstep (se 2 (by rfl) ⟨591621, by rfl⟩ : syracuseStep 1577657 = 1183243) B1183243
theorem B7574309 : Blo 622298 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B1053499 : Blo 622298 1053499 := bstep (se 1 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 1053499 = 1580249) B1580249
theorem B2003771 : Blo 622298 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B1708919 : Blo 622298 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B3150737 : Blo 622298 3150737 := bstep (se 2 (by rfl) ⟨1181526, by rfl⟩ : syracuseStep 3150737 = 2363053) B2363053
theorem B1053641 : Blo 622298 1053641 := bstep (se 2 (by rfl) ⟨395115, by rfl⟩ : syracuseStep 1053641 = 790231) B790231
theorem B890041 : Blo 622298 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B2659529 : Blo 622298 2659529 := bstep (se 2 (by rfl) ⟨997323, by rfl⟩ : syracuseStep 2659529 = 1994647) B1994647
theorem B2102543 : Blo 622298 2102543 := bstep (se 1 (by rfl) ⟨1576907, by rfl⟩ : syracuseStep 2102543 = 3153815) B3153815
theorem B791851 : Blo 622298 791851 := bstep (se 1 (by rfl) ⟨593888, by rfl⟩ : syracuseStep 791851 = 1187777) B1187777
theorem B1775105 : Blo 622298 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B2102813 : Blo 622298 2102813 := bstep (se 3 (by rfl) ⟨394277, by rfl⟩ : syracuseStep 2102813 = 788555) B788555
theorem B1054343 : Blo 622298 1054343 := bstep (se 1 (by rfl) ⟨790757, by rfl⟩ : syracuseStep 1054343 = 1581515) B1581515
theorem B1578649 : Blo 622298 1578649 := bstep (se 2 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 1578649 = 1183987) B1183987
theorem B4265729 : Blo 622298 4265729 := bstep (se 2 (by rfl) ⟨1599648, by rfl⟩ : syracuseStep 4265729 = 3199297) B3199297
theorem B4495105 : Blo 622298 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B2660111 : Blo 622298 2660111 := bstep (se 1 (by rfl) ⟨1995083, by rfl⟩ : syracuseStep 2660111 = 3990167) B3990167
theorem B1578811 : Blo 622298 1578811 := bstep (se 1 (by rfl) ⟨1184108, by rfl⟩ : syracuseStep 1578811 = 2368217) B2368217
theorem B1578953 : Blo 622298 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B11999249 : Blo 622298 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B2365469 : Blo 622298 2365469 := bstep (se 3 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 2365469 = 887051) B887051
theorem B2365483 : Blo 622298 2365483 := bstep (se 1 (by rfl) ⟨1774112, by rfl⟩ : syracuseStep 2365483 = 3548225) B3548225
theorem B2660471 : Blo 622298 2660471 := bstep (se 1 (by rfl) ⟨1995353, by rfl⟩ : syracuseStep 2660471 = 3990707) B3990707
theorem B15177901 : Blo 622298 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B1185977 : Blo 622298 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B1054991 : Blo 622298 1054991 := bstep (se 1 (by rfl) ⟨791243, by rfl⟩ : syracuseStep 1054991 = 1582487) B1582487
theorem B1579297 : Blo 622298 1579297 := bstep (se 2 (by rfl) ⟨592236, by rfl⟩ : syracuseStep 1579297 = 1184473) B1184473
theorem B891271 : Blo 622298 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B3545491 : Blo 622298 3545491 := bstep (se 1 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 3545491 = 5318237) B5318237
theorem B1186319 : Blo 622298 1186319 := bstep (se 1 (by rfl) ⟨889739, by rfl⟩ : syracuseStep 1186319 = 1779479) B1779479
theorem B1055531 : Blo 622298 1055531 := bstep (se 1 (by rfl) ⟨791648, by rfl⟩ : syracuseStep 1055531 = 1583297) B1583297
theorem B1579895 : Blo 622298 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B2104217 : Blo 622298 2104217 := bstep (se 2 (by rfl) ⟨789081, by rfl⟩ : syracuseStep 2104217 = 1578163) B1578163
theorem B6757283 : Blo 622298 6757283 := bstep (se 1 (by rfl) ⟨5067962, by rfl⟩ : syracuseStep 6757283 = 10135925) B10135925
theorem B3152843 : Blo 622298 3152843 := bstep (se 1 (by rfl) ⟨2364632, by rfl⟩ : syracuseStep 3152843 = 4729265) B4729265
theorem B2661443 : Blo 622298 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B1776755 : Blo 622298 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1121465 : Blo 622298 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B1055929 : Blo 622298 1055929 := bstep (se 2 (by rfl) ⟨395973, by rfl⟩ : syracuseStep 1055929 = 791947) B791947
theorem B3153167 : Blo 622298 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B1187131 : Blo 622298 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B1187207 : Blo 622298 1187207 := bstep (se 1 (by rfl) ⟨890405, by rfl⟩ : syracuseStep 1187207 = 1780811) B1780811
theorem B2661785 : Blo 622298 2661785 := bstep (se 2 (by rfl) ⟨998169, by rfl⟩ : syracuseStep 2661785 = 1996339) B1996339
theorem B2530769 : Blo 622298 2530769 := bstep (se 2 (by rfl) ⟨949038, by rfl⟩ : syracuseStep 2530769 = 1898077) B1898077
theorem B1777211 : Blo 622298 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B4726349 : Blo 622298 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B2104919 : Blo 622298 2104919 := bstep (se 1 (by rfl) ⟨1578689, by rfl⟩ : syracuseStep 2104919 = 3157379) B3157379
theorem B1187617 : Blo 622298 1187617 := bstep (se 2 (by rfl) ⟨445356, by rfl⟩ : syracuseStep 1187617 = 890713) B890713
theorem B1056631 : Blo 622298 1056631 := bstep (se 1 (by rfl) ⟨792473, by rfl⟩ : syracuseStep 1056631 = 1584947) B1584947
theorem B1056827 : Blo 622298 1056827 := bstep (se 1 (by rfl) ⟨792620, by rfl⟩ : syracuseStep 1056827 = 1585241) B1585241
theorem B2105405 : Blo 622298 2105405 := bstep (se 3 (by rfl) ⟨394763, by rfl⟩ : syracuseStep 2105405 = 789527) B789527
theorem B3547223 : Blo 622298 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B1187959 : Blo 622298 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B1581191 : Blo 622298 1581191 := bstep (se 1 (by rfl) ⟨1185893, by rfl⟩ : syracuseStep 1581191 = 2371787) B2371787
theorem B1581241 : Blo 622298 1581241 := bstep (se 2 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 1581241 = 1185931) B1185931
theorem B1777963 : Blo 622298 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B5710139 : Blo 622298 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B3383699 : Blo 622298 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B25960981 : Blo 622298 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B1778237 : Blo 622298 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B3154625 : Blo 622298 3154625 := bstep (se 2 (by rfl) ⟨1182984, by rfl⟩ : syracuseStep 3154625 = 2365969) B2365969
theorem B1581839 : Blo 622298 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B4793177 : Blo 622298 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B3384179 : Blo 622298 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B13477013 : Blo 622298 13477013 := bstep (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) B631735
theorem B1779079 : Blo 622298 1779079 := bstep (se 1 (by rfl) ⟨1334309, by rfl⟩ : syracuseStep 1779079 = 2668619) B2668619
theorem B2106809 : Blo 622298 2106809 := bstep (se 2 (by rfl) ⟨790053, by rfl⟩ : syracuseStep 2106809 = 1580107) B1580107
theorem B1582537 : Blo 622298 1582537 := bstep (se 2 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 1582537 = 1186903) B1186903
theorem B1582679 : Blo 622298 1582679 := bstep (se 1 (by rfl) ⟨1187009, by rfl⟩ : syracuseStep 1582679 = 2374019) B2374019
theorem B1779353 : Blo 622298 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B4728779 : Blo 622298 4728779 := bstep (se 1 (by rfl) ⟨3546584, by rfl⟩ : syracuseStep 4728779 = 7093169) B7093169
theorem B3155921 : Blo 622298 3155921 := bstep (se 2 (by rfl) ⟨1183470, by rfl⟩ : syracuseStep 3155921 = 2366941) B2366941
theorem B2107403 : Blo 622298 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B2107511 : Blo 622298 2107511 := bstep (se 1 (by rfl) ⟨1580633, by rfl⟩ : syracuseStep 2107511 = 3161267) B3161267
theorem B5417401 : Blo 622298 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B2533949 : Blo 622298 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B2108105 : Blo 622298 2108105 := bstep (se 2 (by rfl) ⟨790539, by rfl⟩ : syracuseStep 2108105 = 1581079) B1581079
theorem B1780481 : Blo 622298 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B2370647 : Blo 622298 2370647 := bstep (se 1 (by rfl) ⟨1777985, by rfl⟩ : syracuseStep 2370647 = 3555971) B3555971
theorem B1780937 : Blo 622298 1780937 := bstep (se 2 (by rfl) ⟨667851, by rfl⟩ : syracuseStep 1780937 = 1335703) B1335703
theorem B2108807 : Blo 622298 2108807 := bstep (se 1 (by rfl) ⟨1581605, by rfl⟩ : syracuseStep 2108807 = 3163211) B3163211
theorem B2371133 : Blo 622298 2371133 := bstep (se 3 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 2371133 = 889175) B889175
theorem B1584755 : Blo 622298 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B4009591 : Blo 622298 4009591 := bstep (se 1 (by rfl) ⟨3007193, by rfl⟩ : syracuseStep 4009591 = 6014387) B6014387
theorem B2109185 : Blo 622298 2109185 := bstep (se 2 (by rfl) ⟨790944, by rfl⟩ : syracuseStep 2109185 = 1581889) B1581889
theorem B7286543 : Blo 622298 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B700303 : Blo 622298 700303 := bstep (se 1 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 700303 = 1050455) B1050455
theorem B34090955 : Blo 622298 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B3158027 : Blo 622298 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B4501565 : Blo 622298 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B1585271 : Blo 622298 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B3158189 : Blo 622298 3158189 := bstep (se 3 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 3158189 = 1184321) B1184321
theorem B12824821 : Blo 622298 12824821 := bstep (se 5 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 12824821 = 1202327) B1202327
theorem B1126775 : Blo 622298 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B700807 : Blo 622298 700807 := bstep (se 1 (by rfl) ⟨525605, by rfl⟩ : syracuseStep 700807 = 1051211) B1051211
theorem B2109995 : Blo 622298 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B700987 : Blo 622298 700987 := bstep (se 1 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 700987 = 1051481) B1051481
theorem B1782587 : Blo 622298 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B7123787 : Blo 622298 7123787 := bstep (se 1 (by rfl) ⟨5342840, by rfl⟩ : syracuseStep 7123787 = 10685681) B10685681
theorem B2372561 : Blo 622298 2372561 := bstep (se 2 (by rfl) ⟨889710, by rfl⟩ : syracuseStep 2372561 = 1779421) B1779421
theorem B701455 : Blo 622298 701455 := bstep (se 1 (by rfl) ⟨526091, by rfl⟩ : syracuseStep 701455 = 1052183) B1052183
theorem B5321861 : Blo 622298 5321861 := bstep (se 4 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 5321861 = 997849) B997849
theorem B1848473 : Blo 622298 1848473 := bstep (se 2 (by rfl) ⟨693177, by rfl⟩ : syracuseStep 1848473 = 1386355) B1386355
theorem B2995393 : Blo 622298 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B1783225 : Blo 622298 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B701959 : Blo 622298 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B6010469 : Blo 622298 6010469 := bstep (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) B1126963
theorem B702139 : Blo 622298 702139 := bstep (se 1 (by rfl) ⟨526604, by rfl⟩ : syracuseStep 702139 = 1053209) B1053209
theorem B3159809 : Blo 622298 3159809 := bstep (se 2 (by rfl) ⟨1184928, by rfl⟩ : syracuseStep 3159809 = 2369857) B2369857
theorem B2111291 : Blo 622298 2111291 := bstep (se 1 (by rfl) ⟨1583468, by rfl⟩ : syracuseStep 2111291 = 3166937) B3166937
theorem B5322611 : Blo 622298 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B1685623 : Blo 622298 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B702607 : Blo 622298 702607 := bstep (se 1 (by rfl) ⟨526955, by rfl⟩ : syracuseStep 702607 = 1053911) B1053911
theorem B2111777 : Blo 622298 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B2668859 : Blo 622298 2668859 := bstep (se 1 (by rfl) ⟨2001644, by rfl⟩ : syracuseStep 2668859 = 4003289) B4003289
theorem B3553739 : Blo 622298 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B3160619 : Blo 622298 3160619 := bstep (se 1 (by rfl) ⟨2370464, by rfl⟩ : syracuseStep 3160619 = 4740929) B4740929
theorem B2374231 : Blo 622298 2374231 := bstep (se 1 (by rfl) ⟨1780673, by rfl⟩ : syracuseStep 2374231 = 3561347) B3561347
theorem B703111 : Blo 622298 703111 := bstep (se 1 (by rfl) ⟨527333, by rfl⟩ : syracuseStep 703111 = 1054667) B1054667
theorem B703291 : Blo 622298 703291 := bstep (se 1 (by rfl) ⟨527468, by rfl⟩ : syracuseStep 703291 = 1054937) B1054937
theorem B10992473 : Blo 622298 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B2112371 : Blo 622298 2112371 := bstep (se 1 (by rfl) ⟨1584278, by rfl⟩ : syracuseStep 2112371 = 3168557) B3168557
theorem B2374535 : Blo 622298 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B6011927 : Blo 622298 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B3423293 : Blo 622298 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B2374717 : Blo 622298 2374717 := bstep (se 3 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 2374717 = 890519) B890519
theorem B4734125 : Blo 622298 4734125 := bstep (se 3 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 4734125 = 1775297) B1775297
theorem B703759 : Blo 622298 703759 := bstep (se 1 (by rfl) ⟨527819, by rfl⟩ : syracuseStep 703759 = 1055639) B1055639
theorem B2244125 : Blo 622298 2244125 := bstep (se 3 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 2244125 = 841547) B841547
theorem B933449 : Blo 622298 933449 := bstep (se 2 (by rfl) ⟨350043, by rfl⟩ : syracuseStep 933449 = 700087) B700087
theorem B933563 : Blo 622298 933563 := bstep (se 1 (by rfl) ⟨700172, by rfl⟩ : syracuseStep 933563 = 1400345) B1400345
theorem B933623 : Blo 622298 933623 := bstep (se 1 (by rfl) ⟨700217, by rfl⟩ : syracuseStep 933623 = 1400435) B1400435
theorem B704263 : Blo 622298 704263 := bstep (se 1 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 704263 = 1056395) B1056395
theorem B933647 : Blo 622298 933647 := bstep (se 1 (by rfl) ⟨700235, by rfl⟩ : syracuseStep 933647 = 1400471) B1400471
theorem B769807 : Blo 622298 769807 := bstep (se 1 (by rfl) ⟨577355, by rfl⟩ : syracuseStep 769807 = 1154711) B1154711
theorem B933689 : Blo 622298 933689 := bstep (se 2 (by rfl) ⟨350133, by rfl⟩ : syracuseStep 933689 = 700267) B700267
theorem B3161915 : Blo 622298 3161915 := bstep (se 1 (by rfl) ⟨2371436, by rfl⟩ : syracuseStep 3161915 = 4742873) B4742873
theorem B933767 : Blo 622298 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B933803 : Blo 622298 933803 := bstep (se 1 (by rfl) ⟨700352, by rfl⟩ : syracuseStep 933803 = 1400705) B1400705
theorem B704443 : Blo 622298 704443 := bstep (se 1 (by rfl) ⟨528332, by rfl⟩ : syracuseStep 704443 = 1056665) B1056665
theorem B933833 : Blo 622298 933833 := bstep (se 2 (by rfl) ⟨350187, by rfl⟩ : syracuseStep 933833 = 700375) B700375
theorem B3162077 : Blo 622298 3162077 := bstep (se 3 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 3162077 = 1185779) B1185779
theorem B933947 : Blo 622298 933947 := bstep (se 1 (by rfl) ⟨700460, by rfl⟩ : syracuseStep 933947 = 1400921) B1400921
theorem B934007 : Blo 622298 934007 := bstep (se 1 (by rfl) ⟨700505, by rfl⟩ : syracuseStep 934007 = 1401011) B1401011
theorem B934031 : Blo 622298 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B934073 : Blo 622298 934073 := bstep (se 2 (by rfl) ⟨350277, by rfl⟩ : syracuseStep 934073 = 700555) B700555
theorem B934151 : Blo 622298 934151 := bstep (se 1 (by rfl) ⟨700613, by rfl⟩ : syracuseStep 934151 = 1401227) B1401227
theorem B12828941 : Blo 622298 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B999695 : Blo 622298 999695 := bstep (se 1 (by rfl) ⟨749771, by rfl⟩ : syracuseStep 999695 = 1499543) B1499543
theorem B2277665 : Blo 622298 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B3162401 : Blo 622298 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B934187 : Blo 622298 934187 := bstep (se 1 (by rfl) ⟨700640, by rfl⟩ : syracuseStep 934187 = 1401281) B1401281
theorem B934217 : Blo 622298 934217 := bstep (se 2 (by rfl) ⟨350331, by rfl⟩ : syracuseStep 934217 = 700663) B700663
theorem B1524055 : Blo 622298 1524055 := bstep (se 1 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 1524055 = 2286083) B2286083
theorem B11977105 : Blo 622298 11977105 := bstep (se 2 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 11977105 = 8982829) B8982829
theorem B2670995 : Blo 622298 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B639419 : Blo 622298 639419 := bstep (se 1 (by rfl) ⟨479564, by rfl⟩ : syracuseStep 639419 = 959129) B959129
theorem B934331 : Blo 622298 934331 := bstep (se 1 (by rfl) ⟨700748, by rfl⟩ : syracuseStep 934331 = 1401497) B1401497
theorem B999881 : Blo 622298 999881 := bstep (se 2 (by rfl) ⟨374955, by rfl⟩ : syracuseStep 999881 = 749911) B749911
theorem B934391 : Blo 622298 934391 := bstep (se 1 (by rfl) ⟨700793, by rfl⟩ : syracuseStep 934391 = 1401587) B1401587
theorem B934415 : Blo 622298 934415 := bstep (se 1 (by rfl) ⟨700811, by rfl⟩ : syracuseStep 934415 = 1401623) B1401623
theorem B2671147 : Blo 622298 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B934457 : Blo 622298 934457 := bstep (se 2 (by rfl) ⟨350421, by rfl⟩ : syracuseStep 934457 = 700843) B700843
theorem B934535 : Blo 622298 934535 := bstep (se 1 (by rfl) ⟨700901, by rfl⟩ : syracuseStep 934535 = 1401803) B1401803
theorem B934571 : Blo 622298 934571 := bstep (se 1 (by rfl) ⟨700928, by rfl⟩ : syracuseStep 934571 = 1401857) B1401857
theorem B934601 : Blo 622298 934601 := bstep (se 2 (by rfl) ⟨350475, by rfl⟩ : syracuseStep 934601 = 700951) B700951
theorem B2376449 : Blo 622298 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B934715 : Blo 622298 934715 := bstep (se 1 (by rfl) ⟨701036, by rfl⟩ : syracuseStep 934715 = 1402073) B1402073
theorem B934775 : Blo 622298 934775 := bstep (se 1 (by rfl) ⟨701081, by rfl⟩ : syracuseStep 934775 = 1402163) B1402163
theorem B934799 : Blo 622298 934799 := bstep (se 1 (by rfl) ⟨701099, by rfl⟩ : syracuseStep 934799 = 1402199) B1402199
theorem B934841 : Blo 622298 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B934919 : Blo 622298 934919 := bstep (se 1 (by rfl) ⟨701189, by rfl⟩ : syracuseStep 934919 = 1402379) B1402379
theorem B934955 : Blo 622298 934955 := bstep (se 1 (by rfl) ⟨701216, by rfl⟩ : syracuseStep 934955 = 1402433) B1402433
theorem B934985 : Blo 622298 934985 := bstep (se 2 (by rfl) ⟨350619, by rfl⟩ : syracuseStep 934985 = 701239) B701239
theorem B935099 : Blo 622298 935099 := bstep (se 1 (by rfl) ⟨701324, by rfl⟩ : syracuseStep 935099 = 1402649) B1402649
theorem B3163373 : Blo 622298 3163373 := bstep (se 3 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 3163373 = 1186265) B1186265
theorem B935159 : Blo 622298 935159 := bstep (se 1 (by rfl) ⟨701369, by rfl⟩ : syracuseStep 935159 = 1402739) B1402739
theorem B935183 : Blo 622298 935183 := bstep (se 1 (by rfl) ⟨701387, by rfl⟩ : syracuseStep 935183 = 1402775) B1402775
theorem B935225 : Blo 622298 935225 := bstep (se 2 (by rfl) ⟨350709, by rfl⟩ : syracuseStep 935225 = 701419) B701419
theorem B935303 : Blo 622298 935303 := bstep (se 1 (by rfl) ⟨701477, by rfl⟩ : syracuseStep 935303 = 1402955) B1402955
theorem B2999699 : Blo 622298 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B935339 : Blo 622298 935339 := bstep (se 1 (by rfl) ⟨701504, by rfl⟩ : syracuseStep 935339 = 1403009) B1403009
theorem B935369 : Blo 622298 935369 := bstep (se 2 (by rfl) ⟨350763, by rfl⟩ : syracuseStep 935369 = 701527) B701527
theorem B4736555 : Blo 622298 4736555 := bstep (se 1 (by rfl) ⟨3552416, by rfl⟩ : syracuseStep 4736555 = 7104833) B7104833
theorem B935483 : Blo 622298 935483 := bstep (se 1 (by rfl) ⟨701612, by rfl⟩ : syracuseStep 935483 = 1403225) B1403225
theorem B935543 : Blo 622298 935543 := bstep (se 1 (by rfl) ⟨701657, by rfl⟩ : syracuseStep 935543 = 1403315) B1403315
theorem B935567 : Blo 622298 935567 := bstep (se 1 (by rfl) ⟨701675, by rfl⟩ : syracuseStep 935567 = 1403351) B1403351
theorem B935609 : Blo 622298 935609 := bstep (se 2 (by rfl) ⟨350853, by rfl⟩ : syracuseStep 935609 = 701707) B701707
theorem B4572929 : Blo 622298 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B935687 : Blo 622298 935687 := bstep (se 1 (by rfl) ⟨701765, by rfl⟩ : syracuseStep 935687 = 1403531) B1403531
theorem B935723 : Blo 622298 935723 := bstep (se 1 (by rfl) ⟨701792, by rfl⟩ : syracuseStep 935723 = 1403585) B1403585
theorem B935753 : Blo 622298 935753 := bstep (se 2 (by rfl) ⟨350907, by rfl⟩ : syracuseStep 935753 = 701815) B701815
theorem B1001335 : Blo 622298 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B3000199 : Blo 622298 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B2377619 : Blo 622298 2377619 := bstep (se 1 (by rfl) ⟨1783214, by rfl⟩ : syracuseStep 2377619 = 3566429) B3566429
theorem B935867 : Blo 622298 935867 := bstep (se 1 (by rfl) ⟨701900, by rfl⟩ : syracuseStep 935867 = 1403801) B1403801
theorem B935927 : Blo 622298 935927 := bstep (se 1 (by rfl) ⟨701945, by rfl⟩ : syracuseStep 935927 = 1403891) B1403891
theorem B2672651 : Blo 622298 2672651 := bstep (se 1 (by rfl) ⟨2004488, by rfl⟩ : syracuseStep 2672651 = 4008977) B4008977
theorem B935951 : Blo 622298 935951 := bstep (se 1 (by rfl) ⟨701963, by rfl⟩ : syracuseStep 935951 = 1403927) B1403927
theorem B3164183 : Blo 622298 3164183 := bstep (se 1 (by rfl) ⟨2373137, by rfl⟩ : syracuseStep 3164183 = 4746275) B4746275
theorem B935993 : Blo 622298 935993 := bstep (se 2 (by rfl) ⟨350997, by rfl⟩ : syracuseStep 935993 = 701995) B701995
theorem B936071 : Blo 622298 936071 := bstep (se 1 (by rfl) ⟨702053, by rfl⟩ : syracuseStep 936071 = 1404107) B1404107
theorem B936107 : Blo 622298 936107 := bstep (se 1 (by rfl) ⟨702080, by rfl⟩ : syracuseStep 936107 = 1404161) B1404161
theorem B936137 : Blo 622298 936137 := bstep (se 2 (by rfl) ⟨351051, by rfl⟩ : syracuseStep 936137 = 702103) B702103
theorem B936251 : Blo 622298 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B936311 : Blo 622298 936311 := bstep (se 1 (by rfl) ⟨702233, by rfl⟩ : syracuseStep 936311 = 1404467) B1404467
theorem B936335 : Blo 622298 936335 := bstep (se 1 (by rfl) ⟨702251, by rfl⟩ : syracuseStep 936335 = 1404503) B1404503
theorem B936377 : Blo 622298 936377 := bstep (se 2 (by rfl) ⟨351141, by rfl⟩ : syracuseStep 936377 = 702283) B702283
theorem B936455 : Blo 622298 936455 := bstep (se 1 (by rfl) ⟨702341, by rfl⟩ : syracuseStep 936455 = 1404683) B1404683
theorem B936491 : Blo 622298 936491 := bstep (se 1 (by rfl) ⟨702368, by rfl⟩ : syracuseStep 936491 = 1404737) B1404737
theorem B4508227 : Blo 622298 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B936521 : Blo 622298 936521 := bstep (se 2 (by rfl) ⟨351195, by rfl⟩ : syracuseStep 936521 = 702391) B702391
theorem B1329799 : Blo 622298 1329799 := bstep (se 1 (by rfl) ⟨997349, by rfl⟩ : syracuseStep 1329799 = 1994699) B1994699
theorem B936635 : Blo 622298 936635 := bstep (se 1 (by rfl) ⟨702476, by rfl⟩ : syracuseStep 936635 = 1404953) B1404953
theorem B936695 : Blo 622298 936695 := bstep (se 1 (by rfl) ⟨702521, by rfl⟩ : syracuseStep 936695 = 1405043) B1405043
theorem B2247439 : Blo 622298 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B936719 : Blo 622298 936719 := bstep (se 1 (by rfl) ⟨702539, by rfl⟩ : syracuseStep 936719 = 1405079) B1405079
theorem B936761 : Blo 622298 936761 := bstep (se 2 (by rfl) ⟨351285, by rfl⟩ : syracuseStep 936761 = 702571) B702571
theorem B936839 : Blo 622298 936839 := bstep (se 1 (by rfl) ⟨702629, by rfl⟩ : syracuseStep 936839 = 1405259) B1405259
theorem B936875 : Blo 622298 936875 := bstep (se 1 (by rfl) ⟨702656, by rfl⟩ : syracuseStep 936875 = 1405313) B1405313
theorem B2673593 : Blo 622298 2673593 := bstep (se 2 (by rfl) ⟨1002597, by rfl⟩ : syracuseStep 2673593 = 2005195) B2005195
theorem B936905 : Blo 622298 936905 := bstep (se 2 (by rfl) ⟨351339, by rfl⟩ : syracuseStep 936905 = 702679) B702679
theorem B937019 : Blo 622298 937019 := bstep (se 1 (by rfl) ⟨702764, by rfl⟩ : syracuseStep 937019 = 1405529) B1405529
theorem B937079 : Blo 622298 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B937103 : Blo 622298 937103 := bstep (se 1 (by rfl) ⟨702827, by rfl⟩ : syracuseStep 937103 = 1405655) B1405655
theorem B937145 : Blo 622298 937145 := bstep (se 2 (by rfl) ⟨351429, by rfl⟩ : syracuseStep 937145 = 702859) B702859
theorem B937223 : Blo 622298 937223 := bstep (se 1 (by rfl) ⟨702917, by rfl⟩ : syracuseStep 937223 = 1405835) B1405835
theorem B937259 : Blo 622298 937259 := bstep (se 1 (by rfl) ⟨702944, by rfl⟩ : syracuseStep 937259 = 1405889) B1405889
theorem B937289 : Blo 622298 937289 := bstep (se 2 (by rfl) ⟨351483, by rfl⟩ : syracuseStep 937289 = 702967) B702967
theorem B1002937 : Blo 622298 1002937 := bstep (se 2 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 1002937 = 752203) B752203
theorem B937403 : Blo 622298 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B937463 : Blo 622298 937463 := bstep (se 1 (by rfl) ⟨703097, by rfl⟩ : syracuseStep 937463 = 1406195) B1406195
theorem B937487 : Blo 622298 937487 := bstep (se 1 (by rfl) ⟨703115, by rfl⟩ : syracuseStep 937487 = 1406231) B1406231
theorem B937529 : Blo 622298 937529 := bstep (se 2 (by rfl) ⟨351573, by rfl⟩ : syracuseStep 937529 = 703147) B703147
theorem B1265287 : Blo 622298 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B937607 : Blo 622298 937607 := bstep (se 1 (by rfl) ⟨703205, by rfl⟩ : syracuseStep 937607 = 1406411) B1406411
theorem B937643 : Blo 622298 937643 := bstep (se 1 (by rfl) ⟨703232, by rfl⟩ : syracuseStep 937643 = 1406465) B1406465
theorem B1003193 : Blo 622298 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B937673 : Blo 622298 937673 := bstep (se 2 (by rfl) ⟨351627, by rfl⟩ : syracuseStep 937673 = 703255) B703255
theorem B1330987 : Blo 622298 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B937787 : Blo 622298 937787 := bstep (se 1 (by rfl) ⟨703340, by rfl⟩ : syracuseStep 937787 = 1406681) B1406681
theorem B937847 : Blo 622298 937847 := bstep (se 1 (by rfl) ⟨703385, by rfl⟩ : syracuseStep 937847 = 1406771) B1406771
theorem B937871 : Blo 622298 937871 := bstep (se 1 (by rfl) ⟨703403, by rfl⟩ : syracuseStep 937871 = 1406807) B1406807
theorem B937913 : Blo 622298 937913 := bstep (se 2 (by rfl) ⟨351717, by rfl⟩ : syracuseStep 937913 = 703435) B703435
theorem B937991 : Blo 622298 937991 := bstep (se 1 (by rfl) ⟨703493, by rfl⟩ : syracuseStep 937991 = 1406987) B1406987
theorem B938027 : Blo 622298 938027 := bstep (se 1 (by rfl) ⟨703520, by rfl⟩ : syracuseStep 938027 = 1407041) B1407041
theorem B938057 : Blo 622298 938057 := bstep (se 2 (by rfl) ⟨351771, by rfl⟩ : syracuseStep 938057 = 703543) B703543
theorem B6475949 : Blo 622298 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B6770861 : Blo 622298 6770861 := bstep (se 3 (by rfl) ⟨1269536, by rfl⟩ : syracuseStep 6770861 = 2539073) B2539073
theorem B938171 : Blo 622298 938171 := bstep (se 1 (by rfl) ⟨703628, by rfl⟩ : syracuseStep 938171 = 1407257) B1407257
theorem B938231 : Blo 622298 938231 := bstep (se 1 (by rfl) ⟨703673, by rfl⟩ : syracuseStep 938231 = 1407347) B1407347
theorem B938255 : Blo 622298 938255 := bstep (se 1 (by rfl) ⟨703691, by rfl⟩ : syracuseStep 938255 = 1407383) B1407383
theorem B938297 : Blo 622298 938297 := bstep (se 2 (by rfl) ⟨351861, by rfl⟩ : syracuseStep 938297 = 703723) B703723
theorem B938375 : Blo 622298 938375 := bstep (se 1 (by rfl) ⟨703781, by rfl⟩ : syracuseStep 938375 = 1407563) B1407563
theorem B938411 : Blo 622298 938411 := bstep (se 1 (by rfl) ⟨703808, by rfl⟩ : syracuseStep 938411 = 1407617) B1407617
theorem B938441 : Blo 622298 938441 := bstep (se 2 (by rfl) ⟨351915, by rfl⟩ : syracuseStep 938441 = 703831) B703831
theorem B3559889 : Blo 622298 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B938555 : Blo 622298 938555 := bstep (se 1 (by rfl) ⟨703916, by rfl⟩ : syracuseStep 938555 = 1407833) B1407833
theorem B938615 : Blo 622298 938615 := bstep (se 1 (by rfl) ⟨703961, by rfl⟩ : syracuseStep 938615 = 1407923) B1407923
theorem B938639 : Blo 622298 938639 := bstep (se 1 (by rfl) ⟨703979, by rfl⟩ : syracuseStep 938639 = 1407959) B1407959
theorem B938681 : Blo 622298 938681 := bstep (se 2 (by rfl) ⟨352005, by rfl⟩ : syracuseStep 938681 = 704011) B704011
theorem B938759 : Blo 622298 938759 := bstep (se 1 (by rfl) ⟨704069, by rfl⟩ : syracuseStep 938759 = 1408139) B1408139
theorem B4051727 : Blo 622298 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B938795 : Blo 622298 938795 := bstep (se 1 (by rfl) ⟨704096, by rfl⟩ : syracuseStep 938795 = 1408193) B1408193
theorem B938825 : Blo 622298 938825 := bstep (se 2 (by rfl) ⟨352059, by rfl⟩ : syracuseStep 938825 = 704119) B704119
theorem B3560345 : Blo 622298 3560345 := bstep (se 2 (by rfl) ⟨1335129, by rfl⟩ : syracuseStep 3560345 = 2670259) B2670259
theorem B938939 : Blo 622298 938939 := bstep (se 1 (by rfl) ⟨704204, by rfl⟩ : syracuseStep 938939 = 1408409) B1408409
theorem B938999 : Blo 622298 938999 := bstep (se 1 (by rfl) ⟨704249, by rfl⟩ : syracuseStep 938999 = 1408499) B1408499
theorem B939023 : Blo 622298 939023 := bstep (se 1 (by rfl) ⟨704267, by rfl⟩ : syracuseStep 939023 = 1408535) B1408535
theorem B3167261 : Blo 622298 3167261 := bstep (se 3 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 3167261 = 1187723) B1187723
theorem B939065 : Blo 622298 939065 := bstep (se 2 (by rfl) ⟨352149, by rfl⟩ : syracuseStep 939065 = 704299) B704299
theorem B939143 : Blo 622298 939143 := bstep (se 1 (by rfl) ⟨704357, by rfl⟩ : syracuseStep 939143 = 1408715) B1408715
theorem B939179 : Blo 622298 939179 := bstep (se 1 (by rfl) ⟨704384, by rfl⟩ : syracuseStep 939179 = 1408769) B1408769
theorem B939209 : Blo 622298 939209 := bstep (se 2 (by rfl) ⟨352203, by rfl⟩ : syracuseStep 939209 = 704407) B704407
theorem B939323 : Blo 622298 939323 := bstep (se 1 (by rfl) ⟨704492, by rfl⟩ : syracuseStep 939323 = 1408985) B1408985
theorem B939383 : Blo 622298 939383 := bstep (se 1 (by rfl) ⟨704537, by rfl⟩ : syracuseStep 939383 = 1409075) B1409075
theorem B939407 : Blo 622298 939407 := bstep (se 1 (by rfl) ⟨704555, by rfl⟩ : syracuseStep 939407 = 1409111) B1409111
theorem B26990009 : Blo 622298 26990009 := bstep (se 2 (by rfl) ⟨10121253, by rfl⟩ : syracuseStep 26990009 = 20242507) B20242507
theorem B3167747 : Blo 622298 3167747 := bstep (se 1 (by rfl) ⟨2375810, by rfl⟩ : syracuseStep 3167747 = 4751621) B4751621
theorem B841487 : Blo 622298 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B1267591 : Blo 622298 1267591 := bstep (se 1 (by rfl) ⟨950693, by rfl⟩ : syracuseStep 1267591 = 1901387) B1901387
theorem B2021267 : Blo 622298 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B184440907 : Blo 622298 184440907 := bstep (se 1 (by rfl) ⟨138330680, by rfl⟩ : syracuseStep 184440907 = 276661361) B276661361
theorem B1136825 : Blo 622298 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B842119 : Blo 622298 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B2251705 : Blo 622298 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B3169367 : Blo 622298 3169367 := bstep (se 1 (by rfl) ⟨2377025, by rfl⟩ : syracuseStep 3169367 = 4754051) B4754051
theorem B1400183 : Blo 622298 1400183 := bstep (se 1 (by rfl) ⟨1050137, by rfl⟩ : syracuseStep 1400183 = 2100275) B2100275
theorem B3005849 : Blo 622298 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B7101917 : Blo 622298 7101917 := bstep (se 3 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 7101917 = 2663219) B2663219
theorem B712199 : Blo 622298 712199 := bstep (se 1 (by rfl) ⟨534149, by rfl⟩ : syracuseStep 712199 = 1068299) B1068299
theorem B1400363 : Blo 622298 1400363 := bstep (se 1 (by rfl) ⟨1050272, by rfl⟩ : syracuseStep 1400363 = 2100545) B2100545
theorem B3169853 : Blo 622298 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B3202679 : Blo 622298 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B4120183 : Blo 622298 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B1400723 : Blo 622298 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B1400777 : Blo 622298 1400777 := bstep (se 2 (by rfl) ⟨525291, by rfl⟩ : syracuseStep 1400777 = 1050583) B1050583
theorem B3792919 : Blo 622298 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B1401479 : Blo 622298 1401479 := bstep (se 1 (by rfl) ⟨1051109, by rfl⟩ : syracuseStep 1401479 = 2102219) B2102219
theorem B1401659 : Blo 622298 1401659 := bstep (se 1 (by rfl) ⟨1051244, by rfl⟩ : syracuseStep 1401659 = 2102489) B2102489
theorem B1401785 : Blo 622298 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B1402127 : Blo 622298 1402127 := bstep (se 1 (by rfl) ⟨1051595, by rfl⟩ : syracuseStep 1402127 = 2103191) B2103191
theorem B1336591 : Blo 622298 1336591 := bstep (se 1 (by rfl) ⟨1002443, by rfl⟩ : syracuseStep 1336591 = 2004887) B2004887
theorem B1402145 : Blo 622298 1402145 := bstep (se 2 (by rfl) ⟨525804, by rfl⟩ : syracuseStep 1402145 = 1051609) B1051609
theorem B16442657 : Blo 622298 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B1402487 : Blo 622298 1402487 := bstep (se 1 (by rfl) ⟨1051865, by rfl⟩ : syracuseStep 1402487 = 2103731) B2103731
theorem B1402667 : Blo 622298 1402667 := bstep (se 1 (by rfl) ⟨1052000, by rfl⟩ : syracuseStep 1402667 = 2104001) B2104001
theorem B1894259 : Blo 622298 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B3073945 : Blo 622298 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B4745303 : Blo 622298 4745303 := bstep (se 1 (by rfl) ⟨3558977, by rfl⟩ : syracuseStep 4745303 = 7117955) B7117955
theorem B1403027 : Blo 622298 1403027 := bstep (se 1 (by rfl) ⟨1052270, by rfl⟩ : syracuseStep 1403027 = 2104541) B2104541
theorem B1403081 : Blo 622298 1403081 := bstep (se 2 (by rfl) ⟨526155, by rfl⟩ : syracuseStep 1403081 = 1052311) B1052311
theorem B5990861 : Blo 622298 5990861 := bstep (se 3 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 5990861 = 2246573) B2246573
theorem B5073475 : Blo 622298 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B5991013 : Blo 622298 5991013 := bstep (se 4 (by rfl) ⟨561657, by rfl⟩ : syracuseStep 5991013 = 1123315) B1123315
theorem B5073601 : Blo 622298 5073601 := bstep (se 2 (by rfl) ⟨1902600, by rfl⟩ : syracuseStep 5073601 = 3805201) B3805201
theorem B1403783 : Blo 622298 1403783 := bstep (se 1 (by rfl) ⟨1052837, by rfl⟩ : syracuseStep 1403783 = 2105675) B2105675
theorem B11725829 : Blo 622298 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B8219659 : Blo 622298 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B1403963 : Blo 622298 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B2255959 : Blo 622298 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B1404089 : Blo 622298 1404089 := bstep (se 2 (by rfl) ⟨526533, by rfl⟩ : syracuseStep 1404089 = 1053067) B1053067
theorem B3599597 : Blo 622298 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B1895681 : Blo 622298 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B1404431 : Blo 622298 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B1404449 : Blo 622298 1404449 := bstep (se 2 (by rfl) ⟨526668, by rfl⟩ : syracuseStep 1404449 = 1053337) B1053337
theorem B28897073 : Blo 622298 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B1404791 : Blo 622298 1404791 := bstep (se 1 (by rfl) ⟨1053593, by rfl⟩ : syracuseStep 1404791 = 2107187) B2107187
theorem B1404971 : Blo 622298 1404971 := bstep (se 1 (by rfl) ⟨1053728, by rfl⟩ : syracuseStep 1404971 = 2107457) B2107457
theorem B1896851 : Blo 622298 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B1405331 : Blo 622298 1405331 := bstep (se 1 (by rfl) ⟨1053998, by rfl⟩ : syracuseStep 1405331 = 2107997) B2107997
theorem B1405385 : Blo 622298 1405385 := bstep (se 2 (by rfl) ⟨527019, by rfl⟩ : syracuseStep 1405385 = 1054039) B1054039
theorem B8516161 : Blo 622298 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B946873 : Blo 622298 946873 := bstep (se 2 (by rfl) ⟨355077, by rfl⟩ : syracuseStep 946873 = 710155) B710155
theorem B1504289 : Blo 622298 1504289 := bstep (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) B1128217
theorem B1406087 : Blo 622298 1406087 := bstep (se 1 (by rfl) ⟨1054565, by rfl⟩ : syracuseStep 1406087 = 2109131) B2109131
theorem B1406267 : Blo 622298 1406267 := bstep (se 1 (by rfl) ⟨1054700, by rfl⟩ : syracuseStep 1406267 = 2109401) B2109401
theorem B1602931 : Blo 622298 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B1406393 : Blo 622298 1406393 := bstep (se 2 (by rfl) ⟨527397, by rfl⟩ : syracuseStep 1406393 = 1054795) B1054795
theorem B3372587 : Blo 622298 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B5076523 : Blo 622298 5076523 := bstep (se 1 (by rfl) ⟨3807392, by rfl⟩ : syracuseStep 5076523 = 7614785) B7614785
theorem B1406735 : Blo 622298 1406735 := bstep (se 1 (by rfl) ⟨1055051, by rfl⟩ : syracuseStep 1406735 = 2110103) B2110103
theorem B1406753 : Blo 622298 1406753 := bstep (se 2 (by rfl) ⟨527532, by rfl⟩ : syracuseStep 1406753 = 1055065) B1055065
theorem B1996697 : Blo 622298 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B1407095 : Blo 622298 1407095 := bstep (se 1 (by rfl) ⟨1055321, by rfl⟩ : syracuseStep 1407095 = 2110643) B2110643
theorem B1800377 : Blo 622298 1800377 := bstep (se 2 (by rfl) ⟨675141, by rfl⟩ : syracuseStep 1800377 = 1350283) B1350283
theorem B1407275 : Blo 622298 1407275 := bstep (se 1 (by rfl) ⟨1055456, by rfl⟩ : syracuseStep 1407275 = 2110913) B2110913
theorem B14383507 : Blo 622298 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B3373579 : Blo 622298 3373579 := bstep (se 1 (by rfl) ⟨2530184, by rfl⟩ : syracuseStep 3373579 = 5060369) B5060369
theorem B1407635 : Blo 622298 1407635 := bstep (se 1 (by rfl) ⟨1055726, by rfl⟩ : syracuseStep 1407635 = 2111453) B2111453
theorem B1407689 : Blo 622298 1407689 := bstep (se 2 (by rfl) ⟨527883, by rfl⟩ : syracuseStep 1407689 = 1055767) B1055767
theorem B5340107 : Blo 622298 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B1408391 : Blo 622298 1408391 := bstep (se 1 (by rfl) ⟨1056293, by rfl⟩ : syracuseStep 1408391 = 2112587) B2112587
theorem B1408571 : Blo 622298 1408571 := bstep (se 1 (by rfl) ⟨1056428, by rfl⟩ : syracuseStep 1408571 = 2112857) B2112857
theorem B1900217 : Blo 622298 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1408697 : Blo 622298 1408697 := bstep (se 2 (by rfl) ⟨528261, by rfl⟩ : syracuseStep 1408697 = 1056523) B1056523
theorem B622343 : Blo 622298 622343 := bstep (se 1 (by rfl) ⟨466757, by rfl⟩ : syracuseStep 622343 = 933515) B933515
theorem B622351 : Blo 622298 622351 := bstep (se 1 (by rfl) ⟨466763, by rfl⟩ : syracuseStep 622351 = 933527) B933527
theorem B622395 : Blo 622298 622395 := bstep (se 1 (by rfl) ⟨466796, by rfl⟩ : syracuseStep 622395 = 933593) B933593
theorem B3374963 : Blo 622298 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B622471 : Blo 622298 622471 := bstep (se 1 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 622471 = 933707) B933707
theorem B622479 : Blo 622298 622479 := bstep (se 1 (by rfl) ⟨466859, by rfl⟩ : syracuseStep 622479 = 933719) B933719
theorem B6422435 : Blo 622298 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B622523 : Blo 622298 622523 := bstep (se 1 (by rfl) ⟨466892, by rfl⟩ : syracuseStep 622523 = 933785) B933785
theorem B622631 : Blo 622298 622631 := bstep (se 1 (by rfl) ⟨466973, by rfl⟩ : syracuseStep 622631 = 933947) B933947
theorem B622671 : Blo 622298 622671 := bstep (se 1 (by rfl) ⟨467003, by rfl⟩ : syracuseStep 622671 = 934007) B934007
theorem B622687 : Blo 622298 622687 := bstep (se 1 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 622687 = 934031) B934031
theorem B622715 : Blo 622298 622715 := bstep (se 1 (by rfl) ⟨467036, by rfl⟩ : syracuseStep 622715 = 934073) B934073
theorem B622767 : Blo 622298 622767 := bstep (se 1 (by rfl) ⟨467075, by rfl⟩ : syracuseStep 622767 = 934151) B934151
theorem B8552627 : Blo 622298 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B622791 : Blo 622298 622791 := bstep (se 1 (by rfl) ⟨467093, by rfl⟩ : syracuseStep 622791 = 934187) B934187
theorem B622811 : Blo 622298 622811 := bstep (se 1 (by rfl) ⟨467108, by rfl⟩ : syracuseStep 622811 = 934217) B934217
theorem B622887 : Blo 622298 622887 := bstep (se 1 (by rfl) ⟨467165, by rfl⟩ : syracuseStep 622887 = 934331) B934331
theorem B622927 : Blo 622298 622927 := bstep (se 1 (by rfl) ⟨467195, by rfl⟩ : syracuseStep 622927 = 934391) B934391
theorem B622943 : Blo 622298 622943 := bstep (se 1 (by rfl) ⟨467207, by rfl⟩ : syracuseStep 622943 = 934415) B934415
theorem B622971 : Blo 622298 622971 := bstep (se 1 (by rfl) ⟨467228, by rfl⟩ : syracuseStep 622971 = 934457) B934457
theorem B623023 : Blo 622298 623023 := bstep (se 1 (by rfl) ⟨467267, by rfl⟩ : syracuseStep 623023 = 934535) B934535
theorem B623047 : Blo 622298 623047 := bstep (se 1 (by rfl) ⟨467285, by rfl⟩ : syracuseStep 623047 = 934571) B934571
theorem B2032073 : Blo 622298 2032073 := bstep (se 2 (by rfl) ⟨762027, by rfl⟩ : syracuseStep 2032073 = 1524055) B1524055
theorem B623067 : Blo 622298 623067 := bstep (se 1 (by rfl) ⟨467300, by rfl⟩ : syracuseStep 623067 = 934601) B934601
theorem B623143 : Blo 622298 623143 := bstep (se 1 (by rfl) ⟨467357, by rfl⟩ : syracuseStep 623143 = 934715) B934715
theorem B623183 : Blo 622298 623183 := bstep (se 1 (by rfl) ⟨467387, by rfl⟩ : syracuseStep 623183 = 934775) B934775
theorem B623199 : Blo 622298 623199 := bstep (se 1 (by rfl) ⟨467399, by rfl⟩ : syracuseStep 623199 = 934799) B934799
theorem B623227 : Blo 622298 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B623279 : Blo 622298 623279 := bstep (se 1 (by rfl) ⟨467459, by rfl⟩ : syracuseStep 623279 = 934919) B934919
theorem B623303 : Blo 622298 623303 := bstep (se 1 (by rfl) ⟨467477, by rfl⟩ : syracuseStep 623303 = 934955) B934955
theorem B623323 : Blo 622298 623323 := bstep (se 1 (by rfl) ⟨467492, by rfl⟩ : syracuseStep 623323 = 934985) B934985
theorem B623399 : Blo 622298 623399 := bstep (se 1 (by rfl) ⟨467549, by rfl⟩ : syracuseStep 623399 = 935099) B935099
theorem B623439 : Blo 622298 623439 := bstep (se 1 (by rfl) ⟨467579, by rfl⟩ : syracuseStep 623439 = 935159) B935159
theorem B623455 : Blo 622298 623455 := bstep (se 1 (by rfl) ⟨467591, by rfl⟩ : syracuseStep 623455 = 935183) B935183
theorem B623483 : Blo 622298 623483 := bstep (se 1 (by rfl) ⟨467612, by rfl⟩ : syracuseStep 623483 = 935225) B935225
theorem B623535 : Blo 622298 623535 := bstep (se 1 (by rfl) ⟨467651, by rfl⟩ : syracuseStep 623535 = 935303) B935303
theorem B1999799 : Blo 622298 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B623559 : Blo 622298 623559 := bstep (se 1 (by rfl) ⟨467669, by rfl⟩ : syracuseStep 623559 = 935339) B935339
theorem B623579 : Blo 622298 623579 := bstep (se 1 (by rfl) ⟨467684, by rfl⟩ : syracuseStep 623579 = 935369) B935369
theorem B623655 : Blo 622298 623655 := bstep (se 1 (by rfl) ⟨467741, by rfl⟩ : syracuseStep 623655 = 935483) B935483
theorem B623695 : Blo 622298 623695 := bstep (se 1 (by rfl) ⟨467771, by rfl⟩ : syracuseStep 623695 = 935543) B935543
theorem B623711 : Blo 622298 623711 := bstep (se 1 (by rfl) ⟨467783, by rfl⟩ : syracuseStep 623711 = 935567) B935567
theorem B623739 : Blo 622298 623739 := bstep (se 1 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 623739 = 935609) B935609
theorem B19268761 : Blo 622298 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B3048619 : Blo 622298 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B623791 : Blo 622298 623791 := bstep (se 1 (by rfl) ⟨467843, by rfl⟩ : syracuseStep 623791 = 935687) B935687
theorem B623815 : Blo 622298 623815 := bstep (se 1 (by rfl) ⟨467861, by rfl⟩ : syracuseStep 623815 = 935723) B935723
theorem B623835 : Blo 622298 623835 := bstep (se 1 (by rfl) ⟨467876, by rfl⟩ : syracuseStep 623835 = 935753) B935753
theorem B623911 : Blo 622298 623911 := bstep (se 1 (by rfl) ⟨467933, by rfl⟩ : syracuseStep 623911 = 935867) B935867
theorem B623951 : Blo 622298 623951 := bstep (se 1 (by rfl) ⟨467963, by rfl⟩ : syracuseStep 623951 = 935927) B935927
theorem B623967 : Blo 622298 623967 := bstep (se 1 (by rfl) ⟨467975, by rfl⟩ : syracuseStep 623967 = 935951) B935951
theorem B623995 : Blo 622298 623995 := bstep (se 1 (by rfl) ⟨467996, by rfl⟩ : syracuseStep 623995 = 935993) B935993
theorem B624047 : Blo 622298 624047 := bstep (se 1 (by rfl) ⟨468035, by rfl⟩ : syracuseStep 624047 = 936071) B936071
theorem B624071 : Blo 622298 624071 := bstep (se 1 (by rfl) ⟨468053, by rfl⟩ : syracuseStep 624071 = 936107) B936107
theorem B624091 : Blo 622298 624091 := bstep (se 1 (by rfl) ⟨468068, by rfl⟩ : syracuseStep 624091 = 936137) B936137
theorem B5703131 : Blo 622298 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B1050151 : Blo 622298 1050151 := bstep (se 1 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 1050151 = 1575227) B1575227
theorem B624167 : Blo 622298 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B624207 : Blo 622298 624207 := bstep (se 1 (by rfl) ⟨468155, by rfl⟩ : syracuseStep 624207 = 936311) B936311
theorem B624223 : Blo 622298 624223 := bstep (se 1 (by rfl) ⟨468167, by rfl⟩ : syracuseStep 624223 = 936335) B936335
theorem B624251 : Blo 622298 624251 := bstep (se 1 (by rfl) ⟨468188, by rfl⟩ : syracuseStep 624251 = 936377) B936377
theorem B3212939 : Blo 622298 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B624303 : Blo 622298 624303 := bstep (se 1 (by rfl) ⟨468227, by rfl⟩ : syracuseStep 624303 = 936455) B936455
theorem B624327 : Blo 622298 624327 := bstep (se 1 (by rfl) ⟨468245, by rfl⟩ : syracuseStep 624327 = 936491) B936491
theorem B624347 : Blo 622298 624347 := bstep (se 1 (by rfl) ⟨468260, by rfl⟩ : syracuseStep 624347 = 936521) B936521
theorem B624423 : Blo 622298 624423 := bstep (se 1 (by rfl) ⟨468317, by rfl⟩ : syracuseStep 624423 = 936635) B936635
theorem B624463 : Blo 622298 624463 := bstep (se 1 (by rfl) ⟨468347, by rfl⟩ : syracuseStep 624463 = 936695) B936695
theorem B624479 : Blo 622298 624479 := bstep (se 1 (by rfl) ⟨468359, by rfl⟩ : syracuseStep 624479 = 936719) B936719
theorem B1050475 : Blo 622298 1050475 := bstep (se 1 (by rfl) ⟨787856, by rfl⟩ : syracuseStep 1050475 = 1575713) B1575713
theorem B624507 : Blo 622298 624507 := bstep (se 1 (by rfl) ⟨468380, by rfl⟩ : syracuseStep 624507 = 936761) B936761
theorem B624559 : Blo 622298 624559 := bstep (se 1 (by rfl) ⟨468419, by rfl⟩ : syracuseStep 624559 = 936839) B936839
theorem B624583 : Blo 622298 624583 := bstep (se 1 (by rfl) ⟨468437, by rfl⟩ : syracuseStep 624583 = 936875) B936875
theorem B624603 : Blo 622298 624603 := bstep (se 1 (by rfl) ⟨468452, by rfl⟩ : syracuseStep 624603 = 936905) B936905
theorem B4491301 : Blo 622298 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B624679 : Blo 622298 624679 := bstep (se 1 (by rfl) ⟨468509, by rfl⟩ : syracuseStep 624679 = 937019) B937019
theorem B624719 : Blo 622298 624719 := bstep (se 1 (by rfl) ⟨468539, by rfl⟩ : syracuseStep 624719 = 937079) B937079
theorem B624735 : Blo 622298 624735 := bstep (se 1 (by rfl) ⟨468551, by rfl⟩ : syracuseStep 624735 = 937103) B937103
theorem B624763 : Blo 622298 624763 := bstep (se 1 (by rfl) ⟨468572, by rfl⟩ : syracuseStep 624763 = 937145) B937145
theorem B4753565 : Blo 622298 4753565 := bstep (se 3 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 4753565 = 1782587) B1782587
theorem B624815 : Blo 622298 624815 := bstep (se 1 (by rfl) ⟨468611, by rfl⟩ : syracuseStep 624815 = 937223) B937223
theorem B624839 : Blo 622298 624839 := bstep (se 1 (by rfl) ⟨468629, by rfl⟩ : syracuseStep 624839 = 937259) B937259
theorem B624859 : Blo 622298 624859 := bstep (se 1 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 624859 = 937289) B937289
theorem B1181945 : Blo 622298 1181945 := bstep (se 2 (by rfl) ⟨443229, by rfl⟩ : syracuseStep 1181945 = 886459) B886459
theorem B624935 : Blo 622298 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B624975 : Blo 622298 624975 := bstep (se 1 (by rfl) ⟨468731, by rfl⟩ : syracuseStep 624975 = 937463) B937463
theorem B624991 : Blo 622298 624991 := bstep (se 1 (by rfl) ⟨468743, by rfl⟩ : syracuseStep 624991 = 937487) B937487
theorem B625019 : Blo 622298 625019 := bstep (se 1 (by rfl) ⟨468764, by rfl⟩ : syracuseStep 625019 = 937529) B937529
theorem B1182127 : Blo 622298 1182127 := bstep (se 1 (by rfl) ⟨886595, by rfl⟩ : syracuseStep 1182127 = 1773191) B1773191
theorem B625071 : Blo 622298 625071 := bstep (se 1 (by rfl) ⟨468803, by rfl⟩ : syracuseStep 625071 = 937607) B937607
theorem B625095 : Blo 622298 625095 := bstep (se 1 (by rfl) ⟨468821, by rfl⟩ : syracuseStep 625095 = 937643) B937643
theorem B625115 : Blo 622298 625115 := bstep (se 1 (by rfl) ⟨468836, by rfl⟩ : syracuseStep 625115 = 937673) B937673
theorem B4000265 : Blo 622298 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B4098593 : Blo 622298 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B789031 : Blo 622298 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B625191 : Blo 622298 625191 := bstep (se 1 (by rfl) ⟨468893, by rfl⟩ : syracuseStep 625191 = 937787) B937787
theorem B625231 : Blo 622298 625231 := bstep (se 1 (by rfl) ⟨468923, by rfl⟩ : syracuseStep 625231 = 937847) B937847
theorem B625247 : Blo 622298 625247 := bstep (se 1 (by rfl) ⟨468935, by rfl⟩ : syracuseStep 625247 = 937871) B937871
theorem B1575521 : Blo 622298 1575521 := bstep (se 2 (by rfl) ⟨590820, by rfl⟩ : syracuseStep 1575521 = 1181641) B1181641
theorem B625275 : Blo 622298 625275 := bstep (se 1 (by rfl) ⟨468956, by rfl⟩ : syracuseStep 625275 = 937913) B937913
theorem B625327 : Blo 622298 625327 := bstep (se 1 (by rfl) ⟨468995, by rfl⟩ : syracuseStep 625327 = 937991) B937991
theorem B625351 : Blo 622298 625351 := bstep (se 1 (by rfl) ⟨469013, by rfl⟩ : syracuseStep 625351 = 938027) B938027
theorem B625371 : Blo 622298 625371 := bstep (se 1 (by rfl) ⟨469028, by rfl⟩ : syracuseStep 625371 = 938057) B938057
theorem B625447 : Blo 622298 625447 := bstep (se 1 (by rfl) ⟨469085, by rfl⟩ : syracuseStep 625447 = 938171) B938171
theorem B625487 : Blo 622298 625487 := bstep (se 1 (by rfl) ⟨469115, by rfl⟩ : syracuseStep 625487 = 938231) B938231
theorem B625503 : Blo 622298 625503 := bstep (se 1 (by rfl) ⟨469127, by rfl⟩ : syracuseStep 625503 = 938255) B938255
theorem B789355 : Blo 622298 789355 := bstep (se 1 (by rfl) ⟨592016, by rfl⟩ : syracuseStep 789355 = 1184033) B1184033
theorem B625531 : Blo 622298 625531 := bstep (se 1 (by rfl) ⟨469148, by rfl⟩ : syracuseStep 625531 = 938297) B938297
theorem B1051535 : Blo 622298 1051535 := bstep (se 1 (by rfl) ⟨788651, by rfl⟩ : syracuseStep 1051535 = 1577303) B1577303
theorem B625583 : Blo 622298 625583 := bstep (se 1 (by rfl) ⟨469187, by rfl⟩ : syracuseStep 625583 = 938375) B938375
theorem B625607 : Blo 622298 625607 := bstep (se 1 (by rfl) ⟨469205, by rfl⟩ : syracuseStep 625607 = 938411) B938411
theorem B625627 : Blo 622298 625627 := bstep (se 1 (by rfl) ⟨469220, by rfl⟩ : syracuseStep 625627 = 938441) B938441
theorem B45419525 : Blo 622298 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B625703 : Blo 622298 625703 := bstep (se 1 (by rfl) ⟨469277, by rfl⟩ : syracuseStep 625703 = 938555) B938555
theorem B789583 : Blo 622298 789583 := bstep (se 1 (by rfl) ⟨592187, by rfl⟩ : syracuseStep 789583 = 1184375) B1184375
theorem B625743 : Blo 622298 625743 := bstep (se 1 (by rfl) ⟨469307, by rfl⟩ : syracuseStep 625743 = 938615) B938615
theorem B625759 : Blo 622298 625759 := bstep (se 1 (by rfl) ⟨469319, by rfl⟩ : syracuseStep 625759 = 938639) B938639
theorem B1051771 : Blo 622298 1051771 := bstep (se 1 (by rfl) ⟨788828, by rfl⟩ : syracuseStep 1051771 = 1577657) B1577657
theorem B625787 : Blo 622298 625787 := bstep (se 1 (by rfl) ⟨469340, by rfl⟩ : syracuseStep 625787 = 938681) B938681
theorem B625839 : Blo 622298 625839 := bstep (se 1 (by rfl) ⟨469379, by rfl⟩ : syracuseStep 625839 = 938759) B938759
theorem B5049539 : Blo 622298 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B625863 : Blo 622298 625863 := bstep (se 1 (by rfl) ⟨469397, by rfl⟩ : syracuseStep 625863 = 938795) B938795
theorem B625883 : Blo 622298 625883 := bstep (se 1 (by rfl) ⟨469412, by rfl⟩ : syracuseStep 625883 = 938825) B938825
theorem B2100491 : Blo 622298 2100491 := bstep (se 1 (by rfl) ⟨1575368, by rfl⟩ : syracuseStep 2100491 = 3150737) B3150737
theorem B625959 : Blo 622298 625959 := bstep (se 1 (by rfl) ⟨469469, by rfl⟩ : syracuseStep 625959 = 938939) B938939
theorem B625999 : Blo 622298 625999 := bstep (se 1 (by rfl) ⟨469499, by rfl⟩ : syracuseStep 625999 = 938999) B938999
theorem B626015 : Blo 622298 626015 := bstep (se 1 (by rfl) ⟨469511, by rfl⟩ : syracuseStep 626015 = 939023) B939023
theorem B626043 : Blo 622298 626043 := bstep (se 1 (by rfl) ⟨469532, by rfl⟩ : syracuseStep 626043 = 939065) B939065
theorem B626095 : Blo 622298 626095 := bstep (se 1 (by rfl) ⟨469571, by rfl⟩ : syracuseStep 626095 = 939143) B939143
theorem B626119 : Blo 622298 626119 := bstep (se 1 (by rfl) ⟨469589, by rfl⟩ : syracuseStep 626119 = 939179) B939179
theorem B1773019 : Blo 622298 1773019 := bstep (se 1 (by rfl) ⟨1329764, by rfl⟩ : syracuseStep 1773019 = 2659529) B2659529
theorem B626139 : Blo 622298 626139 := bstep (se 1 (by rfl) ⟨469604, by rfl⟩ : syracuseStep 626139 = 939209) B939209
theorem B1773065 : Blo 622298 1773065 := bstep (se 2 (by rfl) ⟨664899, by rfl⟩ : syracuseStep 1773065 = 1329799) B1329799
theorem B2100761 : Blo 622298 2100761 := bstep (se 2 (by rfl) ⟨787785, by rfl⟩ : syracuseStep 2100761 = 1575571) B1575571
theorem B626215 : Blo 622298 626215 := bstep (se 1 (by rfl) ⟨469661, by rfl⟩ : syracuseStep 626215 = 939323) B939323
theorem B626255 : Blo 622298 626255 := bstep (se 1 (by rfl) ⟨469691, by rfl⟩ : syracuseStep 626255 = 939383) B939383
theorem B626271 : Blo 622298 626271 := bstep (se 1 (by rfl) ⟨469703, by rfl⟩ : syracuseStep 626271 = 939407) B939407
theorem B17993339 : Blo 622298 17993339 := bstep (se 1 (by rfl) ⟨13495004, by rfl⟩ : syracuseStep 17993339 = 26990009) B26990009
theorem B5049989 : Blo 622298 5049989 := bstep (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) B946873
theorem B1183403 : Blo 622298 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B1773407 : Blo 622298 1773407 := bstep (se 1 (by rfl) ⟨1330055, by rfl⟩ : syracuseStep 1773407 = 2660111) B2660111
theorem B1347511 : Blo 622298 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B1052635 : Blo 622298 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B7999499 : Blo 622298 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1576979 : Blo 622298 1576979 := bstep (se 1 (by rfl) ⟨1182734, by rfl⟩ : syracuseStep 1576979 = 2365469) B2365469
theorem B1773647 : Blo 622298 1773647 := bstep (se 1 (by rfl) ⟨1330235, by rfl⟩ : syracuseStep 1773647 = 2660471) B2660471
theorem B757883 : Blo 622298 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B790651 : Blo 622298 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B790879 : Blo 622298 790879 := bstep (se 1 (by rfl) ⟨593159, by rfl⟩ : syracuseStep 790879 = 1186319) B1186319
theorem B1053263 : Blo 622298 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B6820469 : Blo 622298 6820469 := bstep (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) B639419
theorem B2101895 : Blo 622298 2101895 := bstep (se 1 (by rfl) ⟨1576421, by rfl⟩ : syracuseStep 2101895 = 3152843) B3152843
theorem B2101949 : Blo 622298 2101949 := bstep (se 3 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 2101949 = 788231) B788231
theorem B1774295 : Blo 622298 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B5346121 : Blo 622298 5346121 := bstep (se 2 (by rfl) ⟨2004795, by rfl⟩ : syracuseStep 5346121 = 4009591) B4009591
theorem B2102111 : Blo 622298 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B791471 : Blo 622298 791471 := bstep (se 1 (by rfl) ⟨593603, by rfl⟩ : syracuseStep 791471 = 1187207) B1187207
theorem B1774523 : Blo 622298 1774523 := bstep (se 1 (by rfl) ⟨1330892, by rfl⟩ : syracuseStep 1774523 = 2661785) B2661785
theorem B2102273 : Blo 622298 2102273 := bstep (se 2 (by rfl) ⟨788352, by rfl⟩ : syracuseStep 2102273 = 1576705) B1576705
theorem B1184777 : Blo 622298 1184777 := bstep (se 2 (by rfl) ⟨444291, by rfl⟩ : syracuseStep 1184777 = 888583) B888583
theorem B1184807 : Blo 622298 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B3150899 : Blo 622298 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B1774649 : Blo 622298 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B2364497 : Blo 622298 2364497 := bstep (se 2 (by rfl) ⟨886686, by rfl⟩ : syracuseStep 2364497 = 1773373) B1773373
theorem B2364815 : Blo 622298 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B1054127 : Blo 622298 1054127 := bstep (se 1 (by rfl) ⟨790595, by rfl⟩ : syracuseStep 1054127 = 1581191) B1581191
theorem B3806759 : Blo 622298 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B1185491 : Blo 622298 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B1185529 : Blo 622298 1185529 := bstep (se 2 (by rfl) ⟨444573, by rfl⟩ : syracuseStep 1185529 = 889147) B889147
theorem B2103083 : Blo 622298 2103083 := bstep (se 1 (by rfl) ⟨1577312, by rfl⟩ : syracuseStep 2103083 = 3154625) B3154625
theorem B1054559 : Blo 622298 1054559 := bstep (se 1 (by rfl) ⟨790919, by rfl⟩ : syracuseStep 1054559 = 1581839) B1581839
theorem B2103353 : Blo 622298 2103353 := bstep (se 2 (by rfl) ⟨788757, by rfl⟩ : syracuseStep 2103353 = 1577515) B1577515
theorem B8984675 : Blo 622298 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B2365757 : Blo 622298 2365757 := bstep (se 3 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 2365757 = 887159) B887159
theorem B2103677 : Blo 622298 2103677 := bstep (se 3 (by rfl) ⟨394439, by rfl⟩ : syracuseStep 2103677 = 788879) B788879
theorem B1055119 : Blo 622298 1055119 := bstep (se 1 (by rfl) ⟨791339, by rfl⟩ : syracuseStep 1055119 = 1582679) B1582679
theorem B1186235 : Blo 622298 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B3152519 : Blo 622298 3152519 := bstep (se 1 (by rfl) ⟨2364389, by rfl⟩ : syracuseStep 3152519 = 4728779) B4728779
theorem B2103947 : Blo 622298 2103947 := bstep (se 1 (by rfl) ⟨1577960, by rfl⟩ : syracuseStep 2103947 = 3155921) B3155921
theorem B1186721 : Blo 622298 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B1055801 : Blo 622298 1055801 := bstep (se 2 (by rfl) ⟨395925, by rfl⟩ : syracuseStep 1055801 = 791851) B791851
theorem B2137241 : Blo 622298 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B1186987 : Blo 622298 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B1580431 : Blo 622298 1580431 := bstep (se 1 (by rfl) ⟨1185323, by rfl⟩ : syracuseStep 1580431 = 2370647) B2370647
theorem B1187291 : Blo 622298 1187291 := bstep (se 1 (by rfl) ⟨890468, by rfl⟩ : syracuseStep 1187291 = 1780937) B1780937
theorem B2104865 : Blo 622298 2104865 := bstep (se 2 (by rfl) ⟨789324, by rfl⟩ : syracuseStep 2104865 = 1578649) B1578649
theorem B1580755 : Blo 622298 1580755 := bstep (se 1 (by rfl) ⟨1185566, by rfl⟩ : syracuseStep 1580755 = 2371133) B2371133
theorem B1056503 : Blo 622298 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B2105081 : Blo 622298 2105081 := bstep (se 2 (by rfl) ⟨789405, by rfl⟩ : syracuseStep 2105081 = 1578811) B1578811
theorem B4857695 : Blo 622298 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B2105351 : Blo 622298 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B3153977 : Blo 622298 3153977 := bstep (se 2 (by rfl) ⟨1182741, by rfl⟩ : syracuseStep 3153977 = 2365483) B2365483
theorem B1056847 : Blo 622298 1056847 := bstep (se 1 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 1056847 = 1585271) B1585271
theorem B2105459 : Blo 622298 2105459 := bstep (se 1 (by rfl) ⟨1579094, by rfl⟩ : syracuseStep 2105459 = 3158189) B3158189
theorem B2105729 : Blo 622298 2105729 := bstep (se 2 (by rfl) ⟨789648, by rfl⟩ : syracuseStep 2105729 = 1579297) B1579297
theorem B1188361 : Blo 622298 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B4727321 : Blo 622298 4727321 := bstep (se 2 (by rfl) ⟨1772745, by rfl⟩ : syracuseStep 4727321 = 3545491) B3545491
theorem B19178009 : Blo 622298 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B1581707 : Blo 622298 1581707 := bstep (se 1 (by rfl) ⟨1186280, by rfl⟩ : syracuseStep 1581707 = 2372561) B2372561
theorem B5055149 : Blo 622298 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B4498105 : Blo 622298 4498105 := bstep (se 2 (by rfl) ⟨1686789, by rfl⟩ : syracuseStep 4498105 = 3373579) B3373579
theorem B3547907 : Blo 622298 3547907 := bstep (se 1 (by rfl) ⟨2660930, by rfl⟩ : syracuseStep 3547907 = 5321861) B5321861
theorem B4006979 : Blo 622298 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B2106539 : Blo 622298 2106539 := bstep (se 1 (by rfl) ⟨1579904, by rfl⟩ : syracuseStep 2106539 = 3159809) B3159809
theorem B3548407 : Blo 622298 3548407 := bstep (se 1 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 3548407 = 5322611) B5322611
theorem B4105637 : Blo 622298 4105637 := bstep (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) B769807
theorem B1779239 : Blo 622298 1779239 := bstep (se 1 (by rfl) ⟨1334429, by rfl⟩ : syracuseStep 1779239 = 2668859) B2668859
theorem B2369159 : Blo 622298 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B2107079 : Blo 622298 2107079 := bstep (se 1 (by rfl) ⟨1580309, by rfl⟩ : syracuseStep 2107079 = 3160619) B3160619
theorem B1582841 : Blo 622298 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B1583023 : Blo 622298 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B4007951 : Blo 622298 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B3156083 : Blo 622298 3156083 := bstep (se 1 (by rfl) ⟨2367062, by rfl⟩ : syracuseStep 3156083 = 4734125) B4734125
theorem B1583489 : Blo 622298 1583489 := bstep (se 2 (by rfl) ⟨593808, by rfl⟩ : syracuseStep 1583489 = 1187617) B1187617
theorem B2107943 : Blo 622298 2107943 := bstep (se 1 (by rfl) ⟨1580957, by rfl⟩ : syracuseStep 2107943 = 3161915) B3161915
theorem B2108051 : Blo 622298 2108051 := bstep (se 1 (by rfl) ⟨1581038, by rfl⟩ : syracuseStep 2108051 = 3162077) B3162077
theorem B5057225 : Blo 622298 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B2665169 : Blo 622298 2665169 := bstep (se 2 (by rfl) ⟨999438, by rfl⟩ : syracuseStep 2665169 = 1998877) B1998877
theorem B1583945 : Blo 622298 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B666463 : Blo 622298 666463 := bstep (se 1 (by rfl) ⟨499847, by rfl⟩ : syracuseStep 666463 = 999695) B999695
theorem B1518443 : Blo 622298 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B2108267 : Blo 622298 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B2108321 : Blo 622298 2108321 := bstep (se 2 (by rfl) ⟨790620, by rfl⟩ : syracuseStep 2108321 = 1581241) B1581241
theorem B9612215 : Blo 622298 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B1780663 : Blo 622298 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B666587 : Blo 622298 666587 := bstep (se 1 (by rfl) ⟨499940, by rfl⟩ : syracuseStep 666587 = 999881) B999881
theorem B621849635 : Blo 622298 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B2370617 : Blo 622298 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B1584299 : Blo 622298 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B15969473 : Blo 622298 15969473 := bstep (se 2 (by rfl) ⟨5988552, by rfl⟩ : syracuseStep 15969473 = 11977105) B11977105
theorem B34614641 : Blo 622298 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B4730237 : Blo 622298 4730237 := bstep (se 3 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 4730237 = 1773839) B1773839
theorem B2108915 : Blo 622298 2108915 := bstep (se 1 (by rfl) ⟨1581686, by rfl⟩ : syracuseStep 2108915 = 3163373) B3163373
theorem B3157703 : Blo 622298 3157703 := bstep (se 1 (by rfl) ⟨2368277, by rfl⟩ : syracuseStep 3157703 = 4736555) B4736555
theorem B2404039 : Blo 622298 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B9023197 : Blo 622298 9023197 := bstep (se 3 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 9023197 = 3383699) B3383699
theorem B1585079 : Blo 622298 1585079 := bstep (se 1 (by rfl) ⟨1188809, by rfl⟩ : syracuseStep 1585079 = 2377619) B2377619
theorem B1781767 : Blo 622298 1781767 := bstep (se 1 (by rfl) ⟨1336325, by rfl⟩ : syracuseStep 1781767 = 2672651) B2672651
theorem B2109455 : Blo 622298 2109455 := bstep (se 1 (by rfl) ⟨1582091, by rfl⟩ : syracuseStep 2109455 = 3164183) B3164183
theorem B7090253 : Blo 622298 7090253 := bstep (se 3 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 7090253 = 2658845) B2658845
theorem B1782121 : Blo 622298 1782121 := bstep (se 2 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 1782121 = 1336591) B1336591
theorem B2372105 : Blo 622298 2372105 := bstep (se 2 (by rfl) ⟨889539, by rfl⟩ : syracuseStep 2372105 = 1779079) B1779079
theorem B2110049 : Blo 622298 2110049 := bstep (se 2 (by rfl) ⟨791268, by rfl⟩ : syracuseStep 2110049 = 1582537) B1582537
theorem B1782395 : Blo 622298 1782395 := bstep (se 1 (by rfl) ⟨1336796, by rfl⟩ : syracuseStep 1782395 = 2673593) B2673593
theorem B3846865 : Blo 622298 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B10138385 : Blo 622298 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B701563 : Blo 622298 701563 := bstep (se 1 (by rfl) ⟨526172, by rfl⟩ : syracuseStep 701563 = 1052345) B1052345
theorem B668795 : Blo 622298 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B4011437 : Blo 622298 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B702031 : Blo 622298 702031 := bstep (se 1 (by rfl) ⟨526523, by rfl⟩ : syracuseStep 702031 = 1053047) B1053047
theorem B2373259 : Blo 622298 2373259 := bstep (se 1 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 2373259 = 3559889) B3559889
theorem B4503239 : Blo 622298 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B2701151 : Blo 622298 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B7223201 : Blo 622298 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B2373563 : Blo 622298 2373563 := bstep (se 1 (by rfl) ⟨1780172, by rfl⟩ : syracuseStep 2373563 = 3560345) B3560345
theorem B702427 : Blo 622298 702427 := bstep (se 1 (by rfl) ⟨526820, by rfl⟩ : syracuseStep 702427 = 1053641) B1053641
theorem B2111507 : Blo 622298 2111507 := bstep (se 1 (by rfl) ⟨1583630, by rfl⟩ : syracuseStep 2111507 = 3167261) B3167261
theorem B6010969 : Blo 622298 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B6764633 : Blo 622298 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B6764801 : Blo 622298 6764801 := bstep (se 2 (by rfl) ⟨2536800, by rfl⟩ : syracuseStep 6764801 = 5073601) B5073601
theorem B2111831 : Blo 622298 2111831 := bstep (se 1 (by rfl) ⟨1583873, by rfl⟩ : syracuseStep 2111831 = 3167747) B3167747
theorem B2996585 : Blo 622298 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B702895 : Blo 622298 702895 := bstep (se 1 (by rfl) ⟨527171, by rfl⟩ : syracuseStep 702895 = 1054343) B1054343
theorem B10959545 : Blo 622298 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B703327 : Blo 622298 703327 := bstep (se 1 (by rfl) ⟨527495, by rfl⟩ : syracuseStep 703327 = 1054991) B1054991
theorem B703687 : Blo 622298 703687 := bstep (se 1 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 703687 = 1055531) B1055531
theorem B4504855 : Blo 622298 4504855 := bstep (se 1 (by rfl) ⟨3378641, by rfl⟩ : syracuseStep 4504855 = 6757283) B6757283
theorem B2243965 : Blo 622298 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B2538877 : Blo 622298 2538877 := bstep (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) B952079
theorem B2112911 : Blo 622298 2112911 := bstep (se 1 (by rfl) ⟨1584683, by rfl⟩ : syracuseStep 2112911 = 3169367) B3169367
theorem B1687049 : Blo 622298 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B933455 : Blo 622298 933455 := bstep (se 1 (by rfl) ⟨700091, by rfl⟩ : syracuseStep 933455 = 1400183) B1400183
theorem B4734611 : Blo 622298 4734611 := bstep (se 1 (by rfl) ⟨3550958, by rfl⟩ : syracuseStep 4734611 = 7101917) B7101917
theorem B933575 : Blo 622298 933575 := bstep (se 1 (by rfl) ⟨700181, by rfl⟩ : syracuseStep 933575 = 1400363) B1400363
theorem B2113235 : Blo 622298 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B5324525 : Blo 622298 5324525 := bstep (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) B1996697
theorem B933737 : Blo 622298 933737 := bstep (se 2 (by rfl) ⟨350151, by rfl⟩ : syracuseStep 933737 = 700303) B700303
theorem B933815 : Blo 622298 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B933851 : Blo 622298 933851 := bstep (se 1 (by rfl) ⟨700388, by rfl⟩ : syracuseStep 933851 = 1400777) B1400777
theorem B704551 : Blo 622298 704551 := bstep (se 1 (by rfl) ⟨528413, by rfl⟩ : syracuseStep 704551 = 1056827) B1056827
theorem B934319 : Blo 622298 934319 := bstep (se 1 (by rfl) ⟨700739, by rfl⟩ : syracuseStep 934319 = 1401479) B1401479
theorem B934409 : Blo 622298 934409 := bstep (se 2 (by rfl) ⟨350403, by rfl⟩ : syracuseStep 934409 = 700807) B700807
theorem B934439 : Blo 622298 934439 := bstep (se 1 (by rfl) ⟨700829, by rfl⟩ : syracuseStep 934439 = 1401659) B1401659
theorem B3195451 : Blo 622298 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B2277985 : Blo 622298 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B934523 : Blo 622298 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B934649 : Blo 622298 934649 := bstep (se 2 (by rfl) ⟨350493, by rfl⟩ : syracuseStep 934649 = 700987) B700987
theorem B934751 : Blo 622298 934751 := bstep (se 1 (by rfl) ⟨701063, by rfl⟩ : syracuseStep 934751 = 1402127) B1402127
theorem B934763 : Blo 622298 934763 := bstep (se 1 (by rfl) ⟨701072, by rfl⟩ : syracuseStep 934763 = 1402145) B1402145
theorem B10961771 : Blo 622298 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B934991 : Blo 622298 934991 := bstep (se 1 (by rfl) ⟨701243, by rfl⟩ : syracuseStep 934991 = 1402487) B1402487
theorem B935111 : Blo 622298 935111 := bstep (se 1 (by rfl) ⟨701333, by rfl⟩ : syracuseStep 935111 = 1402667) B1402667
theorem B1262839 : Blo 622298 1262839 := bstep (se 1 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 1262839 = 1894259) B1894259
theorem B935273 : Blo 622298 935273 := bstep (se 2 (by rfl) ⟨350727, by rfl⟩ : syracuseStep 935273 = 701455) B701455
theorem B3163535 : Blo 622298 3163535 := bstep (se 1 (by rfl) ⟨2372651, by rfl⟩ : syracuseStep 3163535 = 4745303) B4745303
theorem B935351 : Blo 622298 935351 := bstep (se 1 (by rfl) ⟨701513, by rfl⟩ : syracuseStep 935351 = 1403027) B1403027
theorem B935387 : Blo 622298 935387 := bstep (se 1 (by rfl) ⟨701540, by rfl⟩ : syracuseStep 935387 = 1403081) B1403081
theorem B1689299 : Blo 622298 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B2377633 : Blo 622298 2377633 := bstep (se 2 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 2377633 = 1783225) B1783225
theorem B935855 : Blo 622298 935855 := bstep (se 1 (by rfl) ⟨701891, by rfl⟩ : syracuseStep 935855 = 1403783) B1403783
theorem B7817219 : Blo 622298 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B935945 : Blo 622298 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B935975 : Blo 622298 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B6768697 : Blo 622298 6768697 := bstep (se 2 (by rfl) ⟨2538261, by rfl⟩ : syracuseStep 6768697 = 5076523) B5076523
theorem B936059 : Blo 622298 936059 := bstep (se 1 (by rfl) ⟨702044, by rfl⟩ : syracuseStep 936059 = 1404089) B1404089
theorem B936185 : Blo 622298 936185 := bstep (se 2 (by rfl) ⟨351069, by rfl⟩ : syracuseStep 936185 = 702139) B702139
theorem B936287 : Blo 622298 936287 := bstep (se 1 (by rfl) ⟨702215, by rfl⟩ : syracuseStep 936287 = 1404431) B1404431
theorem B936299 : Blo 622298 936299 := bstep (se 1 (by rfl) ⟨702224, by rfl⟩ : syracuseStep 936299 = 1404449) B1404449
theorem B1690121 : Blo 622298 1690121 := bstep (se 2 (by rfl) ⟨633795, by rfl⟩ : syracuseStep 1690121 = 1267591) B1267591
theorem B936527 : Blo 622298 936527 := bstep (se 1 (by rfl) ⟨702395, by rfl⟩ : syracuseStep 936527 = 1404791) B1404791
theorem B22727303 : Blo 622298 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B936647 : Blo 622298 936647 := bstep (se 1 (by rfl) ⟨702485, by rfl⟩ : syracuseStep 936647 = 1404971) B1404971
theorem B3001043 : Blo 622298 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B2247497 : Blo 622298 2247497 := bstep (se 2 (by rfl) ⟨842811, by rfl⟩ : syracuseStep 2247497 = 1685623) B1685623
theorem B936809 : Blo 622298 936809 := bstep (se 2 (by rfl) ⟨351303, by rfl⟩ : syracuseStep 936809 = 702607) B702607
theorem B20237201 : Blo 622298 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B1264567 : Blo 622298 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B936887 : Blo 622298 936887 := bstep (se 1 (by rfl) ⟨702665, by rfl⟩ : syracuseStep 936887 = 1405331) B1405331
theorem B936923 : Blo 622298 936923 := bstep (se 1 (by rfl) ⟨702692, by rfl⟩ : syracuseStep 936923 = 1405385) B1405385
theorem B4738013 : Blo 622298 4738013 := bstep (se 3 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 4738013 = 1776755) B1776755
theorem B937391 : Blo 622298 937391 := bstep (se 1 (by rfl) ⟨703043, by rfl⟩ : syracuseStep 937391 = 1406087) B1406087
theorem B1232315 : Blo 622298 1232315 := bstep (se 1 (by rfl) ⟨924236, by rfl⟩ : syracuseStep 1232315 = 1848473) B1848473
theorem B3165641 : Blo 622298 3165641 := bstep (se 2 (by rfl) ⟨1187115, by rfl⟩ : syracuseStep 3165641 = 2374231) B2374231
theorem B937481 : Blo 622298 937481 := bstep (se 2 (by rfl) ⟨351555, by rfl⟩ : syracuseStep 937481 = 703111) B703111
theorem B937511 : Blo 622298 937511 := bstep (se 1 (by rfl) ⟨703133, by rfl⟩ : syracuseStep 937511 = 1406267) B1406267
theorem B937595 : Blo 622298 937595 := bstep (se 1 (by rfl) ⟨703196, by rfl⟩ : syracuseStep 937595 = 1406393) B1406393
theorem B2248391 : Blo 622298 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B8015597 : Blo 622298 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B937721 : Blo 622298 937721 := bstep (se 2 (by rfl) ⟨351645, by rfl⟩ : syracuseStep 937721 = 703291) B703291
theorem B937823 : Blo 622298 937823 := bstep (se 1 (by rfl) ⟨703367, by rfl⟩ : syracuseStep 937823 = 1406735) B1406735
theorem B937835 : Blo 622298 937835 := bstep (se 1 (by rfl) ⟨703376, by rfl⟩ : syracuseStep 937835 = 1406753) B1406753
theorem B3002273 : Blo 622298 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B23973893 : Blo 622298 23973893 := bstep (se 4 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 23973893 = 4495105) B4495105
theorem B938063 : Blo 622298 938063 := bstep (se 1 (by rfl) ⟨703547, by rfl⟩ : syracuseStep 938063 = 1407095) B1407095
theorem B3166289 : Blo 622298 3166289 := bstep (se 2 (by rfl) ⟨1187358, by rfl⟩ : syracuseStep 3166289 = 2374717) B2374717
theorem B1200251 : Blo 622298 1200251 := bstep (se 1 (by rfl) ⟨900188, by rfl⟩ : syracuseStep 1200251 = 1800377) B1800377
theorem B938183 : Blo 622298 938183 := bstep (se 1 (by rfl) ⟨703637, by rfl⟩ : syracuseStep 938183 = 1407275) B1407275
theorem B8540477 : Blo 622298 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B938345 : Blo 622298 938345 := bstep (se 2 (by rfl) ⟨351879, by rfl⟩ : syracuseStep 938345 = 703759) B703759
theorem B938423 : Blo 622298 938423 := bstep (se 1 (by rfl) ⟨703817, by rfl⟩ : syracuseStep 938423 = 1407635) B1407635
theorem B938459 : Blo 622298 938459 := bstep (se 1 (by rfl) ⟨703844, by rfl⟩ : syracuseStep 938459 = 1407689) B1407689
theorem B5067245 : Blo 622298 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B7328315 : Blo 622298 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B3560071 : Blo 622298 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B2282195 : Blo 622298 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B5493577 : Blo 622298 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B938927 : Blo 622298 938927 := bstep (se 1 (by rfl) ⟨704195, by rfl⟩ : syracuseStep 938927 = 1408391) B1408391
theorem B939017 : Blo 622298 939017 := bstep (se 2 (by rfl) ⟨352131, by rfl⟩ : syracuseStep 939017 = 704263) B704263
theorem B1496083 : Blo 622298 1496083 := bstep (se 1 (by rfl) ⟨1122062, by rfl⟩ : syracuseStep 1496083 = 2244125) B2244125
theorem B939047 : Blo 622298 939047 := bstep (se 1 (by rfl) ⟨704285, by rfl⟩ : syracuseStep 939047 = 1408571) B1408571
theorem B939131 : Blo 622298 939131 := bstep (se 1 (by rfl) ⟨704348, by rfl⟩ : syracuseStep 939131 = 1408697) B1408697
theorem B2249975 : Blo 622298 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B939257 : Blo 622298 939257 := bstep (se 2 (by rfl) ⟨352221, by rfl⟩ : syracuseStep 939257 = 704443) B704443
theorem B4281623 : Blo 622298 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B939359 : Blo 622298 939359 := bstep (se 1 (by rfl) ⟨704519, by rfl⟩ : syracuseStep 939359 = 1409039) B1409039
theorem B939371 : Blo 622298 939371 := bstep (se 1 (by rfl) ⟨704528, by rfl⟩ : syracuseStep 939371 = 1409057) B1409057
theorem B983684837 : Blo 622298 983684837 := bstep (se 4 (by rfl) ⟨92220453, by rfl⟩ : syracuseStep 983684837 = 184440907) B184440907
theorem B1202015 : Blo 622298 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B3561529 : Blo 622298 3561529 := bstep (se 2 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 3561529 = 2671147) B2671147
theorem B3004733 : Blo 622298 3004733 := bstep (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) B1126775
theorem B1268111 : Blo 622298 1268111 := bstep (se 1 (by rfl) ⟨951083, by rfl⟩ : syracuseStep 1268111 = 1902167) B1902167
theorem B1333883 : Blo 622298 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B1268743 : Blo 622298 1268743 := bstep (se 1 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 1268743 = 1903115) B1903115
theorem B3038411 : Blo 622298 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B1400417 : Blo 622298 1400417 := bstep (se 2 (by rfl) ⟨525156, by rfl⟩ : syracuseStep 1400417 = 1050313) B1050313
theorem B9002785 : Blo 622298 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B1335113 : Blo 622298 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B1400759 : Blo 622298 1400759 := bstep (se 1 (by rfl) ⟨1050569, by rfl⟩ : syracuseStep 1400759 = 2101139) B2101139
theorem B2252731 : Blo 622298 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B4317299 : Blo 622298 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B4513907 : Blo 622298 4513907 := bstep (se 1 (by rfl) ⟨3385430, by rfl⟩ : syracuseStep 4513907 = 6770861) B6770861
theorem B1401353 : Blo 622298 1401353 := bstep (se 2 (by rfl) ⟨525507, by rfl⟩ : syracuseStep 1401353 = 1051015) B1051015
theorem B1335847 : Blo 622298 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B1139279 : Blo 622298 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B7988017 : Blo 622298 7988017 := bstep (se 2 (by rfl) ⟨2995506, by rfl⟩ : syracuseStep 7988017 = 5991013) B5991013
theorem B1401695 : Blo 622298 1401695 := bstep (se 1 (by rfl) ⟨1051271, by rfl⟩ : syracuseStep 1401695 = 2102543) B2102543
theorem B1401875 : Blo 622298 1401875 := bstep (se 1 (by rfl) ⟨1051406, by rfl⟩ : syracuseStep 1401875 = 2102813) B2102813
theorem B2843819 : Blo 622298 2843819 := bstep (se 1 (by rfl) ⟨2132864, by rfl⟩ : syracuseStep 2843819 = 4265729) B4265729
theorem B1402217 : Blo 622298 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B3007945 : Blo 622298 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B1337249 : Blo 622298 1337249 := bstep (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) B1002937
theorem B1402811 : Blo 622298 1402811 := bstep (se 1 (by rfl) ⟨1052108, by rfl⟩ : syracuseStep 1402811 = 2104217) B2104217
theorem B1402937 : Blo 622298 1402937 := bstep (se 2 (by rfl) ⟨526101, by rfl⟩ : syracuseStep 1402937 = 1052203) B1052203
theorem B747643 : Blo 622298 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B1403279 : Blo 622298 1403279 := bstep (se 1 (by rfl) ⟨1052459, by rfl⟩ : syracuseStep 1403279 = 2104919) B2104919
theorem B1403603 : Blo 622298 1403603 := bstep (se 1 (by rfl) ⟨1052702, by rfl⟩ : syracuseStep 1403603 = 2105405) B2105405
theorem B17099761 : Blo 622298 17099761 := bstep (se 2 (by rfl) ⟨6412410, by rfl⟩ : syracuseStep 17099761 = 12824821) B12824821
theorem B2256119 : Blo 622298 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B1404539 : Blo 622298 1404539 := bstep (se 1 (by rfl) ⟨1053404, by rfl⟩ : syracuseStep 1404539 = 2106809) B2106809
theorem B1404665 : Blo 622298 1404665 := bstep (se 2 (by rfl) ⟨526749, by rfl⟩ : syracuseStep 1404665 = 1053499) B1053499
theorem B1404935 : Blo 622298 1404935 := bstep (se 1 (by rfl) ⟨1053701, by rfl⟩ : syracuseStep 1404935 = 2107403) B2107403
theorem B1405007 : Blo 622298 1405007 := bstep (se 1 (by rfl) ⟨1053755, by rfl⟩ : syracuseStep 1405007 = 2107511) B2107511
theorem B3993857 : Blo 622298 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B3993907 : Blo 622298 3993907 := bstep (se 1 (by rfl) ⟨2995430, by rfl⟩ : syracuseStep 3993907 = 5990861) B5990861
theorem B1405403 : Blo 622298 1405403 := bstep (se 1 (by rfl) ⟨1054052, by rfl⟩ : syracuseStep 1405403 = 2108105) B2108105
theorem B1405871 : Blo 622298 1405871 := bstep (se 1 (by rfl) ⟨1054403, by rfl⟩ : syracuseStep 1405871 = 2108807) B2108807
theorem B1406123 : Blo 622298 1406123 := bstep (se 1 (by rfl) ⟨1054592, by rfl⟩ : syracuseStep 1406123 = 2109185) B2109185
theorem B19264715 : Blo 622298 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B1406663 : Blo 622298 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B4749191 : Blo 622298 4749191 := bstep (se 1 (by rfl) ⟨3561893, by rfl⟩ : syracuseStep 4749191 = 7123787) B7123787
theorem B9598925 : Blo 622298 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B1407527 : Blo 622298 1407527 := bstep (se 1 (by rfl) ⟨1055645, by rfl⟩ : syracuseStep 1407527 = 2111291) B2111291
theorem B6748717 : Blo 622298 6748717 := bstep (se 3 (by rfl) ⟨1265384, by rfl⟩ : syracuseStep 6748717 = 2530769) B2530769
theorem B1899197 : Blo 622298 1899197 := bstep (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) B712199
theorem B1407851 : Blo 622298 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B1407905 : Blo 622298 1407905 := bstep (se 2 (by rfl) ⟨527964, by rfl⟩ : syracuseStep 1407905 = 1055929) B1055929
theorem B1408247 : Blo 622298 1408247 := bstep (se 1 (by rfl) ⟨1056185, by rfl⟩ : syracuseStep 1408247 = 2112371) B2112371
theorem B622299 : Blo 622298 622299 := bstep (se 1 (by rfl) ⟨466724, by rfl⟩ : syracuseStep 622299 = 933449) B933449
theorem B622375 : Blo 622298 622375 := bstep (se 1 (by rfl) ⟨466781, by rfl⟩ : syracuseStep 622375 = 933563) B933563
theorem B1408841 : Blo 622298 1408841 := bstep (se 2 (by rfl) ⟨528315, by rfl⟩ : syracuseStep 1408841 = 1056631) B1056631
theorem B622415 : Blo 622298 622415 := bstep (se 1 (by rfl) ⟨466811, by rfl⟩ : syracuseStep 622415 = 933623) B933623
theorem B622431 : Blo 622298 622431 := bstep (se 1 (by rfl) ⟨466823, by rfl⟩ : syracuseStep 622431 = 933647) B933647
theorem B622459 : Blo 622298 622459 := bstep (se 1 (by rfl) ⟨466844, by rfl⟩ : syracuseStep 622459 = 933689) B933689
theorem B622511 : Blo 622298 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B622535 : Blo 622298 622535 := bstep (se 1 (by rfl) ⟨466901, by rfl⟩ : syracuseStep 622535 = 933803) B933803
theorem B622555 : Blo 622298 622555 := bstep (se 1 (by rfl) ⟨466916, by rfl⟩ : syracuseStep 622555 = 933833) B933833
theorem B1409129 : Blo 622298 1409129 := bstep (se 2 (by rfl) ⟨528423, by rfl⟩ : syracuseStep 1409129 = 1056847) B1056847
theorem B5701751 : Blo 622298 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B622879 : Blo 622298 622879 := bstep (se 1 (by rfl) ⟨467159, by rfl⟩ : syracuseStep 622879 = 934319) B934319
theorem B622939 : Blo 622298 622939 := bstep (se 1 (by rfl) ⟨467204, by rfl⟩ : syracuseStep 622939 = 934409) B934409
theorem B622959 : Blo 622298 622959 := bstep (se 1 (by rfl) ⟨467219, by rfl⟩ : syracuseStep 622959 = 934439) B934439
theorem B623015 : Blo 622298 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B623099 : Blo 622298 623099 := bstep (se 1 (by rfl) ⟨467324, by rfl⟩ : syracuseStep 623099 = 934649) B934649
theorem B623167 : Blo 622298 623167 := bstep (se 1 (by rfl) ⟨467375, by rfl⟩ : syracuseStep 623167 = 934751) B934751
theorem B623175 : Blo 622298 623175 := bstep (se 1 (by rfl) ⟨467381, by rfl⟩ : syracuseStep 623175 = 934763) B934763
theorem B623327 : Blo 622298 623327 := bstep (se 1 (by rfl) ⟨467495, by rfl⟩ : syracuseStep 623327 = 934991) B934991
theorem B4260601 : Blo 622298 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B623407 : Blo 622298 623407 := bstep (se 1 (by rfl) ⟨467555, by rfl⟩ : syracuseStep 623407 = 935111) B935111
theorem B623515 : Blo 622298 623515 := bstep (se 1 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 623515 = 935273) B935273
theorem B5997473 : Blo 622298 5997473 := bstep (se 2 (by rfl) ⟨2249052, by rfl⟩ : syracuseStep 5997473 = 4498105) B4498105
theorem B623567 : Blo 622298 623567 := bstep (se 1 (by rfl) ⟨467675, by rfl⟩ : syracuseStep 623567 = 935351) B935351
theorem B623591 : Blo 622298 623591 := bstep (se 1 (by rfl) ⟨467693, by rfl⟩ : syracuseStep 623591 = 935387) B935387
theorem B3802087 : Blo 622298 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B10650689 : Blo 622298 10650689 := bstep (se 2 (by rfl) ⟨3994008, by rfl⟩ : syracuseStep 10650689 = 7988017) B7988017
theorem B623903 : Blo 622298 623903 := bstep (se 1 (by rfl) ⟨467927, by rfl⟩ : syracuseStep 623903 = 935855) B935855
theorem B5211479 : Blo 622298 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B623963 : Blo 622298 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B623983 : Blo 622298 623983 := bstep (se 1 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 623983 = 935975) B935975
theorem B624039 : Blo 622298 624039 := bstep (se 1 (by rfl) ⟨468029, by rfl⟩ : syracuseStep 624039 = 936059) B936059
theorem B787963 : Blo 622298 787963 := bstep (se 1 (by rfl) ⟨590972, by rfl⟩ : syracuseStep 787963 = 1181945) B1181945
theorem B624123 : Blo 622298 624123 := bstep (se 1 (by rfl) ⟨468092, by rfl⟩ : syracuseStep 624123 = 936185) B936185
theorem B25691681 : Blo 622298 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B4064825 : Blo 622298 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B624191 : Blo 622298 624191 := bstep (se 1 (by rfl) ⟨468143, by rfl⟩ : syracuseStep 624191 = 936287) B936287
theorem B624199 : Blo 622298 624199 := bstep (se 1 (by rfl) ⟨468149, by rfl⟩ : syracuseStep 624199 = 936299) B936299
theorem B624351 : Blo 622298 624351 := bstep (se 1 (by rfl) ⟨468263, by rfl⟩ : syracuseStep 624351 = 936527) B936527
theorem B1050347 : Blo 622298 1050347 := bstep (se 1 (by rfl) ⟨787760, by rfl⟩ : syracuseStep 1050347 = 1575521) B1575521
theorem B624431 : Blo 622298 624431 := bstep (se 1 (by rfl) ⟨468323, by rfl⟩ : syracuseStep 624431 = 936647) B936647
theorem B2000695 : Blo 622298 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B624539 : Blo 622298 624539 := bstep (se 1 (by rfl) ⟨468404, by rfl⟩ : syracuseStep 624539 = 936809) B936809
theorem B624591 : Blo 622298 624591 := bstep (se 1 (by rfl) ⟨468443, by rfl⟩ : syracuseStep 624591 = 936887) B936887
theorem B624615 : Blo 622298 624615 := bstep (se 1 (by rfl) ⟨468461, by rfl⟩ : syracuseStep 624615 = 936923) B936923
theorem B30279683 : Blo 622298 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B29231389 : Blo 622298 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B624927 : Blo 622298 624927 := bstep (se 1 (by rfl) ⟨468695, by rfl⟩ : syracuseStep 624927 = 937391) B937391
theorem B821543 : Blo 622298 821543 := bstep (se 1 (by rfl) ⟨616157, by rfl⟩ : syracuseStep 821543 = 1232315) B1232315
theorem B1182043 : Blo 622298 1182043 := bstep (se 1 (by rfl) ⟨886532, by rfl⟩ : syracuseStep 1182043 = 1773065) B1773065
theorem B624987 : Blo 622298 624987 := bstep (se 1 (by rfl) ⟨468740, by rfl⟩ : syracuseStep 624987 = 937481) B937481
theorem B625007 : Blo 622298 625007 := bstep (se 1 (by rfl) ⟨468755, by rfl⟩ : syracuseStep 625007 = 937511) B937511
theorem B11995559 : Blo 622298 11995559 := bstep (se 1 (by rfl) ⟨8996669, by rfl⟩ : syracuseStep 11995559 = 17993339) B17993339
theorem B625063 : Blo 622298 625063 := bstep (se 1 (by rfl) ⟨468797, by rfl⟩ : syracuseStep 625063 = 937595) B937595
theorem B788935 : Blo 622298 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B5343731 : Blo 622298 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B625147 : Blo 622298 625147 := bstep (se 1 (by rfl) ⟨468860, by rfl⟩ : syracuseStep 625147 = 937721) B937721
theorem B1182271 : Blo 622298 1182271 := bstep (se 1 (by rfl) ⟨886703, by rfl⟩ : syracuseStep 1182271 = 1773407) B1773407
theorem B625215 : Blo 622298 625215 := bstep (se 1 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 625215 = 937823) B937823
theorem B625223 : Blo 622298 625223 := bstep (se 1 (by rfl) ⟨468917, by rfl⟩ : syracuseStep 625223 = 937835) B937835
theorem B2001515 : Blo 622298 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B1051319 : Blo 622298 1051319 := bstep (se 1 (by rfl) ⟨788489, by rfl⟩ : syracuseStep 1051319 = 1576979) B1576979
theorem B1182431 : Blo 622298 1182431 := bstep (se 1 (by rfl) ⟨886823, by rfl⟩ : syracuseStep 1182431 = 1773647) B1773647
theorem B625375 : Blo 622298 625375 := bstep (se 1 (by rfl) ⟨469031, by rfl⟩ : syracuseStep 625375 = 938063) B938063
theorem B625455 : Blo 622298 625455 := bstep (se 1 (by rfl) ⟨469091, by rfl⟩ : syracuseStep 625455 = 938183) B938183
theorem B625563 : Blo 622298 625563 := bstep (se 1 (by rfl) ⟨469172, by rfl⟩ : syracuseStep 625563 = 938345) B938345
theorem B625615 : Blo 622298 625615 := bstep (se 1 (by rfl) ⟨469211, by rfl⟩ : syracuseStep 625615 = 938423) B938423
theorem B625639 : Blo 622298 625639 := bstep (se 1 (by rfl) ⟨469229, by rfl⟩ : syracuseStep 625639 = 938459) B938459
theorem B4885543 : Blo 622298 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B1182863 : Blo 622298 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B1576169 : Blo 622298 1576169 := bstep (se 2 (by rfl) ⟨591063, by rfl⟩ : syracuseStep 1576169 = 1182127) B1182127
theorem B625951 : Blo 622298 625951 := bstep (se 1 (by rfl) ⟨469463, by rfl⟩ : syracuseStep 625951 = 938927) B938927
theorem B1183015 : Blo 622298 1183015 := bstep (se 1 (by rfl) ⟨887261, by rfl⟩ : syracuseStep 1183015 = 1774523) B1774523
theorem B5999933 : Blo 622298 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B789851 : Blo 622298 789851 := bstep (se 1 (by rfl) ⟨592388, by rfl⟩ : syracuseStep 789851 = 1184777) B1184777
theorem B626011 : Blo 622298 626011 := bstep (se 1 (by rfl) ⟨469508, by rfl⟩ : syracuseStep 626011 = 939017) B939017
theorem B626031 : Blo 622298 626031 := bstep (se 1 (by rfl) ⟨469523, by rfl⟩ : syracuseStep 626031 = 939047) B939047
theorem B2100599 : Blo 622298 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B1183099 : Blo 622298 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B1052041 : Blo 622298 1052041 := bstep (se 2 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 1052041 = 789031) B789031
theorem B1576331 : Blo 622298 1576331 := bstep (se 1 (by rfl) ⟨1182248, by rfl⟩ : syracuseStep 1576331 = 2364497) B2364497
theorem B626087 : Blo 622298 626087 := bstep (se 1 (by rfl) ⟨469565, by rfl⟩ : syracuseStep 626087 = 939131) B939131
theorem B626171 : Blo 622298 626171 := bstep (se 1 (by rfl) ⟨469628, by rfl⟩ : syracuseStep 626171 = 939257) B939257
theorem B2854415 : Blo 622298 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B626239 : Blo 622298 626239 := bstep (se 1 (by rfl) ⟨469679, by rfl⟩ : syracuseStep 626239 = 939359) B939359
theorem B626247 : Blo 622298 626247 := bstep (se 1 (by rfl) ⟨469685, by rfl⟩ : syracuseStep 626247 = 939371) B939371
theorem B1576543 : Blo 622298 1576543 := bstep (se 1 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 1576543 = 2364815) B2364815
theorem B888617 : Blo 622298 888617 := bstep (se 2 (by rfl) ⟨333231, by rfl⟩ : syracuseStep 888617 = 666463) B666463
theorem B790327 : Blo 622298 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1052473 : Blo 622298 1052473 := bstep (se 2 (by rfl) ⟨394677, by rfl⟩ : syracuseStep 1052473 = 789355) B789355
theorem B655789891 : Blo 622298 655789891 := bstep (se 1 (by rfl) ⟨491842418, by rfl⟩ : syracuseStep 655789891 = 983684837) B983684837
theorem B1052777 : Blo 622298 1052777 := bstep (se 2 (by rfl) ⟨394791, by rfl⟩ : syracuseStep 1052777 = 789583) B789583
theorem B1577171 : Blo 622298 1577171 := bstep (se 1 (by rfl) ⟨1182878, by rfl⟩ : syracuseStep 1577171 = 2365757) B2365757
theorem B790823 : Blo 622298 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B889255 : Blo 622298 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B2101679 : Blo 622298 2101679 := bstep (se 1 (by rfl) ⟨1576259, by rfl⟩ : syracuseStep 2101679 = 3152519) B3152519
theorem B791147 : Blo 622298 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B2364025 : Blo 622298 2364025 := bstep (se 2 (by rfl) ⟨886509, by rfl⟩ : syracuseStep 2364025 = 1773019) B1773019
theorem B12030929 : Blo 622298 12030929 := bstep (se 2 (by rfl) ⟨4511598, by rfl⟩ : syracuseStep 12030929 = 9023197) B9023197
theorem B791527 : Blo 622298 791527 := bstep (se 1 (by rfl) ⟨593645, by rfl⟩ : syracuseStep 791527 = 1187291) B1187291
theorem B890075 : Blo 622298 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B2102651 : Blo 622298 2102651 := bstep (se 1 (by rfl) ⟨1576988, by rfl⟩ : syracuseStep 2102651 = 3153977) B3153977
theorem B1054201 : Blo 622298 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B3151547 : Blo 622298 3151547 := bstep (se 1 (by rfl) ⟨2363660, by rfl⟩ : syracuseStep 3151547 = 4727321) B4727321
theorem B12785339 : Blo 622298 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B1054471 : Blo 622298 1054471 := bstep (se 1 (by rfl) ⟨790853, by rfl⟩ : syracuseStep 1054471 = 1581707) B1581707
theorem B1054505 : Blo 622298 1054505 := bstep (se 2 (by rfl) ⟨395439, by rfl⟩ : syracuseStep 1054505 = 790879) B790879
theorem B2365271 : Blo 622298 2365271 := bstep (se 1 (by rfl) ⟨1773953, by rfl⟩ : syracuseStep 2365271 = 3547907) B3547907
theorem B1186159 : Blo 622298 1186159 := bstep (se 1 (by rfl) ⟨889619, by rfl⟩ : syracuseStep 1186159 = 1779239) B1779239
theorem B1579439 : Blo 622298 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B1055227 : Blo 622298 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B891499 : Blo 622298 891499 := bstep (se 1 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 891499 = 1337249) B1337249
theorem B2104055 : Blo 622298 2104055 := bstep (se 1 (by rfl) ⟨1578041, by rfl⟩ : syracuseStep 2104055 = 3156083) B3156083
theorem B1055659 : Blo 622298 1055659 := bstep (se 1 (by rfl) ⟨791744, by rfl⟩ : syracuseStep 1055659 = 1583489) B1583489
theorem B1776779 : Blo 622298 1776779 := bstep (se 1 (by rfl) ⟨1332584, by rfl⟩ : syracuseStep 1776779 = 2665169) B2665169
theorem B1055963 : Blo 622298 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B1580411 : Blo 622298 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B1056199 : Blo 622298 1056199 := bstep (se 1 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 1056199 = 1584299) B1584299
theorem B23076427 : Blo 622298 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B3153491 : Blo 622298 3153491 := bstep (se 1 (by rfl) ⟨2365118, by rfl⟩ : syracuseStep 3153491 = 4730237) B4730237
theorem B1580705 : Blo 622298 1580705 := bstep (se 2 (by rfl) ⟨592764, by rfl⟩ : syracuseStep 1580705 = 1185529) B1185529
theorem B2105135 : Blo 622298 2105135 := bstep (se 1 (by rfl) ⟨1578851, by rfl⟩ : syracuseStep 2105135 = 3157703) B3157703
theorem B1777565 : Blo 622298 1777565 := bstep (se 3 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 1777565 = 666587) B666587
theorem B1056719 : Blo 622298 1056719 := bstep (se 1 (by rfl) ⟨792539, by rfl⟩ : syracuseStep 1056719 = 1585079) B1585079
theorem B4726835 : Blo 622298 4726835 := bstep (se 1 (by rfl) ⟨3545126, by rfl⟩ : syracuseStep 4726835 = 7090253) B7090253
theorem B2662571 : Blo 622298 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B1581403 : Blo 622298 1581403 := bstep (se 1 (by rfl) ⟨1186052, by rfl⟩ : syracuseStep 1581403 = 2372105) B2372105
theorem B1188263 : Blo 622298 1188263 := bstep (se 1 (by rfl) ⟨891197, by rfl⟩ : syracuseStep 1188263 = 1782395) B1782395
theorem B6758923 : Blo 622298 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1582375 : Blo 622298 1582375 := bstep (se 1 (by rfl) ⟨1186781, by rfl⟩ : syracuseStep 1582375 = 2373563) B2373563
theorem B6399283 : Blo 622298 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B1582649 : Blo 622298 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B6006473 : Blo 622298 6006473 := bstep (se 2 (by rfl) ⟨2252427, by rfl⟩ : syracuseStep 6006473 = 4504855) B4504855
theorem B2991953 : Blo 622298 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B3385169 : Blo 622298 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B2107241 : Blo 622298 2107241 := bstep (se 2 (by rfl) ⟨790215, by rfl⟩ : syracuseStep 2107241 = 1580431) B1580431
theorem B2107673 : Blo 622298 2107673 := bstep (se 2 (by rfl) ⟨790377, by rfl⟩ : syracuseStep 2107673 = 1580755) B1580755
theorem B1124699 : Blo 622298 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B12003713 : Blo 622298 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B3156407 : Blo 622298 3156407 := bstep (se 1 (by rfl) ⟨2367305, by rfl⟩ : syracuseStep 3156407 = 4734611) B4734611
theorem B3549683 : Blo 622298 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B1354715 : Blo 622298 1354715 := bstep (se 1 (by rfl) ⟨1016036, by rfl⟩ : syracuseStep 1354715 = 2032073) B2032073
theorem B1584481 : Blo 622298 1584481 := bstep (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) B1188361
theorem B1781129 : Blo 622298 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B2109023 : Blo 622298 2109023 := bstep (se 1 (by rfl) ⟨1581767, by rfl⟩ : syracuseStep 2109023 = 3163535) B3163535
theorem B2141959 : Blo 622298 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B1126199 : Blo 622298 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B13512653 : Blo 622298 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B1683785 : Blo 622298 1683785 := bstep (se 2 (by rfl) ⟨631419, by rfl⟩ : syracuseStep 1683785 = 1262839) B1262839
theorem B4731209 : Blo 622298 4731209 := bstep (se 2 (by rfl) ⟨1774203, by rfl⟩ : syracuseStep 4731209 = 3548407) B3548407
theorem B2666843 : Blo 622298 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B1126747 : Blo 622298 1126747 := bstep (se 1 (by rfl) ⟨845060, by rfl⟩ : syracuseStep 1126747 = 1690121) B1690121
theorem B2732395 : Blo 622298 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B15151535 : Blo 622298 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B701023 : Blo 622298 701023 := bstep (se 1 (by rfl) ⟨525767, by rfl⟩ : syracuseStep 701023 = 1051535) B1051535
theorem B4010593 : Blo 622298 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B3158675 : Blo 622298 3158675 := bstep (se 1 (by rfl) ⟨2369006, by rfl⟩ : syracuseStep 3158675 = 4738013) B4738013
theorem B2110427 : Blo 622298 2110427 := bstep (se 1 (by rfl) ⟨1582820, by rfl⟩ : syracuseStep 2110427 = 3165641) B3165641
theorem B2110589 : Blo 622298 2110589 := bstep (se 3 (by rfl) ⟨395735, by rfl⟩ : syracuseStep 2110589 = 791471) B791471
theorem B2110697 : Blo 622298 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B2110859 : Blo 622298 2110859 := bstep (se 1 (by rfl) ⟨1583144, by rfl⟩ : syracuseStep 2110859 = 3166289) B3166289
theorem B9024929 : Blo 622298 9024929 := bstep (se 2 (by rfl) ⟨3384348, by rfl⟩ : syracuseStep 9024929 = 6768697) B6768697
theorem B800167 : Blo 622298 800167 := bstep (se 1 (by rfl) ⟨600125, by rfl⟩ : syracuseStep 800167 = 1200251) B1200251
theorem B3159485 : Blo 622298 3159485 := bstep (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) B1184807
theorem B996857 : Blo 622298 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B1783453 : Blo 622298 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B702175 : Blo 622298 702175 := bstep (se 1 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 702175 = 1053263) B1053263
theorem B702751 : Blo 622298 702751 := bstep (se 1 (by rfl) ⟨527063, by rfl⟩ : syracuseStep 702751 = 1054127) B1054127
theorem B2537839 : Blo 622298 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B801343 : Blo 622298 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B703039 : Blo 622298 703039 := bstep (se 1 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 703039 = 1054559) B1054559
theorem B1686089 : Blo 622298 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B2374217 : Blo 622298 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B703867 : Blo 622298 703867 := bstep (se 1 (by rfl) ⟨527900, by rfl⟩ : syracuseStep 703867 = 1055801) B1055801
theorem B1424827 : Blo 622298 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B933611 : Blo 622298 933611 := bstep (se 1 (by rfl) ⟨700208, by rfl⟩ : syracuseStep 933611 = 1400417) B1400417
theorem B704335 : Blo 622298 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B933839 : Blo 622298 933839 := bstep (se 1 (by rfl) ⟨700379, by rfl⟩ : syracuseStep 933839 = 1400759) B1400759
theorem B2375689 : Blo 622298 2375689 := bstep (se 2 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 2375689 = 1781767) B1781767
theorem B934235 : Blo 622298 934235 := bstep (se 1 (by rfl) ⟨700676, by rfl⟩ : syracuseStep 934235 = 1401353) B1401353
theorem B5325209 : Blo 622298 5325209 := bstep (se 2 (by rfl) ⟨1996953, by rfl⟩ : syracuseStep 5325209 = 3993907) B3993907
theorem B2376161 : Blo 622298 2376161 := bstep (se 2 (by rfl) ⟨891060, by rfl⟩ : syracuseStep 2376161 = 1782121) B1782121
theorem B934463 : Blo 622298 934463 := bstep (se 1 (by rfl) ⟨700847, by rfl⟩ : syracuseStep 934463 = 1401695) B1401695
theorem B18039469 : Blo 622298 18039469 := bstep (se 3 (by rfl) ⟨3382400, by rfl⟩ : syracuseStep 18039469 = 6764801) B6764801
theorem B934583 : Blo 622298 934583 := bstep (se 1 (by rfl) ⟨700937, by rfl⟩ : syracuseStep 934583 = 1401875) B1401875
theorem B2671319 : Blo 622298 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B8012621 : Blo 622298 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B934811 : Blo 622298 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B5129153 : Blo 622298 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B2737091 : Blo 622298 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B7128161 : Blo 622298 7128161 := bstep (se 2 (by rfl) ⟨2673060, by rfl⟩ : syracuseStep 7128161 = 5346121) B5346121
theorem B7324769 : Blo 622298 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B935207 : Blo 622298 935207 := bstep (se 1 (by rfl) ⟨701405, by rfl⟩ : syracuseStep 935207 = 1402811) B1402811
theorem B2671967 : Blo 622298 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B935291 : Blo 622298 935291 := bstep (se 1 (by rfl) ⟨701468, by rfl⟩ : syracuseStep 935291 = 1402937) B1402937
theorem B935417 : Blo 622298 935417 := bstep (se 2 (by rfl) ⟨350781, by rfl⟩ : syracuseStep 935417 = 701563) B701563
theorem B935519 : Blo 622298 935519 := bstep (se 1 (by rfl) ⟨701639, by rfl⟩ : syracuseStep 935519 = 1403279) B1403279
theorem B935735 : Blo 622298 935735 := bstep (se 1 (by rfl) ⟨701801, by rfl⟩ : syracuseStep 935735 = 1403603) B1403603
theorem B6408143 : Blo 622298 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B414566423 : Blo 622298 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B936041 : Blo 622298 936041 := bstep (se 2 (by rfl) ⟨351015, by rfl⟩ : syracuseStep 936041 = 702031) B702031
theorem B3164345 : Blo 622298 3164345 := bstep (se 2 (by rfl) ⟨1186629, by rfl⟩ : syracuseStep 3164345 = 2373259) B2373259
theorem B936359 : Blo 622298 936359 := bstep (se 1 (by rfl) ⟨702269, by rfl⟩ : syracuseStep 936359 = 1404539) B1404539
theorem B936443 : Blo 622298 936443 := bstep (se 1 (by rfl) ⟨702332, by rfl⟩ : syracuseStep 936443 = 1404665) B1404665
theorem B936569 : Blo 622298 936569 := bstep (se 2 (by rfl) ⟨351213, by rfl⟩ : syracuseStep 936569 = 702427) B702427
theorem B936623 : Blo 622298 936623 := bstep (se 1 (by rfl) ⟨702467, by rfl⟩ : syracuseStep 936623 = 1404935) B1404935
theorem B936671 : Blo 622298 936671 := bstep (se 1 (by rfl) ⟨702503, by rfl⟩ : syracuseStep 936671 = 1405007) B1405007
theorem B8014625 : Blo 622298 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B936935 : Blo 622298 936935 := bstep (se 1 (by rfl) ⟨702701, by rfl⟩ : syracuseStep 936935 = 1405403) B1405403
theorem B937193 : Blo 622298 937193 := bstep (se 2 (by rfl) ⟨351447, by rfl⟩ : syracuseStep 937193 = 702895) B702895
theorem B937247 : Blo 622298 937247 := bstep (se 1 (by rfl) ⟨702935, by rfl⟩ : syracuseStep 937247 = 1405871) B1405871
theorem B8998289 : Blo 622298 8998289 := bstep (se 2 (by rfl) ⟨3374358, by rfl⟩ : syracuseStep 8998289 = 6748717) B6748717
theorem B937415 : Blo 622298 937415 := bstep (se 1 (by rfl) ⟨703061, by rfl⟩ : syracuseStep 937415 = 1406123) B1406123
theorem B2674291 : Blo 622298 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B937769 : Blo 622298 937769 := bstep (se 2 (by rfl) ⟨351663, by rfl⟩ : syracuseStep 937769 = 703327) B703327
theorem B3002159 : Blo 622298 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B937775 : Blo 622298 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B3166127 : Blo 622298 3166127 := bstep (se 1 (by rfl) ⟨2374595, by rfl⟩ : syracuseStep 3166127 = 4749191) B4749191
theorem B1691657 : Blo 622298 1691657 := bstep (se 2 (by rfl) ⟨634371, by rfl⟩ : syracuseStep 1691657 = 1268743) B1268743
theorem B4509755 : Blo 622298 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B938249 : Blo 622298 938249 := bstep (se 2 (by rfl) ⟨351843, by rfl⟩ : syracuseStep 938249 = 703687) B703687
theorem B938351 : Blo 622298 938351 := bstep (se 1 (by rfl) ⟨703763, by rfl⟩ : syracuseStep 938351 = 1407527) B1407527
theorem B1266131 : Blo 622298 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B938567 : Blo 622298 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B938603 : Blo 622298 938603 := bstep (se 1 (by rfl) ⟨703952, by rfl⟩ : syracuseStep 938603 = 1407905) B1407905
theorem B938831 : Blo 622298 938831 := bstep (se 1 (by rfl) ⟨704123, by rfl⟩ : syracuseStep 938831 = 1408247) B1408247
theorem B939227 : Blo 622298 939227 := bstep (se 1 (by rfl) ⟨704420, by rfl⟩ : syracuseStep 939227 = 1408841) B1408841
theorem B3003641 : Blo 622298 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B939401 : Blo 622298 939401 := bstep (se 2 (by rfl) ⟨352275, by rfl⟩ : syracuseStep 939401 = 704551) B704551
theorem B2021021 : Blo 622298 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B1333199 : Blo 622298 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B3037313 : Blo 622298 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B3169043 : Blo 622298 3169043 := bstep (se 1 (by rfl) ⟨2376782, by rfl⟩ : syracuseStep 3169043 = 4753565) B4753565
theorem B3038077 : Blo 622298 3038077 := bstep (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) B1139279
theorem B1498331 : Blo 622298 1498331 := bstep (se 1 (by rfl) ⟨1123748, by rfl⟩ : syracuseStep 1498331 = 2247497) B2247497
theorem B6085853 : Blo 622298 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B13491467 : Blo 622298 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B1400201 : Blo 622298 1400201 := bstep (se 2 (by rfl) ⟨525075, by rfl⟩ : syracuseStep 1400201 = 1050151) B1050151
theorem B3366359 : Blo 622298 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B1400327 : Blo 622298 1400327 := bstep (se 1 (by rfl) ⟨1050245, by rfl⟩ : syracuseStep 1400327 = 2100491) B2100491
theorem B1400507 : Blo 622298 1400507 := bstep (se 1 (by rfl) ⟨1050380, by rfl⟩ : syracuseStep 1400507 = 2100761) B2100761
theorem B3366659 : Blo 622298 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B1498927 : Blo 622298 1498927 := bstep (se 1 (by rfl) ⟨1124195, by rfl⟩ : syracuseStep 1498927 = 2248391) B2248391
theorem B1400633 : Blo 622298 1400633 := bstep (se 2 (by rfl) ⟨525237, by rfl⟩ : syracuseStep 1400633 = 1050475) B1050475
theorem B3170177 : Blo 622298 3170177 := bstep (se 2 (by rfl) ⟨1188816, by rfl⟩ : syracuseStep 3170177 = 2377633) B2377633
theorem B15982595 : Blo 622298 15982595 := bstep (se 1 (by rfl) ⟨11986946, by rfl⟩ : syracuseStep 15982595 = 23973893) B23973893
theorem B5332999 : Blo 622298 5332999 := bstep (se 1 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 5332999 = 7999499) B7999499
theorem B5988401 : Blo 622298 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B5693651 : Blo 622298 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B4546979 : Blo 622298 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B1401263 : Blo 622298 1401263 := bstep (se 1 (by rfl) ⟨1050947, by rfl⟩ : syracuseStep 1401263 = 2101895) B2101895
theorem B1401299 : Blo 622298 1401299 := bstep (se 1 (by rfl) ⟨1050974, by rfl⟩ : syracuseStep 1401299 = 2101949) B2101949
theorem B1401407 : Blo 622298 1401407 := bstep (se 1 (by rfl) ⟨1051055, by rfl⟩ : syracuseStep 1401407 = 2102111) B2102111
theorem B1401515 : Blo 622298 1401515 := bstep (se 1 (by rfl) ⟨1051136, by rfl⟩ : syracuseStep 1401515 = 2102273) B2102273
theorem B1402055 : Blo 622298 1402055 := bstep (se 1 (by rfl) ⟨1051541, by rfl⟩ : syracuseStep 1402055 = 2103083) B2103083
theorem B22799681 : Blo 622298 22799681 := bstep (se 2 (by rfl) ⟨8549880, by rfl⟩ : syracuseStep 22799681 = 17099761) B17099761
theorem B1402235 : Blo 622298 1402235 := bstep (se 1 (by rfl) ⟨1051676, by rfl⟩ : syracuseStep 1402235 = 2103353) B2103353
theorem B5989783 : Blo 622298 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1402361 : Blo 622298 1402361 := bstep (se 2 (by rfl) ⟨525885, by rfl⟩ : syracuseStep 1402361 = 1051771) B1051771
theorem B1402451 : Blo 622298 1402451 := bstep (se 1 (by rfl) ⟨1051838, by rfl⟩ : syracuseStep 1402451 = 2103677) B2103677
theorem B845407 : Blo 622298 845407 := bstep (se 1 (by rfl) ⟨634055, by rfl⟩ : syracuseStep 845407 = 1268111) B1268111
theorem B1402631 : Blo 622298 1402631 := bstep (se 1 (by rfl) ⟨1051973, by rfl⟩ : syracuseStep 1402631 = 2103947) B2103947
theorem B2025607 : Blo 622298 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B3205385 : Blo 622298 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B1403243 : Blo 622298 1403243 := bstep (se 1 (by rfl) ⟨1052432, by rfl⟩ : syracuseStep 1403243 = 2104865) B2104865
theorem B1403387 : Blo 622298 1403387 := bstep (se 1 (by rfl) ⟨1052540, by rfl⟩ : syracuseStep 1403387 = 2105081) B2105081
theorem B3238463 : Blo 622298 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B1796681 : Blo 622298 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1403513 : Blo 622298 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B1403567 : Blo 622298 1403567 := bstep (se 1 (by rfl) ⟨1052675, by rfl⟩ : syracuseStep 1403567 = 2105351) B2105351
theorem B2878199 : Blo 622298 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B1403639 : Blo 622298 1403639 := bstep (se 1 (by rfl) ⟨1052729, by rfl⟩ : syracuseStep 1403639 = 2105459) B2105459
theorem B3009271 : Blo 622298 3009271 := bstep (se 1 (by rfl) ⟨2256953, by rfl⟩ : syracuseStep 3009271 = 4513907) B4513907
theorem B1403819 : Blo 622298 1403819 := bstep (se 1 (by rfl) ⟨1052864, by rfl⟩ : syracuseStep 1403819 = 2105729) B2105729
theorem B3370099 : Blo 622298 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B1895879 : Blo 622298 1895879 := bstep (se 1 (by rfl) ⟨1421909, by rfl⟩ : syracuseStep 1895879 = 2843819) B2843819
theorem B1404359 : Blo 622298 1404359 := bstep (se 1 (by rfl) ⟨1053269, by rfl⟩ : syracuseStep 1404359 = 2106539) B2106539
theorem B4746761 : Blo 622298 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B1404719 : Blo 622298 1404719 := bstep (se 1 (by rfl) ⟨1053539, by rfl⟩ : syracuseStep 1404719 = 2107079) B2107079
theorem B1994777 : Blo 622298 1994777 := bstep (se 2 (by rfl) ⟨748041, by rfl⟩ : syracuseStep 1994777 = 1496083) B1496083
theorem B1405295 : Blo 622298 1405295 := bstep (se 1 (by rfl) ⟨1053971, by rfl⟩ : syracuseStep 1405295 = 2107943) B2107943
theorem B1405367 : Blo 622298 1405367 := bstep (se 1 (by rfl) ⟨1054025, by rfl⟩ : syracuseStep 1405367 = 2108051) B2108051
theorem B3371483 : Blo 622298 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B1012295 : Blo 622298 1012295 := bstep (se 1 (by rfl) ⟨759221, by rfl⟩ : syracuseStep 1012295 = 1518443) B1518443
theorem B1405511 : Blo 622298 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B1405547 : Blo 622298 1405547 := bstep (se 1 (by rfl) ⟨1054160, by rfl⟩ : syracuseStep 1405547 = 2108321) B2108321
theorem B10646315 : Blo 622298 10646315 := bstep (se 1 (by rfl) ⟨7984736, by rfl⟩ : syracuseStep 10646315 = 15969473) B15969473
theorem B1504079 : Blo 622298 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B1405943 : Blo 622298 1405943 := bstep (se 1 (by rfl) ⟨1054457, by rfl⟩ : syracuseStep 1405943 = 2108915) B2108915
theorem B1406303 : Blo 622298 1406303 := bstep (se 1 (by rfl) ⟨1054727, by rfl⟩ : syracuseStep 1406303 = 2109455) B2109455
theorem B4748705 : Blo 622298 4748705 := bstep (se 2 (by rfl) ⟨1780764, by rfl⟩ : syracuseStep 4748705 = 3561529) B3561529
theorem B1406699 : Blo 622298 1406699 := bstep (se 1 (by rfl) ⟨1055024, by rfl⟩ : syracuseStep 1406699 = 2110049) B2110049
theorem B1406825 : Blo 622298 1406825 := bstep (se 2 (by rfl) ⟨527559, by rfl⟩ : syracuseStep 1406825 = 1055119) B1055119
theorem B12843143 : Blo 622298 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B1800767 : Blo 622298 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B4815467 : Blo 622298 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B1407671 : Blo 622298 1407671 := bstep (se 1 (by rfl) ⟨1055753, by rfl⟩ : syracuseStep 1407671 = 2111507) B2111507
theorem B1407887 : Blo 622298 1407887 := bstep (se 1 (by rfl) ⟨1055915, by rfl⟩ : syracuseStep 1407887 = 2111831) B2111831
theorem B1997723 : Blo 622298 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B7306363 : Blo 622298 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B1408607 : Blo 622298 1408607 := bstep (se 1 (by rfl) ⟨1056455, by rfl⟩ : syracuseStep 1408607 = 2112911) B2112911
theorem B622303 : Blo 622298 622303 := bstep (se 1 (by rfl) ⟨466727, by rfl⟩ : syracuseStep 622303 = 933455) B933455
theorem B622383 : Blo 622298 622383 := bstep (se 1 (by rfl) ⟨466787, by rfl⟩ : syracuseStep 622383 = 933575) B933575
theorem B1408823 : Blo 622298 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B622491 : Blo 622298 622491 := bstep (se 1 (by rfl) ⟨466868, by rfl⟩ : syracuseStep 622491 = 933737) B933737
theorem B622543 : Blo 622298 622543 := bstep (se 1 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 622543 = 933815) B933815
theorem B622567 : Blo 622298 622567 := bstep (se 1 (by rfl) ⟨466925, by rfl⟩ : syracuseStep 622567 = 933851) B933851
theorem B7110665 : Blo 622298 7110665 := bstep (se 2 (by rfl) ⟨2666499, by rfl⟩ : syracuseStep 7110665 = 5332999) B5332999
theorem B3801167 : Blo 622298 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B622823 : Blo 622298 622823 := bstep (se 1 (by rfl) ⟨467117, by rfl⟩ : syracuseStep 622823 = 934235) B934235
theorem B622975 : Blo 622298 622975 := bstep (se 1 (by rfl) ⟨467231, by rfl⟩ : syracuseStep 622975 = 934463) B934463
theorem B623055 : Blo 622298 623055 := bstep (se 1 (by rfl) ⟨467291, by rfl⟩ : syracuseStep 623055 = 934583) B934583
theorem B5341747 : Blo 622298 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B623207 : Blo 622298 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B3998315 : Blo 622298 3998315 := bstep (se 1 (by rfl) ⟨2998736, by rfl⟩ : syracuseStep 3998315 = 5997473) B5997473
theorem B9011897 : Blo 622298 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B4752107 : Blo 622298 4752107 := bstep (se 1 (by rfl) ⟨3564080, by rfl⟩ : syracuseStep 4752107 = 7128161) B7128161
theorem B4883179 : Blo 622298 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B4490093 : Blo 622298 4490093 := bstep (se 3 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 4490093 = 1683785) B1683785
theorem B623471 : Blo 622298 623471 := bstep (se 1 (by rfl) ⟨467603, by rfl⟩ : syracuseStep 623471 = 935207) B935207
theorem B24052625 : Blo 622298 24052625 := bstep (se 2 (by rfl) ⟨9019734, by rfl⟩ : syracuseStep 24052625 = 18039469) B18039469
theorem B623527 : Blo 622298 623527 := bstep (se 1 (by rfl) ⟨467645, by rfl⟩ : syracuseStep 623527 = 935291) B935291
theorem B623611 : Blo 622298 623611 := bstep (se 1 (by rfl) ⟨467708, by rfl⟩ : syracuseStep 623611 = 935417) B935417
theorem B623679 : Blo 622298 623679 := bstep (se 1 (by rfl) ⟨467759, by rfl⟩ : syracuseStep 623679 = 935519) B935519
theorem B623823 : Blo 622298 623823 := bstep (se 1 (by rfl) ⟨467867, by rfl⟩ : syracuseStep 623823 = 935735) B935735
theorem B3376349 : Blo 622298 3376349 := bstep (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) B1266131
theorem B20186455 : Blo 622298 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B624027 : Blo 622298 624027 := bstep (se 1 (by rfl) ⟨468020, by rfl⟩ : syracuseStep 624027 = 936041) B936041
theorem B7997039 : Blo 622298 7997039 := bstep (se 1 (by rfl) ⟨5997779, by rfl⟩ : syracuseStep 7997039 = 11995559) B11995559
theorem B624239 : Blo 622298 624239 := bstep (se 1 (by rfl) ⟨468179, by rfl⟩ : syracuseStep 624239 = 936359) B936359
theorem B624295 : Blo 622298 624295 := bstep (se 1 (by rfl) ⟨468221, by rfl⟩ : syracuseStep 624295 = 936443) B936443
theorem B624379 : Blo 622298 624379 := bstep (se 1 (by rfl) ⟨468284, by rfl⟩ : syracuseStep 624379 = 936569) B936569
theorem B624415 : Blo 622298 624415 := bstep (se 1 (by rfl) ⟨468311, by rfl⟩ : syracuseStep 624415 = 936623) B936623
theorem B788287 : Blo 622298 788287 := bstep (se 1 (by rfl) ⟨591215, by rfl⟩ : syracuseStep 788287 = 1182431) B1182431
theorem B624447 : Blo 622298 624447 := bstep (se 1 (by rfl) ⟨468335, by rfl⟩ : syracuseStep 624447 = 936671) B936671
theorem B5343083 : Blo 622298 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B624623 : Blo 622298 624623 := bstep (se 1 (by rfl) ⟨468467, by rfl⟩ : syracuseStep 624623 = 936935) B936935
theorem B1050617 : Blo 622298 1050617 := bstep (se 2 (by rfl) ⟨393981, by rfl⟩ : syracuseStep 1050617 = 787963) B787963
theorem B1050779 : Blo 622298 1050779 := bstep (se 1 (by rfl) ⟨788084, by rfl⟩ : syracuseStep 1050779 = 1576169) B1576169
theorem B624795 : Blo 622298 624795 := bstep (se 1 (by rfl) ⟨468596, by rfl⟩ : syracuseStep 624795 = 937193) B937193
theorem B624831 : Blo 622298 624831 := bstep (se 1 (by rfl) ⟨468623, by rfl⟩ : syracuseStep 624831 = 937247) B937247
theorem B3999955 : Blo 622298 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B1050887 : Blo 622298 1050887 := bstep (se 1 (by rfl) ⟨788165, by rfl⟩ : syracuseStep 1050887 = 1576331) B1576331
theorem B5998859 : Blo 622298 5998859 := bstep (se 1 (by rfl) ⟨4499144, by rfl⟩ : syracuseStep 5998859 = 8998289) B8998289
theorem B624943 : Blo 622298 624943 := bstep (se 1 (by rfl) ⟨468707, by rfl⟩ : syracuseStep 624943 = 937415) B937415
theorem B1902943 : Blo 622298 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B625179 : Blo 622298 625179 := bstep (se 1 (by rfl) ⟨468884, by rfl⟩ : syracuseStep 625179 = 937769) B937769
theorem B2001439 : Blo 622298 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B625183 : Blo 622298 625183 := bstep (se 1 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 625183 = 937775) B937775
theorem B1051447 : Blo 622298 1051447 := bstep (se 1 (by rfl) ⟨788585, by rfl⟩ : syracuseStep 1051447 = 1577171) B1577171
theorem B625499 : Blo 622298 625499 := bstep (se 1 (by rfl) ⟨469124, by rfl⟩ : syracuseStep 625499 = 938249) B938249
theorem B625567 : Blo 622298 625567 := bstep (se 1 (by rfl) ⟨469175, by rfl⟩ : syracuseStep 625567 = 938351) B938351
theorem B625711 : Blo 622298 625711 := bstep (se 1 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 625711 = 938567) B938567
theorem B625735 : Blo 622298 625735 := bstep (se 1 (by rfl) ⟨469301, by rfl⟩ : syracuseStep 625735 = 938603) B938603
theorem B1576057 : Blo 622298 1576057 := bstep (se 2 (by rfl) ⟨591021, by rfl⟩ : syracuseStep 1576057 = 1182043) B1182043
theorem B625887 : Blo 622298 625887 := bstep (se 1 (by rfl) ⟨469415, by rfl⟩ : syracuseStep 625887 = 938831) B938831
theorem B1051913 : Blo 622298 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B1576361 : Blo 622298 1576361 := bstep (se 2 (by rfl) ⟨591135, by rfl⟩ : syracuseStep 1576361 = 1182271) B1182271
theorem B626151 : Blo 622298 626151 := bstep (se 1 (by rfl) ⟨469613, by rfl⟩ : syracuseStep 626151 = 939227) B939227
theorem B2002427 : Blo 622298 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B13897277 : Blo 622298 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B626267 : Blo 622298 626267 := bstep (se 1 (by rfl) ⟨469700, by rfl⟩ : syracuseStep 626267 = 939401) B939401
theorem B1347347 : Blo 622298 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B2101031 : Blo 622298 2101031 := bstep (se 1 (by rfl) ⟨1575773, by rfl⟩ : syracuseStep 2101031 = 3151547) B3151547
theorem B8523559 : Blo 622298 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1576847 : Blo 622298 1576847 := bstep (se 1 (by rfl) ⟨1182635, by rfl⟩ : syracuseStep 1576847 = 2365271) B2365271
theorem B4493465 : Blo 622298 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B1052959 : Blo 622298 1052959 := bstep (se 1 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 1052959 = 1579439) B1579439
theorem B1577353 : Blo 622298 1577353 := bstep (se 2 (by rfl) ⟨591507, by rfl⟩ : syracuseStep 1577353 = 1183015) B1183015
theorem B1577465 : Blo 622298 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B1184519 : Blo 622298 1184519 := bstep (se 1 (by rfl) ⟨888389, by rfl⟩ : syracuseStep 1184519 = 1776779) B1776779
theorem B2102057 : Blo 622298 2102057 := bstep (se 2 (by rfl) ⟨788271, by rfl⟩ : syracuseStep 2102057 = 1576543) B1576543
theorem B1053607 : Blo 622298 1053607 := bstep (se 1 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 1053607 = 1580411) B1580411
theorem B2855945 : Blo 622298 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B2102327 : Blo 622298 2102327 := bstep (se 1 (by rfl) ⟨1576745, by rfl⟩ : syracuseStep 2102327 = 3153491) B3153491
theorem B1053769 : Blo 622298 1053769 := bstep (se 2 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 1053769 = 790327) B790327
theorem B874386521 : Blo 622298 874386521 := bstep (se 2 (by rfl) ⟨327894945, by rfl⟩ : syracuseStep 874386521 = 655789891) B655789891
theorem B1053803 : Blo 622298 1053803 := bstep (se 1 (by rfl) ⟨790352, by rfl⟩ : syracuseStep 1053803 = 1580705) B1580705
theorem B1185043 : Blo 622298 1185043 := bstep (se 1 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 1185043 = 1777565) B1777565
theorem B10655063 : Blo 622298 10655063 := bstep (se 1 (by rfl) ⟨7991297, by rfl⟩ : syracuseStep 10655063 = 15982595) B15982595
theorem B3151223 : Blo 622298 3151223 := bstep (se 1 (by rfl) ⟨2363417, by rfl⟩ : syracuseStep 3151223 = 4726835) B4726835
theorem B1775047 : Blo 622298 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B792175 : Blo 622298 792175 := bstep (se 1 (by rfl) ⟨594131, by rfl⟩ : syracuseStep 792175 = 1188263) B1188263
theorem B3643193 : Blo 622298 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B1185673 : Blo 622298 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B5347457 : Blo 622298 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B3152033 : Blo 622298 3152033 := bstep (se 2 (by rfl) ⟨1182012, by rfl⟩ : syracuseStep 3152033 = 2364025) B2364025
theorem B1055099 : Blo 622298 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B4004315 : Blo 622298 4004315 := bstep (se 1 (by rfl) ⟨3003236, by rfl⟩ : syracuseStep 4004315 = 6006473) B6006473
theorem B1055369 : Blo 622298 1055369 := bstep (se 2 (by rfl) ⟨395763, by rfl⟩ : syracuseStep 1055369 = 791527) B791527
theorem B2136923 : Blo 622298 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B8002475 : Blo 622298 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B2104271 : Blo 622298 2104271 := bstep (se 1 (by rfl) ⟨1578203, by rfl⟩ : syracuseStep 2104271 = 3156407) B3156407
theorem B2366455 : Blo 622298 2366455 := bstep (se 1 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 2366455 = 3549683) B3549683
theorem B3154139 : Blo 622298 3154139 := bstep (se 1 (by rfl) ⟨2365604, by rfl⟩ : syracuseStep 3154139 = 4731209) B4731209
theorem B1777895 : Blo 622298 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B10101023 : Blo 622298 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B3154301 : Blo 622298 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B2105783 : Blo 622298 2105783 := bstep (se 1 (by rfl) ⟨1579337, by rfl⟩ : syracuseStep 2105783 = 3158675) B3158675
theorem B1581545 : Blo 622298 1581545 := bstep (se 2 (by rfl) ⟨593079, by rfl⟩ : syracuseStep 1581545 = 1186159) B1186159
theorem B3383785 : Blo 622298 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B1188665 : Blo 622298 1188665 := bstep (se 2 (by rfl) ⟨445749, by rfl⟩ : syracuseStep 1188665 = 891499) B891499
theorem B2106269 : Blo 622298 2106269 := bstep (se 3 (by rfl) ⟨394925, by rfl⟩ : syracuseStep 2106269 = 789851) B789851
theorem B2106323 : Blo 622298 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B664571 : Blo 622298 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B8562095 : Blo 622298 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B9741817 : Blo 622298 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B1582811 : Blo 622298 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B1124059 : Blo 622298 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B2369645 : Blo 622298 2369645 := bstep (se 3 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 2369645 = 888617) B888617
theorem B3550139 : Blo 622298 3550139 := bstep (se 1 (by rfl) ⟨2662604, by rfl⟩ : syracuseStep 3550139 = 5325209) B5325209
theorem B1584107 : Blo 622298 1584107 := bstep (se 1 (by rfl) ⟨1188080, by rfl⟩ : syracuseStep 1584107 = 2376161) B2376161
theorem B2108537 : Blo 622298 2108537 := bstep (se 2 (by rfl) ⟨790701, by rfl⟩ : syracuseStep 2108537 = 1581403) B1581403
theorem B1780879 : Blo 622298 1780879 := bstep (se 1 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 1780879 = 2671319) B2671319
theorem B3419435 : Blo 622298 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2108861 : Blo 622298 2108861 := bstep (se 3 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 2108861 = 790823) B790823
theorem B5680801 : Blo 622298 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B700231 : Blo 622298 700231 := bstep (se 1 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 700231 = 1050347) B1050347
theorem B8990621 : Blo 622298 8990621 := bstep (se 3 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 8990621 = 3371483) B3371483
theorem B4272095 : Blo 622298 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B276377615 : Blo 622298 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B2109563 : Blo 622298 2109563 := bstep (se 1 (by rfl) ⟨1582172, by rfl⟩ : syracuseStep 2109563 = 3164345) B3164345
theorem B2699453 : Blo 622298 2699453 := bstep (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) B1012295
theorem B2109725 : Blo 622298 2109725 := bstep (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) B791147
theorem B2109833 : Blo 622298 2109833 := bstep (se 2 (by rfl) ⟨791187, by rfl⟩ : syracuseStep 2109833 = 1582375) B1582375
theorem B8532377 : Blo 622298 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B700879 : Blo 622298 700879 := bstep (se 1 (by rfl) ⟨525659, by rfl⟩ : syracuseStep 700879 = 1051319) B1051319
theorem B1127209 : Blo 622298 1127209 := bstep (se 2 (by rfl) ⟨422703, by rfl⟩ : syracuseStep 1127209 = 845407) B845407
theorem B2667593 : Blo 622298 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B2110751 : Blo 622298 2110751 := bstep (se 1 (by rfl) ⟨1583063, by rfl⟩ : syracuseStep 2110751 = 3166127) B3166127
theorem B1127771 : Blo 622298 1127771 := bstep (se 1 (by rfl) ⟨845828, by rfl⟩ : syracuseStep 1127771 = 1691657) B1691657
theorem B701851 : Blo 622298 701851 := bstep (se 1 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 701851 = 1052777) B1052777
theorem B2700809 : Blo 622298 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B38975185 : Blo 622298 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B8763125 : Blo 622298 8763125 := bstep (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) B821543
theorem B2373533 : Blo 622298 2373533 := bstep (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) B890075
theorem B7125245 : Blo 622298 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B4012361 : Blo 622298 4012361 := bstep (se 2 (by rfl) ⟨1504635, by rfl⟩ : syracuseStep 4012361 = 3009271) B3009271
theorem B703003 : Blo 622298 703003 := bstep (se 1 (by rfl) ⟨527252, by rfl⟩ : syracuseStep 703003 = 1054505) B1054505
theorem B2112641 : Blo 622298 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B2112695 : Blo 622298 2112695 := bstep (se 1 (by rfl) ⟨1584521, by rfl⟩ : syracuseStep 2112695 = 3169043) B3169043
theorem B998887 : Blo 622298 998887 := bstep (se 1 (by rfl) ⟨749165, by rfl⟩ : syracuseStep 998887 = 1498331) B1498331
theorem B703975 : Blo 622298 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B8994311 : Blo 622298 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B933467 : Blo 622298 933467 := bstep (se 1 (by rfl) ⟨700100, by rfl⟩ : syracuseStep 933467 = 1400201) B1400201
theorem B2244239 : Blo 622298 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B933551 : Blo 622298 933551 := bstep (se 1 (by rfl) ⟨700163, by rfl⟩ : syracuseStep 933551 = 1400327) B1400327
theorem B933671 : Blo 622298 933671 := bstep (se 1 (by rfl) ⟨700253, by rfl⟩ : syracuseStep 933671 = 1400507) B1400507
theorem B2244439 : Blo 622298 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B933755 : Blo 622298 933755 := bstep (se 1 (by rfl) ⟨700316, by rfl⟩ : syracuseStep 933755 = 1400633) B1400633
theorem B3555197 : Blo 622298 3555197 := bstep (se 3 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 3555197 = 1333199) B1333199
theorem B2113451 : Blo 622298 2113451 := bstep (se 1 (by rfl) ⟨1585088, by rfl⟩ : syracuseStep 2113451 = 3170177) B3170177
theorem B704479 : Blo 622298 704479 := bstep (se 1 (by rfl) ⟨528359, by rfl⟩ : syracuseStep 704479 = 1056719) B1056719
theorem B3031319 : Blo 622298 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B934175 : Blo 622298 934175 := bstep (se 1 (by rfl) ⟨700631, by rfl⟩ : syracuseStep 934175 = 1401263) B1401263
theorem B934199 : Blo 622298 934199 := bstep (se 1 (by rfl) ⟨700649, by rfl⟩ : syracuseStep 934199 = 1401299) B1401299
theorem B934271 : Blo 622298 934271 := bstep (se 1 (by rfl) ⟨700703, by rfl⟩ : syracuseStep 934271 = 1401407) B1401407
theorem B934343 : Blo 622298 934343 := bstep (se 1 (by rfl) ⟨700757, by rfl⟩ : syracuseStep 934343 = 1401515) B1401515
theorem B934697 : Blo 622298 934697 := bstep (se 2 (by rfl) ⟨350511, by rfl⟩ : syracuseStep 934697 = 701023) B701023
theorem B934703 : Blo 622298 934703 := bstep (se 1 (by rfl) ⟨701027, by rfl⟩ : syracuseStep 934703 = 1402055) B1402055
theorem B2999197 : Blo 622298 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B934823 : Blo 622298 934823 := bstep (se 1 (by rfl) ⟨701117, by rfl⟩ : syracuseStep 934823 = 1402235) B1402235
theorem B934907 : Blo 622298 934907 := bstep (se 1 (by rfl) ⟨701180, by rfl⟩ : syracuseStep 934907 = 1402361) B1402361
theorem B934967 : Blo 622298 934967 := bstep (se 1 (by rfl) ⟨701225, by rfl⟩ : syracuseStep 934967 = 1402451) B1402451
theorem B935087 : Blo 622298 935087 := bstep (se 1 (by rfl) ⟨701315, by rfl⟩ : syracuseStep 935087 = 1402631) B1402631
theorem B8635901 : Blo 622298 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B935495 : Blo 622298 935495 := bstep (se 1 (by rfl) ⟨701621, by rfl⟩ : syracuseStep 935495 = 1403243) B1403243
theorem B935591 : Blo 622298 935591 := bstep (se 1 (by rfl) ⟨701693, by rfl⟩ : syracuseStep 935591 = 1403387) B1403387
theorem B1197787 : Blo 622298 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B935675 : Blo 622298 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B935711 : Blo 622298 935711 := bstep (se 1 (by rfl) ⟨701783, by rfl⟩ : syracuseStep 935711 = 1403567) B1403567
theorem B1918799 : Blo 622298 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B935759 : Blo 622298 935759 := bstep (se 1 (by rfl) ⟨701819, by rfl⟩ : syracuseStep 935759 = 1403639) B1403639
theorem B1066889 : Blo 622298 1066889 := bstep (se 2 (by rfl) ⟨400083, by rfl⟩ : syracuseStep 1066889 = 800167) B800167
theorem B935879 : Blo 622298 935879 := bstep (se 1 (by rfl) ⟨701909, by rfl⟩ : syracuseStep 935879 = 1403819) B1403819
theorem B903143 : Blo 622298 903143 := bstep (se 1 (by rfl) ⟨677357, by rfl⟩ : syracuseStep 903143 = 1354715) B1354715
theorem B2377937 : Blo 622298 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B936233 : Blo 622298 936233 := bstep (se 2 (by rfl) ⟨351087, by rfl⟩ : syracuseStep 936233 = 702175) B702175
theorem B1263919 : Blo 622298 1263919 := bstep (se 1 (by rfl) ⟨947939, by rfl⟩ : syracuseStep 1263919 = 1895879) B1895879
theorem B936239 : Blo 622298 936239 := bstep (se 1 (by rfl) ⟨702179, by rfl⟩ : syracuseStep 936239 = 1404359) B1404359
theorem B3164507 : Blo 622298 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B936479 : Blo 622298 936479 := bstep (se 1 (by rfl) ⟨702359, by rfl⟩ : syracuseStep 936479 = 1404719) B1404719
theorem B1329851 : Blo 622298 1329851 := bstep (se 1 (by rfl) ⟨997388, by rfl⟩ : syracuseStep 1329851 = 1994777) B1994777
theorem B936863 : Blo 622298 936863 := bstep (se 1 (by rfl) ⟨702647, by rfl⟩ : syracuseStep 936863 = 1405295) B1405295
theorem B936911 : Blo 622298 936911 := bstep (se 1 (by rfl) ⟨702683, by rfl⟩ : syracuseStep 936911 = 1405367) B1405367
theorem B937001 : Blo 622298 937001 := bstep (se 2 (by rfl) ⟨351375, by rfl⟩ : syracuseStep 937001 = 702751) B702751
theorem B937007 : Blo 622298 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B937031 : Blo 622298 937031 := bstep (se 1 (by rfl) ⟨702773, by rfl⟩ : syracuseStep 937031 = 1405547) B1405547
theorem B7097543 : Blo 622298 7097543 := bstep (se 1 (by rfl) ⟨5323157, by rfl⟩ : syracuseStep 7097543 = 10646315) B10646315
theorem B1002719 : Blo 622298 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B937295 : Blo 622298 937295 := bstep (se 1 (by rfl) ⟨702971, by rfl⟩ : syracuseStep 937295 = 1405943) B1405943
theorem B1068457 : Blo 622298 1068457 := bstep (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) B801343
theorem B937385 : Blo 622298 937385 := bstep (se 2 (by rfl) ⟨351519, by rfl⟩ : syracuseStep 937385 = 703039) B703039
theorem B937535 : Blo 622298 937535 := bstep (se 1 (by rfl) ⟨703151, by rfl⟩ : syracuseStep 937535 = 1406303) B1406303
theorem B3165803 : Blo 622298 3165803 := bstep (se 1 (by rfl) ⟨2374352, by rfl⟩ : syracuseStep 3165803 = 4748705) B4748705
theorem B6016619 : Blo 622298 6016619 := bstep (se 1 (by rfl) ⟨4512464, by rfl⟩ : syracuseStep 6016619 = 9024929) B9024929
theorem B937799 : Blo 622298 937799 := bstep (se 1 (by rfl) ⟨703349, by rfl⟩ : syracuseStep 937799 = 1406699) B1406699
theorem B4050769 : Blo 622298 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B937883 : Blo 622298 937883 := bstep (se 1 (by rfl) ⟨703412, by rfl⟩ : syracuseStep 937883 = 1406825) B1406825
theorem B1200511 : Blo 622298 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B938447 : Blo 622298 938447 := bstep (se 1 (by rfl) ⟨703835, by rfl⟩ : syracuseStep 938447 = 1407671) B1407671
theorem B938489 : Blo 622298 938489 := bstep (se 2 (by rfl) ⟨351933, by rfl⟩ : syracuseStep 938489 = 703867) B703867
theorem B938591 : Blo 622298 938591 := bstep (se 1 (by rfl) ⟨703943, by rfl⟩ : syracuseStep 938591 = 1407887) B1407887
theorem B1331815 : Blo 622298 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B939071 : Blo 622298 939071 := bstep (se 1 (by rfl) ⟨704303, by rfl⟩ : syracuseStep 939071 = 1408607) B1408607
theorem B939113 : Blo 622298 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B939215 : Blo 622298 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B3167585 : Blo 622298 3167585 := bstep (se 2 (by rfl) ⟨1187844, by rfl⟩ : syracuseStep 3167585 = 2375689) B2375689
theorem B939419 : Blo 622298 939419 := bstep (se 1 (by rfl) ⟨704564, by rfl⟩ : syracuseStep 939419 = 1409129) B1409129
theorem B7100459 : Blo 622298 7100459 := bstep (se 1 (by rfl) ⟨5325344, by rfl⟩ : syracuseStep 7100459 = 10650689) B10650689
theorem B17127787 : Blo 622298 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B2709883 : Blo 622298 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B5069449 : Blo 622298 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B3562487 : Blo 622298 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B7986377 : Blo 622298 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B1400399 : Blo 622298 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B7298909 : Blo 622298 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B3006503 : Blo 622298 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B1401119 : Blo 622298 1401119 := bstep (se 1 (by rfl) ⟨1050839, by rfl⟩ : syracuseStep 1401119 = 2101679) B2101679
theorem B8020619 : Blo 622298 8020619 := bstep (se 1 (by rfl) ⟨6015464, by rfl⟩ : syracuseStep 8020619 = 12030929) B12030929
theorem B1401767 : Blo 622298 1401767 := bstep (se 1 (by rfl) ⟨1051325, by rfl⟩ : syracuseStep 1401767 = 2102651) B2102651
theorem B6514057 : Blo 622298 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B2024875 : Blo 622298 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B1402703 : Blo 622298 1402703 := bstep (se 1 (by rfl) ⟨1052027, by rfl⟩ : syracuseStep 1402703 = 2104055) B2104055
theorem B1402721 : Blo 622298 1402721 := bstep (se 2 (by rfl) ⟨526020, by rfl⟩ : syracuseStep 1402721 = 1052041) B1052041
theorem B4057235 : Blo 622298 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B3565721 : Blo 622298 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B1403297 : Blo 622298 1403297 := bstep (se 2 (by rfl) ⟨526236, by rfl⟩ : syracuseStep 1403297 = 1052473) B1052473
theorem B1403423 : Blo 622298 1403423 := bstep (se 1 (by rfl) ⟨1052567, by rfl⟩ : syracuseStep 1403423 = 2105135) B2105135
theorem B3992267 : Blo 622298 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B3795767 : Blo 622298 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B1502329 : Blo 622298 1502329 := bstep (se 2 (by rfl) ⟨563373, by rfl⟩ : syracuseStep 1502329 = 1126747) B1126747
theorem B15199787 : Blo 622298 15199787 := bstep (se 1 (by rfl) ⟨11399840, by rfl⟩ : syracuseStep 15199787 = 22799681) B22799681
theorem B1994635 : Blo 622298 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B2256779 : Blo 622298 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B1404827 : Blo 622298 1404827 := bstep (se 1 (by rfl) ⟨1053620, by rfl⟩ : syracuseStep 1404827 = 2107241) B2107241
theorem B1405115 : Blo 622298 1405115 := bstep (se 1 (by rfl) ⟨1053836, by rfl⟩ : syracuseStep 1405115 = 2107673) B2107673
theorem B5337373 : Blo 622298 5337373 := bstep (se 3 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 5337373 = 2001515) B2001515
theorem B1405601 : Blo 622298 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B1405961 : Blo 622298 1405961 := bstep (se 2 (by rfl) ⟨527235, by rfl⟩ : syracuseStep 1405961 = 1054471) B1054471
theorem B1406015 : Blo 622298 1406015 := bstep (se 1 (by rfl) ⟨1054511, by rfl⟩ : syracuseStep 1406015 = 2109023) B2109023
theorem B750799 : Blo 622298 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B9008435 : Blo 622298 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B1406951 : Blo 622298 1406951 := bstep (se 1 (by rfl) ⟨1055213, by rfl⟩ : syracuseStep 1406951 = 2110427) B2110427
theorem B1406969 : Blo 622298 1406969 := bstep (se 2 (by rfl) ⟨527613, by rfl⟩ : syracuseStep 1406969 = 1055227) B1055227
theorem B1407059 : Blo 622298 1407059 := bstep (se 1 (by rfl) ⟨1055294, by rfl⟩ : syracuseStep 1407059 = 2110589) B2110589
theorem B1407131 : Blo 622298 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B1407239 : Blo 622298 1407239 := bstep (se 1 (by rfl) ⟨1055429, by rfl⟩ : syracuseStep 1407239 = 2110859) B2110859
theorem B4749677 : Blo 622298 4749677 := bstep (se 3 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 4749677 = 1781129) B1781129
theorem B1407545 : Blo 622298 1407545 := bstep (se 2 (by rfl) ⟨527829, by rfl⟩ : syracuseStep 1407545 = 1055659) B1055659
theorem B3210311 : Blo 622298 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B1899769 : Blo 622298 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B1408265 : Blo 622298 1408265 := bstep (se 2 (by rfl) ⟨528099, by rfl⟩ : syracuseStep 1408265 = 1056199) B1056199
theorem B30768569 : Blo 622298 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B1998569 : Blo 622298 1998569 := bstep (se 2 (by rfl) ⟨749463, by rfl⟩ : syracuseStep 1998569 = 1498927) B1498927
theorem B622407 : Blo 622298 622407 := bstep (se 1 (by rfl) ⟨466805, by rfl⟩ : syracuseStep 622407 = 933611) B933611
theorem B622559 : Blo 622298 622559 := bstep (se 1 (by rfl) ⟨466919, by rfl⟩ : syracuseStep 622559 = 933839) B933839
theorem B622783 : Blo 622298 622783 := bstep (se 1 (by rfl) ⟨467087, by rfl⟩ : syracuseStep 622783 = 934175) B934175
theorem B622799 : Blo 622298 622799 := bstep (se 1 (by rfl) ⟨467099, by rfl⟩ : syracuseStep 622799 = 934199) B934199
theorem B622847 : Blo 622298 622847 := bstep (se 1 (by rfl) ⟨467135, by rfl⟩ : syracuseStep 622847 = 934271) B934271
theorem B622895 : Blo 622298 622895 := bstep (se 1 (by rfl) ⟨467171, by rfl⟩ : syracuseStep 622895 = 934343) B934343
theorem B623131 : Blo 622298 623131 := bstep (se 1 (by rfl) ⟨467348, by rfl⟩ : syracuseStep 623131 = 934697) B934697
theorem B623135 : Blo 622298 623135 := bstep (se 1 (by rfl) ⟨467351, by rfl⟩ : syracuseStep 623135 = 934703) B934703
theorem B623215 : Blo 622298 623215 := bstep (se 1 (by rfl) ⟨467411, by rfl⟩ : syracuseStep 623215 = 934823) B934823
theorem B623271 : Blo 622298 623271 := bstep (se 1 (by rfl) ⟨467453, by rfl⟩ : syracuseStep 623271 = 934907) B934907
theorem B623311 : Blo 622298 623311 := bstep (se 1 (by rfl) ⟨467483, by rfl⟩ : syracuseStep 623311 = 934967) B934967
theorem B623391 : Blo 622298 623391 := bstep (se 1 (by rfl) ⟨467543, by rfl⟩ : syracuseStep 623391 = 935087) B935087
theorem B623663 : Blo 622298 623663 := bstep (se 1 (by rfl) ⟨467747, by rfl⟩ : syracuseStep 623663 = 935495) B935495
theorem B623727 : Blo 622298 623727 := bstep (se 1 (by rfl) ⟨467795, by rfl⟩ : syracuseStep 623727 = 935591) B935591
theorem B623783 : Blo 622298 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B623807 : Blo 622298 623807 := bstep (se 1 (by rfl) ⟨467855, by rfl⟩ : syracuseStep 623807 = 935711) B935711
theorem B1279199 : Blo 622298 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B623839 : Blo 622298 623839 := bstep (se 1 (by rfl) ⟨467879, by rfl⟩ : syracuseStep 623839 = 935759) B935759
theorem B623919 : Blo 622298 623919 := bstep (se 1 (by rfl) ⟨467939, by rfl⟩ : syracuseStep 623919 = 935879) B935879
theorem B3999239 : Blo 622298 3999239 := bstep (se 1 (by rfl) ⟨2999429, by rfl⟩ : syracuseStep 3999239 = 5998859) B5998859
theorem B624155 : Blo 622298 624155 := bstep (se 1 (by rfl) ⟨468116, by rfl⟩ : syracuseStep 624155 = 936233) B936233
theorem B624159 : Blo 622298 624159 := bstep (se 1 (by rfl) ⟨468119, by rfl⟩ : syracuseStep 624159 = 936239) B936239
theorem B624319 : Blo 622298 624319 := bstep (se 1 (by rfl) ⟨468239, by rfl⟩ : syracuseStep 624319 = 936479) B936479
theorem B886567 : Blo 622298 886567 := bstep (se 1 (by rfl) ⟨664925, by rfl⟩ : syracuseStep 886567 = 1329851) B1329851
theorem B8685409 : Blo 622298 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B624575 : Blo 622298 624575 := bstep (se 1 (by rfl) ⟨468431, by rfl⟩ : syracuseStep 624575 = 936863) B936863
theorem B624607 : Blo 622298 624607 := bstep (se 1 (by rfl) ⟨468455, by rfl⟩ : syracuseStep 624607 = 936911) B936911
theorem B624667 : Blo 622298 624667 := bstep (se 1 (by rfl) ⟨468500, by rfl⟩ : syracuseStep 624667 = 937001) B937001
theorem B624671 : Blo 622298 624671 := bstep (se 1 (by rfl) ⟨468503, by rfl⟩ : syracuseStep 624671 = 937007) B937007
theorem B624687 : Blo 622298 624687 := bstep (se 1 (by rfl) ⟨468515, by rfl⟩ : syracuseStep 624687 = 937031) B937031
theorem B624863 : Blo 622298 624863 := bstep (se 1 (by rfl) ⟨468647, by rfl⟩ : syracuseStep 624863 = 937295) B937295
theorem B1050907 : Blo 622298 1050907 := bstep (se 1 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 1050907 = 1576361) B1576361
theorem B624923 : Blo 622298 624923 := bstep (se 1 (by rfl) ⟨468692, by rfl⟩ : syracuseStep 624923 = 937385) B937385
theorem B625023 : Blo 622298 625023 := bstep (se 1 (by rfl) ⟨468767, by rfl⟩ : syracuseStep 625023 = 937535) B937535
theorem B1051049 : Blo 622298 1051049 := bstep (se 2 (by rfl) ⟨394143, by rfl⟩ : syracuseStep 1051049 = 788287) B788287
theorem B625199 : Blo 622298 625199 := bstep (se 1 (by rfl) ⟨468899, by rfl⟩ : syracuseStep 625199 = 937799) B937799
theorem B1051231 : Blo 622298 1051231 := bstep (se 1 (by rfl) ⟨788423, by rfl⟩ : syracuseStep 1051231 = 1576847) B1576847
theorem B625255 : Blo 622298 625255 := bstep (se 1 (by rfl) ⟨468941, by rfl⟩ : syracuseStep 625255 = 937883) B937883
theorem B1772189 : Blo 622298 1772189 := bstep (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) B664571
theorem B7113581 : Blo 622298 7113581 := bstep (se 3 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 7113581 = 2667593) B2667593
theorem B625631 : Blo 622298 625631 := bstep (se 1 (by rfl) ⟨469223, by rfl⟩ : syracuseStep 625631 = 938447) B938447
theorem B1051643 : Blo 622298 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B625659 : Blo 622298 625659 := bstep (se 1 (by rfl) ⟨469244, by rfl⟩ : syracuseStep 625659 = 938489) B938489
theorem B625727 : Blo 622298 625727 := bstep (se 1 (by rfl) ⟨469295, by rfl⟩ : syracuseStep 625727 = 938591) B938591
theorem B789679 : Blo 622298 789679 := bstep (se 1 (by rfl) ⟨592259, by rfl⟩ : syracuseStep 789679 = 1184519) B1184519
theorem B626047 : Blo 622298 626047 := bstep (se 1 (by rfl) ⟨469535, by rfl⟩ : syracuseStep 626047 = 939071) B939071
theorem B27037061 : Blo 622298 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B626075 : Blo 622298 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B626143 : Blo 622298 626143 := bstep (se 1 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 626143 = 939215) B939215
theorem B2100815 : Blo 622298 2100815 := bstep (se 1 (by rfl) ⟨1575611, by rfl⟩ : syracuseStep 2100815 = 3151223) B3151223
theorem B626279 : Blo 622298 626279 := bstep (se 1 (by rfl) ⟨469709, by rfl⟩ : syracuseStep 626279 = 939419) B939419
theorem B2428795 : Blo 622298 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B2101355 : Blo 622298 2101355 := bstep (se 1 (by rfl) ⟨1576016, by rfl⟩ : syracuseStep 2101355 = 3152033) B3152033
theorem B2101409 : Blo 622298 2101409 := bstep (se 2 (by rfl) ⟨788028, by rfl⟩ : syracuseStep 2101409 = 1576057) B1576057
theorem B2003105 : Blo 622298 2003105 := bstep (se 2 (by rfl) ⟨751164, by rfl⟩ : syracuseStep 2003105 = 1502329) B1502329
theorem B23368333 : Blo 622298 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B15995717 : Blo 622298 15995717 := bstep (se 4 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 15995717 = 2999197) B2999197
theorem B7574401 : Blo 622298 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B2659513 : Blo 622298 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B2004335 : Blo 622298 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B2102759 : Blo 622298 2102759 := bstep (se 1 (by rfl) ⟨1577069, by rfl⟩ : syracuseStep 2102759 = 3154139) B3154139
theorem B1185263 : Blo 622298 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B2102867 : Blo 622298 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B1054363 : Blo 622298 1054363 := bstep (se 1 (by rfl) ⟨790772, by rfl⟩ : syracuseStep 1054363 = 1581545) B1581545
theorem B7116497 : Blo 622298 7116497 := bstep (se 2 (by rfl) ⟨2668686, by rfl⟩ : syracuseStep 7116497 = 5337373) B5337373
theorem B5347079 : Blo 622298 5347079 := bstep (se 1 (by rfl) ⟨4010309, by rfl⟩ : syracuseStep 5347079 = 8020619) B8020619
theorem B2103137 : Blo 622298 2103137 := bstep (se 2 (by rfl) ⟨788676, by rfl⟩ : syracuseStep 2103137 = 1577353) B1577353
theorem B792443 : Blo 622298 792443 := bstep (se 1 (by rfl) ⟨594332, by rfl⟩ : syracuseStep 792443 = 1188665) B1188665
theorem B1775753 : Blo 622298 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B5708063 : Blo 622298 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B4004261 : Blo 622298 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B1055207 : Blo 622298 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B1579763 : Blo 622298 1579763 := bstep (se 1 (by rfl) ⟨1184822, by rfl⟩ : syracuseStep 1579763 = 2369645) B2369645
theorem B1580057 : Blo 622298 1580057 := bstep (se 2 (by rfl) ⟨592521, by rfl⟩ : syracuseStep 1580057 = 1185043) B1185043
theorem B2661511 : Blo 622298 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B2530511 : Blo 622298 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B2366729 : Blo 622298 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B2366759 : Blo 622298 2366759 := bstep (se 1 (by rfl) ⟨1775069, by rfl⟩ : syracuseStep 2366759 = 3550139) B3550139
theorem B1056071 : Blo 622298 1056071 := bstep (se 1 (by rfl) ⟨792053, by rfl⟩ : syracuseStep 1056071 = 1584107) B1584107
theorem B1056233 : Blo 622298 1056233 := bstep (se 2 (by rfl) ⟨396087, by rfl⟩ : syracuseStep 1056233 = 792175) B792175
theorem B10133191 : Blo 622298 10133191 := bstep (se 1 (by rfl) ⟨7599893, by rfl⟩ : syracuseStep 10133191 = 15199787) B15199787
theorem B1580897 : Blo 622298 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B8560829 : Blo 622298 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B3613177 : Blo 622298 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B9118493 : Blo 622298 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B6005623 : Blo 622298 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B1582355 : Blo 622298 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B3155273 : Blo 622298 3155273 := bstep (se 2 (by rfl) ⟨1183227, by rfl⟩ : syracuseStep 3155273 = 2366455) B2366455
theorem B2533025 : Blo 622298 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B11970341 : Blo 622298 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B2370131 : Blo 622298 2370131 := bstep (se 1 (by rfl) ⟨1777598, by rfl⟩ : syracuseStep 2370131 = 3555197) B3555197
theorem B2534111 : Blo 622298 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B2665543 : Blo 622298 2665543 := bstep (se 1 (by rfl) ⟨1999157, by rfl⟩ : syracuseStep 2665543 = 3998315) B3998315
theorem B6007931 : Blo 622298 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B2993395 : Blo 622298 2993395 := bstep (se 1 (by rfl) ⟨2245046, by rfl⟩ : syracuseStep 2993395 = 4490093) B4490093
theorem B16035083 : Blo 622298 16035083 := bstep (se 1 (by rfl) ⟨12026312, by rfl⟩ : syracuseStep 16035083 = 24052625) B24052625
theorem B7122329 : Blo 622298 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B700411 : Blo 622298 700411 := bstep (se 1 (by rfl) ⟨525308, by rfl⟩ : syracuseStep 700411 = 1050617) B1050617
theorem B700519 : Blo 622298 700519 := bstep (se 1 (by rfl) ⟨525389, by rfl⟩ : syracuseStep 700519 = 1050779) B1050779
theorem B1585291 : Blo 622298 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B700591 : Blo 622298 700591 := bstep (se 1 (by rfl) ⟨525443, by rfl⟩ : syracuseStep 700591 = 1050887) B1050887
theorem B2109671 : Blo 622298 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B26915273 : Blo 622298 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B2699833 : Blo 622298 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B12989089 : Blo 622298 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B6402725 : Blo 622298 6402725 := bstep (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) B1200511
theorem B4731695 : Blo 622298 4731695 := bstep (se 1 (by rfl) ⟨3548771, by rfl⟩ : syracuseStep 4731695 = 7097543) B7097543
theorem B701275 : Blo 622298 701275 := bstep (se 1 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 701275 = 1051913) B1051913
theorem B2110535 : Blo 622298 2110535 := bstep (se 1 (by rfl) ⟨1582901, by rfl⟩ : syracuseStep 2110535 = 3165803) B3165803
theorem B4011079 : Blo 622298 4011079 := bstep (se 1 (by rfl) ⟨3008309, by rfl⟩ : syracuseStep 4011079 = 6016619) B6016619
theorem B898231 : Blo 622298 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B7615853 : Blo 622298 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B2995643 : Blo 622298 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1685225 : Blo 622298 1685225 := bstep (se 2 (by rfl) ⟨631959, by rfl⟩ : syracuseStep 1685225 = 1263919) B1263919
theorem B2537257 : Blo 622298 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B2668585 : Blo 622298 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B582924347 : Blo 622298 582924347 := bstep (se 1 (by rfl) ⟨437193260, by rfl⟩ : syracuseStep 582924347 = 874386521) B874386521
theorem B702535 : Blo 622298 702535 := bstep (se 1 (by rfl) ⟨526901, by rfl⟩ : syracuseStep 702535 = 1053803) B1053803
theorem B2111723 : Blo 622298 2111723 := bstep (se 1 (by rfl) ⟨1583792, by rfl⟩ : syracuseStep 2111723 = 3167585) B3167585
theorem B4733639 : Blo 622298 4733639 := bstep (se 1 (by rfl) ⟨3550229, by rfl⟩ : syracuseStep 4733639 = 7100459) B7100459
theorem B2374505 : Blo 622298 2374505 := bstep (se 2 (by rfl) ⟨890439, by rfl⟩ : syracuseStep 2374505 = 1780879) B1780879
theorem B703399 : Blo 622298 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B2669543 : Blo 622298 2669543 := bstep (se 1 (by rfl) ⟨2002157, by rfl⟩ : syracuseStep 2669543 = 4004315) B4004315
theorem B703579 : Blo 622298 703579 := bstep (se 1 (by rfl) ⟨527684, by rfl⟩ : syracuseStep 703579 = 1055369) B1055369
theorem B1424609 : Blo 622298 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B1424615 : Blo 622298 1424615 := bstep (se 1 (by rfl) ⟨1068461, by rfl⟩ : syracuseStep 1424615 = 2136923) B2136923
theorem B2374991 : Blo 622298 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B5324251 : Blo 622298 5324251 := bstep (se 1 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 5324251 = 7986377) B7986377
theorem B933599 : Blo 622298 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B933641 : Blo 622298 933641 := bstep (se 2 (by rfl) ⟨350115, by rfl⟩ : syracuseStep 933641 = 700231) B700231
theorem B4865939 : Blo 622298 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B2408381 : Blo 622298 2408381 := bstep (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) B903143
theorem B934079 : Blo 622298 934079 := bstep (se 1 (by rfl) ⟨700559, by rfl⟩ : syracuseStep 934079 = 1401119) B1401119
theorem B6734015 : Blo 622298 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B934505 : Blo 622298 934505 := bstep (se 2 (by rfl) ⟨350439, by rfl⟩ : syracuseStep 934505 = 700879) B700879
theorem B934511 : Blo 622298 934511 := bstep (se 1 (by rfl) ⟨700883, by rfl⟩ : syracuseStep 934511 = 1401767) B1401767
theorem B935135 : Blo 622298 935135 := bstep (se 1 (by rfl) ⟨701351, by rfl⟩ : syracuseStep 935135 = 1402703) B1402703
theorem B935147 : Blo 622298 935147 := bstep (se 1 (by rfl) ⟨701360, by rfl⟩ : syracuseStep 935147 = 1402721) B1402721
theorem B2704823 : Blo 622298 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B2377147 : Blo 622298 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B935531 : Blo 622298 935531 := bstep (se 1 (by rfl) ⟨701648, by rfl⟩ : syracuseStep 935531 = 1403297) B1403297
theorem B935615 : Blo 622298 935615 := bstep (se 1 (by rfl) ⟨701711, by rfl⟩ : syracuseStep 935615 = 1403423) B1403423
theorem B935801 : Blo 622298 935801 := bstep (se 2 (by rfl) ⟨350925, by rfl⟩ : syracuseStep 935801 = 701851) B701851
theorem B936551 : Blo 622298 936551 := bstep (se 1 (by rfl) ⟨702413, by rfl⟩ : syracuseStep 936551 = 1404827) B1404827
theorem B936743 : Blo 622298 936743 := bstep (se 1 (by rfl) ⟨702557, by rfl⟩ : syracuseStep 936743 = 1405115) B1405115
theorem B5688251 : Blo 622298 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B937067 : Blo 622298 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B2673917 : Blo 622298 2673917 := bstep (se 3 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 2673917 = 1002719) B1002719
theorem B937307 : Blo 622298 937307 := bstep (se 1 (by rfl) ⟨702980, by rfl⟩ : syracuseStep 937307 = 1405961) B1405961
theorem B937337 : Blo 622298 937337 := bstep (se 2 (by rfl) ⟨351501, by rfl⟩ : syracuseStep 937337 = 703003) B703003
theorem B937343 : Blo 622298 937343 := bstep (se 1 (by rfl) ⟨703007, by rfl⟩ : syracuseStep 937343 = 1406015) B1406015
theorem B207867653 : Blo 622298 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B937967 : Blo 622298 937967 := bstep (se 1 (by rfl) ⟨703475, by rfl⟩ : syracuseStep 937967 = 1406951) B1406951
theorem B937979 : Blo 622298 937979 := bstep (se 1 (by rfl) ⟨703484, by rfl⟩ : syracuseStep 937979 = 1406969) B1406969
theorem B938039 : Blo 622298 938039 := bstep (se 1 (by rfl) ⟨703529, by rfl⟩ : syracuseStep 938039 = 1407059) B1407059
theorem B938087 : Blo 622298 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B938159 : Blo 622298 938159 := bstep (se 1 (by rfl) ⟨703619, by rfl⟩ : syracuseStep 938159 = 1407239) B1407239
theorem B2674907 : Blo 622298 2674907 := bstep (se 1 (by rfl) ⟨2006180, by rfl⟩ : syracuseStep 2674907 = 4012361) B4012361
theorem B3166451 : Blo 622298 3166451 := bstep (se 1 (by rfl) ⟨2374838, by rfl⟩ : syracuseStep 3166451 = 4749677) B4749677
theorem B938363 : Blo 622298 938363 := bstep (se 1 (by rfl) ⟨703772, by rfl⟩ : syracuseStep 938363 = 1407545) B1407545
theorem B1331849 : Blo 622298 1331849 := bstep (se 2 (by rfl) ⟨499443, by rfl⟩ : syracuseStep 1331849 = 998887) B998887
theorem B938633 : Blo 622298 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B938843 : Blo 622298 938843 := bstep (se 1 (by rfl) ⟨704132, by rfl⟩ : syracuseStep 938843 = 1408265) B1408265
theorem B6018077 : Blo 622298 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B1496159 : Blo 622298 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B1332379 : Blo 622298 1332379 := bstep (se 1 (by rfl) ⟨999284, by rfl⟩ : syracuseStep 1332379 = 1998569) B1998569
theorem B939305 : Blo 622298 939305 := bstep (se 2 (by rfl) ⟨352239, by rfl⟩ : syracuseStep 939305 = 704479) B704479
theorem B4740443 : Blo 622298 4740443 := bstep (se 1 (by rfl) ⟨3555332, by rfl⟩ : syracuseStep 4740443 = 7110665) B7110665
theorem B2020879 : Blo 622298 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B3168071 : Blo 622298 3168071 := bstep (se 1 (by rfl) ⟨2376053, by rfl⟩ : syracuseStep 3168071 = 4752107) B4752107
theorem B7198541 : Blo 622298 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B4511713 : Blo 622298 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B2250899 : Blo 622298 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B6510905 : Blo 622298 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B5331359 : Blo 622298 5331359 := bstep (se 1 (by rfl) ⟨3998519, by rfl⟩ : syracuseStep 5331359 = 7997039) B7997039
theorem B3562055 : Blo 622298 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B1597049 : Blo 622298 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B1498745 : Blo 622298 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B1334951 : Blo 622298 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B9264851 : Blo 622298 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B1400687 : Blo 622298 1400687 := bstep (se 1 (by rfl) ⟨1050515, by rfl⟩ : syracuseStep 1400687 = 2101031) B2101031
theorem B5333273 : Blo 622298 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B1401371 : Blo 622298 1401371 := bstep (se 1 (by rfl) ⟨1051028, by rfl⟩ : syracuseStep 1401371 = 2102057) B2102057
theorem B1401551 : Blo 622298 1401551 := bstep (se 1 (by rfl) ⟨1051163, by rfl⟩ : syracuseStep 1401551 = 2102327) B2102327
theorem B7103375 : Blo 622298 7103375 := bstep (se 1 (by rfl) ⟨5327531, by rfl⟩ : syracuseStep 7103375 = 10655063) B10655063
theorem B1401929 : Blo 622298 1401929 := bstep (se 2 (by rfl) ⟨525723, by rfl⟩ : syracuseStep 1401929 = 1051447) B1051447
theorem B23029069 : Blo 622298 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B3564971 : Blo 622298 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B5334983 : Blo 622298 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B1402847 : Blo 622298 1402847 := bstep (se 1 (by rfl) ⟨1052135, by rfl⟩ : syracuseStep 1402847 = 2104271) B2104271
theorem B2845037 : Blo 622298 2845037 := bstep (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) B1066889
theorem B11364745 : Blo 622298 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B5401025 : Blo 622298 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B1403855 : Blo 622298 1403855 := bstep (se 1 (by rfl) ⟨1052891, by rfl⟩ : syracuseStep 1403855 = 2105783) B2105783
theorem B1403945 : Blo 622298 1403945 := bstep (se 2 (by rfl) ⟨526479, by rfl⟩ : syracuseStep 1403945 = 1052959) B1052959
theorem B1404179 : Blo 622298 1404179 := bstep (se 1 (by rfl) ⟨1053134, by rfl⟩ : syracuseStep 1404179 = 2106269) B2106269
theorem B1404215 : Blo 622298 1404215 := bstep (se 1 (by rfl) ⟨1053161, by rfl⟩ : syracuseStep 1404215 = 2106323) B2106323
theorem B1502945 : Blo 622298 1502945 := bstep (se 2 (by rfl) ⟨563604, by rfl⟩ : syracuseStep 1502945 = 1127209) B1127209
theorem B1404809 : Blo 622298 1404809 := bstep (se 2 (by rfl) ⟨526803, by rfl⟩ : syracuseStep 1404809 = 1053607) B1053607
theorem B1405025 : Blo 622298 1405025 := bstep (se 2 (by rfl) ⟨526884, by rfl⟩ : syracuseStep 1405025 = 1053769) B1053769
theorem B1405691 : Blo 622298 1405691 := bstep (se 1 (by rfl) ⟨1054268, by rfl⟩ : syracuseStep 1405691 = 2108537) B2108537
theorem B1405907 : Blo 622298 1405907 := bstep (se 1 (by rfl) ⟨1054430, by rfl⟩ : syracuseStep 1405907 = 2108861) B2108861
theorem B5993747 : Blo 622298 5993747 := bstep (se 1 (by rfl) ⟨4495310, by rfl⟩ : syracuseStep 5993747 = 8990621) B8990621
theorem B2848063 : Blo 622298 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B184251743 : Blo 622298 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B1406375 : Blo 622298 1406375 := bstep (se 1 (by rfl) ⟨1054781, by rfl⟩ : syracuseStep 1406375 = 2109563) B2109563
theorem B1406483 : Blo 622298 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B1406555 : Blo 622298 1406555 := bstep (se 1 (by rfl) ⟨1054916, by rfl⟩ : syracuseStep 1406555 = 2109833) B2109833
theorem B22837049 : Blo 622298 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B1407167 : Blo 622298 1407167 := bstep (se 1 (by rfl) ⟨1055375, by rfl⟩ : syracuseStep 1407167 = 2110751) B2110751
theorem B751847 : Blo 622298 751847 := bstep (se 1 (by rfl) ⟨563885, by rfl⟩ : syracuseStep 751847 = 1127771) B1127771
theorem B1800539 : Blo 622298 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B4750163 : Blo 622298 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B1408427 : Blo 622298 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B1408463 : Blo 622298 1408463 := bstep (se 1 (by rfl) ⟨1056347, by rfl⟩ : syracuseStep 1408463 = 2112695) B2112695
theorem B20512379 : Blo 622298 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B5996207 : Blo 622298 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B622311 : Blo 622298 622311 := bstep (se 1 (by rfl) ⟨466733, by rfl⟩ : syracuseStep 622311 = 933467) B933467
theorem B622367 : Blo 622298 622367 := bstep (se 1 (by rfl) ⟨466775, by rfl⟩ : syracuseStep 622367 = 933551) B933551
theorem B622447 : Blo 622298 622447 := bstep (se 1 (by rfl) ⟨466835, by rfl⟩ : syracuseStep 622447 = 933671) B933671
theorem B622503 : Blo 622298 622503 := bstep (se 1 (by rfl) ⟨466877, by rfl⟩ : syracuseStep 622503 = 933755) B933755
theorem B1408967 : Blo 622298 1408967 := bstep (se 1 (by rfl) ⟨1056725, by rfl⟩ : syracuseStep 1408967 = 2113451) B2113451
theorem B622719 : Blo 622298 622719 := bstep (se 1 (by rfl) ⟨467039, by rfl⟩ : syracuseStep 622719 = 934079) B934079
theorem B4489343 : Blo 622298 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B623003 : Blo 622298 623003 := bstep (se 1 (by rfl) ⟨467252, by rfl⟩ : syracuseStep 623003 = 934505) B934505
theorem B623007 : Blo 622298 623007 := bstep (se 1 (by rfl) ⟨467255, by rfl⟩ : syracuseStep 623007 = 934511) B934511
theorem B4817569 : Blo 622298 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B623423 : Blo 622298 623423 := bstep (se 1 (by rfl) ⟨467567, by rfl⟩ : syracuseStep 623423 = 935135) B935135
theorem B623431 : Blo 622298 623431 := bstep (se 1 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 623431 = 935147) B935147
theorem B1803215 : Blo 622298 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B623687 : Blo 622298 623687 := bstep (se 1 (by rfl) ⟨467765, by rfl⟩ : syracuseStep 623687 = 935531) B935531
theorem B623743 : Blo 622298 623743 := bstep (se 1 (by rfl) ⟨467807, by rfl⟩ : syracuseStep 623743 = 935615) B935615
theorem B623867 : Blo 622298 623867 := bstep (se 1 (by rfl) ⟨467900, by rfl⟩ : syracuseStep 623867 = 935801) B935801
theorem B624367 : Blo 622298 624367 := bstep (se 1 (by rfl) ⟨468275, by rfl⟩ : syracuseStep 624367 = 936551) B936551
theorem B30705425 : Blo 622298 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B1181459 : Blo 622298 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B624495 : Blo 622298 624495 := bstep (se 1 (by rfl) ⟨468371, by rfl⟩ : syracuseStep 624495 = 936743) B936743
theorem B624711 : Blo 622298 624711 := bstep (se 1 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 624711 = 937067) B937067
theorem B624871 : Blo 622298 624871 := bstep (se 1 (by rfl) ⟨468653, by rfl⟩ : syracuseStep 624871 = 937307) B937307
theorem B624891 : Blo 622298 624891 := bstep (se 1 (by rfl) ⟨468668, by rfl⟩ : syracuseStep 624891 = 937337) B937337
theorem B624895 : Blo 622298 624895 := bstep (se 1 (by rfl) ⟨468671, by rfl⟩ : syracuseStep 624895 = 937343) B937343
theorem B18024707 : Blo 622298 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B1182089 : Blo 622298 1182089 := bstep (se 2 (by rfl) ⟨443283, by rfl⟩ : syracuseStep 1182089 = 886567) B886567
theorem B138578435 : Blo 622298 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B625311 : Blo 622298 625311 := bstep (se 1 (by rfl) ⟨468983, by rfl⟩ : syracuseStep 625311 = 937967) B937967
theorem B625319 : Blo 622298 625319 := bstep (se 1 (by rfl) ⟨468989, by rfl⟩ : syracuseStep 625319 = 937979) B937979
theorem B625359 : Blo 622298 625359 := bstep (se 1 (by rfl) ⟨469019, by rfl⟩ : syracuseStep 625359 = 938039) B938039
theorem B625391 : Blo 622298 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B625439 : Blo 622298 625439 := bstep (se 1 (by rfl) ⟨469079, by rfl⟩ : syracuseStep 625439 = 938159) B938159
theorem B625575 : Blo 622298 625575 := bstep (se 1 (by rfl) ⟨469181, by rfl⟩ : syracuseStep 625575 = 938363) B938363
theorem B625755 : Blo 622298 625755 := bstep (se 1 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 625755 = 938633) B938633
theorem B625895 : Blo 622298 625895 := bstep (se 1 (by rfl) ⟨469421, by rfl⟩ : syracuseStep 625895 = 938843) B938843
theorem B3411197 : Blo 622298 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B626203 : Blo 622298 626203 := bstep (se 1 (by rfl) ⟨469652, by rfl⟩ : syracuseStep 626203 = 939305) B939305
theorem B790175 : Blo 622298 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B1183835 : Blo 622298 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B3805375 : Blo 622298 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B1052905 : Blo 622298 1052905 := bstep (se 2 (by rfl) ⟨394839, by rfl⟩ : syracuseStep 1052905 = 789679) B789679
theorem B1053175 : Blo 622298 1053175 := bstep (se 1 (by rfl) ⟨789881, by rfl⟩ : syracuseStep 1053175 = 1579763) B1579763
theorem B1053371 : Blo 622298 1053371 := bstep (se 1 (by rfl) ⟨790028, by rfl⟩ : syracuseStep 1053371 = 1580057) B1580057
theorem B1577819 : Blo 622298 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B1577839 : Blo 622298 1577839 := bstep (se 1 (by rfl) ⟨1183379, by rfl⟩ : syracuseStep 1577839 = 2366759) B2366759
theorem B889967 : Blo 622298 889967 := bstep (se 1 (by rfl) ⟨667475, by rfl⟩ : syracuseStep 889967 = 1334951) B1334951
theorem B1053931 : Blo 622298 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B2004925 : Blo 622298 2004925 := bstep (se 3 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 2004925 = 751847) B751847
theorem B1054903 : Blo 622298 1054903 := bstep (se 1 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 1054903 = 1582355) B1582355
theorem B2103515 : Blo 622298 2103515 := bstep (se 1 (by rfl) ⟨1577636, by rfl⟩ : syracuseStep 2103515 = 3155273) B3155273
theorem B10099201 : Blo 622298 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B5348105 : Blo 622298 5348105 := bstep (se 2 (by rfl) ⟨2005539, by rfl⟩ : syracuseStep 5348105 = 4011079) B4011079
theorem B1776505 : Blo 622298 1776505 := bstep (se 2 (by rfl) ⟨666189, by rfl⟩ : syracuseStep 1776505 = 1332379) B1332379
theorem B3546017 : Blo 622298 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B1580087 : Blo 622298 1580087 := bstep (se 1 (by rfl) ⟨1185065, by rfl⟩ : syracuseStep 1580087 = 2370131) B2370131
theorem B2694505 : Blo 622298 2694505 := bstep (se 2 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 2694505 = 2020879) B2020879
theorem B4005287 : Blo 622298 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B10690055 : Blo 622298 10690055 := bstep (se 1 (by rfl) ⟨8017541, by rfl⟩ : syracuseStep 10690055 = 16035083) B16035083
theorem B3383009 : Blo 622298 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B4268483 : Blo 622298 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B3154463 : Blo 622298 3154463 := bstep (se 1 (by rfl) ⟨2365847, by rfl⟩ : syracuseStep 3154463 = 4731695) B4731695
theorem B1123483 : Blo 622298 1123483 := bstep (se 1 (by rfl) ⟨842612, by rfl⟩ : syracuseStep 1123483 = 1685225) B1685225
theorem B3548681 : Blo 622298 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B3155759 : Blo 622298 3155759 := bstep (se 1 (by rfl) ⟨2366819, by rfl⟩ : syracuseStep 3155759 = 4733639) B4733639
theorem B1583003 : Blo 622298 1583003 := bstep (se 1 (by rfl) ⟨1187252, by rfl⟩ : syracuseStep 1583003 = 2374505) B2374505
theorem B1779695 : Blo 622298 1779695 := bstep (se 1 (by rfl) ⟨1334771, by rfl⟩ : syracuseStep 1779695 = 2669543) B2669543
theorem B1583327 : Blo 622298 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B13510921 : Blo 622298 13510921 := bstep (se 2 (by rfl) ⟨5066595, by rfl⟩ : syracuseStep 13510921 = 10133191) B10133191
theorem B13674919 : Blo 622298 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B2666159 : Blo 622298 2666159 := bstep (se 1 (by rfl) ⟨1999619, by rfl⟩ : syracuseStep 2666159 = 3999239) B3999239
theorem B8007497 : Blo 622298 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B700699 : Blo 622298 700699 := bstep (se 1 (by rfl) ⟨525524, by rfl⟩ : syracuseStep 700699 = 1051049) B1051049
theorem B3551597 : Blo 622298 3551597 := bstep (se 3 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 3551597 = 1331849) B1331849
theorem B701095 : Blo 622298 701095 := bstep (se 1 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 701095 = 1051643) B1051643
theorem B1782611 : Blo 622298 1782611 := bstep (se 1 (by rfl) ⟨1336958, by rfl⟩ : syracuseStep 1782611 = 2673917) B2673917
theorem B11580545 : Blo 622298 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B1783271 : Blo 622298 1783271 := bstep (se 1 (by rfl) ⟨1337453, by rfl⟩ : syracuseStep 1783271 = 2674907) B2674907
theorem B2110967 : Blo 622298 2110967 := bstep (se 1 (by rfl) ⟨1583225, by rfl⟩ : syracuseStep 2110967 = 3166451) B3166451
theorem B15152993 : Blo 622298 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B10663811 : Blo 622298 10663811 := bstep (se 1 (by rfl) ⟨7997858, by rfl⟩ : syracuseStep 10663811 = 15995717) B15995717
theorem B997439 : Blo 622298 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B3160295 : Blo 622298 3160295 := bstep (se 1 (by rfl) ⟨2370221, by rfl⟩ : syracuseStep 3160295 = 4740443) B4740443
theorem B2112047 : Blo 622298 2112047 := bstep (se 1 (by rfl) ⟨1584035, by rfl⟩ : syracuseStep 2112047 = 3168071) B3168071
theorem B4799027 : Blo 622298 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B3554057 : Blo 622298 3554057 := bstep (se 2 (by rfl) ⟨1332771, by rfl⟩ : syracuseStep 3554057 = 2665543) B2665543
theorem B4340603 : Blo 622298 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B3554239 : Blo 622298 3554239 := bstep (se 1 (by rfl) ⟨2665679, by rfl⟩ : syracuseStep 3554239 = 5331359) B5331359
theorem B2669507 : Blo 622298 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B703471 : Blo 622298 703471 := bstep (se 1 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 703471 = 1055207) B1055207
theorem B2374703 : Blo 622298 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B1687007 : Blo 622298 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B704047 : Blo 622298 704047 := bstep (se 1 (by rfl) ⟨528035, by rfl⟩ : syracuseStep 704047 = 1056071) B1056071
theorem B704155 : Blo 622298 704155 := bstep (se 1 (by rfl) ⟨528116, by rfl⟩ : syracuseStep 704155 = 1056233) B1056233
theorem B2113181 : Blo 622298 2113181 := bstep (se 3 (by rfl) ⟨396221, by rfl⟩ : syracuseStep 2113181 = 792443) B792443
theorem B1064699 : Blo 622298 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B999163 : Blo 622298 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B6176567 : Blo 622298 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B933791 : Blo 622298 933791 := bstep (se 1 (by rfl) ⟨700343, by rfl⟩ : syracuseStep 933791 = 1400687) B1400687
theorem B933881 : Blo 622298 933881 := bstep (se 2 (by rfl) ⟨350205, by rfl⟩ : syracuseStep 933881 = 700411) B700411
theorem B934025 : Blo 622298 934025 := bstep (se 2 (by rfl) ⟨350259, by rfl⟩ : syracuseStep 934025 = 700519) B700519
theorem B2113721 : Blo 622298 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B3555515 : Blo 622298 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B934121 : Blo 622298 934121 := bstep (se 2 (by rfl) ⟨350295, by rfl⟩ : syracuseStep 934121 = 700591) B700591
theorem B934247 : Blo 622298 934247 := bstep (se 1 (by rfl) ⟨700685, by rfl⟩ : syracuseStep 934247 = 1401371) B1401371
theorem B934367 : Blo 622298 934367 := bstep (se 1 (by rfl) ⟨700775, by rfl⟩ : syracuseStep 934367 = 1401551) B1401551
theorem B6078995 : Blo 622298 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B4735583 : Blo 622298 4735583 := bstep (se 1 (by rfl) ⟨3551687, by rfl⟩ : syracuseStep 4735583 = 7103375) B7103375
theorem B934619 : Blo 622298 934619 := bstep (se 1 (by rfl) ⟨700964, by rfl⟩ : syracuseStep 934619 = 1401929) B1401929
theorem B17318785 : Blo 622298 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B2376647 : Blo 622298 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B1688683 : Blo 622298 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B935033 : Blo 622298 935033 := bstep (se 2 (by rfl) ⟨350637, by rfl⟩ : syracuseStep 935033 = 701275) B701275
theorem B7980227 : Blo 622298 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B3556655 : Blo 622298 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B935231 : Blo 622298 935231 := bstep (se 1 (by rfl) ⟨701423, by rfl⟩ : syracuseStep 935231 = 1402847) B1402847
theorem B1197641 : Blo 622298 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B1689407 : Blo 622298 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B935903 : Blo 622298 935903 := bstep (se 1 (by rfl) ⟨701927, by rfl⟩ : syracuseStep 935903 = 1403855) B1403855
theorem B935963 : Blo 622298 935963 := bstep (se 1 (by rfl) ⟨701972, by rfl⟩ : syracuseStep 935963 = 1403945) B1403945
theorem B936119 : Blo 622298 936119 := bstep (se 1 (by rfl) ⟨702089, by rfl⟩ : syracuseStep 936119 = 1404179) B1404179
theorem B936143 : Blo 622298 936143 := bstep (se 1 (by rfl) ⟨702107, by rfl⟩ : syracuseStep 936143 = 1404215) B1404215
theorem B1001963 : Blo 622298 1001963 := bstep (se 1 (by rfl) ⟨751472, by rfl⟩ : syracuseStep 1001963 = 1502945) B1502945
theorem B936539 : Blo 622298 936539 := bstep (se 1 (by rfl) ⟨702404, by rfl⟩ : syracuseStep 936539 = 1404809) B1404809
theorem B6015617 : Blo 622298 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B3558113 : Blo 622298 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B936683 : Blo 622298 936683 := bstep (se 1 (by rfl) ⟨702512, by rfl⟩ : syracuseStep 936683 = 1405025) B1405025
theorem B936713 : Blo 622298 936713 := bstep (se 2 (by rfl) ⟨351267, by rfl⟩ : syracuseStep 936713 = 702535) B702535
theorem B17943515 : Blo 622298 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B937127 : Blo 622298 937127 := bstep (se 1 (by rfl) ⟨702845, by rfl⟩ : syracuseStep 937127 = 1405691) B1405691
theorem B937271 : Blo 622298 937271 := bstep (se 1 (by rfl) ⟨702953, by rfl⟩ : syracuseStep 937271 = 1405907) B1405907
theorem B122834495 : Blo 622298 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B937583 : Blo 622298 937583 := bstep (se 1 (by rfl) ⟨703187, by rfl⟩ : syracuseStep 937583 = 1406375) B1406375
theorem B937655 : Blo 622298 937655 := bstep (se 1 (by rfl) ⟨703241, by rfl⟩ : syracuseStep 937655 = 1406483) B1406483
theorem B937703 : Blo 622298 937703 := bstep (se 1 (by rfl) ⟨703277, by rfl⟩ : syracuseStep 937703 = 1406555) B1406555
theorem B15224699 : Blo 622298 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B937865 : Blo 622298 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B388616231 : Blo 622298 388616231 := bstep (se 1 (by rfl) ⟨291462173, by rfl⟩ : syracuseStep 388616231 = 582924347) B582924347
theorem B938105 : Blo 622298 938105 := bstep (se 2 (by rfl) ⟨351789, by rfl⟩ : syracuseStep 938105 = 703579) B703579
theorem B938111 : Blo 622298 938111 := bstep (se 1 (by rfl) ⟨703583, by rfl⟩ : syracuseStep 938111 = 1407167) B1407167
theorem B1200359 : Blo 622298 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B3166775 : Blo 622298 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B7099001 : Blo 622298 7099001 := bstep (se 2 (by rfl) ⟨2662125, by rfl⟩ : syracuseStep 7099001 = 5324251) B5324251
theorem B938951 : Blo 622298 938951 := bstep (se 1 (by rfl) ⟨704213, by rfl⟩ : syracuseStep 938951 = 1408427) B1408427
theorem B938975 : Blo 622298 938975 := bstep (se 1 (by rfl) ⟨704231, by rfl⟩ : syracuseStep 938975 = 1408463) B1408463
theorem B939311 : Blo 622298 939311 := bstep (se 1 (by rfl) ⟨704483, by rfl⟩ : syracuseStep 939311 = 1408967) B1408967
theorem B22828877 : Blo 622298 22828877 := bstep (se 3 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 22828877 = 8560829) B8560829
theorem B4742387 : Blo 622298 4742387 := bstep (se 1 (by rfl) ⟨3556790, by rfl⟩ : syracuseStep 4742387 = 7113581) B7113581
theorem B3169529 : Blo 622298 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B3792167 : Blo 622298 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B1400543 : Blo 622298 1400543 := bstep (se 1 (by rfl) ⟨1050407, by rfl⟩ : syracuseStep 1400543 = 2100815) B2100815
theorem B1400903 : Blo 622298 1400903 := bstep (se 1 (by rfl) ⟨1050677, by rfl⟩ : syracuseStep 1400903 = 2101355) B2101355
theorem B16048205 : Blo 622298 16048205 := bstep (se 3 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 16048205 = 6018077) B6018077
theorem B1400939 : Blo 622298 1400939 := bstep (se 1 (by rfl) ⟨1050704, by rfl⟩ : syracuseStep 1400939 = 2101409) B2101409
theorem B1335403 : Blo 622298 1335403 := bstep (se 1 (by rfl) ⟨1001552, by rfl⟩ : syracuseStep 1335403 = 2003105) B2003105
theorem B1401209 : Blo 622298 1401209 := bstep (se 2 (by rfl) ⟨525453, by rfl⟩ : syracuseStep 1401209 = 1050907) B1050907
theorem B1401641 : Blo 622298 1401641 := bstep (se 2 (by rfl) ⟨525615, by rfl⟩ : syracuseStep 1401641 = 1051231) B1051231
theorem B1336223 : Blo 622298 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B1401839 : Blo 622298 1401839 := bstep (se 1 (by rfl) ⟨1051379, by rfl⟩ : syracuseStep 1401839 = 2102759) B2102759
theorem B1401911 : Blo 622298 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B4744331 : Blo 622298 4744331 := bstep (se 1 (by rfl) ⟨3558248, by rfl⟩ : syracuseStep 4744331 = 7116497) B7116497
theorem B7988381 : Blo 622298 7988381 := bstep (se 3 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 7988381 = 2995643) B2995643
theorem B3564719 : Blo 622298 3564719 := bstep (se 1 (by rfl) ⟨2673539, by rfl⟩ : syracuseStep 3564719 = 5347079) B5347079
theorem B1402091 : Blo 622298 1402091 := bstep (se 1 (by rfl) ⟨1051568, by rfl⟩ : syracuseStep 1402091 = 2103137) B2103137
theorem B1500599 : Blo 622298 1500599 := bstep (se 1 (by rfl) ⟨1125449, by rfl⟩ : syracuseStep 1500599 = 2250899) B2250899
theorem B3991193 : Blo 622298 3991193 := bstep (se 2 (by rfl) ⟨1496697, by rfl⟩ : syracuseStep 3991193 = 2993395) B2993395
theorem B3238393 : Blo 622298 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B3599777 : Blo 622298 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B31157777 : Blo 622298 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B1896691 : Blo 622298 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B3600683 : Blo 622298 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B3797417 : Blo 622298 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B1405817 : Blo 622298 1405817 := bstep (se 2 (by rfl) ⟨527181, by rfl⟩ : syracuseStep 1405817 = 1054363) B1054363
theorem B4748219 : Blo 622298 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B1406447 : Blo 622298 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B3798973 : Blo 622298 3798973 := bstep (se 3 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 3798973 = 1424615) B1424615
theorem B1407023 : Blo 622298 1407023 := bstep (se 1 (by rfl) ⟨1055267, by rfl⟩ : syracuseStep 1407023 = 2110535) B2110535
theorem B3995831 : Blo 622298 3995831 := bstep (se 1 (by rfl) ⟨2996873, by rfl⟩ : syracuseStep 3995831 = 5993747) B5993747
theorem B5077235 : Blo 622298 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B1407815 : Blo 622298 1407815 := bstep (se 1 (by rfl) ⟨1055861, by rfl⟩ : syracuseStep 1407815 = 2111723) B2111723
theorem B949739 : Blo 622298 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B3997471 : Blo 622298 3997471 := bstep (se 1 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 3997471 = 5996207) B5996207
theorem B622399 : Blo 622298 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B622427 : Blo 622298 622427 := bstep (se 1 (by rfl) ⟨466820, by rfl⟩ : syracuseStep 622427 = 933641) B933641
theorem B3243959 : Blo 622298 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B1605587 : Blo 622298 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B622683 : Blo 622298 622683 := bstep (se 1 (by rfl) ⟨467012, by rfl⟩ : syracuseStep 622683 = 934025) B934025
theorem B1409147 : Blo 622298 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B622747 : Blo 622298 622747 := bstep (se 1 (by rfl) ⟨467060, by rfl⟩ : syracuseStep 622747 = 934121) B934121
theorem B622831 : Blo 622298 622831 := bstep (se 1 (by rfl) ⟨467123, by rfl⟩ : syracuseStep 622831 = 934247) B934247
theorem B622911 : Blo 622298 622911 := bstep (se 1 (by rfl) ⟨467183, by rfl⟩ : syracuseStep 622911 = 934367) B934367
theorem B623079 : Blo 622298 623079 := bstep (se 1 (by rfl) ⟨467309, by rfl⟩ : syracuseStep 623079 = 934619) B934619
theorem B623355 : Blo 622298 623355 := bstep (se 1 (by rfl) ⟨467516, by rfl⟩ : syracuseStep 623355 = 935033) B935033
theorem B623487 : Blo 622298 623487 := bstep (se 1 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 623487 = 935231) B935231
theorem B6423425 : Blo 622298 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B787639 : Blo 622298 787639 := bstep (se 1 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 787639 = 1181459) B1181459
theorem B623935 : Blo 622298 623935 := bstep (se 1 (by rfl) ⟨467951, by rfl⟩ : syracuseStep 623935 = 935903) B935903
theorem B623975 : Blo 622298 623975 := bstep (se 1 (by rfl) ⟨467981, by rfl⟩ : syracuseStep 623975 = 935963) B935963
theorem B624079 : Blo 622298 624079 := bstep (se 1 (by rfl) ⟨468059, by rfl⟩ : syracuseStep 624079 = 936119) B936119
theorem B624095 : Blo 622298 624095 := bstep (se 1 (by rfl) ⟨468071, by rfl⟩ : syracuseStep 624095 = 936143) B936143
theorem B788059 : Blo 622298 788059 := bstep (se 1 (by rfl) ⟨591044, by rfl⟩ : syracuseStep 788059 = 1182089) B1182089
theorem B624359 : Blo 622298 624359 := bstep (se 1 (by rfl) ⟨468269, by rfl⟩ : syracuseStep 624359 = 936539) B936539
theorem B624455 : Blo 622298 624455 := bstep (se 1 (by rfl) ⟨468341, by rfl⟩ : syracuseStep 624455 = 936683) B936683
theorem B624475 : Blo 622298 624475 := bstep (se 1 (by rfl) ⟨468356, by rfl⟩ : syracuseStep 624475 = 936713) B936713
theorem B11962343 : Blo 622298 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B624751 : Blo 622298 624751 := bstep (se 1 (by rfl) ⟨468563, by rfl⟩ : syracuseStep 624751 = 937127) B937127
theorem B624847 : Blo 622298 624847 := bstep (se 1 (by rfl) ⟨468635, by rfl⟩ : syracuseStep 624847 = 937271) B937271
theorem B81889663 : Blo 622298 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B625055 : Blo 622298 625055 := bstep (se 1 (by rfl) ⟨468791, by rfl⟩ : syracuseStep 625055 = 937583) B937583
theorem B625103 : Blo 622298 625103 := bstep (se 1 (by rfl) ⟨468827, by rfl⟩ : syracuseStep 625103 = 937655) B937655
theorem B625135 : Blo 622298 625135 := bstep (se 1 (by rfl) ⟨468851, by rfl⟩ : syracuseStep 625135 = 937703) B937703
theorem B625243 : Blo 622298 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B625403 : Blo 622298 625403 := bstep (se 1 (by rfl) ⟨469052, by rfl⟩ : syracuseStep 625403 = 938105) B938105
theorem B625407 : Blo 622298 625407 := bstep (se 1 (by rfl) ⟨469055, by rfl⟩ : syracuseStep 625407 = 938111) B938111
theorem B1051879 : Blo 622298 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B625967 : Blo 622298 625967 := bstep (se 1 (by rfl) ⟨469475, by rfl⟩ : syracuseStep 625967 = 938951) B938951
theorem B625983 : Blo 622298 625983 := bstep (se 1 (by rfl) ⟨469487, by rfl⟩ : syracuseStep 625983 = 938975) B938975
theorem B626207 : Blo 622298 626207 := bstep (se 1 (by rfl) ⟨469655, by rfl⟩ : syracuseStep 626207 = 939311) B939311
theorem B2364011 : Blo 622298 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B1053391 : Blo 622298 1053391 := bstep (se 1 (by rfl) ⟨790043, by rfl⟩ : syracuseStep 1053391 = 1580087) B1580087
theorem B2528111 : Blo 622298 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B2659837 : Blo 622298 2659837 := bstep (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) B997439
theorem B2528921 : Blo 622298 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B2102975 : Blo 622298 2102975 := bstep (se 1 (by rfl) ⟨1577231, by rfl⟩ : syracuseStep 2102975 = 3154463) B3154463
theorem B2365787 : Blo 622298 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B2660795 : Blo 622298 2660795 := bstep (se 1 (by rfl) ⟨1995596, by rfl⟩ : syracuseStep 2660795 = 3991193) B3991193
theorem B2103785 : Blo 622298 2103785 := bstep (se 2 (by rfl) ⟨788919, by rfl⟩ : syracuseStep 2103785 = 1577839) B1577839
theorem B2103839 : Blo 622298 2103839 := bstep (se 1 (by rfl) ⟨1577879, by rfl⟩ : syracuseStep 2103839 = 3155759) B3155759
theorem B1055335 : Blo 622298 1055335 := bstep (se 1 (by rfl) ⟨791501, by rfl⟩ : syracuseStep 1055335 = 1583003) B1583003
theorem B1186463 : Blo 622298 1186463 := bstep (se 1 (by rfl) ⟨889847, by rfl⟩ : syracuseStep 1186463 = 1779695) B1779695
theorem B1055551 : Blo 622298 1055551 := bstep (se 1 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 1055551 = 1583327) B1583327
theorem B2399851 : Blo 622298 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B1777439 : Blo 622298 1777439 := bstep (se 1 (by rfl) ⟨1333079, by rfl⟩ : syracuseStep 1777439 = 2666159) B2666159
theorem B2400455 : Blo 622298 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B2367731 : Blo 622298 2367731 := bstep (se 1 (by rfl) ⟨1775798, by rfl⟩ : syracuseStep 2367731 = 3551597) B3551597
theorem B2531611 : Blo 622298 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B1188407 : Blo 622298 1188407 := bstep (se 1 (by rfl) ⟨891305, by rfl⟩ : syracuseStep 1188407 = 1782611) B1782611
theorem B1188847 : Blo 622298 1188847 := bstep (se 1 (by rfl) ⟨891635, by rfl⟩ : syracuseStep 1188847 = 1783271) B1783271
theorem B2368673 : Blo 622298 2368673 := bstep (se 2 (by rfl) ⟨888252, by rfl⟩ : syracuseStep 2368673 = 1776505) B1776505
theorem B10101995 : Blo 622298 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B2532637 : Blo 622298 2532637 := bstep (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) B949739
theorem B2663887 : Blo 622298 2663887 := bstep (se 1 (by rfl) ⟨1997915, by rfl⟩ : syracuseStep 2663887 = 3995831) B3995831
theorem B2106863 : Blo 622298 2106863 := bstep (se 1 (by rfl) ⟨1580147, by rfl⟩ : syracuseStep 2106863 = 3160295) B3160295
theorem B3384823 : Blo 622298 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B2107133 : Blo 622298 2107133 := bstep (se 3 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 2107133 = 790175) B790175
theorem B2369371 : Blo 622298 2369371 := bstep (se 1 (by rfl) ⟨1777028, by rfl⟩ : syracuseStep 2369371 = 3554057) B3554057
theorem B2893735 : Blo 622298 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B1779671 : Blo 622298 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B1583135 : Blo 622298 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B1124671 : Blo 622298 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B2992895 : Blo 622298 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B2370343 : Blo 622298 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B1780537 : Blo 622298 1780537 := bstep (se 2 (by rfl) ⟨667701, by rfl⟩ : syracuseStep 1780537 = 1335403) B1335403
theorem B3156893 : Blo 622298 3156893 := bstep (se 3 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 3156893 = 1183835) B1183835
theorem B3157055 : Blo 622298 3157055 := bstep (se 1 (by rfl) ⟨2367791, by rfl⟩ : syracuseStep 3157055 = 4735583) B4735583
theorem B1584431 : Blo 622298 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B5320151 : Blo 622298 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B2371103 : Blo 622298 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B798427 : Blo 622298 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B1126271 : Blo 622298 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B667975 : Blo 622298 667975 := bstep (se 1 (by rfl) ⟨500981, by rfl⟩ : syracuseStep 667975 = 1001963) B1001963
theorem B92385623 : Blo 622298 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B4010411 : Blo 622298 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B2372075 : Blo 622298 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B2274131 : Blo 622298 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B259077487 : Blo 622298 259077487 := bstep (se 1 (by rfl) ⟨194308115, by rfl⟩ : syracuseStep 259077487 = 388616231) B388616231
theorem B2373245 : Blo 622298 2373245 := bstep (se 3 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 2373245 = 889967) B889967
theorem B2111183 : Blo 622298 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B4732667 : Blo 622298 4732667 := bstep (se 1 (by rfl) ⟨3549500, by rfl⟩ : syracuseStep 4732667 = 7099001) B7099001
theorem B702247 : Blo 622298 702247 := bstep (se 1 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 702247 = 1053371) B1053371
theorem B18233225 : Blo 622298 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B15219251 : Blo 622298 15219251 := bstep (se 1 (by rfl) ⟨11414438, by rfl⟩ : syracuseStep 15219251 = 22828877) B22828877
theorem B3161591 : Blo 622298 3161591 := bstep (se 1 (by rfl) ⟨2371193, by rfl⟩ : syracuseStep 3161591 = 4742387) B4742387
theorem B2113019 : Blo 622298 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B2670191 : Blo 622298 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B7126703 : Blo 622298 7126703 := bstep (se 1 (by rfl) ⟨5345027, by rfl⟩ : syracuseStep 7126703 = 10690055) B10690055
theorem B933695 : Blo 622298 933695 := bstep (se 1 (by rfl) ⟨700271, by rfl⟩ : syracuseStep 933695 = 1400543) B1400543
theorem B933935 : Blo 622298 933935 := bstep (se 1 (by rfl) ⟨700451, by rfl⟩ : syracuseStep 933935 = 1400903) B1400903
theorem B10698803 : Blo 622298 10698803 := bstep (se 1 (by rfl) ⟨8024102, by rfl⟩ : syracuseStep 10698803 = 16048205) B16048205
theorem B933959 : Blo 622298 933959 := bstep (se 1 (by rfl) ⟨700469, by rfl⟩ : syracuseStep 933959 = 1400939) B1400939
theorem B934139 : Blo 622298 934139 := bstep (se 1 (by rfl) ⟨700604, by rfl⟩ : syracuseStep 934139 = 1401209) B1401209
theorem B934265 : Blo 622298 934265 := bstep (se 2 (by rfl) ⟨350349, by rfl⟩ : syracuseStep 934265 = 700699) B700699
theorem B934427 : Blo 622298 934427 := bstep (se 1 (by rfl) ⟨700820, by rfl⟩ : syracuseStep 934427 = 1401641) B1401641
theorem B934559 : Blo 622298 934559 := bstep (se 1 (by rfl) ⟨700919, by rfl⟩ : syracuseStep 934559 = 1401839) B1401839
theorem B934607 : Blo 622298 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B3162887 : Blo 622298 3162887 := bstep (se 1 (by rfl) ⟨2372165, by rfl⟩ : syracuseStep 3162887 = 4744331) B4744331
theorem B5325587 : Blo 622298 5325587 := bstep (se 1 (by rfl) ⟨3994190, by rfl⟩ : syracuseStep 5325587 = 7988381) B7988381
theorem B2376479 : Blo 622298 2376479 := bstep (se 1 (by rfl) ⟨1782359, by rfl⟩ : syracuseStep 2376479 = 3564719) B3564719
theorem B934727 : Blo 622298 934727 := bstep (se 1 (by rfl) ⟨701045, by rfl⟩ : syracuseStep 934727 = 1402091) B1402091
theorem B934793 : Blo 622298 934793 := bstep (se 2 (by rfl) ⟨350547, by rfl⟩ : syracuseStep 934793 = 701095) B701095
theorem B1000399 : Blo 622298 1000399 := bstep (se 1 (by rfl) ⟨750299, by rfl⟩ : syracuseStep 1000399 = 1500599) B1500599
theorem B5065297 : Blo 622298 5065297 := bstep (se 2 (by rfl) ⟨1899486, by rfl⟩ : syracuseStep 5065297 = 3798973) B3798973
theorem B2673233 : Blo 622298 2673233 := bstep (se 2 (by rfl) ⟨1002462, by rfl⟩ : syracuseStep 2673233 = 2004925) B2004925
theorem B937211 : Blo 622298 937211 := bstep (se 1 (by rfl) ⟨702908, by rfl⟩ : syracuseStep 937211 = 1405817) B1405817
theorem B3165479 : Blo 622298 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B7720363 : Blo 622298 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B937631 : Blo 622298 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B4738985 : Blo 622298 4738985 := bstep (se 2 (by rfl) ⟨1777119, by rfl⟩ : syracuseStep 4738985 = 3554239) B3554239
theorem B937961 : Blo 622298 937961 := bstep (se 2 (by rfl) ⟨351735, by rfl⟩ : syracuseStep 937961 = 703471) B703471
theorem B938015 : Blo 622298 938015 := bstep (se 1 (by rfl) ⟨703511, by rfl⟩ : syracuseStep 938015 = 1407023) B1407023
theorem B3199351 : Blo 622298 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B3592673 : Blo 622298 3592673 := bstep (se 2 (by rfl) ⟨1347252, by rfl⟩ : syracuseStep 3592673 = 2694505) B2694505
theorem B938543 : Blo 622298 938543 := bstep (se 1 (by rfl) ⟨703907, by rfl⟩ : syracuseStep 938543 = 1407815) B1407815
theorem B938729 : Blo 622298 938729 := bstep (se 2 (by rfl) ⟨352023, by rfl⟩ : syracuseStep 938729 = 704047) B704047
theorem B17126261 : Blo 622298 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B938873 : Blo 622298 938873 := bstep (se 2 (by rfl) ⟨352077, by rfl⟩ : syracuseStep 938873 = 704155) B704155
theorem B1332217 : Blo 622298 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B5329961 : Blo 622298 5329961 := bstep (se 2 (by rfl) ⟨1998735, by rfl⟩ : syracuseStep 5329961 = 3997471) B3997471
theorem B709799 : Blo 622298 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B4117711 : Blo 622298 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B4052663 : Blo 622298 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B3200957 : Blo 622298 3200957 := bstep (se 3 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 3200957 = 1200359) B1200359
theorem B23091713 : Blo 622298 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B20470283 : Blo 622298 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B2251577 : Blo 622298 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B12016471 : Blo 622298 12016471 := bstep (se 1 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 12016471 = 18024707) B18024707
theorem B1497977 : Blo 622298 1497977 := bstep (se 2 (by rfl) ⟨561741, by rfl⟩ : syracuseStep 1497977 = 1123483) B1123483
theorem B3563261 : Blo 622298 3563261 := bstep (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) B1336223
theorem B4808573 : Blo 622298 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B10149799 : Blo 622298 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B18014561 : Blo 622298 18014561 := bstep (se 2 (by rfl) ⟨6755460, by rfl⟩ : syracuseStep 18014561 = 13510921) B13510921
theorem B4317857 : Blo 622298 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B1402343 : Blo 622298 1402343 := bstep (se 1 (by rfl) ⟨1051757, by rfl⟩ : syracuseStep 1402343 = 2103515) B2103515
theorem B3565403 : Blo 622298 3565403 := bstep (se 1 (by rfl) ⟨2674052, by rfl⟩ : syracuseStep 3565403 = 5348105) B5348105
theorem B2255339 : Blo 622298 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B5073833 : Blo 622298 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B2845655 : Blo 622298 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1403873 : Blo 622298 1403873 := bstep (se 2 (by rfl) ⟨526452, by rfl⟩ : syracuseStep 1403873 = 1052905) B1052905
theorem B1404233 : Blo 622298 1404233 := bstep (se 2 (by rfl) ⟨526587, by rfl⟩ : syracuseStep 1404233 = 1053175) B1053175
theorem B1405241 : Blo 622298 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B20771851 : Blo 622298 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B5338331 : Blo 622298 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B1406537 : Blo 622298 1406537 := bstep (se 2 (by rfl) ⟨527451, by rfl⟩ : syracuseStep 1406537 = 1054903) B1054903
theorem B13465601 : Blo 622298 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B1407311 : Blo 622298 1407311 := bstep (se 1 (by rfl) ⟨1055483, by rfl⟩ : syracuseStep 1407311 = 2110967) B2110967
theorem B7109207 : Blo 622298 7109207 := bstep (se 1 (by rfl) ⟨5331905, by rfl⟩ : syracuseStep 7109207 = 10663811) B10663811
theorem B1408031 : Blo 622298 1408031 := bstep (se 1 (by rfl) ⟨1056023, by rfl⟩ : syracuseStep 1408031 = 2112047) B2112047
theorem B1408787 : Blo 622298 1408787 := bstep (se 1 (by rfl) ⟨1056590, by rfl⟩ : syracuseStep 1408787 = 2113181) B2113181
theorem B622527 : Blo 622298 622527 := bstep (se 1 (by rfl) ⟨466895, by rfl⟩ : syracuseStep 622527 = 933791) B933791
theorem B2162639 : Blo 622298 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B622587 : Blo 622298 622587 := bstep (se 1 (by rfl) ⟨466940, by rfl⟩ : syracuseStep 622587 = 933881) B933881
theorem B622623 : Blo 622298 622623 := bstep (se 1 (by rfl) ⟨466967, by rfl⟩ : syracuseStep 622623 = 933935) B933935
theorem B622639 : Blo 622298 622639 := bstep (se 1 (by rfl) ⟨466979, by rfl⟩ : syracuseStep 622639 = 933959) B933959
theorem B622759 : Blo 622298 622759 := bstep (se 1 (by rfl) ⟨467069, by rfl⟩ : syracuseStep 622759 = 934139) B934139
theorem B622843 : Blo 622298 622843 := bstep (se 1 (by rfl) ⟨467132, by rfl⟩ : syracuseStep 622843 = 934265) B934265
theorem B622951 : Blo 622298 622951 := bstep (se 1 (by rfl) ⟨467213, by rfl⟩ : syracuseStep 622951 = 934427) B934427
theorem B3375481 : Blo 622298 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B623039 : Blo 622298 623039 := bstep (se 1 (by rfl) ⟨467279, by rfl⟩ : syracuseStep 623039 = 934559) B934559
theorem B623071 : Blo 622298 623071 := bstep (se 1 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 623071 = 934607) B934607
theorem B623151 : Blo 622298 623151 := bstep (se 1 (by rfl) ⟨467363, by rfl⟩ : syracuseStep 623151 = 934727) B934727
theorem B623195 : Blo 622298 623195 := bstep (se 1 (by rfl) ⟨467396, by rfl⟩ : syracuseStep 623195 = 934793) B934793
theorem B1050185 : Blo 622298 1050185 := bstep (se 2 (by rfl) ⟨393819, by rfl⟩ : syracuseStep 1050185 = 787639) B787639
theorem B3376849 : Blo 622298 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B7571189 : Blo 622298 7571189 := bstep (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) B709799
theorem B1050745 : Blo 622298 1050745 := bstep (se 2 (by rfl) ⟨394029, by rfl⟩ : syracuseStep 1050745 = 788059) B788059
theorem B624807 : Blo 622298 624807 := bstep (se 1 (by rfl) ⟨468605, by rfl⟩ : syracuseStep 624807 = 937211) B937211
theorem B625087 : Blo 622298 625087 := bstep (se 1 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 625087 = 937631) B937631
theorem B625307 : Blo 622298 625307 := bstep (se 1 (by rfl) ⟨468980, by rfl⟩ : syracuseStep 625307 = 937961) B937961
theorem B625343 : Blo 622298 625343 := bstep (se 1 (by rfl) ⟨469007, by rfl⟩ : syracuseStep 625343 = 938015) B938015
theorem B2395115 : Blo 622298 2395115 := bstep (se 1 (by rfl) ⟨1796336, by rfl⟩ : syracuseStep 2395115 = 3592673) B3592673
theorem B625695 : Blo 622298 625695 := bstep (se 1 (by rfl) ⟨469271, by rfl⟩ : syracuseStep 625695 = 938543) B938543
theorem B1576007 : Blo 622298 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B625819 : Blo 622298 625819 := bstep (se 1 (by rfl) ⟨469364, by rfl⟩ : syracuseStep 625819 = 938729) B938729
theorem B109186217 : Blo 622298 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B625915 : Blo 622298 625915 := bstep (se 1 (by rfl) ⟨469436, by rfl⟩ : syracuseStep 625915 = 938873) B938873
theorem B2133971 : Blo 622298 2133971 := bstep (se 1 (by rfl) ⟨1600478, by rfl⟩ : syracuseStep 2133971 = 3200957) B3200957
theorem B1577191 : Blo 622298 1577191 := bstep (se 1 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 1577191 = 2365787) B2365787
theorem B1773863 : Blo 622298 1773863 := bstep (se 1 (by rfl) ⟨1330397, by rfl⟩ : syracuseStep 1773863 = 2660795) B2660795
theorem B790975 : Blo 622298 790975 := bstep (se 1 (by rfl) ⟨593231, by rfl⟩ : syracuseStep 790975 = 1186463) B1186463
theorem B10293817 : Blo 622298 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B1184959 : Blo 622298 1184959 := bstep (se 1 (by rfl) ⟨888719, by rfl⟩ : syracuseStep 1184959 = 1777439) B1777439
theorem B1578487 : Blo 622298 1578487 := bstep (se 1 (by rfl) ⟨1183865, by rfl⟩ : syracuseStep 1578487 = 2367731) B2367731
theorem B792271 : Blo 622298 792271 := bstep (se 1 (by rfl) ⟨594203, by rfl⟩ : syracuseStep 792271 = 1188407) B1188407
theorem B890633 : Blo 622298 890633 := bstep (se 2 (by rfl) ⟨333987, by rfl⟩ : syracuseStep 890633 = 667975) B667975
theorem B4265801 : Blo 622298 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B1579115 : Blo 622298 1579115 := bstep (se 1 (by rfl) ⟨1184336, by rfl⟩ : syracuseStep 1579115 = 2368673) B2368673
theorem B1776289 : Blo 622298 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B27695801 : Blo 622298 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B1055423 : Blo 622298 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B2104595 : Blo 622298 2104595 := bstep (se 1 (by rfl) ⟨1578446, by rfl⟩ : syracuseStep 2104595 = 3156893) B3156893
theorem B3382555 : Blo 622298 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B3546449 : Blo 622298 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B2104703 : Blo 622298 2104703 := bstep (se 1 (by rfl) ⟨1578527, by rfl⟩ : syracuseStep 2104703 = 3157055) B3157055
theorem B6004205 : Blo 622298 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B1056287 : Blo 622298 1056287 := bstep (se 1 (by rfl) ⟨792215, by rfl⟩ : syracuseStep 1056287 = 1584431) B1584431
theorem B3546767 : Blo 622298 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B1580735 : Blo 622298 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B1581383 : Blo 622298 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B1516087 : Blo 622298 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B1582163 : Blo 622298 1582163 := bstep (se 1 (by rfl) ⟨1186622, by rfl⟩ : syracuseStep 1582163 = 2373245) B2373245
theorem B3155111 : Blo 622298 3155111 := bstep (se 1 (by rfl) ⟨2366333, by rfl⟩ : syracuseStep 3155111 = 4732667) B4732667
theorem B2107727 : Blo 622298 2107727 := bstep (se 1 (by rfl) ⟨1580795, by rfl⟩ : syracuseStep 2107727 = 3161591) B3161591
theorem B1780127 : Blo 622298 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2108591 : Blo 622298 2108591 := bstep (se 1 (by rfl) ⟨1581443, by rfl⟩ : syracuseStep 2108591 = 3162887) B3162887
theorem B3550391 : Blo 622298 3550391 := bstep (se 1 (by rfl) ⟨2662793, by rfl⟩ : syracuseStep 3550391 = 5325587) B5325587
theorem B6401213 : Blo 622298 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B1584319 : Blo 622298 1584319 := bstep (se 1 (by rfl) ⟨1188239, by rfl⟩ : syracuseStep 1584319 = 2376479) B2376479
theorem B10694429 : Blo 622298 10694429 := bstep (se 3 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 10694429 = 4010411) B4010411
theorem B1585129 : Blo 622298 1585129 := bstep (se 2 (by rfl) ⟨594423, by rfl⟩ : syracuseStep 1585129 = 1188847) B1188847
theorem B7974895 : Blo 622298 7974895 := bstep (se 1 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 7974895 = 11962343) B11962343
theorem B1782155 : Blo 622298 1782155 := bstep (se 1 (by rfl) ⟨1336616, by rfl⟩ : syracuseStep 1782155 = 2673233) B2673233
theorem B3551849 : Blo 622298 3551849 := bstep (se 2 (by rfl) ⟨1331943, by rfl⟩ : syracuseStep 3551849 = 2663887) B2663887
theorem B2110319 : Blo 622298 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B3159161 : Blo 622298 3159161 := bstep (se 2 (by rfl) ⟨1184685, by rfl⟩ : syracuseStep 3159161 = 2369371) B2369371
theorem B3159323 : Blo 622298 3159323 := bstep (se 1 (by rfl) ⟨2369492, by rfl⟩ : syracuseStep 3159323 = 4738985) B4738985
theorem B27014917 : Blo 622298 27014917 := bstep (se 4 (by rfl) ⟨2532648, by rfl⟩ : syracuseStep 27014917 = 5065297) B5065297
theorem B1685407 : Blo 622298 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B11417507 : Blo 622298 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B3553307 : Blo 622298 3553307 := bstep (se 1 (by rfl) ⟨2664980, by rfl⟩ : syracuseStep 3553307 = 5329961) B5329961
theorem B3160457 : Blo 622298 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B2374049 : Blo 622298 2374049 := bstep (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) B1780537
theorem B1685947 : Blo 622298 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B2701775 : Blo 622298 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B13646855 : Blo 622298 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B998651 : Blo 622298 998651 := bstep (se 1 (by rfl) ⟨748988, by rfl⟩ : syracuseStep 998651 = 1497977) B1497977
theorem B1064569 : Blo 622298 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B2375507 : Blo 622298 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B12009707 : Blo 622298 12009707 := bstep (se 1 (by rfl) ⟨9007280, by rfl⟩ : syracuseStep 12009707 = 18014561) B18014561
theorem B6734663 : Blo 622298 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B934895 : Blo 622298 934895 := bstep (se 1 (by rfl) ⟨701171, by rfl⟩ : syracuseStep 934895 = 1402343) B1402343
theorem B2376935 : Blo 622298 2376935 := bstep (se 1 (by rfl) ⟨1782701, by rfl⟩ : syracuseStep 2376935 = 3565403) B3565403
theorem B5490281 : Blo 622298 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B935915 : Blo 622298 935915 := bstep (se 1 (by rfl) ⟨701936, by rfl⟩ : syracuseStep 935915 = 1403873) B1403873
theorem B936155 : Blo 622298 936155 := bstep (se 1 (by rfl) ⟨702116, by rfl⟩ : syracuseStep 936155 = 1404233) B1404233
theorem B936329 : Blo 622298 936329 := bstep (se 2 (by rfl) ⟨351123, by rfl⟩ : syracuseStep 936329 = 702247) B702247
theorem B936827 : Blo 622298 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B61590415 : Blo 622298 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B12799205 : Blo 622298 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B3558887 : Blo 622298 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B937691 : Blo 622298 937691 := bstep (se 1 (by rfl) ⟨703268, by rfl⟩ : syracuseStep 937691 = 1406537) B1406537
theorem B938207 : Blo 622298 938207 := bstep (se 1 (by rfl) ⟨703655, by rfl⟩ : syracuseStep 938207 = 1407311) B1407311
theorem B10146167 : Blo 622298 10146167 := bstep (se 1 (by rfl) ⟨7609625, by rfl⟩ : syracuseStep 10146167 = 15219251) B15219251
theorem B4739471 : Blo 622298 4739471 := bstep (se 1 (by rfl) ⟨3554603, by rfl⟩ : syracuseStep 4739471 = 7109207) B7109207
theorem B938687 : Blo 622298 938687 := bstep (se 1 (by rfl) ⟨704015, by rfl⟩ : syracuseStep 938687 = 1408031) B1408031
theorem B3003389 : Blo 622298 3003389 := bstep (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) B1126271
theorem B939191 : Blo 622298 939191 := bstep (se 1 (by rfl) ⟨704393, by rfl⟩ : syracuseStep 939191 = 1408787) B1408787
theorem B7132535 : Blo 622298 7132535 := bstep (se 1 (by rfl) ⟨5349401, by rfl⟩ : syracuseStep 7132535 = 10698803) B10698803
theorem B939431 : Blo 622298 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B4282283 : Blo 622298 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1333865 : Blo 622298 1333865 := bstep (se 2 (by rfl) ⟨500199, by rfl⟩ : syracuseStep 1333865 = 1000399) B1000399
theorem B4513097 : Blo 622298 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B3858313 : Blo 622298 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B1499561 : Blo 622298 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B1401983 : Blo 622298 1401983 := bstep (se 1 (by rfl) ⟨1051487, by rfl⟩ : syracuseStep 1401983 = 2102975) B2102975
theorem B1402505 : Blo 622298 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B1402523 : Blo 622298 1402523 := bstep (se 1 (by rfl) ⟨1051892, by rfl⟩ : syracuseStep 1402523 = 2103785) B2103785
theorem B15394475 : Blo 622298 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B1402559 : Blo 622298 1402559 := bstep (se 1 (by rfl) ⟨1051919, by rfl⟩ : syracuseStep 1402559 = 2103839) B2103839
theorem B4745789 : Blo 622298 4745789 := bstep (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) B1779671
theorem B3205715 : Blo 622298 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B2878571 : Blo 622298 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B1404521 : Blo 622298 1404521 := bstep (se 2 (by rfl) ⟨526695, by rfl⟩ : syracuseStep 1404521 = 1053391) B1053391
theorem B1404575 : Blo 622298 1404575 := bstep (se 1 (by rfl) ⟨1053431, by rfl⟩ : syracuseStep 1404575 = 2106863) B2106863
theorem B1404755 : Blo 622298 1404755 := bstep (se 1 (by rfl) ⟨1053566, by rfl⟩ : syracuseStep 1404755 = 2107133) B2107133
theorem B1503559 : Blo 622298 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B345436649 : Blo 622298 345436649 := bstep (se 2 (by rfl) ⟨129538743, by rfl⟩ : syracuseStep 345436649 = 259077487) B259077487
theorem B1995263 : Blo 622298 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B1897103 : Blo 622298 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B1407113 : Blo 622298 1407113 := bstep (se 2 (by rfl) ⟨527667, by rfl⟩ : syracuseStep 1407113 = 1055335) B1055335
theorem B1407401 : Blo 622298 1407401 := bstep (se 2 (by rfl) ⟨527775, by rfl⟩ : syracuseStep 1407401 = 1055551) B1055551
theorem B16021961 : Blo 622298 16021961 := bstep (se 2 (by rfl) ⟨6008235, by rfl⟩ : syracuseStep 16021961 = 12016471) B12016471
theorem B1407455 : Blo 622298 1407455 := bstep (se 1 (by rfl) ⟨1055591, by rfl⟩ : syracuseStep 1407455 = 2111183) B2111183
theorem B12155483 : Blo 622298 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B8977067 : Blo 622298 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B1408679 : Blo 622298 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B4751135 : Blo 622298 4751135 := bstep (se 1 (by rfl) ⟨3563351, by rfl⟩ : syracuseStep 4751135 = 7126703) B7126703
theorem B5767037 : Blo 622298 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B622463 : Blo 622298 622463 := bstep (se 1 (by rfl) ⟨466847, by rfl⟩ : syracuseStep 622463 = 933695) B933695
theorem B13533065 : Blo 622298 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B4489775 : Blo 622298 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B623263 : Blo 622298 623263 := bstep (se 1 (by rfl) ⟨467447, by rfl⟩ : syracuseStep 623263 = 934895) B934895
theorem B623943 : Blo 622298 623943 := bstep (se 1 (by rfl) ⟨467957, by rfl⟩ : syracuseStep 623943 = 935915) B935915
theorem B624103 : Blo 622298 624103 := bstep (se 1 (by rfl) ⟨468077, by rfl⟩ : syracuseStep 624103 = 936155) B936155
theorem B624219 : Blo 622298 624219 := bstep (se 1 (by rfl) ⟨468164, by rfl⟩ : syracuseStep 624219 = 936329) B936329
theorem B624551 : Blo 622298 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B1050671 : Blo 622298 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B625127 : Blo 622298 625127 := bstep (se 1 (by rfl) ⟨468845, by rfl⟩ : syracuseStep 625127 = 937691) B937691
theorem B625471 : Blo 622298 625471 := bstep (se 1 (by rfl) ⟨469103, by rfl⟩ : syracuseStep 625471 = 938207) B938207
theorem B1182575 : Blo 622298 1182575 := bstep (se 1 (by rfl) ⟨886931, by rfl⟩ : syracuseStep 1182575 = 1773863) B1773863
theorem B625791 : Blo 622298 625791 := bstep (se 1 (by rfl) ⟨469343, by rfl⟩ : syracuseStep 625791 = 938687) B938687
theorem B2002259 : Blo 622298 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B626127 : Blo 622298 626127 := bstep (se 1 (by rfl) ⟨469595, by rfl⟩ : syracuseStep 626127 = 939191) B939191
theorem B4755023 : Blo 622298 4755023 := bstep (se 1 (by rfl) ⟨3566267, by rfl⟩ : syracuseStep 4755023 = 7132535) B7132535
theorem B626287 : Blo 622298 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B82120553 : Blo 622298 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B2854855 : Blo 622298 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B1052743 : Blo 622298 1052743 := bstep (se 1 (by rfl) ⟨789557, by rfl⟩ : syracuseStep 1052743 = 1579115) B1579115
theorem B20189837 : Blo 622298 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B2364299 : Blo 622298 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B4002803 : Blo 622298 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B2364511 : Blo 622298 2364511 := bstep (se 1 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 2364511 = 3546767) B3546767
theorem B1053823 : Blo 622298 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B1054255 : Blo 622298 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B2102921 : Blo 622298 2102921 := bstep (se 2 (by rfl) ⟨788595, by rfl⟩ : syracuseStep 2102921 = 1577191) B1577191
theorem B2004745 : Blo 622298 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B1054633 : Blo 622298 1054633 := bstep (se 2 (by rfl) ⟨395487, by rfl⟩ : syracuseStep 1054633 = 790975) B790975
theorem B1054775 : Blo 622298 1054775 := bstep (se 1 (by rfl) ⟨791081, by rfl⟩ : syracuseStep 1054775 = 1582163) B1582163
theorem B2103407 : Blo 622298 2103407 := bstep (se 1 (by rfl) ⟨1577555, by rfl⟩ : syracuseStep 2103407 = 3155111) B3155111
theorem B10262983 : Blo 622298 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B1579945 : Blo 622298 1579945 := bstep (se 2 (by rfl) ⟨592479, by rfl⟩ : syracuseStep 1579945 = 1184959) B1184959
theorem B1186751 : Blo 622298 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B2104649 : Blo 622298 2104649 := bstep (se 2 (by rfl) ⟨789243, by rfl⟩ : syracuseStep 2104649 = 1578487) B1578487
theorem B2366927 : Blo 622298 2366927 := bstep (se 1 (by rfl) ⟨1775195, by rfl⟩ : syracuseStep 2366927 = 3550391) B3550391
theorem B4267475 : Blo 622298 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B1056361 : Blo 622298 1056361 := bstep (se 2 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 1056361 = 792271) B792271
theorem B36019889 : Blo 622298 36019889 := bstep (se 2 (by rfl) ⟨13507458, by rfl⟩ : syracuseStep 36019889 = 27014917) B27014917
theorem B1188103 : Blo 622298 1188103 := bstep (se 1 (by rfl) ⟨891077, by rfl⟩ : syracuseStep 1188103 = 1782155) B1782155
theorem B2367899 : Blo 622298 2367899 := bstep (se 1 (by rfl) ⟨1775924, by rfl⟩ : syracuseStep 2367899 = 3551849) B3551849
theorem B2106107 : Blo 622298 2106107 := bstep (se 1 (by rfl) ⟨1579580, by rfl⟩ : syracuseStep 2106107 = 3159161) B3159161
theorem B2106215 : Blo 622298 2106215 := bstep (se 1 (by rfl) ⟨1579661, by rfl⟩ : syracuseStep 2106215 = 3159323) B3159323
theorem B12034925 : Blo 622298 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B2368385 : Blo 622298 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B7611671 : Blo 622298 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B2368871 : Blo 622298 2368871 := bstep (se 1 (by rfl) ⟨1776653, by rfl⟩ : syracuseStep 2368871 = 3553307) B3553307
theorem B2106971 : Blo 622298 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B1582699 : Blo 622298 1582699 := bstep (se 1 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 1582699 = 2374049) B2374049
theorem B8103655 : Blo 622298 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B1419425 : Blo 622298 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B665767 : Blo 622298 665767 := bstep (se 1 (by rfl) ⟨499325, by rfl⟩ : syracuseStep 665767 = 998651) B998651
theorem B1583671 : Blo 622298 1583671 := bstep (se 1 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 1583671 = 2375507) B2375507
theorem B3844691 : Blo 622298 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B9022043 : Blo 622298 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B8006471 : Blo 622298 8006471 := bstep (se 1 (by rfl) ⟨6004853, by rfl⟩ : syracuseStep 8006471 = 12009707) B12009707
theorem B4500641 : Blo 622298 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B1584623 : Blo 622298 1584623 := bstep (se 1 (by rfl) ⟨1188467, by rfl⟩ : syracuseStep 1584623 = 2376935) B2376935
theorem B700123 : Blo 622298 700123 := bstep (se 1 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 700123 = 1050185) B1050185
theorem B5058941 : Blo 622298 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B72790811 : Blo 622298 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B8532803 : Blo 622298 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B4502465 : Blo 622298 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B2372591 : Blo 622298 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B1422647 : Blo 622298 1422647 := bstep (se 1 (by rfl) ⟨1066985, by rfl⟩ : syracuseStep 1422647 = 2133971) B2133971
theorem B6764111 : Blo 622298 6764111 := bstep (se 1 (by rfl) ⟨5073083, by rfl⟩ : syracuseStep 6764111 = 10146167) B10146167
theorem B3159647 : Blo 622298 3159647 := bstep (se 1 (by rfl) ⟨2369735, by rfl⟩ : syracuseStep 3159647 = 4739471) B4739471
theorem B2112425 : Blo 622298 2112425 := bstep (se 2 (by rfl) ⟨792159, by rfl⟩ : syracuseStep 2112425 = 1584319) B1584319
theorem B703615 : Blo 622298 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B2375021 : Blo 622298 2375021 := bstep (se 3 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 2375021 = 890633) B890633
theorem B704191 : Blo 622298 704191 := bstep (se 1 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 704191 = 1056287) B1056287
theorem B2113505 : Blo 622298 2113505 := bstep (se 2 (by rfl) ⟨792564, by rfl⟩ : syracuseStep 2113505 = 1585129) B1585129
theorem B10633193 : Blo 622298 10633193 := bstep (se 2 (by rfl) ⟨3987447, by rfl⟩ : syracuseStep 10633193 = 7974895) B7974895
theorem B999707 : Blo 622298 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B934655 : Blo 622298 934655 := bstep (se 1 (by rfl) ⟨700991, by rfl⟩ : syracuseStep 934655 = 1401983) B1401983
theorem B935003 : Blo 622298 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B935015 : Blo 622298 935015 := bstep (se 1 (by rfl) ⟨701261, by rfl⟩ : syracuseStep 935015 = 1402523) B1402523
theorem B935039 : Blo 622298 935039 := bstep (se 1 (by rfl) ⟨701279, by rfl⟩ : syracuseStep 935039 = 1402559) B1402559
theorem B3556973 : Blo 622298 3556973 := bstep (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) B1333865
theorem B3163859 : Blo 622298 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B1919047 : Blo 622298 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B936347 : Blo 622298 936347 := bstep (se 1 (by rfl) ⟨702260, by rfl⟩ : syracuseStep 936347 = 1404521) B1404521
theorem B936383 : Blo 622298 936383 := bstep (se 1 (by rfl) ⟨702287, by rfl⟩ : syracuseStep 936383 = 1404575) B1404575
theorem B7129619 : Blo 622298 7129619 := bstep (se 1 (by rfl) ⟨5347214, by rfl⟩ : syracuseStep 7129619 = 10694429) B10694429
theorem B2247209 : Blo 622298 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B936503 : Blo 622298 936503 := bstep (se 1 (by rfl) ⟨702377, by rfl⟩ : syracuseStep 936503 = 1404755) B1404755
theorem B1330175 : Blo 622298 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B2247929 : Blo 622298 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B938075 : Blo 622298 938075 := bstep (se 1 (by rfl) ⟨703556, by rfl⟩ : syracuseStep 938075 = 1407113) B1407113
theorem B938267 : Blo 622298 938267 := bstep (se 1 (by rfl) ⟨703700, by rfl⟩ : syracuseStep 938267 = 1407401) B1407401
theorem B938303 : Blo 622298 938303 := bstep (se 1 (by rfl) ⟨703727, by rfl⟩ : syracuseStep 938303 = 1407455) B1407455
theorem B4510073 : Blo 622298 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B5984711 : Blo 622298 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B9097903 : Blo 622298 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B939119 : Blo 622298 939119 := bstep (se 1 (by rfl) ⟨704339, by rfl⟩ : syracuseStep 939119 = 1408679) B1408679
theorem B3167423 : Blo 622298 3167423 := bstep (se 1 (by rfl) ⟨2375567, by rfl⟩ : syracuseStep 3167423 = 4751135) B4751135
theorem B2021449 : Blo 622298 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B1596743 : Blo 622298 1596743 := bstep (se 1 (by rfl) ⟨1197557, by rfl⟩ : syracuseStep 1596743 = 2395115) B2395115
theorem B1400993 : Blo 622298 1400993 := bstep (se 2 (by rfl) ⟨525372, by rfl⟩ : syracuseStep 1400993 = 1050745) B1050745
theorem B2843867 : Blo 622298 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B14640749 : Blo 622298 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B1403063 : Blo 622298 1403063 := bstep (se 1 (by rfl) ⟨1052297, by rfl⟩ : syracuseStep 1403063 = 2104595) B2104595
theorem B1403135 : Blo 622298 1403135 := bstep (se 1 (by rfl) ⟨1052351, by rfl⟩ : syracuseStep 1403135 = 2104703) B2104703
theorem B13725089 : Blo 622298 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B8548573 : Blo 622298 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B1405151 : Blo 622298 1405151 := bstep (se 1 (by rfl) ⟨1053863, by rfl⟩ : syracuseStep 1405151 = 2107727) B2107727
theorem B73855469 : Blo 622298 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B1405727 : Blo 622298 1405727 := bstep (se 1 (by rfl) ⟨1054295, by rfl⟩ : syracuseStep 1405727 = 2108591) B2108591
theorem B230291099 : Blo 622298 230291099 := bstep (se 1 (by rfl) ⟨172718324, by rfl⟩ : syracuseStep 230291099 = 345436649) B345436649
theorem B1406879 : Blo 622298 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B10681307 : Blo 622298 10681307 := bstep (se 1 (by rfl) ⟨8010980, by rfl⟩ : syracuseStep 10681307 = 16021961) B16021961
theorem B1801183 : Blo 622298 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B5144417 : Blo 622298 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B623103 : Blo 622298 623103 := bstep (se 1 (by rfl) ⟨467327, by rfl⟩ : syracuseStep 623103 = 934655) B934655
theorem B623335 : Blo 622298 623335 := bstep (se 1 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 623335 = 935003) B935003
theorem B623343 : Blo 622298 623343 := bstep (se 1 (by rfl) ⟨467507, by rfl⟩ : syracuseStep 623343 = 935015) B935015
theorem B623359 : Blo 622298 623359 := bstep (se 1 (by rfl) ⟨467519, by rfl⟩ : syracuseStep 623359 = 935039) B935039
theorem B624231 : Blo 622298 624231 := bstep (se 1 (by rfl) ⟨468173, by rfl⟩ : syracuseStep 624231 = 936347) B936347
theorem B624255 : Blo 622298 624255 := bstep (se 1 (by rfl) ⟨468191, by rfl⟩ : syracuseStep 624255 = 936383) B936383
theorem B15140533 : Blo 622298 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B4753079 : Blo 622298 4753079 := bstep (se 1 (by rfl) ⟨3564809, by rfl⟩ : syracuseStep 4753079 = 7129619) B7129619
theorem B624335 : Blo 622298 624335 := bstep (se 1 (by rfl) ⟨468251, by rfl⟩ : syracuseStep 624335 = 936503) B936503
theorem B788383 : Blo 622298 788383 := bstep (se 1 (by rfl) ⟨591287, by rfl⟩ : syracuseStep 788383 = 1182575) B1182575
theorem B886783 : Blo 622298 886783 := bstep (se 1 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 886783 = 1330175) B1330175
theorem B625383 : Blo 622298 625383 := bstep (se 1 (by rfl) ⟨469037, by rfl⟩ : syracuseStep 625383 = 938075) B938075
theorem B2558729 : Blo 622298 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B625511 : Blo 622298 625511 := bstep (se 1 (by rfl) ⟨469133, by rfl⟩ : syracuseStep 625511 = 938267) B938267
theorem B625535 : Blo 622298 625535 := bstep (se 1 (by rfl) ⟨469151, by rfl⟩ : syracuseStep 625535 = 938303) B938303
theorem B887689 : Blo 622298 887689 := bstep (se 2 (by rfl) ⟨332883, by rfl⟩ : syracuseStep 887689 = 665767) B665767
theorem B1576199 : Blo 622298 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B626079 : Blo 622298 626079 := bstep (se 1 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 626079 = 939119) B939119
theorem B1577951 : Blo 622298 1577951 := bstep (se 1 (by rfl) ⟨1183463, by rfl⟩ : syracuseStep 1577951 = 2366927) B2366927
theorem B3806473 : Blo 622298 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B1578599 : Blo 622298 1578599 := bstep (se 1 (by rfl) ⟨1183949, by rfl⟩ : syracuseStep 1578599 = 2367899) B2367899
theorem B1578923 : Blo 622298 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B1579247 : Blo 622298 1579247 := bstep (se 1 (by rfl) ⟨1184435, by rfl⟩ : syracuseStep 1579247 = 2368871) B2368871
theorem B3152681 : Blo 622298 3152681 := bstep (se 2 (by rfl) ⟨1182255, by rfl⟩ : syracuseStep 3152681 = 2364511) B2364511
theorem B2563127 : Blo 622298 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B9150059 : Blo 622298 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B1056415 : Blo 622298 1056415 := bstep (se 1 (by rfl) ⟨792311, by rfl⟩ : syracuseStep 1056415 = 1584623) B1584623
theorem B2695265 : Blo 622298 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B12001709 : Blo 622298 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B1581727 : Blo 622298 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B2106431 : Blo 622298 2106431 := bstep (se 1 (by rfl) ⟨1579823, by rfl⟩ : syracuseStep 2106431 = 3159647) B3159647
theorem B153527399 : Blo 622298 153527399 := bstep (se 1 (by rfl) ⟨115145549, by rfl⟩ : syracuseStep 153527399 = 230291099) B230291099
theorem B2106593 : Blo 622298 2106593 := bstep (se 2 (by rfl) ⟨789972, by rfl⟩ : syracuseStep 2106593 = 1579945) B1579945
theorem B2401577 : Blo 622298 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B7120871 : Blo 622298 7120871 := bstep (se 1 (by rfl) ⟨5340653, by rfl⟩ : syracuseStep 7120871 = 10681307) B10681307
theorem B1583347 : Blo 622298 1583347 := bstep (se 1 (by rfl) ⟨1187510, by rfl⟩ : syracuseStep 1583347 = 2375021) B2375021
theorem B7088795 : Blo 622298 7088795 := bstep (se 1 (by rfl) ⟨5316596, by rfl⟩ : syracuseStep 7088795 = 10633193) B10633193
theorem B1584137 : Blo 622298 1584137 := bstep (se 2 (by rfl) ⟨594051, by rfl⟩ : syracuseStep 1584137 = 1188103) B1188103
theorem B2993183 : Blo 622298 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B2665885 : Blo 622298 2665885 := bstep (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) B999707
theorem B2371315 : Blo 622298 2371315 := bstep (se 1 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 2371315 = 3556973) B3556973
theorem B2109239 : Blo 622298 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B700447 : Blo 622298 700447 := bstep (se 1 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 700447 = 1050671) B1050671
theorem B2110265 : Blo 622298 2110265 := bstep (se 2 (by rfl) ⟨791349, by rfl⟩ : syracuseStep 2110265 = 1582699) B1582699
theorem B22754141 : Blo 622298 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B7583645 : Blo 622298 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B2668535 : Blo 622298 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B20297789 : Blo 622298 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B2111561 : Blo 622298 2111561 := bstep (se 2 (by rfl) ⟨791835, by rfl⟩ : syracuseStep 2111561 = 1583671) B1583671
theorem B2111615 : Blo 622298 2111615 := bstep (se 1 (by rfl) ⟨1583711, by rfl⟩ : syracuseStep 2111615 = 3167423) B3167423
theorem B703183 : Blo 622298 703183 := bstep (se 1 (by rfl) ⟨527387, by rfl⟩ : syracuseStep 703183 = 1054775) B1054775
theorem B1064495 : Blo 622298 1064495 := bstep (se 1 (by rfl) ⟨798371, by rfl⟩ : syracuseStep 1064495 = 1596743) B1596743
theorem B933497 : Blo 622298 933497 := bstep (se 2 (by rfl) ⟨350061, by rfl⟩ : syracuseStep 933497 = 700123) B700123
theorem B933995 : Blo 622298 933995 := bstep (se 1 (by rfl) ⟨700496, by rfl⟩ : syracuseStep 933995 = 1400993) B1400993
theorem B935375 : Blo 622298 935375 := bstep (se 1 (by rfl) ⟨701531, by rfl⟩ : syracuseStep 935375 = 1403063) B1403063
theorem B935423 : Blo 622298 935423 := bstep (se 1 (by rfl) ⟨701567, by rfl⟩ : syracuseStep 935423 = 1403135) B1403135
theorem B6014695 : Blo 622298 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B2672993 : Blo 622298 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B3164669 : Blo 622298 3164669 := bstep (se 3 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 3164669 = 1186751) B1186751
theorem B936767 : Blo 622298 936767 := bstep (se 1 (by rfl) ⟨702575, by rfl⟩ : syracuseStep 936767 = 1405151) B1405151
theorem B49236979 : Blo 622298 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B937151 : Blo 622298 937151 := bstep (se 1 (by rfl) ⟨702863, by rfl⟩ : syracuseStep 937151 = 1405727) B1405727
theorem B13683977 : Blo 622298 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B3001643 : Blo 622298 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B4509407 : Blo 622298 4509407 := bstep (se 1 (by rfl) ⟨3382055, by rfl⟩ : syracuseStep 4509407 = 6764111) B6764111
theorem B937919 : Blo 622298 937919 := bstep (se 1 (by rfl) ⟨703439, by rfl⟩ : syracuseStep 937919 = 1406879) B1406879
theorem B938153 : Blo 622298 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B938921 : Blo 622298 938921 := bstep (se 2 (by rfl) ⟨352095, by rfl⟩ : syracuseStep 938921 = 704191) B704191
theorem B3429611 : Blo 622298 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B13490509 : Blo 622298 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B1498139 : Blo 622298 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B1498619 : Blo 622298 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B3170015 : Blo 622298 3170015 := bstep (se 1 (by rfl) ⟨2377511, by rfl⟩ : syracuseStep 3170015 = 4755023) B4755023
theorem B54747035 : Blo 622298 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B3006715 : Blo 622298 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B3989807 : Blo 622298 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B13459891 : Blo 622298 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B48522149 : Blo 622298 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B1401947 : Blo 622298 1401947 := bstep (se 1 (by rfl) ⟨1051460, by rfl⟩ : syracuseStep 1401947 = 2102921) B2102921
theorem B1402271 : Blo 622298 1402271 := bstep (se 1 (by rfl) ⟨1051703, by rfl⟩ : syracuseStep 1402271 = 2103407) B2103407
theorem B1403099 : Blo 622298 1403099 := bstep (se 1 (by rfl) ⟨1052324, by rfl⟩ : syracuseStep 1403099 = 2104649) B2104649
theorem B2844983 : Blo 622298 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B24013259 : Blo 622298 24013259 := bstep (se 1 (by rfl) ⟨18009944, by rfl⟩ : syracuseStep 24013259 = 36019889) B36019889
theorem B1403657 : Blo 622298 1403657 := bstep (se 2 (by rfl) ⟨526371, by rfl⟩ : syracuseStep 1403657 = 1052743) B1052743
theorem B11398097 : Blo 622298 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B1404071 : Blo 622298 1404071 := bstep (se 1 (by rfl) ⟨1053053, by rfl⟩ : syracuseStep 1404071 = 2106107) B2106107
theorem B1404143 : Blo 622298 1404143 := bstep (se 1 (by rfl) ⟨1053107, by rfl⟩ : syracuseStep 1404143 = 2106215) B2106215
theorem B8023283 : Blo 622298 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B1404647 : Blo 622298 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B9760499 : Blo 622298 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B1405097 : Blo 622298 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B5337647 : Blo 622298 5337647 := bstep (se 1 (by rfl) ⟨4003235, by rfl⟩ : syracuseStep 5337647 = 8006471) B8006471
theorem B1405673 : Blo 622298 1405673 := bstep (se 2 (by rfl) ⟨527127, by rfl⟩ : syracuseStep 1405673 = 1054255) B1054255
theorem B1406177 : Blo 622298 1406177 := bstep (se 2 (by rfl) ⟨527316, by rfl⟩ : syracuseStep 1406177 = 1054633) B1054633
theorem B48527207 : Blo 622298 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B948431 : Blo 622298 948431 := bstep (se 1 (by rfl) ⟨711323, by rfl⟩ : syracuseStep 948431 = 1422647) B1422647
theorem B5339357 : Blo 622298 5339357 := bstep (se 3 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 5339357 = 2002259) B2002259
theorem B43219493 : Blo 622298 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B1408283 : Blo 622298 1408283 := bstep (se 1 (by rfl) ⟨1056212, by rfl⟩ : syracuseStep 1408283 = 2112425) B2112425
theorem B1408481 : Blo 622298 1408481 := bstep (se 2 (by rfl) ⟨528180, by rfl⟩ : syracuseStep 1408481 = 1056361) B1056361
theorem B1409003 : Blo 622298 1409003 := bstep (se 1 (by rfl) ⟨1056752, by rfl⟩ : syracuseStep 1409003 = 2113505) B2113505
theorem B622663 : Blo 622298 622663 := bstep (se 1 (by rfl) ⟨466997, by rfl⟩ : syracuseStep 622663 = 933995) B933995
theorem B623583 : Blo 622298 623583 := bstep (se 1 (by rfl) ⟨467687, by rfl⟩ : syracuseStep 623583 = 935375) B935375
theorem B623615 : Blo 622298 623615 := bstep (se 1 (by rfl) ⟨467711, by rfl⟩ : syracuseStep 623615 = 935423) B935423
theorem B1705819 : Blo 622298 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B624511 : Blo 622298 624511 := bstep (se 1 (by rfl) ⟨468383, by rfl⟩ : syracuseStep 624511 = 936767) B936767
theorem B624767 : Blo 622298 624767 := bstep (se 1 (by rfl) ⟨468575, by rfl⟩ : syracuseStep 624767 = 937151) B937151
theorem B1050799 : Blo 622298 1050799 := bstep (se 1 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 1050799 = 1576199) B1576199
theorem B2001095 : Blo 622298 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B20187377 : Blo 622298 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B1051177 : Blo 622298 1051177 := bstep (se 2 (by rfl) ⟨394191, by rfl⟩ : syracuseStep 1051177 = 788383) B788383
theorem B625279 : Blo 622298 625279 := bstep (se 1 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 625279 = 937919) B937919
theorem B1182377 : Blo 622298 1182377 := bstep (se 2 (by rfl) ⟨443391, by rfl⟩ : syracuseStep 1182377 = 886783) B886783
theorem B625435 : Blo 622298 625435 := bstep (se 1 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 625435 = 938153) B938153
theorem B625947 : Blo 622298 625947 := bstep (se 1 (by rfl) ⟨469460, by rfl⟩ : syracuseStep 625947 = 938921) B938921
theorem B1051967 : Blo 622298 1051967 := bstep (se 1 (by rfl) ⟨788975, by rfl⟩ : syracuseStep 1051967 = 1577951) B1577951
theorem B1052399 : Blo 622298 1052399 := bstep (se 1 (by rfl) ⟨789299, by rfl⟩ : syracuseStep 1052399 = 1578599) B1578599
theorem B1183585 : Blo 622298 1183585 := bstep (se 2 (by rfl) ⟨443844, by rfl⟩ : syracuseStep 1183585 = 887689) B887689
theorem B1052615 : Blo 622298 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B1052831 : Blo 622298 1052831 := bstep (se 1 (by rfl) ⟨789623, by rfl⟩ : syracuseStep 1052831 = 1579247) B1579247
theorem B2101787 : Blo 622298 2101787 := bstep (se 1 (by rfl) ⟨1576340, by rfl⟩ : syracuseStep 2101787 = 3152681) B3152681
theorem B6100039 : Blo 622298 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B20223053 : Blo 622298 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B2659871 : Blo 622298 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B8001139 : Blo 622298 8001139 := bstep (se 1 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 8001139 = 12001709) B12001709
theorem B32348099 : Blo 622298 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B4725863 : Blo 622298 4725863 := bstep (se 1 (by rfl) ⟨3544397, by rfl⟩ : syracuseStep 4725863 = 7088795) B7088795
theorem B1056091 : Blo 622298 1056091 := bstep (se 1 (by rfl) ⟨792068, by rfl⟩ : syracuseStep 1056091 = 1584137) B1584137
theorem B5348855 : Blo 622298 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B32351471 : Blo 622298 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B1779023 : Blo 622298 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B632287 : Blo 622298 632287 := bstep (se 1 (by rfl) ⟨474215, by rfl⟩ : syracuseStep 632287 = 948431) B948431
theorem B28812995 : Blo 622298 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B4008953 : Blo 622298 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B27340021 : Blo 622298 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B2108969 : Blo 622298 2108969 := bstep (se 2 (by rfl) ⟨790863, by rfl⟩ : syracuseStep 2108969 = 1581727) B1581727
theorem B1781995 : Blo 622298 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B2109779 : Blo 622298 2109779 := bstep (se 1 (by rfl) ⟨1582334, by rfl⟩ : syracuseStep 2109779 = 3164669) B3164669
theorem B9122651 : Blo 622298 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B2111129 : Blo 622298 2111129 := bstep (se 2 (by rfl) ⟨791673, by rfl⟩ : syracuseStep 2111129 = 1583347) B1583347
theorem B65649305 : Blo 622298 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B3554513 : Blo 622298 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B998759 : Blo 622298 998759 := bstep (se 1 (by rfl) ⟨749069, by rfl⟩ : syracuseStep 998759 = 1498139) B1498139
theorem B3161753 : Blo 622298 3161753 := bstep (se 2 (by rfl) ⟨1185657, by rfl⟩ : syracuseStep 3161753 = 2371315) B2371315
theorem B2113343 : Blo 622298 2113343 := bstep (se 1 (by rfl) ⟨1585007, by rfl⟩ : syracuseStep 2113343 = 3170015) B3170015
theorem B933929 : Blo 622298 933929 := bstep (se 2 (by rfl) ⟨350223, by rfl⟩ : syracuseStep 933929 = 700447) B700447
theorem B934631 : Blo 622298 934631 := bstep (se 1 (by rfl) ⟨700973, by rfl⟩ : syracuseStep 934631 = 1401947) B1401947
theorem B102351599 : Blo 622298 102351599 := bstep (se 1 (by rfl) ⟨76763699, by rfl⟩ : syracuseStep 102351599 = 153527399) B153527399
theorem B7586621 : Blo 622298 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B934847 : Blo 622298 934847 := bstep (se 1 (by rfl) ⟨701135, by rfl⟩ : syracuseStep 934847 = 1402271) B1402271
theorem B935399 : Blo 622298 935399 := bstep (se 1 (by rfl) ⟨701549, by rfl⟩ : syracuseStep 935399 = 1403099) B1403099
theorem B16008839 : Blo 622298 16008839 := bstep (se 1 (by rfl) ⟨12006629, by rfl⟩ : syracuseStep 16008839 = 24013259) B24013259
theorem B935771 : Blo 622298 935771 := bstep (se 1 (by rfl) ⟨701828, by rfl⟩ : syracuseStep 935771 = 1403657) B1403657
theorem B936047 : Blo 622298 936047 := bstep (se 1 (by rfl) ⟨702035, by rfl⟩ : syracuseStep 936047 = 1404071) B1404071
theorem B936095 : Blo 622298 936095 := bstep (se 1 (by rfl) ⟨702071, by rfl⟩ : syracuseStep 936095 = 1404143) B1404143
theorem B936431 : Blo 622298 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B6506999 : Blo 622298 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B936731 : Blo 622298 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B3558431 : Blo 622298 3558431 := bstep (se 1 (by rfl) ⟨2668823, by rfl⟩ : syracuseStep 3558431 = 5337647) B5337647
theorem B937115 : Blo 622298 937115 := bstep (se 1 (by rfl) ⟨702836, by rfl⟩ : syracuseStep 937115 = 1405673) B1405673
theorem B937451 : Blo 622298 937451 := bstep (se 1 (by rfl) ⟨703088, by rfl⟩ : syracuseStep 937451 = 1406177) B1406177
theorem B937577 : Blo 622298 937577 := bstep (se 2 (by rfl) ⟨351591, by rfl⟩ : syracuseStep 937577 = 703183) B703183
theorem B3559571 : Blo 622298 3559571 := bstep (se 1 (by rfl) ⟨2669678, by rfl⟩ : syracuseStep 3559571 = 5339357) B5339357
theorem B938855 : Blo 622298 938855 := bstep (se 1 (by rfl) ⟨704141, by rfl⟩ : syracuseStep 938855 = 1408283) B1408283
theorem B938987 : Blo 622298 938987 := bstep (se 1 (by rfl) ⟨704240, by rfl⟩ : syracuseStep 938987 = 1408481) B1408481
theorem B709663 : Blo 622298 709663 := bstep (se 1 (by rfl) ⟨532247, by rfl⟩ : syracuseStep 709663 = 1064495) B1064495
theorem B939335 : Blo 622298 939335 := bstep (se 1 (by rfl) ⟨704501, by rfl⟩ : syracuseStep 939335 = 1409003) B1409003
theorem B17946521 : Blo 622298 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B3168719 : Blo 622298 3168719 := bstep (se 1 (by rfl) ⟨2376539, by rfl⟩ : syracuseStep 3168719 = 4753079) B4753079
theorem B8019593 : Blo 622298 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B3006271 : Blo 622298 3006271 := bstep (se 1 (by rfl) ⟨2254703, by rfl⟩ : syracuseStep 3006271 = 4509407) B4509407
theorem B2286407 : Blo 622298 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B36498023 : Blo 622298 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B1796843 : Blo 622298 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B1404287 : Blo 622298 1404287 := bstep (se 1 (by rfl) ⟨1053215, by rfl⟩ : syracuseStep 1404287 = 2106431) B2106431
theorem B1404395 : Blo 622298 1404395 := bstep (se 1 (by rfl) ⟨1053296, by rfl⟩ : syracuseStep 1404395 = 2106593) B2106593
theorem B1601051 : Blo 622298 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B4747247 : Blo 622298 4747247 := bstep (se 1 (by rfl) ⟨3560435, by rfl⟩ : syracuseStep 4747247 = 7120871) B7120871
theorem B5075297 : Blo 622298 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B7598731 : Blo 622298 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B1995455 : Blo 622298 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B1406159 : Blo 622298 1406159 := bstep (se 1 (by rfl) ⟨1054619, by rfl⟩ : syracuseStep 1406159 = 2109239) B2109239
theorem B17987345 : Blo 622298 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B1406843 : Blo 622298 1406843 := bstep (se 1 (by rfl) ⟨1055132, by rfl⟩ : syracuseStep 1406843 = 2110265) B2110265
theorem B15169427 : Blo 622298 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B3996317 : Blo 622298 3996317 := bstep (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) B1498619
theorem B13531859 : Blo 622298 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B1407707 : Blo 622298 1407707 := bstep (se 1 (by rfl) ⟨1055780, by rfl⟩ : syracuseStep 1407707 = 2111561) B2111561
theorem B1407743 : Blo 622298 1407743 := bstep (se 1 (by rfl) ⟨1055807, by rfl⟩ : syracuseStep 1407743 = 2111615) B2111615
theorem B1408553 : Blo 622298 1408553 := bstep (se 2 (by rfl) ⟨528207, by rfl⟩ : syracuseStep 1408553 = 1056415) B1056415
theorem B622331 : Blo 622298 622331 := bstep (se 1 (by rfl) ⟨466748, by rfl⟩ : syracuseStep 622331 = 933497) B933497
theorem B622619 : Blo 622298 622619 := bstep (se 1 (by rfl) ⟨466964, by rfl⟩ : syracuseStep 622619 = 933929) B933929
theorem B623087 : Blo 622298 623087 := bstep (se 1 (by rfl) ⟨467315, by rfl⟩ : syracuseStep 623087 = 934631) B934631
theorem B623231 : Blo 622298 623231 := bstep (se 1 (by rfl) ⟨467423, by rfl⟩ : syracuseStep 623231 = 934847) B934847
theorem B623599 : Blo 622298 623599 := bstep (se 1 (by rfl) ⟨467699, by rfl⟩ : syracuseStep 623599 = 935399) B935399
theorem B623847 : Blo 622298 623847 := bstep (se 1 (by rfl) ⟨467885, by rfl⟩ : syracuseStep 623847 = 935771) B935771
theorem B624031 : Blo 622298 624031 := bstep (se 1 (by rfl) ⟨468023, by rfl⟩ : syracuseStep 624031 = 936047) B936047
theorem B624063 : Blo 622298 624063 := bstep (se 1 (by rfl) ⟨468047, by rfl⟩ : syracuseStep 624063 = 936095) B936095
theorem B624287 : Blo 622298 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B624487 : Blo 622298 624487 := bstep (se 1 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 624487 = 936731) B936731
theorem B624743 : Blo 622298 624743 := bstep (se 1 (by rfl) ⟨468557, by rfl⟩ : syracuseStep 624743 = 937115) B937115
theorem B624967 : Blo 622298 624967 := bstep (se 1 (by rfl) ⟨468725, by rfl⟩ : syracuseStep 624967 = 937451) B937451
theorem B625051 : Blo 622298 625051 := bstep (se 1 (by rfl) ⟨468788, by rfl⟩ : syracuseStep 625051 = 937577) B937577
theorem B625903 : Blo 622298 625903 := bstep (se 1 (by rfl) ⟨469427, by rfl⟩ : syracuseStep 625903 = 938855) B938855
theorem B625991 : Blo 622298 625991 := bstep (se 1 (by rfl) ⟨469493, by rfl⟩ : syracuseStep 625991 = 938987) B938987
theorem B626223 : Blo 622298 626223 := bstep (se 1 (by rfl) ⟨469667, by rfl⟩ : syracuseStep 626223 = 939335) B939335
theorem B1773247 : Blo 622298 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B11964347 : Blo 622298 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B3150575 : Blo 622298 3150575 := bstep (se 1 (by rfl) ⟨2362931, by rfl⟩ : syracuseStep 3150575 = 4725863) B4725863
theorem B5346395 : Blo 622298 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B1578113 : Blo 622298 1578113 := bstep (se 2 (by rfl) ⟨591792, by rfl⟩ : syracuseStep 1578113 = 1183585) B1183585
theorem B21567647 : Blo 622298 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B10131641 : Blo 622298 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B1186015 : Blo 622298 1186015 := bstep (se 1 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 1186015 = 1779023) B1779023
theorem B19208663 : Blo 622298 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B8133385 : Blo 622298 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B3153005 : Blo 622298 3153005 := bstep (se 3 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 3153005 = 1182377) B1182377
theorem B4791581 : Blo 622298 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B3383531 : Blo 622298 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B4269469 : Blo 622298 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B2664211 : Blo 622298 2664211 := bstep (se 1 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 2664211 = 3996317) B3996317
theorem B9021239 : Blo 622298 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B2369675 : Blo 622298 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B665839 : Blo 622298 665839 := bstep (se 1 (by rfl) ⟨499379, by rfl⟩ : syracuseStep 665839 = 998759) B998759
theorem B4008361 : Blo 622298 4008361 := bstep (se 2 (by rfl) ⟨1503135, by rfl⟩ : syracuseStep 4008361 = 3006271) B3006271
theorem B2107835 : Blo 622298 2107835 := bstep (se 1 (by rfl) ⟨1580876, by rfl⟩ : syracuseStep 2107835 = 3161753) B3161753
theorem B68234399 : Blo 622298 68234399 := bstep (se 1 (by rfl) ⟨51175799, by rfl⟩ : syracuseStep 68234399 = 102351599) B102351599
theorem B5057747 : Blo 622298 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B4337999 : Blo 622298 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B5321213 : Blo 622298 5321213 := bstep (se 3 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 5321213 = 1995455) B1995455
theorem B2372287 : Blo 622298 2372287 := bstep (se 1 (by rfl) ⟨1779215, by rfl⟩ : syracuseStep 2372287 = 3558431) B3558431
theorem B701311 : Blo 622298 701311 := bstep (se 1 (by rfl) ⟨525983, by rfl⟩ : syracuseStep 701311 = 1051967) B1051967
theorem B2274425 : Blo 622298 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B701599 : Blo 622298 701599 := bstep (se 1 (by rfl) ⟨526199, by rfl⟩ : syracuseStep 701599 = 1052399) B1052399
theorem B701743 : Blo 622298 701743 := bstep (se 1 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 701743 = 1052615) B1052615
theorem B2373047 : Blo 622298 2373047 := bstep (se 1 (by rfl) ⟨1779785, by rfl⟩ : syracuseStep 2373047 = 3559571) B3559571
theorem B701887 : Blo 622298 701887 := bstep (se 1 (by rfl) ⟨526415, by rfl⟩ : syracuseStep 701887 = 1052831) B1052831
theorem B13482035 : Blo 622298 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B2112479 : Blo 622298 2112479 := bstep (se 1 (by rfl) ⟨1584359, by rfl⟩ : syracuseStep 2112479 = 3168719) B3168719
theorem B36453361 : Blo 622298 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B86261597 : Blo 622298 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B2375993 : Blo 622298 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B1524271 : Blo 622298 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B24332015 : Blo 622298 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B2672635 : Blo 622298 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B10668185 : Blo 622298 10668185 := bstep (se 2 (by rfl) ⟨4000569, by rfl⟩ : syracuseStep 10668185 = 8001139) B8001139
theorem B936191 : Blo 622298 936191 := bstep (se 1 (by rfl) ⟨702143, by rfl⟩ : syracuseStep 936191 = 1404287) B1404287
theorem B936263 : Blo 622298 936263 := bstep (se 1 (by rfl) ⟨702197, by rfl⟩ : syracuseStep 936263 = 1404395) B1404395
theorem B3164831 : Blo 622298 3164831 := bstep (se 1 (by rfl) ⟨2373623, by rfl⟩ : syracuseStep 3164831 = 4747247) B4747247
theorem B6081767 : Blo 622298 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B937439 : Blo 622298 937439 := bstep (se 1 (by rfl) ⟨703079, by rfl⟩ : syracuseStep 937439 = 1406159) B1406159
theorem B937895 : Blo 622298 937895 := bstep (se 1 (by rfl) ⟨703421, by rfl⟩ : syracuseStep 937895 = 1406843) B1406843
theorem B10112951 : Blo 622298 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B43766203 : Blo 622298 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B938471 : Blo 622298 938471 := bstep (se 1 (by rfl) ⟨703853, by rfl⟩ : syracuseStep 938471 = 1407707) B1407707
theorem B938495 : Blo 622298 938495 := bstep (se 1 (by rfl) ⟨703871, by rfl⟩ : syracuseStep 938495 = 1407743) B1407743
theorem B939035 : Blo 622298 939035 := bstep (se 1 (by rfl) ⟨704276, by rfl⟩ : syracuseStep 939035 = 1408553) B1408553
theorem B10672559 : Blo 622298 10672559 := bstep (se 1 (by rfl) ⟨8004419, by rfl⟩ : syracuseStep 10672559 = 16008839) B16008839
theorem B1334063 : Blo 622298 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B13458251 : Blo 622298 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B843049 : Blo 622298 843049 := bstep (se 2 (by rfl) ⟨316143, by rfl⟩ : syracuseStep 843049 = 632287) B632287
theorem B1401065 : Blo 622298 1401065 := bstep (se 2 (by rfl) ⟨525399, by rfl⟩ : syracuseStep 1401065 = 1050799) B1050799
theorem B1401191 : Blo 622298 1401191 := bstep (se 1 (by rfl) ⟨1050893, by rfl⟩ : syracuseStep 1401191 = 2101787) B2101787
theorem B1401569 : Blo 622298 1401569 := bstep (se 2 (by rfl) ⟨525588, by rfl⟩ : syracuseStep 1401569 = 1051177) B1051177
theorem B3565903 : Blo 622298 3565903 := bstep (se 1 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 3565903 = 5348855) B5348855
theorem B946217 : Blo 622298 946217 := bstep (se 2 (by rfl) ⟨354831, by rfl⟩ : syracuseStep 946217 = 709663) B709663
theorem B1405979 : Blo 622298 1405979 := bstep (se 1 (by rfl) ⟨1054484, by rfl⟩ : syracuseStep 1405979 = 2108969) B2108969
theorem B1406519 : Blo 622298 1406519 := bstep (se 1 (by rfl) ⟨1054889, by rfl⟩ : syracuseStep 1406519 = 2109779) B2109779
theorem B1407419 : Blo 622298 1407419 := bstep (se 1 (by rfl) ⟨1055564, by rfl⟩ : syracuseStep 1407419 = 2111129) B2111129
theorem B11991563 : Blo 622298 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B1408121 : Blo 622298 1408121 := bstep (se 2 (by rfl) ⟨528045, by rfl⟩ : syracuseStep 1408121 = 1056091) B1056091
theorem B1408895 : Blo 622298 1408895 := bstep (se 1 (by rfl) ⟨1056671, by rfl⟩ : syracuseStep 1408895 = 2113343) B2113343
theorem B2032361 : Blo 622298 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B7112123 : Blo 622298 7112123 := bstep (se 1 (by rfl) ⟨5334092, by rfl⟩ : syracuseStep 7112123 = 10668185) B10668185
theorem B624127 : Blo 622298 624127 := bstep (se 1 (by rfl) ⟨468095, by rfl⟩ : syracuseStep 624127 = 936191) B936191
theorem B624175 : Blo 622298 624175 := bstep (se 1 (by rfl) ⟨468131, by rfl⟩ : syracuseStep 624175 = 936263) B936263
theorem B624959 : Blo 622298 624959 := bstep (se 1 (by rfl) ⟨468719, by rfl⟩ : syracuseStep 624959 = 937439) B937439
theorem B625263 : Blo 622298 625263 := bstep (se 1 (by rfl) ⟨468947, by rfl⟩ : syracuseStep 625263 = 937895) B937895
theorem B625647 : Blo 622298 625647 := bstep (se 1 (by rfl) ⟨469235, by rfl⟩ : syracuseStep 625647 = 938471) B938471
theorem B625663 : Blo 622298 625663 := bstep (se 1 (by rfl) ⟨469247, by rfl⟩ : syracuseStep 625663 = 938495) B938495
theorem B4754537 : Blo 622298 4754537 := bstep (se 2 (by rfl) ⟨1782951, by rfl⟩ : syracuseStep 4754537 = 3565903) B3565903
theorem B2100383 : Blo 622298 2100383 := bstep (se 1 (by rfl) ⟨1575287, by rfl⟩ : syracuseStep 2100383 = 3150575) B3150575
theorem B5344481 : Blo 622298 5344481 := bstep (se 2 (by rfl) ⟨2004180, by rfl⟩ : syracuseStep 5344481 = 4008361) B4008361
theorem B626023 : Blo 622298 626023 := bstep (se 1 (by rfl) ⟨469517, by rfl⟩ : syracuseStep 626023 = 939035) B939035
theorem B1052075 : Blo 622298 1052075 := bstep (se 1 (by rfl) ⟨789056, by rfl⟩ : syracuseStep 1052075 = 1578113) B1578113
theorem B6754427 : Blo 622298 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B7115039 : Blo 622298 7115039 := bstep (se 1 (by rfl) ⟨5336279, by rfl⟩ : syracuseStep 7115039 = 10672559) B10672559
theorem B889375 : Blo 622298 889375 := bstep (se 1 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 889375 = 1334063) B1334063
theorem B64885373 : Blo 622298 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B2102003 : Blo 622298 2102003 := bstep (se 1 (by rfl) ⟨1576502, by rfl⟩ : syracuseStep 2102003 = 3153005) B3153005
theorem B2364329 : Blo 622298 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B57513725 : Blo 622298 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B1579783 : Blo 622298 1579783 := bstep (se 1 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 1579783 = 2369675) B2369675
theorem B45489599 : Blo 622298 45489599 := bstep (se 1 (by rfl) ⟨34117199, by rfl⟩ : syracuseStep 45489599 = 68234399) B68234399
theorem B630811 : Blo 622298 630811 := bstep (se 1 (by rfl) ⟨473108, by rfl⟩ : syracuseStep 630811 = 946217) B946217
theorem B2891999 : Blo 622298 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B1581353 : Blo 622298 1581353 := bstep (se 2 (by rfl) ⟨593007, by rfl⟩ : syracuseStep 1581353 = 1186015) B1186015
theorem B3547475 : Blo 622298 3547475 := bstep (se 1 (by rfl) ⟨2660606, by rfl⟩ : syracuseStep 3547475 = 5321213) B5321213
theorem B1516283 : Blo 622298 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B1582031 : Blo 622298 1582031 := bstep (se 1 (by rfl) ⟨1186523, by rfl⟩ : syracuseStep 1582031 = 2373047) B2373047
theorem B48604481 : Blo 622298 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B8988023 : Blo 622298 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B1124065 : Blo 622298 1124065 := bstep (se 2 (by rfl) ⟨421524, by rfl⟩ : syracuseStep 1124065 = 843049) B843049
theorem B1583995 : Blo 622298 1583995 := bstep (se 1 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 1583995 = 2375993) B2375993
theorem B3551141 : Blo 622298 3551141 := bstep (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) B665839
theorem B2109887 : Blo 622298 2109887 := bstep (se 1 (by rfl) ⟨1582415, by rfl⟩ : syracuseStep 2109887 = 3164831) B3164831
theorem B3552281 : Blo 622298 3552281 := bstep (se 2 (by rfl) ⟨1332105, by rfl⟩ : syracuseStep 3552281 = 2664211) B2664211
theorem B7976231 : Blo 622298 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B3194387 : Blo 622298 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B934043 : Blo 622298 934043 := bstep (se 1 (by rfl) ⟨700532, by rfl⟩ : syracuseStep 934043 = 1401065) B1401065
theorem B934127 : Blo 622298 934127 := bstep (se 1 (by rfl) ⟨700595, by rfl⟩ : syracuseStep 934127 = 1401191) B1401191
theorem B934379 : Blo 622298 934379 := bstep (se 1 (by rfl) ⟨700784, by rfl⟩ : syracuseStep 934379 = 1401569) B1401569
theorem B3163049 : Blo 622298 3163049 := bstep (se 2 (by rfl) ⟨1186143, by rfl⟩ : syracuseStep 3163049 = 2372287) B2372287
theorem B935081 : Blo 622298 935081 := bstep (se 2 (by rfl) ⟨350655, by rfl⟩ : syracuseStep 935081 = 701311) B701311
theorem B6014159 : Blo 622298 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B935465 : Blo 622298 935465 := bstep (se 2 (by rfl) ⟨350799, by rfl⟩ : syracuseStep 935465 = 701599) B701599
theorem B935657 : Blo 622298 935657 := bstep (se 2 (by rfl) ⟨350871, by rfl⟩ : syracuseStep 935657 = 701743) B701743
theorem B935849 : Blo 622298 935849 := bstep (se 2 (by rfl) ⟨350943, by rfl⟩ : syracuseStep 935849 = 701887) B701887
theorem B937319 : Blo 622298 937319 := bstep (se 1 (by rfl) ⟨702989, by rfl⟩ : syracuseStep 937319 = 1405979) B1405979
theorem B937679 : Blo 622298 937679 := bstep (se 1 (by rfl) ⟨703259, by rfl⟩ : syracuseStep 937679 = 1406519) B1406519
theorem B938279 : Blo 622298 938279 := bstep (se 1 (by rfl) ⟨703709, by rfl⟩ : syracuseStep 938279 = 1407419) B1407419
theorem B938747 : Blo 622298 938747 := bstep (se 1 (by rfl) ⟨704060, by rfl⟩ : syracuseStep 938747 = 1408121) B1408121
theorem B939263 : Blo 622298 939263 := bstep (se 1 (by rfl) ⟨704447, by rfl⟩ : syracuseStep 939263 = 1408895) B1408895
theorem B5692625 : Blo 622298 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B4054511 : Blo 622298 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B6741967 : Blo 622298 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B3563513 : Blo 622298 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B3564263 : Blo 622298 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B12805775 : Blo 622298 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B8972167 : Blo 622298 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B2255687 : Blo 622298 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B58354937 : Blo 622298 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B1405223 : Blo 622298 1405223 := bstep (se 1 (by rfl) ⟨1053917, by rfl⟩ : syracuseStep 1405223 = 2107835) B2107835
theorem B3371831 : Blo 622298 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B10844513 : Blo 622298 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B7994375 : Blo 622298 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B1408319 : Blo 622298 1408319 := bstep (se 1 (by rfl) ⟨1056239, by rfl⟩ : syracuseStep 1408319 = 2112479) B2112479
theorem B57507731 : Blo 622298 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B622695 : Blo 622298 622695 := bstep (se 1 (by rfl) ⟨467021, by rfl⟩ : syracuseStep 622695 = 934043) B934043
theorem B622751 : Blo 622298 622751 := bstep (se 1 (by rfl) ⟨467063, by rfl⟩ : syracuseStep 622751 = 934127) B934127
theorem B622919 : Blo 622298 622919 := bstep (se 1 (by rfl) ⟨467189, by rfl⟩ : syracuseStep 622919 = 934379) B934379
theorem B623387 : Blo 622298 623387 := bstep (se 1 (by rfl) ⟨467540, by rfl⟩ : syracuseStep 623387 = 935081) B935081
theorem B623643 : Blo 622298 623643 := bstep (se 1 (by rfl) ⟨467732, by rfl⟩ : syracuseStep 623643 = 935465) B935465
theorem B623771 : Blo 622298 623771 := bstep (se 1 (by rfl) ⟨467828, by rfl⟩ : syracuseStep 623771 = 935657) B935657
theorem B623899 : Blo 622298 623899 := bstep (se 1 (by rfl) ⟨467924, by rfl⟩ : syracuseStep 623899 = 935849) B935849
theorem B624879 : Blo 622298 624879 := bstep (se 1 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 624879 = 937319) B937319
theorem B625119 : Blo 622298 625119 := bstep (se 1 (by rfl) ⟨468839, by rfl⟩ : syracuseStep 625119 = 937679) B937679
theorem B11962889 : Blo 622298 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B625519 : Blo 622298 625519 := bstep (se 1 (by rfl) ⟨469139, by rfl⟩ : syracuseStep 625519 = 938279) B938279
theorem B43256915 : Blo 622298 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B625831 : Blo 622298 625831 := bstep (se 1 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 625831 = 938747) B938747
theorem B1576219 : Blo 622298 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B626175 : Blo 622298 626175 := bstep (se 1 (by rfl) ⟨469631, by rfl⟩ : syracuseStep 626175 = 939263) B939263
theorem B38342483 : Blo 622298 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B1054235 : Blo 622298 1054235 := bstep (se 1 (by rfl) ⟨790676, by rfl⟩ : syracuseStep 1054235 = 1581353) B1581353
theorem B2364983 : Blo 622298 2364983 := bstep (se 1 (by rfl) ⟨1773737, by rfl⟩ : syracuseStep 2364983 = 3547475) B3547475
theorem B1054687 : Blo 622298 1054687 := bstep (se 1 (by rfl) ⟨791015, by rfl⟩ : syracuseStep 1054687 = 1582031) B1582031
theorem B1185833 : Blo 622298 1185833 := bstep (se 2 (by rfl) ⟨444687, by rfl⟩ : syracuseStep 1185833 = 889375) B889375
theorem B38903291 : Blo 622298 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B2367427 : Blo 622298 2367427 := bstep (se 1 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 2367427 = 3551141) B3551141
theorem B2368187 : Blo 622298 2368187 := bstep (se 1 (by rfl) ⟨1776140, by rfl⟩ : syracuseStep 2368187 = 3552281) B3552281
theorem B5317487 : Blo 622298 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B2106377 : Blo 622298 2106377 := bstep (se 2 (by rfl) ⟨789891, by rfl⟩ : syracuseStep 2106377 = 1579783) B1579783
theorem B8989289 : Blo 622298 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B1354907 : Blo 622298 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B2108699 : Blo 622298 2108699 := bstep (se 1 (by rfl) ⟨1581524, by rfl⟩ : syracuseStep 2108699 = 3163049) B3163049
theorem B4009439 : Blo 622298 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B701383 : Blo 622298 701383 := bstep (se 1 (by rfl) ⟨526037, by rfl⟩ : syracuseStep 701383 = 1052075) B1052075
theorem B4502951 : Blo 622298 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B2111993 : Blo 622298 2111993 := bstep (se 2 (by rfl) ⟨791997, by rfl⟩ : syracuseStep 2111993 = 1583995) B1583995
theorem B30326399 : Blo 622298 30326399 := bstep (se 1 (by rfl) ⟨22744799, by rfl⟩ : syracuseStep 30326399 = 45489599) B45489599
theorem B2703007 : Blo 622298 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B2375675 : Blo 622298 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B2376175 : Blo 622298 2376175 := bstep (se 1 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 2376175 = 3564263) B3564263
theorem B8537183 : Blo 622298 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B936815 : Blo 622298 936815 := bstep (se 1 (by rfl) ⟨702611, by rfl⟩ : syracuseStep 936815 = 1405223) B1405223
theorem B2247887 : Blo 622298 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B7229675 : Blo 622298 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B5329583 : Blo 622298 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B938879 : Blo 622298 938879 := bstep (se 1 (by rfl) ⟨704159, by rfl⟩ : syracuseStep 938879 = 1408319) B1408319
theorem B3364325 : Blo 622298 3364325 := bstep (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) B630811
theorem B4741415 : Blo 622298 4741415 := bstep (se 1 (by rfl) ⟨3556061, by rfl⟩ : syracuseStep 4741415 = 7112123) B7112123
theorem B3169691 : Blo 622298 3169691 := bstep (se 1 (by rfl) ⟨2377268, by rfl⟩ : syracuseStep 3169691 = 4754537) B4754537
theorem B1400255 : Blo 622298 1400255 := bstep (se 1 (by rfl) ⟨1050191, by rfl⟩ : syracuseStep 1400255 = 2100383) B2100383
theorem B3562987 : Blo 622298 3562987 := bstep (se 1 (by rfl) ⟨2672240, by rfl⟩ : syracuseStep 3562987 = 5344481) B5344481
theorem B1498753 : Blo 622298 1498753 := bstep (se 2 (by rfl) ⟨562032, by rfl⟩ : syracuseStep 1498753 = 1124065) B1124065
theorem B4743359 : Blo 622298 4743359 := bstep (se 1 (by rfl) ⟨3557519, by rfl⟩ : syracuseStep 4743359 = 7115039) B7115039
theorem B1401335 : Blo 622298 1401335 := bstep (se 1 (by rfl) ⟨1051001, by rfl⟩ : syracuseStep 1401335 = 2102003) B2102003
theorem B3795083 : Blo 622298 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B1927999 : Blo 622298 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B1010855 : Blo 622298 1010855 := bstep (se 1 (by rfl) ⟨758141, by rfl⟩ : syracuseStep 1010855 = 1516283) B1516283
theorem B32402987 : Blo 622298 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B5992015 : Blo 622298 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B1503791 : Blo 622298 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B1406591 : Blo 622298 1406591 := bstep (se 1 (by rfl) ⟨1054943, by rfl⟩ : syracuseStep 1406591 = 2109887) B2109887
theorem B2129591 : Blo 622298 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B38338487 : Blo 622298 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B624543 : Blo 622298 624543 := bstep (se 1 (by rfl) ⟨468407, by rfl⟩ : syracuseStep 624543 = 936815) B936815
theorem B28837943 : Blo 622298 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B25561655 : Blo 622298 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B4819783 : Blo 622298 4819783 := bstep (se 1 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 4819783 = 7229675) B7229675
theorem B625919 : Blo 622298 625919 := bstep (se 1 (by rfl) ⟨469439, by rfl⟩ : syracuseStep 625919 = 938879) B938879
theorem B1576655 : Blo 622298 1576655 := bstep (se 1 (by rfl) ⟨1182491, by rfl⟩ : syracuseStep 1576655 = 2364983) B2364983
theorem B790555 : Blo 622298 790555 := bstep (se 1 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 790555 = 1185833) B1185833
theorem B2101625 : Blo 622298 2101625 := bstep (se 2 (by rfl) ⟨788109, by rfl⟩ : syracuseStep 2101625 = 1576219) B1576219
theorem B1578791 : Blo 622298 1578791 := bstep (se 1 (by rfl) ⟨1184093, by rfl⟩ : syracuseStep 1578791 = 2368187) B2368187
theorem B3544991 : Blo 622298 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B2530055 : Blo 622298 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B21601991 : Blo 622298 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B3613085 : Blo 622298 3613085 := bstep (se 3 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 3613085 = 1354907) B1354907
theorem B5678909 : Blo 622298 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B3156569 : Blo 622298 3156569 := bstep (se 2 (by rfl) ⟨1183713, by rfl⟩ : syracuseStep 3156569 = 2367427) B2367427
theorem B1583783 : Blo 622298 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B7975259 : Blo 622298 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B3553055 : Blo 622298 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B2242883 : Blo 622298 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B702823 : Blo 622298 702823 := bstep (se 1 (by rfl) ⟨527117, by rfl⟩ : syracuseStep 702823 = 1054235) B1054235
theorem B2570665 : Blo 622298 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B3160943 : Blo 622298 3160943 := bstep (se 1 (by rfl) ⟨2370707, by rfl⟩ : syracuseStep 3160943 = 4741415) B4741415
theorem B2113127 : Blo 622298 2113127 := bstep (se 1 (by rfl) ⟨1584845, by rfl⟩ : syracuseStep 2113127 = 3169691) B3169691
theorem B933503 : Blo 622298 933503 := bstep (se 1 (by rfl) ⟨700127, by rfl⟩ : syracuseStep 933503 = 1400255) B1400255
theorem B25935527 : Blo 622298 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B3162239 : Blo 622298 3162239 := bstep (se 1 (by rfl) ⟨2371679, by rfl⟩ : syracuseStep 3162239 = 4743359) B4743359
theorem B934223 : Blo 622298 934223 := bstep (se 1 (by rfl) ⟨700667, by rfl⟩ : syracuseStep 934223 = 1401335) B1401335
theorem B935177 : Blo 622298 935177 := bstep (se 2 (by rfl) ⟨350691, by rfl⟩ : syracuseStep 935177 = 701383) B701383
theorem B673903 : Blo 622298 673903 := bstep (se 1 (by rfl) ⟨505427, by rfl⟩ : syracuseStep 673903 = 1010855) B1010855
theorem B2672959 : Blo 622298 2672959 := bstep (se 1 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 2672959 = 4009439) B4009439
theorem B1002527 : Blo 622298 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B3001967 : Blo 622298 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B937727 : Blo 622298 937727 := bstep (se 1 (by rfl) ⟨703295, by rfl⟩ : syracuseStep 937727 = 1406591) B1406591
theorem B3168233 : Blo 622298 3168233 := bstep (se 2 (by rfl) ⟨1188087, by rfl⟩ : syracuseStep 3168233 = 2376175) B2376175
theorem B5691455 : Blo 622298 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B1498591 : Blo 622298 1498591 := bstep (se 1 (by rfl) ⟨1123943, by rfl⟩ : syracuseStep 1498591 = 2247887) B2247887
theorem B7989353 : Blo 622298 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B1404251 : Blo 622298 1404251 := bstep (se 1 (by rfl) ⟨1053188, by rfl⟩ : syracuseStep 1404251 = 2106377) B2106377
theorem B5992859 : Blo 622298 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B1405799 : Blo 622298 1405799 := bstep (se 1 (by rfl) ⟨1054349, by rfl⟩ : syracuseStep 1405799 = 2108699) B2108699
theorem B1406249 : Blo 622298 1406249 := bstep (se 2 (by rfl) ⟨527343, by rfl⟩ : syracuseStep 1406249 = 1054687) B1054687
theorem B7993349 : Blo 622298 7993349 := bstep (se 4 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 7993349 = 1498753) B1498753
theorem B1407995 : Blo 622298 1407995 := bstep (se 1 (by rfl) ⟨1055996, by rfl⟩ : syracuseStep 1407995 = 2111993) B2111993
theorem B4750649 : Blo 622298 4750649 := bstep (se 2 (by rfl) ⟨1781493, by rfl⟩ : syracuseStep 4750649 = 3562987) B3562987
theorem B3604009 : Blo 622298 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B20217599 : Blo 622298 20217599 := bstep (se 1 (by rfl) ⟨15163199, by rfl⟩ : syracuseStep 20217599 = 30326399) B30326399
theorem B25558991 : Blo 622298 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B622815 : Blo 622298 622815 := bstep (se 1 (by rfl) ⟨467111, by rfl⟩ : syracuseStep 622815 = 934223) B934223
theorem B623451 : Blo 622298 623451 := bstep (se 1 (by rfl) ⟨467588, by rfl⟩ : syracuseStep 623451 = 935177) B935177
theorem B17041103 : Blo 622298 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B2001311 : Blo 622298 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B1051103 : Blo 622298 1051103 := bstep (se 1 (by rfl) ⟨788327, by rfl⟩ : syracuseStep 1051103 = 1576655) B1576655
theorem B625151 : Blo 622298 625151 := bstep (se 1 (by rfl) ⟨468863, by rfl⟩ : syracuseStep 625151 = 937727) B937727
theorem B6426377 : Blo 622298 6426377 := bstep (se 2 (by rfl) ⟨2409891, by rfl⟩ : syracuseStep 6426377 = 4819783) B4819783
theorem B1052527 : Blo 622298 1052527 := bstep (se 1 (by rfl) ⟨789395, by rfl⟩ : syracuseStep 1052527 = 1578791) B1578791
theorem B2363327 : Blo 622298 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B1054073 : Blo 622298 1054073 := bstep (se 2 (by rfl) ⟨395277, by rfl⟩ : syracuseStep 1054073 = 790555) B790555
theorem B2104379 : Blo 622298 2104379 := bstep (se 1 (by rfl) ⟨1578284, by rfl⟩ : syracuseStep 2104379 = 3156569) B3156569
theorem B1055855 : Blo 622298 1055855 := bstep (se 1 (by rfl) ⟨791891, by rfl⟩ : syracuseStep 1055855 = 1583783) B1583783
theorem B5316839 : Blo 622298 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B2368703 : Blo 622298 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B2107295 : Blo 622298 2107295 := bstep (se 1 (by rfl) ⟨1580471, by rfl⟩ : syracuseStep 2107295 = 3160943) B3160943
theorem B13478399 : Blo 622298 13478399 := bstep (se 1 (by rfl) ⟨10108799, by rfl⟩ : syracuseStep 13478399 = 20217599) B20217599
theorem B2108159 : Blo 622298 2108159 := bstep (se 1 (by rfl) ⟨1581119, by rfl⟩ : syracuseStep 2108159 = 3162239) B3162239
theorem B668351 : Blo 622298 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B898537 : Blo 622298 898537 := bstep (se 2 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 898537 = 673903) B673903
theorem B2112155 : Blo 622298 2112155 := bstep (se 1 (by rfl) ⟨1584116, by rfl⟩ : syracuseStep 2112155 = 3168233) B3168233
theorem B14401327 : Blo 622298 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B2408723 : Blo 622298 2408723 := bstep (se 1 (by rfl) ⟨1806542, by rfl⟩ : syracuseStep 2408723 = 3613085) B3613085
theorem B3785939 : Blo 622298 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B5326235 : Blo 622298 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B936167 : Blo 622298 936167 := bstep (se 1 (by rfl) ⟨702125, by rfl⟩ : syracuseStep 936167 = 1404251) B1404251
theorem B937097 : Blo 622298 937097 := bstep (se 2 (by rfl) ⟨351411, by rfl⟩ : syracuseStep 937097 = 702823) B702823
theorem B3427553 : Blo 622298 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B937199 : Blo 622298 937199 := bstep (se 1 (by rfl) ⟨702899, by rfl⟩ : syracuseStep 937199 = 1405799) B1405799
theorem B937499 : Blo 622298 937499 := bstep (se 1 (by rfl) ⟨703124, by rfl⟩ : syracuseStep 937499 = 1406249) B1406249
theorem B5328899 : Blo 622298 5328899 := bstep (se 1 (by rfl) ⟨3996674, by rfl⟩ : syracuseStep 5328899 = 7993349) B7993349
theorem B1495255 : Blo 622298 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B938663 : Blo 622298 938663 := bstep (se 1 (by rfl) ⟨703997, by rfl⟩ : syracuseStep 938663 = 1407995) B1407995
theorem B4805345 : Blo 622298 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B3167099 : Blo 622298 3167099 := bstep (se 1 (by rfl) ⟨2375324, by rfl⟩ : syracuseStep 3167099 = 4750649) B4750649
theorem B17290351 : Blo 622298 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B19225295 : Blo 622298 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B1401083 : Blo 622298 1401083 := bstep (se 1 (by rfl) ⟨1050812, by rfl⟩ : syracuseStep 1401083 = 2101625) B2101625
theorem B3563945 : Blo 622298 3563945 := bstep (se 2 (by rfl) ⟨1336479, by rfl⟩ : syracuseStep 3563945 = 2672959) B2672959
theorem B3794303 : Blo 622298 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B6746813 : Blo 622298 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B3995239 : Blo 622298 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B1998121 : Blo 622298 1998121 := bstep (se 2 (by rfl) ⟨749295, by rfl⟩ : syracuseStep 1998121 = 1498591) B1498591
theorem B1408751 : Blo 622298 1408751 := bstep (se 1 (by rfl) ⟨1056563, by rfl⟩ : syracuseStep 1408751 = 2113127) B2113127
theorem B622335 : Blo 622298 622335 := bstep (se 1 (by rfl) ⟨466751, by rfl⟩ : syracuseStep 622335 = 933503) B933503
theorem B17039327 : Blo 622298 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B1605815 : Blo 622298 1605815 := bstep (se 1 (by rfl) ⟨1204361, by rfl⟩ : syracuseStep 1605815 = 2408723) B2408723
theorem B2523959 : Blo 622298 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B624111 : Blo 622298 624111 := bstep (se 1 (by rfl) ⟨468083, by rfl⟩ : syracuseStep 624111 = 936167) B936167
theorem B624731 : Blo 622298 624731 := bstep (se 1 (by rfl) ⟨468548, by rfl⟩ : syracuseStep 624731 = 937097) B937097
theorem B624799 : Blo 622298 624799 := bstep (se 1 (by rfl) ⟨468599, by rfl⟩ : syracuseStep 624799 = 937199) B937199
theorem B624999 : Blo 622298 624999 := bstep (se 1 (by rfl) ⟨468749, by rfl⟩ : syracuseStep 624999 = 937499) B937499
theorem B1575551 : Blo 622298 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B625775 : Blo 622298 625775 := bstep (se 1 (by rfl) ⟨469331, by rfl⟩ : syracuseStep 625775 = 938663) B938663
theorem B12816863 : Blo 622298 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B3544559 : Blo 622298 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B92215205 : Blo 622298 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B1579135 : Blo 622298 1579135 := bstep (se 1 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 1579135 = 2368703) B2368703
theorem B8985599 : Blo 622298 8985599 := bstep (se 1 (by rfl) ⟨6739199, by rfl⟩ : syracuseStep 8985599 = 13478399) B13478399
theorem B4497875 : Blo 622298 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B2664161 : Blo 622298 2664161 := bstep (se 2 (by rfl) ⟨999060, by rfl⟩ : syracuseStep 2664161 = 1998121) B1998121
theorem B3550823 : Blo 622298 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B700735 : Blo 622298 700735 := bstep (se 1 (by rfl) ⟨525551, by rfl⟩ : syracuseStep 700735 = 1051103) B1051103
theorem B1782269 : Blo 622298 1782269 := bstep (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) B668351
theorem B3552599 : Blo 622298 3552599 := bstep (se 1 (by rfl) ⟨2664449, by rfl⟩ : syracuseStep 3552599 = 5328899) B5328899
theorem B2111399 : Blo 622298 2111399 := bstep (se 1 (by rfl) ⟨1583549, by rfl⟩ : syracuseStep 2111399 = 3167099) B3167099
theorem B702715 : Blo 622298 702715 := bstep (se 1 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 702715 = 1054073) B1054073
theorem B703903 : Blo 622298 703903 := bstep (se 1 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 703903 = 1055855) B1055855
theorem B934055 : Blo 622298 934055 := bstep (se 1 (by rfl) ⟨700541, by rfl⟩ : syracuseStep 934055 = 1401083) B1401083
theorem B2375963 : Blo 622298 2375963 := bstep (se 1 (by rfl) ⟨1781972, by rfl⟩ : syracuseStep 2375963 = 3563945) B3563945
theorem B1198049 : Blo 622298 1198049 := bstep (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) B898537
theorem B5326985 : Blo 622298 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B181752821 : Blo 622298 181752821 := bstep (se 5 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 181752821 = 17039327) B17039327
theorem B939167 : Blo 622298 939167 := bstep (se 1 (by rfl) ⟨704375, by rfl⟩ : syracuseStep 939167 = 1408751) B1408751
theorem B11360735 : Blo 622298 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B1334207 : Blo 622298 1334207 := bstep (se 1 (by rfl) ⟨1000655, by rfl⟩ : syracuseStep 1334207 = 2001311) B2001311
theorem B4284251 : Blo 622298 4284251 := bstep (se 1 (by rfl) ⟨3213188, by rfl⟩ : syracuseStep 4284251 = 6426377) B6426377
theorem B3203563 : Blo 622298 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B10118141 : Blo 622298 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B1402919 : Blo 622298 1402919 := bstep (se 1 (by rfl) ⟨1052189, by rfl⟩ : syracuseStep 1402919 = 2104379) B2104379
theorem B1403369 : Blo 622298 1403369 := bstep (se 2 (by rfl) ⟨526263, by rfl⟩ : syracuseStep 1403369 = 1052527) B1052527
theorem B1993673 : Blo 622298 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B1404863 : Blo 622298 1404863 := bstep (se 1 (by rfl) ⟨1053647, by rfl⟩ : syracuseStep 1404863 = 2107295) B2107295
theorem B1405439 : Blo 622298 1405439 := bstep (se 1 (by rfl) ⟨1054079, by rfl⟩ : syracuseStep 1405439 = 2108159) B2108159
theorem B9140141 : Blo 622298 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B1408103 : Blo 622298 1408103 := bstep (se 1 (by rfl) ⟨1056077, by rfl⟩ : syracuseStep 1408103 = 2112155) B2112155
theorem B19201769 : Blo 622298 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B622703 : Blo 622298 622703 := bstep (se 1 (by rfl) ⟨467027, by rfl⟩ : syracuseStep 622703 = 934055) B934055
theorem B1050367 : Blo 622298 1050367 := bstep (se 1 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 1050367 = 1575551) B1575551
theorem B626111 : Blo 622298 626111 := bstep (se 1 (by rfl) ⟨469583, by rfl⟩ : syracuseStep 626111 = 939167) B939167
theorem B2363039 : Blo 622298 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B61476803 : Blo 622298 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B7573823 : Blo 622298 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B889471 : Blo 622298 889471 := bstep (se 1 (by rfl) ⟨667103, by rfl⟩ : syracuseStep 889471 = 1334207) B1334207
theorem B2856167 : Blo 622298 2856167 := bstep (se 1 (by rfl) ⟨2142125, by rfl⟩ : syracuseStep 2856167 = 4284251) B4284251
theorem B1776107 : Blo 622298 1776107 := bstep (se 1 (by rfl) ⟨1332080, by rfl⟩ : syracuseStep 1776107 = 2664161) B2664161
theorem B2367215 : Blo 622298 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B5316461 : Blo 622298 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B2105513 : Blo 622298 2105513 := bstep (se 2 (by rfl) ⟨789567, by rfl⟩ : syracuseStep 2105513 = 1579135) B1579135
theorem B1188179 : Blo 622298 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B2368399 : Blo 622298 2368399 := bstep (se 1 (by rfl) ⟨1776299, by rfl⟩ : syracuseStep 2368399 = 3552599) B3552599
theorem B1583975 : Blo 622298 1583975 := bstep (se 1 (by rfl) ⟨1187981, by rfl⟩ : syracuseStep 1583975 = 2375963) B2375963
theorem B1682639 : Blo 622298 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B4271417 : Blo 622298 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B3551323 : Blo 622298 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B3194797 : Blo 622298 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B2998583 : Blo 622298 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B934313 : Blo 622298 934313 := bstep (se 2 (by rfl) ⟨350367, by rfl⟩ : syracuseStep 934313 = 700735) B700735
theorem B935279 : Blo 622298 935279 := bstep (se 1 (by rfl) ⟨701459, by rfl⟩ : syracuseStep 935279 = 1402919) B1402919
theorem B935579 : Blo 622298 935579 := bstep (se 1 (by rfl) ⟨701684, by rfl⟩ : syracuseStep 935579 = 1403369) B1403369
theorem B936575 : Blo 622298 936575 := bstep (se 1 (by rfl) ⟨702431, by rfl⟩ : syracuseStep 936575 = 1404863) B1404863
theorem B936953 : Blo 622298 936953 := bstep (se 2 (by rfl) ⟨351357, by rfl⟩ : syracuseStep 936953 = 702715) B702715
theorem B936959 : Blo 622298 936959 := bstep (se 1 (by rfl) ⟨702719, by rfl⟩ : syracuseStep 936959 = 1405439) B1405439
theorem B938537 : Blo 622298 938537 := bstep (se 2 (by rfl) ⟨351951, by rfl⟩ : syracuseStep 938537 = 703903) B703903
theorem B938735 : Blo 622298 938735 := bstep (se 1 (by rfl) ⟨704051, by rfl⟩ : syracuseStep 938735 = 1408103) B1408103
theorem B12801179 : Blo 622298 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B1070543 : Blo 622298 1070543 := bstep (se 1 (by rfl) ⟨802907, by rfl⟩ : syracuseStep 1070543 = 1605815) B1605815
theorem B8544575 : Blo 622298 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B121168547 : Blo 622298 121168547 := bstep (se 1 (by rfl) ⟨90876410, by rfl⟩ : syracuseStep 121168547 = 181752821) B181752821
theorem B5990399 : Blo 622298 5990399 := bstep (se 1 (by rfl) ⟨4492799, by rfl⟩ : syracuseStep 5990399 = 8985599) B8985599
theorem B6745427 : Blo 622298 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B1407599 : Blo 622298 1407599 := bstep (se 1 (by rfl) ⟨1055699, by rfl⟩ : syracuseStep 1407599 = 2111399) B2111399
theorem B6093427 : Blo 622298 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B1999055 : Blo 622298 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B622875 : Blo 622298 622875 := bstep (se 1 (by rfl) ⟨467156, by rfl⟩ : syracuseStep 622875 = 934313) B934313
theorem B623519 : Blo 622298 623519 := bstep (se 1 (by rfl) ⟨467639, by rfl⟩ : syracuseStep 623519 = 935279) B935279
theorem B623719 : Blo 622298 623719 := bstep (se 1 (by rfl) ⟨467789, by rfl⟩ : syracuseStep 623719 = 935579) B935579
theorem B624383 : Blo 622298 624383 := bstep (se 1 (by rfl) ⟨468287, by rfl⟩ : syracuseStep 624383 = 936575) B936575
theorem B624635 : Blo 622298 624635 := bstep (se 1 (by rfl) ⟨468476, by rfl⟩ : syracuseStep 624635 = 936953) B936953
theorem B624639 : Blo 622298 624639 := bstep (se 1 (by rfl) ⟨468479, by rfl⟩ : syracuseStep 624639 = 936959) B936959
theorem B1575359 : Blo 622298 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B5049215 : Blo 622298 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B625691 : Blo 622298 625691 := bstep (se 1 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 625691 = 938537) B938537
theorem B625823 : Blo 622298 625823 := bstep (se 1 (by rfl) ⟨469367, by rfl⟩ : syracuseStep 625823 = 938735) B938735
theorem B1904111 : Blo 622298 1904111 := bstep (se 1 (by rfl) ⟨1428083, by rfl⟩ : syracuseStep 1904111 = 2856167) B2856167
theorem B1184071 : Blo 622298 1184071 := bstep (se 1 (by rfl) ⟨888053, by rfl⟩ : syracuseStep 1184071 = 1776107) B1776107
theorem B1578143 : Blo 622298 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B3544307 : Blo 622298 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B792119 : Blo 622298 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B80779031 : Blo 622298 80779031 := bstep (se 1 (by rfl) ⟨60584273, by rfl⟩ : syracuseStep 80779031 = 121168547) B121168547
theorem B1055983 : Blo 622298 1055983 := bstep (se 1 (by rfl) ⟨791987, by rfl⟩ : syracuseStep 1055983 = 1583975) B1583975
theorem B1121759 : Blo 622298 1121759 := bstep (se 1 (by rfl) ⟨841319, by rfl⟩ : syracuseStep 1121759 = 1682639) B1682639
theorem B4496951 : Blo 622298 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B22785533 : Blo 622298 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B3157865 : Blo 622298 3157865 := bstep (se 2 (by rfl) ⟨1184199, by rfl⟩ : syracuseStep 3157865 = 2368399) B2368399
theorem B8534119 : Blo 622298 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B4735097 : Blo 622298 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B938399 : Blo 622298 938399 := bstep (se 1 (by rfl) ⟨703799, by rfl⟩ : syracuseStep 938399 = 1407599) B1407599
theorem B1400489 : Blo 622298 1400489 := bstep (se 2 (by rfl) ⟨525183, by rfl⟩ : syracuseStep 1400489 = 1050367) B1050367
theorem B40984535 : Blo 622298 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B4743845 : Blo 622298 4743845 := bstep (se 4 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 4743845 = 889471) B889471
theorem B713695 : Blo 622298 713695 := bstep (se 1 (by rfl) ⟨535271, by rfl⟩ : syracuseStep 713695 = 1070543) B1070543
theorem B1403675 : Blo 622298 1403675 := bstep (se 1 (by rfl) ⟨1052756, by rfl⟩ : syracuseStep 1403675 = 2105513) B2105513
theorem B3993599 : Blo 622298 3993599 := bstep (se 1 (by rfl) ⟨2995199, by rfl⟩ : syracuseStep 3993599 = 5990399) B5990399
theorem B2847611 : Blo 622298 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B8124569 : Blo 622298 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B4259729 : Blo 622298 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B951593 : Blo 622298 951593 := bstep (se 2 (by rfl) ⟨356847, by rfl⟩ : syracuseStep 951593 = 713695) B713695
theorem B1050239 : Blo 622298 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B625599 : Blo 622298 625599 := bstep (se 1 (by rfl) ⟨469199, by rfl⟩ : syracuseStep 625599 = 938399) B938399
theorem B1052095 : Blo 622298 1052095 := bstep (se 1 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 1052095 = 1578143) B1578143
theorem B2362871 : Blo 622298 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B1578761 : Blo 622298 1578761 := bstep (se 2 (by rfl) ⟨592035, by rfl⟩ : syracuseStep 1578761 = 1184071) B1184071
theorem B2105243 : Blo 622298 2105243 := bstep (se 1 (by rfl) ⟨1578932, by rfl⟩ : syracuseStep 2105243 = 3157865) B3157865
theorem B2662399 : Blo 622298 2662399 := bstep (se 1 (by rfl) ⟨1996799, by rfl⟩ : syracuseStep 2662399 = 3993599) B3993599
theorem B11378825 : Blo 622298 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B5416379 : Blo 622298 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B3156731 : Blo 622298 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B53852687 : Blo 622298 53852687 := bstep (se 1 (by rfl) ⟨40389515, by rfl⟩ : syracuseStep 53852687 = 80779031) B80779031
theorem B2112317 : Blo 622298 2112317 := bstep (se 3 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 2112317 = 792119) B792119
theorem B2997967 : Blo 622298 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B933659 : Blo 622298 933659 := bstep (se 1 (by rfl) ⟨700244, by rfl⟩ : syracuseStep 933659 = 1400489) B1400489
theorem B3162563 : Blo 622298 3162563 := bstep (se 1 (by rfl) ⟨2371922, by rfl⟩ : syracuseStep 3162563 = 4743845) B4743845
theorem B935783 : Blo 622298 935783 := bstep (se 1 (by rfl) ⟨701837, by rfl⟩ : syracuseStep 935783 = 1403675) B1403675
theorem B15190355 : Blo 622298 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B11359277 : Blo 622298 11359277 := bstep (se 3 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 11359277 = 4259729) B4259729
theorem B1332703 : Blo 622298 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B3366143 : Blo 622298 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B1269407 : Blo 622298 1269407 := bstep (se 1 (by rfl) ⟨952055, by rfl⟩ : syracuseStep 1269407 = 1904111) B1904111
theorem B747839 : Blo 622298 747839 := bstep (se 1 (by rfl) ⟨560879, by rfl⟩ : syracuseStep 747839 = 1121759) B1121759
theorem B27323023 : Blo 622298 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B1898407 : Blo 622298 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B1407977 : Blo 622298 1407977 := bstep (se 2 (by rfl) ⟨527991, by rfl⟩ : syracuseStep 1407977 = 1055983) B1055983
theorem B623855 : Blo 622298 623855 := bstep (se 1 (by rfl) ⟨467891, by rfl⟩ : syracuseStep 623855 = 935783) B935783
theorem B1575247 : Blo 622298 1575247 := bstep (se 1 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 1575247 = 2362871) B2362871
theorem B7572851 : Blo 622298 7572851 := bstep (se 1 (by rfl) ⟨5679638, by rfl⟩ : syracuseStep 7572851 = 11359277) B11359277
theorem B1052507 : Blo 622298 1052507 := bstep (se 1 (by rfl) ⟨789380, by rfl⟩ : syracuseStep 1052507 = 1578761) B1578761
theorem B40507613 : Blo 622298 40507613 := bstep (se 3 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 40507613 = 15190355) B15190355
theorem B3610919 : Blo 622298 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B2104487 : Blo 622298 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B2531209 : Blo 622298 2531209 := bstep (se 2 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 2531209 = 1898407) B1898407
theorem B3549865 : Blo 622298 3549865 := bstep (se 2 (by rfl) ⟨1331199, by rfl⟩ : syracuseStep 3549865 = 2662399) B2662399
theorem B2108375 : Blo 622298 2108375 := bstep (se 1 (by rfl) ⟨1581281, by rfl⟩ : syracuseStep 2108375 = 3162563) B3162563
theorem B700159 : Blo 622298 700159 := bstep (se 1 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 700159 = 1050239) B1050239
theorem B2537581 : Blo 622298 2537581 := bstep (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) B951593
theorem B2244095 : Blo 622298 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B7585883 : Blo 622298 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B35901791 : Blo 622298 35901791 := bstep (se 1 (by rfl) ⟨26926343, by rfl⟩ : syracuseStep 35901791 = 53852687) B53852687
theorem B938651 : Blo 622298 938651 := bstep (se 1 (by rfl) ⟨703988, by rfl⟩ : syracuseStep 938651 = 1407977) B1407977
theorem B36430697 : Blo 622298 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B1402793 : Blo 622298 1402793 := bstep (se 2 (by rfl) ⟨526047, by rfl⟩ : syracuseStep 1402793 = 1052095) B1052095
theorem B846271 : Blo 622298 846271 := bstep (se 1 (by rfl) ⟨634703, by rfl⟩ : syracuseStep 846271 = 1269407) B1269407
theorem B1403495 : Blo 622298 1403495 := bstep (se 1 (by rfl) ⟨1052621, by rfl⟩ : syracuseStep 1403495 = 2105243) B2105243
theorem B1994237 : Blo 622298 1994237 := bstep (se 3 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 1994237 = 747839) B747839
theorem B7107749 : Blo 622298 7107749 := bstep (se 4 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 7107749 = 1332703) B1332703
theorem B1408211 : Blo 622298 1408211 := bstep (se 1 (by rfl) ⟨1056158, by rfl⟩ : syracuseStep 1408211 = 2112317) B2112317
theorem B3997289 : Blo 622298 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B622439 : Blo 622298 622439 := bstep (se 1 (by rfl) ⟨466829, by rfl⟩ : syracuseStep 622439 = 933659) B933659
theorem B5048567 : Blo 622298 5048567 := bstep (se 1 (by rfl) ⟨3786425, by rfl⟩ : syracuseStep 5048567 = 7572851) B7572851
theorem B625767 : Blo 622298 625767 := bstep (se 1 (by rfl) ⟨469325, by rfl⟩ : syracuseStep 625767 = 938651) B938651
theorem B2100329 : Blo 622298 2100329 := bstep (se 2 (by rfl) ⟨787623, by rfl⟩ : syracuseStep 2100329 = 1575247) B1575247
theorem B27005075 : Blo 622298 27005075 := bstep (se 1 (by rfl) ⟨20253806, by rfl⟩ : syracuseStep 27005075 = 40507613) B40507613
theorem B24287131 : Blo 622298 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B3383441 : Blo 622298 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B10659437 : Blo 622298 10659437 := bstep (se 3 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 10659437 = 3997289) B3997289
theorem B5057255 : Blo 622298 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B701671 : Blo 622298 701671 := bstep (se 1 (by rfl) ⟨526253, by rfl⟩ : syracuseStep 701671 = 1052507) B1052507
theorem B23934527 : Blo 622298 23934527 := bstep (se 1 (by rfl) ⟨17950895, by rfl⟩ : syracuseStep 23934527 = 35901791) B35901791
theorem B4733153 : Blo 622298 4733153 := bstep (se 2 (by rfl) ⟨1774932, by rfl⟩ : syracuseStep 4733153 = 3549865) B3549865
theorem B2407279 : Blo 622298 2407279 := bstep (se 1 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 2407279 = 3610919) B3610919
theorem B933545 : Blo 622298 933545 := bstep (se 2 (by rfl) ⟨350079, by rfl⟩ : syracuseStep 933545 = 700159) B700159
theorem B935195 : Blo 622298 935195 := bstep (se 1 (by rfl) ⟨701396, by rfl⟩ : syracuseStep 935195 = 1402793) B1402793
theorem B935663 : Blo 622298 935663 := bstep (se 1 (by rfl) ⟨701747, by rfl⟩ : syracuseStep 935663 = 1403495) B1403495
theorem B1329491 : Blo 622298 1329491 := bstep (se 1 (by rfl) ⟨997118, by rfl⟩ : syracuseStep 1329491 = 1994237) B1994237
theorem B4738499 : Blo 622298 4738499 := bstep (se 1 (by rfl) ⟨3553874, by rfl⟩ : syracuseStep 4738499 = 7107749) B7107749
theorem B938807 : Blo 622298 938807 := bstep (se 1 (by rfl) ⟨704105, by rfl⟩ : syracuseStep 938807 = 1408211) B1408211
theorem B1496063 : Blo 622298 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B4513445 : Blo 622298 4513445 := bstep (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) B846271
theorem B1402991 : Blo 622298 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B1405583 : Blo 622298 1405583 := bstep (se 1 (by rfl) ⟨1054187, by rfl⟩ : syracuseStep 1405583 = 2108375) B2108375
theorem B3374945 : Blo 622298 3374945 := bstep (se 2 (by rfl) ⟨1265604, by rfl⟩ : syracuseStep 3374945 = 2531209) B2531209
theorem B623463 : Blo 622298 623463 := bstep (se 1 (by rfl) ⟨467597, by rfl⟩ : syracuseStep 623463 = 935195) B935195
theorem B623775 : Blo 622298 623775 := bstep (se 1 (by rfl) ⟨467831, by rfl⟩ : syracuseStep 623775 = 935663) B935663
theorem B625871 : Blo 622298 625871 := bstep (se 1 (by rfl) ⟨469403, by rfl⟩ : syracuseStep 625871 = 938807) B938807
theorem B3545309 : Blo 622298 3545309 := bstep (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) B1329491
theorem B32382841 : Blo 622298 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B3155435 : Blo 622298 3155435 := bstep (se 1 (by rfl) ⟨2366576, by rfl⟩ : syracuseStep 3155435 = 4733153) B4733153
theorem B3158999 : Blo 622298 3158999 := bstep (se 1 (by rfl) ⟨2369249, by rfl⟩ : syracuseStep 3158999 = 4738499) B4738499
theorem B18003383 : Blo 622298 18003383 := bstep (se 1 (by rfl) ⟨13502537, by rfl⟩ : syracuseStep 18003383 = 27005075) B27005075
theorem B997375 : Blo 622298 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B935327 : Blo 622298 935327 := bstep (se 1 (by rfl) ⟨701495, by rfl⟩ : syracuseStep 935327 = 1402991) B1402991
theorem B935561 : Blo 622298 935561 := bstep (se 2 (by rfl) ⟨350835, by rfl⟩ : syracuseStep 935561 = 701671) B701671
theorem B13486013 : Blo 622298 13486013 := bstep (se 3 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 13486013 = 5057255) B5057255
theorem B937055 : Blo 622298 937055 := bstep (se 1 (by rfl) ⟨702791, by rfl⟩ : syracuseStep 937055 = 1405583) B1405583
theorem B2249963 : Blo 622298 2249963 := bstep (se 1 (by rfl) ⟨1687472, by rfl⟩ : syracuseStep 2249963 = 3374945) B3374945
theorem B3365711 : Blo 622298 3365711 := bstep (se 1 (by rfl) ⟨2524283, by rfl⟩ : syracuseStep 3365711 = 5048567) B5048567
theorem B1400219 : Blo 622298 1400219 := bstep (se 1 (by rfl) ⟨1050164, by rfl⟩ : syracuseStep 1400219 = 2100329) B2100329
theorem B3008963 : Blo 622298 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B2255627 : Blo 622298 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B7106291 : Blo 622298 7106291 := bstep (se 1 (by rfl) ⟨5329718, by rfl⟩ : syracuseStep 7106291 = 10659437) B10659437
theorem B15956351 : Blo 622298 15956351 := bstep (se 1 (by rfl) ⟨11967263, by rfl⟩ : syracuseStep 15956351 = 23934527) B23934527
theorem B3209705 : Blo 622298 3209705 := bstep (se 2 (by rfl) ⟨1203639, by rfl⟩ : syracuseStep 3209705 = 2407279) B2407279
theorem B622363 : Blo 622298 622363 := bstep (se 1 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 622363 = 933545) B933545
theorem B623551 : Blo 622298 623551 := bstep (se 1 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 623551 = 935327) B935327
theorem B623707 : Blo 622298 623707 := bstep (se 1 (by rfl) ⟨467780, by rfl⟩ : syracuseStep 623707 = 935561) B935561
theorem B624703 : Blo 622298 624703 := bstep (se 1 (by rfl) ⟨468527, by rfl⟩ : syracuseStep 624703 = 937055) B937055
theorem B2363539 : Blo 622298 2363539 := bstep (se 1 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 2363539 = 3545309) B3545309
theorem B2103623 : Blo 622298 2103623 := bstep (se 1 (by rfl) ⟨1577717, by rfl⟩ : syracuseStep 2103623 = 3155435) B3155435
theorem B2005975 : Blo 622298 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B2105999 : Blo 622298 2105999 := bstep (se 1 (by rfl) ⟨1579499, by rfl⟩ : syracuseStep 2105999 = 3158999) B3158999
theorem B12002255 : Blo 622298 12002255 := bstep (se 1 (by rfl) ⟨9001691, by rfl⟩ : syracuseStep 12002255 = 18003383) B18003383
theorem B2139803 : Blo 622298 2139803 := bstep (se 1 (by rfl) ⟨1604852, by rfl⟩ : syracuseStep 2139803 = 3209705) B3209705
theorem B8990675 : Blo 622298 8990675 := bstep (se 1 (by rfl) ⟨6743006, by rfl⟩ : syracuseStep 8990675 = 13486013) B13486013
theorem B2243807 : Blo 622298 2243807 := bstep (se 1 (by rfl) ⟨1682855, by rfl⟩ : syracuseStep 2243807 = 3365711) B3365711
theorem B933479 : Blo 622298 933479 := bstep (se 1 (by rfl) ⟨700109, by rfl⟩ : syracuseStep 933479 = 1400219) B1400219
theorem B4737527 : Blo 622298 4737527 := bstep (se 1 (by rfl) ⟨3553145, by rfl⟩ : syracuseStep 4737527 = 7106291) B7106291
theorem B1329833 : Blo 622298 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B10637567 : Blo 622298 10637567 := bstep (se 1 (by rfl) ⟨7978175, by rfl⟩ : syracuseStep 10637567 = 15956351) B15956351
theorem B43177121 : Blo 622298 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B1499975 : Blo 622298 1499975 := bstep (se 1 (by rfl) ⟨1124981, by rfl⟩ : syracuseStep 1499975 = 2249963) B2249963
theorem B1503751 : Blo 622298 1503751 := bstep (se 1 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 1503751 = 2255627) B2255627
theorem B886555 : Blo 622298 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B3151385 : Blo 622298 3151385 := bstep (se 2 (by rfl) ⟨1181769, by rfl⟩ : syracuseStep 3151385 = 2363539) B2363539
theorem B8001503 : Blo 622298 8001503 := bstep (se 1 (by rfl) ⟨6001127, by rfl⟩ : syracuseStep 8001503 = 12002255) B12002255
theorem B2005001 : Blo 622298 2005001 := bstep (se 2 (by rfl) ⟨751875, by rfl⟩ : syracuseStep 2005001 = 1503751) B1503751
theorem B3158351 : Blo 622298 3158351 := bstep (se 1 (by rfl) ⟨2368763, by rfl⟩ : syracuseStep 3158351 = 4737527) B4737527
theorem B7091711 : Blo 622298 7091711 := bstep (se 1 (by rfl) ⟨5318783, by rfl⟩ : syracuseStep 7091711 = 10637567) B10637567
theorem B28784747 : Blo 622298 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B999983 : Blo 622298 999983 := bstep (se 1 (by rfl) ⟨749987, by rfl⟩ : syracuseStep 999983 = 1499975) B1499975
theorem B1426535 : Blo 622298 1426535 := bstep (se 1 (by rfl) ⟨1069901, by rfl⟩ : syracuseStep 1426535 = 2139803) B2139803
theorem B2674633 : Blo 622298 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B1495871 : Blo 622298 1495871 := bstep (se 1 (by rfl) ⟨1121903, by rfl⟩ : syracuseStep 1495871 = 2243807) B2243807
theorem B1402415 : Blo 622298 1402415 := bstep (se 1 (by rfl) ⟨1051811, by rfl⟩ : syracuseStep 1402415 = 2103623) B2103623
theorem B1403999 : Blo 622298 1403999 := bstep (se 1 (by rfl) ⟨1052999, by rfl⟩ : syracuseStep 1403999 = 2105999) B2105999
theorem B5993783 : Blo 622298 5993783 := bstep (se 1 (by rfl) ⟨4495337, by rfl⟩ : syracuseStep 5993783 = 8990675) B8990675
theorem B622319 : Blo 622298 622319 := bstep (se 1 (by rfl) ⟨466739, by rfl⟩ : syracuseStep 622319 = 933479) B933479
theorem B951023 : Blo 622298 951023 := bstep (se 1 (by rfl) ⟨713267, by rfl⟩ : syracuseStep 951023 = 1426535) B1426535
theorem B2100923 : Blo 622298 2100923 := bstep (se 1 (by rfl) ⟨1575692, by rfl⟩ : syracuseStep 2100923 = 3151385) B3151385
theorem B2105567 : Blo 622298 2105567 := bstep (se 1 (by rfl) ⟨1579175, by rfl⟩ : syracuseStep 2105567 = 3158351) B3158351
theorem B4727807 : Blo 622298 4727807 := bstep (se 1 (by rfl) ⟨3545855, by rfl⟩ : syracuseStep 4727807 = 7091711) B7091711
theorem B4728293 : Blo 622298 4728293 := bstep (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) B886555
theorem B2666621 : Blo 622298 2666621 := bstep (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) B999983
theorem B997247 : Blo 622298 997247 := bstep (se 1 (by rfl) ⟨747935, by rfl⟩ : syracuseStep 997247 = 1495871) B1495871
theorem B76759325 : Blo 622298 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B934943 : Blo 622298 934943 := bstep (se 1 (by rfl) ⟨701207, by rfl⟩ : syracuseStep 934943 = 1402415) B1402415
theorem B935999 : Blo 622298 935999 := bstep (se 1 (by rfl) ⟨701999, by rfl⟩ : syracuseStep 935999 = 1403999) B1403999
theorem B5334335 : Blo 622298 5334335 := bstep (se 1 (by rfl) ⟨4000751, by rfl⟩ : syracuseStep 5334335 = 8001503) B8001503
theorem B1336667 : Blo 622298 1336667 := bstep (se 1 (by rfl) ⟨1002500, by rfl⟩ : syracuseStep 1336667 = 2005001) B2005001
theorem B3566177 : Blo 622298 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B3995855 : Blo 622298 3995855 := bstep (se 1 (by rfl) ⟨2996891, by rfl⟩ : syracuseStep 3995855 = 5993783) B5993783
theorem B623295 : Blo 622298 623295 := bstep (se 1 (by rfl) ⟨467471, by rfl⟩ : syracuseStep 623295 = 934943) B934943
theorem B623999 : Blo 622298 623999 := bstep (se 1 (by rfl) ⟨467999, by rfl⟩ : syracuseStep 623999 = 935999) B935999
theorem B3151871 : Blo 622298 3151871 := bstep (se 1 (by rfl) ⟨2363903, by rfl⟩ : syracuseStep 3151871 = 4727807) B4727807
theorem B3152195 : Blo 622298 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B1777747 : Blo 622298 1777747 := bstep (se 1 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 1777747 = 2666621) B2666621
theorem B664831 : Blo 622298 664831 := bstep (se 1 (by rfl) ⟨498623, by rfl⟩ : syracuseStep 664831 = 997247) B997247
theorem B2663903 : Blo 622298 2663903 := bstep (se 1 (by rfl) ⟨1997927, by rfl⟩ : syracuseStep 2663903 = 3995855) B3995855
theorem B634015 : Blo 622298 634015 := bstep (se 1 (by rfl) ⟨475511, by rfl⟩ : syracuseStep 634015 = 951023) B951023
theorem B3556223 : Blo 622298 3556223 := bstep (se 1 (by rfl) ⟨2667167, by rfl⟩ : syracuseStep 3556223 = 5334335) B5334335
theorem B2377451 : Blo 622298 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B51172883 : Blo 622298 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B1400615 : Blo 622298 1400615 := bstep (se 1 (by rfl) ⟨1050461, by rfl⟩ : syracuseStep 1400615 = 2100923) B2100923
theorem B3564445 : Blo 622298 3564445 := bstep (se 3 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 3564445 = 1336667) B1336667
theorem B1403711 : Blo 622298 1403711 := bstep (se 1 (by rfl) ⟨1052783, by rfl⟩ : syracuseStep 1403711 = 2105567) B2105567
theorem B4752593 : Blo 622298 4752593 := bstep (se 2 (by rfl) ⟨1782222, by rfl⟩ : syracuseStep 4752593 = 3564445) B3564445
theorem B34115255 : Blo 622298 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B2101247 : Blo 622298 2101247 := bstep (se 1 (by rfl) ⟨1575935, by rfl⟩ : syracuseStep 2101247 = 3151871) B3151871
theorem B2101463 : Blo 622298 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B1775935 : Blo 622298 1775935 := bstep (se 1 (by rfl) ⟨1331951, by rfl⟩ : syracuseStep 1775935 = 2663903) B2663903
theorem B3545765 : Blo 622298 3545765 := bstep (se 4 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 3545765 = 664831) B664831
theorem B2370329 : Blo 622298 2370329 := bstep (se 2 (by rfl) ⟨888873, by rfl⟩ : syracuseStep 2370329 = 1777747) B1777747
theorem B2370815 : Blo 622298 2370815 := bstep (se 1 (by rfl) ⟨1778111, by rfl⟩ : syracuseStep 2370815 = 3556223) B3556223
theorem B1584967 : Blo 622298 1584967 := bstep (se 1 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 1584967 = 2377451) B2377451
theorem B933743 : Blo 622298 933743 := bstep (se 1 (by rfl) ⟨700307, by rfl⟩ : syracuseStep 933743 = 1400615) B1400615
theorem B935807 : Blo 622298 935807 := bstep (se 1 (by rfl) ⟨701855, by rfl⟩ : syracuseStep 935807 = 1403711) B1403711
theorem B845353 : Blo 622298 845353 := bstep (se 2 (by rfl) ⟨317007, by rfl⟩ : syracuseStep 845353 = 634015) B634015
theorem B623871 : Blo 622298 623871 := bstep (se 1 (by rfl) ⟨467903, by rfl⟩ : syracuseStep 623871 = 935807) B935807
theorem B22743503 : Blo 622298 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B2363843 : Blo 622298 2363843 := bstep (se 1 (by rfl) ⟨1772882, by rfl⟩ : syracuseStep 2363843 = 3545765) B3545765
theorem B1580219 : Blo 622298 1580219 := bstep (se 1 (by rfl) ⟨1185164, by rfl⟩ : syracuseStep 1580219 = 2370329) B2370329
theorem B1580543 : Blo 622298 1580543 := bstep (se 1 (by rfl) ⟨1185407, by rfl⟩ : syracuseStep 1580543 = 2370815) B2370815
theorem B2367913 : Blo 622298 2367913 := bstep (se 2 (by rfl) ⟨887967, by rfl⟩ : syracuseStep 2367913 = 1775935) B1775935
theorem B1127137 : Blo 622298 1127137 := bstep (se 2 (by rfl) ⟨422676, by rfl⟩ : syracuseStep 1127137 = 845353) B845353
theorem B2113289 : Blo 622298 2113289 := bstep (se 2 (by rfl) ⟨792483, by rfl⟩ : syracuseStep 2113289 = 1584967) B1584967
theorem B3168395 : Blo 622298 3168395 := bstep (se 1 (by rfl) ⟨2376296, by rfl⟩ : syracuseStep 3168395 = 4752593) B4752593
theorem B1400831 : Blo 622298 1400831 := bstep (se 1 (by rfl) ⟨1050623, by rfl⟩ : syracuseStep 1400831 = 2101247) B2101247
theorem B1400975 : Blo 622298 1400975 := bstep (se 1 (by rfl) ⟨1050731, by rfl⟩ : syracuseStep 1400975 = 2101463) B2101463
theorem B622495 : Blo 622298 622495 := bstep (se 1 (by rfl) ⟨466871, by rfl⟩ : syracuseStep 622495 = 933743) B933743
theorem B1575895 : Blo 622298 1575895 := bstep (se 1 (by rfl) ⟨1181921, by rfl⟩ : syracuseStep 1575895 = 2363843) B2363843
theorem B1053479 : Blo 622298 1053479 := bstep (se 1 (by rfl) ⟨790109, by rfl⟩ : syracuseStep 1053479 = 1580219) B1580219
theorem B1053695 : Blo 622298 1053695 := bstep (se 1 (by rfl) ⟨790271, by rfl⟩ : syracuseStep 1053695 = 1580543) B1580543
theorem B3157217 : Blo 622298 3157217 := bstep (se 2 (by rfl) ⟨1183956, by rfl⟩ : syracuseStep 3157217 = 2367913) B2367913
theorem B2112263 : Blo 622298 2112263 := bstep (se 1 (by rfl) ⟨1584197, by rfl⟩ : syracuseStep 2112263 = 3168395) B3168395
theorem B933887 : Blo 622298 933887 := bstep (se 1 (by rfl) ⟨700415, by rfl⟩ : syracuseStep 933887 = 1400831) B1400831
theorem B933983 : Blo 622298 933983 := bstep (se 1 (by rfl) ⟨700487, by rfl⟩ : syracuseStep 933983 = 1400975) B1400975
theorem B15162335 : Blo 622298 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B1502849 : Blo 622298 1502849 := bstep (se 2 (by rfl) ⟨563568, by rfl⟩ : syracuseStep 1502849 = 1127137) B1127137
theorem B1408859 : Blo 622298 1408859 := bstep (se 1 (by rfl) ⟨1056644, by rfl⟩ : syracuseStep 1408859 = 2113289) B2113289
theorem B622655 : Blo 622298 622655 := bstep (se 1 (by rfl) ⟨466991, by rfl⟩ : syracuseStep 622655 = 933983) B933983
theorem B2101193 : Blo 622298 2101193 := bstep (se 2 (by rfl) ⟨787947, by rfl⟩ : syracuseStep 2101193 = 1575895) B1575895
theorem B2104811 : Blo 622298 2104811 := bstep (se 1 (by rfl) ⟨1578608, by rfl⟩ : syracuseStep 2104811 = 3157217) B3157217
theorem B702319 : Blo 622298 702319 := bstep (se 1 (by rfl) ⟨526739, by rfl⟩ : syracuseStep 702319 = 1053479) B1053479
theorem B702463 : Blo 622298 702463 := bstep (se 1 (by rfl) ⟨526847, by rfl⟩ : syracuseStep 702463 = 1053695) B1053695
theorem B10108223 : Blo 622298 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B1001899 : Blo 622298 1001899 := bstep (se 1 (by rfl) ⟨751424, by rfl⟩ : syracuseStep 1001899 = 1502849) B1502849
theorem B939239 : Blo 622298 939239 := bstep (se 1 (by rfl) ⟨704429, by rfl⟩ : syracuseStep 939239 = 1408859) B1408859
theorem B1408175 : Blo 622298 1408175 := bstep (se 1 (by rfl) ⟨1056131, by rfl⟩ : syracuseStep 1408175 = 2112263) B2112263
theorem B622591 : Blo 622298 622591 := bstep (se 1 (by rfl) ⟨466943, by rfl⟩ : syracuseStep 622591 = 933887) B933887
theorem B626159 : Blo 622298 626159 := bstep (se 1 (by rfl) ⟨469619, by rfl⟩ : syracuseStep 626159 = 939239) B939239
theorem B936425 : Blo 622298 936425 := bstep (se 2 (by rfl) ⟨351159, by rfl⟩ : syracuseStep 936425 = 702319) B702319
theorem B936617 : Blo 622298 936617 := bstep (se 2 (by rfl) ⟨351231, by rfl⟩ : syracuseStep 936617 = 702463) B702463
theorem B938783 : Blo 622298 938783 := bstep (se 1 (by rfl) ⟨704087, by rfl⟩ : syracuseStep 938783 = 1408175) B1408175
theorem B6738815 : Blo 622298 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B1400795 : Blo 622298 1400795 := bstep (se 1 (by rfl) ⟨1050596, by rfl⟩ : syracuseStep 1400795 = 2101193) B2101193
theorem B1335865 : Blo 622298 1335865 := bstep (se 2 (by rfl) ⟨500949, by rfl⟩ : syracuseStep 1335865 = 1001899) B1001899
theorem B1403207 : Blo 622298 1403207 := bstep (se 1 (by rfl) ⟨1052405, by rfl⟩ : syracuseStep 1403207 = 2104811) B2104811
theorem B624283 : Blo 622298 624283 := bstep (se 1 (by rfl) ⟨468212, by rfl⟩ : syracuseStep 624283 = 936425) B936425
theorem B624411 : Blo 622298 624411 := bstep (se 1 (by rfl) ⟨468308, by rfl⟩ : syracuseStep 624411 = 936617) B936617
theorem B625855 : Blo 622298 625855 := bstep (se 1 (by rfl) ⟨469391, by rfl⟩ : syracuseStep 625855 = 938783) B938783
theorem B4492543 : Blo 622298 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B1781153 : Blo 622298 1781153 := bstep (se 2 (by rfl) ⟨667932, by rfl⟩ : syracuseStep 1781153 = 1335865) B1335865
theorem B933863 : Blo 622298 933863 := bstep (se 1 (by rfl) ⟨700397, by rfl⟩ : syracuseStep 933863 = 1400795) B1400795
theorem B935471 : Blo 622298 935471 := bstep (se 1 (by rfl) ⟨701603, by rfl⟩ : syracuseStep 935471 = 1403207) B1403207
theorem B623647 : Blo 622298 623647 := bstep (se 1 (by rfl) ⟨467735, by rfl⟩ : syracuseStep 623647 = 935471) B935471
theorem B1187435 : Blo 622298 1187435 := bstep (se 1 (by rfl) ⟨890576, by rfl⟩ : syracuseStep 1187435 = 1781153) B1781153
theorem B5990057 : Blo 622298 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B622575 : Blo 622298 622575 := bstep (se 1 (by rfl) ⟨466931, by rfl⟩ : syracuseStep 622575 = 933863) B933863
theorem B791623 : Blo 622298 791623 := bstep (se 1 (by rfl) ⟨593717, by rfl⟩ : syracuseStep 791623 = 1187435) B1187435
theorem B3993371 : Blo 622298 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B1055497 : Blo 622298 1055497 := bstep (se 2 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 1055497 = 791623) B791623
theorem B2662247 : Blo 622298 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B1774831 : Blo 622298 1774831 := bstep (se 1 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 1774831 = 2662247) B2662247
theorem B1407329 : Blo 622298 1407329 := bstep (se 2 (by rfl) ⟨527748, by rfl⟩ : syracuseStep 1407329 = 1055497) B1055497
theorem B2366441 : Blo 622298 2366441 := bstep (se 2 (by rfl) ⟨887415, by rfl⟩ : syracuseStep 2366441 = 1774831) B1774831
theorem B938219 : Blo 622298 938219 := bstep (se 1 (by rfl) ⟨703664, by rfl⟩ : syracuseStep 938219 = 1407329) B1407329
theorem B625479 : Blo 622298 625479 := bstep (se 1 (by rfl) ⟨469109, by rfl⟩ : syracuseStep 625479 = 938219) B938219
theorem B1577627 : Blo 622298 1577627 := bstep (se 1 (by rfl) ⟨1183220, by rfl⟩ : syracuseStep 1577627 = 2366441) B2366441
theorem B1051751 : Blo 622298 1051751 := bstep (se 1 (by rfl) ⟨788813, by rfl⟩ : syracuseStep 1051751 = 1577627) B1577627
theorem B701167 : Blo 622298 701167 := bstep (se 1 (by rfl) ⟨525875, by rfl⟩ : syracuseStep 701167 = 1051751) B1051751
theorem B934889 : Blo 622298 934889 := bstep (se 2 (by rfl) ⟨350583, by rfl⟩ : syracuseStep 934889 = 701167) B701167
theorem B623259 : Blo 622298 623259 := bstep (se 1 (by rfl) ⟨467444, by rfl⟩ : syracuseStep 623259 = 934889) B934889

theorem C0 (j : ℕ) (h1 : 155574 ≤ j) (h2 : j ≤ 156273) : Blo 622298 (4 * j + 3) := by
  interval_cases j
  · exact B622299
  · exact B622303
  · exact B622307
  · exact B622311
  · exact B622315
  · exact B622319
  · exact B622323
  · exact B622327
  · exact B622331
  · exact B622335
  · exact B622339
  · exact B622343
  · exact B622347
  · exact B622351
  · exact B622355
  · exact B622359
  · exact B622363
  · exact B622367
  · exact B622371
  · exact B622375
  · exact B622379
  · exact B622383
  · exact B622387
  · exact B622391
  · exact B622395
  · exact B622399
  · exact B622403
  · exact B622407
  · exact B622411
  · exact B622415
  · exact B622419
  · exact B622423
  · exact B622427
  · exact B622431
  · exact B622435
  · exact B622439
  · exact B622443
  · exact B622447
  · exact B622451
  · exact B622455
  · exact B622459
  · exact B622463
  · exact B622467
  · exact B622471
  · exact B622475
  · exact B622479
  · exact B622483
  · exact B622487
  · exact B622491
  · exact B622495
  · exact B622499
  · exact B622503
  · exact B622507
  · exact B622511
  · exact B622515
  · exact B622519
  · exact B622523
  · exact B622527
  · exact B622531
  · exact B622535
  · exact B622539
  · exact B622543
  · exact B622547
  · exact B622551
  · exact B622555
  · exact B622559
  · exact B622563
  · exact B622567
  · exact B622571
  · exact B622575
  · exact B622579
  · exact B622583
  · exact B622587
  · exact B622591
  · exact B622595
  · exact B622599
  · exact B622603
  · exact B622607
  · exact B622611
  · exact B622615
  · exact B622619
  · exact B622623
  · exact B622627
  · exact B622631
  · exact B622635
  · exact B622639
  · exact B622643
  · exact B622647
  · exact B622651
  · exact B622655
  · exact B622659
  · exact B622663
  · exact B622667
  · exact B622671
  · exact B622675
  · exact B622679
  · exact B622683
  · exact B622687
  · exact B622691
  · exact B622695
  · exact B622699
  · exact B622703
  · exact B622707
  · exact B622711
  · exact B622715
  · exact B622719
  · exact B622723
  · exact B622727
  · exact B622731
  · exact B622735
  · exact B622739
  · exact B622743
  · exact B622747
  · exact B622751
  · exact B622755
  · exact B622759
  · exact B622763
  · exact B622767
  · exact B622771
  · exact B622775
  · exact B622779
  · exact B622783
  · exact B622787
  · exact B622791
  · exact B622795
  · exact B622799
  · exact B622803
  · exact B622807
  · exact B622811
  · exact B622815
  · exact B622819
  · exact B622823
  · exact B622827
  · exact B622831
  · exact B622835
  · exact B622839
  · exact B622843
  · exact B622847
  · exact B622851
  · exact B622855
  · exact B622859
  · exact B622863
  · exact B622867
  · exact B622871
  · exact B622875
  · exact B622879
  · exact B622883
  · exact B622887
  · exact B622891
  · exact B622895
  · exact B622899
  · exact B622903
  · exact B622907
  · exact B622911
  · exact B622915
  · exact B622919
  · exact B622923
  · exact B622927
  · exact B622931
  · exact B622935
  · exact B622939
  · exact B622943
  · exact B622947
  · exact B622951
  · exact B622955
  · exact B622959
  · exact B622963
  · exact B622967
  · exact B622971
  · exact B622975
  · exact B622979
  · exact B622983
  · exact B622987
  · exact B622991
  · exact B622995
  · exact B622999
  · exact B623003
  · exact B623007
  · exact B623011
  · exact B623015
  · exact B623019
  · exact B623023
  · exact B623027
  · exact B623031
  · exact B623035
  · exact B623039
  · exact B623043
  · exact B623047
  · exact B623051
  · exact B623055
  · exact B623059
  · exact B623063
  · exact B623067
  · exact B623071
  · exact B623075
  · exact B623079
  · exact B623083
  · exact B623087
  · exact B623091
  · exact B623095
  · exact B623099
  · exact B623103
  · exact B623107
  · exact B623111
  · exact B623115
  · exact B623119
  · exact B623123
  · exact B623127
  · exact B623131
  · exact B623135
  · exact B623139
  · exact B623143
  · exact B623147
  · exact B623151
  · exact B623155
  · exact B623159
  · exact B623163
  · exact B623167
  · exact B623171
  · exact B623175
  · exact B623179
  · exact B623183
  · exact B623187
  · exact B623191
  · exact B623195
  · exact B623199
  · exact B623203
  · exact B623207
  · exact B623211
  · exact B623215
  · exact B623219
  · exact B623223
  · exact B623227
  · exact B623231
  · exact B623235
  · exact B623239
  · exact B623243
  · exact B623247
  · exact B623251
  · exact B623255
  · exact B623259
  · exact B623263
  · exact B623267
  · exact B623271
  · exact B623275
  · exact B623279
  · exact B623283
  · exact B623287
  · exact B623291
  · exact B623295
  · exact B623299
  · exact B623303
  · exact B623307
  · exact B623311
  · exact B623315
  · exact B623319
  · exact B623323
  · exact B623327
  · exact B623331
  · exact B623335
  · exact B623339
  · exact B623343
  · exact B623347
  · exact B623351
  · exact B623355
  · exact B623359
  · exact B623363
  · exact B623367
  · exact B623371
  · exact B623375
  · exact B623379
  · exact B623383
  · exact B623387
  · exact B623391
  · exact B623395
  · exact B623399
  · exact B623403
  · exact B623407
  · exact B623411
  · exact B623415
  · exact B623419
  · exact B623423
  · exact B623427
  · exact B623431
  · exact B623435
  · exact B623439
  · exact B623443
  · exact B623447
  · exact B623451
  · exact B623455
  · exact B623459
  · exact B623463
  · exact B623467
  · exact B623471
  · exact B623475
  · exact B623479
  · exact B623483
  · exact B623487
  · exact B623491
  · exact B623495
  · exact B623499
  · exact B623503
  · exact B623507
  · exact B623511
  · exact B623515
  · exact B623519
  · exact B623523
  · exact B623527
  · exact B623531
  · exact B623535
  · exact B623539
  · exact B623543
  · exact B623547
  · exact B623551
  · exact B623555
  · exact B623559
  · exact B623563
  · exact B623567
  · exact B623571
  · exact B623575
  · exact B623579
  · exact B623583
  · exact B623587
  · exact B623591
  · exact B623595
  · exact B623599
  · exact B623603
  · exact B623607
  · exact B623611
  · exact B623615
  · exact B623619
  · exact B623623
  · exact B623627
  · exact B623631
  · exact B623635
  · exact B623639
  · exact B623643
  · exact B623647
  · exact B623651
  · exact B623655
  · exact B623659
  · exact B623663
  · exact B623667
  · exact B623671
  · exact B623675
  · exact B623679
  · exact B623683
  · exact B623687
  · exact B623691
  · exact B623695
  · exact B623699
  · exact B623703
  · exact B623707
  · exact B623711
  · exact B623715
  · exact B623719
  · exact B623723
  · exact B623727
  · exact B623731
  · exact B623735
  · exact B623739
  · exact B623743
  · exact B623747
  · exact B623751
  · exact B623755
  · exact B623759
  · exact B623763
  · exact B623767
  · exact B623771
  · exact B623775
  · exact B623779
  · exact B623783
  · exact B623787
  · exact B623791
  · exact B623795
  · exact B623799
  · exact B623803
  · exact B623807
  · exact B623811
  · exact B623815
  · exact B623819
  · exact B623823
  · exact B623827
  · exact B623831
  · exact B623835
  · exact B623839
  · exact B623843
  · exact B623847
  · exact B623851
  · exact B623855
  · exact B623859
  · exact B623863
  · exact B623867
  · exact B623871
  · exact B623875
  · exact B623879
  · exact B623883
  · exact B623887
  · exact B623891
  · exact B623895
  · exact B623899
  · exact B623903
  · exact B623907
  · exact B623911
  · exact B623915
  · exact B623919
  · exact B623923
  · exact B623927
  · exact B623931
  · exact B623935
  · exact B623939
  · exact B623943
  · exact B623947
  · exact B623951
  · exact B623955
  · exact B623959
  · exact B623963
  · exact B623967
  · exact B623971
  · exact B623975
  · exact B623979
  · exact B623983
  · exact B623987
  · exact B623991
  · exact B623995
  · exact B623999
  · exact B624003
  · exact B624007
  · exact B624011
  · exact B624015
  · exact B624019
  · exact B624023
  · exact B624027
  · exact B624031
  · exact B624035
  · exact B624039
  · exact B624043
  · exact B624047
  · exact B624051
  · exact B624055
  · exact B624059
  · exact B624063
  · exact B624067
  · exact B624071
  · exact B624075
  · exact B624079
  · exact B624083
  · exact B624087
  · exact B624091
  · exact B624095
  · exact B624099
  · exact B624103
  · exact B624107
  · exact B624111
  · exact B624115
  · exact B624119
  · exact B624123
  · exact B624127
  · exact B624131
  · exact B624135
  · exact B624139
  · exact B624143
  · exact B624147
  · exact B624151
  · exact B624155
  · exact B624159
  · exact B624163
  · exact B624167
  · exact B624171
  · exact B624175
  · exact B624179
  · exact B624183
  · exact B624187
  · exact B624191
  · exact B624195
  · exact B624199
  · exact B624203
  · exact B624207
  · exact B624211
  · exact B624215
  · exact B624219
  · exact B624223
  · exact B624227
  · exact B624231
  · exact B624235
  · exact B624239
  · exact B624243
  · exact B624247
  · exact B624251
  · exact B624255
  · exact B624259
  · exact B624263
  · exact B624267
  · exact B624271
  · exact B624275
  · exact B624279
  · exact B624283
  · exact B624287
  · exact B624291
  · exact B624295
  · exact B624299
  · exact B624303
  · exact B624307
  · exact B624311
  · exact B624315
  · exact B624319
  · exact B624323
  · exact B624327
  · exact B624331
  · exact B624335
  · exact B624339
  · exact B624343
  · exact B624347
  · exact B624351
  · exact B624355
  · exact B624359
  · exact B624363
  · exact B624367
  · exact B624371
  · exact B624375
  · exact B624379
  · exact B624383
  · exact B624387
  · exact B624391
  · exact B624395
  · exact B624399
  · exact B624403
  · exact B624407
  · exact B624411
  · exact B624415
  · exact B624419
  · exact B624423
  · exact B624427
  · exact B624431
  · exact B624435
  · exact B624439
  · exact B624443
  · exact B624447
  · exact B624451
  · exact B624455
  · exact B624459
  · exact B624463
  · exact B624467
  · exact B624471
  · exact B624475
  · exact B624479
  · exact B624483
  · exact B624487
  · exact B624491
  · exact B624495
  · exact B624499
  · exact B624503
  · exact B624507
  · exact B624511
  · exact B624515
  · exact B624519
  · exact B624523
  · exact B624527
  · exact B624531
  · exact B624535
  · exact B624539
  · exact B624543
  · exact B624547
  · exact B624551
  · exact B624555
  · exact B624559
  · exact B624563
  · exact B624567
  · exact B624571
  · exact B624575
  · exact B624579
  · exact B624583
  · exact B624587
  · exact B624591
  · exact B624595
  · exact B624599
  · exact B624603
  · exact B624607
  · exact B624611
  · exact B624615
  · exact B624619
  · exact B624623
  · exact B624627
  · exact B624631
  · exact B624635
  · exact B624639
  · exact B624643
  · exact B624647
  · exact B624651
  · exact B624655
  · exact B624659
  · exact B624663
  · exact B624667
  · exact B624671
  · exact B624675
  · exact B624679
  · exact B624683
  · exact B624687
  · exact B624691
  · exact B624695
  · exact B624699
  · exact B624703
  · exact B624707
  · exact B624711
  · exact B624715
  · exact B624719
  · exact B624723
  · exact B624727
  · exact B624731
  · exact B624735
  · exact B624739
  · exact B624743
  · exact B624747
  · exact B624751
  · exact B624755
  · exact B624759
  · exact B624763
  · exact B624767
  · exact B624771
  · exact B624775
  · exact B624779
  · exact B624783
  · exact B624787
  · exact B624791
  · exact B624795
  · exact B624799
  · exact B624803
  · exact B624807
  · exact B624811
  · exact B624815
  · exact B624819
  · exact B624823
  · exact B624827
  · exact B624831
  · exact B624835
  · exact B624839
  · exact B624843
  · exact B624847
  · exact B624851
  · exact B624855
  · exact B624859
  · exact B624863
  · exact B624867
  · exact B624871
  · exact B624875
  · exact B624879
  · exact B624883
  · exact B624887
  · exact B624891
  · exact B624895
  · exact B624899
  · exact B624903
  · exact B624907
  · exact B624911
  · exact B624915
  · exact B624919
  · exact B624923
  · exact B624927
  · exact B624931
  · exact B624935
  · exact B624939
  · exact B624943
  · exact B624947
  · exact B624951
  · exact B624955
  · exact B624959
  · exact B624963
  · exact B624967
  · exact B624971
  · exact B624975
  · exact B624979
  · exact B624983
  · exact B624987
  · exact B624991
  · exact B624995
  · exact B624999
  · exact B625003
  · exact B625007
  · exact B625011
  · exact B625015
  · exact B625019
  · exact B625023
  · exact B625027
  · exact B625031
  · exact B625035
  · exact B625039
  · exact B625043
  · exact B625047
  · exact B625051
  · exact B625055
  · exact B625059
  · exact B625063
  · exact B625067
  · exact B625071
  · exact B625075
  · exact B625079
  · exact B625083
  · exact B625087
  · exact B625091
  · exact B625095

theorem C1 (j : ℕ) (h1 : 156274 ≤ j) (h2 : j ≤ 156573) : Blo 622298 (4 * j + 3) := by
  interval_cases j
  · exact B625099
  · exact B625103
  · exact B625107
  · exact B625111
  · exact B625115
  · exact B625119
  · exact B625123
  · exact B625127
  · exact B625131
  · exact B625135
  · exact B625139
  · exact B625143
  · exact B625147
  · exact B625151
  · exact B625155
  · exact B625159
  · exact B625163
  · exact B625167
  · exact B625171
  · exact B625175
  · exact B625179
  · exact B625183
  · exact B625187
  · exact B625191
  · exact B625195
  · exact B625199
  · exact B625203
  · exact B625207
  · exact B625211
  · exact B625215
  · exact B625219
  · exact B625223
  · exact B625227
  · exact B625231
  · exact B625235
  · exact B625239
  · exact B625243
  · exact B625247
  · exact B625251
  · exact B625255
  · exact B625259
  · exact B625263
  · exact B625267
  · exact B625271
  · exact B625275
  · exact B625279
  · exact B625283
  · exact B625287
  · exact B625291
  · exact B625295
  · exact B625299
  · exact B625303
  · exact B625307
  · exact B625311
  · exact B625315
  · exact B625319
  · exact B625323
  · exact B625327
  · exact B625331
  · exact B625335
  · exact B625339
  · exact B625343
  · exact B625347
  · exact B625351
  · exact B625355
  · exact B625359
  · exact B625363
  · exact B625367
  · exact B625371
  · exact B625375
  · exact B625379
  · exact B625383
  · exact B625387
  · exact B625391
  · exact B625395
  · exact B625399
  · exact B625403
  · exact B625407
  · exact B625411
  · exact B625415
  · exact B625419
  · exact B625423
  · exact B625427
  · exact B625431
  · exact B625435
  · exact B625439
  · exact B625443
  · exact B625447
  · exact B625451
  · exact B625455
  · exact B625459
  · exact B625463
  · exact B625467
  · exact B625471
  · exact B625475
  · exact B625479
  · exact B625483
  · exact B625487
  · exact B625491
  · exact B625495
  · exact B625499
  · exact B625503
  · exact B625507
  · exact B625511
  · exact B625515
  · exact B625519
  · exact B625523
  · exact B625527
  · exact B625531
  · exact B625535
  · exact B625539
  · exact B625543
  · exact B625547
  · exact B625551
  · exact B625555
  · exact B625559
  · exact B625563
  · exact B625567
  · exact B625571
  · exact B625575
  · exact B625579
  · exact B625583
  · exact B625587
  · exact B625591
  · exact B625595
  · exact B625599
  · exact B625603
  · exact B625607
  · exact B625611
  · exact B625615
  · exact B625619
  · exact B625623
  · exact B625627
  · exact B625631
  · exact B625635
  · exact B625639
  · exact B625643
  · exact B625647
  · exact B625651
  · exact B625655
  · exact B625659
  · exact B625663
  · exact B625667
  · exact B625671
  · exact B625675
  · exact B625679
  · exact B625683
  · exact B625687
  · exact B625691
  · exact B625695
  · exact B625699
  · exact B625703
  · exact B625707
  · exact B625711
  · exact B625715
  · exact B625719
  · exact B625723
  · exact B625727
  · exact B625731
  · exact B625735
  · exact B625739
  · exact B625743
  · exact B625747
  · exact B625751
  · exact B625755
  · exact B625759
  · exact B625763
  · exact B625767
  · exact B625771
  · exact B625775
  · exact B625779
  · exact B625783
  · exact B625787
  · exact B625791
  · exact B625795
  · exact B625799
  · exact B625803
  · exact B625807
  · exact B625811
  · exact B625815
  · exact B625819
  · exact B625823
  · exact B625827
  · exact B625831
  · exact B625835
  · exact B625839
  · exact B625843
  · exact B625847
  · exact B625851
  · exact B625855
  · exact B625859
  · exact B625863
  · exact B625867
  · exact B625871
  · exact B625875
  · exact B625879
  · exact B625883
  · exact B625887
  · exact B625891
  · exact B625895
  · exact B625899
  · exact B625903
  · exact B625907
  · exact B625911
  · exact B625915
  · exact B625919
  · exact B625923
  · exact B625927
  · exact B625931
  · exact B625935
  · exact B625939
  · exact B625943
  · exact B625947
  · exact B625951
  · exact B625955
  · exact B625959
  · exact B625963
  · exact B625967
  · exact B625971
  · exact B625975
  · exact B625979
  · exact B625983
  · exact B625987
  · exact B625991
  · exact B625995
  · exact B625999
  · exact B626003
  · exact B626007
  · exact B626011
  · exact B626015
  · exact B626019
  · exact B626023
  · exact B626027
  · exact B626031
  · exact B626035
  · exact B626039
  · exact B626043
  · exact B626047
  · exact B626051
  · exact B626055
  · exact B626059
  · exact B626063
  · exact B626067
  · exact B626071
  · exact B626075
  · exact B626079
  · exact B626083
  · exact B626087
  · exact B626091
  · exact B626095
  · exact B626099
  · exact B626103
  · exact B626107
  · exact B626111
  · exact B626115
  · exact B626119
  · exact B626123
  · exact B626127
  · exact B626131
  · exact B626135
  · exact B626139
  · exact B626143
  · exact B626147
  · exact B626151
  · exact B626155
  · exact B626159
  · exact B626163
  · exact B626167
  · exact B626171
  · exact B626175
  · exact B626179
  · exact B626183
  · exact B626187
  · exact B626191
  · exact B626195
  · exact B626199
  · exact B626203
  · exact B626207
  · exact B626211
  · exact B626215
  · exact B626219
  · exact B626223
  · exact B626227
  · exact B626231
  · exact B626235
  · exact B626239
  · exact B626243
  · exact B626247
  · exact B626251
  · exact B626255
  · exact B626259
  · exact B626263
  · exact B626267
  · exact B626271
  · exact B626275
  · exact B626279
  · exact B626283
  · exact B626287
  · exact B626291
  · exact B626295

theorem solution (m : ℕ) (hlo : 622298 ≤ m) (hhi : m ≤ 626298) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 155574 ≤ j := by omega
    have hj2 : j ≤ 156573 := by omega
    have hb : Blo 622298 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 156274 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
