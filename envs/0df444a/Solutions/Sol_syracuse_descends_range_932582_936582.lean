-- Prove2me | solution 1 for syracuse_descends_range_932582_936582
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:55.867445+00:00
-- url     : https://prove2.me/submissions/ef5c6e8b-dd0a-4082-802f-2890c23dc1ae

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


theorem B1999021 : Blo 932582 1999021 := bbase (se 3 (by rfl) ⟨374816, by rfl⟩ : syracuseStep 1999021 = 749633) (by norm_num)
theorem B3997957 : Blo 932582 3997957 := bbase (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) (by norm_num)
theorem B3997973 : Blo 932582 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B1212797 : Blo 932582 1212797 := bbase (se 3 (by rfl) ⟨227399, by rfl⟩ : syracuseStep 1212797 = 454799) (by norm_num)
theorem B1999397 : Blo 932582 1999397 := bbase (se 4 (by rfl) ⟨187443, by rfl⟩ : syracuseStep 1999397 = 374887) (by norm_num)
theorem B1049161 : Blo 932582 1049161 := bbase (se 2 (by rfl) ⟨393435, by rfl⟩ : syracuseStep 1049161 = 786871) (by norm_num)
theorem B1049197 : Blo 932582 1049197 := bbase (se 3 (by rfl) ⟨196724, by rfl⟩ : syracuseStep 1049197 = 393449) (by norm_num)
theorem B1049233 : Blo 932582 1049233 := bbase (se 2 (by rfl) ⟨393462, by rfl⟩ : syracuseStep 1049233 = 786925) (by norm_num)
theorem B4489877 : Blo 932582 4489877 := bbase (se 6 (by rfl) ⟨105231, by rfl⟩ : syracuseStep 4489877 = 210463) (by norm_num)
theorem B1049269 : Blo 932582 1049269 := bbase (se 5 (by rfl) ⟨49184, by rfl⟩ : syracuseStep 1049269 = 98369) (by norm_num)
theorem B1049305 : Blo 932582 1049305 := bbase (se 2 (by rfl) ⟨393489, by rfl⟩ : syracuseStep 1049305 = 786979) (by norm_num)
theorem B6390517 : Blo 932582 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B1049341 : Blo 932582 1049341 := bbase (se 3 (by rfl) ⟨196751, by rfl⟩ : syracuseStep 1049341 = 393503) (by norm_num)
theorem B3834629 : Blo 932582 3834629 := bbase (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) (by norm_num)
theorem B1180433 : Blo 932582 1180433 := bbase (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) (by norm_num)
theorem B1049377 : Blo 932582 1049377 := bbase (se 2 (by rfl) ⟨393516, by rfl⟩ : syracuseStep 1049377 = 787033) (by norm_num)
theorem B1049413 : Blo 932582 1049413 := bbase (se 4 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 1049413 = 196765) (by norm_num)
theorem B1180489 : Blo 932582 1180489 := bbase (se 2 (by rfl) ⟨442683, by rfl⟩ : syracuseStep 1180489 = 885367) (by norm_num)
theorem B1049449 : Blo 932582 1049449 := bbase (se 2 (by rfl) ⟨393543, by rfl⟩ : syracuseStep 1049449 = 787087) (by norm_num)
theorem B1049485 : Blo 932582 1049485 := bbase (se 3 (by rfl) ⟨196778, by rfl⟩ : syracuseStep 1049485 = 393557) (by norm_num)
theorem B1573789 : Blo 932582 1573789 := bbase (se 3 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 1573789 = 590171) (by norm_num)
theorem B1180585 : Blo 932582 1180585 := bbase (se 2 (by rfl) ⟨442719, by rfl⟩ : syracuseStep 1180585 = 885439) (by norm_num)
theorem B1049521 : Blo 932582 1049521 := bbase (se 2 (by rfl) ⟨393570, by rfl⟩ : syracuseStep 1049521 = 787141) (by norm_num)
theorem B1049557 : Blo 932582 1049557 := bbase (se 7 (by rfl) ⟨12299, by rfl⟩ : syracuseStep 1049557 = 24599) (by norm_num)
theorem B7111637 : Blo 932582 7111637 := bbase (se 7 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 7111637 = 166679) (by norm_num)
theorem B1573877 : Blo 932582 1573877 := bbase (se 5 (by rfl) ⟨73775, by rfl⟩ : syracuseStep 1573877 = 147551) (by norm_num)
theorem B1049593 : Blo 932582 1049593 := bbase (se 2 (by rfl) ⟨393597, by rfl⟩ : syracuseStep 1049593 = 787195) (by norm_num)
theorem B1049629 : Blo 932582 1049629 := bbase (se 3 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 1049629 = 393611) (by norm_num)
theorem B1049665 : Blo 932582 1049665 := bbase (se 2 (by rfl) ⟨393624, by rfl⟩ : syracuseStep 1049665 = 787249) (by norm_num)
theorem B1180757 : Blo 932582 1180757 := bbase (se 8 (by rfl) ⟨6918, by rfl⟩ : syracuseStep 1180757 = 13837) (by norm_num)
theorem B1770589 : Blo 932582 1770589 := bbase (se 3 (by rfl) ⟨331985, by rfl⟩ : syracuseStep 1770589 = 663971) (by norm_num)
theorem B1049701 : Blo 932582 1049701 := bbase (se 4 (by rfl) ⟨98409, by rfl⟩ : syracuseStep 1049701 = 196819) (by norm_num)
theorem B1574005 : Blo 932582 1574005 := bbase (se 5 (by rfl) ⟨73781, by rfl⟩ : syracuseStep 1574005 = 147563) (by norm_num)
theorem B1049737 : Blo 932582 1049737 := bbase (se 2 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 1049737 = 787303) (by norm_num)
theorem B1180813 : Blo 932582 1180813 := bbase (se 3 (by rfl) ⟨221402, by rfl⟩ : syracuseStep 1180813 = 442805) (by norm_num)
theorem B2098349 : Blo 932582 2098349 := bbase (se 3 (by rfl) ⟨393440, by rfl⟩ : syracuseStep 2098349 = 786881) (by norm_num)
theorem B1049773 : Blo 932582 1049773 := bbase (se 3 (by rfl) ⟨196832, by rfl⟩ : syracuseStep 1049773 = 393665) (by norm_num)
theorem B1574093 : Blo 932582 1574093 := bbase (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) (by norm_num)
theorem B1049809 : Blo 932582 1049809 := bbase (se 2 (by rfl) ⟨393678, by rfl⟩ : syracuseStep 1049809 = 787357) (by norm_num)
theorem B1180909 : Blo 932582 1180909 := bbase (se 3 (by rfl) ⟨221420, by rfl⟩ : syracuseStep 1180909 = 442841) (by norm_num)
theorem B2098421 : Blo 932582 2098421 := bbase (se 5 (by rfl) ⟨98363, by rfl⟩ : syracuseStep 2098421 = 196727) (by norm_num)
theorem B1049845 : Blo 932582 1049845 := bbase (se 5 (by rfl) ⟨49211, by rfl⟩ : syracuseStep 1049845 = 98423) (by norm_num)
theorem B1049881 : Blo 932582 1049881 := bbase (se 2 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 1049881 = 787411) (by norm_num)
theorem B2098493 : Blo 932582 2098493 := bbase (se 3 (by rfl) ⟨393467, by rfl⟩ : syracuseStep 2098493 = 786935) (by norm_num)
theorem B1049917 : Blo 932582 1049917 := bbase (se 3 (by rfl) ⟨196859, by rfl⟩ : syracuseStep 1049917 = 393719) (by norm_num)
theorem B1574221 : Blo 932582 1574221 := bbase (se 3 (by rfl) ⟨295166, by rfl⟩ : syracuseStep 1574221 = 590333) (by norm_num)
theorem B1049953 : Blo 932582 1049953 := bbase (se 2 (by rfl) ⟨393732, by rfl⟩ : syracuseStep 1049953 = 787465) (by norm_num)
theorem B2098565 : Blo 932582 2098565 := bbase (se 4 (by rfl) ⟨196740, by rfl⟩ : syracuseStep 2098565 = 393481) (by norm_num)
theorem B1049989 : Blo 932582 1049989 := bbase (se 4 (by rfl) ⟨98436, by rfl⟩ : syracuseStep 1049989 = 196873) (by norm_num)
theorem B1770893 : Blo 932582 1770893 := bbase (se 3 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 1770893 = 664085) (by norm_num)
theorem B1181081 : Blo 932582 1181081 := bbase (se 2 (by rfl) ⟨442905, by rfl⟩ : syracuseStep 1181081 = 885811) (by norm_num)
theorem B1574309 : Blo 932582 1574309 := bbase (se 4 (by rfl) ⟨147591, by rfl⟩ : syracuseStep 1574309 = 295183) (by norm_num)
theorem B1050025 : Blo 932582 1050025 := bbase (se 2 (by rfl) ⟨393759, by rfl⟩ : syracuseStep 1050025 = 787519) (by norm_num)
theorem B2360765 : Blo 932582 2360765 := bbase (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) (by norm_num)
theorem B2098637 : Blo 932582 2098637 := bbase (se 3 (by rfl) ⟨393494, by rfl⟩ : syracuseStep 2098637 = 786989) (by norm_num)
theorem B1050061 : Blo 932582 1050061 := bbase (se 3 (by rfl) ⟨196886, by rfl⟩ : syracuseStep 1050061 = 393773) (by norm_num)
theorem B1181137 : Blo 932582 1181137 := bbase (se 2 (by rfl) ⟨442926, by rfl⟩ : syracuseStep 1181137 = 885853) (by norm_num)
theorem B1050097 : Blo 932582 1050097 := bbase (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) (by norm_num)
theorem B2098709 : Blo 932582 2098709 := bbase (se 6 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 2098709 = 98377) (by norm_num)
theorem B1050133 : Blo 932582 1050133 := bbase (se 6 (by rfl) ⟨24612, by rfl⟩ : syracuseStep 1050133 = 49225) (by norm_num)
theorem B1574437 : Blo 932582 1574437 := bbase (se 4 (by rfl) ⟨147603, by rfl⟩ : syracuseStep 1574437 = 295207) (by norm_num)
theorem B1181233 : Blo 932582 1181233 := bbase (se 2 (by rfl) ⟨442962, by rfl⟩ : syracuseStep 1181233 = 885925) (by norm_num)
theorem B1050169 : Blo 932582 1050169 := bbase (se 2 (by rfl) ⟨393813, by rfl⟩ : syracuseStep 1050169 = 787627) (by norm_num)
theorem B2098781 : Blo 932582 2098781 := bbase (se 3 (by rfl) ⟨393521, by rfl⟩ : syracuseStep 2098781 = 787043) (by norm_num)
theorem B1050205 : Blo 932582 1050205 := bbase (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) (by norm_num)
theorem B1574525 : Blo 932582 1574525 := bbase (se 3 (by rfl) ⟨295223, by rfl⟩ : syracuseStep 1574525 = 590447) (by norm_num)
theorem B1050241 : Blo 932582 1050241 := bbase (se 2 (by rfl) ⟨393840, by rfl⟩ : syracuseStep 1050241 = 787681) (by norm_num)
theorem B2098853 : Blo 932582 2098853 := bbase (se 4 (by rfl) ⟨196767, by rfl⟩ : syracuseStep 2098853 = 393535) (by norm_num)
theorem B1050277 : Blo 932582 1050277 := bbase (se 4 (by rfl) ⟨98463, by rfl⟩ : syracuseStep 1050277 = 196927) (by norm_num)
theorem B1050313 : Blo 932582 1050313 := bbase (se 2 (by rfl) ⟨393867, by rfl⟩ : syracuseStep 1050313 = 787735) (by norm_num)
theorem B1181405 : Blo 932582 1181405 := bbase (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) (by norm_num)
theorem B2098925 : Blo 932582 2098925 := bbase (se 3 (by rfl) ⟨393548, by rfl⟩ : syracuseStep 2098925 = 787097) (by norm_num)
theorem B1050349 : Blo 932582 1050349 := bbase (se 3 (by rfl) ⟨196940, by rfl⟩ : syracuseStep 1050349 = 393881) (by norm_num)
theorem B7571189 : Blo 932582 7571189 := bbase (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) (by norm_num)
theorem B1574653 : Blo 932582 1574653 := bbase (se 3 (by rfl) ⟨295247, by rfl⟩ : syracuseStep 1574653 = 590495) (by norm_num)
theorem B1050385 : Blo 932582 1050385 := bbase (se 2 (by rfl) ⟨393894, by rfl⟩ : syracuseStep 1050385 = 787789) (by norm_num)
theorem B2361109 : Blo 932582 2361109 := bbase (se 6 (by rfl) ⟨55338, by rfl⟩ : syracuseStep 2361109 = 110677) (by norm_num)
theorem B7669525 : Blo 932582 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B1181461 : Blo 932582 1181461 := bbase (se 6 (by rfl) ⟨27690, by rfl⟩ : syracuseStep 1181461 = 55381) (by norm_num)
theorem B2098997 : Blo 932582 2098997 := bbase (se 5 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 2098997 = 196781) (by norm_num)
theorem B1050421 : Blo 932582 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B3147605 : Blo 932582 3147605 := bbase (se 9 (by rfl) ⟨9221, by rfl⟩ : syracuseStep 3147605 = 18443) (by norm_num)
theorem B1574741 : Blo 932582 1574741 := bbase (se 9 (by rfl) ⟨4613, by rfl⟩ : syracuseStep 1574741 = 9227) (by norm_num)
theorem B1050457 : Blo 932582 1050457 := bbase (se 2 (by rfl) ⟨393921, by rfl⟩ : syracuseStep 1050457 = 787843) (by norm_num)
theorem B1181557 : Blo 932582 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B2099069 : Blo 932582 2099069 := bbase (se 3 (by rfl) ⟨393575, by rfl⟩ : syracuseStep 2099069 = 787151) (by norm_num)
theorem B1050493 : Blo 932582 1050493 := bbase (se 3 (by rfl) ⟨196967, by rfl⟩ : syracuseStep 1050493 = 393935) (by norm_num)
theorem B2361221 : Blo 932582 2361221 := bbase (se 4 (by rfl) ⟨221364, by rfl⟩ : syracuseStep 2361221 = 442729) (by norm_num)
theorem B1050529 : Blo 932582 1050529 := bbase (se 2 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 1050529 = 787897) (by norm_num)
theorem B2099141 : Blo 932582 2099141 := bbase (se 4 (by rfl) ⟨196794, by rfl⟩ : syracuseStep 2099141 = 393589) (by norm_num)
theorem B1050565 : Blo 932582 1050565 := bbase (se 4 (by rfl) ⟨98490, by rfl⟩ : syracuseStep 1050565 = 196981) (by norm_num)
theorem B1574869 : Blo 932582 1574869 := bbase (se 7 (by rfl) ⟨18455, by rfl⟩ : syracuseStep 1574869 = 36911) (by norm_num)
theorem B1050601 : Blo 932582 1050601 := bbase (se 2 (by rfl) ⟨393975, by rfl⟩ : syracuseStep 1050601 = 787951) (by norm_num)
theorem B2099213 : Blo 932582 2099213 := bbase (se 3 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 2099213 = 787205) (by norm_num)
theorem B1050637 : Blo 932582 1050637 := bbase (se 3 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 1050637 = 393989) (by norm_num)
theorem B1181729 : Blo 932582 1181729 := bbase (se 2 (by rfl) ⟨443148, by rfl⟩ : syracuseStep 1181729 = 886297) (by norm_num)
theorem B4491301 : Blo 932582 4491301 := bbase (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) (by norm_num)
theorem B1574957 : Blo 932582 1574957 := bbase (se 3 (by rfl) ⟨295304, by rfl⟩ : syracuseStep 1574957 = 590609) (by norm_num)
theorem B1050673 : Blo 932582 1050673 := bbase (se 2 (by rfl) ⟨394002, by rfl⟩ : syracuseStep 1050673 = 788005) (by norm_num)
theorem B2361413 : Blo 932582 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B2099285 : Blo 932582 2099285 := bbase (se 8 (by rfl) ⟨12300, by rfl⟩ : syracuseStep 2099285 = 24601) (by norm_num)
theorem B1050709 : Blo 932582 1050709 := bbase (se 8 (by rfl) ⟨6156, by rfl⟩ : syracuseStep 1050709 = 12313) (by norm_num)
theorem B1181785 : Blo 932582 1181785 := bbase (se 2 (by rfl) ⟨443169, by rfl⟩ : syracuseStep 1181785 = 886339) (by norm_num)
theorem B1050745 : Blo 932582 1050745 := bbase (se 2 (by rfl) ⟨394029, by rfl⟩ : syracuseStep 1050745 = 788059) (by norm_num)
theorem B1771645 : Blo 932582 1771645 := bbase (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) (by norm_num)
theorem B2099357 : Blo 932582 2099357 := bbase (se 3 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 2099357 = 787259) (by norm_num)
theorem B1050781 : Blo 932582 1050781 := bbase (se 3 (by rfl) ⟨197021, by rfl⟩ : syracuseStep 1050781 = 394043) (by norm_num)
theorem B1575085 : Blo 932582 1575085 := bbase (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) (by norm_num)
theorem B1181881 : Blo 932582 1181881 := bbase (se 2 (by rfl) ⟨443205, by rfl⟩ : syracuseStep 1181881 = 886411) (by norm_num)
theorem B1050817 : Blo 932582 1050817 := bbase (se 2 (by rfl) ⟨394056, by rfl⟩ : syracuseStep 1050817 = 788113) (by norm_num)
theorem B5998805 : Blo 932582 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B2099429 : Blo 932582 2099429 := bbase (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) (by norm_num)
theorem B1050853 : Blo 932582 1050853 := bbase (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) (by norm_num)
theorem B3148037 : Blo 932582 3148037 := bbase (se 4 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 3148037 = 590257) (by norm_num)
theorem B1575173 : Blo 932582 1575173 := bbase (se 4 (by rfl) ⟨147672, by rfl⟩ : syracuseStep 1575173 = 295345) (by norm_num)
theorem B1050889 : Blo 932582 1050889 := bbase (se 2 (by rfl) ⟨394083, by rfl⟩ : syracuseStep 1050889 = 788167) (by norm_num)
theorem B1771789 : Blo 932582 1771789 := bbase (se 3 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 1771789 = 664421) (by norm_num)
theorem B2099501 : Blo 932582 2099501 := bbase (se 3 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 2099501 = 787313) (by norm_num)
theorem B1050925 : Blo 932582 1050925 := bbase (se 3 (by rfl) ⟨197048, by rfl⟩ : syracuseStep 1050925 = 394097) (by norm_num)
theorem B1050961 : Blo 932582 1050961 := bbase (se 2 (by rfl) ⟨394110, by rfl⟩ : syracuseStep 1050961 = 788221) (by norm_num)
theorem B2656613 : Blo 932582 2656613 := bbase (se 4 (by rfl) ⟨249057, by rfl⟩ : syracuseStep 2656613 = 498115) (by norm_num)
theorem B1182053 : Blo 932582 1182053 := bbase (se 4 (by rfl) ⟨110817, by rfl⟩ : syracuseStep 1182053 = 221635) (by norm_num)
theorem B2099573 : Blo 932582 2099573 := bbase (se 5 (by rfl) ⟨98417, by rfl⟩ : syracuseStep 2099573 = 196835) (by norm_num)
theorem B1050997 : Blo 932582 1050997 := bbase (se 5 (by rfl) ⟨49265, by rfl⟩ : syracuseStep 1050997 = 98531) (by norm_num)
theorem B1575301 : Blo 932582 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B1051033 : Blo 932582 1051033 := bbase (se 2 (by rfl) ⟨394137, by rfl⟩ : syracuseStep 1051033 = 788275) (by norm_num)
theorem B2361757 : Blo 932582 2361757 := bbase (se 3 (by rfl) ⟨442829, by rfl⟩ : syracuseStep 2361757 = 885659) (by norm_num)
theorem B1182109 : Blo 932582 1182109 := bbase (se 3 (by rfl) ⟨221645, by rfl⟩ : syracuseStep 1182109 = 443291) (by norm_num)
theorem B1771949 : Blo 932582 1771949 := bbase (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) (by norm_num)
theorem B2099645 : Blo 932582 2099645 := bbase (se 3 (by rfl) ⟨393683, by rfl⟩ : syracuseStep 2099645 = 787367) (by norm_num)
theorem B1051069 : Blo 932582 1051069 := bbase (se 3 (by rfl) ⟨197075, by rfl⟩ : syracuseStep 1051069 = 394151) (by norm_num)
theorem B1575389 : Blo 932582 1575389 := bbase (se 3 (by rfl) ⟨295385, by rfl⟩ : syracuseStep 1575389 = 590771) (by norm_num)
theorem B1051105 : Blo 932582 1051105 := bbase (se 2 (by rfl) ⟨394164, by rfl⟩ : syracuseStep 1051105 = 788329) (by norm_num)
theorem B4000229 : Blo 932582 4000229 := bbase (se 4 (by rfl) ⟨375021, by rfl⟩ : syracuseStep 4000229 = 750043) (by norm_num)
theorem B1182205 : Blo 932582 1182205 := bbase (se 3 (by rfl) ⟨221663, by rfl⟩ : syracuseStep 1182205 = 443327) (by norm_num)
theorem B2099717 : Blo 932582 2099717 := bbase (se 4 (by rfl) ⟨196848, by rfl⟩ : syracuseStep 2099717 = 393697) (by norm_num)
theorem B1051141 : Blo 932582 1051141 := bbase (se 4 (by rfl) ⟨98544, by rfl⟩ : syracuseStep 1051141 = 197089) (by norm_num)
theorem B2361869 : Blo 932582 2361869 := bbase (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) (by norm_num)
theorem B1051177 : Blo 932582 1051177 := bbase (se 2 (by rfl) ⟨394191, by rfl⟩ : syracuseStep 1051177 = 788383) (by norm_num)
theorem B1772093 : Blo 932582 1772093 := bbase (se 3 (by rfl) ⟨332267, by rfl⟩ : syracuseStep 1772093 = 664535) (by norm_num)
theorem B2099789 : Blo 932582 2099789 := bbase (se 3 (by rfl) ⟨393710, by rfl⟩ : syracuseStep 2099789 = 787421) (by norm_num)
theorem B1051213 : Blo 932582 1051213 := bbase (se 3 (by rfl) ⟨197102, by rfl⟩ : syracuseStep 1051213 = 394205) (by norm_num)
theorem B3541589 : Blo 932582 3541589 := bbase (se 8 (by rfl) ⟨20751, by rfl⟩ : syracuseStep 3541589 = 41503) (by norm_num)
theorem B1575517 : Blo 932582 1575517 := bbase (se 3 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 1575517 = 590819) (by norm_num)
theorem B1051249 : Blo 932582 1051249 := bbase (se 2 (by rfl) ⟨394218, by rfl⟩ : syracuseStep 1051249 = 788437) (by norm_num)
theorem B2099861 : Blo 932582 2099861 := bbase (se 6 (by rfl) ⟨49215, by rfl⟩ : syracuseStep 2099861 = 98431) (by norm_num)
theorem B15960725 : Blo 932582 15960725 := bbase (se 6 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 15960725 = 748159) (by norm_num)
theorem B1051285 : Blo 932582 1051285 := bbase (se 6 (by rfl) ⟨24639, by rfl⟩ : syracuseStep 1051285 = 49279) (by norm_num)
theorem B7998101 : Blo 932582 7998101 := bbase (se 6 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 7998101 = 374911) (by norm_num)
theorem B1182377 : Blo 932582 1182377 := bbase (se 2 (by rfl) ⟨443391, by rfl⟩ : syracuseStep 1182377 = 886783) (by norm_num)
theorem B3148469 : Blo 932582 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B1575605 : Blo 932582 1575605 := bbase (se 5 (by rfl) ⟨73856, by rfl⟩ : syracuseStep 1575605 = 147713) (by norm_num)
theorem B1051321 : Blo 932582 1051321 := bbase (se 2 (by rfl) ⟨394245, by rfl⟩ : syracuseStep 1051321 = 788491) (by norm_num)
theorem B2362061 : Blo 932582 2362061 := bbase (se 3 (by rfl) ⟨442886, by rfl⟩ : syracuseStep 2362061 = 885773) (by norm_num)
theorem B2099933 : Blo 932582 2099933 := bbase (se 3 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 2099933 = 787475) (by norm_num)
theorem B1051357 : Blo 932582 1051357 := bbase (se 3 (by rfl) ⟨197129, by rfl⟩ : syracuseStep 1051357 = 394259) (by norm_num)
theorem B1182433 : Blo 932582 1182433 := bbase (se 2 (by rfl) ⟨443412, by rfl⟩ : syracuseStep 1182433 = 886825) (by norm_num)
theorem B1051393 : Blo 932582 1051393 := bbase (se 2 (by rfl) ⟨394272, by rfl⟩ : syracuseStep 1051393 = 788545) (by norm_num)
theorem B2100005 : Blo 932582 2100005 := bbase (se 4 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 2100005 = 393751) (by norm_num)
theorem B2394917 : Blo 932582 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1051429 : Blo 932582 1051429 := bbase (se 4 (by rfl) ⟨98571, by rfl⟩ : syracuseStep 1051429 = 197143) (by norm_num)
theorem B1575733 : Blo 932582 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B1182529 : Blo 932582 1182529 := bbase (se 2 (by rfl) ⟨443448, by rfl⟩ : syracuseStep 1182529 = 886897) (by norm_num)
theorem B1051465 : Blo 932582 1051465 := bbase (se 2 (by rfl) ⟨394299, by rfl⟩ : syracuseStep 1051465 = 788599) (by norm_num)
theorem B1772381 : Blo 932582 1772381 := bbase (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) (by norm_num)
theorem B2132837 : Blo 932582 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B2100077 : Blo 932582 2100077 := bbase (se 3 (by rfl) ⟨393764, by rfl⟩ : syracuseStep 2100077 = 787529) (by norm_num)
theorem B1051501 : Blo 932582 1051501 := bbase (se 3 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 1051501 = 394313) (by norm_num)
theorem B3541877 : Blo 932582 3541877 := bbase (se 5 (by rfl) ⟨166025, by rfl⟩ : syracuseStep 3541877 = 332051) (by norm_num)
theorem B1575821 : Blo 932582 1575821 := bbase (se 3 (by rfl) ⟨295466, by rfl⟩ : syracuseStep 1575821 = 590933) (by norm_num)
theorem B1051537 : Blo 932582 1051537 := bbase (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) (by norm_num)
theorem B2100149 : Blo 932582 2100149 := bbase (se 5 (by rfl) ⟨98444, by rfl⟩ : syracuseStep 2100149 = 196889) (by norm_num)
theorem B1051573 : Blo 932582 1051573 := bbase (se 5 (by rfl) ⟨49292, by rfl⟩ : syracuseStep 1051573 = 98585) (by norm_num)
theorem B1051609 : Blo 932582 1051609 := bbase (se 2 (by rfl) ⟨394353, by rfl⟩ : syracuseStep 1051609 = 788707) (by norm_num)
theorem B1182701 : Blo 932582 1182701 := bbase (se 3 (by rfl) ⟨221756, by rfl⟩ : syracuseStep 1182701 = 443513) (by norm_num)
theorem B1772533 : Blo 932582 1772533 := bbase (se 5 (by rfl) ⟨83087, by rfl⟩ : syracuseStep 1772533 = 166175) (by norm_num)
theorem B2100221 : Blo 932582 2100221 := bbase (se 3 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 2100221 = 787583) (by norm_num)
theorem B1051645 : Blo 932582 1051645 := bbase (se 3 (by rfl) ⟨197183, by rfl⟩ : syracuseStep 1051645 = 394367) (by norm_num)
theorem B1575949 : Blo 932582 1575949 := bbase (se 3 (by rfl) ⟨295490, by rfl⟩ : syracuseStep 1575949 = 590981) (by norm_num)
theorem B1051681 : Blo 932582 1051681 := bbase (se 2 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 1051681 = 788761) (by norm_num)
theorem B2362405 : Blo 932582 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B1182757 : Blo 932582 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B2100293 : Blo 932582 2100293 := bbase (se 4 (by rfl) ⟨196902, by rfl⟩ : syracuseStep 2100293 = 393805) (by norm_num)
theorem B1051717 : Blo 932582 1051717 := bbase (se 4 (by rfl) ⟨98598, by rfl⟩ : syracuseStep 1051717 = 197197) (by norm_num)
theorem B3148901 : Blo 932582 3148901 := bbase (se 4 (by rfl) ⟨295209, by rfl⟩ : syracuseStep 3148901 = 590419) (by norm_num)
theorem B1576037 : Blo 932582 1576037 := bbase (se 4 (by rfl) ⟨147753, by rfl⟩ : syracuseStep 1576037 = 295507) (by norm_num)
theorem B1051753 : Blo 932582 1051753 := bbase (se 2 (by rfl) ⟨394407, by rfl⟩ : syracuseStep 1051753 = 788815) (by norm_num)
theorem B1182853 : Blo 932582 1182853 := bbase (se 4 (by rfl) ⟨110892, by rfl⟩ : syracuseStep 1182853 = 221785) (by norm_num)
theorem B2100365 : Blo 932582 2100365 := bbase (se 3 (by rfl) ⟨393818, by rfl⟩ : syracuseStep 2100365 = 787637) (by norm_num)
theorem B1051789 : Blo 932582 1051789 := bbase (se 3 (by rfl) ⟨197210, by rfl⟩ : syracuseStep 1051789 = 394421) (by norm_num)
theorem B4721813 : Blo 932582 4721813 := bbase (se 6 (by rfl) ⟨110667, by rfl⟩ : syracuseStep 4721813 = 221335) (by norm_num)
theorem B2362517 : Blo 932582 2362517 := bbase (se 6 (by rfl) ⟨55371, by rfl⟩ : syracuseStep 2362517 = 110743) (by norm_num)
theorem B1051825 : Blo 932582 1051825 := bbase (se 2 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 1051825 = 788869) (by norm_num)
theorem B2100437 : Blo 932582 2100437 := bbase (se 7 (by rfl) ⟨24614, by rfl⟩ : syracuseStep 2100437 = 49229) (by norm_num)
theorem B2526421 : Blo 932582 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B1051861 : Blo 932582 1051861 := bbase (se 7 (by rfl) ⟨12326, by rfl⟩ : syracuseStep 1051861 = 24653) (by norm_num)
theorem B1576165 : Blo 932582 1576165 := bbase (se 4 (by rfl) ⟨147765, by rfl⟩ : syracuseStep 1576165 = 295531) (by norm_num)
theorem B1051897 : Blo 932582 1051897 := bbase (se 2 (by rfl) ⟨394461, by rfl⟩ : syracuseStep 1051897 = 788923) (by norm_num)
theorem B2100509 : Blo 932582 2100509 := bbase (se 3 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 2100509 = 787691) (by norm_num)
theorem B1051933 : Blo 932582 1051933 := bbase (se 3 (by rfl) ⟨197237, by rfl⟩ : syracuseStep 1051933 = 394475) (by norm_num)
theorem B1772837 : Blo 932582 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B1183025 : Blo 932582 1183025 := bbase (se 2 (by rfl) ⟨443634, by rfl⟩ : syracuseStep 1183025 = 887269) (by norm_num)
theorem B1215797 : Blo 932582 1215797 := bbase (se 5 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 1215797 = 113981) (by norm_num)
theorem B1576253 : Blo 932582 1576253 := bbase (se 3 (by rfl) ⟨295547, by rfl⟩ : syracuseStep 1576253 = 591095) (by norm_num)
theorem B1051969 : Blo 932582 1051969 := bbase (se 2 (by rfl) ⟨394488, by rfl⟩ : syracuseStep 1051969 = 788977) (by norm_num)
theorem B2362709 : Blo 932582 2362709 := bbase (se 11 (by rfl) ⟨1730, by rfl⟩ : syracuseStep 2362709 = 3461) (by norm_num)
theorem B2100581 : Blo 932582 2100581 := bbase (se 4 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 2100581 = 393859) (by norm_num)
theorem B1052005 : Blo 932582 1052005 := bbase (se 4 (by rfl) ⟨98625, by rfl⟩ : syracuseStep 1052005 = 197251) (by norm_num)
theorem B1183081 : Blo 932582 1183081 := bbase (se 2 (by rfl) ⟨443655, by rfl⟩ : syracuseStep 1183081 = 887311) (by norm_num)
theorem B1052041 : Blo 932582 1052041 := bbase (se 2 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 1052041 = 789031) (by norm_num)
theorem B2100653 : Blo 932582 2100653 := bbase (se 3 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 2100653 = 787745) (by norm_num)
theorem B1052077 : Blo 932582 1052077 := bbase (se 3 (by rfl) ⟨197264, by rfl⟩ : syracuseStep 1052077 = 394529) (by norm_num)
theorem B1576381 : Blo 932582 1576381 := bbase (se 3 (by rfl) ⟨295571, by rfl⟩ : syracuseStep 1576381 = 591143) (by norm_num)
theorem B1183177 : Blo 932582 1183177 := bbase (se 2 (by rfl) ⟨443691, by rfl⟩ : syracuseStep 1183177 = 887383) (by norm_num)
theorem B1052113 : Blo 932582 1052113 := bbase (se 2 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 1052113 = 789085) (by norm_num)
theorem B2100725 : Blo 932582 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B1052149 : Blo 932582 1052149 := bbase (se 5 (by rfl) ⟨49319, by rfl⟩ : syracuseStep 1052149 = 98639) (by norm_num)
theorem B3149333 : Blo 932582 3149333 := bbase (se 6 (by rfl) ⟨73812, by rfl⟩ : syracuseStep 3149333 = 147625) (by norm_num)
theorem B7573013 : Blo 932582 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B1576469 : Blo 932582 1576469 := bbase (se 6 (by rfl) ⟨36948, by rfl⟩ : syracuseStep 1576469 = 73897) (by norm_num)
theorem B1052185 : Blo 932582 1052185 := bbase (se 2 (by rfl) ⟨394569, by rfl⟩ : syracuseStep 1052185 = 789139) (by norm_num)
theorem B2100797 : Blo 932582 2100797 := bbase (se 3 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 2100797 = 787799) (by norm_num)
theorem B1052221 : Blo 932582 1052221 := bbase (se 3 (by rfl) ⟨197291, by rfl⟩ : syracuseStep 1052221 = 394583) (by norm_num)
theorem B1052257 : Blo 932582 1052257 := bbase (se 2 (by rfl) ⟨394596, by rfl⟩ : syracuseStep 1052257 = 789193) (by norm_num)
theorem B1183349 : Blo 932582 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B2100869 : Blo 932582 2100869 := bbase (se 4 (by rfl) ⟨196956, by rfl⟩ : syracuseStep 2100869 = 393913) (by norm_num)
theorem B1052293 : Blo 932582 1052293 := bbase (se 4 (by rfl) ⟨98652, by rfl⟩ : syracuseStep 1052293 = 197305) (by norm_num)
theorem B1576597 : Blo 932582 1576597 := bbase (se 6 (by rfl) ⟨36951, by rfl⟩ : syracuseStep 1576597 = 73903) (by norm_num)
theorem B1052329 : Blo 932582 1052329 := bbase (se 2 (by rfl) ⟨394623, by rfl⟩ : syracuseStep 1052329 = 789247) (by norm_num)
theorem B2363053 : Blo 932582 2363053 := bbase (se 3 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 2363053 = 886145) (by norm_num)
theorem B1183405 : Blo 932582 1183405 := bbase (se 3 (by rfl) ⟨221888, by rfl⟩ : syracuseStep 1183405 = 443777) (by norm_num)
theorem B2100941 : Blo 932582 2100941 := bbase (se 3 (by rfl) ⟨393926, by rfl⟩ : syracuseStep 2100941 = 787853) (by norm_num)
theorem B1052365 : Blo 932582 1052365 := bbase (se 3 (by rfl) ⟨197318, by rfl⟩ : syracuseStep 1052365 = 394637) (by norm_num)
theorem B1576685 : Blo 932582 1576685 := bbase (se 3 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 1576685 = 591257) (by norm_num)
theorem B1052401 : Blo 932582 1052401 := bbase (se 2 (by rfl) ⟨394650, by rfl⟩ : syracuseStep 1052401 = 789301) (by norm_num)
theorem B1183501 : Blo 932582 1183501 := bbase (se 3 (by rfl) ⟨221906, by rfl⟩ : syracuseStep 1183501 = 443813) (by norm_num)
theorem B2101013 : Blo 932582 2101013 := bbase (se 6 (by rfl) ⟨49242, by rfl⟩ : syracuseStep 2101013 = 98485) (by norm_num)
theorem B1052437 : Blo 932582 1052437 := bbase (se 6 (by rfl) ⟨24666, by rfl⟩ : syracuseStep 1052437 = 49333) (by norm_num)
theorem B2363165 : Blo 932582 2363165 := bbase (se 3 (by rfl) ⟨443093, by rfl⟩ : syracuseStep 2363165 = 886187) (by norm_num)
theorem B1052473 : Blo 932582 1052473 := bbase (se 2 (by rfl) ⟨394677, by rfl⟩ : syracuseStep 1052473 = 789355) (by norm_num)
theorem B2101085 : Blo 932582 2101085 := bbase (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) (by norm_num)
theorem B1052509 : Blo 932582 1052509 := bbase (se 3 (by rfl) ⟨197345, by rfl⟩ : syracuseStep 1052509 = 394691) (by norm_num)
theorem B1576813 : Blo 932582 1576813 := bbase (se 3 (by rfl) ⟨295652, by rfl⟩ : syracuseStep 1576813 = 591305) (by norm_num)
theorem B1052545 : Blo 932582 1052545 := bbase (se 2 (by rfl) ⟨394704, by rfl⟩ : syracuseStep 1052545 = 789409) (by norm_num)
theorem B5312405 : Blo 932582 5312405 := bbase (se 6 (by rfl) ⟨124509, by rfl⟩ : syracuseStep 5312405 = 249019) (by norm_num)
theorem B2658197 : Blo 932582 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2101157 : Blo 932582 2101157 := bbase (se 4 (by rfl) ⟨196983, by rfl⟩ : syracuseStep 2101157 = 393967) (by norm_num)
theorem B1052581 : Blo 932582 1052581 := bbase (se 4 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 1052581 = 197359) (by norm_num)
theorem B1183673 : Blo 932582 1183673 := bbase (se 2 (by rfl) ⟨443877, by rfl⟩ : syracuseStep 1183673 = 887755) (by norm_num)
theorem B3149765 : Blo 932582 3149765 := bbase (se 4 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 3149765 = 590581) (by norm_num)
theorem B1576901 : Blo 932582 1576901 := bbase (se 4 (by rfl) ⟨147834, by rfl⟩ : syracuseStep 1576901 = 295669) (by norm_num)
theorem B1052617 : Blo 932582 1052617 := bbase (se 2 (by rfl) ⟨394731, by rfl⟩ : syracuseStep 1052617 = 789463) (by norm_num)
theorem B2363357 : Blo 932582 2363357 := bbase (se 3 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 2363357 = 886259) (by norm_num)
theorem B2101229 : Blo 932582 2101229 := bbase (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) (by norm_num)
theorem B1052653 : Blo 932582 1052653 := bbase (se 3 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 1052653 = 394745) (by norm_num)
theorem B1183729 : Blo 932582 1183729 := bbase (se 2 (by rfl) ⟨443898, by rfl⟩ : syracuseStep 1183729 = 887797) (by norm_num)
theorem B1052689 : Blo 932582 1052689 := bbase (se 2 (by rfl) ⟨394758, by rfl⟩ : syracuseStep 1052689 = 789517) (by norm_num)
theorem B3543061 : Blo 932582 3543061 := bbase (se 6 (by rfl) ⟨83040, by rfl⟩ : syracuseStep 3543061 = 166081) (by norm_num)
theorem B1773589 : Blo 932582 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B2101301 : Blo 932582 2101301 := bbase (se 5 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 2101301 = 196997) (by norm_num)
theorem B5050421 : Blo 932582 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B1052725 : Blo 932582 1052725 := bbase (se 5 (by rfl) ⟨49346, by rfl⟩ : syracuseStep 1052725 = 98693) (by norm_num)
theorem B1577029 : Blo 932582 1577029 := bbase (se 4 (by rfl) ⟨147846, by rfl⟩ : syracuseStep 1577029 = 295693) (by norm_num)
theorem B1183825 : Blo 932582 1183825 := bbase (se 2 (by rfl) ⟨443934, by rfl⟩ : syracuseStep 1183825 = 887869) (by norm_num)
theorem B1052761 : Blo 932582 1052761 := bbase (se 2 (by rfl) ⟨394785, by rfl⟩ : syracuseStep 1052761 = 789571) (by norm_num)
theorem B2101373 : Blo 932582 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B1052797 : Blo 932582 1052797 := bbase (se 3 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 1052797 = 394799) (by norm_num)
theorem B8982677 : Blo 932582 8982677 := bbase (se 6 (by rfl) ⟨210531, by rfl⟩ : syracuseStep 8982677 = 421063) (by norm_num)
theorem B1577117 : Blo 932582 1577117 := bbase (se 3 (by rfl) ⟨295709, by rfl⟩ : syracuseStep 1577117 = 591419) (by norm_num)
theorem B1052833 : Blo 932582 1052833 := bbase (se 2 (by rfl) ⟨394812, by rfl⟩ : syracuseStep 1052833 = 789625) (by norm_num)
theorem B1773733 : Blo 932582 1773733 := bbase (se 4 (by rfl) ⟨166287, by rfl⟩ : syracuseStep 1773733 = 332575) (by norm_num)
theorem B2101445 : Blo 932582 2101445 := bbase (se 4 (by rfl) ⟨197010, by rfl⟩ : syracuseStep 2101445 = 394021) (by norm_num)
theorem B1052869 : Blo 932582 1052869 := bbase (se 4 (by rfl) ⟨98706, by rfl⟩ : syracuseStep 1052869 = 197413) (by norm_num)
theorem B1052905 : Blo 932582 1052905 := bbase (se 2 (by rfl) ⟨394839, by rfl⟩ : syracuseStep 1052905 = 789679) (by norm_num)
theorem B1183997 : Blo 932582 1183997 := bbase (se 3 (by rfl) ⟨221999, by rfl⟩ : syracuseStep 1183997 = 443999) (by norm_num)
theorem B2101517 : Blo 932582 2101517 := bbase (se 3 (by rfl) ⟨394034, by rfl⟩ : syracuseStep 2101517 = 788069) (by norm_num)
theorem B1052941 : Blo 932582 1052941 := bbase (se 3 (by rfl) ⟨197426, by rfl⟩ : syracuseStep 1052941 = 394853) (by norm_num)
theorem B1577245 : Blo 932582 1577245 := bbase (se 3 (by rfl) ⟨295733, by rfl⟩ : syracuseStep 1577245 = 591467) (by norm_num)
theorem B1052977 : Blo 932582 1052977 := bbase (se 2 (by rfl) ⟨394866, by rfl⟩ : syracuseStep 1052977 = 789733) (by norm_num)
theorem B2363701 : Blo 932582 2363701 := bbase (se 5 (by rfl) ⟨110798, by rfl⟩ : syracuseStep 2363701 = 221597) (by norm_num)
theorem B1184053 : Blo 932582 1184053 := bbase (se 5 (by rfl) ⟨55502, by rfl⟩ : syracuseStep 1184053 = 111005) (by norm_num)
theorem B3543365 : Blo 932582 3543365 := bbase (se 4 (by rfl) ⟨332190, by rfl⟩ : syracuseStep 3543365 = 664381) (by norm_num)
theorem B1773893 : Blo 932582 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B2101589 : Blo 932582 2101589 := bbase (se 10 (by rfl) ⟨3078, by rfl⟩ : syracuseStep 2101589 = 6157) (by norm_num)
theorem B1053013 : Blo 932582 1053013 := bbase (se 10 (by rfl) ⟨1542, by rfl⟩ : syracuseStep 1053013 = 3085) (by norm_num)
theorem B3150197 : Blo 932582 3150197 := bbase (se 5 (by rfl) ⟨147665, by rfl⟩ : syracuseStep 3150197 = 295331) (by norm_num)
theorem B1577333 : Blo 932582 1577333 := bbase (se 5 (by rfl) ⟨73937, by rfl⟩ : syracuseStep 1577333 = 147875) (by norm_num)
theorem B1053049 : Blo 932582 1053049 := bbase (se 2 (by rfl) ⟨394893, by rfl⟩ : syracuseStep 1053049 = 789787) (by norm_num)
theorem B1184149 : Blo 932582 1184149 := bbase (se 6 (by rfl) ⟨27753, by rfl⟩ : syracuseStep 1184149 = 55507) (by norm_num)
theorem B1216921 : Blo 932582 1216921 := bbase (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) (by norm_num)
theorem B2101661 : Blo 932582 2101661 := bbase (se 3 (by rfl) ⟨394061, by rfl⟩ : syracuseStep 2101661 = 788123) (by norm_num)
theorem B1053085 : Blo 932582 1053085 := bbase (se 3 (by rfl) ⟨197453, by rfl⟩ : syracuseStep 1053085 = 394907) (by norm_num)
theorem B4723109 : Blo 932582 4723109 := bbase (se 4 (by rfl) ⟨442791, by rfl⟩ : syracuseStep 4723109 = 885583) (by norm_num)
theorem B2363813 : Blo 932582 2363813 := bbase (se 4 (by rfl) ⟨221607, by rfl⟩ : syracuseStep 2363813 = 443215) (by norm_num)
theorem B1053121 : Blo 932582 1053121 := bbase (se 2 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 1053121 = 789841) (by norm_num)
theorem B1774037 : Blo 932582 1774037 := bbase (se 7 (by rfl) ⟨20789, by rfl⟩ : syracuseStep 1774037 = 41579) (by norm_num)
theorem B2101733 : Blo 932582 2101733 := bbase (se 4 (by rfl) ⟨197037, by rfl⟩ : syracuseStep 2101733 = 394075) (by norm_num)
theorem B1053157 : Blo 932582 1053157 := bbase (se 4 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 1053157 = 197467) (by norm_num)
theorem B1577461 : Blo 932582 1577461 := bbase (se 5 (by rfl) ⟨73943, by rfl⟩ : syracuseStep 1577461 = 147887) (by norm_num)
theorem B1053193 : Blo 932582 1053193 := bbase (se 2 (by rfl) ⟨394947, by rfl⟩ : syracuseStep 1053193 = 789895) (by norm_num)
theorem B2101805 : Blo 932582 2101805 := bbase (se 3 (by rfl) ⟨394088, by rfl⟩ : syracuseStep 2101805 = 788177) (by norm_num)
theorem B1053229 : Blo 932582 1053229 := bbase (se 3 (by rfl) ⟨197480, by rfl⟩ : syracuseStep 1053229 = 394961) (by norm_num)
theorem B2658869 : Blo 932582 2658869 := bbase (se 5 (by rfl) ⟨124634, by rfl⟩ : syracuseStep 2658869 = 249269) (by norm_num)
theorem B1184321 : Blo 932582 1184321 := bbase (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) (by norm_num)
theorem B1577549 : Blo 932582 1577549 := bbase (se 3 (by rfl) ⟨295790, by rfl⟩ : syracuseStep 1577549 = 591581) (by norm_num)
theorem B1053265 : Blo 932582 1053265 := bbase (se 2 (by rfl) ⟨394974, by rfl⟩ : syracuseStep 1053265 = 789949) (by norm_num)
theorem B2364005 : Blo 932582 2364005 := bbase (se 4 (by rfl) ⟨221625, by rfl⟩ : syracuseStep 2364005 = 443251) (by norm_num)
theorem B2101877 : Blo 932582 2101877 := bbase (se 5 (by rfl) ⟨98525, by rfl⟩ : syracuseStep 2101877 = 197051) (by norm_num)
theorem B1053301 : Blo 932582 1053301 := bbase (se 5 (by rfl) ⟨49373, by rfl⟩ : syracuseStep 1053301 = 98747) (by norm_num)
theorem B1184377 : Blo 932582 1184377 := bbase (se 2 (by rfl) ⟨444141, by rfl⟩ : syracuseStep 1184377 = 888283) (by norm_num)
theorem B1217173 : Blo 932582 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1053337 : Blo 932582 1053337 := bbase (se 2 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 1053337 = 790003) (by norm_num)
theorem B2101949 : Blo 932582 2101949 := bbase (se 3 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 2101949 = 788231) (by norm_num)
theorem B1053373 : Blo 932582 1053373 := bbase (se 3 (by rfl) ⟨197507, by rfl⟩ : syracuseStep 1053373 = 395015) (by norm_num)
theorem B1577677 : Blo 932582 1577677 := bbase (se 3 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 1577677 = 591629) (by norm_num)
theorem B1184473 : Blo 932582 1184473 := bbase (se 2 (by rfl) ⟨444177, by rfl⟩ : syracuseStep 1184473 = 888355) (by norm_num)
theorem B1053409 : Blo 932582 1053409 := bbase (se 2 (by rfl) ⟨395028, by rfl⟩ : syracuseStep 1053409 = 790057) (by norm_num)
theorem B1774325 : Blo 932582 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B2102021 : Blo 932582 2102021 := bbase (se 4 (by rfl) ⟨197064, by rfl⟩ : syracuseStep 2102021 = 394129) (by norm_num)
theorem B1053445 : Blo 932582 1053445 := bbase (se 4 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 1053445 = 197521) (by norm_num)
theorem B3150629 : Blo 932582 3150629 := bbase (se 4 (by rfl) ⟨295371, by rfl⟩ : syracuseStep 3150629 = 590743) (by norm_num)
theorem B1577765 : Blo 932582 1577765 := bbase (se 4 (by rfl) ⟨147915, by rfl⟩ : syracuseStep 1577765 = 295831) (by norm_num)
theorem B1053481 : Blo 932582 1053481 := bbase (se 2 (by rfl) ⟨395055, by rfl⟩ : syracuseStep 1053481 = 790111) (by norm_num)
theorem B2102093 : Blo 932582 2102093 := bbase (se 3 (by rfl) ⟨394142, by rfl⟩ : syracuseStep 2102093 = 788285) (by norm_num)
theorem B1053517 : Blo 932582 1053517 := bbase (se 3 (by rfl) ⟨197534, by rfl⟩ : syracuseStep 1053517 = 395069) (by norm_num)
theorem B1053553 : Blo 932582 1053553 := bbase (se 2 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 1053553 = 790165) (by norm_num)
theorem B1184645 : Blo 932582 1184645 := bbase (se 4 (by rfl) ⟨111060, by rfl⟩ : syracuseStep 1184645 = 222121) (by norm_num)
theorem B1774477 : Blo 932582 1774477 := bbase (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) (by norm_num)
theorem B2102165 : Blo 932582 2102165 := bbase (se 6 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 2102165 = 98539) (by norm_num)
theorem B1053589 : Blo 932582 1053589 := bbase (se 6 (by rfl) ⟨24693, by rfl⟩ : syracuseStep 1053589 = 49387) (by norm_num)
theorem B1577893 : Blo 932582 1577893 := bbase (se 4 (by rfl) ⟨147927, by rfl⟩ : syracuseStep 1577893 = 295855) (by norm_num)
theorem B1053625 : Blo 932582 1053625 := bbase (se 2 (by rfl) ⟨395109, by rfl⟩ : syracuseStep 1053625 = 790219) (by norm_num)
theorem B2364349 : Blo 932582 2364349 := bbase (se 3 (by rfl) ⟨443315, by rfl⟩ : syracuseStep 2364349 = 886631) (by norm_num)
theorem B1184701 : Blo 932582 1184701 := bbase (se 3 (by rfl) ⟨222131, by rfl⟩ : syracuseStep 1184701 = 444263) (by norm_num)
theorem B2102237 : Blo 932582 2102237 := bbase (se 3 (by rfl) ⟨394169, by rfl⟩ : syracuseStep 2102237 = 788339) (by norm_num)
theorem B2659301 : Blo 932582 2659301 := bbase (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) (by norm_num)
theorem B1577981 : Blo 932582 1577981 := bbase (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) (by norm_num)
theorem B1184797 : Blo 932582 1184797 := bbase (se 3 (by rfl) ⟨222149, by rfl⟩ : syracuseStep 1184797 = 444299) (by norm_num)
theorem B2102309 : Blo 932582 2102309 := bbase (se 4 (by rfl) ⟨197091, by rfl⟩ : syracuseStep 2102309 = 394183) (by norm_num)
theorem B2364461 : Blo 932582 2364461 := bbase (se 3 (by rfl) ⟨443336, by rfl⟩ : syracuseStep 2364461 = 886673) (by norm_num)
theorem B2102381 : Blo 932582 2102381 := bbase (se 3 (by rfl) ⟨394196, by rfl⟩ : syracuseStep 2102381 = 788393) (by norm_num)
theorem B1578109 : Blo 932582 1578109 := bbase (se 3 (by rfl) ⟨295895, by rfl⟩ : syracuseStep 1578109 = 591791) (by norm_num)
theorem B2135173 : Blo 932582 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B2102453 : Blo 932582 2102453 := bbase (se 5 (by rfl) ⟨98552, by rfl⟩ : syracuseStep 2102453 = 197105) (by norm_num)
theorem B1774781 : Blo 932582 1774781 := bbase (se 3 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 1774781 = 665543) (by norm_num)
theorem B1184969 : Blo 932582 1184969 := bbase (se 2 (by rfl) ⟨444363, by rfl⟩ : syracuseStep 1184969 = 888727) (by norm_num)
theorem B3151061 : Blo 932582 3151061 := bbase (se 7 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 3151061 = 73853) (by norm_num)
theorem B1578197 : Blo 932582 1578197 := bbase (se 7 (by rfl) ⟨18494, by rfl⟩ : syracuseStep 1578197 = 36989) (by norm_num)
theorem B4560101 : Blo 932582 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B2364653 : Blo 932582 2364653 := bbase (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) (by norm_num)
theorem B2102525 : Blo 932582 2102525 := bbase (se 3 (by rfl) ⟨394223, by rfl⟩ : syracuseStep 2102525 = 788447) (by norm_num)
theorem B1185025 : Blo 932582 1185025 := bbase (se 2 (by rfl) ⟨444384, by rfl⟩ : syracuseStep 1185025 = 888769) (by norm_num)
theorem B2102597 : Blo 932582 2102597 := bbase (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) (by norm_num)
theorem B1578325 : Blo 932582 1578325 := bbase (se 14 (by rfl) ⟨144, by rfl⟩ : syracuseStep 1578325 = 289) (by norm_num)
theorem B1185121 : Blo 932582 1185121 := bbase (se 2 (by rfl) ⟨444420, by rfl⟩ : syracuseStep 1185121 = 888841) (by norm_num)
theorem B2102669 : Blo 932582 2102669 := bbase (se 3 (by rfl) ⟨394250, by rfl⟩ : syracuseStep 2102669 = 788501) (by norm_num)
theorem B1578413 : Blo 932582 1578413 := bbase (se 3 (by rfl) ⟨295952, by rfl⟩ : syracuseStep 1578413 = 591905) (by norm_num)
theorem B2102741 : Blo 932582 2102741 := bbase (se 7 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 2102741 = 49283) (by norm_num)
theorem B1185293 : Blo 932582 1185293 := bbase (se 3 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 1185293 = 444485) (by norm_num)
theorem B2102813 : Blo 932582 2102813 := bbase (se 3 (by rfl) ⟨394277, by rfl⟩ : syracuseStep 2102813 = 788555) (by norm_num)
theorem B1578541 : Blo 932582 1578541 := bbase (se 3 (by rfl) ⟨295976, by rfl⟩ : syracuseStep 1578541 = 591953) (by norm_num)
theorem B2364997 : Blo 932582 2364997 := bbase (se 4 (by rfl) ⟨221718, by rfl⟩ : syracuseStep 2364997 = 443437) (by norm_num)
theorem B1185349 : Blo 932582 1185349 := bbase (se 4 (by rfl) ⟨111126, by rfl⟩ : syracuseStep 1185349 = 222253) (by norm_num)
theorem B2102885 : Blo 932582 2102885 := bbase (se 4 (by rfl) ⟨197145, by rfl⟩ : syracuseStep 2102885 = 394291) (by norm_num)
theorem B3151493 : Blo 932582 3151493 := bbase (se 4 (by rfl) ⟨295452, by rfl⟩ : syracuseStep 3151493 = 590905) (by norm_num)
theorem B1578629 : Blo 932582 1578629 := bbase (se 4 (by rfl) ⟨147996, by rfl⟩ : syracuseStep 1578629 = 295993) (by norm_num)
theorem B2102957 : Blo 932582 2102957 := bbase (se 3 (by rfl) ⟨394304, by rfl⟩ : syracuseStep 2102957 = 788609) (by norm_num)
theorem B4724405 : Blo 932582 4724405 := bbase (se 5 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 4724405 = 442913) (by norm_num)
theorem B2365109 : Blo 932582 2365109 := bbase (se 5 (by rfl) ⟨110864, by rfl⟩ : syracuseStep 2365109 = 221729) (by norm_num)
theorem B2660053 : Blo 932582 2660053 := bbase (se 7 (by rfl) ⟨31172, by rfl⟩ : syracuseStep 2660053 = 62345) (by norm_num)
theorem B1349357 : Blo 932582 1349357 := bbase (se 3 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 1349357 = 506009) (by norm_num)
theorem B2103029 : Blo 932582 2103029 := bbase (se 5 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 2103029 = 197159) (by norm_num)
theorem B1578757 : Blo 932582 1578757 := bbase (se 4 (by rfl) ⟨148008, by rfl⟩ : syracuseStep 1578757 = 296017) (by norm_num)
theorem B2103101 : Blo 932582 2103101 := bbase (se 3 (by rfl) ⟨394331, by rfl⟩ : syracuseStep 2103101 = 788663) (by norm_num)
theorem B1578845 : Blo 932582 1578845 := bbase (se 3 (by rfl) ⟨296033, by rfl⟩ : syracuseStep 1578845 = 592067) (by norm_num)
theorem B2365301 : Blo 932582 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B2103173 : Blo 932582 2103173 := bbase (se 4 (by rfl) ⟨197172, by rfl⟩ : syracuseStep 2103173 = 394345) (by norm_num)
theorem B1775533 : Blo 932582 1775533 := bbase (se 3 (by rfl) ⟨332912, by rfl⟩ : syracuseStep 1775533 = 665825) (by norm_num)
theorem B2103245 : Blo 932582 2103245 := bbase (se 3 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 2103245 = 788717) (by norm_num)
theorem B1578973 : Blo 932582 1578973 := bbase (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) (by norm_num)
theorem B2103317 : Blo 932582 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B3151925 : Blo 932582 3151925 := bbase (se 5 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 3151925 = 295493) (by norm_num)
theorem B1579061 : Blo 932582 1579061 := bbase (se 5 (by rfl) ⟨74018, by rfl⟩ : syracuseStep 1579061 = 148037) (by norm_num)
theorem B1775677 : Blo 932582 1775677 := bbase (se 3 (by rfl) ⟨332939, by rfl⟩ : syracuseStep 1775677 = 665879) (by norm_num)
theorem B4790341 : Blo 932582 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B2103389 : Blo 932582 2103389 := bbase (se 3 (by rfl) ⟨394385, by rfl⟩ : syracuseStep 2103389 = 788771) (by norm_num)
theorem B2103461 : Blo 932582 2103461 := bbase (se 4 (by rfl) ⟨197199, by rfl⟩ : syracuseStep 2103461 = 394399) (by norm_num)
theorem B1579189 : Blo 932582 1579189 := bbase (se 5 (by rfl) ⟨74024, by rfl⟩ : syracuseStep 1579189 = 148049) (by norm_num)
theorem B2365645 : Blo 932582 2365645 := bbase (se 3 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 2365645 = 887117) (by norm_num)
theorem B1775837 : Blo 932582 1775837 := bbase (se 3 (by rfl) ⟨332969, by rfl⟩ : syracuseStep 1775837 = 665939) (by norm_num)
theorem B2103533 : Blo 932582 2103533 := bbase (se 3 (by rfl) ⟨394412, by rfl⟩ : syracuseStep 2103533 = 788825) (by norm_num)
theorem B1579277 : Blo 932582 1579277 := bbase (se 3 (by rfl) ⟨296114, by rfl⟩ : syracuseStep 1579277 = 592229) (by norm_num)
theorem B2103605 : Blo 932582 2103605 := bbase (se 5 (by rfl) ⟨98606, by rfl⟩ : syracuseStep 2103605 = 197213) (by norm_num)
theorem B2365757 : Blo 932582 2365757 := bbase (se 3 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 2365757 = 887159) (by norm_num)
theorem B1775981 : Blo 932582 1775981 := bbase (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) (by norm_num)
theorem B2103677 : Blo 932582 2103677 := bbase (se 3 (by rfl) ⟨394439, by rfl⟩ : syracuseStep 2103677 = 788879) (by norm_num)
theorem B3545477 : Blo 932582 3545477 := bbase (se 4 (by rfl) ⟨332388, by rfl⟩ : syracuseStep 3545477 = 664777) (by norm_num)
theorem B1579405 : Blo 932582 1579405 := bbase (se 3 (by rfl) ⟨296138, by rfl⟩ : syracuseStep 1579405 = 592277) (by norm_num)
theorem B2988485 : Blo 932582 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B2103749 : Blo 932582 2103749 := bbase (se 4 (by rfl) ⟨197226, by rfl⟩ : syracuseStep 2103749 = 394453) (by norm_num)
theorem B1710533 : Blo 932582 1710533 := bbase (se 4 (by rfl) ⟨160362, by rfl⟩ : syracuseStep 1710533 = 320725) (by norm_num)
theorem B3152357 : Blo 932582 3152357 := bbase (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) (by norm_num)
theorem B1579493 : Blo 932582 1579493 := bbase (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) (by norm_num)
theorem B2365949 : Blo 932582 2365949 := bbase (se 3 (by rfl) ⟨443615, by rfl⟩ : syracuseStep 2365949 = 887231) (by norm_num)
theorem B2103821 : Blo 932582 2103821 := bbase (se 3 (by rfl) ⟨394466, by rfl⟩ : syracuseStep 2103821 = 788933) (by norm_num)
theorem B2103893 : Blo 932582 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B1579621 : Blo 932582 1579621 := bbase (se 4 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 1579621 = 296179) (by norm_num)
theorem B1120889 : Blo 932582 1120889 := bbase (se 2 (by rfl) ⟨420333, by rfl⟩ : syracuseStep 1120889 = 840667) (by norm_num)
theorem B1776269 : Blo 932582 1776269 := bbase (se 3 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 1776269 = 666101) (by norm_num)
theorem B2103965 : Blo 932582 2103965 := bbase (se 3 (by rfl) ⟨394493, by rfl⟩ : syracuseStep 2103965 = 788987) (by norm_num)
theorem B3545765 : Blo 932582 3545765 := bbase (se 4 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 3545765 = 664831) (by norm_num)
theorem B1579709 : Blo 932582 1579709 := bbase (se 3 (by rfl) ⟨296195, by rfl⟩ : syracuseStep 1579709 = 592391) (by norm_num)
theorem B2104037 : Blo 932582 2104037 := bbase (se 4 (by rfl) ⟨197253, by rfl⟩ : syracuseStep 2104037 = 394507) (by norm_num)
theorem B1776421 : Blo 932582 1776421 := bbase (se 4 (by rfl) ⟨166539, by rfl⟩ : syracuseStep 1776421 = 333079) (by norm_num)
theorem B2104109 : Blo 932582 2104109 := bbase (se 3 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 2104109 = 789041) (by norm_num)
theorem B1579837 : Blo 932582 1579837 := bbase (se 3 (by rfl) ⟨296219, by rfl⟩ : syracuseStep 1579837 = 592439) (by norm_num)
theorem B2366293 : Blo 932582 2366293 := bbase (se 9 (by rfl) ⟨6932, by rfl⟩ : syracuseStep 2366293 = 13865) (by norm_num)
theorem B2104181 : Blo 932582 2104181 := bbase (se 5 (by rfl) ⟨98633, by rfl⟩ : syracuseStep 2104181 = 197267) (by norm_num)
theorem B3152789 : Blo 932582 3152789 := bbase (se 6 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 3152789 = 147787) (by norm_num)
theorem B1579925 : Blo 932582 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B1121197 : Blo 932582 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B2104253 : Blo 932582 2104253 := bbase (se 3 (by rfl) ⟨394547, by rfl⟩ : syracuseStep 2104253 = 789095) (by norm_num)
theorem B1350589 : Blo 932582 1350589 := bbase (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) (by norm_num)
theorem B4725701 : Blo 932582 4725701 := bbase (se 4 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 4725701 = 886069) (by norm_num)
theorem B2366405 : Blo 932582 2366405 := bbase (se 4 (by rfl) ⟨221850, by rfl⟩ : syracuseStep 2366405 = 443701) (by norm_num)
theorem B2104325 : Blo 932582 2104325 := bbase (se 4 (by rfl) ⟨197280, by rfl⟩ : syracuseStep 2104325 = 394561) (by norm_num)
theorem B1121297 : Blo 932582 1121297 := bbase (se 2 (by rfl) ⟨420486, by rfl⟩ : syracuseStep 1121297 = 840973) (by norm_num)
theorem B1580053 : Blo 932582 1580053 := bbase (se 6 (by rfl) ⟨37032, by rfl⟩ : syracuseStep 1580053 = 74065) (by norm_num)
theorem B3513413 : Blo 932582 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B2104397 : Blo 932582 2104397 := bbase (se 3 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 2104397 = 789149) (by norm_num)
theorem B1776725 : Blo 932582 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B1580141 : Blo 932582 1580141 := bbase (se 3 (by rfl) ⟨296276, by rfl⟩ : syracuseStep 1580141 = 592553) (by norm_num)
theorem B3939445 : Blo 932582 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B2366597 : Blo 932582 2366597 := bbase (se 4 (by rfl) ⟨221868, by rfl⟩ : syracuseStep 2366597 = 443737) (by norm_num)
theorem B2694293 : Blo 932582 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2104469 : Blo 932582 2104469 := bbase (se 6 (by rfl) ⟨49323, by rfl⟩ : syracuseStep 2104469 = 98647) (by norm_num)
theorem B2104541 : Blo 932582 2104541 := bbase (se 3 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 2104541 = 789203) (by norm_num)
theorem B1580269 : Blo 932582 1580269 := bbase (se 3 (by rfl) ⟨296300, by rfl⟩ : syracuseStep 1580269 = 592601) (by norm_num)
theorem B2530565 : Blo 932582 2530565 := bbase (se 4 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 2530565 = 474481) (by norm_num)
theorem B2104613 : Blo 932582 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B3153221 : Blo 932582 3153221 := bbase (se 4 (by rfl) ⟨295614, by rfl⟩ : syracuseStep 3153221 = 591229) (by norm_num)
theorem B1580357 : Blo 932582 1580357 := bbase (se 4 (by rfl) ⟨148158, by rfl⟩ : syracuseStep 1580357 = 296317) (by norm_num)
theorem B2104685 : Blo 932582 2104685 := bbase (se 3 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 2104685 = 789257) (by norm_num)
theorem B1351037 : Blo 932582 1351037 := bbase (se 3 (by rfl) ⟨253319, by rfl⟩ : syracuseStep 1351037 = 506639) (by norm_num)
theorem B1121701 : Blo 932582 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B2104757 : Blo 932582 2104757 := bbase (se 5 (by rfl) ⟨98660, by rfl⟩ : syracuseStep 2104757 = 197321) (by norm_num)
theorem B2366941 : Blo 932582 2366941 := bbase (se 3 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 2366941 = 887603) (by norm_num)
theorem B2104829 : Blo 932582 2104829 := bbase (se 3 (by rfl) ⟨394655, by rfl⟩ : syracuseStep 2104829 = 789311) (by norm_num)
theorem B2104901 : Blo 932582 2104901 := bbase (se 4 (by rfl) ⟨197334, by rfl⟩ : syracuseStep 2104901 = 394669) (by norm_num)
theorem B2367053 : Blo 932582 2367053 := bbase (se 3 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 2367053 = 887645) (by norm_num)
theorem B2104973 : Blo 932582 2104973 := bbase (se 3 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 2104973 = 789365) (by norm_num)
theorem B2530997 : Blo 932582 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B2399933 : Blo 932582 2399933 := bbase (se 3 (by rfl) ⟨449987, by rfl⟩ : syracuseStep 2399933 = 899975) (by norm_num)
theorem B2105045 : Blo 932582 2105045 := bbase (se 7 (by rfl) ⟨24668, by rfl⟩ : syracuseStep 2105045 = 49337) (by norm_num)
theorem B3153653 : Blo 932582 3153653 := bbase (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) (by norm_num)
theorem B2367245 : Blo 932582 2367245 := bbase (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) (by norm_num)
theorem B2105117 : Blo 932582 2105117 := bbase (se 3 (by rfl) ⟨394709, by rfl⟩ : syracuseStep 2105117 = 789419) (by norm_num)
theorem B1122085 : Blo 932582 1122085 := bbase (se 4 (by rfl) ⟨105195, by rfl⟩ : syracuseStep 1122085 = 210391) (by norm_num)
theorem B3546949 : Blo 932582 3546949 := bbase (se 4 (by rfl) ⟨332526, by rfl⟩ : syracuseStep 3546949 = 665053) (by norm_num)
theorem B1777477 : Blo 932582 1777477 := bbase (se 4 (by rfl) ⟨166638, by rfl⟩ : syracuseStep 1777477 = 333277) (by norm_num)
theorem B2105189 : Blo 932582 2105189 := bbase (se 4 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 2105189 = 394723) (by norm_num)
theorem B2105261 : Blo 932582 2105261 := bbase (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) (by norm_num)
theorem B1777621 : Blo 932582 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B2105333 : Blo 932582 2105333 := bbase (se 5 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 2105333 = 197375) (by norm_num)
theorem B2105405 : Blo 932582 2105405 := bbase (se 3 (by rfl) ⟨394763, by rfl⟩ : syracuseStep 2105405 = 789527) (by norm_num)
theorem B2367589 : Blo 932582 2367589 := bbase (se 4 (by rfl) ⟨221961, by rfl⟩ : syracuseStep 2367589 = 443923) (by norm_num)
theorem B3547253 : Blo 932582 3547253 := bbase (se 5 (by rfl) ⟨166277, by rfl⟩ : syracuseStep 3547253 = 332555) (by norm_num)
theorem B1777781 : Blo 932582 1777781 := bbase (se 5 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 1777781 = 166667) (by norm_num)
theorem B2105477 : Blo 932582 2105477 := bbase (se 4 (by rfl) ⟨197388, by rfl⟩ : syracuseStep 2105477 = 394777) (by norm_num)
theorem B3154085 : Blo 932582 3154085 := bbase (se 4 (by rfl) ⟨295695, by rfl⟩ : syracuseStep 3154085 = 591391) (by norm_num)
theorem B2105549 : Blo 932582 2105549 := bbase (se 3 (by rfl) ⟨394790, by rfl⟩ : syracuseStep 2105549 = 789581) (by norm_num)
theorem B4726997 : Blo 932582 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B2367701 : Blo 932582 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B3416309 : Blo 932582 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B1777925 : Blo 932582 1777925 := bbase (se 4 (by rfl) ⟨166680, by rfl⟩ : syracuseStep 1777925 = 333361) (by norm_num)
theorem B2105621 : Blo 932582 2105621 := bbase (se 6 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 2105621 = 98701) (by norm_num)
theorem B2695493 : Blo 932582 2695493 := bbase (se 4 (by rfl) ⟨252702, by rfl⟩ : syracuseStep 2695493 = 505405) (by norm_num)
theorem B12165461 : Blo 932582 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B2105693 : Blo 932582 2105693 := bbase (se 3 (by rfl) ⟨394817, by rfl⟩ : syracuseStep 2105693 = 789635) (by norm_num)
theorem B2367893 : Blo 932582 2367893 := bbase (se 6 (by rfl) ⟨55497, by rfl⟩ : syracuseStep 2367893 = 110995) (by norm_num)
theorem B2105765 : Blo 932582 2105765 := bbase (se 4 (by rfl) ⟨197415, by rfl⟩ : syracuseStep 2105765 = 394831) (by norm_num)
theorem B2105837 : Blo 932582 2105837 := bbase (se 3 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 2105837 = 789689) (by norm_num)
theorem B2662901 : Blo 932582 2662901 := bbase (se 5 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 2662901 = 249647) (by norm_num)
theorem B2105909 : Blo 932582 2105909 := bbase (se 5 (by rfl) ⟨98714, by rfl⟩ : syracuseStep 2105909 = 197429) (by norm_num)
theorem B2990677 : Blo 932582 2990677 := bbase (se 8 (by rfl) ⟨17523, by rfl⟩ : syracuseStep 2990677 = 35047) (by norm_num)
theorem B3154517 : Blo 932582 3154517 := bbase (se 8 (by rfl) ⟨18483, by rfl⟩ : syracuseStep 3154517 = 36967) (by norm_num)
theorem B1122941 : Blo 932582 1122941 := bbase (se 3 (by rfl) ⟨210551, by rfl⟩ : syracuseStep 1122941 = 421103) (by norm_num)
theorem B2105981 : Blo 932582 2105981 := bbase (se 3 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 2105981 = 789743) (by norm_num)
theorem B2106053 : Blo 932582 2106053 := bbase (se 4 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 2106053 = 394885) (by norm_num)
theorem B2368237 : Blo 932582 2368237 := bbase (se 3 (by rfl) ⟨444044, by rfl⟩ : syracuseStep 2368237 = 888089) (by norm_num)
theorem B4498181 : Blo 932582 4498181 := bbase (se 4 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 4498181 = 843409) (by norm_num)
theorem B2106125 : Blo 932582 2106125 := bbase (se 3 (by rfl) ⟨394898, by rfl⟩ : syracuseStep 2106125 = 789797) (by norm_num)
theorem B2106197 : Blo 932582 2106197 := bbase (se 9 (by rfl) ⟨6170, by rfl⟩ : syracuseStep 2106197 = 12341) (by norm_num)
theorem B2368349 : Blo 932582 2368349 := bbase (se 3 (by rfl) ⟨444065, by rfl⟩ : syracuseStep 2368349 = 888131) (by norm_num)
theorem B2106269 : Blo 932582 2106269 := bbase (se 3 (by rfl) ⟨394925, by rfl⟩ : syracuseStep 2106269 = 789851) (by norm_num)
theorem B1123249 : Blo 932582 1123249 := bbase (se 2 (by rfl) ⟨421218, by rfl⟩ : syracuseStep 1123249 = 842437) (by norm_num)
theorem B2106341 : Blo 932582 2106341 := bbase (se 4 (by rfl) ⟨197469, by rfl⟩ : syracuseStep 2106341 = 394939) (by norm_num)
theorem B3154949 : Blo 932582 3154949 := bbase (se 4 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 3154949 = 591553) (by norm_num)
theorem B2368541 : Blo 932582 2368541 := bbase (se 3 (by rfl) ⟨444101, by rfl⟩ : syracuseStep 2368541 = 888203) (by norm_num)
theorem B2106413 : Blo 932582 2106413 := bbase (se 3 (by rfl) ⟨394952, by rfl⟩ : syracuseStep 2106413 = 789905) (by norm_num)
theorem B2106485 : Blo 932582 2106485 := bbase (se 5 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 2106485 = 197483) (by norm_num)
theorem B1123465 : Blo 932582 1123465 := bbase (se 2 (by rfl) ⟨421299, by rfl⟩ : syracuseStep 1123465 = 842599) (by norm_num)
theorem B13477013 : Blo 932582 13477013 := bbase (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) (by norm_num)
theorem B2106557 : Blo 932582 2106557 := bbase (se 3 (by rfl) ⟨394979, by rfl⟩ : syracuseStep 2106557 = 789959) (by norm_num)
theorem B2106629 : Blo 932582 2106629 := bbase (se 4 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 2106629 = 394993) (by norm_num)
theorem B2106701 : Blo 932582 2106701 := bbase (se 3 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 2106701 = 790013) (by norm_num)
theorem B2368885 : Blo 932582 2368885 := bbase (se 5 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 2368885 = 222083) (by norm_num)
theorem B2991509 : Blo 932582 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B2106773 : Blo 932582 2106773 := bbase (se 6 (by rfl) ⟨49377, by rfl⟩ : syracuseStep 2106773 = 98755) (by norm_num)
theorem B4105637 : Blo 932582 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B3155381 : Blo 932582 3155381 := bbase (se 5 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 3155381 = 295817) (by norm_num)
theorem B2106845 : Blo 932582 2106845 := bbase (se 3 (by rfl) ⟨395033, by rfl⟩ : syracuseStep 2106845 = 790067) (by norm_num)
theorem B4728293 : Blo 932582 4728293 := bbase (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) (by norm_num)
theorem B2368997 : Blo 932582 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B2106917 : Blo 932582 2106917 := bbase (se 4 (by rfl) ⟨197523, by rfl⟩ : syracuseStep 2106917 = 395047) (by norm_num)
theorem B2106989 : Blo 932582 2106989 := bbase (se 3 (by rfl) ⟨395060, by rfl⟩ : syracuseStep 2106989 = 790121) (by norm_num)
theorem B2664085 : Blo 932582 2664085 := bbase (se 6 (by rfl) ⟨62439, by rfl⟩ : syracuseStep 2664085 = 124879) (by norm_num)
theorem B2369189 : Blo 932582 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B2107061 : Blo 932582 2107061 := bbase (se 5 (by rfl) ⟨98768, by rfl⟩ : syracuseStep 2107061 = 197537) (by norm_num)
theorem B7186133 : Blo 932582 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B1124065 : Blo 932582 1124065 := bbase (se 2 (by rfl) ⟨421524, by rfl⟩ : syracuseStep 1124065 = 843049) (by norm_num)
theorem B2107133 : Blo 932582 2107133 := bbase (se 3 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 2107133 = 790175) (by norm_num)
theorem B2664245 : Blo 932582 2664245 := bbase (se 5 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 2664245 = 249773) (by norm_num)
theorem B2107205 : Blo 932582 2107205 := bbase (se 4 (by rfl) ⟨197550, by rfl⟩ : syracuseStep 2107205 = 395101) (by norm_num)
theorem B3155813 : Blo 932582 3155813 := bbase (se 4 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 3155813 = 591715) (by norm_num)
theorem B2107277 : Blo 932582 2107277 := bbase (se 3 (by rfl) ⟨395114, by rfl⟩ : syracuseStep 2107277 = 790229) (by norm_num)
theorem B2369533 : Blo 932582 2369533 := bbase (se 3 (by rfl) ⟨444287, by rfl⟩ : syracuseStep 2369533 = 888575) (by norm_num)
theorem B2664485 : Blo 932582 2664485 := bbase (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) (by norm_num)
theorem B13674581 : Blo 932582 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B2369645 : Blo 932582 2369645 := bbase (se 3 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 2369645 = 888617) (by norm_num)
theorem B7088309 : Blo 932582 7088309 := bbase (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) (by norm_num)
theorem B3549365 : Blo 932582 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B2664677 : Blo 932582 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B3156245 : Blo 932582 3156245 := bbase (se 6 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 3156245 = 147949) (by norm_num)
theorem B2369837 : Blo 932582 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B3549653 : Blo 932582 3549653 := bbase (se 7 (by rfl) ⟨41597, by rfl⟩ : syracuseStep 3549653 = 83195) (by norm_num)
theorem B2370181 : Blo 932582 2370181 := bbase (se 4 (by rfl) ⟨222204, by rfl⟩ : syracuseStep 2370181 = 444409) (by norm_num)
theorem B3156677 : Blo 932582 3156677 := bbase (se 4 (by rfl) ⟨295938, by rfl⟩ : syracuseStep 3156677 = 591877) (by norm_num)
theorem B4729589 : Blo 932582 4729589 := bbase (se 5 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 4729589 = 443399) (by norm_num)
theorem B2370293 : Blo 932582 2370293 := bbase (se 5 (by rfl) ⟨111107, by rfl⟩ : syracuseStep 2370293 = 222215) (by norm_num)
theorem B2370485 : Blo 932582 2370485 := bbase (se 5 (by rfl) ⟨111116, by rfl⟩ : syracuseStep 2370485 = 222233) (by norm_num)
theorem B1518605 : Blo 932582 1518605 := bbase (se 3 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 1518605 = 569477) (by norm_num)
theorem B3157109 : Blo 932582 3157109 := bbase (se 5 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 3157109 = 295979) (by norm_num)
theorem B2665669 : Blo 932582 2665669 := bbase (se 4 (by rfl) ⟨249906, by rfl⟩ : syracuseStep 2665669 = 499813) (by norm_num)
theorem B2993381 : Blo 932582 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B1420573 : Blo 932582 1420573 := bbase (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) (by norm_num)
theorem B1682869 : Blo 932582 1682869 := bbase (se 5 (by rfl) ⟨78884, by rfl⟩ : syracuseStep 1682869 = 157769) (by norm_num)
theorem B17935829 : Blo 932582 17935829 := bbase (se 7 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 17935829 = 420371) (by norm_num)
theorem B3157541 : Blo 932582 3157541 := bbase (se 4 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 3157541 = 592039) (by norm_num)
theorem B1683013 : Blo 932582 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B1617509 : Blo 932582 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B3550837 : Blo 932582 3550837 := bbase (se 5 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 3550837 = 332891) (by norm_num)
theorem B1683085 : Blo 932582 1683085 := bbase (se 3 (by rfl) ⟨315578, by rfl⟩ : syracuseStep 1683085 = 631157) (by norm_num)
theorem B3551141 : Blo 932582 3551141 := bbase (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) (by norm_num)
theorem B3157973 : Blo 932582 3157973 := bbase (se 7 (by rfl) ⟨37007, by rfl⟩ : syracuseStep 3157973 = 74015) (by norm_num)
theorem B4730885 : Blo 932582 4730885 := bbase (se 4 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 4730885 = 887041) (by norm_num)
theorem B1421501 : Blo 932582 1421501 := bbase (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) (by norm_num)
theorem B5058773 : Blo 932582 5058773 := bbase (se 7 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 5058773 = 118565) (by norm_num)
theorem B2666773 : Blo 932582 2666773 := bbase (se 6 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 2666773 = 125005) (by norm_num)
theorem B3158405 : Blo 932582 3158405 := bbase (se 4 (by rfl) ⟨296100, by rfl⟩ : syracuseStep 3158405 = 592201) (by norm_num)
theorem B2240941 : Blo 932582 2240941 := bbase (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) (by norm_num)
theorem B2241037 : Blo 932582 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B5976661 : Blo 932582 5976661 := bbase (se 8 (by rfl) ⟨35019, by rfl⟩ : syracuseStep 5976661 = 70039) (by norm_num)
theorem B996025 : Blo 932582 996025 := bbase (se 2 (by rfl) ⟨373509, by rfl⟩ : syracuseStep 996025 = 747019) (by norm_num)
theorem B996085 : Blo 932582 996085 := bbase (se 5 (by rfl) ⟨46691, by rfl⟩ : syracuseStep 996085 = 93383) (by norm_num)
theorem B3158837 : Blo 932582 3158837 := bbase (se 5 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 3158837 = 296141) (by norm_num)
theorem B1422245 : Blo 932582 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B1684397 : Blo 932582 1684397 := bbase (se 3 (by rfl) ⟨315824, by rfl⟩ : syracuseStep 1684397 = 631649) (by norm_num)
theorem B2241557 : Blo 932582 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B996401 : Blo 932582 996401 := bbase (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) (by norm_num)
theorem B1684685 : Blo 932582 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B3159269 : Blo 932582 3159269 := bbase (se 4 (by rfl) ⟨296181, by rfl⟩ : syracuseStep 3159269 = 592363) (by norm_num)
theorem B4732181 : Blo 932582 4732181 := bbase (se 6 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 4732181 = 221821) (by norm_num)
theorem B1684909 : Blo 932582 1684909 := bbase (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) (by norm_num)
theorem B996845 : Blo 932582 996845 := bbase (se 3 (by rfl) ⟨186908, by rfl⟩ : syracuseStep 996845 = 373817) (by norm_num)
theorem B1684973 : Blo 932582 1684973 := bbase (se 3 (by rfl) ⟨315932, by rfl⟩ : syracuseStep 1684973 = 631865) (by norm_num)
theorem B2242085 : Blo 932582 2242085 := bbase (se 4 (by rfl) ⟨210195, by rfl⟩ : syracuseStep 2242085 = 420391) (by norm_num)
theorem B996905 : Blo 932582 996905 := bbase (se 2 (by rfl) ⟨373839, by rfl⟩ : syracuseStep 996905 = 747679) (by norm_num)
theorem B5322293 : Blo 932582 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B3159701 : Blo 932582 3159701 := bbase (se 6 (by rfl) ⟨74055, by rfl⟩ : syracuseStep 3159701 = 148111) (by norm_num)
theorem B997033 : Blo 932582 997033 := bbase (se 2 (by rfl) ⟨373887, by rfl⟩ : syracuseStep 997033 = 747775) (by norm_num)
theorem B2242325 : Blo 932582 2242325 := bbase (se 6 (by rfl) ⟨52554, by rfl⟩ : syracuseStep 2242325 = 105109) (by norm_num)
theorem B1423229 : Blo 932582 1423229 := bbase (se 3 (by rfl) ⟨266855, by rfl⟩ : syracuseStep 1423229 = 533711) (by norm_num)
theorem B2996149 : Blo 932582 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B3553253 : Blo 932582 3553253 := bbase (se 4 (by rfl) ⟨333117, by rfl⟩ : syracuseStep 3553253 = 666235) (by norm_num)
theorem B3160133 : Blo 932582 3160133 := bbase (se 4 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 3160133 = 592525) (by norm_num)
theorem B997477 : Blo 932582 997477 := bbase (se 4 (by rfl) ⟨93513, by rfl⟩ : syracuseStep 997477 = 187027) (by norm_num)
theorem B3782789 : Blo 932582 3782789 := bbase (se 4 (by rfl) ⟨354636, by rfl⟩ : syracuseStep 3782789 = 709273) (by norm_num)
theorem B997597 : Blo 932582 997597 := bbase (se 3 (by rfl) ⟨187049, by rfl⟩ : syracuseStep 997597 = 374099) (by norm_num)
theorem B3553541 : Blo 932582 3553541 := bbase (se 4 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 3553541 = 666289) (by norm_num)
theorem B1423813 : Blo 932582 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B997849 : Blo 932582 997849 := bbase (se 2 (by rfl) ⟨374193, by rfl⟩ : syracuseStep 997849 = 748387) (by norm_num)
theorem B997853 : Blo 932582 997853 := bbase (se 3 (by rfl) ⟨187097, by rfl⟩ : syracuseStep 997853 = 374195) (by norm_num)
theorem B3160565 : Blo 932582 3160565 := bbase (se 5 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 3160565 = 296303) (by norm_num)
theorem B4733477 : Blo 932582 4733477 := bbase (se 4 (by rfl) ⟨443763, by rfl⟩ : syracuseStep 4733477 = 887527) (by norm_num)
theorem B2702261 : Blo 932582 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B998417 : Blo 932582 998417 := bbase (se 2 (by rfl) ⟨374406, by rfl⟩ : syracuseStep 998417 = 748813) (by norm_num)
theorem B998605 : Blo 932582 998605 := bbase (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) (by norm_num)
theorem B7585109 : Blo 932582 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B6733205 : Blo 932582 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B3554725 : Blo 932582 3554725 := bbase (se 4 (by rfl) ⟨333255, by rfl⟩ : syracuseStep 3554725 = 666511) (by norm_num)
theorem B2244037 : Blo 932582 2244037 := bbase (se 4 (by rfl) ⟨210378, by rfl⟩ : syracuseStep 2244037 = 420757) (by norm_num)
theorem B24592085 : Blo 932582 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B3555029 : Blo 932582 3555029 := bbase (se 7 (by rfl) ⟨41660, by rfl⟩ : syracuseStep 3555029 = 83321) (by norm_num)
theorem B4734773 : Blo 932582 4734773 := bbase (se 5 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 4734773 = 443885) (by norm_num)
theorem B1064773 : Blo 932582 1064773 := bbase (se 4 (by rfl) ⟨99822, by rfl⟩ : syracuseStep 1064773 = 199645) (by norm_num)
theorem B999425 : Blo 932582 999425 := bbase (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) (by norm_num)
theorem B6406229 : Blo 932582 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B13648213 : Blo 932582 13648213 := bbase (se 10 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 13648213 = 39985) (by norm_num)
theorem B999869 : Blo 932582 999869 := bbase (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) (by norm_num)
theorem B1819093 : Blo 932582 1819093 := bbase (se 7 (by rfl) ⟨21317, by rfl⟩ : syracuseStep 1819093 = 42635) (by norm_num)
theorem B6406613 : Blo 932582 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B5980661 : Blo 932582 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B3785221 : Blo 932582 3785221 := bbase (se 4 (by rfl) ⟨354864, by rfl⟩ : syracuseStep 3785221 = 709729) (by norm_num)
theorem B3195413 : Blo 932582 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B1000117 : Blo 932582 1000117 := bbase (se 5 (by rfl) ⟨46880, by rfl⟩ : syracuseStep 1000117 = 93761) (by norm_num)
theorem B2999045 : Blo 932582 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B1065761 : Blo 932582 1065761 := bbase (se 2 (by rfl) ⟨399660, by rfl⟩ : syracuseStep 1065761 = 799321) (by norm_num)
theorem B1262389 : Blo 932582 1262389 := bbase (se 5 (by rfl) ⟨59174, by rfl⟩ : syracuseStep 1262389 = 118349) (by norm_num)
theorem B2245477 : Blo 932582 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B1328005 : Blo 932582 1328005 := bbase (se 4 (by rfl) ⟨124500, by rfl⟩ : syracuseStep 1328005 = 249001) (by norm_num)
theorem B14599061 : Blo 932582 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B1262557 : Blo 932582 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1065953 : Blo 932582 1065953 := bbase (se 2 (by rfl) ⟨399732, by rfl⟩ : syracuseStep 1065953 = 799465) (by norm_num)
theorem B4736069 : Blo 932582 4736069 := bbase (se 4 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 4736069 = 888013) (by norm_num)
theorem B8996021 : Blo 932582 8996021 := bbase (se 5 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 8996021 = 843377) (by norm_num)
theorem B1328341 : Blo 932582 1328341 := bbase (se 7 (by rfl) ⟨15566, by rfl⟩ : syracuseStep 1328341 = 31133) (by norm_num)
theorem B1197421 : Blo 932582 1197421 := bbase (se 3 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 1197421 = 449033) (by norm_num)
theorem B1328557 : Blo 932582 1328557 := bbase (se 3 (by rfl) ⟨249104, by rfl⟩ : syracuseStep 1328557 = 498209) (by norm_num)
theorem B2246093 : Blo 932582 2246093 := bbase (se 3 (by rfl) ⟨421142, by rfl⟩ : syracuseStep 2246093 = 842285) (by norm_num)
theorem B2737781 : Blo 932582 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B2246285 : Blo 932582 2246285 := bbase (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) (by norm_num)
theorem B7096085 : Blo 932582 7096085 := bbase (se 6 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 7096085 = 332629) (by norm_num)
theorem B1328933 : Blo 932582 1328933 := bbase (se 4 (by rfl) ⟨124587, by rfl⟩ : syracuseStep 1328933 = 249175) (by norm_num)
theorem B1066829 : Blo 932582 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B1066889 : Blo 932582 1066889 := bbase (se 2 (by rfl) ⟨400083, by rfl⟩ : syracuseStep 1066889 = 800167) (by norm_num)
theorem B2246573 : Blo 932582 2246573 := bbase (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) (by norm_num)
theorem B1263773 : Blo 932582 1263773 := bbase (se 3 (by rfl) ⟨236957, by rfl⟩ : syracuseStep 1263773 = 473915) (by norm_num)
theorem B1067185 : Blo 932582 1067185 := bbase (se 2 (by rfl) ⟨400194, by rfl⟩ : syracuseStep 1067185 = 800389) (by norm_num)
theorem B4737365 : Blo 932582 4737365 := bbase (se 10 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 4737365 = 13879) (by norm_num)
theorem B1067413 : Blo 932582 1067413 := bbase (se 6 (by rfl) ⟨25017, by rfl⟩ : syracuseStep 1067413 = 50035) (by norm_num)
theorem B6736405 : Blo 932582 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B1330357 : Blo 932582 1330357 := bbase (se 5 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 1330357 = 124721) (by norm_num)
theorem B2837701 : Blo 932582 2837701 := bbase (se 4 (by rfl) ⟨266034, by rfl⟩ : syracuseStep 2837701 = 532069) (by norm_num)
theorem B2837749 : Blo 932582 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B13454869 : Blo 932582 13454869 := bbase (se 6 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 13454869 = 630697) (by norm_num)
theorem B4738661 : Blo 932582 4738661 := bbase (se 4 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 4738661 = 888499) (by norm_num)
theorem B3985109 : Blo 932582 3985109 := bbase (se 7 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 3985109 = 93401) (by norm_num)
theorem B1330949 : Blo 932582 1330949 := bbase (se 4 (by rfl) ⟨124776, by rfl⟩ : syracuseStep 1330949 = 249553) (by norm_num)
theorem B1331029 : Blo 932582 1331029 := bbase (se 9 (by rfl) ⟨3899, by rfl⟩ : syracuseStep 1331029 = 7799) (by norm_num)
theorem B2248573 : Blo 932582 2248573 := bbase (se 3 (by rfl) ⟨421607, by rfl⟩ : syracuseStep 2248573 = 843215) (by norm_num)
theorem B1200029 : Blo 932582 1200029 := bbase (se 3 (by rfl) ⟨225005, by rfl⟩ : syracuseStep 1200029 = 450011) (by norm_num)
theorem B1331149 : Blo 932582 1331149 := bbase (se 3 (by rfl) ⟨249590, by rfl⟩ : syracuseStep 1331149 = 499181) (by norm_num)
theorem B1495037 : Blo 932582 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1331245 : Blo 932582 1331245 := bbase (se 3 (by rfl) ⟨249608, by rfl⟩ : syracuseStep 1331245 = 499217) (by norm_num)
theorem B1200377 : Blo 932582 1200377 := bbase (se 2 (by rfl) ⟨450141, by rfl⟩ : syracuseStep 1200377 = 900283) (by norm_num)
theorem B1495493 : Blo 932582 1495493 := bbase (se 4 (by rfl) ⟨140202, by rfl⟩ : syracuseStep 1495493 = 280405) (by norm_num)
theorem B1331741 : Blo 932582 1331741 := bbase (se 3 (by rfl) ⟨249701, by rfl⟩ : syracuseStep 1331741 = 499403) (by norm_num)
theorem B3330629 : Blo 932582 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B8966837 : Blo 932582 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B3986117 : Blo 932582 3986117 := bbase (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) (by norm_num)
theorem B1921781 : Blo 932582 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B4739957 : Blo 932582 4739957 := bbase (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) (by norm_num)
theorem B1332293 : Blo 932582 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B2249957 : Blo 932582 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B1496485 : Blo 932582 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B5330357 : Blo 932582 5330357 := bbase (se 5 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 5330357 = 499721) (by norm_num)
theorem B3364325 : Blo 932582 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B2053837 : Blo 932582 2053837 := bbase (se 3 (by rfl) ⟨385094, by rfl⟩ : syracuseStep 2053837 = 770189) (by norm_num)
theorem B1333045 : Blo 932582 1333045 := bbase (se 5 (by rfl) ⟨62486, by rfl⟩ : syracuseStep 1333045 = 124973) (by norm_num)
theorem B1497133 : Blo 932582 1497133 := bbase (se 3 (by rfl) ⟨280712, by rfl⟩ : syracuseStep 1497133 = 561425) (by norm_num)
theorem B1398893 : Blo 932582 1398893 := bbase (se 3 (by rfl) ⟨262292, by rfl⟩ : syracuseStep 1398893 = 524585) (by norm_num)
theorem B1398917 : Blo 932582 1398917 := bbase (se 4 (by rfl) ⟨131148, by rfl⟩ : syracuseStep 1398917 = 262297) (by norm_num)
theorem B4741253 : Blo 932582 4741253 := bbase (se 4 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 4741253 = 888985) (by norm_num)
theorem B1398941 : Blo 932582 1398941 := bbase (se 3 (by rfl) ⟨262301, by rfl⟩ : syracuseStep 1398941 = 524603) (by norm_num)
theorem B1398965 : Blo 932582 1398965 := bbase (se 5 (by rfl) ⟨65576, by rfl⟩ : syracuseStep 1398965 = 131153) (by norm_num)
theorem B1398989 : Blo 932582 1398989 := bbase (se 3 (by rfl) ⟨262310, by rfl⟩ : syracuseStep 1398989 = 524621) (by norm_num)
theorem B1399013 : Blo 932582 1399013 := bbase (se 4 (by rfl) ⟨131157, by rfl⟩ : syracuseStep 1399013 = 262315) (by norm_num)
theorem B1399037 : Blo 932582 1399037 := bbase (se 3 (by rfl) ⟨262319, by rfl⟩ : syracuseStep 1399037 = 524639) (by norm_num)
theorem B1399061 : Blo 932582 1399061 := bbase (se 6 (by rfl) ⟨32790, by rfl⟩ : syracuseStep 1399061 = 65581) (by norm_num)
theorem B1399085 : Blo 932582 1399085 := bbase (se 3 (by rfl) ⟨262328, by rfl⟩ : syracuseStep 1399085 = 524657) (by norm_num)
theorem B1399109 : Blo 932582 1399109 := bbase (se 4 (by rfl) ⟨131166, by rfl⟩ : syracuseStep 1399109 = 262333) (by norm_num)
theorem B1399133 : Blo 932582 1399133 := bbase (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) (by norm_num)
theorem B1399157 : Blo 932582 1399157 := bbase (se 5 (by rfl) ⟨65585, by rfl⟩ : syracuseStep 1399157 = 131171) (by norm_num)
theorem B1399181 : Blo 932582 1399181 := bbase (se 3 (by rfl) ⟨262346, by rfl⟩ : syracuseStep 1399181 = 524693) (by norm_num)
theorem B5986709 : Blo 932582 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B1399205 : Blo 932582 1399205 := bbase (se 4 (by rfl) ⟨131175, by rfl⟩ : syracuseStep 1399205 = 262351) (by norm_num)
theorem B3987893 : Blo 932582 3987893 := bbase (se 5 (by rfl) ⟨186932, by rfl⟩ : syracuseStep 3987893 = 373865) (by norm_num)
theorem B1399229 : Blo 932582 1399229 := bbase (se 3 (by rfl) ⟨262355, by rfl⟩ : syracuseStep 1399229 = 524711) (by norm_num)
theorem B1399253 : Blo 932582 1399253 := bbase (se 7 (by rfl) ⟨16397, by rfl⟩ : syracuseStep 1399253 = 32795) (by norm_num)
theorem B3365333 : Blo 932582 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B1399277 : Blo 932582 1399277 := bbase (se 3 (by rfl) ⟨262364, by rfl⟩ : syracuseStep 1399277 = 524729) (by norm_num)
theorem B1399301 : Blo 932582 1399301 := bbase (se 4 (by rfl) ⟨131184, by rfl⟩ : syracuseStep 1399301 = 262369) (by norm_num)
theorem B1399325 : Blo 932582 1399325 := bbase (se 3 (by rfl) ⟨262373, by rfl⟩ : syracuseStep 1399325 = 524747) (by norm_num)
theorem B1399349 : Blo 932582 1399349 := bbase (se 5 (by rfl) ⟨65594, by rfl⟩ : syracuseStep 1399349 = 131189) (by norm_num)
theorem B1399373 : Blo 932582 1399373 := bbase (se 3 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 1399373 = 524765) (by norm_num)
theorem B5331541 : Blo 932582 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B1399397 : Blo 932582 1399397 := bbase (se 4 (by rfl) ⟨131193, by rfl⟩ : syracuseStep 1399397 = 262387) (by norm_num)
theorem B1399421 : Blo 932582 1399421 := bbase (se 3 (by rfl) ⟨262391, by rfl⟩ : syracuseStep 1399421 = 524783) (by norm_num)
theorem B1399445 : Blo 932582 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B1399469 : Blo 932582 1399469 := bbase (se 3 (by rfl) ⟨262400, by rfl⟩ : syracuseStep 1399469 = 524801) (by norm_num)
theorem B1399493 : Blo 932582 1399493 := bbase (se 4 (by rfl) ⟨131202, by rfl⟩ : syracuseStep 1399493 = 262405) (by norm_num)
theorem B1399517 : Blo 932582 1399517 := bbase (se 3 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 1399517 = 524819) (by norm_num)
theorem B1596125 : Blo 932582 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B1399541 : Blo 932582 1399541 := bbase (se 5 (by rfl) ⟨65603, by rfl⟩ : syracuseStep 1399541 = 131207) (by norm_num)
theorem B1399565 : Blo 932582 1399565 := bbase (se 3 (by rfl) ⟨262418, by rfl⟩ : syracuseStep 1399565 = 524837) (by norm_num)
theorem B1399589 : Blo 932582 1399589 := bbase (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) (by norm_num)
theorem B1399613 : Blo 932582 1399613 := bbase (se 3 (by rfl) ⟨262427, by rfl⟩ : syracuseStep 1399613 = 524855) (by norm_num)
theorem B1399637 : Blo 932582 1399637 := bbase (se 9 (by rfl) ⟨4100, by rfl⟩ : syracuseStep 1399637 = 8201) (by norm_num)
theorem B2841445 : Blo 932582 2841445 := bbase (se 4 (by rfl) ⟨266385, by rfl⟩ : syracuseStep 2841445 = 532771) (by norm_num)
theorem B1399661 : Blo 932582 1399661 := bbase (se 3 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 1399661 = 524873) (by norm_num)
theorem B1399685 : Blo 932582 1399685 := bbase (se 4 (by rfl) ⟨131220, by rfl⟩ : syracuseStep 1399685 = 262441) (by norm_num)
theorem B1399709 : Blo 932582 1399709 := bbase (se 3 (by rfl) ⟨262445, by rfl⟩ : syracuseStep 1399709 = 524891) (by norm_num)
theorem B1399733 : Blo 932582 1399733 := bbase (se 5 (by rfl) ⟨65612, by rfl⟩ : syracuseStep 1399733 = 131225) (by norm_num)
theorem B1399757 : Blo 932582 1399757 := bbase (se 3 (by rfl) ⟨262454, by rfl⟩ : syracuseStep 1399757 = 524909) (by norm_num)
theorem B1498061 : Blo 932582 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B1399781 : Blo 932582 1399781 := bbase (se 4 (by rfl) ⟨131229, by rfl⟩ : syracuseStep 1399781 = 262459) (by norm_num)
theorem B1399805 : Blo 932582 1399805 := bbase (se 3 (by rfl) ⟨262463, by rfl⟩ : syracuseStep 1399805 = 524927) (by norm_num)
theorem B1399829 : Blo 932582 1399829 := bbase (se 6 (by rfl) ⟨32808, by rfl⟩ : syracuseStep 1399829 = 65617) (by norm_num)
theorem B1399853 : Blo 932582 1399853 := bbase (se 3 (by rfl) ⟨262472, by rfl⟩ : syracuseStep 1399853 = 524945) (by norm_num)
theorem B1399877 : Blo 932582 1399877 := bbase (se 4 (by rfl) ⟨131238, by rfl⟩ : syracuseStep 1399877 = 262477) (by norm_num)
theorem B1399901 : Blo 932582 1399901 := bbase (se 3 (by rfl) ⟨262481, by rfl⟩ : syracuseStep 1399901 = 524963) (by norm_num)
theorem B1399925 : Blo 932582 1399925 := bbase (se 5 (by rfl) ⟨65621, by rfl⟩ : syracuseStep 1399925 = 131243) (by norm_num)
theorem B1399949 : Blo 932582 1399949 := bbase (se 3 (by rfl) ⟨262490, by rfl⟩ : syracuseStep 1399949 = 524981) (by norm_num)
theorem B1399973 : Blo 932582 1399973 := bbase (se 4 (by rfl) ⟨131247, by rfl⟩ : syracuseStep 1399973 = 262495) (by norm_num)
theorem B1399997 : Blo 932582 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1891525 : Blo 932582 1891525 := bbase (se 4 (by rfl) ⟨177330, by rfl⟩ : syracuseStep 1891525 = 354661) (by norm_num)
theorem B1400021 : Blo 932582 1400021 := bbase (se 7 (by rfl) ⟨16406, by rfl⟩ : syracuseStep 1400021 = 32813) (by norm_num)
theorem B1400045 : Blo 932582 1400045 := bbase (se 3 (by rfl) ⟨262508, by rfl⟩ : syracuseStep 1400045 = 525017) (by norm_num)
theorem B1400069 : Blo 932582 1400069 := bbase (se 4 (by rfl) ⟨131256, by rfl⟩ : syracuseStep 1400069 = 262513) (by norm_num)
theorem B1400093 : Blo 932582 1400093 := bbase (se 3 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 1400093 = 525035) (by norm_num)
theorem B1400117 : Blo 932582 1400117 := bbase (se 5 (by rfl) ⟨65630, by rfl⟩ : syracuseStep 1400117 = 131261) (by norm_num)
theorem B1400141 : Blo 932582 1400141 := bbase (se 3 (by rfl) ⟨262526, by rfl⟩ : syracuseStep 1400141 = 525053) (by norm_num)
theorem B1400165 : Blo 932582 1400165 := bbase (se 4 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 1400165 = 262531) (by norm_num)
theorem B1400189 : Blo 932582 1400189 := bbase (se 3 (by rfl) ⟨262535, by rfl⟩ : syracuseStep 1400189 = 525071) (by norm_num)
theorem B1400213 : Blo 932582 1400213 := bbase (se 6 (by rfl) ⟨32817, by rfl⟩ : syracuseStep 1400213 = 65635) (by norm_num)
theorem B1498517 : Blo 932582 1498517 := bbase (se 6 (by rfl) ⟨35121, by rfl⟩ : syracuseStep 1498517 = 70243) (by norm_num)
theorem B1400237 : Blo 932582 1400237 := bbase (se 3 (by rfl) ⟨262544, by rfl⟩ : syracuseStep 1400237 = 525089) (by norm_num)
theorem B1400261 : Blo 932582 1400261 := bbase (se 4 (by rfl) ⟨131274, by rfl⟩ : syracuseStep 1400261 = 262549) (by norm_num)
theorem B1400285 : Blo 932582 1400285 := bbase (se 3 (by rfl) ⟨262553, by rfl⟩ : syracuseStep 1400285 = 525107) (by norm_num)
theorem B1400309 : Blo 932582 1400309 := bbase (se 5 (by rfl) ⟨65639, by rfl⟩ : syracuseStep 1400309 = 131279) (by norm_num)
theorem B1400333 : Blo 932582 1400333 := bbase (se 3 (by rfl) ⟨262562, by rfl⟩ : syracuseStep 1400333 = 525125) (by norm_num)
theorem B1400357 : Blo 932582 1400357 := bbase (se 4 (by rfl) ⟨131283, by rfl⟩ : syracuseStep 1400357 = 262567) (by norm_num)
theorem B1400381 : Blo 932582 1400381 := bbase (se 3 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 1400381 = 525143) (by norm_num)
theorem B1400405 : Blo 932582 1400405 := bbase (se 8 (by rfl) ⟨8205, by rfl⟩ : syracuseStep 1400405 = 16411) (by norm_num)
theorem B4316773 : Blo 932582 4316773 := bbase (se 4 (by rfl) ⟨404697, by rfl⟩ : syracuseStep 4316773 = 809395) (by norm_num)
theorem B1400429 : Blo 932582 1400429 := bbase (se 3 (by rfl) ⟨262580, by rfl⟩ : syracuseStep 1400429 = 525161) (by norm_num)
theorem B1400453 : Blo 932582 1400453 := bbase (se 4 (by rfl) ⟨131292, by rfl⟩ : syracuseStep 1400453 = 262585) (by norm_num)
theorem B1400477 : Blo 932582 1400477 := bbase (se 3 (by rfl) ⟨262589, by rfl⟩ : syracuseStep 1400477 = 525179) (by norm_num)
theorem B1400501 : Blo 932582 1400501 := bbase (se 5 (by rfl) ⟨65648, by rfl⟩ : syracuseStep 1400501 = 131297) (by norm_num)
theorem B1400525 : Blo 932582 1400525 := bbase (se 3 (by rfl) ⟨262598, by rfl⟩ : syracuseStep 1400525 = 525197) (by norm_num)
theorem B1400549 : Blo 932582 1400549 := bbase (se 4 (by rfl) ⟨131301, by rfl⟩ : syracuseStep 1400549 = 262603) (by norm_num)
theorem B1400573 : Blo 932582 1400573 := bbase (se 3 (by rfl) ⟨262607, by rfl⟩ : syracuseStep 1400573 = 525215) (by norm_num)
theorem B1400597 : Blo 932582 1400597 := bbase (se 6 (by rfl) ⟨32826, by rfl⟩ : syracuseStep 1400597 = 65653) (by norm_num)
theorem B1400621 : Blo 932582 1400621 := bbase (se 3 (by rfl) ⟨262616, by rfl⟩ : syracuseStep 1400621 = 525233) (by norm_num)
theorem B1400645 : Blo 932582 1400645 := bbase (se 4 (by rfl) ⟨131310, by rfl⟩ : syracuseStep 1400645 = 262621) (by norm_num)
theorem B1400669 : Blo 932582 1400669 := bbase (se 3 (by rfl) ⟨262625, by rfl⟩ : syracuseStep 1400669 = 525251) (by norm_num)
theorem B1400693 : Blo 932582 1400693 := bbase (se 5 (by rfl) ⟨65657, by rfl⟩ : syracuseStep 1400693 = 131315) (by norm_num)
theorem B1400717 : Blo 932582 1400717 := bbase (se 3 (by rfl) ⟨262634, by rfl⟩ : syracuseStep 1400717 = 525269) (by norm_num)
theorem B1400741 : Blo 932582 1400741 := bbase (se 4 (by rfl) ⟨131319, by rfl⟩ : syracuseStep 1400741 = 262639) (by norm_num)
theorem B1400765 : Blo 932582 1400765 := bbase (se 3 (by rfl) ⟨262643, by rfl⟩ : syracuseStep 1400765 = 525287) (by norm_num)
theorem B1400789 : Blo 932582 1400789 := bbase (se 7 (by rfl) ⟨16415, by rfl⟩ : syracuseStep 1400789 = 32831) (by norm_num)
theorem B1400813 : Blo 932582 1400813 := bbase (se 3 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 1400813 = 525305) (by norm_num)
theorem B1400837 : Blo 932582 1400837 := bbase (se 4 (by rfl) ⟨131328, by rfl⟩ : syracuseStep 1400837 = 262657) (by norm_num)
theorem B1400861 : Blo 932582 1400861 := bbase (se 3 (by rfl) ⟨262661, by rfl⟩ : syracuseStep 1400861 = 525323) (by norm_num)
theorem B1597493 : Blo 932582 1597493 := bbase (se 5 (by rfl) ⟨74882, by rfl⟩ : syracuseStep 1597493 = 149765) (by norm_num)
theorem B1400885 : Blo 932582 1400885 := bbase (se 5 (by rfl) ⟨65666, by rfl⟩ : syracuseStep 1400885 = 131333) (by norm_num)
theorem B1400909 : Blo 932582 1400909 := bbase (se 3 (by rfl) ⟨262670, by rfl⟩ : syracuseStep 1400909 = 525341) (by norm_num)
theorem B1400933 : Blo 932582 1400933 := bbase (se 4 (by rfl) ⟨131337, by rfl⟩ : syracuseStep 1400933 = 262675) (by norm_num)
theorem B1400957 : Blo 932582 1400957 := bbase (se 3 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 1400957 = 525359) (by norm_num)
theorem B1400981 : Blo 932582 1400981 := bbase (se 6 (by rfl) ⟨32835, by rfl⟩ : syracuseStep 1400981 = 65671) (by norm_num)
theorem B1401005 : Blo 932582 1401005 := bbase (se 3 (by rfl) ⟨262688, by rfl⟩ : syracuseStep 1401005 = 525377) (by norm_num)
theorem B1401029 : Blo 932582 1401029 := bbase (se 4 (by rfl) ⟨131346, by rfl⟩ : syracuseStep 1401029 = 262693) (by norm_num)
theorem B1401053 : Blo 932582 1401053 := bbase (se 3 (by rfl) ⟨262697, by rfl⟩ : syracuseStep 1401053 = 525395) (by norm_num)
theorem B1401077 : Blo 932582 1401077 := bbase (se 5 (by rfl) ⟨65675, by rfl⟩ : syracuseStep 1401077 = 131351) (by norm_num)
theorem B1401101 : Blo 932582 1401101 := bbase (se 3 (by rfl) ⟨262706, by rfl⟩ : syracuseStep 1401101 = 525413) (by norm_num)
theorem B1401125 : Blo 932582 1401125 := bbase (se 4 (by rfl) ⟨131355, by rfl⟩ : syracuseStep 1401125 = 262711) (by norm_num)
theorem B1401149 : Blo 932582 1401149 := bbase (se 3 (by rfl) ⟨262715, by rfl⟩ : syracuseStep 1401149 = 525431) (by norm_num)
theorem B1401173 : Blo 932582 1401173 := bbase (se 10 (by rfl) ⟨2052, by rfl⟩ : syracuseStep 1401173 = 4105) (by norm_num)
theorem B1401197 : Blo 932582 1401197 := bbase (se 3 (by rfl) ⟨262724, by rfl⟩ : syracuseStep 1401197 = 525449) (by norm_num)
theorem B1401221 : Blo 932582 1401221 := bbase (se 4 (by rfl) ⟨131364, by rfl⟩ : syracuseStep 1401221 = 262729) (by norm_num)
theorem B1401245 : Blo 932582 1401245 := bbase (se 3 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 1401245 = 525467) (by norm_num)
theorem B1401269 : Blo 932582 1401269 := bbase (se 5 (by rfl) ⟨65684, by rfl⟩ : syracuseStep 1401269 = 131369) (by norm_num)
theorem B3203525 : Blo 932582 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B1401293 : Blo 932582 1401293 := bbase (se 3 (by rfl) ⟨262742, by rfl⟩ : syracuseStep 1401293 = 525485) (by norm_num)
theorem B1401317 : Blo 932582 1401317 := bbase (se 4 (by rfl) ⟨131373, by rfl⟩ : syracuseStep 1401317 = 262747) (by norm_num)
theorem B1401341 : Blo 932582 1401341 := bbase (se 3 (by rfl) ⟨262751, by rfl⟩ : syracuseStep 1401341 = 525503) (by norm_num)
theorem B1401365 : Blo 932582 1401365 := bbase (se 6 (by rfl) ⟨32844, by rfl⟩ : syracuseStep 1401365 = 65689) (by norm_num)
theorem B10641941 : Blo 932582 10641941 := bbase (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) (by norm_num)
theorem B5333525 : Blo 932582 5333525 := bbase (se 6 (by rfl) ⟨125004, by rfl⟩ : syracuseStep 5333525 = 250009) (by norm_num)
theorem B4481573 : Blo 932582 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B1401389 : Blo 932582 1401389 := bbase (se 3 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 1401389 = 525521) (by norm_num)
theorem B1401413 : Blo 932582 1401413 := bbase (se 4 (by rfl) ⟨131382, by rfl⟩ : syracuseStep 1401413 = 262765) (by norm_num)
theorem B1401437 : Blo 932582 1401437 := bbase (se 3 (by rfl) ⟨262769, by rfl⟩ : syracuseStep 1401437 = 525539) (by norm_num)
theorem B1401461 : Blo 932582 1401461 := bbase (se 5 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 1401461 = 131387) (by norm_num)
theorem B1401485 : Blo 932582 1401485 := bbase (se 3 (by rfl) ⟨262778, by rfl⟩ : syracuseStep 1401485 = 525557) (by norm_num)
theorem B15131285 : Blo 932582 15131285 := bbase (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) (by norm_num)
theorem B1401509 : Blo 932582 1401509 := bbase (se 4 (by rfl) ⟨131391, by rfl⟩ : syracuseStep 1401509 = 262783) (by norm_num)
theorem B1401533 : Blo 932582 1401533 := bbase (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) (by norm_num)
theorem B1139393 : Blo 932582 1139393 := bbase (se 2 (by rfl) ⟨427272, by rfl⟩ : syracuseStep 1139393 = 854545) (by norm_num)
theorem B1401557 : Blo 932582 1401557 := bbase (se 7 (by rfl) ⟨16424, by rfl⟩ : syracuseStep 1401557 = 32849) (by norm_num)
theorem B1401581 : Blo 932582 1401581 := bbase (se 3 (by rfl) ⟨262796, by rfl⟩ : syracuseStep 1401581 = 525593) (by norm_num)
theorem B1401605 : Blo 932582 1401605 := bbase (se 4 (by rfl) ⟨131400, by rfl⟩ : syracuseStep 1401605 = 262801) (by norm_num)
theorem B1401629 : Blo 932582 1401629 := bbase (se 3 (by rfl) ⟨262805, by rfl⟩ : syracuseStep 1401629 = 525611) (by norm_num)
theorem B1499933 : Blo 932582 1499933 := bbase (se 3 (by rfl) ⟨281237, by rfl⟩ : syracuseStep 1499933 = 562475) (by norm_num)
theorem B1401653 : Blo 932582 1401653 := bbase (se 5 (by rfl) ⟨65702, by rfl⟩ : syracuseStep 1401653 = 131405) (by norm_num)
theorem B1401677 : Blo 932582 1401677 := bbase (se 3 (by rfl) ⟨262814, by rfl⟩ : syracuseStep 1401677 = 525629) (by norm_num)
theorem B1794901 : Blo 932582 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B1401701 : Blo 932582 1401701 := bbase (se 4 (by rfl) ⟨131409, by rfl⟩ : syracuseStep 1401701 = 262819) (by norm_num)
theorem B1401725 : Blo 932582 1401725 := bbase (se 3 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 1401725 = 525647) (by norm_num)
theorem B3367813 : Blo 932582 3367813 := bbase (se 4 (by rfl) ⟨315732, by rfl⟩ : syracuseStep 3367813 = 631465) (by norm_num)
theorem B1401749 : Blo 932582 1401749 := bbase (se 6 (by rfl) ⟨32853, by rfl⟩ : syracuseStep 1401749 = 65707) (by norm_num)
theorem B1401773 : Blo 932582 1401773 := bbase (se 3 (by rfl) ⟨262832, by rfl⟩ : syracuseStep 1401773 = 525665) (by norm_num)
theorem B1401797 : Blo 932582 1401797 := bbase (se 4 (by rfl) ⟨131418, by rfl⟩ : syracuseStep 1401797 = 262837) (by norm_num)
theorem B1401821 : Blo 932582 1401821 := bbase (se 3 (by rfl) ⟨262841, by rfl⟩ : syracuseStep 1401821 = 525683) (by norm_num)
theorem B1401845 : Blo 932582 1401845 := bbase (se 5 (by rfl) ⟨65711, by rfl⟩ : syracuseStep 1401845 = 131423) (by norm_num)
theorem B1500157 : Blo 932582 1500157 := bbase (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) (by norm_num)
theorem B1401869 : Blo 932582 1401869 := bbase (se 3 (by rfl) ⟨262850, by rfl⟩ : syracuseStep 1401869 = 525701) (by norm_num)
theorem B1139729 : Blo 932582 1139729 := bbase (se 2 (by rfl) ⟨427398, by rfl⟩ : syracuseStep 1139729 = 854797) (by norm_num)
theorem B3367973 : Blo 932582 3367973 := bbase (se 4 (by rfl) ⟨315747, by rfl⟩ : syracuseStep 3367973 = 631495) (by norm_num)
theorem B1401893 : Blo 932582 1401893 := bbase (se 4 (by rfl) ⟨131427, by rfl⟩ : syracuseStep 1401893 = 262855) (by norm_num)
theorem B1401917 : Blo 932582 1401917 := bbase (se 3 (by rfl) ⟨262859, by rfl⟩ : syracuseStep 1401917 = 525719) (by norm_num)
theorem B1401941 : Blo 932582 1401941 := bbase (se 8 (by rfl) ⟨8214, by rfl⟩ : syracuseStep 1401941 = 16429) (by norm_num)
theorem B1401965 : Blo 932582 1401965 := bbase (se 3 (by rfl) ⟨262868, by rfl⟩ : syracuseStep 1401965 = 525737) (by norm_num)
theorem B1401989 : Blo 932582 1401989 := bbase (se 4 (by rfl) ⟨131436, by rfl⟩ : syracuseStep 1401989 = 262873) (by norm_num)
theorem B1402013 : Blo 932582 1402013 := bbase (se 3 (by rfl) ⟨262877, by rfl⟩ : syracuseStep 1402013 = 525755) (by norm_num)
theorem B1402037 : Blo 932582 1402037 := bbase (se 5 (by rfl) ⟨65720, by rfl⟩ : syracuseStep 1402037 = 131441) (by norm_num)
theorem B1402061 : Blo 932582 1402061 := bbase (se 3 (by rfl) ⟨262886, by rfl⟩ : syracuseStep 1402061 = 525773) (by norm_num)
theorem B1402085 : Blo 932582 1402085 := bbase (se 4 (by rfl) ⟨131445, by rfl⟩ : syracuseStep 1402085 = 262891) (by norm_num)
theorem B1402109 : Blo 932582 1402109 := bbase (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) (by norm_num)
theorem B1402133 : Blo 932582 1402133 := bbase (se 6 (by rfl) ⟨32862, by rfl⟩ : syracuseStep 1402133 = 65725) (by norm_num)
theorem B1991965 : Blo 932582 1991965 := bbase (se 3 (by rfl) ⟨373493, by rfl⟩ : syracuseStep 1991965 = 746987) (by norm_num)
theorem B1402157 : Blo 932582 1402157 := bbase (se 3 (by rfl) ⟨262904, by rfl⟩ : syracuseStep 1402157 = 525809) (by norm_num)
theorem B1402181 : Blo 932582 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1402205 : Blo 932582 1402205 := bbase (se 3 (by rfl) ⟨262913, by rfl⟩ : syracuseStep 1402205 = 525827) (by norm_num)
theorem B1402229 : Blo 932582 1402229 := bbase (se 5 (by rfl) ⟨65729, by rfl⟩ : syracuseStep 1402229 = 131459) (by norm_num)
theorem B7103861 : Blo 932582 7103861 := bbase (se 5 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 7103861 = 665987) (by norm_num)
theorem B1402253 : Blo 932582 1402253 := bbase (se 3 (by rfl) ⟨262922, by rfl⟩ : syracuseStep 1402253 = 525845) (by norm_num)
theorem B1402277 : Blo 932582 1402277 := bbase (se 4 (by rfl) ⟨131463, by rfl⟩ : syracuseStep 1402277 = 262927) (by norm_num)
theorem B1402301 : Blo 932582 1402301 := bbase (se 3 (by rfl) ⟨262931, by rfl⟩ : syracuseStep 1402301 = 525863) (by norm_num)
theorem B1402325 : Blo 932582 1402325 := bbase (se 7 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 1402325 = 32867) (by norm_num)
theorem B1402349 : Blo 932582 1402349 := bbase (se 3 (by rfl) ⟨262940, by rfl⟩ : syracuseStep 1402349 = 525881) (by norm_num)
theorem B1402373 : Blo 932582 1402373 := bbase (se 4 (by rfl) ⟨131472, by rfl⟩ : syracuseStep 1402373 = 262945) (by norm_num)
theorem B1402397 : Blo 932582 1402397 := bbase (se 3 (by rfl) ⟨262949, by rfl⟩ : syracuseStep 1402397 = 525899) (by norm_num)
theorem B1893925 : Blo 932582 1893925 := bbase (se 4 (by rfl) ⟨177555, by rfl⟩ : syracuseStep 1893925 = 355111) (by norm_num)
theorem B1402421 : Blo 932582 1402421 := bbase (se 5 (by rfl) ⟨65738, by rfl⟩ : syracuseStep 1402421 = 131477) (by norm_num)
theorem B1402445 : Blo 932582 1402445 := bbase (se 3 (by rfl) ⟨262958, by rfl⟩ : syracuseStep 1402445 = 525917) (by norm_num)
theorem B1402469 : Blo 932582 1402469 := bbase (se 4 (by rfl) ⟨131481, by rfl⟩ : syracuseStep 1402469 = 262963) (by norm_num)
theorem B1402493 : Blo 932582 1402493 := bbase (se 3 (by rfl) ⟨262967, by rfl⟩ : syracuseStep 1402493 = 525935) (by norm_num)
theorem B1402517 : Blo 932582 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B1402541 : Blo 932582 1402541 := bbase (se 3 (by rfl) ⟨262976, by rfl⟩ : syracuseStep 1402541 = 525953) (by norm_num)
theorem B1402565 : Blo 932582 1402565 := bbase (se 4 (by rfl) ⟨131490, by rfl⟩ : syracuseStep 1402565 = 262981) (by norm_num)
theorem B1402589 : Blo 932582 1402589 := bbase (se 3 (by rfl) ⟨262985, by rfl⟩ : syracuseStep 1402589 = 525971) (by norm_num)
theorem B1402613 : Blo 932582 1402613 := bbase (se 5 (by rfl) ⟨65747, by rfl⟩ : syracuseStep 1402613 = 131495) (by norm_num)
theorem B1730317 : Blo 932582 1730317 := bbase (se 3 (by rfl) ⟨324434, by rfl⟩ : syracuseStep 1730317 = 648869) (by norm_num)
theorem B1402637 : Blo 932582 1402637 := bbase (se 3 (by rfl) ⟨262994, by rfl⟩ : syracuseStep 1402637 = 525989) (by norm_num)
theorem B1402661 : Blo 932582 1402661 := bbase (se 4 (by rfl) ⟨131499, by rfl⟩ : syracuseStep 1402661 = 262999) (by norm_num)
theorem B1402685 : Blo 932582 1402685 := bbase (se 3 (by rfl) ⟨263003, by rfl⟩ : syracuseStep 1402685 = 526007) (by norm_num)
theorem B1402709 : Blo 932582 1402709 := bbase (se 9 (by rfl) ⟨4109, by rfl⟩ : syracuseStep 1402709 = 8219) (by norm_num)
theorem B1795949 : Blo 932582 1795949 := bbase (se 3 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 1795949 = 673481) (by norm_num)
theorem B1402733 : Blo 932582 1402733 := bbase (se 3 (by rfl) ⟨263012, by rfl⟩ : syracuseStep 1402733 = 526025) (by norm_num)
theorem B1402757 : Blo 932582 1402757 := bbase (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) (by norm_num)
theorem B1402781 : Blo 932582 1402781 := bbase (se 3 (by rfl) ⟨263021, by rfl⟩ : syracuseStep 1402781 = 526043) (by norm_num)
theorem B1402805 : Blo 932582 1402805 := bbase (se 5 (by rfl) ⟨65756, by rfl⟩ : syracuseStep 1402805 = 131513) (by norm_num)
theorem B1402829 : Blo 932582 1402829 := bbase (se 3 (by rfl) ⟨263030, by rfl⟩ : syracuseStep 1402829 = 526061) (by norm_num)
theorem B1402853 : Blo 932582 1402853 := bbase (se 4 (by rfl) ⟨131517, by rfl⟩ : syracuseStep 1402853 = 263035) (by norm_num)
theorem B1402877 : Blo 932582 1402877 := bbase (se 3 (by rfl) ⟨263039, by rfl⟩ : syracuseStep 1402877 = 526079) (by norm_num)
theorem B1402901 : Blo 932582 1402901 := bbase (se 6 (by rfl) ⟨32880, by rfl⟩ : syracuseStep 1402901 = 65761) (by norm_num)
theorem B1402925 : Blo 932582 1402925 := bbase (se 3 (by rfl) ⟨263048, by rfl⟩ : syracuseStep 1402925 = 526097) (by norm_num)
theorem B1402949 : Blo 932582 1402949 := bbase (se 4 (by rfl) ⟨131526, by rfl⟩ : syracuseStep 1402949 = 263053) (by norm_num)
theorem B1402973 : Blo 932582 1402973 := bbase (se 3 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 1402973 = 526115) (by norm_num)
theorem B1402997 : Blo 932582 1402997 := bbase (se 5 (by rfl) ⟨65765, by rfl⟩ : syracuseStep 1402997 = 131531) (by norm_num)
theorem B1403021 : Blo 932582 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B1992853 : Blo 932582 1992853 := bbase (se 6 (by rfl) ⟨46707, by rfl⟩ : syracuseStep 1992853 = 93415) (by norm_num)
theorem B1403045 : Blo 932582 1403045 := bbase (se 4 (by rfl) ⟨131535, by rfl⟩ : syracuseStep 1403045 = 263071) (by norm_num)
theorem B1403069 : Blo 932582 1403069 := bbase (se 3 (by rfl) ⟨263075, by rfl⟩ : syracuseStep 1403069 = 526151) (by norm_num)
theorem B1403093 : Blo 932582 1403093 := bbase (se 7 (by rfl) ⟨16442, by rfl⟩ : syracuseStep 1403093 = 32885) (by norm_num)
theorem B1403117 : Blo 932582 1403117 := bbase (se 3 (by rfl) ⟨263084, by rfl⟩ : syracuseStep 1403117 = 526169) (by norm_num)
theorem B1403141 : Blo 932582 1403141 := bbase (se 4 (by rfl) ⟨131544, by rfl⟩ : syracuseStep 1403141 = 263089) (by norm_num)
theorem B1403165 : Blo 932582 1403165 := bbase (se 3 (by rfl) ⟨263093, by rfl⟩ : syracuseStep 1403165 = 526187) (by norm_num)
theorem B1403189 : Blo 932582 1403189 := bbase (se 5 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 1403189 = 131549) (by norm_num)
theorem B1403213 : Blo 932582 1403213 := bbase (se 3 (by rfl) ⟨263102, by rfl⟩ : syracuseStep 1403213 = 526205) (by norm_num)
theorem B1403237 : Blo 932582 1403237 := bbase (se 4 (by rfl) ⟨131553, by rfl⟩ : syracuseStep 1403237 = 263107) (by norm_num)
theorem B1403261 : Blo 932582 1403261 := bbase (se 3 (by rfl) ⟨263111, by rfl⟩ : syracuseStep 1403261 = 526223) (by norm_num)
theorem B1403285 : Blo 932582 1403285 := bbase (se 6 (by rfl) ⟨32889, by rfl⟩ : syracuseStep 1403285 = 65779) (by norm_num)
theorem B1403309 : Blo 932582 1403309 := bbase (se 3 (by rfl) ⟨263120, by rfl⟩ : syracuseStep 1403309 = 526241) (by norm_num)
theorem B1403333 : Blo 932582 1403333 := bbase (se 4 (by rfl) ⟨131562, by rfl⟩ : syracuseStep 1403333 = 263125) (by norm_num)
theorem B1403357 : Blo 932582 1403357 := bbase (se 3 (by rfl) ⟨263129, by rfl⟩ : syracuseStep 1403357 = 526259) (by norm_num)
theorem B1010161 : Blo 932582 1010161 := bbase (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) (by norm_num)
theorem B1403381 : Blo 932582 1403381 := bbase (se 5 (by rfl) ⟨65783, by rfl⟩ : syracuseStep 1403381 = 131567) (by norm_num)
theorem B1403405 : Blo 932582 1403405 := bbase (se 3 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 1403405 = 526277) (by norm_num)
theorem B1403429 : Blo 932582 1403429 := bbase (se 4 (by rfl) ⟨131571, by rfl⟩ : syracuseStep 1403429 = 263143) (by norm_num)
theorem B1403453 : Blo 932582 1403453 := bbase (se 3 (by rfl) ⟨263147, by rfl⟩ : syracuseStep 1403453 = 526295) (by norm_num)
theorem B1403477 : Blo 932582 1403477 := bbase (se 8 (by rfl) ⟨8223, by rfl⟩ : syracuseStep 1403477 = 16447) (by norm_num)
theorem B1895005 : Blo 932582 1895005 := bbase (se 3 (by rfl) ⟨355313, by rfl⟩ : syracuseStep 1895005 = 710627) (by norm_num)
theorem B3992165 : Blo 932582 3992165 := bbase (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) (by norm_num)
theorem B1403501 : Blo 932582 1403501 := bbase (se 3 (by rfl) ⟨263156, by rfl⟩ : syracuseStep 1403501 = 526313) (by norm_num)
theorem B1993349 : Blo 932582 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B1403525 : Blo 932582 1403525 := bbase (se 4 (by rfl) ⟨131580, by rfl⟩ : syracuseStep 1403525 = 263161) (by norm_num)
theorem B1403549 : Blo 932582 1403549 := bbase (se 3 (by rfl) ⟨263165, by rfl⟩ : syracuseStep 1403549 = 526331) (by norm_num)
theorem B1403573 : Blo 932582 1403573 := bbase (se 5 (by rfl) ⟨65792, by rfl⟩ : syracuseStep 1403573 = 131585) (by norm_num)
theorem B1403597 : Blo 932582 1403597 := bbase (se 3 (by rfl) ⟨263174, by rfl⟩ : syracuseStep 1403597 = 526349) (by norm_num)
theorem B1403621 : Blo 932582 1403621 := bbase (se 4 (by rfl) ⟨131589, by rfl⟩ : syracuseStep 1403621 = 263179) (by norm_num)
theorem B1403645 : Blo 932582 1403645 := bbase (se 3 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 1403645 = 526367) (by norm_num)
theorem B1403669 : Blo 932582 1403669 := bbase (se 6 (by rfl) ⟨32898, by rfl⟩ : syracuseStep 1403669 = 65797) (by norm_num)
theorem B1403693 : Blo 932582 1403693 := bbase (se 3 (by rfl) ⟨263192, by rfl⟩ : syracuseStep 1403693 = 526385) (by norm_num)
theorem B1403717 : Blo 932582 1403717 := bbase (se 4 (by rfl) ⟨131598, by rfl⟩ : syracuseStep 1403717 = 263197) (by norm_num)
theorem B1403741 : Blo 932582 1403741 := bbase (se 3 (by rfl) ⟨263201, by rfl⟩ : syracuseStep 1403741 = 526403) (by norm_num)
theorem B1403765 : Blo 932582 1403765 := bbase (se 5 (by rfl) ⟨65801, by rfl⟩ : syracuseStep 1403765 = 131603) (by norm_num)
theorem B1403789 : Blo 932582 1403789 := bbase (se 3 (by rfl) ⟨263210, by rfl⟩ : syracuseStep 1403789 = 526421) (by norm_num)
theorem B1403813 : Blo 932582 1403813 := bbase (se 4 (by rfl) ⟨131607, by rfl⟩ : syracuseStep 1403813 = 263215) (by norm_num)
theorem B2845621 : Blo 932582 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B1403837 : Blo 932582 1403837 := bbase (se 3 (by rfl) ⟨263219, by rfl⟩ : syracuseStep 1403837 = 526439) (by norm_num)
theorem B1403861 : Blo 932582 1403861 := bbase (se 7 (by rfl) ⟨16451, by rfl⟩ : syracuseStep 1403861 = 32903) (by norm_num)
theorem B1403885 : Blo 932582 1403885 := bbase (se 3 (by rfl) ⟨263228, by rfl⟩ : syracuseStep 1403885 = 526457) (by norm_num)
theorem B1403909 : Blo 932582 1403909 := bbase (se 4 (by rfl) ⟨131616, by rfl⟩ : syracuseStep 1403909 = 263233) (by norm_num)
theorem B1403933 : Blo 932582 1403933 := bbase (se 3 (by rfl) ⟨263237, by rfl⟩ : syracuseStep 1403933 = 526475) (by norm_num)
theorem B1403957 : Blo 932582 1403957 := bbase (se 5 (by rfl) ⟨65810, by rfl⟩ : syracuseStep 1403957 = 131621) (by norm_num)
theorem B1403981 : Blo 932582 1403981 := bbase (se 3 (by rfl) ⟨263246, by rfl⟩ : syracuseStep 1403981 = 526493) (by norm_num)
theorem B1404005 : Blo 932582 1404005 := bbase (se 4 (by rfl) ⟨131625, by rfl⟩ : syracuseStep 1404005 = 263251) (by norm_num)
theorem B1404029 : Blo 932582 1404029 := bbase (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) (by norm_num)
theorem B1404053 : Blo 932582 1404053 := bbase (se 6 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 1404053 = 65815) (by norm_num)
theorem B1404077 : Blo 932582 1404077 := bbase (se 3 (by rfl) ⟨263264, by rfl⟩ : syracuseStep 1404077 = 526529) (by norm_num)
theorem B945329 : Blo 932582 945329 := bbase (se 2 (by rfl) ⟨354498, by rfl⟩ : syracuseStep 945329 = 708997) (by norm_num)
theorem B1404101 : Blo 932582 1404101 := bbase (se 4 (by rfl) ⟨131634, by rfl⟩ : syracuseStep 1404101 = 263269) (by norm_num)
theorem B945365 : Blo 932582 945365 := bbase (se 7 (by rfl) ⟨11078, by rfl⟩ : syracuseStep 945365 = 22157) (by norm_num)
theorem B11365589 : Blo 932582 11365589 := bbase (se 7 (by rfl) ⟨133190, by rfl⟩ : syracuseStep 11365589 = 266381) (by norm_num)
theorem B1404125 : Blo 932582 1404125 := bbase (se 3 (by rfl) ⟨263273, by rfl⟩ : syracuseStep 1404125 = 526547) (by norm_num)
theorem B1895653 : Blo 932582 1895653 := bbase (se 4 (by rfl) ⟨177717, by rfl⟩ : syracuseStep 1895653 = 355435) (by norm_num)
theorem B1404149 : Blo 932582 1404149 := bbase (se 5 (by rfl) ⟨65819, by rfl⟩ : syracuseStep 1404149 = 131639) (by norm_num)
theorem B1404173 : Blo 932582 1404173 := bbase (se 3 (by rfl) ⟨263282, by rfl⟩ : syracuseStep 1404173 = 526565) (by norm_num)
theorem B1404197 : Blo 932582 1404197 := bbase (se 4 (by rfl) ⟨131643, by rfl⟩ : syracuseStep 1404197 = 263287) (by norm_num)
theorem B1404221 : Blo 932582 1404221 := bbase (se 3 (by rfl) ⟨263291, by rfl⟩ : syracuseStep 1404221 = 526583) (by norm_num)
theorem B1404245 : Blo 932582 1404245 := bbase (se 11 (by rfl) ⟨1028, by rfl⟩ : syracuseStep 1404245 = 2057) (by norm_num)
theorem B1404269 : Blo 932582 1404269 := bbase (se 3 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 1404269 = 526601) (by norm_num)
theorem B1011061 : Blo 932582 1011061 := bbase (se 5 (by rfl) ⟨47393, by rfl⟩ : syracuseStep 1011061 = 94787) (by norm_num)
theorem B1404293 : Blo 932582 1404293 := bbase (se 4 (by rfl) ⟨131652, by rfl⟩ : syracuseStep 1404293 = 263305) (by norm_num)
theorem B1404317 : Blo 932582 1404317 := bbase (se 3 (by rfl) ⟨263309, by rfl⟩ : syracuseStep 1404317 = 526619) (by norm_num)
theorem B945589 : Blo 932582 945589 := bbase (se 5 (by rfl) ⟨44324, by rfl⟩ : syracuseStep 945589 = 88649) (by norm_num)
theorem B1404341 : Blo 932582 1404341 := bbase (se 5 (by rfl) ⟨65828, by rfl⟩ : syracuseStep 1404341 = 131657) (by norm_num)
theorem B1404365 : Blo 932582 1404365 := bbase (se 3 (by rfl) ⟨263318, by rfl⟩ : syracuseStep 1404365 = 526637) (by norm_num)
theorem B1404389 : Blo 932582 1404389 := bbase (se 4 (by rfl) ⟨131661, by rfl⟩ : syracuseStep 1404389 = 263323) (by norm_num)
theorem B1994237 : Blo 932582 1994237 := bbase (se 3 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 1994237 = 747839) (by norm_num)
theorem B1404413 : Blo 932582 1404413 := bbase (se 3 (by rfl) ⟨263327, by rfl⟩ : syracuseStep 1404413 = 526655) (by norm_num)
theorem B5041685 : Blo 932582 5041685 := bbase (se 6 (by rfl) ⟨118164, by rfl⟩ : syracuseStep 5041685 = 236329) (by norm_num)
theorem B1404437 : Blo 932582 1404437 := bbase (se 6 (by rfl) ⟨32916, by rfl⟩ : syracuseStep 1404437 = 65833) (by norm_num)
theorem B1404461 : Blo 932582 1404461 := bbase (se 3 (by rfl) ⟨263336, by rfl⟩ : syracuseStep 1404461 = 526673) (by norm_num)
theorem B1404485 : Blo 932582 1404485 := bbase (se 4 (by rfl) ⟨131670, by rfl⟩ : syracuseStep 1404485 = 263341) (by norm_num)
theorem B1404509 : Blo 932582 1404509 := bbase (se 3 (by rfl) ⟨263345, by rfl⟩ : syracuseStep 1404509 = 526691) (by norm_num)
theorem B1994357 : Blo 932582 1994357 := bbase (se 5 (by rfl) ⟨93485, by rfl⟩ : syracuseStep 1994357 = 186971) (by norm_num)
theorem B1404533 : Blo 932582 1404533 := bbase (se 5 (by rfl) ⟨65837, by rfl⟩ : syracuseStep 1404533 = 131675) (by norm_num)
theorem B1404557 : Blo 932582 1404557 := bbase (se 3 (by rfl) ⟨263354, by rfl⟩ : syracuseStep 1404557 = 526709) (by norm_num)
theorem B1404581 : Blo 932582 1404581 := bbase (se 4 (by rfl) ⟨131679, by rfl⟩ : syracuseStep 1404581 = 263359) (by norm_num)
theorem B1404605 : Blo 932582 1404605 := bbase (se 3 (by rfl) ⟨263363, by rfl⟩ : syracuseStep 1404605 = 526727) (by norm_num)
theorem B1404629 : Blo 932582 1404629 := bbase (se 7 (by rfl) ⟨16460, by rfl⟩ : syracuseStep 1404629 = 32921) (by norm_num)
theorem B1404653 : Blo 932582 1404653 := bbase (se 3 (by rfl) ⟨263372, by rfl⟩ : syracuseStep 1404653 = 526745) (by norm_num)
theorem B1404677 : Blo 932582 1404677 := bbase (se 4 (by rfl) ⟨131688, by rfl⟩ : syracuseStep 1404677 = 263377) (by norm_num)
theorem B1404701 : Blo 932582 1404701 := bbase (se 3 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 1404701 = 526763) (by norm_num)
theorem B1404725 : Blo 932582 1404725 := bbase (se 5 (by rfl) ⟨65846, by rfl⟩ : syracuseStep 1404725 = 131693) (by norm_num)
theorem B1404749 : Blo 932582 1404749 := bbase (se 3 (by rfl) ⟨263390, by rfl⟩ : syracuseStep 1404749 = 526781) (by norm_num)
theorem B1404773 : Blo 932582 1404773 := bbase (se 4 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 1404773 = 263395) (by norm_num)
theorem B1404797 : Blo 932582 1404797 := bbase (se 3 (by rfl) ⟨263399, by rfl⟩ : syracuseStep 1404797 = 526799) (by norm_num)
theorem B1404821 : Blo 932582 1404821 := bbase (se 6 (by rfl) ⟨32925, by rfl⟩ : syracuseStep 1404821 = 65851) (by norm_num)
theorem B1404845 : Blo 932582 1404845 := bbase (se 3 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 1404845 = 526817) (by norm_num)
theorem B1896373 : Blo 932582 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1404869 : Blo 932582 1404869 := bbase (se 4 (by rfl) ⟨131706, by rfl⟩ : syracuseStep 1404869 = 263413) (by norm_num)
theorem B5992501 : Blo 932582 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B946273 : Blo 932582 946273 := bbase (se 2 (by rfl) ⟨354852, by rfl⟩ : syracuseStep 946273 = 709705) (by norm_num)
theorem B1994989 : Blo 932582 1994989 := bbase (se 3 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 1994989 = 748121) (by norm_num)
theorem B3993941 : Blo 932582 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B3600949 : Blo 932582 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B3994181 : Blo 932582 3994181 := bbase (se 4 (by rfl) ⟨374454, by rfl⟩ : syracuseStep 3994181 = 748909) (by norm_num)
theorem B946873 : Blo 932582 946873 := bbase (se 2 (by rfl) ⟨355077, by rfl⟩ : syracuseStep 946873 = 710155) (by norm_num)
theorem B1995877 : Blo 932582 1995877 := bbase (se 4 (by rfl) ⟨187113, by rfl⟩ : syracuseStep 1995877 = 374227) (by norm_num)
theorem B1995997 : Blo 932582 1995997 := bbase (se 3 (by rfl) ⟨374249, by rfl⟩ : syracuseStep 1995997 = 748499) (by norm_num)
theorem B2159941 : Blo 932582 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B1996253 : Blo 932582 1996253 := bbase (se 3 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 1996253 = 748595) (by norm_num)
theorem B1898077 : Blo 932582 1898077 := bbase (se 3 (by rfl) ⟨355889, by rfl⟩ : syracuseStep 1898077 = 711779) (by norm_num)
theorem B2127581 : Blo 932582 2127581 := bbase (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) (by norm_num)
theorem B948349 : Blo 932582 948349 := bbase (se 3 (by rfl) ⟨177815, by rfl⟩ : syracuseStep 948349 = 355631) (by norm_num)
theorem B6387893 : Blo 932582 6387893 := bbase (se 5 (by rfl) ⟨299432, by rfl⟩ : syracuseStep 6387893 = 598865) (by norm_num)
theorem B1898677 : Blo 932582 1898677 := bbase (se 5 (by rfl) ⟨89000, by rfl⟩ : syracuseStep 1898677 = 178001) (by norm_num)
theorem B1997141 : Blo 932582 1997141 := bbase (se 10 (by rfl) ⟨2925, by rfl⟩ : syracuseStep 1997141 = 5851) (by norm_num)
theorem B2521493 : Blo 932582 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B4323797 : Blo 932582 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B1997381 : Blo 932582 1997381 := bbase (se 4 (by rfl) ⟨187254, by rfl⟩ : syracuseStep 1997381 = 374509) (by norm_num)
theorem B12974741 : Blo 932582 12974741 := bbase (se 6 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 12974741 = 608191) (by norm_num)
theorem B4487861 : Blo 932582 4487861 := bbase (se 5 (by rfl) ⟨210368, by rfl⟩ : syracuseStep 4487861 = 420737) (by norm_num)
theorem B4487957 : Blo 932582 4487957 := bbase (se 6 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 4487957 = 210373) (by norm_num)
theorem B3996469 : Blo 932582 3996469 := bbase (se 5 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 3996469 = 374669) (by norm_num)
theorem B1997885 : Blo 932582 1997885 := bbase (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) (by norm_num)
theorem B1997893 : Blo 932582 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B22772821 : Blo 932582 22772821 := bbase (se 8 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 22772821 = 266869) (by norm_num)
theorem B1080409 : Blo 932582 1080409 := bbase (se 2 (by rfl) ⟨405153, by rfl⟩ : syracuseStep 1080409 = 810307) (by norm_num)
theorem B2522261 : Blo 932582 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B4259141 : Blo 932582 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B8977877 : Blo 932582 8977877 := bbase (se 7 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 8977877 = 210419) (by norm_num)
theorem B2883077 : Blo 932582 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B3374789 : Blo 932582 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B7995125 : Blo 932582 7995125 := bbase (se 5 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 7995125 = 749543) (by norm_num)
theorem B2130275 : Blo 932582 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B2556419 : Blo 932582 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B1999363 : Blo 932582 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B9732707 : Blo 932582 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B2425457 : Blo 932582 2425457 := bstep (se 2 (by rfl) ⟨909546, by rfl⟩ : syracuseStep 2425457 = 1819093) B1819093
theorem B1049251 : Blo 932582 1049251 := bstep (se 1 (by rfl) ⟨786938, by rfl⟩ : syracuseStep 1049251 = 1573877) B1573877
theorem B5046961 : Blo 932582 5046961 := bstep (se 2 (by rfl) ⟨1892610, by rfl⟩ : syracuseStep 5046961 = 3785221) B3785221
theorem B5997347 : Blo 932582 5997347 := bstep (se 1 (by rfl) ⟨4498010, by rfl⟩ : syracuseStep 5997347 = 8996021) B8996021
theorem B1049395 : Blo 932582 1049395 := bstep (se 1 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 1049395 = 1574093) B1574093
theorem B1180595 : Blo 932582 1180595 := bstep (se 1 (by rfl) ⟨885446, by rfl⟩ : syracuseStep 1180595 = 1770893) B1770893
theorem B1049539 : Blo 932582 1049539 := bstep (se 1 (by rfl) ⟨787154, by rfl⟩ : syracuseStep 1049539 = 1574309) B1574309
theorem B1573843 : Blo 932582 1573843 := bstep (se 1 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 1573843 = 2360765) B2360765
theorem B8520689 : Blo 932582 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B1049683 : Blo 932582 1049683 := bstep (se 1 (by rfl) ⟨787262, by rfl⟩ : syracuseStep 1049683 = 1574525) B1574525
theorem B1573985 : Blo 932582 1573985 := bstep (se 2 (by rfl) ⟨590244, by rfl⟩ : syracuseStep 1573985 = 1180489) B1180489
theorem B2393201 : Blo 932582 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B1770673 : Blo 932582 1770673 := bstep (se 2 (by rfl) ⟨664002, by rfl⟩ : syracuseStep 1770673 = 1328005) B1328005
theorem B4490417 : Blo 932582 4490417 := bstep (se 2 (by rfl) ⟨1683906, by rfl⟩ : syracuseStep 4490417 = 3367813) B3367813
theorem B2098385 : Blo 932582 2098385 := bstep (se 2 (by rfl) ⟨786894, by rfl⟩ : syracuseStep 2098385 = 1573789) B1573789
theorem B1574113 : Blo 932582 1574113 := bstep (se 2 (by rfl) ⟨590292, by rfl⟩ : syracuseStep 1574113 = 1180585) B1180585
theorem B2098403 : Blo 932582 2098403 := bstep (se 1 (by rfl) ⟨1573802, by rfl⟩ : syracuseStep 2098403 = 3147605) B3147605
theorem B1049827 : Blo 932582 1049827 := bstep (se 1 (by rfl) ⟨787370, by rfl⟩ : syracuseStep 1049827 = 1574741) B1574741
theorem B1574147 : Blo 932582 1574147 := bstep (se 1 (by rfl) ⟨1180610, by rfl⟩ : syracuseStep 1574147 = 2361221) B2361221
theorem B2000209 : Blo 932582 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B1049971 : Blo 932582 1049971 := bstep (se 1 (by rfl) ⟨787478, by rfl⟩ : syracuseStep 1049971 = 1574957) B1574957
theorem B1574275 : Blo 932582 1574275 := bstep (se 1 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 1574275 = 2361413) B2361413
theorem B2360785 : Blo 932582 2360785 := bstep (se 2 (by rfl) ⟨885294, by rfl⟩ : syracuseStep 2360785 = 1770589) B1770589
theorem B3999203 : Blo 932582 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B2098673 : Blo 932582 2098673 := bstep (se 2 (by rfl) ⟨787002, by rfl⟩ : syracuseStep 2098673 = 1574005) B1574005
theorem B2098691 : Blo 932582 2098691 := bstep (se 1 (by rfl) ⟨1574018, by rfl⟩ : syracuseStep 2098691 = 3148037) B3148037
theorem B1050115 : Blo 932582 1050115 := bstep (se 1 (by rfl) ⟨787586, by rfl⟩ : syracuseStep 1050115 = 1575173) B1575173
theorem B1574417 : Blo 932582 1574417 := bstep (se 2 (by rfl) ⟨590406, by rfl⟩ : syracuseStep 1574417 = 1180813) B1180813
theorem B1771075 : Blo 932582 1771075 := bstep (se 1 (by rfl) ⟨1328306, by rfl⟩ : syracuseStep 1771075 = 2656613) B2656613
theorem B1771121 : Blo 932582 1771121 := bstep (se 2 (by rfl) ⟨664170, by rfl⟩ : syracuseStep 1771121 = 1328341) B1328341
theorem B1181299 : Blo 932582 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B1574545 : Blo 932582 1574545 := bstep (se 2 (by rfl) ⟨590454, by rfl⟩ : syracuseStep 1574545 = 1180909) B1180909
theorem B1050259 : Blo 932582 1050259 := bstep (se 1 (by rfl) ⟨787694, by rfl⟩ : syracuseStep 1050259 = 1575389) B1575389
theorem B1574579 : Blo 932582 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B2655953 : Blo 932582 2655953 := bstep (se 2 (by rfl) ⟨995982, by rfl⟩ : syracuseStep 2655953 = 1991965) B1991965
theorem B1181395 : Blo 932582 1181395 := bstep (se 1 (by rfl) ⟨886046, by rfl⟩ : syracuseStep 1181395 = 1772093) B1772093
theorem B2361059 : Blo 932582 2361059 := bstep (se 1 (by rfl) ⟨1770794, by rfl⟩ : syracuseStep 2361059 = 3541589) B3541589
theorem B2098961 : Blo 932582 2098961 := bstep (se 2 (by rfl) ⟨787110, by rfl⟩ : syracuseStep 2098961 = 1574221) B1574221
theorem B2098979 : Blo 932582 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B1050403 : Blo 932582 1050403 := bstep (se 1 (by rfl) ⟨787802, by rfl⟩ : syracuseStep 1050403 = 1575605) B1575605
theorem B1574707 : Blo 932582 1574707 := bstep (se 1 (by rfl) ⟨1181030, by rfl⟩ : syracuseStep 1574707 = 2362061) B2362061
theorem B1771409 : Blo 932582 1771409 := bstep (se 2 (by rfl) ⟨664278, by rfl⟩ : syracuseStep 1771409 = 1328557) B1328557
theorem B2361251 : Blo 932582 2361251 := bstep (se 1 (by rfl) ⟨1770938, by rfl⟩ : syracuseStep 2361251 = 3541877) B3541877
theorem B1050547 : Blo 932582 1050547 := bstep (se 1 (by rfl) ⟨787910, by rfl⟩ : syracuseStep 1050547 = 1575821) B1575821
theorem B1574849 : Blo 932582 1574849 := bstep (se 2 (by rfl) ⟨590568, by rfl⟩ : syracuseStep 1574849 = 1181137) B1181137
theorem B3147821 : Blo 932582 3147821 := bstep (se 3 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 3147821 = 1180433) B1180433
theorem B2099249 : Blo 932582 2099249 := bstep (se 2 (by rfl) ⟨787218, by rfl⟩ : syracuseStep 2099249 = 1574437) B1574437
theorem B1574977 : Blo 932582 1574977 := bstep (se 2 (by rfl) ⟨590616, by rfl⟩ : syracuseStep 1574977 = 1181233) B1181233
theorem B2099267 : Blo 932582 2099267 := bstep (se 1 (by rfl) ⟨1574450, by rfl⟩ : syracuseStep 2099267 = 3148901) B3148901
theorem B1050691 : Blo 932582 1050691 := bstep (se 1 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 1050691 = 1576037) B1576037
theorem B3147875 : Blo 932582 3147875 := bstep (se 1 (by rfl) ⟨2360906, by rfl⟩ : syracuseStep 3147875 = 4721813) B4721813
theorem B1575011 : Blo 932582 1575011 := bstep (se 1 (by rfl) ⟨1181258, by rfl⟩ : syracuseStep 1575011 = 2362517) B2362517
theorem B1181891 : Blo 932582 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B1050835 : Blo 932582 1050835 := bstep (se 1 (by rfl) ⟨788126, by rfl⟩ : syracuseStep 1050835 = 1576253) B1576253
theorem B1575139 : Blo 932582 1575139 := bstep (se 1 (by rfl) ⟨1181354, by rfl⟩ : syracuseStep 1575139 = 2362709) B2362709
theorem B2099537 : Blo 932582 2099537 := bstep (se 2 (by rfl) ⟨787326, by rfl⟩ : syracuseStep 2099537 = 1574653) B1574653
theorem B2099555 : Blo 932582 2099555 := bstep (se 1 (by rfl) ⟨1574666, by rfl⟩ : syracuseStep 2099555 = 3149333) B3149333
theorem B5048675 : Blo 932582 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B1050979 : Blo 932582 1050979 := bstep (se 1 (by rfl) ⟨788234, by rfl⟩ : syracuseStep 1050979 = 1576469) B1576469
theorem B3148145 : Blo 932582 3148145 := bstep (se 2 (by rfl) ⟨1180554, by rfl⟩ : syracuseStep 3148145 = 2361109) B2361109
theorem B10226033 : Blo 932582 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B1575281 : Blo 932582 1575281 := bstep (se 2 (by rfl) ⟨590730, by rfl⟩ : syracuseStep 1575281 = 1181461) B1181461
theorem B2656739 : Blo 932582 2656739 := bstep (se 1 (by rfl) ⟨1992554, by rfl⟩ : syracuseStep 2656739 = 3985109) B3985109
theorem B1575409 : Blo 932582 1575409 := bstep (se 2 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 1575409 = 1181557) B1181557
theorem B1051123 : Blo 932582 1051123 := bstep (se 1 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 1051123 = 1576685) B1576685
theorem B1575443 : Blo 932582 1575443 := bstep (se 1 (by rfl) ⟨1181582, by rfl⟩ : syracuseStep 1575443 = 2363165) B2363165
theorem B3541603 : Blo 932582 3541603 := bstep (se 1 (by rfl) ⟨2656202, by rfl⟩ : syracuseStep 3541603 = 5312405) B5312405
theorem B1772131 : Blo 932582 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B2099825 : Blo 932582 2099825 := bstep (se 2 (by rfl) ⟨787434, by rfl⟩ : syracuseStep 2099825 = 1574869) B1574869
theorem B2099843 : Blo 932582 2099843 := bstep (se 1 (by rfl) ⟨1574882, by rfl⟩ : syracuseStep 2099843 = 3149765) B3149765
theorem B1051267 : Blo 932582 1051267 := bstep (se 1 (by rfl) ⟨788450, by rfl⟩ : syracuseStep 1051267 = 1576901) B1576901
theorem B1575571 : Blo 932582 1575571 := bstep (se 1 (by rfl) ⟨1181678, by rfl⟩ : syracuseStep 1575571 = 2363357) B2363357
theorem B1051411 : Blo 932582 1051411 := bstep (se 1 (by rfl) ⟨788558, by rfl⟩ : syracuseStep 1051411 = 1577117) B1577117
theorem B1575713 : Blo 932582 1575713 := bstep (se 2 (by rfl) ⟨590892, by rfl⟩ : syracuseStep 1575713 = 1181785) B1181785
theorem B2657069 : Blo 932582 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B2362193 : Blo 932582 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B2657137 : Blo 932582 2657137 := bstep (se 2 (by rfl) ⟨996426, by rfl⟩ : syracuseStep 2657137 = 1992853) B1992853
theorem B2362243 : Blo 932582 2362243 := bstep (se 1 (by rfl) ⟨1771682, by rfl⟩ : syracuseStep 2362243 = 3543365) B3543365
theorem B1182595 : Blo 932582 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B3148685 : Blo 932582 3148685 := bstep (se 3 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 3148685 = 1180757) B1180757
theorem B2100113 : Blo 932582 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B1575841 : Blo 932582 1575841 := bstep (se 2 (by rfl) ⟨590940, by rfl⟩ : syracuseStep 1575841 = 1181881) B1181881
theorem B2100131 : Blo 932582 2100131 := bstep (se 1 (by rfl) ⟨1575098, by rfl⟩ : syracuseStep 2100131 = 3150197) B3150197
theorem B1051555 : Blo 932582 1051555 := bstep (se 1 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 1051555 = 1577333) B1577333
theorem B3148739 : Blo 932582 3148739 := bstep (se 1 (by rfl) ⟨2361554, by rfl⟩ : syracuseStep 3148739 = 4723109) B4723109
theorem B1575875 : Blo 932582 1575875 := bstep (se 1 (by rfl) ⟨1181906, by rfl⟩ : syracuseStep 1575875 = 2363813) B2363813
theorem B1182691 : Blo 932582 1182691 := bstep (se 1 (by rfl) ⟨887018, by rfl⟩ : syracuseStep 1182691 = 1774037) B1774037
theorem B2362385 : Blo 932582 2362385 := bstep (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) B1771789
theorem B1772579 : Blo 932582 1772579 := bstep (se 1 (by rfl) ⟨1329434, by rfl⟩ : syracuseStep 1772579 = 2658869) B2658869
theorem B1051699 : Blo 932582 1051699 := bstep (se 1 (by rfl) ⟨788774, by rfl⟩ : syracuseStep 1051699 = 1577549) B1577549
theorem B1576003 : Blo 932582 1576003 := bstep (se 1 (by rfl) ⟨1182002, by rfl⟩ : syracuseStep 1576003 = 2364005) B2364005
theorem B2657411 : Blo 932582 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B1281187 : Blo 932582 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B2100401 : Blo 932582 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B1051843 : Blo 932582 1051843 := bstep (se 1 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 1051843 = 1577765) B1577765
theorem B2100419 : Blo 932582 2100419 := bstep (se 1 (by rfl) ⟨1575314, by rfl⟩ : syracuseStep 2100419 = 3150629) B3150629
theorem B4492493 : Blo 932582 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B3149009 : Blo 932582 3149009 := bstep (se 2 (by rfl) ⟨1180878, by rfl⟩ : syracuseStep 3149009 = 2361757) B2361757
theorem B1576145 : Blo 932582 1576145 := bstep (se 2 (by rfl) ⟨591054, by rfl⟩ : syracuseStep 1576145 = 1182109) B1182109
theorem B1346881 : Blo 932582 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B1772867 : Blo 932582 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B1576273 : Blo 932582 1576273 := bstep (se 2 (by rfl) ⟨591102, by rfl⟩ : syracuseStep 1576273 = 1182205) B1182205
theorem B1051987 : Blo 932582 1051987 := bstep (se 1 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 1051987 = 1577981) B1577981
theorem B8981873 : Blo 932582 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B1576307 : Blo 932582 1576307 := bstep (se 1 (by rfl) ⟨1182230, by rfl⟩ : syracuseStep 1576307 = 2364461) B2364461
theorem B2100689 : Blo 932582 2100689 := bstep (se 2 (by rfl) ⟨787758, by rfl⟩ : syracuseStep 2100689 = 1575517) B1575517
theorem B2526673 : Blo 932582 2526673 := bstep (se 2 (by rfl) ⟨947502, by rfl⟩ : syracuseStep 2526673 = 1895005) B1895005
theorem B1183187 : Blo 932582 1183187 := bstep (se 1 (by rfl) ⟨887390, by rfl⟩ : syracuseStep 1183187 = 1774781) B1774781
theorem B2100707 : Blo 932582 2100707 := bstep (se 1 (by rfl) ⟨1575530, by rfl⟩ : syracuseStep 2100707 = 3151061) B3151061
theorem B1052131 : Blo 932582 1052131 := bstep (se 1 (by rfl) ⟨789098, by rfl⟩ : syracuseStep 1052131 = 1578197) B1578197
theorem B1576435 : Blo 932582 1576435 := bstep (se 1 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 1576435 = 2364653) B2364653
theorem B1052275 : Blo 932582 1052275 := bstep (se 1 (by rfl) ⟨789206, by rfl⟩ : syracuseStep 1052275 = 1578413) B1578413
theorem B1576577 : Blo 932582 1576577 := bstep (se 2 (by rfl) ⟨591216, by rfl⟩ : syracuseStep 1576577 = 1182433) B1182433
theorem B5049989 : Blo 932582 5049989 := bstep (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) B946873
theorem B3149549 : Blo 932582 3149549 := bstep (se 3 (by rfl) ⟨590540, by rfl⟩ : syracuseStep 3149549 = 1181081) B1181081
theorem B2100977 : Blo 932582 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B1576705 : Blo 932582 1576705 := bstep (se 2 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 1576705 = 1182529) B1182529
theorem B2100995 : Blo 932582 2100995 := bstep (se 1 (by rfl) ⟨1575746, by rfl⟩ : syracuseStep 2100995 = 3151493) B3151493
theorem B1052419 : Blo 932582 1052419 := bstep (se 1 (by rfl) ⟨789314, by rfl⟩ : syracuseStep 1052419 = 1578629) B1578629
theorem B3149603 : Blo 932582 3149603 := bstep (se 1 (by rfl) ⟨2362202, by rfl⟩ : syracuseStep 3149603 = 4724405) B4724405
theorem B1576739 : Blo 932582 1576739 := bstep (se 1 (by rfl) ⟨1182554, by rfl⟩ : syracuseStep 1576739 = 2365109) B2365109
theorem B1052563 : Blo 932582 1052563 := bstep (se 1 (by rfl) ⟨789422, by rfl⟩ : syracuseStep 1052563 = 1578845) B1578845
theorem B1576867 : Blo 932582 1576867 := bstep (se 1 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 1576867 = 2365301) B2365301
theorem B2658253 : Blo 932582 2658253 := bstep (se 3 (by rfl) ⟨498422, by rfl⟩ : syracuseStep 2658253 = 996845) B996845
theorem B2363377 : Blo 932582 2363377 := bstep (se 2 (by rfl) ⟨886266, by rfl⟩ : syracuseStep 2363377 = 1772533) B1772533
theorem B2101265 : Blo 932582 2101265 := bstep (se 2 (by rfl) ⟨787974, by rfl⟩ : syracuseStep 2101265 = 1575949) B1575949
theorem B2101283 : Blo 932582 2101283 := bstep (se 1 (by rfl) ⟨1575962, by rfl⟩ : syracuseStep 2101283 = 3151925) B3151925
theorem B1052707 : Blo 932582 1052707 := bstep (se 1 (by rfl) ⟨789530, by rfl⟩ : syracuseStep 1052707 = 1579061) B1579061
theorem B3149873 : Blo 932582 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B1577009 : Blo 932582 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B2658413 : Blo 932582 2658413 := bstep (se 3 (by rfl) ⟨498452, by rfl⟩ : syracuseStep 2658413 = 996905) B996905
theorem B1183891 : Blo 932582 1183891 := bstep (se 1 (by rfl) ⟨887918, by rfl⟩ : syracuseStep 1183891 = 1775837) B1775837
theorem B1577137 : Blo 932582 1577137 := bstep (se 2 (by rfl) ⟨591426, by rfl⟩ : syracuseStep 1577137 = 1182853) B1182853
theorem B1052851 : Blo 932582 1052851 := bstep (se 1 (by rfl) ⟨789638, by rfl⟩ : syracuseStep 1052851 = 1579277) B1579277
theorem B1577171 : Blo 932582 1577171 := bstep (se 1 (by rfl) ⟨1182878, by rfl⟩ : syracuseStep 1577171 = 2365757) B2365757
theorem B1773809 : Blo 932582 1773809 := bstep (se 2 (by rfl) ⟨665178, by rfl⟩ : syracuseStep 1773809 = 1330357) B1330357
theorem B1183987 : Blo 932582 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B2363651 : Blo 932582 2363651 := bstep (se 1 (by rfl) ⟨1772738, by rfl⟩ : syracuseStep 2363651 = 3545477) B3545477
theorem B2658595 : Blo 932582 2658595 := bstep (se 1 (by rfl) ⟨1993946, by rfl⟩ : syracuseStep 2658595 = 3987893) B3987893
theorem B2101553 : Blo 932582 2101553 := bstep (se 2 (by rfl) ⟨788082, by rfl⟩ : syracuseStep 2101553 = 1576165) B1576165
theorem B2527537 : Blo 932582 2527537 := bstep (se 2 (by rfl) ⟨947826, by rfl⟩ : syracuseStep 2527537 = 1895653) B1895653
theorem B2101571 : Blo 932582 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B1052995 : Blo 932582 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B1577299 : Blo 932582 1577299 := bstep (se 1 (by rfl) ⟨1182974, by rfl⟩ : syracuseStep 1577299 = 2365949) B2365949
theorem B2363843 : Blo 932582 2363843 := bstep (se 1 (by rfl) ⟨1772882, by rfl⟩ : syracuseStep 2363843 = 3545765) B3545765
theorem B1053139 : Blo 932582 1053139 := bstep (se 1 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 1053139 = 1579709) B1579709
theorem B1577441 : Blo 932582 1577441 := bstep (se 2 (by rfl) ⟨591540, by rfl⟩ : syracuseStep 1577441 = 1183081) B1183081
theorem B3150413 : Blo 932582 3150413 := bstep (se 3 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 3150413 = 1181405) B1181405
theorem B2101841 : Blo 932582 2101841 := bstep (se 2 (by rfl) ⟨788190, by rfl⟩ : syracuseStep 2101841 = 1576381) B1576381
theorem B1577569 : Blo 932582 1577569 := bstep (se 2 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 1577569 = 1183177) B1183177
theorem B2101859 : Blo 932582 2101859 := bstep (se 1 (by rfl) ⟨1576394, by rfl⟩ : syracuseStep 2101859 = 3152789) B3152789
theorem B1053283 : Blo 932582 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B3150467 : Blo 932582 3150467 := bstep (se 1 (by rfl) ⟨2362850, by rfl⟩ : syracuseStep 3150467 = 4725701) B4725701
theorem B1577603 : Blo 932582 1577603 := bstep (se 1 (by rfl) ⟨1183202, by rfl⟩ : syracuseStep 1577603 = 2366405) B2366405
theorem B20189837 : Blo 932582 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B1184483 : Blo 932582 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B1053427 : Blo 932582 1053427 := bstep (se 1 (by rfl) ⟨790070, by rfl⟩ : syracuseStep 1053427 = 1580141) B1580141
theorem B1577731 : Blo 932582 1577731 := bstep (se 1 (by rfl) ⟨1183298, by rfl⟩ : syracuseStep 1577731 = 2366597) B2366597
theorem B3543821 : Blo 932582 3543821 := bstep (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) B1328933
theorem B2102129 : Blo 932582 2102129 := bstep (se 2 (by rfl) ⟨788298, by rfl⟩ : syracuseStep 2102129 = 1576597) B1576597
theorem B2102147 : Blo 932582 2102147 := bstep (se 1 (by rfl) ⟨1576610, by rfl⟩ : syracuseStep 2102147 = 3153221) B3153221
theorem B1053571 : Blo 932582 1053571 := bstep (se 1 (by rfl) ⟨790178, by rfl⟩ : syracuseStep 1053571 = 1580357) B1580357
theorem B3150737 : Blo 932582 3150737 := bstep (se 2 (by rfl) ⟨1181526, by rfl⟩ : syracuseStep 3150737 = 2363053) B2363053
theorem B1577873 : Blo 932582 1577873 := bstep (se 2 (by rfl) ⟨591702, by rfl⟩ : syracuseStep 1577873 = 1183405) B1183405
theorem B1578001 : Blo 932582 1578001 := bstep (se 2 (by rfl) ⟨591750, by rfl⟩ : syracuseStep 1578001 = 1183501) B1183501
theorem B1578035 : Blo 932582 1578035 := bstep (se 1 (by rfl) ⟨1183526, by rfl⟩ : syracuseStep 1578035 = 2367053) B2367053
theorem B1774705 : Blo 932582 1774705 := bstep (se 2 (by rfl) ⟨665514, by rfl⟩ : syracuseStep 1774705 = 1331029) B1331029
theorem B2102417 : Blo 932582 2102417 := bstep (se 2 (by rfl) ⟨788406, by rfl⟩ : syracuseStep 2102417 = 1576813) B1576813
theorem B2102435 : Blo 932582 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B1578163 : Blo 932582 1578163 := bstep (se 1 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 1578163 = 2367245) B2367245
theorem B2528497 : Blo 932582 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B1774865 : Blo 932582 1774865 := bstep (se 2 (by rfl) ⟨665574, by rfl⟩ : syracuseStep 1774865 = 1331149) B1331149
theorem B1578305 : Blo 932582 1578305 := bstep (se 2 (by rfl) ⟨591864, by rfl⟩ : syracuseStep 1578305 = 1183729) B1183729
theorem B4724081 : Blo 932582 4724081 := bstep (se 2 (by rfl) ⟨1771530, by rfl⟩ : syracuseStep 4724081 = 3543061) B3543061
theorem B2364785 : Blo 932582 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B2364835 : Blo 932582 2364835 := bstep (se 1 (by rfl) ⟨1773626, by rfl⟩ : syracuseStep 2364835 = 3547253) B3547253
theorem B1185187 : Blo 932582 1185187 := bstep (se 1 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 1185187 = 1777781) B1777781
theorem B3151277 : Blo 932582 3151277 := bstep (se 3 (by rfl) ⟨590864, by rfl⟩ : syracuseStep 3151277 = 1181729) B1181729
theorem B2102705 : Blo 932582 2102705 := bstep (se 2 (by rfl) ⟨788514, by rfl⟩ : syracuseStep 2102705 = 1577029) B1577029
theorem B1578433 : Blo 932582 1578433 := bstep (se 2 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 1578433 = 1183825) B1183825
theorem B2102723 : Blo 932582 2102723 := bstep (se 1 (by rfl) ⟨1577042, by rfl⟩ : syracuseStep 2102723 = 3154085) B3154085
theorem B3151331 : Blo 932582 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B1578467 : Blo 932582 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B1185283 : Blo 932582 1185283 := bstep (se 1 (by rfl) ⟨888962, by rfl⟩ : syracuseStep 1185283 = 1777925) B1777925
theorem B2364977 : Blo 932582 2364977 := bstep (se 2 (by rfl) ⟨886866, by rfl⟩ : syracuseStep 2364977 = 1773733) B1773733
theorem B1578595 : Blo 932582 1578595 := bstep (se 1 (by rfl) ⟨1183946, by rfl⟩ : syracuseStep 1578595 = 2367893) B2367893
theorem B2135683 : Blo 932582 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B2659985 : Blo 932582 2659985 := bstep (se 2 (by rfl) ⟨997494, by rfl⟩ : syracuseStep 2659985 = 1994989) B1994989
theorem B1775267 : Blo 932582 1775267 := bstep (se 1 (by rfl) ⟨1331450, by rfl⟩ : syracuseStep 1775267 = 2662901) B2662901
theorem B2102993 : Blo 932582 2102993 := bstep (se 2 (by rfl) ⟨788622, by rfl⟩ : syracuseStep 2102993 = 1577245) B1577245
theorem B2103011 : Blo 932582 2103011 := bstep (se 1 (by rfl) ⟨1577258, by rfl⟩ : syracuseStep 2103011 = 3154517) B3154517
theorem B3151601 : Blo 932582 3151601 := bstep (se 2 (by rfl) ⟨1181850, by rfl⟩ : syracuseStep 3151601 = 2363701) B2363701
theorem B1578737 : Blo 932582 1578737 := bstep (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) B1184053
theorem B1578865 : Blo 932582 1578865 := bstep (se 2 (by rfl) ⟨592074, by rfl⟩ : syracuseStep 1578865 = 1184149) B1184149
theorem B2987921 : Blo 932582 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B1578899 : Blo 932582 1578899 := bstep (se 1 (by rfl) ⟨1184174, by rfl⟩ : syracuseStep 1578899 = 2368349) B2368349
theorem B21010373 : Blo 932582 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B2103281 : Blo 932582 2103281 := bstep (se 2 (by rfl) ⟨788730, by rfl⟩ : syracuseStep 2103281 = 1577461) B1577461
theorem B2103299 : Blo 932582 2103299 := bstep (se 1 (by rfl) ⟨1577474, by rfl⟩ : syracuseStep 2103299 = 3154949) B3154949
theorem B1579027 : Blo 932582 1579027 := bstep (se 1 (by rfl) ⟨1184270, by rfl⟩ : syracuseStep 1579027 = 2368541) B2368541
theorem B8984675 : Blo 932582 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B7968881 : Blo 932582 7968881 := bstep (se 2 (by rfl) ⟨2988330, by rfl⟩ : syracuseStep 7968881 = 5976661) B5976661
theorem B1579169 : Blo 932582 1579169 := bstep (se 2 (by rfl) ⟨592188, by rfl⟩ : syracuseStep 1579169 = 1184377) B1184377
theorem B3152141 : Blo 932582 3152141 := bstep (se 3 (by rfl) ⟨591026, by rfl⟩ : syracuseStep 3152141 = 1182053) B1182053
theorem B2103569 : Blo 932582 2103569 := bstep (se 2 (by rfl) ⟨788838, by rfl⟩ : syracuseStep 2103569 = 1577677) B1577677
theorem B1579297 : Blo 932582 1579297 := bstep (se 2 (by rfl) ⟨592236, by rfl⟩ : syracuseStep 1579297 = 1184473) B1184473
theorem B2103587 : Blo 932582 2103587 := bstep (se 1 (by rfl) ⟨1577690, by rfl⟩ : syracuseStep 2103587 = 3155381) B3155381
theorem B3152195 : Blo 932582 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B1579331 : Blo 932582 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B1579459 : Blo 932582 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B4790755 : Blo 932582 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B2365969 : Blo 932582 2365969 := bstep (se 2 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 2365969 = 1774477) B1774477
theorem B1776163 : Blo 932582 1776163 := bstep (se 1 (by rfl) ⟨1332122, by rfl⟩ : syracuseStep 1776163 = 2664245) B2664245
theorem B2103857 : Blo 932582 2103857 := bstep (se 2 (by rfl) ⟨788946, by rfl⟩ : syracuseStep 2103857 = 1577893) B1577893
theorem B2103875 : Blo 932582 2103875 := bstep (se 1 (by rfl) ⟨1577906, by rfl⟩ : syracuseStep 2103875 = 3155813) B3155813
theorem B2660941 : Blo 932582 2660941 := bstep (se 3 (by rfl) ⟨498926, by rfl⟩ : syracuseStep 2660941 = 997853) B997853
theorem B3152465 : Blo 932582 3152465 := bstep (se 2 (by rfl) ⟨1182174, by rfl⟩ : syracuseStep 3152465 = 2364349) B2364349
theorem B1579601 : Blo 932582 1579601 := bstep (se 2 (by rfl) ⟨592350, by rfl⟩ : syracuseStep 1579601 = 1184701) B1184701
theorem B1776323 : Blo 932582 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B1579729 : Blo 932582 1579729 := bstep (se 2 (by rfl) ⟨592398, by rfl⟩ : syracuseStep 1579729 = 1184797) B1184797
theorem B9116387 : Blo 932582 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B1579763 : Blo 932582 1579763 := bstep (se 1 (by rfl) ⟨1184822, by rfl⟩ : syracuseStep 1579763 = 2369645) B2369645
theorem B4725539 : Blo 932582 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B2366243 : Blo 932582 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B2661169 : Blo 932582 2661169 := bstep (se 2 (by rfl) ⟨997938, by rfl⟩ : syracuseStep 2661169 = 1995877) B1995877
theorem B2104145 : Blo 932582 2104145 := bstep (se 2 (by rfl) ⟨789054, by rfl⟩ : syracuseStep 2104145 = 1578109) B1578109
theorem B2104163 : Blo 932582 2104163 := bstep (se 1 (by rfl) ⟨1578122, by rfl⟩ : syracuseStep 2104163 = 3156245) B3156245
theorem B1579891 : Blo 932582 1579891 := bstep (se 1 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 1579891 = 2369837) B2369837
theorem B2661329 : Blo 932582 2661329 := bstep (se 2 (by rfl) ⟨997998, by rfl⟩ : syracuseStep 2661329 = 1995997) B1995997
theorem B2366435 : Blo 932582 2366435 := bstep (se 1 (by rfl) ⟨1774826, by rfl⟩ : syracuseStep 2366435 = 3549653) B3549653
theorem B2989037 : Blo 932582 2989037 := bstep (se 3 (by rfl) ⟨560444, by rfl⟩ : syracuseStep 2989037 = 1120889) B1120889
theorem B1580033 : Blo 932582 1580033 := bstep (se 2 (by rfl) ⟨592512, by rfl⟩ : syracuseStep 1580033 = 1185025) B1185025
theorem B2661443 : Blo 932582 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B3153005 : Blo 932582 3153005 := bstep (se 3 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 3153005 = 1182377) B1182377
theorem B2104433 : Blo 932582 2104433 := bstep (se 2 (by rfl) ⟨789162, by rfl⟩ : syracuseStep 2104433 = 1578325) B1578325
theorem B1580161 : Blo 932582 1580161 := bstep (se 2 (by rfl) ⟨592560, by rfl⟩ : syracuseStep 1580161 = 1185121) B1185121
theorem B2104451 : Blo 932582 2104451 := bstep (se 1 (by rfl) ⟨1578338, by rfl⟩ : syracuseStep 2104451 = 3156677) B3156677
theorem B3153059 : Blo 932582 3153059 := bstep (se 1 (by rfl) ⟨2364794, by rfl⟩ : syracuseStep 3153059 = 4729589) B4729589
theorem B1580195 : Blo 932582 1580195 := bstep (se 1 (by rfl) ⟨1185146, by rfl⟩ : syracuseStep 1580195 = 2370293) B2370293
theorem B1580323 : Blo 932582 1580323 := bstep (se 1 (by rfl) ⟨1185242, by rfl⟩ : syracuseStep 1580323 = 2370485) B2370485
theorem B2104721 : Blo 932582 2104721 := bstep (se 2 (by rfl) ⟨789270, by rfl⟩ : syracuseStep 2104721 = 1578541) B1578541
theorem B2104739 : Blo 932582 2104739 := bstep (se 1 (by rfl) ⟨1578554, by rfl⟩ : syracuseStep 2104739 = 3157109) B3157109
theorem B3153329 : Blo 932582 3153329 := bstep (se 2 (by rfl) ⟨1182498, by rfl⟩ : syracuseStep 3153329 = 2364997) B2364997
theorem B1580465 : Blo 932582 1580465 := bstep (se 2 (by rfl) ⟨592674, by rfl⟩ : syracuseStep 1580465 = 1185349) B1185349
theorem B2530769 : Blo 932582 2530769 := bstep (se 2 (by rfl) ⟨949038, by rfl⟩ : syracuseStep 2530769 = 1898077) B1898077
theorem B7577059 : Blo 932582 7577059 := bstep (se 1 (by rfl) ⟨5682794, by rfl⟩ : syracuseStep 7577059 = 11365589) B11365589
theorem B4726349 : Blo 932582 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B3546737 : Blo 932582 3546737 := bstep (se 2 (by rfl) ⟨1330026, by rfl⟩ : syracuseStep 3546737 = 2660053) B2660053
theorem B2105009 : Blo 932582 2105009 := bstep (se 2 (by rfl) ⟨789378, by rfl⟩ : syracuseStep 2105009 = 1578757) B1578757
theorem B2105027 : Blo 932582 2105027 := bstep (se 1 (by rfl) ⟨1578770, by rfl⟩ : syracuseStep 2105027 = 3157541) B3157541
theorem B1777393 : Blo 932582 1777393 := bstep (se 2 (by rfl) ⟨666522, by rfl⟩ : syracuseStep 1777393 = 1333045) B1333045
theorem B2367377 : Blo 932582 2367377 := bstep (se 2 (by rfl) ⟨887766, by rfl⟩ : syracuseStep 2367377 = 1775533) B1775533
theorem B2367427 : Blo 932582 2367427 := bstep (se 1 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 2367427 = 3551141) B3551141
theorem B3153869 : Blo 932582 3153869 := bstep (se 3 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 3153869 = 1182701) B1182701
theorem B2105297 : Blo 932582 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B2105315 : Blo 932582 2105315 := bstep (se 1 (by rfl) ⟨1578986, by rfl⟩ : syracuseStep 2105315 = 3157973) B3157973
theorem B3153923 : Blo 932582 3153923 := bstep (se 1 (by rfl) ⟨2365442, by rfl⟩ : syracuseStep 3153923 = 4730885) B4730885
theorem B2990125 : Blo 932582 2990125 := bstep (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) B1121297
theorem B2662445 : Blo 932582 2662445 := bstep (se 3 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 2662445 = 998417) B998417
theorem B2367569 : Blo 932582 2367569 := bstep (se 2 (by rfl) ⟨887838, by rfl⟩ : syracuseStep 2367569 = 1775677) B1775677
theorem B10100933 : Blo 932582 10100933 := bstep (se 4 (by rfl) ⟨946962, by rfl⟩ : syracuseStep 10100933 = 1893925) B1893925
theorem B72982741 : Blo 932582 72982741 := bstep (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) B1710533
theorem B2662627 : Blo 932582 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B2105585 : Blo 932582 2105585 := bstep (se 2 (by rfl) ⟨789594, by rfl⟩ : syracuseStep 2105585 = 1579189) B1579189
theorem B2531569 : Blo 932582 2531569 := bstep (se 2 (by rfl) ⟨949338, by rfl⟩ : syracuseStep 2531569 = 1898677) B1898677
theorem B2105603 : Blo 932582 2105603 := bstep (se 1 (by rfl) ⟨1579202, by rfl⟩ : syracuseStep 2105603 = 3158405) B3158405
theorem B3154193 : Blo 932582 3154193 := bstep (se 2 (by rfl) ⟨1182822, by rfl⟩ : syracuseStep 3154193 = 2365645) B2365645
theorem B2662787 : Blo 932582 2662787 := bstep (se 1 (by rfl) ⟨1997090, by rfl⟩ : syracuseStep 2662787 = 3994181) B3994181
theorem B2105873 : Blo 932582 2105873 := bstep (se 2 (by rfl) ⟨789702, by rfl⟩ : syracuseStep 2105873 = 1579405) B1579405
theorem B25960981 : Blo 932582 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B2105891 : Blo 932582 2105891 := bstep (se 1 (by rfl) ⟨1579418, by rfl⟩ : syracuseStep 2105891 = 3158837) B3158837
theorem B1122931 : Blo 932582 1122931 := bstep (se 1 (by rfl) ⟨842198, by rfl⟩ : syracuseStep 1122931 = 1684397) B1684397
theorem B3154733 : Blo 932582 3154733 := bstep (se 3 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 3154733 = 1183025) B1183025
theorem B2106161 : Blo 932582 2106161 := bstep (se 2 (by rfl) ⟨789810, by rfl⟩ : syracuseStep 2106161 = 1579621) B1579621
theorem B2106179 : Blo 932582 2106179 := bstep (se 1 (by rfl) ⟨1579634, by rfl⟩ : syracuseStep 2106179 = 3159269) B3159269
theorem B207496021 : Blo 932582 207496021 := bstep (se 9 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 207496021 = 1215797) B1215797
theorem B3154787 : Blo 932582 3154787 := bstep (se 1 (by rfl) ⟨2366090, by rfl⟩ : syracuseStep 3154787 = 4732181) B4732181
theorem B1123315 : Blo 932582 1123315 := bstep (se 1 (by rfl) ⟨842486, by rfl⟩ : syracuseStep 1123315 = 1684973) B1684973
theorem B3548195 : Blo 932582 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B2368561 : Blo 932582 2368561 := bstep (se 2 (by rfl) ⟨888210, by rfl⟩ : syracuseStep 2368561 = 1776421) B1776421
theorem B2106449 : Blo 932582 2106449 := bstep (se 2 (by rfl) ⟨789918, by rfl⟩ : syracuseStep 2106449 = 1579837) B1579837
theorem B2106467 : Blo 932582 2106467 := bstep (se 1 (by rfl) ⟨1579850, by rfl⟩ : syracuseStep 2106467 = 3159701) B3159701
theorem B3155057 : Blo 932582 3155057 := bstep (se 2 (by rfl) ⟨1183146, by rfl⟩ : syracuseStep 3155057 = 2366293) B2366293
theorem B1418387 : Blo 932582 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B2368835 : Blo 932582 2368835 := bstep (se 1 (by rfl) ⟨1776626, by rfl⟩ : syracuseStep 2368835 = 3553253) B3553253
theorem B2106737 : Blo 932582 2106737 := bstep (se 2 (by rfl) ⟨790026, by rfl⟩ : syracuseStep 2106737 = 1580053) B1580053
theorem B2106755 : Blo 932582 2106755 := bstep (se 1 (by rfl) ⟨1580066, by rfl⟩ : syracuseStep 2106755 = 3160133) B3160133
theorem B2663857 : Blo 932582 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B2369027 : Blo 932582 2369027 := bstep (se 1 (by rfl) ⟨1776770, by rfl⟩ : syracuseStep 2369027 = 3553541) B3553541
theorem B1680995 : Blo 932582 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B3155597 : Blo 932582 3155597 := bstep (se 3 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 3155597 = 1183349) B1183349
theorem B2107025 : Blo 932582 2107025 := bstep (se 2 (by rfl) ⟨790134, by rfl⟩ : syracuseStep 2107025 = 1580269) B1580269
theorem B2107043 : Blo 932582 2107043 := bstep (se 1 (by rfl) ⟨1580282, by rfl⟩ : syracuseStep 2107043 = 3160565) B3160565
theorem B3155651 : Blo 932582 3155651 := bstep (se 1 (by rfl) ⟨2366738, by rfl⟩ : syracuseStep 3155651 = 4733477) B4733477
theorem B2991907 : Blo 932582 2991907 := bstep (se 1 (by rfl) ⟨2243930, by rfl⟩ : syracuseStep 2991907 = 4487861) B4487861
theorem B2991971 : Blo 932582 2991971 := bstep (se 1 (by rfl) ⟨2243978, by rfl⟩ : syracuseStep 2991971 = 4487957) B4487957
theorem B2992049 : Blo 932582 2992049 := bstep (se 2 (by rfl) ⟨1122018, by rfl⟩ : syracuseStep 2992049 = 2244037) B2244037
theorem B3155921 : Blo 932582 3155921 := bstep (se 2 (by rfl) ⟨1183470, by rfl⟩ : syracuseStep 3155921 = 2366941) B2366941
theorem B3549197 : Blo 932582 3549197 := bstep (se 3 (by rfl) ⟨665474, by rfl⟩ : syracuseStep 3549197 = 1330949) B1330949
theorem B1681507 : Blo 932582 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B5056739 : Blo 932582 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B1419697 : Blo 932582 1419697 := bstep (se 2 (by rfl) ⟨532386, by rfl⟩ : syracuseStep 1419697 = 1064773) B1064773
theorem B4729265 : Blo 932582 4729265 := bstep (se 2 (by rfl) ⟨1773474, by rfl⟩ : syracuseStep 4729265 = 3546949) B3546949
theorem B2369969 : Blo 932582 2369969 := bstep (se 2 (by rfl) ⟨888738, by rfl⟩ : syracuseStep 2369969 = 1777477) B1777477
theorem B16394723 : Blo 932582 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B2370019 : Blo 932582 2370019 := bstep (se 1 (by rfl) ⟨1777514, by rfl⟩ : syracuseStep 2370019 = 3555029) B3555029
theorem B3156461 : Blo 932582 3156461 := bstep (se 3 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 3156461 = 1183673) B1183673
theorem B3156515 : Blo 932582 3156515 := bstep (se 1 (by rfl) ⟨2367386, by rfl⟩ : syracuseStep 3156515 = 4734773) B4734773
theorem B2370161 : Blo 932582 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B2665133 : Blo 932582 2665133 := bstep (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) B999425
theorem B4270819 : Blo 932582 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B3156785 : Blo 932582 3156785 := bstep (se 2 (by rfl) ⟨1183794, by rfl⟩ : syracuseStep 3156785 = 2367589) B2367589
theorem B2665315 : Blo 932582 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B2665361 : Blo 932582 2665361 := bstep (se 2 (by rfl) ⟨999510, by rfl⟩ : syracuseStep 2665361 = 1999021) B1999021
theorem B4271075 : Blo 932582 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B18197617 : Blo 932582 18197617 := bstep (se 2 (by rfl) ⟨6824106, by rfl⟩ : syracuseStep 18197617 = 13648213) B13648213
theorem B5319877 : Blo 932582 5319877 := bstep (se 4 (by rfl) ⟨498738, by rfl⟩ : syracuseStep 5319877 = 997477) B997477
theorem B3157325 : Blo 932582 3157325 := bstep (se 3 (by rfl) ⟨591998, by rfl⟩ : syracuseStep 3157325 = 1183997) B1183997
theorem B3157379 : Blo 932582 3157379 := bstep (se 1 (by rfl) ⟨2368034, by rfl⟩ : syracuseStep 3157379 = 4736069) B4736069
theorem B3157649 : Blo 932582 3157649 := bstep (se 2 (by rfl) ⟨1184118, by rfl⟩ : syracuseStep 3157649 = 2368237) B2368237
theorem B1683185 : Blo 932582 1683185 := bstep (se 2 (by rfl) ⟨631194, by rfl⟩ : syracuseStep 1683185 = 1262389) B1262389
theorem B2993969 : Blo 932582 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B4730723 : Blo 932582 4730723 := bstep (se 1 (by rfl) ⟨3548042, by rfl⟩ : syracuseStep 4730723 = 7096085) B7096085
theorem B3551309 : Blo 932582 3551309 := bstep (se 3 (by rfl) ⟨665870, by rfl⟩ : syracuseStep 3551309 = 1331741) B1331741
theorem B3158189 : Blo 932582 3158189 := bstep (se 3 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 3158189 = 1184321) B1184321
theorem B3158243 : Blo 932582 3158243 := bstep (se 1 (by rfl) ⟨2368682, by rfl⟩ : syracuseStep 3158243 = 4737365) B4737365
theorem B2666819 : Blo 932582 2666819 := bstep (se 1 (by rfl) ⟨2000114, by rfl⟩ : syracuseStep 2666819 = 4000229) B4000229
theorem B2994509 : Blo 932582 2994509 := bstep (se 3 (by rfl) ⟨561470, by rfl⟩ : syracuseStep 2994509 = 1122941) B1122941
theorem B11973005 : Blo 932582 11973005 := bstep (se 3 (by rfl) ⟨2244938, by rfl⟩ : syracuseStep 11973005 = 4489877) B4489877
theorem B3158513 : Blo 932582 3158513 := bstep (se 2 (by rfl) ⟨1184442, by rfl⟩ : syracuseStep 3158513 = 2368885) B2368885
theorem B1421891 : Blo 932582 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B4731533 : Blo 932582 4731533 := bstep (se 3 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 4731533 = 1774325) B1774325
theorem B3552113 : Blo 932582 3552113 := bstep (se 2 (by rfl) ⟨1332042, by rfl⟩ : syracuseStep 3552113 = 2664085) B2664085
theorem B3159053 : Blo 932582 3159053 := bstep (se 3 (by rfl) ⟨592322, by rfl⟩ : syracuseStep 3159053 = 1184645) B1184645
theorem B2307089 : Blo 932582 2307089 := bstep (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) B1730317
theorem B3159107 : Blo 932582 3159107 := bstep (se 1 (by rfl) ⟨2369330, by rfl⟩ : syracuseStep 3159107 = 4738661) B4738661
theorem B5321861 : Blo 932582 5321861 := bstep (se 4 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 5321861 = 997849) B997849
theorem B3159377 : Blo 932582 3159377 := bstep (se 2 (by rfl) ⟨1184766, by rfl⟩ : syracuseStep 3159377 = 2369533) B2369533
theorem B3552781 : Blo 932582 3552781 := bstep (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) B1332293
theorem B996995 : Blo 932582 996995 := bstep (se 1 (by rfl) ⟨747746, by rfl⟩ : syracuseStep 996995 = 1495493) B1495493
theorem B5977891 : Blo 932582 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B3159917 : Blo 932582 3159917 := bstep (se 3 (by rfl) ⟨592484, by rfl⟩ : syracuseStep 3159917 = 1184969) B1184969
theorem B1423217 : Blo 932582 1423217 := bstep (se 2 (by rfl) ⟨533706, by rfl⟩ : syracuseStep 1423217 = 1067413) B1067413
theorem B3159971 : Blo 932582 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B3160241 : Blo 932582 3160241 := bstep (se 2 (by rfl) ⟨1185090, by rfl⟩ : syracuseStep 3160241 = 2370181) B2370181
theorem B3553571 : Blo 932582 3553571 := bstep (se 1 (by rfl) ⟨2665178, by rfl⟩ : syracuseStep 3553571 = 5330357) B5330357
theorem B2242883 : Blo 932582 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B3160781 : Blo 932582 3160781 := bstep (se 3 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 3160781 = 1185293) B1185293
theorem B932595 : Blo 932582 932595 := bstep (se 1 (by rfl) ⟨699446, by rfl⟩ : syracuseStep 932595 = 1398893) B1398893
theorem B932611 : Blo 932582 932611 := bstep (se 1 (by rfl) ⟨699458, by rfl⟩ : syracuseStep 932611 = 1398917) B1398917
theorem B3160835 : Blo 932582 3160835 := bstep (se 1 (by rfl) ⟨2370626, by rfl⟩ : syracuseStep 3160835 = 4741253) B4741253
theorem B5978893 : Blo 932582 5978893 := bstep (se 3 (by rfl) ⟨1121042, by rfl⟩ : syracuseStep 5978893 = 2242085) B2242085
theorem B932627 : Blo 932582 932627 := bstep (se 1 (by rfl) ⟨699470, by rfl⟩ : syracuseStep 932627 = 1398941) B1398941
theorem B932643 : Blo 932582 932643 := bstep (se 1 (by rfl) ⟨699482, by rfl⟩ : syracuseStep 932643 = 1398965) B1398965
theorem B932659 : Blo 932582 932659 := bstep (se 1 (by rfl) ⟨699494, by rfl⟩ : syracuseStep 932659 = 1398989) B1398989
theorem B932675 : Blo 932582 932675 := bstep (se 1 (by rfl) ⟨699506, by rfl⟩ : syracuseStep 932675 = 1399013) B1399013
theorem B932691 : Blo 932582 932691 := bstep (se 1 (by rfl) ⟨699518, by rfl⟩ : syracuseStep 932691 = 1399037) B1399037
theorem B932707 : Blo 932582 932707 := bstep (se 1 (by rfl) ⟨699530, by rfl⟩ : syracuseStep 932707 = 1399061) B1399061
theorem B932723 : Blo 932582 932723 := bstep (se 1 (by rfl) ⟨699542, by rfl⟩ : syracuseStep 932723 = 1399085) B1399085
theorem B932739 : Blo 932582 932739 := bstep (se 1 (by rfl) ⟨699554, by rfl⟩ : syracuseStep 932739 = 1399109) B1399109
theorem B932755 : Blo 932582 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B932771 : Blo 932582 932771 := bstep (se 1 (by rfl) ⟨699578, by rfl⟩ : syracuseStep 932771 = 1399157) B1399157
theorem B3783601 : Blo 932582 3783601 := bstep (se 2 (by rfl) ⟨1418850, by rfl⟩ : syracuseStep 3783601 = 2837701) B2837701
theorem B932787 : Blo 932582 932787 := bstep (se 1 (by rfl) ⟨699590, by rfl⟩ : syracuseStep 932787 = 1399181) B1399181
theorem B3554225 : Blo 932582 3554225 := bstep (se 2 (by rfl) ⟨1332834, by rfl⟩ : syracuseStep 3554225 = 2665669) B2665669
theorem B932803 : Blo 932582 932803 := bstep (se 1 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 932803 = 1399205) B1399205
theorem B932819 : Blo 932582 932819 := bstep (se 1 (by rfl) ⟨699614, by rfl⟩ : syracuseStep 932819 = 1399229) B1399229
theorem B932835 : Blo 932582 932835 := bstep (se 1 (by rfl) ⟨699626, by rfl⟩ : syracuseStep 932835 = 1399253) B1399253
theorem B2243555 : Blo 932582 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B3783665 : Blo 932582 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B932851 : Blo 932582 932851 := bstep (se 1 (by rfl) ⟨699638, by rfl⟩ : syracuseStep 932851 = 1399277) B1399277
theorem B932867 : Blo 932582 932867 := bstep (se 1 (by rfl) ⟨699650, by rfl⟩ : syracuseStep 932867 = 1399301) B1399301
theorem B932883 : Blo 932582 932883 := bstep (se 1 (by rfl) ⟨699662, by rfl⟩ : syracuseStep 932883 = 1399325) B1399325
theorem B932899 : Blo 932582 932899 := bstep (se 1 (by rfl) ⟨699674, by rfl⟩ : syracuseStep 932899 = 1399349) B1399349
theorem B932915 : Blo 932582 932915 := bstep (se 1 (by rfl) ⟨699686, by rfl⟩ : syracuseStep 932915 = 1399373) B1399373
theorem B932931 : Blo 932582 932931 := bstep (se 1 (by rfl) ⟨699698, by rfl⟩ : syracuseStep 932931 = 1399397) B1399397
theorem B932947 : Blo 932582 932947 := bstep (se 1 (by rfl) ⟨699710, by rfl⟩ : syracuseStep 932947 = 1399421) B1399421
theorem B932963 : Blo 932582 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B932979 : Blo 932582 932979 := bstep (se 1 (by rfl) ⟨699734, by rfl⟩ : syracuseStep 932979 = 1399469) B1399469
theorem B932995 : Blo 932582 932995 := bstep (se 1 (by rfl) ⟨699746, by rfl⟩ : syracuseStep 932995 = 1399493) B1399493
theorem B933011 : Blo 932582 933011 := bstep (se 1 (by rfl) ⟨699758, by rfl⟩ : syracuseStep 933011 = 1399517) B1399517
theorem B1064083 : Blo 932582 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B933027 : Blo 932582 933027 := bstep (se 1 (by rfl) ⟨699770, by rfl⟩ : syracuseStep 933027 = 1399541) B1399541
theorem B933043 : Blo 932582 933043 := bstep (se 1 (by rfl) ⟨699782, by rfl⟩ : syracuseStep 933043 = 1399565) B1399565
theorem B933059 : Blo 932582 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B15154373 : Blo 932582 15154373 := bstep (se 4 (by rfl) ⟨1420722, by rfl⟩ : syracuseStep 15154373 = 2841445) B2841445
theorem B933075 : Blo 932582 933075 := bstep (se 1 (by rfl) ⟨699806, by rfl⟩ : syracuseStep 933075 = 1399613) B1399613
theorem B933091 : Blo 932582 933091 := bstep (se 1 (by rfl) ⟨699818, by rfl⟩ : syracuseStep 933091 = 1399637) B1399637
theorem B1260785 : Blo 932582 1260785 := bstep (se 2 (by rfl) ⟨472794, by rfl⟩ : syracuseStep 1260785 = 945589) B945589
theorem B2243825 : Blo 932582 2243825 := bstep (se 2 (by rfl) ⟨841434, by rfl⟩ : syracuseStep 2243825 = 1682869) B1682869
theorem B933107 : Blo 932582 933107 := bstep (se 1 (by rfl) ⟨699830, by rfl⟩ : syracuseStep 933107 = 1399661) B1399661
theorem B933123 : Blo 932582 933123 := bstep (se 1 (by rfl) ⟨699842, by rfl⟩ : syracuseStep 933123 = 1399685) B1399685
theorem B933139 : Blo 932582 933139 := bstep (se 1 (by rfl) ⟨699854, by rfl⟩ : syracuseStep 933139 = 1399709) B1399709
theorem B933155 : Blo 932582 933155 := bstep (se 1 (by rfl) ⟨699866, by rfl⟩ : syracuseStep 933155 = 1399733) B1399733
theorem B933171 : Blo 932582 933171 := bstep (se 1 (by rfl) ⟨699878, by rfl⟩ : syracuseStep 933171 = 1399757) B1399757
theorem B10665269 : Blo 932582 10665269 := bstep (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) B999869
theorem B933187 : Blo 932582 933187 := bstep (se 1 (by rfl) ⟨699890, by rfl⟩ : syracuseStep 933187 = 1399781) B1399781
theorem B933203 : Blo 932582 933203 := bstep (se 1 (by rfl) ⟨699902, by rfl⟩ : syracuseStep 933203 = 1399805) B1399805
theorem B933219 : Blo 932582 933219 := bstep (se 1 (by rfl) ⟨699914, by rfl⟩ : syracuseStep 933219 = 1399829) B1399829
theorem B17939825 : Blo 932582 17939825 := bstep (se 2 (by rfl) ⟨6727434, by rfl⟩ : syracuseStep 17939825 = 13454869) B13454869
theorem B933235 : Blo 932582 933235 := bstep (se 1 (by rfl) ⟨699926, by rfl⟩ : syracuseStep 933235 = 1399853) B1399853
theorem B933251 : Blo 932582 933251 := bstep (se 1 (by rfl) ⟨699938, by rfl⟩ : syracuseStep 933251 = 1399877) B1399877
theorem B933267 : Blo 932582 933267 := bstep (se 1 (by rfl) ⟨699950, by rfl⟩ : syracuseStep 933267 = 1399901) B1399901
theorem B933283 : Blo 932582 933283 := bstep (se 1 (by rfl) ⟨699962, by rfl⟩ : syracuseStep 933283 = 1399925) B1399925
theorem B2244017 : Blo 932582 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B933299 : Blo 932582 933299 := bstep (se 1 (by rfl) ⟨699974, by rfl⟩ : syracuseStep 933299 = 1399949) B1399949
theorem B933315 : Blo 932582 933315 := bstep (se 1 (by rfl) ⟨699986, by rfl⟩ : syracuseStep 933315 = 1399973) B1399973
theorem B933331 : Blo 932582 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B933347 : Blo 932582 933347 := bstep (se 1 (by rfl) ⟨700010, by rfl⟩ : syracuseStep 933347 = 1400021) B1400021
theorem B4734449 : Blo 932582 4734449 := bstep (se 2 (by rfl) ⟨1775418, by rfl⟩ : syracuseStep 4734449 = 3550837) B3550837
theorem B933363 : Blo 932582 933363 := bstep (se 1 (by rfl) ⟨700022, by rfl⟩ : syracuseStep 933363 = 1400045) B1400045
theorem B933379 : Blo 932582 933379 := bstep (se 1 (by rfl) ⟨700034, by rfl⟩ : syracuseStep 933379 = 1400069) B1400069
theorem B1687043 : Blo 932582 1687043 := bstep (se 1 (by rfl) ⟨1265282, by rfl⟩ : syracuseStep 1687043 = 2530565) B2530565
theorem B2244113 : Blo 932582 2244113 := bstep (se 2 (by rfl) ⟨841542, by rfl⟩ : syracuseStep 2244113 = 1683085) B1683085
theorem B933395 : Blo 932582 933395 := bstep (se 1 (by rfl) ⟨700046, by rfl⟩ : syracuseStep 933395 = 1400093) B1400093
theorem B933411 : Blo 932582 933411 := bstep (se 1 (by rfl) ⟨700058, by rfl⟩ : syracuseStep 933411 = 1400117) B1400117
theorem B933427 : Blo 932582 933427 := bstep (se 1 (by rfl) ⟨700070, by rfl⟩ : syracuseStep 933427 = 1400141) B1400141
theorem B933443 : Blo 932582 933443 := bstep (se 1 (by rfl) ⟨700082, by rfl⟩ : syracuseStep 933443 = 1400165) B1400165
theorem B933459 : Blo 932582 933459 := bstep (se 1 (by rfl) ⟨700094, by rfl⟩ : syracuseStep 933459 = 1400189) B1400189
theorem B933475 : Blo 932582 933475 := bstep (se 1 (by rfl) ⟨700106, by rfl⟩ : syracuseStep 933475 = 1400213) B1400213
theorem B999011 : Blo 932582 999011 := bstep (se 1 (by rfl) ⟨749258, by rfl⟩ : syracuseStep 999011 = 1498517) B1498517
theorem B933491 : Blo 932582 933491 := bstep (se 1 (by rfl) ⟨700118, by rfl⟩ : syracuseStep 933491 = 1400237) B1400237
theorem B933507 : Blo 932582 933507 := bstep (se 1 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 933507 = 1400261) B1400261
theorem B933523 : Blo 932582 933523 := bstep (se 1 (by rfl) ⟨700142, by rfl⟩ : syracuseStep 933523 = 1400285) B1400285
theorem B933539 : Blo 932582 933539 := bstep (se 1 (by rfl) ⟨700154, by rfl⟩ : syracuseStep 933539 = 1400309) B1400309
theorem B933555 : Blo 932582 933555 := bstep (se 1 (by rfl) ⟨700166, by rfl⟩ : syracuseStep 933555 = 1400333) B1400333
theorem B933571 : Blo 932582 933571 := bstep (se 1 (by rfl) ⟨700178, by rfl⟩ : syracuseStep 933571 = 1400357) B1400357
theorem B933587 : Blo 932582 933587 := bstep (se 1 (by rfl) ⟨700190, by rfl⟩ : syracuseStep 933587 = 1400381) B1400381
theorem B933603 : Blo 932582 933603 := bstep (se 1 (by rfl) ⟨700202, by rfl⟩ : syracuseStep 933603 = 1400405) B1400405
theorem B933619 : Blo 932582 933619 := bstep (se 1 (by rfl) ⟨700214, by rfl⟩ : syracuseStep 933619 = 1400429) B1400429
theorem B933635 : Blo 932582 933635 := bstep (se 1 (by rfl) ⟨700226, by rfl⟩ : syracuseStep 933635 = 1400453) B1400453
theorem B933651 : Blo 932582 933651 := bstep (se 1 (by rfl) ⟨700238, by rfl⟩ : syracuseStep 933651 = 1400477) B1400477
theorem B933667 : Blo 932582 933667 := bstep (se 1 (by rfl) ⟨700250, by rfl⟩ : syracuseStep 933667 = 1400501) B1400501
theorem B1687331 : Blo 932582 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B933683 : Blo 932582 933683 := bstep (se 1 (by rfl) ⟨700262, by rfl⟩ : syracuseStep 933683 = 1400525) B1400525
theorem B933699 : Blo 932582 933699 := bstep (se 1 (by rfl) ⟨700274, by rfl⟩ : syracuseStep 933699 = 1400549) B1400549
theorem B6733637 : Blo 932582 6733637 := bstep (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) B1262557
theorem B2998097 : Blo 932582 2998097 := bstep (se 2 (by rfl) ⟨1124286, by rfl⟩ : syracuseStep 2998097 = 2248573) B2248573
theorem B933715 : Blo 932582 933715 := bstep (se 1 (by rfl) ⟨700286, by rfl⟩ : syracuseStep 933715 = 1400573) B1400573
theorem B933731 : Blo 932582 933731 := bstep (se 1 (by rfl) ⟨700298, by rfl⟩ : syracuseStep 933731 = 1400597) B1400597
theorem B933747 : Blo 932582 933747 := bstep (se 1 (by rfl) ⟨700310, by rfl⟩ : syracuseStep 933747 = 1400621) B1400621
theorem B933763 : Blo 932582 933763 := bstep (se 1 (by rfl) ⟨700322, by rfl⟩ : syracuseStep 933763 = 1400645) B1400645
theorem B933779 : Blo 932582 933779 := bstep (se 1 (by rfl) ⟨700334, by rfl⟩ : syracuseStep 933779 = 1400669) B1400669
theorem B933795 : Blo 932582 933795 := bstep (se 1 (by rfl) ⟨700346, by rfl⟩ : syracuseStep 933795 = 1400693) B1400693
theorem B933811 : Blo 932582 933811 := bstep (se 1 (by rfl) ⟨700358, by rfl⟩ : syracuseStep 933811 = 1400717) B1400717
theorem B933827 : Blo 932582 933827 := bstep (se 1 (by rfl) ⟨700370, by rfl⟩ : syracuseStep 933827 = 1400741) B1400741
theorem B933843 : Blo 932582 933843 := bstep (se 1 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 933843 = 1400765) B1400765
theorem B933859 : Blo 932582 933859 := bstep (se 1 (by rfl) ⟨700394, by rfl⟩ : syracuseStep 933859 = 1400789) B1400789
theorem B933875 : Blo 932582 933875 := bstep (se 1 (by rfl) ⟨700406, by rfl⟩ : syracuseStep 933875 = 1400813) B1400813
theorem B933891 : Blo 932582 933891 := bstep (se 1 (by rfl) ⟨700418, by rfl⟩ : syracuseStep 933891 = 1400837) B1400837
theorem B933907 : Blo 932582 933907 := bstep (se 1 (by rfl) ⟨700430, by rfl⟩ : syracuseStep 933907 = 1400861) B1400861
theorem B1064995 : Blo 932582 1064995 := bstep (se 1 (by rfl) ⟨798746, by rfl⟩ : syracuseStep 1064995 = 1597493) B1597493
theorem B933923 : Blo 932582 933923 := bstep (se 1 (by rfl) ⟨700442, by rfl⟩ : syracuseStep 933923 = 1400885) B1400885
theorem B933939 : Blo 932582 933939 := bstep (se 1 (by rfl) ⟨700454, by rfl⟩ : syracuseStep 933939 = 1400909) B1400909
theorem B933955 : Blo 932582 933955 := bstep (se 1 (by rfl) ⟨700466, by rfl⟩ : syracuseStep 933955 = 1400933) B1400933
theorem B933971 : Blo 932582 933971 := bstep (se 1 (by rfl) ⟨700478, by rfl⟩ : syracuseStep 933971 = 1400957) B1400957
theorem B933987 : Blo 932582 933987 := bstep (se 1 (by rfl) ⟨700490, by rfl⟩ : syracuseStep 933987 = 1400981) B1400981
theorem B934003 : Blo 932582 934003 := bstep (se 1 (by rfl) ⟨700502, by rfl⟩ : syracuseStep 934003 = 1401005) B1401005
theorem B1261697 : Blo 932582 1261697 := bstep (se 2 (by rfl) ⟨473136, by rfl⟩ : syracuseStep 1261697 = 946273) B946273
theorem B934019 : Blo 932582 934019 := bstep (se 1 (by rfl) ⟨700514, by rfl⟩ : syracuseStep 934019 = 1401029) B1401029
theorem B934035 : Blo 932582 934035 := bstep (se 1 (by rfl) ⟨700526, by rfl⟩ : syracuseStep 934035 = 1401053) B1401053
theorem B934051 : Blo 932582 934051 := bstep (se 1 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 934051 = 1401077) B1401077
theorem B2277539 : Blo 932582 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B934067 : Blo 932582 934067 := bstep (se 1 (by rfl) ⟨700550, by rfl⟩ : syracuseStep 934067 = 1401101) B1401101
theorem B934083 : Blo 932582 934083 := bstep (se 1 (by rfl) ⟨700562, by rfl⟩ : syracuseStep 934083 = 1401125) B1401125
theorem B934099 : Blo 932582 934099 := bstep (se 1 (by rfl) ⟨700574, by rfl⟩ : syracuseStep 934099 = 1401149) B1401149
theorem B934115 : Blo 932582 934115 := bstep (se 1 (by rfl) ⟨700586, by rfl⟩ : syracuseStep 934115 = 1401173) B1401173
theorem B8110307 : Blo 932582 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B934131 : Blo 932582 934131 := bstep (se 1 (by rfl) ⟨700598, by rfl⟩ : syracuseStep 934131 = 1401197) B1401197
theorem B934147 : Blo 932582 934147 := bstep (se 1 (by rfl) ⟨700610, by rfl⟩ : syracuseStep 934147 = 1401221) B1401221
theorem B934163 : Blo 932582 934163 := bstep (se 1 (by rfl) ⟨700622, by rfl⟩ : syracuseStep 934163 = 1401245) B1401245
theorem B934179 : Blo 932582 934179 := bstep (se 1 (by rfl) ⟨700634, by rfl⟩ : syracuseStep 934179 = 1401269) B1401269
theorem B934195 : Blo 932582 934195 := bstep (se 1 (by rfl) ⟨700646, by rfl⟩ : syracuseStep 934195 = 1401293) B1401293
theorem B934211 : Blo 932582 934211 := bstep (se 1 (by rfl) ⟨700658, by rfl⟩ : syracuseStep 934211 = 1401317) B1401317
theorem B934227 : Blo 932582 934227 := bstep (se 1 (by rfl) ⟨700670, by rfl⟩ : syracuseStep 934227 = 1401341) B1401341
theorem B934243 : Blo 932582 934243 := bstep (se 1 (by rfl) ⟨700682, by rfl⟩ : syracuseStep 934243 = 1401365) B1401365
theorem B7094627 : Blo 932582 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B3555683 : Blo 932582 3555683 := bstep (se 1 (by rfl) ⟨2666762, by rfl⟩ : syracuseStep 3555683 = 5333525) B5333525
theorem B3555697 : Blo 932582 3555697 := bstep (se 2 (by rfl) ⟨1333386, by rfl⟩ : syracuseStep 3555697 = 2666773) B2666773
theorem B934259 : Blo 932582 934259 := bstep (se 1 (by rfl) ⟨700694, by rfl⟩ : syracuseStep 934259 = 1401389) B1401389
theorem B934275 : Blo 932582 934275 := bstep (se 1 (by rfl) ⟨700706, by rfl⟩ : syracuseStep 934275 = 1401413) B1401413
theorem B934291 : Blo 932582 934291 := bstep (se 1 (by rfl) ⟨700718, by rfl⟩ : syracuseStep 934291 = 1401437) B1401437
theorem B934307 : Blo 932582 934307 := bstep (se 1 (by rfl) ⟨700730, by rfl⟩ : syracuseStep 934307 = 1401461) B1401461
theorem B934323 : Blo 932582 934323 := bstep (se 1 (by rfl) ⟨700742, by rfl⟩ : syracuseStep 934323 = 1401485) B1401485
theorem B934339 : Blo 932582 934339 := bstep (se 1 (by rfl) ⟨700754, by rfl⟩ : syracuseStep 934339 = 1401509) B1401509
theorem B934355 : Blo 932582 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B934371 : Blo 932582 934371 := bstep (se 1 (by rfl) ⟨700778, by rfl⟩ : syracuseStep 934371 = 1401557) B1401557
theorem B934387 : Blo 932582 934387 := bstep (se 1 (by rfl) ⟨700790, by rfl⟩ : syracuseStep 934387 = 1401581) B1401581
theorem B934403 : Blo 932582 934403 := bstep (se 1 (by rfl) ⟨700802, by rfl⟩ : syracuseStep 934403 = 1401605) B1401605
theorem B2998787 : Blo 932582 2998787 := bstep (se 1 (by rfl) ⟨2249090, by rfl⟩ : syracuseStep 2998787 = 4498181) B4498181
theorem B934419 : Blo 932582 934419 := bstep (se 1 (by rfl) ⟨700814, by rfl⟩ : syracuseStep 934419 = 1401629) B1401629
theorem B999955 : Blo 932582 999955 := bstep (se 1 (by rfl) ⟨749966, by rfl⟩ : syracuseStep 999955 = 1499933) B1499933
theorem B934435 : Blo 932582 934435 := bstep (se 1 (by rfl) ⟨700826, by rfl⟩ : syracuseStep 934435 = 1401653) B1401653
theorem B934451 : Blo 932582 934451 := bstep (se 1 (by rfl) ⟨700838, by rfl⟩ : syracuseStep 934451 = 1401677) B1401677
theorem B934467 : Blo 932582 934467 := bstep (se 1 (by rfl) ⟨700850, by rfl⟩ : syracuseStep 934467 = 1401701) B1401701
theorem B934483 : Blo 932582 934483 := bstep (se 1 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 934483 = 1401725) B1401725
theorem B934499 : Blo 932582 934499 := bstep (se 1 (by rfl) ⟨700874, by rfl⟩ : syracuseStep 934499 = 1401749) B1401749
theorem B934515 : Blo 932582 934515 := bstep (se 1 (by rfl) ⟨700886, by rfl⟩ : syracuseStep 934515 = 1401773) B1401773
theorem B934531 : Blo 932582 934531 := bstep (se 1 (by rfl) ⟨700898, by rfl⟩ : syracuseStep 934531 = 1401797) B1401797
theorem B934547 : Blo 932582 934547 := bstep (se 1 (by rfl) ⟨700910, by rfl⟩ : syracuseStep 934547 = 1401821) B1401821
theorem B934563 : Blo 932582 934563 := bstep (se 1 (by rfl) ⟨700922, by rfl⟩ : syracuseStep 934563 = 1401845) B1401845
theorem B934579 : Blo 932582 934579 := bstep (se 1 (by rfl) ⟨700934, by rfl⟩ : syracuseStep 934579 = 1401869) B1401869
theorem B2245315 : Blo 932582 2245315 := bstep (se 1 (by rfl) ⟨1683986, by rfl⟩ : syracuseStep 2245315 = 3367973) B3367973
theorem B934595 : Blo 932582 934595 := bstep (se 1 (by rfl) ⟨700946, by rfl⟩ : syracuseStep 934595 = 1401893) B1401893
theorem B934611 : Blo 932582 934611 := bstep (se 1 (by rfl) ⟨700958, by rfl⟩ : syracuseStep 934611 = 1401917) B1401917
theorem B934627 : Blo 932582 934627 := bstep (se 1 (by rfl) ⟨700970, by rfl⟩ : syracuseStep 934627 = 1401941) B1401941
theorem B4801265 : Blo 932582 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B934643 : Blo 932582 934643 := bstep (se 1 (by rfl) ⟨700982, by rfl⟩ : syracuseStep 934643 = 1401965) B1401965
theorem B934659 : Blo 932582 934659 := bstep (se 1 (by rfl) ⟨700994, by rfl⟩ : syracuseStep 934659 = 1401989) B1401989
theorem B934675 : Blo 932582 934675 := bstep (se 1 (by rfl) ⟨701006, by rfl⟩ : syracuseStep 934675 = 1402013) B1402013
theorem B934691 : Blo 932582 934691 := bstep (se 1 (by rfl) ⟨701018, by rfl⟩ : syracuseStep 934691 = 1402037) B1402037
theorem B934707 : Blo 932582 934707 := bstep (se 1 (by rfl) ⟨701030, by rfl⟩ : syracuseStep 934707 = 1402061) B1402061
theorem B934723 : Blo 932582 934723 := bstep (se 1 (by rfl) ⟨701042, by rfl⟩ : syracuseStep 934723 = 1402085) B1402085
theorem B934739 : Blo 932582 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B934755 : Blo 932582 934755 := bstep (se 1 (by rfl) ⟨701066, by rfl⟩ : syracuseStep 934755 = 1402133) B1402133
theorem B1622897 : Blo 932582 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B934771 : Blo 932582 934771 := bstep (se 1 (by rfl) ⟨701078, by rfl⟩ : syracuseStep 934771 = 1402157) B1402157
theorem B934787 : Blo 932582 934787 := bstep (se 1 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 934787 = 1402181) B1402181
theorem B5325709 : Blo 932582 5325709 := bstep (se 3 (by rfl) ⟨998570, by rfl⟩ : syracuseStep 5325709 = 1997141) B1997141
theorem B934803 : Blo 932582 934803 := bstep (se 1 (by rfl) ⟨701102, by rfl⟩ : syracuseStep 934803 = 1402205) B1402205
theorem B1328033 : Blo 932582 1328033 := bstep (se 2 (by rfl) ⟨498012, by rfl⟩ : syracuseStep 1328033 = 996025) B996025
theorem B934819 : Blo 932582 934819 := bstep (se 1 (by rfl) ⟨701114, by rfl⟩ : syracuseStep 934819 = 1402229) B1402229
theorem B4735907 : Blo 932582 4735907 := bstep (se 1 (by rfl) ⟨3551930, by rfl⟩ : syracuseStep 4735907 = 7103861) B7103861
theorem B934835 : Blo 932582 934835 := bstep (se 1 (by rfl) ⟨701126, by rfl⟩ : syracuseStep 934835 = 1402253) B1402253
theorem B934851 : Blo 932582 934851 := bstep (se 1 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 934851 = 1402277) B1402277
theorem B2737091 : Blo 932582 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B934867 : Blo 932582 934867 := bstep (se 1 (by rfl) ⟨701150, by rfl⟩ : syracuseStep 934867 = 1402301) B1402301
theorem B934883 : Blo 932582 934883 := bstep (se 1 (by rfl) ⟨701162, by rfl⟩ : syracuseStep 934883 = 1402325) B1402325
theorem B1328113 : Blo 932582 1328113 := bstep (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) B996085
theorem B934899 : Blo 932582 934899 := bstep (se 1 (by rfl) ⟨701174, by rfl⟩ : syracuseStep 934899 = 1402349) B1402349
theorem B934915 : Blo 932582 934915 := bstep (se 1 (by rfl) ⟨701186, by rfl⟩ : syracuseStep 934915 = 1402373) B1402373
theorem B934931 : Blo 932582 934931 := bstep (se 1 (by rfl) ⟨701198, by rfl⟩ : syracuseStep 934931 = 1402397) B1402397
theorem B934947 : Blo 932582 934947 := bstep (se 1 (by rfl) ⟨701210, by rfl⟩ : syracuseStep 934947 = 1402421) B1402421
theorem B934963 : Blo 932582 934963 := bstep (se 1 (by rfl) ⟨701222, by rfl⟩ : syracuseStep 934963 = 1402445) B1402445
theorem B934979 : Blo 932582 934979 := bstep (se 1 (by rfl) ⟨701234, by rfl⟩ : syracuseStep 934979 = 1402469) B1402469
theorem B934995 : Blo 932582 934995 := bstep (se 1 (by rfl) ⟨701246, by rfl⟩ : syracuseStep 934995 = 1402493) B1402493
theorem B935011 : Blo 932582 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B935027 : Blo 932582 935027 := bstep (se 1 (by rfl) ⟨701270, by rfl⟩ : syracuseStep 935027 = 1402541) B1402541
theorem B935043 : Blo 932582 935043 := bstep (se 1 (by rfl) ⟨701282, by rfl⟩ : syracuseStep 935043 = 1402565) B1402565
theorem B935059 : Blo 932582 935059 := bstep (se 1 (by rfl) ⟨701294, by rfl⟩ : syracuseStep 935059 = 1402589) B1402589
theorem B935075 : Blo 932582 935075 := bstep (se 1 (by rfl) ⟨701306, by rfl⟩ : syracuseStep 935075 = 1402613) B1402613
theorem B935091 : Blo 932582 935091 := bstep (se 1 (by rfl) ⟨701318, by rfl⟩ : syracuseStep 935091 = 1402637) B1402637
theorem B935107 : Blo 932582 935107 := bstep (se 1 (by rfl) ⟨701330, by rfl⟩ : syracuseStep 935107 = 1402661) B1402661
theorem B935123 : Blo 932582 935123 := bstep (se 1 (by rfl) ⟨701342, by rfl⟩ : syracuseStep 935123 = 1402685) B1402685
theorem B935139 : Blo 932582 935139 := bstep (se 1 (by rfl) ⟨701354, by rfl⟩ : syracuseStep 935139 = 1402709) B1402709
theorem B1197299 : Blo 932582 1197299 := bstep (se 1 (by rfl) ⟨897974, by rfl⟩ : syracuseStep 1197299 = 1795949) B1795949
theorem B935155 : Blo 932582 935155 := bstep (se 1 (by rfl) ⟨701366, by rfl⟩ : syracuseStep 935155 = 1402733) B1402733
theorem B935171 : Blo 932582 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B935187 : Blo 932582 935187 := bstep (se 1 (by rfl) ⟨701390, by rfl⟩ : syracuseStep 935187 = 1402781) B1402781
theorem B935203 : Blo 932582 935203 := bstep (se 1 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 935203 = 1402805) B1402805
theorem B935219 : Blo 932582 935219 := bstep (se 1 (by rfl) ⟨701414, by rfl⟩ : syracuseStep 935219 = 1402829) B1402829
theorem B935235 : Blo 932582 935235 := bstep (se 1 (by rfl) ⟨701426, by rfl⟩ : syracuseStep 935235 = 1402853) B1402853
theorem B935251 : Blo 932582 935251 := bstep (se 1 (by rfl) ⟨701438, by rfl⟩ : syracuseStep 935251 = 1402877) B1402877
theorem B935267 : Blo 932582 935267 := bstep (se 1 (by rfl) ⟨701450, by rfl⟩ : syracuseStep 935267 = 1402901) B1402901
theorem B935283 : Blo 932582 935283 := bstep (se 1 (by rfl) ⟨701462, by rfl⟩ : syracuseStep 935283 = 1402925) B1402925
theorem B935299 : Blo 932582 935299 := bstep (se 1 (by rfl) ⟨701474, by rfl⟩ : syracuseStep 935299 = 1402949) B1402949
theorem B935315 : Blo 932582 935315 := bstep (se 1 (by rfl) ⟨701486, by rfl⟩ : syracuseStep 935315 = 1402973) B1402973
theorem B935331 : Blo 932582 935331 := bstep (se 1 (by rfl) ⟨701498, by rfl⟩ : syracuseStep 935331 = 1402997) B1402997
theorem B935347 : Blo 932582 935347 := bstep (se 1 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 935347 = 1403021) B1403021
theorem B935363 : Blo 932582 935363 := bstep (se 1 (by rfl) ⟨701522, by rfl⟩ : syracuseStep 935363 = 1403045) B1403045
theorem B935379 : Blo 932582 935379 := bstep (se 1 (by rfl) ⟨701534, by rfl⟩ : syracuseStep 935379 = 1403069) B1403069
theorem B935395 : Blo 932582 935395 := bstep (se 1 (by rfl) ⟨701546, by rfl⟩ : syracuseStep 935395 = 1403093) B1403093
theorem B935411 : Blo 932582 935411 := bstep (se 1 (by rfl) ⟨701558, by rfl⟩ : syracuseStep 935411 = 1403117) B1403117
theorem B935427 : Blo 932582 935427 := bstep (se 1 (by rfl) ⟨701570, by rfl⟩ : syracuseStep 935427 = 1403141) B1403141
theorem B935443 : Blo 932582 935443 := bstep (se 1 (by rfl) ⟨701582, by rfl⟩ : syracuseStep 935443 = 1403165) B1403165
theorem B935459 : Blo 932582 935459 := bstep (se 1 (by rfl) ⟨701594, by rfl⟩ : syracuseStep 935459 = 1403189) B1403189
theorem B935475 : Blo 932582 935475 := bstep (se 1 (by rfl) ⟨701606, by rfl⟩ : syracuseStep 935475 = 1403213) B1403213
theorem B935491 : Blo 932582 935491 := bstep (se 1 (by rfl) ⟨701618, by rfl⟩ : syracuseStep 935491 = 1403237) B1403237
theorem B935507 : Blo 932582 935507 := bstep (se 1 (by rfl) ⟨701630, by rfl⟩ : syracuseStep 935507 = 1403261) B1403261
theorem B935523 : Blo 932582 935523 := bstep (se 1 (by rfl) ⟨701642, by rfl⟩ : syracuseStep 935523 = 1403285) B1403285
theorem B935539 : Blo 932582 935539 := bstep (se 1 (by rfl) ⟨701654, by rfl⟩ : syracuseStep 935539 = 1403309) B1403309
theorem B935555 : Blo 932582 935555 := bstep (se 1 (by rfl) ⟨701666, by rfl⟩ : syracuseStep 935555 = 1403333) B1403333
theorem B935571 : Blo 932582 935571 := bstep (se 1 (by rfl) ⟨701678, by rfl⟩ : syracuseStep 935571 = 1403357) B1403357
theorem B935587 : Blo 932582 935587 := bstep (se 1 (by rfl) ⟨701690, by rfl⟩ : syracuseStep 935587 = 1403381) B1403381
theorem B935603 : Blo 932582 935603 := bstep (se 1 (by rfl) ⟨701702, by rfl⟩ : syracuseStep 935603 = 1403405) B1403405
theorem B935619 : Blo 932582 935619 := bstep (se 1 (by rfl) ⟨701714, by rfl⟩ : syracuseStep 935619 = 1403429) B1403429
theorem B4736717 : Blo 932582 4736717 := bstep (se 3 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 4736717 = 1776269) B1776269
theorem B935635 : Blo 932582 935635 := bstep (se 1 (by rfl) ⟨701726, by rfl⟩ : syracuseStep 935635 = 1403453) B1403453
theorem B935651 : Blo 932582 935651 := bstep (se 1 (by rfl) ⟨701738, by rfl⟩ : syracuseStep 935651 = 1403477) B1403477
theorem B935667 : Blo 932582 935667 := bstep (se 1 (by rfl) ⟨701750, by rfl⟩ : syracuseStep 935667 = 1403501) B1403501
theorem B1328899 : Blo 932582 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B935683 : Blo 932582 935683 := bstep (se 1 (by rfl) ⟨701762, by rfl⟩ : syracuseStep 935683 = 1403525) B1403525
theorem B935699 : Blo 932582 935699 := bstep (se 1 (by rfl) ⟨701774, by rfl⟩ : syracuseStep 935699 = 1403549) B1403549
theorem B935715 : Blo 932582 935715 := bstep (se 1 (by rfl) ⟨701786, by rfl⟩ : syracuseStep 935715 = 1403573) B1403573
theorem B935731 : Blo 932582 935731 := bstep (se 1 (by rfl) ⟨701798, by rfl⟩ : syracuseStep 935731 = 1403597) B1403597
theorem B935747 : Blo 932582 935747 := bstep (se 1 (by rfl) ⟨701810, by rfl⟩ : syracuseStep 935747 = 1403621) B1403621
theorem B935763 : Blo 932582 935763 := bstep (se 1 (by rfl) ⟨701822, by rfl⟩ : syracuseStep 935763 = 1403645) B1403645
theorem B935779 : Blo 932582 935779 := bstep (se 1 (by rfl) ⟨701834, by rfl⟩ : syracuseStep 935779 = 1403669) B1403669
theorem B935795 : Blo 932582 935795 := bstep (se 1 (by rfl) ⟨701846, by rfl⟩ : syracuseStep 935795 = 1403693) B1403693
theorem B935811 : Blo 932582 935811 := bstep (se 1 (by rfl) ⟨701858, by rfl⟩ : syracuseStep 935811 = 1403717) B1403717
theorem B2246545 : Blo 932582 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B935827 : Blo 932582 935827 := bstep (se 1 (by rfl) ⟨701870, by rfl⟩ : syracuseStep 935827 = 1403741) B1403741
theorem B935843 : Blo 932582 935843 := bstep (se 1 (by rfl) ⟨701882, by rfl⟩ : syracuseStep 935843 = 1403765) B1403765
theorem B935859 : Blo 932582 935859 := bstep (se 1 (by rfl) ⟨701894, by rfl⟩ : syracuseStep 935859 = 1403789) B1403789
theorem B935875 : Blo 932582 935875 := bstep (se 1 (by rfl) ⟨701906, by rfl⟩ : syracuseStep 935875 = 1403813) B1403813
theorem B5392325 : Blo 932582 5392325 := bstep (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) B1011061
theorem B935891 : Blo 932582 935891 := bstep (se 1 (by rfl) ⟨701918, by rfl⟩ : syracuseStep 935891 = 1403837) B1403837
theorem B935907 : Blo 932582 935907 := bstep (se 1 (by rfl) ⟨701930, by rfl⟩ : syracuseStep 935907 = 1403861) B1403861
theorem B935923 : Blo 932582 935923 := bstep (se 1 (by rfl) ⟨701942, by rfl⟩ : syracuseStep 935923 = 1403885) B1403885
theorem B935939 : Blo 932582 935939 := bstep (se 1 (by rfl) ⟨701954, by rfl⟩ : syracuseStep 935939 = 1403909) B1403909
theorem B935955 : Blo 932582 935955 := bstep (se 1 (by rfl) ⟨701966, by rfl⟩ : syracuseStep 935955 = 1403933) B1403933
theorem B935971 : Blo 932582 935971 := bstep (se 1 (by rfl) ⟨701978, by rfl⟩ : syracuseStep 935971 = 1403957) B1403957
theorem B935987 : Blo 932582 935987 := bstep (se 1 (by rfl) ⟨701990, by rfl⟩ : syracuseStep 935987 = 1403981) B1403981
theorem B936003 : Blo 932582 936003 := bstep (se 1 (by rfl) ⟨702002, by rfl⟩ : syracuseStep 936003 = 1404005) B1404005
theorem B936019 : Blo 932582 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B936035 : Blo 932582 936035 := bstep (se 1 (by rfl) ⟨702026, by rfl⟩ : syracuseStep 936035 = 1404053) B1404053
theorem B936051 : Blo 932582 936051 := bstep (se 1 (by rfl) ⟨702038, by rfl⟩ : syracuseStep 936051 = 1404077) B1404077
theorem B936067 : Blo 932582 936067 := bstep (se 1 (by rfl) ⟨702050, by rfl⟩ : syracuseStep 936067 = 1404101) B1404101
theorem B936083 : Blo 932582 936083 := bstep (se 1 (by rfl) ⟨702062, by rfl⟩ : syracuseStep 936083 = 1404125) B1404125
theorem B936099 : Blo 932582 936099 := bstep (se 1 (by rfl) ⟨702074, by rfl⟩ : syracuseStep 936099 = 1404149) B1404149
theorem B936115 : Blo 932582 936115 := bstep (se 1 (by rfl) ⟨702086, by rfl⟩ : syracuseStep 936115 = 1404173) B1404173
theorem B936131 : Blo 932582 936131 := bstep (se 1 (by rfl) ⟨702098, by rfl⟩ : syracuseStep 936131 = 1404197) B1404197
theorem B7981253 : Blo 932582 7981253 := bstep (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) B1496485
theorem B936147 : Blo 932582 936147 := bstep (se 1 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 936147 = 1404221) B1404221
theorem B1329377 : Blo 932582 1329377 := bstep (se 2 (by rfl) ⟨498516, by rfl⟩ : syracuseStep 1329377 = 997033) B997033
theorem B936163 : Blo 932582 936163 := bstep (se 1 (by rfl) ⟨702122, by rfl⟩ : syracuseStep 936163 = 1404245) B1404245
theorem B936179 : Blo 932582 936179 := bstep (se 1 (by rfl) ⟨702134, by rfl⟩ : syracuseStep 936179 = 1404269) B1404269
theorem B936195 : Blo 932582 936195 := bstep (se 1 (by rfl) ⟨702146, by rfl⟩ : syracuseStep 936195 = 1404293) B1404293
theorem B2738449 : Blo 932582 2738449 := bstep (se 2 (by rfl) ⟨1026918, by rfl⟩ : syracuseStep 2738449 = 2053837) B2053837
theorem B936211 : Blo 932582 936211 := bstep (se 1 (by rfl) ⟨702158, by rfl⟩ : syracuseStep 936211 = 1404317) B1404317
theorem B936227 : Blo 932582 936227 := bstep (se 1 (by rfl) ⟨702170, by rfl⟩ : syracuseStep 936227 = 1404341) B1404341
theorem B936243 : Blo 932582 936243 := bstep (se 1 (by rfl) ⟨702182, by rfl⟩ : syracuseStep 936243 = 1404365) B1404365
theorem B936259 : Blo 932582 936259 := bstep (se 1 (by rfl) ⟨702194, by rfl⟩ : syracuseStep 936259 = 1404389) B1404389
theorem B1329491 : Blo 932582 1329491 := bstep (se 1 (by rfl) ⟨997118, by rfl⟩ : syracuseStep 1329491 = 1994237) B1994237
theorem B936275 : Blo 932582 936275 := bstep (se 1 (by rfl) ⟨702206, by rfl⟩ : syracuseStep 936275 = 1404413) B1404413
theorem B3361123 : Blo 932582 3361123 := bstep (se 1 (by rfl) ⟨2520842, by rfl⟩ : syracuseStep 3361123 = 5041685) B5041685
theorem B936291 : Blo 932582 936291 := bstep (se 1 (by rfl) ⟨702218, by rfl⟩ : syracuseStep 936291 = 1404437) B1404437
theorem B936307 : Blo 932582 936307 := bstep (se 1 (by rfl) ⟨702230, by rfl⟩ : syracuseStep 936307 = 1404461) B1404461
theorem B936323 : Blo 932582 936323 := bstep (se 1 (by rfl) ⟨702242, by rfl⟩ : syracuseStep 936323 = 1404485) B1404485
theorem B936339 : Blo 932582 936339 := bstep (se 1 (by rfl) ⟨702254, by rfl⟩ : syracuseStep 936339 = 1404509) B1404509
theorem B1329571 : Blo 932582 1329571 := bstep (se 1 (by rfl) ⟨997178, by rfl⟩ : syracuseStep 1329571 = 1994357) B1994357
theorem B936355 : Blo 932582 936355 := bstep (se 1 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 936355 = 1404533) B1404533
theorem B936371 : Blo 932582 936371 := bstep (se 1 (by rfl) ⟨702278, by rfl⟩ : syracuseStep 936371 = 1404557) B1404557
theorem B936387 : Blo 932582 936387 := bstep (se 1 (by rfl) ⟨702290, by rfl⟩ : syracuseStep 936387 = 1404581) B1404581
theorem B936403 : Blo 932582 936403 := bstep (se 1 (by rfl) ⟨702302, by rfl⟩ : syracuseStep 936403 = 1404605) B1404605
theorem B936419 : Blo 932582 936419 := bstep (se 1 (by rfl) ⟨702314, by rfl⟩ : syracuseStep 936419 = 1404629) B1404629
theorem B936435 : Blo 932582 936435 := bstep (se 1 (by rfl) ⟨702326, by rfl⟩ : syracuseStep 936435 = 1404653) B1404653
theorem B936451 : Blo 932582 936451 := bstep (se 1 (by rfl) ⟨702338, by rfl⟩ : syracuseStep 936451 = 1404677) B1404677
theorem B936467 : Blo 932582 936467 := bstep (se 1 (by rfl) ⟨702350, by rfl⟩ : syracuseStep 936467 = 1404701) B1404701
theorem B936483 : Blo 932582 936483 := bstep (se 1 (by rfl) ⟨702362, by rfl⟩ : syracuseStep 936483 = 1404725) B1404725
theorem B936499 : Blo 932582 936499 := bstep (se 1 (by rfl) ⟨702374, by rfl⟩ : syracuseStep 936499 = 1404749) B1404749
theorem B936515 : Blo 932582 936515 := bstep (se 1 (by rfl) ⟨702386, by rfl⟩ : syracuseStep 936515 = 1404773) B1404773
theorem B936531 : Blo 932582 936531 := bstep (se 1 (by rfl) ⟨702398, by rfl⟩ : syracuseStep 936531 = 1404797) B1404797
theorem B936547 : Blo 932582 936547 := bstep (se 1 (by rfl) ⟨702410, by rfl⟩ : syracuseStep 936547 = 1404821) B1404821
theorem B936563 : Blo 932582 936563 := bstep (se 1 (by rfl) ⟨702422, by rfl⟩ : syracuseStep 936563 = 1404845) B1404845
theorem B936579 : Blo 932582 936579 := bstep (se 1 (by rfl) ⟨702434, by rfl⟩ : syracuseStep 936579 = 1404869) B1404869
theorem B5327693 : Blo 932582 5327693 := bstep (se 3 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 5327693 = 1997885) B1997885
theorem B1264465 : Blo 932582 1264465 := bstep (se 2 (by rfl) ⟨474174, by rfl⟩ : syracuseStep 1264465 = 948349) B948349
theorem B1330129 : Blo 932582 1330129 := bstep (se 2 (by rfl) ⟨498798, by rfl⟩ : syracuseStep 1330129 = 997597) B997597
theorem B1494371 : Blo 932582 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B1330835 : Blo 932582 1330835 := bstep (se 1 (by rfl) ⟨998126, by rfl⟩ : syracuseStep 1330835 = 1996253) B1996253
theorem B5328625 : Blo 932582 5328625 := bstep (se 2 (by rfl) ⟨1998234, by rfl⟩ : syracuseStep 5328625 = 3996469) B3996469
theorem B1494883 : Blo 932582 1494883 := bstep (se 1 (by rfl) ⟨1121162, by rfl⟩ : syracuseStep 1494883 = 2242325) B2242325
theorem B1494929 : Blo 932582 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B30363761 : Blo 932582 30363761 := bstep (se 2 (by rfl) ⟨11386410, by rfl⟩ : syracuseStep 30363761 = 22772821) B22772821
theorem B4313357 : Blo 932582 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B1331473 : Blo 932582 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B1331587 : Blo 932582 1331587 := bstep (se 1 (by rfl) ⟨998690, by rfl⟩ : syracuseStep 1331587 = 1997381) B1997381
theorem B8999437 : Blo 932582 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B1495601 : Blo 932582 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B4739633 : Blo 932582 4739633 := bstep (se 2 (by rfl) ⟨1777362, by rfl⟩ : syracuseStep 4739633 = 3554725) B3554725
theorem B5755697 : Blo 932582 5755697 := bstep (se 2 (by rfl) ⟨2158386, by rfl⟩ : syracuseStep 5755697 = 4316773) B4316773
theorem B2839427 : Blo 932582 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B5985251 : Blo 932582 5985251 := bstep (se 1 (by rfl) ⟨4488938, by rfl⟩ : syracuseStep 5985251 = 8977877) B8977877
theorem B1922051 : Blo 932582 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B1496113 : Blo 932582 1496113 := bstep (se 2 (by rfl) ⟨561042, by rfl⟩ : syracuseStep 1496113 = 1122085) B1122085
theorem B3200077 : Blo 932582 3200077 := bstep (se 3 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 3200077 = 1200029) B1200029
theorem B5330083 : Blo 932582 5330083 := bstep (se 1 (by rfl) ⟨3997562, by rfl⟩ : syracuseStep 5330083 = 7995125) B7995125
theorem B3986765 : Blo 932582 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B7099973 : Blo 932582 7099973 := bstep (se 4 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 7099973 = 1331245) B1331245
theorem B3987107 : Blo 932582 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B5330609 : Blo 932582 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B1332931 : Blo 932582 1332931 := bstep (se 1 (by rfl) ⟨999698, by rfl⟩ : syracuseStep 1332931 = 1999397) B1999397
theorem B4741091 : Blo 932582 4741091 := bstep (se 1 (by rfl) ⟨3555818, by rfl⟩ : syracuseStep 4741091 = 7111637) B7111637
theorem B3201005 : Blo 932582 3201005 := bstep (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) B1200377
theorem B1398881 : Blo 932582 1398881 := bstep (se 2 (by rfl) ⟨524580, by rfl⟩ : syracuseStep 1398881 = 1049161) B1049161
theorem B3987569 : Blo 932582 3987569 := bstep (se 2 (by rfl) ⟨1495338, by rfl⟩ : syracuseStep 3987569 = 2990677) B2990677
theorem B1398899 : Blo 932582 1398899 := bstep (se 1 (by rfl) ⟨1049174, by rfl⟩ : syracuseStep 1398899 = 2098349) B2098349
theorem B1398929 : Blo 932582 1398929 := bstep (se 2 (by rfl) ⟨524598, by rfl⟩ : syracuseStep 1398929 = 1049197) B1049197
theorem B1398947 : Blo 932582 1398947 := bstep (se 1 (by rfl) ⟨1049210, by rfl⟩ : syracuseStep 1398947 = 2098421) B2098421
theorem B1398977 : Blo 932582 1398977 := bstep (se 2 (by rfl) ⟨524616, by rfl⟩ : syracuseStep 1398977 = 1049233) B1049233
theorem B1398995 : Blo 932582 1398995 := bstep (se 1 (by rfl) ⟨1049246, by rfl⟩ : syracuseStep 1398995 = 2098493) B2098493
theorem B1399025 : Blo 932582 1399025 := bstep (se 2 (by rfl) ⟨524634, by rfl⟩ : syracuseStep 1399025 = 1049269) B1049269
theorem B1399043 : Blo 932582 1399043 := bstep (se 1 (by rfl) ⟨1049282, by rfl⟩ : syracuseStep 1399043 = 2098565) B2098565
theorem B5691653 : Blo 932582 5691653 := bstep (se 4 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 5691653 = 1067185) B1067185
theorem B1399073 : Blo 932582 1399073 := bstep (se 2 (by rfl) ⟨524652, by rfl⟩ : syracuseStep 1399073 = 1049305) B1049305
theorem B1399091 : Blo 932582 1399091 := bstep (se 1 (by rfl) ⟨1049318, by rfl⟩ : syracuseStep 1399091 = 2098637) B2098637
theorem B1497395 : Blo 932582 1497395 := bstep (se 1 (by rfl) ⟨1123046, by rfl⟩ : syracuseStep 1497395 = 2246093) B2246093
theorem B3234125 : Blo 932582 3234125 := bstep (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) B1212797
theorem B1399121 : Blo 932582 1399121 := bstep (se 2 (by rfl) ⟨524670, by rfl⟩ : syracuseStep 1399121 = 1049341) B1049341
theorem B1399139 : Blo 932582 1399139 := bstep (se 1 (by rfl) ⟨1049354, by rfl⟩ : syracuseStep 1399139 = 2098709) B2098709
theorem B1399169 : Blo 932582 1399169 := bstep (se 2 (by rfl) ⟨524688, by rfl⟩ : syracuseStep 1399169 = 1049377) B1049377
theorem B1399187 : Blo 932582 1399187 := bstep (se 1 (by rfl) ⟨1049390, by rfl⟩ : syracuseStep 1399187 = 2098781) B2098781
theorem B1825187 : Blo 932582 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B1399217 : Blo 932582 1399217 := bstep (se 2 (by rfl) ⟨524706, by rfl⟩ : syracuseStep 1399217 = 1049413) B1049413
theorem B1497523 : Blo 932582 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B1399235 : Blo 932582 1399235 := bstep (se 1 (by rfl) ⟨1049426, by rfl⟩ : syracuseStep 1399235 = 2098853) B2098853
theorem B1399265 : Blo 932582 1399265 := bstep (se 2 (by rfl) ⟨524724, by rfl⟩ : syracuseStep 1399265 = 1049449) B1049449
theorem B1399283 : Blo 932582 1399283 := bstep (se 1 (by rfl) ⟨1049462, by rfl⟩ : syracuseStep 1399283 = 2098925) B2098925
theorem B1399313 : Blo 932582 1399313 := bstep (se 2 (by rfl) ⟨524742, by rfl⟩ : syracuseStep 1399313 = 1049485) B1049485
theorem B1399331 : Blo 932582 1399331 := bstep (se 1 (by rfl) ⟨1049498, by rfl⟩ : syracuseStep 1399331 = 2098997) B2098997
theorem B1399361 : Blo 932582 1399361 := bstep (se 2 (by rfl) ⟨524760, by rfl⟩ : syracuseStep 1399361 = 1049521) B1049521
theorem B1497665 : Blo 932582 1497665 := bstep (se 2 (by rfl) ⟨561624, by rfl⟩ : syracuseStep 1497665 = 1123249) B1123249
theorem B1399379 : Blo 932582 1399379 := bstep (se 1 (by rfl) ⟨1049534, by rfl⟩ : syracuseStep 1399379 = 2099069) B2099069
theorem B1399409 : Blo 932582 1399409 := bstep (se 2 (by rfl) ⟨524778, by rfl⟩ : syracuseStep 1399409 = 1049557) B1049557
theorem B1399427 : Blo 932582 1399427 := bstep (se 1 (by rfl) ⟨1049570, by rfl⟩ : syracuseStep 1399427 = 2099141) B2099141
theorem B1399457 : Blo 932582 1399457 := bstep (se 2 (by rfl) ⟨524796, by rfl⟩ : syracuseStep 1399457 = 1049593) B1049593
theorem B1399475 : Blo 932582 1399475 := bstep (se 1 (by rfl) ⟨1049606, by rfl⟩ : syracuseStep 1399475 = 2099213) B2099213
theorem B1399505 : Blo 932582 1399505 := bstep (se 2 (by rfl) ⟨524814, by rfl⟩ : syracuseStep 1399505 = 1049629) B1049629
theorem B1399523 : Blo 932582 1399523 := bstep (se 1 (by rfl) ⟨1049642, by rfl⟩ : syracuseStep 1399523 = 2099285) B2099285
theorem B1399553 : Blo 932582 1399553 := bstep (se 2 (by rfl) ⟨524832, by rfl⟩ : syracuseStep 1399553 = 1049665) B1049665
theorem B11950861 : Blo 932582 11950861 := bstep (se 3 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 11950861 = 4481573) B4481573
theorem B1399571 : Blo 932582 1399571 := bstep (se 1 (by rfl) ⟨1049678, by rfl⟩ : syracuseStep 1399571 = 2099357) B2099357
theorem B1399601 : Blo 932582 1399601 := bstep (se 2 (by rfl) ⟨524850, by rfl⟩ : syracuseStep 1399601 = 1049701) B1049701
theorem B1399619 : Blo 932582 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B1399649 : Blo 932582 1399649 := bstep (se 2 (by rfl) ⟨524868, by rfl⟩ : syracuseStep 1399649 = 1049737) B1049737
theorem B1497953 : Blo 932582 1497953 := bstep (se 2 (by rfl) ⟨561732, by rfl⟩ : syracuseStep 1497953 = 1123465) B1123465
theorem B1399667 : Blo 932582 1399667 := bstep (se 1 (by rfl) ⟨1049750, by rfl⟩ : syracuseStep 1399667 = 2099501) B2099501
theorem B1399697 : Blo 932582 1399697 := bstep (se 2 (by rfl) ⟨524886, by rfl⟩ : syracuseStep 1399697 = 1049773) B1049773
theorem B1399715 : Blo 932582 1399715 := bstep (se 1 (by rfl) ⟨1049786, by rfl⟩ : syracuseStep 1399715 = 2099573) B2099573
theorem B1399745 : Blo 932582 1399745 := bstep (se 2 (by rfl) ⟨524904, by rfl⟩ : syracuseStep 1399745 = 1049809) B1049809
theorem B1399763 : Blo 932582 1399763 := bstep (se 1 (by rfl) ⟨1049822, by rfl⟩ : syracuseStep 1399763 = 2099645) B2099645
theorem B1399793 : Blo 932582 1399793 := bstep (se 2 (by rfl) ⟨524922, by rfl⟩ : syracuseStep 1399793 = 1049845) B1049845
theorem B1399811 : Blo 932582 1399811 := bstep (se 1 (by rfl) ⟨1049858, by rfl⟩ : syracuseStep 1399811 = 2099717) B2099717
theorem B1399841 : Blo 932582 1399841 := bstep (se 2 (by rfl) ⟨524940, by rfl⟩ : syracuseStep 1399841 = 1049881) B1049881
theorem B1399859 : Blo 932582 1399859 := bstep (se 1 (by rfl) ⟨1049894, by rfl⟩ : syracuseStep 1399859 = 2099789) B2099789
theorem B1399889 : Blo 932582 1399889 := bstep (se 2 (by rfl) ⟨524958, by rfl⟩ : syracuseStep 1399889 = 1049917) B1049917
theorem B1399907 : Blo 932582 1399907 := bstep (se 1 (by rfl) ⟨1049930, by rfl⟩ : syracuseStep 1399907 = 2099861) B2099861
theorem B10640483 : Blo 932582 10640483 := bstep (se 1 (by rfl) ⟨7980362, by rfl⟩ : syracuseStep 10640483 = 15960725) B15960725
theorem B5332067 : Blo 932582 5332067 := bstep (se 1 (by rfl) ⟨3999050, by rfl⟩ : syracuseStep 5332067 = 7998101) B7998101
theorem B1399937 : Blo 932582 1399937 := bstep (se 2 (by rfl) ⟨524976, by rfl⟩ : syracuseStep 1399937 = 1049953) B1049953
theorem B1399955 : Blo 932582 1399955 := bstep (se 1 (by rfl) ⟨1049966, by rfl⟩ : syracuseStep 1399955 = 2099933) B2099933
theorem B3038381 : Blo 932582 3038381 := bstep (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) B1139393
theorem B1399985 : Blo 932582 1399985 := bstep (se 2 (by rfl) ⟨524994, by rfl⟩ : syracuseStep 1399985 = 1049989) B1049989
theorem B1596611 : Blo 932582 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B1400003 : Blo 932582 1400003 := bstep (se 1 (by rfl) ⟨1050002, by rfl⟩ : syracuseStep 1400003 = 2100005) B2100005
theorem B1400033 : Blo 932582 1400033 := bstep (se 2 (by rfl) ⟨525012, by rfl⟩ : syracuseStep 1400033 = 1050025) B1050025
theorem B1400051 : Blo 932582 1400051 := bstep (se 1 (by rfl) ⟨1050038, by rfl⟩ : syracuseStep 1400051 = 2100077) B2100077
theorem B1400081 : Blo 932582 1400081 := bstep (se 2 (by rfl) ⟨525030, by rfl⟩ : syracuseStep 1400081 = 1050061) B1050061
theorem B1400099 : Blo 932582 1400099 := bstep (se 1 (by rfl) ⟨1050074, by rfl⟩ : syracuseStep 1400099 = 2100149) B2100149
theorem B15162677 : Blo 932582 15162677 := bstep (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) B1421501
theorem B1400129 : Blo 932582 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B1400147 : Blo 932582 1400147 := bstep (se 1 (by rfl) ⟨1050110, by rfl⟩ : syracuseStep 1400147 = 2100221) B2100221
theorem B1400177 : Blo 932582 1400177 := bstep (se 2 (by rfl) ⟨525066, by rfl⟩ : syracuseStep 1400177 = 1050133) B1050133
theorem B1400195 : Blo 932582 1400195 := bstep (se 1 (by rfl) ⟨1050146, by rfl⟩ : syracuseStep 1400195 = 2100293) B2100293
theorem B1400225 : Blo 932582 1400225 := bstep (se 2 (by rfl) ⟨525084, by rfl⟩ : syracuseStep 1400225 = 1050169) B1050169
theorem B1400243 : Blo 932582 1400243 := bstep (se 1 (by rfl) ⟨1050182, by rfl⟩ : syracuseStep 1400243 = 2100365) B2100365
theorem B1400273 : Blo 932582 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B1400291 : Blo 932582 1400291 := bstep (se 1 (by rfl) ⟨1050218, by rfl⟩ : syracuseStep 1400291 = 2100437) B2100437
theorem B1400321 : Blo 932582 1400321 := bstep (se 2 (by rfl) ⟨525120, by rfl⟩ : syracuseStep 1400321 = 1050241) B1050241
theorem B1400339 : Blo 932582 1400339 := bstep (se 1 (by rfl) ⟨1050254, by rfl⟩ : syracuseStep 1400339 = 2100509) B2100509
theorem B1400369 : Blo 932582 1400369 := bstep (se 2 (by rfl) ⟨525138, by rfl⟩ : syracuseStep 1400369 = 1050277) B1050277
theorem B1400387 : Blo 932582 1400387 := bstep (se 1 (by rfl) ⟨1050290, by rfl⟩ : syracuseStep 1400387 = 2100581) B2100581
theorem B1400417 : Blo 932582 1400417 := bstep (se 2 (by rfl) ⟨525156, by rfl⟩ : syracuseStep 1400417 = 1050313) B1050313
theorem B1400435 : Blo 932582 1400435 := bstep (se 1 (by rfl) ⟨1050326, by rfl⟩ : syracuseStep 1400435 = 2100653) B2100653
theorem B1498753 : Blo 932582 1498753 := bstep (se 2 (by rfl) ⟨562032, by rfl⟩ : syracuseStep 1498753 = 1124065) B1124065
theorem B1400465 : Blo 932582 1400465 := bstep (se 2 (by rfl) ⟨525174, by rfl⟩ : syracuseStep 1400465 = 1050349) B1050349
theorem B1400483 : Blo 932582 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B1400513 : Blo 932582 1400513 := bstep (se 2 (by rfl) ⟨525192, by rfl⟩ : syracuseStep 1400513 = 1050385) B1050385
theorem B1400531 : Blo 932582 1400531 := bstep (se 1 (by rfl) ⟨1050398, by rfl⟩ : syracuseStep 1400531 = 2100797) B2100797
theorem B1400561 : Blo 932582 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B1400579 : Blo 932582 1400579 := bstep (se 1 (by rfl) ⟨1050434, by rfl⟩ : syracuseStep 1400579 = 2100869) B2100869
theorem B3792653 : Blo 932582 3792653 := bstep (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) B1422245
theorem B1400609 : Blo 932582 1400609 := bstep (se 2 (by rfl) ⟨525228, by rfl⟩ : syracuseStep 1400609 = 1050457) B1050457
theorem B1400627 : Blo 932582 1400627 := bstep (se 1 (by rfl) ⟨1050470, by rfl⟩ : syracuseStep 1400627 = 2100941) B2100941
theorem B1400657 : Blo 932582 1400657 := bstep (se 2 (by rfl) ⟨525246, by rfl⟩ : syracuseStep 1400657 = 1050493) B1050493
theorem B1400675 : Blo 932582 1400675 := bstep (se 1 (by rfl) ⟨1050506, by rfl⟩ : syracuseStep 1400675 = 2101013) B2101013
theorem B1400705 : Blo 932582 1400705 := bstep (se 2 (by rfl) ⟨525264, by rfl⟩ : syracuseStep 1400705 = 1050529) B1050529
theorem B1400723 : Blo 932582 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B2842541 : Blo 932582 2842541 := bstep (se 3 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 2842541 = 1065953) B1065953
theorem B1400753 : Blo 932582 1400753 := bstep (se 2 (by rfl) ⟨525282, by rfl⟩ : syracuseStep 1400753 = 1050565) B1050565
theorem B1400771 : Blo 932582 1400771 := bstep (se 1 (by rfl) ⟨1050578, by rfl⟩ : syracuseStep 1400771 = 2101157) B2101157
theorem B1400801 : Blo 932582 1400801 := bstep (se 2 (by rfl) ⟨525300, by rfl⟩ : syracuseStep 1400801 = 1050601) B1050601
theorem B1400819 : Blo 932582 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B1400849 : Blo 932582 1400849 := bstep (se 2 (by rfl) ⟨525318, by rfl⟩ : syracuseStep 1400849 = 1050637) B1050637
theorem B1400867 : Blo 932582 1400867 := bstep (se 1 (by rfl) ⟨1050650, by rfl⟩ : syracuseStep 1400867 = 2101301) B2101301
theorem B3366947 : Blo 932582 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B3039277 : Blo 932582 3039277 := bstep (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) B1139729
theorem B5988401 : Blo 932582 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B1400897 : Blo 932582 1400897 := bstep (se 2 (by rfl) ⟨525336, by rfl⟩ : syracuseStep 1400897 = 1050673) B1050673
theorem B11952197 : Blo 932582 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B1400915 : Blo 932582 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B5988451 : Blo 932582 5988451 := bstep (se 1 (by rfl) ⟨4491338, by rfl⟩ : syracuseStep 5988451 = 8982677) B8982677
theorem B1400945 : Blo 932582 1400945 := bstep (se 2 (by rfl) ⟨525354, by rfl⟩ : syracuseStep 1400945 = 1050709) B1050709
theorem B1400963 : Blo 932582 1400963 := bstep (se 1 (by rfl) ⟨1050722, by rfl⟩ : syracuseStep 1400963 = 2101445) B2101445
theorem B1400993 : Blo 932582 1400993 := bstep (se 2 (by rfl) ⟨525372, by rfl⟩ : syracuseStep 1400993 = 1050745) B1050745
theorem B1401011 : Blo 932582 1401011 := bstep (se 1 (by rfl) ⟨1050758, by rfl⟩ : syracuseStep 1401011 = 2101517) B2101517
theorem B1401041 : Blo 932582 1401041 := bstep (se 2 (by rfl) ⟨525390, by rfl⟩ : syracuseStep 1401041 = 1050781) B1050781
theorem B1401059 : Blo 932582 1401059 := bstep (se 1 (by rfl) ⟨1050794, by rfl⟩ : syracuseStep 1401059 = 2101589) B2101589
theorem B1401089 : Blo 932582 1401089 := bstep (se 2 (by rfl) ⟨525408, by rfl⟩ : syracuseStep 1401089 = 1050817) B1050817
theorem B1401107 : Blo 932582 1401107 := bstep (se 1 (by rfl) ⟨1050830, by rfl⟩ : syracuseStep 1401107 = 2101661) B2101661
theorem B1401137 : Blo 932582 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B1401155 : Blo 932582 1401155 := bstep (se 1 (by rfl) ⟨1050866, by rfl⟩ : syracuseStep 1401155 = 2101733) B2101733
theorem B1401185 : Blo 932582 1401185 := bstep (se 2 (by rfl) ⟨525444, by rfl⟩ : syracuseStep 1401185 = 1050889) B1050889
theorem B1401203 : Blo 932582 1401203 := bstep (se 1 (by rfl) ⟨1050902, by rfl⟩ : syracuseStep 1401203 = 2101805) B2101805
theorem B2220419 : Blo 932582 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B1401233 : Blo 932582 1401233 := bstep (se 2 (by rfl) ⟨525462, by rfl⟩ : syracuseStep 1401233 = 1050925) B1050925
theorem B1401251 : Blo 932582 1401251 := bstep (se 1 (by rfl) ⟨1050938, by rfl⟩ : syracuseStep 1401251 = 2101877) B2101877
theorem B1401281 : Blo 932582 1401281 := bstep (se 2 (by rfl) ⟨525480, by rfl⟩ : syracuseStep 1401281 = 1050961) B1050961
theorem B1401299 : Blo 932582 1401299 := bstep (se 1 (by rfl) ⟨1050974, by rfl⟩ : syracuseStep 1401299 = 2101949) B2101949
theorem B1401329 : Blo 932582 1401329 := bstep (se 2 (by rfl) ⟨525498, by rfl⟩ : syracuseStep 1401329 = 1050997) B1050997
theorem B1401347 : Blo 932582 1401347 := bstep (se 1 (by rfl) ⟨1051010, by rfl⟩ : syracuseStep 1401347 = 2102021) B2102021
theorem B1401377 : Blo 932582 1401377 := bstep (se 2 (by rfl) ⟨525516, by rfl⟩ : syracuseStep 1401377 = 1051033) B1051033
theorem B1401395 : Blo 932582 1401395 := bstep (se 1 (by rfl) ⟨1051046, by rfl⟩ : syracuseStep 1401395 = 2102093) B2102093
theorem B1401425 : Blo 932582 1401425 := bstep (se 2 (by rfl) ⟨525534, by rfl⟩ : syracuseStep 1401425 = 1051069) B1051069
theorem B1401443 : Blo 932582 1401443 := bstep (se 1 (by rfl) ⟨1051082, by rfl⟩ : syracuseStep 1401443 = 2102165) B2102165
theorem B1401473 : Blo 932582 1401473 := bstep (se 2 (by rfl) ⟨525552, by rfl⟩ : syracuseStep 1401473 = 1051105) B1051105
theorem B1401491 : Blo 932582 1401491 := bstep (se 1 (by rfl) ⟨1051118, by rfl⟩ : syracuseStep 1401491 = 2102237) B2102237
theorem B1401521 : Blo 932582 1401521 := bstep (se 2 (by rfl) ⟨525570, by rfl⟩ : syracuseStep 1401521 = 1051141) B1051141
theorem B1401539 : Blo 932582 1401539 := bstep (se 1 (by rfl) ⟨1051154, by rfl⟩ : syracuseStep 1401539 = 2102309) B2102309
theorem B1401569 : Blo 932582 1401569 := bstep (se 2 (by rfl) ⟨525588, by rfl⟩ : syracuseStep 1401569 = 1051177) B1051177
theorem B1401587 : Blo 932582 1401587 := bstep (se 1 (by rfl) ⟨1051190, by rfl⟩ : syracuseStep 1401587 = 2102381) B2102381
theorem B1401617 : Blo 932582 1401617 := bstep (se 2 (by rfl) ⟨525606, by rfl⟩ : syracuseStep 1401617 = 1051213) B1051213
theorem B1401635 : Blo 932582 1401635 := bstep (se 1 (by rfl) ⟨1051226, by rfl⟩ : syracuseStep 1401635 = 2102453) B2102453
theorem B1401665 : Blo 932582 1401665 := bstep (se 2 (by rfl) ⟨525624, by rfl⟩ : syracuseStep 1401665 = 1051249) B1051249
theorem B3040067 : Blo 932582 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B1499971 : Blo 932582 1499971 := bstep (se 1 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 1499971 = 2249957) B2249957
theorem B1401683 : Blo 932582 1401683 := bstep (se 1 (by rfl) ⟨1051262, by rfl⟩ : syracuseStep 1401683 = 2102525) B2102525
theorem B1401713 : Blo 932582 1401713 := bstep (se 2 (by rfl) ⟨525642, by rfl⟩ : syracuseStep 1401713 = 1051285) B1051285
theorem B1401731 : Blo 932582 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B1401761 : Blo 932582 1401761 := bstep (se 2 (by rfl) ⟨525660, by rfl⟩ : syracuseStep 1401761 = 1051321) B1051321
theorem B1401779 : Blo 932582 1401779 := bstep (se 1 (by rfl) ⟨1051334, by rfl⟩ : syracuseStep 1401779 = 2102669) B2102669
theorem B5333957 : Blo 932582 5333957 := bstep (se 4 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 5333957 = 1000117) B1000117
theorem B1401809 : Blo 932582 1401809 := bstep (se 2 (by rfl) ⟨525678, by rfl⟩ : syracuseStep 1401809 = 1051357) B1051357
theorem B1401827 : Blo 932582 1401827 := bstep (se 1 (by rfl) ⟨1051370, by rfl⟩ : syracuseStep 1401827 = 2102741) B2102741
theorem B1401857 : Blo 932582 1401857 := bstep (se 2 (by rfl) ⟨525696, by rfl⟩ : syracuseStep 1401857 = 1051393) B1051393
theorem B1401875 : Blo 932582 1401875 := bstep (se 1 (by rfl) ⟨1051406, by rfl⟩ : syracuseStep 1401875 = 2102813) B2102813
theorem B1401905 : Blo 932582 1401905 := bstep (se 2 (by rfl) ⟨525714, by rfl⟩ : syracuseStep 1401905 = 1051429) B1051429
theorem B1401923 : Blo 932582 1401923 := bstep (se 1 (by rfl) ⟨1051442, by rfl⟩ : syracuseStep 1401923 = 2102885) B2102885
theorem B1401953 : Blo 932582 1401953 := bstep (se 2 (by rfl) ⟨525732, by rfl⟩ : syracuseStep 1401953 = 1051465) B1051465
theorem B1401971 : Blo 932582 1401971 := bstep (se 1 (by rfl) ⟨1051478, by rfl⟩ : syracuseStep 1401971 = 2102957) B2102957
theorem B1402001 : Blo 932582 1402001 := bstep (se 2 (by rfl) ⟨525750, by rfl⟩ : syracuseStep 1402001 = 1051501) B1051501
theorem B1402019 : Blo 932582 1402019 := bstep (se 1 (by rfl) ⟨1051514, by rfl⟩ : syracuseStep 1402019 = 2103029) B2103029
theorem B1402049 : Blo 932582 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B1402067 : Blo 932582 1402067 := bstep (se 1 (by rfl) ⟨1051550, by rfl⟩ : syracuseStep 1402067 = 2103101) B2103101
theorem B1402097 : Blo 932582 1402097 := bstep (se 2 (by rfl) ⟨525786, by rfl⟩ : syracuseStep 1402097 = 1051573) B1051573
theorem B3794161 : Blo 932582 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B1402115 : Blo 932582 1402115 := bstep (se 1 (by rfl) ⟨1051586, by rfl⟩ : syracuseStep 1402115 = 2103173) B2103173
theorem B1402145 : Blo 932582 1402145 := bstep (se 2 (by rfl) ⟨525804, by rfl⟩ : syracuseStep 1402145 = 1051609) B1051609
theorem B1402163 : Blo 932582 1402163 := bstep (se 1 (by rfl) ⟨1051622, by rfl⟩ : syracuseStep 1402163 = 2103245) B2103245
theorem B1402193 : Blo 932582 1402193 := bstep (se 2 (by rfl) ⟨525822, by rfl⟩ : syracuseStep 1402193 = 1051645) B1051645
theorem B1402211 : Blo 932582 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B1402241 : Blo 932582 1402241 := bstep (se 2 (by rfl) ⟨525840, by rfl⟩ : syracuseStep 1402241 = 1051681) B1051681
theorem B1402259 : Blo 932582 1402259 := bstep (se 1 (by rfl) ⟨1051694, by rfl⟩ : syracuseStep 1402259 = 2103389) B2103389
theorem B1402289 : Blo 932582 1402289 := bstep (se 2 (by rfl) ⟨525858, by rfl⟩ : syracuseStep 1402289 = 1051717) B1051717
theorem B1402307 : Blo 932582 1402307 := bstep (se 1 (by rfl) ⟨1051730, by rfl⟩ : syracuseStep 1402307 = 2103461) B2103461
theorem B1402337 : Blo 932582 1402337 := bstep (se 2 (by rfl) ⟨525876, by rfl⟩ : syracuseStep 1402337 = 1051753) B1051753
theorem B1402355 : Blo 932582 1402355 := bstep (se 1 (by rfl) ⟨1051766, by rfl⟩ : syracuseStep 1402355 = 2103533) B2103533
theorem B1402385 : Blo 932582 1402385 := bstep (se 2 (by rfl) ⟨525894, by rfl⟩ : syracuseStep 1402385 = 1051789) B1051789
theorem B1402403 : Blo 932582 1402403 := bstep (se 1 (by rfl) ⟨1051802, by rfl⟩ : syracuseStep 1402403 = 2103605) B2103605
theorem B1402433 : Blo 932582 1402433 := bstep (se 2 (by rfl) ⟨525912, by rfl⟩ : syracuseStep 1402433 = 1051825) B1051825
theorem B1402451 : Blo 932582 1402451 := bstep (se 1 (by rfl) ⟨1051838, by rfl⟩ : syracuseStep 1402451 = 2103677) B2103677
theorem B3991139 : Blo 932582 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B3368561 : Blo 932582 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B1402481 : Blo 932582 1402481 := bstep (se 2 (by rfl) ⟨525930, by rfl⟩ : syracuseStep 1402481 = 1051861) B1051861
theorem B1992323 : Blo 932582 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B1402499 : Blo 932582 1402499 := bstep (se 1 (by rfl) ⟨1051874, by rfl⟩ : syracuseStep 1402499 = 2103749) B2103749
theorem B1402529 : Blo 932582 1402529 := bstep (se 2 (by rfl) ⟨525948, by rfl⟩ : syracuseStep 1402529 = 1051897) B1051897
theorem B1402547 : Blo 932582 1402547 := bstep (se 1 (by rfl) ⟨1051910, by rfl⟩ : syracuseStep 1402547 = 2103821) B2103821
theorem B1894097 : Blo 932582 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B1402577 : Blo 932582 1402577 := bstep (se 2 (by rfl) ⟨525966, by rfl⟩ : syracuseStep 1402577 = 1051933) B1051933
theorem B1402595 : Blo 932582 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B1402625 : Blo 932582 1402625 := bstep (se 2 (by rfl) ⟨525984, by rfl⟩ : syracuseStep 1402625 = 1051969) B1051969
theorem B1402643 : Blo 932582 1402643 := bstep (se 1 (by rfl) ⟨1051982, by rfl⟩ : syracuseStep 1402643 = 2103965) B2103965
theorem B1402673 : Blo 932582 1402673 := bstep (se 2 (by rfl) ⟨526002, by rfl⟩ : syracuseStep 1402673 = 1052005) B1052005
theorem B1402691 : Blo 932582 1402691 := bstep (se 1 (by rfl) ⟨1052018, by rfl⟩ : syracuseStep 1402691 = 2104037) B2104037
theorem B1402721 : Blo 932582 1402721 := bstep (se 2 (by rfl) ⟨526020, by rfl⟩ : syracuseStep 1402721 = 1052041) B1052041
theorem B1402739 : Blo 932582 1402739 := bstep (se 1 (by rfl) ⟨1052054, by rfl⟩ : syracuseStep 1402739 = 2104109) B2104109
theorem B1402769 : Blo 932582 1402769 := bstep (se 2 (by rfl) ⟨526038, by rfl⟩ : syracuseStep 1402769 = 1052077) B1052077
theorem B1402787 : Blo 932582 1402787 := bstep (se 1 (by rfl) ⟨1052090, by rfl⟩ : syracuseStep 1402787 = 2104181) B2104181
theorem B1402817 : Blo 932582 1402817 := bstep (se 2 (by rfl) ⟨526056, by rfl⟩ : syracuseStep 1402817 = 1052113) B1052113
theorem B3598285 : Blo 932582 3598285 := bstep (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) B1349357
theorem B1402835 : Blo 932582 1402835 := bstep (se 1 (by rfl) ⟨1052126, by rfl⟩ : syracuseStep 1402835 = 2104253) B2104253
theorem B1402865 : Blo 932582 1402865 := bstep (se 2 (by rfl) ⟨526074, by rfl⟩ : syracuseStep 1402865 = 1052149) B1052149
theorem B1402883 : Blo 932582 1402883 := bstep (se 1 (by rfl) ⟨1052162, by rfl⟩ : syracuseStep 1402883 = 2104325) B2104325
theorem B1402913 : Blo 932582 1402913 := bstep (se 2 (by rfl) ⟨526092, by rfl⟩ : syracuseStep 1402913 = 1052185) B1052185
theorem B1402931 : Blo 932582 1402931 := bstep (se 1 (by rfl) ⟨1052198, by rfl⟩ : syracuseStep 1402931 = 2104397) B2104397
theorem B1402961 : Blo 932582 1402961 := bstep (se 2 (by rfl) ⟨526110, by rfl⟩ : syracuseStep 1402961 = 1052221) B1052221
theorem B1796195 : Blo 932582 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1402979 : Blo 932582 1402979 := bstep (se 1 (by rfl) ⟨1052234, by rfl⟩ : syracuseStep 1402979 = 2104469) B2104469
theorem B1403009 : Blo 932582 1403009 := bstep (se 2 (by rfl) ⟨526128, by rfl⟩ : syracuseStep 1403009 = 1052257) B1052257
theorem B1403027 : Blo 932582 1403027 := bstep (se 1 (by rfl) ⟨1052270, by rfl⟩ : syracuseStep 1403027 = 2104541) B2104541
theorem B1403057 : Blo 932582 1403057 := bstep (se 2 (by rfl) ⟨526146, by rfl⟩ : syracuseStep 1403057 = 1052293) B1052293
theorem B1403075 : Blo 932582 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B2844877 : Blo 932582 2844877 := bstep (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) B1066829
theorem B1403105 : Blo 932582 1403105 := bstep (se 2 (by rfl) ⟨526164, by rfl⟩ : syracuseStep 1403105 = 1052329) B1052329
theorem B1403123 : Blo 932582 1403123 := bstep (se 1 (by rfl) ⟨1052342, by rfl⟩ : syracuseStep 1403123 = 2104685) B2104685
theorem B1403153 : Blo 932582 1403153 := bstep (se 2 (by rfl) ⟨526182, by rfl⟩ : syracuseStep 1403153 = 1052365) B1052365
theorem B1403171 : Blo 932582 1403171 := bstep (se 1 (by rfl) ⟨1052378, by rfl⟩ : syracuseStep 1403171 = 2104757) B2104757
theorem B1403201 : Blo 932582 1403201 := bstep (se 2 (by rfl) ⟨526200, by rfl⟩ : syracuseStep 1403201 = 1052401) B1052401
theorem B3795277 : Blo 932582 3795277 := bstep (se 3 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 3795277 = 1423229) B1423229
theorem B1403219 : Blo 932582 1403219 := bstep (se 1 (by rfl) ⟨1052414, by rfl⟩ : syracuseStep 1403219 = 2104829) B2104829
theorem B2845037 : Blo 932582 2845037 := bstep (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) B1066889
theorem B1403249 : Blo 932582 1403249 := bstep (se 2 (by rfl) ⟨526218, by rfl⟩ : syracuseStep 1403249 = 1052437) B1052437
theorem B1403267 : Blo 932582 1403267 := bstep (se 1 (by rfl) ⟨1052450, by rfl⟩ : syracuseStep 1403267 = 2104901) B2104901
theorem B1403297 : Blo 932582 1403297 := bstep (se 2 (by rfl) ⟨526236, by rfl⟩ : syracuseStep 1403297 = 1052473) B1052473
theorem B1403315 : Blo 932582 1403315 := bstep (se 1 (by rfl) ⟨1052486, by rfl⟩ : syracuseStep 1403315 = 2104973) B2104973
theorem B5990861 : Blo 932582 5990861 := bstep (se 3 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 5990861 = 2246573) B2246573
theorem B1403345 : Blo 932582 1403345 := bstep (se 2 (by rfl) ⟨526254, by rfl⟩ : syracuseStep 1403345 = 1052509) B1052509
theorem B1599955 : Blo 932582 1599955 := bstep (se 1 (by rfl) ⟨1199966, by rfl⟩ : syracuseStep 1599955 = 2399933) B2399933
theorem B1403363 : Blo 932582 1403363 := bstep (se 1 (by rfl) ⟨1052522, by rfl⟩ : syracuseStep 1403363 = 2105045) B2105045
theorem B1403393 : Blo 932582 1403393 := bstep (se 2 (by rfl) ⟨526272, by rfl⟩ : syracuseStep 1403393 = 1052545) B1052545
theorem B1403411 : Blo 932582 1403411 := bstep (se 1 (by rfl) ⟨1052558, by rfl⟩ : syracuseStep 1403411 = 2105117) B2105117
theorem B1403441 : Blo 932582 1403441 := bstep (se 2 (by rfl) ⟨526290, by rfl⟩ : syracuseStep 1403441 = 1052581) B1052581
theorem B1403459 : Blo 932582 1403459 := bstep (se 1 (by rfl) ⟨1052594, by rfl⟩ : syracuseStep 1403459 = 2105189) B2105189
theorem B1403489 : Blo 932582 1403489 := bstep (se 2 (by rfl) ⟨526308, by rfl⟩ : syracuseStep 1403489 = 1052617) B1052617
theorem B1403507 : Blo 932582 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B1403537 : Blo 932582 1403537 := bstep (se 2 (by rfl) ⟨526326, by rfl⟩ : syracuseStep 1403537 = 1052653) B1052653
theorem B1403555 : Blo 932582 1403555 := bstep (se 1 (by rfl) ⟨1052666, by rfl⟩ : syracuseStep 1403555 = 2105333) B2105333
theorem B1403585 : Blo 932582 1403585 := bstep (se 2 (by rfl) ⟨526344, by rfl⟩ : syracuseStep 1403585 = 1052689) B1052689
theorem B1403603 : Blo 932582 1403603 := bstep (se 1 (by rfl) ⟨1052702, by rfl⟩ : syracuseStep 1403603 = 2105405) B2105405
theorem B7990001 : Blo 932582 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B1403633 : Blo 932582 1403633 := bstep (se 2 (by rfl) ⟨526362, by rfl⟩ : syracuseStep 1403633 = 1052725) B1052725
theorem B1403651 : Blo 932582 1403651 := bstep (se 1 (by rfl) ⟨1052738, by rfl⟩ : syracuseStep 1403651 = 2105477) B2105477
theorem B1403681 : Blo 932582 1403681 := bstep (se 2 (by rfl) ⟨526380, by rfl⟩ : syracuseStep 1403681 = 1052761) B1052761
theorem B1403699 : Blo 932582 1403699 := bstep (se 1 (by rfl) ⟨1052774, by rfl⟩ : syracuseStep 1403699 = 2105549) B2105549
theorem B1403729 : Blo 932582 1403729 := bstep (se 2 (by rfl) ⟨526398, by rfl⟩ : syracuseStep 1403729 = 1052797) B1052797
theorem B1403747 : Blo 932582 1403747 := bstep (se 1 (by rfl) ⟨1052810, by rfl⟩ : syracuseStep 1403747 = 2105621) B2105621
theorem B1403777 : Blo 932582 1403777 := bstep (se 2 (by rfl) ⟨526416, by rfl⟩ : syracuseStep 1403777 = 1052833) B1052833
theorem B1796995 : Blo 932582 1796995 := bstep (se 1 (by rfl) ⟨1347746, by rfl⟩ : syracuseStep 1796995 = 2695493) B2695493
theorem B1403795 : Blo 932582 1403795 := bstep (se 1 (by rfl) ⟨1052846, by rfl⟩ : syracuseStep 1403795 = 2105693) B2105693
theorem B1403825 : Blo 932582 1403825 := bstep (se 2 (by rfl) ⟨526434, by rfl⟩ : syracuseStep 1403825 = 1052869) B1052869
theorem B1403843 : Blo 932582 1403843 := bstep (se 1 (by rfl) ⟨1052882, by rfl⟩ : syracuseStep 1403843 = 2105765) B2105765
theorem B1403873 : Blo 932582 1403873 := bstep (se 2 (by rfl) ⟨526452, by rfl⟩ : syracuseStep 1403873 = 1052905) B1052905
theorem B1403891 : Blo 932582 1403891 := bstep (se 1 (by rfl) ⟨1052918, by rfl⟩ : syracuseStep 1403891 = 2105837) B2105837
theorem B1403921 : Blo 932582 1403921 := bstep (se 2 (by rfl) ⟨526470, by rfl⟩ : syracuseStep 1403921 = 1052941) B1052941
theorem B1403939 : Blo 932582 1403939 := bstep (se 1 (by rfl) ⟨1052954, by rfl⟩ : syracuseStep 1403939 = 2105909) B2105909
theorem B1403969 : Blo 932582 1403969 := bstep (se 2 (by rfl) ⟨526488, by rfl⟩ : syracuseStep 1403969 = 1052977) B1052977
theorem B3370061 : Blo 932582 3370061 := bstep (se 3 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 3370061 = 1263773) B1263773
theorem B1403987 : Blo 932582 1403987 := bstep (se 1 (by rfl) ⟨1052990, by rfl⟩ : syracuseStep 1403987 = 2105981) B2105981
theorem B10087523 : Blo 932582 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B1404017 : Blo 932582 1404017 := bstep (se 2 (by rfl) ⟨526506, by rfl⟩ : syracuseStep 1404017 = 1053013) B1053013
theorem B1404035 : Blo 932582 1404035 := bstep (se 1 (by rfl) ⟨1053026, by rfl⟩ : syracuseStep 1404035 = 2106053) B2106053
theorem B1404065 : Blo 932582 1404065 := bstep (se 2 (by rfl) ⟨526524, by rfl⟩ : syracuseStep 1404065 = 1053049) B1053049
theorem B1404083 : Blo 932582 1404083 := bstep (se 1 (by rfl) ⟨1053062, by rfl⟩ : syracuseStep 1404083 = 2106125) B2106125
theorem B1404113 : Blo 932582 1404113 := bstep (se 2 (by rfl) ⟨526542, by rfl⟩ : syracuseStep 1404113 = 1053085) B1053085
theorem B1404131 : Blo 932582 1404131 := bstep (se 1 (by rfl) ⟨1053098, by rfl⟩ : syracuseStep 1404131 = 2106197) B2106197
theorem B1404161 : Blo 932582 1404161 := bstep (se 2 (by rfl) ⟨526560, by rfl⟩ : syracuseStep 1404161 = 1053121) B1053121
theorem B7105805 : Blo 932582 7105805 := bstep (se 3 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 7105805 = 2664677) B2664677
theorem B1404179 : Blo 932582 1404179 := bstep (se 1 (by rfl) ⟨1053134, by rfl⟩ : syracuseStep 1404179 = 2106269) B2106269
theorem B1404209 : Blo 932582 1404209 := bstep (se 2 (by rfl) ⟨526578, by rfl⟩ : syracuseStep 1404209 = 1053157) B1053157
theorem B1404227 : Blo 932582 1404227 := bstep (se 1 (by rfl) ⟨1053170, by rfl⟩ : syracuseStep 1404227 = 2106341) B2106341
theorem B1404257 : Blo 932582 1404257 := bstep (se 2 (by rfl) ⟨526596, by rfl⟩ : syracuseStep 1404257 = 1053193) B1053193
theorem B1404275 : Blo 932582 1404275 := bstep (se 1 (by rfl) ⟨1053206, by rfl⟩ : syracuseStep 1404275 = 2106413) B2106413
theorem B1404305 : Blo 932582 1404305 := bstep (se 2 (by rfl) ⟨526614, by rfl⟩ : syracuseStep 1404305 = 1053229) B1053229
theorem B1404323 : Blo 932582 1404323 := bstep (se 1 (by rfl) ⟨1053242, by rfl⟩ : syracuseStep 1404323 = 2106485) B2106485
theorem B1404353 : Blo 932582 1404353 := bstep (se 2 (by rfl) ⟨526632, by rfl⟩ : syracuseStep 1404353 = 1053265) B1053265
theorem B1404371 : Blo 932582 1404371 := bstep (se 1 (by rfl) ⟨1053278, by rfl⟩ : syracuseStep 1404371 = 2106557) B2106557
theorem B1404401 : Blo 932582 1404401 := bstep (se 2 (by rfl) ⟨526650, by rfl⟩ : syracuseStep 1404401 = 1053301) B1053301
theorem B1404419 : Blo 932582 1404419 := bstep (se 1 (by rfl) ⟨1053314, by rfl⟩ : syracuseStep 1404419 = 2106629) B2106629
theorem B1404449 : Blo 932582 1404449 := bstep (se 2 (by rfl) ⟨526668, by rfl⟩ : syracuseStep 1404449 = 1053337) B1053337
theorem B1404467 : Blo 932582 1404467 := bstep (se 1 (by rfl) ⟨1053350, by rfl⟩ : syracuseStep 1404467 = 2106701) B2106701
theorem B1404497 : Blo 932582 1404497 := bstep (se 2 (by rfl) ⟨526686, by rfl⟩ : syracuseStep 1404497 = 1053373) B1053373
theorem B1994339 : Blo 932582 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B1404515 : Blo 932582 1404515 := bstep (se 1 (by rfl) ⟨1053386, by rfl⟩ : syracuseStep 1404515 = 2106773) B2106773
theorem B1404545 : Blo 932582 1404545 := bstep (se 2 (by rfl) ⟨526704, by rfl⟩ : syracuseStep 1404545 = 1053409) B1053409
theorem B1404563 : Blo 932582 1404563 := bstep (se 1 (by rfl) ⟨1053422, by rfl⟩ : syracuseStep 1404563 = 2106845) B2106845
theorem B1404593 : Blo 932582 1404593 := bstep (se 2 (by rfl) ⟨526722, by rfl⟩ : syracuseStep 1404593 = 1053445) B1053445
theorem B1404611 : Blo 932582 1404611 := bstep (se 1 (by rfl) ⟨1053458, by rfl⟩ : syracuseStep 1404611 = 2106917) B2106917
theorem B1404641 : Blo 932582 1404641 := bstep (se 2 (by rfl) ⟨526740, by rfl⟩ : syracuseStep 1404641 = 1053481) B1053481
theorem B1404659 : Blo 932582 1404659 := bstep (se 1 (by rfl) ⟨1053494, by rfl⟩ : syracuseStep 1404659 = 2106989) B2106989
theorem B1404689 : Blo 932582 1404689 := bstep (se 2 (by rfl) ⟨526758, by rfl⟩ : syracuseStep 1404689 = 1053517) B1053517
theorem B1404707 : Blo 932582 1404707 := bstep (se 1 (by rfl) ⟨1053530, by rfl⟩ : syracuseStep 1404707 = 2107061) B2107061
theorem B1404737 : Blo 932582 1404737 := bstep (se 2 (by rfl) ⟨526776, by rfl⟩ : syracuseStep 1404737 = 1053553) B1053553
theorem B1404755 : Blo 932582 1404755 := bstep (se 1 (by rfl) ⟨1053566, by rfl⟩ : syracuseStep 1404755 = 2107133) B2107133
theorem B1404785 : Blo 932582 1404785 := bstep (se 2 (by rfl) ⟨526794, by rfl⟩ : syracuseStep 1404785 = 1053589) B1053589
theorem B1404803 : Blo 932582 1404803 := bstep (se 1 (by rfl) ⟨1053602, by rfl⟩ : syracuseStep 1404803 = 2107205) B2107205
theorem B1404833 : Blo 932582 1404833 := bstep (se 2 (by rfl) ⟨526812, by rfl⟩ : syracuseStep 1404833 = 1053625) B1053625
theorem B1404851 : Blo 932582 1404851 := bstep (se 1 (by rfl) ⟨1053638, by rfl⟩ : syracuseStep 1404851 = 2107277) B2107277
theorem B2846897 : Blo 932582 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B2879921 : Blo 932582 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B6386245 : Blo 932582 6386245 := bstep (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) B1197421
theorem B1012403 : Blo 932582 1012403 := bstep (se 1 (by rfl) ⟨759302, by rfl⟩ : syracuseStep 1012403 = 1518605) B1518605
theorem B1995587 : Blo 932582 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B11957219 : Blo 932582 11957219 := bstep (se 1 (by rfl) ⟨8967914, by rfl⟩ : syracuseStep 11957219 = 17935829) B17935829
theorem B7206029 : Blo 932582 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B3994829 : Blo 932582 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B3994865 : Blo 932582 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B1996177 : Blo 932582 1996177 := bstep (se 2 (by rfl) ⟨748566, by rfl⟩ : syracuseStep 1996177 = 1497133) B1497133
theorem B6387121 : Blo 932582 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B3372515 : Blo 932582 3372515 := bstep (se 1 (by rfl) ⟨2529386, by rfl⟩ : syracuseStep 3372515 = 5058773) B5058773
theorem B9369101 : Blo 932582 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B11368117 : Blo 932582 11368117 := bstep (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) B1065761
theorem B2520877 : Blo 932582 2520877 := bstep (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) B945329
theorem B2520973 : Blo 932582 2520973 := bstep (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) B945365
theorem B1898417 : Blo 932582 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B7108721 : Blo 932582 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B3602765 : Blo 932582 3602765 := bstep (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) B1351037
theorem B1800785 : Blo 932582 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B2521859 : Blo 932582 2521859 := bstep (se 1 (by rfl) ⟨1891394, by rfl⟩ : syracuseStep 2521859 = 3782789) B3782789
theorem B1440545 : Blo 932582 1440545 := bstep (se 2 (by rfl) ⟨540204, by rfl⟩ : syracuseStep 1440545 = 1080409) B1080409
theorem B4258595 : Blo 932582 4258595 := bstep (se 1 (by rfl) ⟨3193946, by rfl⟩ : syracuseStep 4258595 = 6387893) B6387893
theorem B2522033 : Blo 932582 2522033 := bstep (se 2 (by rfl) ⟨945762, by rfl⟩ : syracuseStep 2522033 = 1891525) B1891525
theorem B2882531 : Blo 932582 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B8649827 : Blo 932582 8649827 := bstep (se 1 (by rfl) ⟨6487370, by rfl⟩ : syracuseStep 8649827 = 12974741) B12974741
theorem B4488803 : Blo 932582 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B8978525 : Blo 932582 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B3375425 : Blo 932582 3375425 := bstep (se 2 (by rfl) ⟨1265784, by rfl⟩ : syracuseStep 3375425 = 2531569) B2531569
theorem B6488471 : Blo 932582 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B3998231 : Blo 932582 3998231 := bstep (se 1 (by rfl) ⟨2998673, by rfl⟩ : syracuseStep 3998231 = 5997347) B5997347
theorem B1081931 : Blo 932582 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B21627485 : Blo 932582 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B1049323 : Blo 932582 1049323 := bstep (se 1 (by rfl) ⟨786992, by rfl⟩ : syracuseStep 1049323 = 1573985) B1573985
theorem B1049431 : Blo 932582 1049431 := bstep (se 1 (by rfl) ⟨787073, by rfl⟩ : syracuseStep 1049431 = 1574147) B1574147
theorem B1049611 : Blo 932582 1049611 := bstep (se 1 (by rfl) ⟨787208, by rfl⟩ : syracuseStep 1049611 = 1574417) B1574417
theorem B1180747 : Blo 932582 1180747 := bstep (se 1 (by rfl) ⟨885560, by rfl⟩ : syracuseStep 1180747 = 1771121) B1771121
theorem B1999961 : Blo 932582 1999961 := bstep (se 2 (by rfl) ⟨749985, by rfl⟩ : syracuseStep 1999961 = 1499971) B1499971
theorem B276661361 : Blo 932582 276661361 := bstep (se 2 (by rfl) ⟨103748010, by rfl⟩ : syracuseStep 276661361 = 207496021) B207496021
theorem B1049719 : Blo 932582 1049719 := bstep (se 1 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 1049719 = 1574579) B1574579
theorem B1770635 : Blo 932582 1770635 := bstep (se 1 (by rfl) ⟨1327976, by rfl⟩ : syracuseStep 1770635 = 2655953) B2655953
theorem B1574039 : Blo 932582 1574039 := bstep (se 1 (by rfl) ⟨1180529, by rfl⟩ : syracuseStep 1574039 = 2361059) B2361059
theorem B1574167 : Blo 932582 1574167 := bstep (se 1 (by rfl) ⟨1180625, by rfl⟩ : syracuseStep 1574167 = 2361251) B2361251
theorem B2098457 : Blo 932582 2098457 := bstep (se 2 (by rfl) ⟨786921, by rfl⟩ : syracuseStep 2098457 = 1573843) B1573843
theorem B1049899 : Blo 932582 1049899 := bstep (se 1 (by rfl) ⟨787424, by rfl⟩ : syracuseStep 1049899 = 1574849) B1574849
theorem B1770817 : Blo 932582 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B6817117 : Blo 932582 6817117 := bstep (se 3 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 6817117 = 2556419) B2556419
theorem B7996765 : Blo 932582 7996765 := bstep (se 3 (by rfl) ⟨1499393, by rfl⟩ : syracuseStep 7996765 = 2998787) B2998787
theorem B2098547 : Blo 932582 2098547 := bstep (se 1 (by rfl) ⟨1573910, by rfl⟩ : syracuseStep 2098547 = 3147821) B3147821
theorem B1050007 : Blo 932582 1050007 := bstep (se 1 (by rfl) ⟨787505, by rfl⟩ : syracuseStep 1050007 = 1575011) B1575011
theorem B2098583 : Blo 932582 2098583 := bstep (se 1 (by rfl) ⟨1573937, by rfl⟩ : syracuseStep 2098583 = 3147875) B3147875
theorem B2360897 : Blo 932582 2360897 := bstep (se 2 (by rfl) ⟨885336, by rfl⟩ : syracuseStep 2360897 = 1770673) B1770673
theorem B2098763 : Blo 932582 2098763 := bstep (se 1 (by rfl) ⟨1574072, by rfl⟩ : syracuseStep 2098763 = 3148145) B3148145
theorem B6817355 : Blo 932582 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B1050187 : Blo 932582 1050187 := bstep (se 1 (by rfl) ⟨787640, by rfl⟩ : syracuseStep 1050187 = 1575281) B1575281
theorem B2098817 : Blo 932582 2098817 := bstep (se 2 (by rfl) ⟨787056, by rfl⟩ : syracuseStep 2098817 = 1574113) B1574113
theorem B1771159 : Blo 932582 1771159 := bstep (se 1 (by rfl) ⟨1328369, by rfl⟩ : syracuseStep 1771159 = 2656739) B2656739
theorem B1050295 : Blo 932582 1050295 := bstep (se 1 (by rfl) ⟨787721, by rfl⟩ : syracuseStep 1050295 = 1575443) B1575443
theorem B2099033 : Blo 932582 2099033 := bstep (se 2 (by rfl) ⟨787137, by rfl⟩ : syracuseStep 2099033 = 1574275) B1574275
theorem B1050475 : Blo 932582 1050475 := bstep (se 1 (by rfl) ⟨787856, by rfl⟩ : syracuseStep 1050475 = 1575713) B1575713
theorem B1771379 : Blo 932582 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1574795 : Blo 932582 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B2099123 : Blo 932582 2099123 := bstep (se 1 (by rfl) ⟨1574342, by rfl⟩ : syracuseStep 2099123 = 3148685) B3148685
theorem B3147713 : Blo 932582 3147713 := bstep (se 2 (by rfl) ⟨1180392, by rfl⟩ : syracuseStep 3147713 = 2360785) B2360785
theorem B2099159 : Blo 932582 2099159 := bstep (se 1 (by rfl) ⟨1574369, by rfl⟩ : syracuseStep 2099159 = 3148739) B3148739
theorem B1050583 : Blo 932582 1050583 := bstep (se 1 (by rfl) ⟨787937, by rfl⟩ : syracuseStep 1050583 = 1575875) B1575875
theorem B1574923 : Blo 932582 1574923 := bstep (se 1 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 1574923 = 2362385) B2362385
theorem B1181719 : Blo 932582 1181719 := bstep (se 1 (by rfl) ⟨886289, by rfl⟩ : syracuseStep 1181719 = 1772579) B1772579
theorem B1771607 : Blo 932582 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B2361433 : Blo 932582 2361433 := bstep (se 2 (by rfl) ⟨885537, by rfl⟩ : syracuseStep 2361433 = 1771075) B1771075
theorem B2099339 : Blo 932582 2099339 := bstep (se 1 (by rfl) ⟨1574504, by rfl⟩ : syracuseStep 2099339 = 3149009) B3149009
theorem B1050763 : Blo 932582 1050763 := bstep (se 1 (by rfl) ⟨788072, by rfl⟩ : syracuseStep 1050763 = 1576145) B1576145
theorem B1575065 : Blo 932582 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B2099393 : Blo 932582 2099393 := bstep (se 2 (by rfl) ⟨787272, by rfl⟩ : syracuseStep 2099393 = 1574545) B1574545
theorem B1050871 : Blo 932582 1050871 := bstep (se 1 (by rfl) ⟨788153, by rfl⟩ : syracuseStep 1050871 = 1576307) B1576307
theorem B1575193 : Blo 932582 1575193 := bstep (se 2 (by rfl) ⟨590697, by rfl⟩ : syracuseStep 1575193 = 1181395) B1181395
theorem B1771865 : Blo 932582 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B2099609 : Blo 932582 2099609 := bstep (se 2 (by rfl) ⟨787353, by rfl⟩ : syracuseStep 2099609 = 1574707) B1574707
theorem B1051051 : Blo 932582 1051051 := bstep (se 1 (by rfl) ⟨788288, by rfl⟩ : syracuseStep 1051051 = 1576577) B1576577
theorem B3541421 : Blo 932582 3541421 := bstep (se 3 (by rfl) ⟨664016, by rfl⟩ : syracuseStep 3541421 = 1328033) B1328033
theorem B3148253 : Blo 932582 3148253 := bstep (se 3 (by rfl) ⟨590297, by rfl⟩ : syracuseStep 3148253 = 1180595) B1180595
theorem B2099699 : Blo 932582 2099699 := bstep (se 1 (by rfl) ⟨1574774, by rfl⟩ : syracuseStep 2099699 = 3149549) B3149549
theorem B2099735 : Blo 932582 2099735 := bstep (se 1 (by rfl) ⟨1574801, by rfl⟩ : syracuseStep 2099735 = 3149603) B3149603
theorem B1051159 : Blo 932582 1051159 := bstep (se 1 (by rfl) ⟨788369, by rfl⟩ : syracuseStep 1051159 = 1576739) B1576739
theorem B2099915 : Blo 932582 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B1051339 : Blo 932582 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B1772275 : Blo 932582 1772275 := bstep (se 1 (by rfl) ⟨1329206, by rfl⟩ : syracuseStep 1772275 = 2658413) B2658413
theorem B2099969 : Blo 932582 2099969 := bstep (se 2 (by rfl) ⟨787488, by rfl⟩ : syracuseStep 2099969 = 1574977) B1574977
theorem B1051447 : Blo 932582 1051447 := bstep (se 1 (by rfl) ⟨788585, by rfl⟩ : syracuseStep 1051447 = 1577171) B1577171
theorem B1182539 : Blo 932582 1182539 := bstep (se 1 (by rfl) ⟨886904, by rfl⟩ : syracuseStep 1182539 = 1773809) B1773809
theorem B1575767 : Blo 932582 1575767 := bstep (se 1 (by rfl) ⟨1181825, by rfl⟩ : syracuseStep 1575767 = 2363651) B2363651
theorem B1575895 : Blo 932582 1575895 := bstep (se 1 (by rfl) ⟨1181921, by rfl⟩ : syracuseStep 1575895 = 2363843) B2363843
theorem B2100185 : Blo 932582 2100185 := bstep (se 2 (by rfl) ⟨787569, by rfl⟩ : syracuseStep 2100185 = 1575139) B1575139
theorem B1051627 : Blo 932582 1051627 := bstep (se 1 (by rfl) ⟨788720, by rfl⟩ : syracuseStep 1051627 = 1577441) B1577441
theorem B2100275 : Blo 932582 2100275 := bstep (se 1 (by rfl) ⟨1575206, by rfl⟩ : syracuseStep 2100275 = 3150413) B3150413
theorem B2100311 : Blo 932582 2100311 := bstep (se 1 (by rfl) ⟨1575233, by rfl⟩ : syracuseStep 2100311 = 3150467) B3150467
theorem B1051735 : Blo 932582 1051735 := bstep (se 1 (by rfl) ⟨788801, by rfl⟩ : syracuseStep 1051735 = 1577603) B1577603
theorem B2362547 : Blo 932582 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B3837131 : Blo 932582 3837131 := bstep (se 1 (by rfl) ⟨2877848, by rfl⟩ : syracuseStep 3837131 = 5755697) B5755697
theorem B1772761 : Blo 932582 1772761 := bstep (se 2 (by rfl) ⟨664785, by rfl⟩ : syracuseStep 1772761 = 1329571) B1329571
theorem B2100491 : Blo 932582 2100491 := bstep (se 1 (by rfl) ⟨1575368, by rfl⟩ : syracuseStep 2100491 = 3150737) B3150737
theorem B1051915 : Blo 932582 1051915 := bstep (se 1 (by rfl) ⟨788936, by rfl⟩ : syracuseStep 1051915 = 1577873) B1577873
theorem B2100545 : Blo 932582 2100545 := bstep (se 2 (by rfl) ⟨787704, by rfl⟩ : syracuseStep 2100545 = 1575409) B1575409
theorem B1281367 : Blo 932582 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B1052023 : Blo 932582 1052023 := bstep (se 1 (by rfl) ⟨789017, by rfl⟩ : syracuseStep 1052023 = 1578035) B1578035
theorem B4722137 : Blo 932582 4722137 := bstep (se 2 (by rfl) ⟨1770801, by rfl⟩ : syracuseStep 4722137 = 3541603) B3541603
theorem B2362841 : Blo 932582 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B1183243 : Blo 932582 1183243 := bstep (se 1 (by rfl) ⟨887432, by rfl⟩ : syracuseStep 1183243 = 1774865) B1774865
theorem B2100761 : Blo 932582 2100761 := bstep (se 2 (by rfl) ⟨787785, by rfl⟩ : syracuseStep 2100761 = 1575571) B1575571
theorem B1052203 : Blo 932582 1052203 := bstep (se 1 (by rfl) ⟨789152, by rfl⟩ : syracuseStep 1052203 = 1578305) B1578305
theorem B2657843 : Blo 932582 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B3149387 : Blo 932582 3149387 := bstep (se 1 (by rfl) ⟨2362040, by rfl⟩ : syracuseStep 3149387 = 4724081) B4724081
theorem B1576523 : Blo 932582 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B2100851 : Blo 932582 2100851 := bstep (se 1 (by rfl) ⟨1575638, by rfl⟩ : syracuseStep 2100851 = 3151277) B3151277
theorem B2100887 : Blo 932582 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B1052311 : Blo 932582 1052311 := bstep (se 1 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 1052311 = 1578467) B1578467
theorem B1576651 : Blo 932582 1576651 := bstep (se 1 (by rfl) ⟨1182488, by rfl⟩ : syracuseStep 1576651 = 2364977) B2364977
theorem B1773323 : Blo 932582 1773323 := bstep (se 1 (by rfl) ⟨1329992, by rfl⟩ : syracuseStep 1773323 = 2659985) B2659985
theorem B2658071 : Blo 932582 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B1183511 : Blo 932582 1183511 := bstep (se 1 (by rfl) ⟨887633, by rfl⟩ : syracuseStep 1183511 = 1775267) B1775267
theorem B3542849 : Blo 932582 3542849 := bstep (se 2 (by rfl) ⟨1328568, by rfl⟩ : syracuseStep 3542849 = 2657137) B2657137
theorem B2101067 : Blo 932582 2101067 := bstep (se 1 (by rfl) ⟨1575800, by rfl⟩ : syracuseStep 2101067 = 3151601) B3151601
theorem B1052491 : Blo 932582 1052491 := bstep (se 1 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 1052491 = 1578737) B1578737
theorem B3149657 : Blo 932582 3149657 := bstep (se 2 (by rfl) ⟨1181121, by rfl⟩ : syracuseStep 3149657 = 2362243) B2362243
theorem B2395993 : Blo 932582 2395993 := bstep (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) B1796995
theorem B1576793 : Blo 932582 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B2101121 : Blo 932582 2101121 := bstep (se 2 (by rfl) ⟨787920, by rfl⟩ : syracuseStep 2101121 = 1575841) B1575841
theorem B1052599 : Blo 932582 1052599 := bstep (se 1 (by rfl) ⟨789449, by rfl⟩ : syracuseStep 1052599 = 1578899) B1578899
theorem B1773505 : Blo 932582 1773505 := bstep (se 2 (by rfl) ⟨665064, by rfl⟩ : syracuseStep 1773505 = 1330129) B1330129
theorem B1576921 : Blo 932582 1576921 := bstep (se 2 (by rfl) ⟨591345, by rfl⟩ : syracuseStep 1576921 = 1182691) B1182691
theorem B5312587 : Blo 932582 5312587 := bstep (se 1 (by rfl) ⟨3984440, by rfl⟩ : syracuseStep 5312587 = 7968881) B7968881
theorem B2658379 : Blo 932582 2658379 := bstep (se 1 (by rfl) ⟨1993784, by rfl⟩ : syracuseStep 2658379 = 3987569) B3987569
theorem B2101337 : Blo 932582 2101337 := bstep (se 2 (by rfl) ⟨788001, by rfl⟩ : syracuseStep 2101337 = 1576003) B1576003
theorem B1052779 : Blo 932582 1052779 := bstep (se 1 (by rfl) ⟨789584, by rfl⟩ : syracuseStep 1052779 = 1579169) B1579169
theorem B2101427 : Blo 932582 2101427 := bstep (se 1 (by rfl) ⟨1576070, by rfl⟩ : syracuseStep 2101427 = 3152141) B3152141
theorem B2101463 : Blo 932582 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B1052887 : Blo 932582 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B1708249 : Blo 932582 1708249 := bstep (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) B1281187
theorem B8982829 : Blo 932582 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B5312861 : Blo 932582 5312861 := bstep (se 3 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 5312861 = 1992323) B1992323
theorem B2658653 : Blo 932582 2658653 := bstep (se 3 (by rfl) ⟨498497, by rfl⟩ : syracuseStep 2658653 = 996995) B996995
theorem B2101643 : Blo 932582 2101643 := bstep (se 1 (by rfl) ⟨1576232, by rfl⟩ : syracuseStep 2101643 = 3152465) B3152465
theorem B1053067 : Blo 932582 1053067 := bstep (se 1 (by rfl) ⟨789800, by rfl⟩ : syracuseStep 1053067 = 1579601) B1579601
theorem B2101697 : Blo 932582 2101697 := bstep (se 2 (by rfl) ⟨788136, by rfl⟩ : syracuseStep 2101697 = 1576273) B1576273
theorem B1184215 : Blo 932582 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1053175 : Blo 932582 1053175 := bstep (se 1 (by rfl) ⟨789881, by rfl⟩ : syracuseStep 1053175 = 1579763) B1579763
theorem B3150359 : Blo 932582 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B1577495 : Blo 932582 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1774219 : Blo 932582 1774219 := bstep (se 1 (by rfl) ⟨1330664, by rfl⟩ : syracuseStep 1774219 = 2661329) B2661329
theorem B1577623 : Blo 932582 1577623 := bstep (se 1 (by rfl) ⟨1183217, by rfl⟩ : syracuseStep 1577623 = 2366435) B2366435
theorem B2101913 : Blo 932582 2101913 := bstep (se 2 (by rfl) ⟨788217, by rfl⟩ : syracuseStep 2101913 = 1576435) B1576435
theorem B1053355 : Blo 932582 1053355 := bstep (se 1 (by rfl) ⟨790016, by rfl⟩ : syracuseStep 1053355 = 1580033) B1580033
theorem B1774295 : Blo 932582 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B2102003 : Blo 932582 2102003 := bstep (se 1 (by rfl) ⟨1576502, by rfl⟩ : syracuseStep 2102003 = 3153005) B3153005
theorem B2102039 : Blo 932582 2102039 := bstep (se 1 (by rfl) ⟨1576529, by rfl⟩ : syracuseStep 2102039 = 3153059) B3153059
theorem B1053463 : Blo 932582 1053463 := bstep (se 1 (by rfl) ⟨790097, by rfl⟩ : syracuseStep 1053463 = 1580195) B1580195
theorem B2102219 : Blo 932582 2102219 := bstep (se 1 (by rfl) ⟨1576664, by rfl⟩ : syracuseStep 2102219 = 3153329) B3153329
theorem B1053643 : Blo 932582 1053643 := bstep (se 1 (by rfl) ⟨790232, by rfl⟩ : syracuseStep 1053643 = 1580465) B1580465
theorem B2102273 : Blo 932582 2102273 := bstep (se 2 (by rfl) ⟨788352, by rfl⟩ : syracuseStep 2102273 = 1576705) B1576705
theorem B4723757 : Blo 932582 4723757 := bstep (se 3 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 4723757 = 1771409) B1771409
theorem B3150899 : Blo 932582 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B2364491 : Blo 932582 2364491 := bstep (se 1 (by rfl) ⟨1773368, by rfl⟩ : syracuseStep 2364491 = 3546737) B3546737
theorem B2528435 : Blo 932582 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B2102489 : Blo 932582 2102489 := bstep (se 2 (by rfl) ⟨788433, by rfl⟩ : syracuseStep 2102489 = 1576867) B1576867
theorem B1578251 : Blo 932582 1578251 := bstep (se 1 (by rfl) ⟨1183688, by rfl⟩ : syracuseStep 1578251 = 2367377) B2367377
theorem B3544337 : Blo 932582 3544337 := bstep (se 2 (by rfl) ⟨1329126, by rfl⟩ : syracuseStep 3544337 = 2658253) B2658253
theorem B2102579 : Blo 932582 2102579 := bstep (se 1 (by rfl) ⟨1576934, by rfl⟩ : syracuseStep 2102579 = 3153869) B3153869
theorem B3151169 : Blo 932582 3151169 := bstep (se 2 (by rfl) ⟨1181688, by rfl⟩ : syracuseStep 3151169 = 2363377) B2363377
theorem B2102615 : Blo 932582 2102615 := bstep (se 1 (by rfl) ⟨1576961, by rfl⟩ : syracuseStep 2102615 = 3153923) B3153923
theorem B1774963 : Blo 932582 1774963 := bstep (se 1 (by rfl) ⟨1331222, by rfl⟩ : syracuseStep 1774963 = 2662445) B2662445
theorem B7968131 : Blo 932582 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1578379 : Blo 932582 1578379 := bstep (se 1 (by rfl) ⟨1183784, by rfl⟩ : syracuseStep 1578379 = 2367569) B2367569
theorem B2102795 : Blo 932582 2102795 := bstep (se 1 (by rfl) ⟨1577096, by rfl⟩ : syracuseStep 2102795 = 3154193) B3154193
theorem B1578521 : Blo 932582 1578521 := bstep (se 2 (by rfl) ⟨591945, by rfl⟩ : syracuseStep 1578521 = 1183891) B1183891
theorem B2102849 : Blo 932582 2102849 := bstep (se 2 (by rfl) ⟨788568, by rfl⟩ : syracuseStep 2102849 = 1577137) B1577137
theorem B1480279 : Blo 932582 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B1775191 : Blo 932582 1775191 := bstep (se 1 (by rfl) ⟨1331393, by rfl⟩ : syracuseStep 1775191 = 2662787) B2662787
theorem B4789853 : Blo 932582 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B1578649 : Blo 932582 1578649 := bstep (se 2 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 1578649 = 1183987) B1183987
theorem B1775297 : Blo 932582 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B3544793 : Blo 932582 3544793 := bstep (se 2 (by rfl) ⟨1329297, by rfl⟩ : syracuseStep 3544793 = 2658595) B2658595
theorem B2103065 : Blo 932582 2103065 := bstep (se 2 (by rfl) ⟨788649, by rfl⟩ : syracuseStep 2103065 = 1577299) B1577299
theorem B1775449 : Blo 932582 1775449 := bstep (se 2 (by rfl) ⟨665793, by rfl⟩ : syracuseStep 1775449 = 1331587) B1331587
theorem B3151709 : Blo 932582 3151709 := bstep (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) B1181891
theorem B2103155 : Blo 932582 2103155 := bstep (se 1 (by rfl) ⟨1577366, by rfl⟩ : syracuseStep 2103155 = 3154733) B3154733
theorem B2103191 : Blo 932582 2103191 := bstep (se 1 (by rfl) ⟨1577393, by rfl⟩ : syracuseStep 2103191 = 3154787) B3154787
theorem B3545005 : Blo 932582 3545005 := bstep (se 3 (by rfl) ⟨664688, by rfl⟩ : syracuseStep 3545005 = 1329377) B1329377
theorem B11999249 : Blo 932582 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B2365463 : Blo 932582 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B2103371 : Blo 932582 2103371 := bstep (se 1 (by rfl) ⟨1577528, by rfl⟩ : syracuseStep 2103371 = 3155057) B3155057
theorem B2103425 : Blo 932582 2103425 := bstep (se 2 (by rfl) ⟨788784, by rfl⟩ : syracuseStep 2103425 = 1577569) B1577569
theorem B8624333 : Blo 932582 8624333 := bstep (se 3 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 8624333 = 3234125) B3234125
theorem B9607373 : Blo 932582 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B1579223 : Blo 932582 1579223 := bstep (se 1 (by rfl) ⟨1184417, by rfl⟩ : syracuseStep 1579223 = 2368835) B2368835
theorem B3545309 : Blo 932582 3545309 := bstep (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) B1329491
theorem B1579351 : Blo 932582 1579351 := bstep (se 1 (by rfl) ⟨1184513, by rfl⟩ : syracuseStep 1579351 = 2369027) B2369027
theorem B2103641 : Blo 932582 2103641 := bstep (se 2 (by rfl) ⟨788865, by rfl⟩ : syracuseStep 2103641 = 1577731) B1577731
theorem B1120663 : Blo 932582 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B2660759 : Blo 932582 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B2103731 : Blo 932582 2103731 := bstep (se 1 (by rfl) ⟨1577798, by rfl⟩ : syracuseStep 2103731 = 3155597) B3155597
theorem B2103767 : Blo 932582 2103767 := bstep (se 1 (by rfl) ⟨1577825, by rfl⟩ : syracuseStep 2103767 = 3155651) B3155651
theorem B2103947 : Blo 932582 2103947 := bstep (se 1 (by rfl) ⟨1577960, by rfl⟩ : syracuseStep 2103947 = 3155921) B3155921
theorem B2366131 : Blo 932582 2366131 := bstep (se 1 (by rfl) ⟨1774598, by rfl⟩ : syracuseStep 2366131 = 3549197) B3549197
theorem B2104001 : Blo 932582 2104001 := bstep (se 2 (by rfl) ⟨789000, by rfl⟩ : syracuseStep 2104001 = 1578001) B1578001
theorem B4266769 : Blo 932582 4266769 := bstep (se 2 (by rfl) ⟨1600038, by rfl⟩ : syracuseStep 4266769 = 3200077) B3200077
theorem B2366273 : Blo 932582 2366273 := bstep (se 2 (by rfl) ⟨887352, by rfl⟩ : syracuseStep 2366273 = 1774705) B1774705
theorem B2104217 : Blo 932582 2104217 := bstep (se 2 (by rfl) ⟨789081, by rfl⟩ : syracuseStep 2104217 = 1578163) B1578163
theorem B3152843 : Blo 932582 3152843 := bstep (se 1 (by rfl) ⟨2364632, by rfl⟩ : syracuseStep 3152843 = 4729265) B4729265
theorem B1579979 : Blo 932582 1579979 := bstep (se 1 (by rfl) ⟨1184984, by rfl⟩ : syracuseStep 1579979 = 2369969) B2369969
theorem B2104307 : Blo 932582 2104307 := bstep (se 1 (by rfl) ⟨1578230, by rfl⟩ : syracuseStep 2104307 = 3156461) B3156461
theorem B2104343 : Blo 932582 2104343 := bstep (se 1 (by rfl) ⟨1578257, by rfl⟩ : syracuseStep 2104343 = 3156515) B3156515
theorem B1580107 : Blo 932582 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B1776755 : Blo 932582 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B2661569 : Blo 932582 2661569 := bstep (se 2 (by rfl) ⟨998088, by rfl⟩ : syracuseStep 2661569 = 1996177) B1996177
theorem B2104523 : Blo 932582 2104523 := bstep (se 1 (by rfl) ⟨1578392, by rfl⟩ : syracuseStep 2104523 = 3156785) B3156785
theorem B3153113 : Blo 932582 3153113 := bstep (se 2 (by rfl) ⟨1182417, by rfl⟩ : syracuseStep 3153113 = 2364835) B2364835
theorem B1580249 : Blo 932582 1580249 := bstep (se 2 (by rfl) ⟨592593, by rfl⟩ : syracuseStep 1580249 = 1185187) B1185187
theorem B2104577 : Blo 932582 2104577 := bstep (se 2 (by rfl) ⟨789216, by rfl⟩ : syracuseStep 2104577 = 1578433) B1578433
theorem B1776907 : Blo 932582 1776907 := bstep (se 1 (by rfl) ⟨1332680, by rfl⟩ : syracuseStep 1776907 = 2665361) B2665361
theorem B1580377 : Blo 932582 1580377 := bstep (se 2 (by rfl) ⟨592641, by rfl⟩ : syracuseStep 1580377 = 1185283) B1185283
theorem B6724957 : Blo 932582 6724957 := bstep (se 3 (by rfl) ⟨1260929, by rfl⟩ : syracuseStep 6724957 = 2521859) B2521859
theorem B6725015 : Blo 932582 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B3841453 : Blo 932582 3841453 := bstep (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) B1440545
theorem B2104793 : Blo 932582 2104793 := bstep (se 2 (by rfl) ⟨789297, by rfl⟩ : syracuseStep 2104793 = 1578595) B1578595
theorem B2104883 : Blo 932582 2104883 := bstep (se 1 (by rfl) ⟨1578662, by rfl⟩ : syracuseStep 2104883 = 3157325) B3157325
theorem B2104919 : Blo 932582 2104919 := bstep (se 1 (by rfl) ⟨1578689, by rfl⟩ : syracuseStep 2104919 = 3157379) B3157379
theorem B1777241 : Blo 932582 1777241 := bstep (se 2 (by rfl) ⟨666465, by rfl⟩ : syracuseStep 1777241 = 1332931) B1332931
theorem B7970521 : Blo 932582 7970521 := bstep (se 2 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 7970521 = 5977891) B5977891
theorem B2105099 : Blo 932582 2105099 := bstep (se 1 (by rfl) ⟨1578824, by rfl⟩ : syracuseStep 2105099 = 3157649) B3157649
theorem B2105153 : Blo 932582 2105153 := bstep (se 2 (by rfl) ⟨789432, by rfl⟩ : syracuseStep 2105153 = 1578865) B1578865
theorem B3153815 : Blo 932582 3153815 := bstep (se 1 (by rfl) ⟨2365361, by rfl⟩ : syracuseStep 3153815 = 4730723) B4730723
theorem B2105369 : Blo 932582 2105369 := bstep (se 2 (by rfl) ⟨789513, by rfl⟩ : syracuseStep 2105369 = 1579027) B1579027
theorem B2367539 : Blo 932582 2367539 := bstep (se 1 (by rfl) ⟨1775654, by rfl⟩ : syracuseStep 2367539 = 3551309) B3551309
theorem B2105459 : Blo 932582 2105459 := bstep (se 1 (by rfl) ⟨1579094, by rfl⟩ : syracuseStep 2105459 = 3158189) B3158189
theorem B2105495 : Blo 932582 2105495 := bstep (se 1 (by rfl) ⟨1579121, by rfl⟩ : syracuseStep 2105495 = 3158243) B3158243
theorem B1777879 : Blo 932582 1777879 := bstep (se 1 (by rfl) ⟨1333409, by rfl⟩ : syracuseStep 1777879 = 2666819) B2666819
theorem B2105675 : Blo 932582 2105675 := bstep (se 1 (by rfl) ⟨1579256, by rfl⟩ : syracuseStep 2105675 = 3158513) B3158513
theorem B2105729 : Blo 932582 2105729 := bstep (se 2 (by rfl) ⟨789648, by rfl⟩ : syracuseStep 2105729 = 1579297) B1579297
theorem B3154355 : Blo 932582 3154355 := bstep (se 1 (by rfl) ⟨2365766, by rfl⟩ : syracuseStep 3154355 = 4731533) B4731533
theorem B2368075 : Blo 932582 2368075 := bstep (se 1 (by rfl) ⟨1776056, by rfl⟩ : syracuseStep 2368075 = 3552113) B3552113
theorem B2105945 : Blo 932582 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B7971479 : Blo 932582 7971479 := bstep (se 1 (by rfl) ⟨5978609, by rfl⟩ : syracuseStep 7971479 = 11957219) B11957219
theorem B2106035 : Blo 932582 2106035 := bstep (se 1 (by rfl) ⟨1579526, by rfl⟩ : syracuseStep 2106035 = 3159053) B3159053
theorem B3154625 : Blo 932582 3154625 := bstep (se 2 (by rfl) ⟨1182984, by rfl⟩ : syracuseStep 3154625 = 2365969) B2365969
theorem B2106071 : Blo 932582 2106071 := bstep (se 1 (by rfl) ⟨1579553, by rfl⟩ : syracuseStep 2106071 = 3159107) B3159107
theorem B2368217 : Blo 932582 2368217 := bstep (se 2 (by rfl) ⟨888081, by rfl⟩ : syracuseStep 2368217 = 1776163) B1776163
theorem B3547907 : Blo 932582 3547907 := bstep (se 1 (by rfl) ⟨2660930, by rfl⟩ : syracuseStep 3547907 = 5321861) B5321861
theorem B3547921 : Blo 932582 3547921 := bstep (se 2 (by rfl) ⟨1330470, by rfl⟩ : syracuseStep 3547921 = 2660941) B2660941
theorem B2663219 : Blo 932582 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B2663243 : Blo 932582 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B4727645 : Blo 932582 4727645 := bstep (se 3 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 4727645 = 1772867) B1772867
theorem B2106251 : Blo 932582 2106251 := bstep (se 1 (by rfl) ⟨1579688, by rfl⟩ : syracuseStep 2106251 = 3159377) B3159377
theorem B2106305 : Blo 932582 2106305 := bstep (se 2 (by rfl) ⟨789864, by rfl⟩ : syracuseStep 2106305 = 1579729) B1579729
theorem B15934481 : Blo 932582 15934481 := bstep (se 2 (by rfl) ⟨5975430, by rfl⟩ : syracuseStep 15934481 = 11950861) B11950861
theorem B7971857 : Blo 932582 7971857 := bstep (se 2 (by rfl) ⟨2989446, by rfl⟩ : syracuseStep 7971857 = 5978893) B5978893
theorem B3548225 : Blo 932582 3548225 := bstep (se 2 (by rfl) ⟨1330584, by rfl⟩ : syracuseStep 3548225 = 2661169) B2661169
theorem B2106521 : Blo 932582 2106521 := bstep (se 2 (by rfl) ⟨789945, by rfl⟩ : syracuseStep 2106521 = 1579891) B1579891
theorem B3155165 : Blo 932582 3155165 := bstep (se 3 (by rfl) ⟨591593, by rfl⟩ : syracuseStep 3155165 = 1183187) B1183187
theorem B2106611 : Blo 932582 2106611 := bstep (se 1 (by rfl) ⟨1579958, by rfl⟩ : syracuseStep 2106611 = 3159917) B3159917
theorem B2106647 : Blo 932582 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B2106827 : Blo 932582 2106827 := bstep (se 1 (by rfl) ⟨1580120, by rfl⟩ : syracuseStep 2106827 = 3160241) B3160241
theorem B2106881 : Blo 932582 2106881 := bstep (se 2 (by rfl) ⟨790080, by rfl⟩ : syracuseStep 2106881 = 1580161) B1580161
theorem B2369047 : Blo 932582 2369047 := bstep (se 1 (by rfl) ⟨1776785, by rfl⟩ : syracuseStep 2369047 = 3553571) B3553571
theorem B1418777 : Blo 932582 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B5318237 : Blo 932582 5318237 := bstep (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) B1994339
theorem B2664029 : Blo 932582 2664029 := bstep (se 3 (by rfl) ⟨499505, by rfl⟩ : syracuseStep 2664029 = 999011) B999011
theorem B2107097 : Blo 932582 2107097 := bstep (se 2 (by rfl) ⟨790161, by rfl⟩ : syracuseStep 2107097 = 1580323) B1580323
theorem B3548893 : Blo 932582 3548893 := bstep (se 3 (by rfl) ⟨665417, by rfl⟩ : syracuseStep 3548893 = 1330835) B1330835
theorem B2107187 : Blo 932582 2107187 := bstep (se 1 (by rfl) ⟨1580390, by rfl⟩ : syracuseStep 2107187 = 3160781) B3160781
theorem B2107223 : Blo 932582 2107223 := bstep (se 1 (by rfl) ⟨1580417, by rfl⟩ : syracuseStep 2107223 = 3160835) B3160835
theorem B1681355 : Blo 932582 1681355 := bstep (se 1 (by rfl) ⟨1261016, by rfl⟩ : syracuseStep 1681355 = 2522033) B2522033
theorem B2369483 : Blo 932582 2369483 := bstep (se 1 (by rfl) ⟨1777112, by rfl⟩ : syracuseStep 2369483 = 3554225) B3554225
theorem B10102745 : Blo 932582 10102745 := bstep (se 2 (by rfl) ⟨3788529, by rfl⟩ : syracuseStep 10102745 = 7577059) B7577059
theorem B4499549 : Blo 932582 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B10102915 : Blo 932582 10102915 := bstep (se 1 (by rfl) ⟨7577186, by rfl⟩ : syracuseStep 10102915 = 15154373) B15154373
theorem B2369857 : Blo 932582 2369857 := bstep (se 2 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 2369857 = 1777393) B1777393
theorem B3156299 : Blo 932582 3156299 := bstep (se 1 (by rfl) ⟨2367224, by rfl⟩ : syracuseStep 3156299 = 4734449) B4734449
theorem B1124695 : Blo 932582 1124695 := bstep (se 1 (by rfl) ⟨843521, by rfl⟩ : syracuseStep 1124695 = 1687043) B1687043
theorem B2992535 : Blo 932582 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B3156569 : Blo 932582 3156569 := bstep (se 2 (by rfl) ⟨1183713, by rfl⟩ : syracuseStep 3156569 = 2367427) B2367427
theorem B1518359 : Blo 932582 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B5679973 : Blo 932582 5679973 := bstep (se 4 (by rfl) ⟨532497, by rfl⟩ : syracuseStep 5679973 = 1064995) B1064995
theorem B1420183 : Blo 932582 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B4729751 : Blo 932582 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B2370455 : Blo 932582 2370455 := bstep (se 1 (by rfl) ⟨1777841, by rfl⟩ : syracuseStep 2370455 = 3555683) B3555683
theorem B3550169 : Blo 932582 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B3157271 : Blo 932582 3157271 := bstep (se 1 (by rfl) ⟨2367953, by rfl⟩ : syracuseStep 3157271 = 4735907) B4735907
theorem B5680459 : Blo 932582 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B2665817 : Blo 932582 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B34614641 : Blo 932582 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B2993611 : Blo 932582 2993611 := bstep (se 1 (by rfl) ⟨2245208, by rfl⟩ : syracuseStep 2993611 = 4490417) B4490417
theorem B6729281 : Blo 932582 6729281 := bstep (se 2 (by rfl) ⟨2523480, by rfl⟩ : syracuseStep 6729281 = 5046961) B5046961
theorem B2993753 : Blo 932582 2993753 := bstep (se 2 (by rfl) ⟨1122657, by rfl⟩ : syracuseStep 2993753 = 2245315) B2245315
theorem B2666135 : Blo 932582 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B3157811 : Blo 932582 3157811 := bstep (se 1 (by rfl) ⟨2368358, by rfl⟩ : syracuseStep 3157811 = 4736717) B4736717
theorem B3158081 : Blo 932582 3158081 := bstep (se 2 (by rfl) ⟨1184280, by rfl⟩ : syracuseStep 3158081 = 2368561) B2368561
theorem B5320835 : Blo 932582 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B6467885 : Blo 932582 6467885 := bstep (se 3 (by rfl) ⟨1212728, by rfl⟩ : syracuseStep 6467885 = 2425457) B2425457
theorem B5058881 : Blo 932582 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B2666945 : Blo 932582 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B2699741 : Blo 932582 2699741 := bstep (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) B1012403
theorem B3551795 : Blo 932582 3551795 := bstep (se 1 (by rfl) ⟨2663846, by rfl⟩ : syracuseStep 3551795 = 5327693) B5327693
theorem B3551809 : Blo 932582 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B3158621 : Blo 932582 3158621 := bstep (se 3 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 3158621 = 1184483) B1184483
theorem B2994995 : Blo 932582 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B996247 : Blo 932582 996247 := bstep (se 1 (by rfl) ⟨747185, by rfl⟩ : syracuseStep 996247 = 1494371) B1494371
theorem B2995393 : Blo 932582 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B996619 : Blo 932582 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B4797713 : Blo 932582 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B2242009 : Blo 932582 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B3651265 : Blo 932582 3651265 := bstep (se 2 (by rfl) ⟨1369224, by rfl⟩ : syracuseStep 3651265 = 2738449) B2738449
theorem B34059973 : Blo 932582 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B997067 : Blo 932582 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B3159755 : Blo 932582 3159755 := bstep (se 1 (by rfl) ⟨2369816, by rfl⟩ : syracuseStep 3159755 = 4739633) B4739633
theorem B5060369 : Blo 932582 5060369 := bstep (se 2 (by rfl) ⟨1897638, by rfl⟩ : syracuseStep 5060369 = 3795277) B3795277
theorem B3160025 : Blo 932582 3160025 := bstep (se 2 (by rfl) ⟨1185009, by rfl⟩ : syracuseStep 3160025 = 2370019) B2370019
theorem B3192797 : Blo 932582 3192797 := bstep (se 3 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 3192797 = 1197299) B1197299
theorem B4733315 : Blo 932582 4733315 := bstep (se 1 (by rfl) ⟨3549986, by rfl⟩ : syracuseStep 4733315 = 7099973) B7099973
theorem B1685953 : Blo 932582 1685953 := bstep (se 2 (by rfl) ⟨632232, by rfl⟩ : syracuseStep 1685953 = 1264465) B1264465
theorem B3553739 : Blo 932582 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B3553753 : Blo 932582 3553753 := bstep (se 2 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 3553753 = 2665315) B2665315
theorem B14006915 : Blo 932582 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B3160727 : Blo 932582 3160727 := bstep (se 1 (by rfl) ⟨2370545, by rfl⟩ : syracuseStep 3160727 = 4741091) B4741091
theorem B932587 : Blo 932582 932587 := bstep (se 1 (by rfl) ⟨699440, by rfl⟩ : syracuseStep 932587 = 1398881) B1398881
theorem B932599 : Blo 932582 932599 := bstep (se 1 (by rfl) ⟨699449, by rfl⟩ : syracuseStep 932599 = 1398899) B1398899
theorem B932619 : Blo 932582 932619 := bstep (se 1 (by rfl) ⟨699464, by rfl⟩ : syracuseStep 932619 = 1398929) B1398929
theorem B932631 : Blo 932582 932631 := bstep (se 1 (by rfl) ⟨699473, by rfl⟩ : syracuseStep 932631 = 1398947) B1398947
theorem B932651 : Blo 932582 932651 := bstep (se 1 (by rfl) ⟨699488, by rfl⟩ : syracuseStep 932651 = 1398977) B1398977
theorem B932663 : Blo 932582 932663 := bstep (se 1 (by rfl) ⟨699497, by rfl⟩ : syracuseStep 932663 = 1398995) B1398995
theorem B24263489 : Blo 932582 24263489 := bstep (se 2 (by rfl) ⟨9098808, by rfl⟩ : syracuseStep 24263489 = 18197617) B18197617
theorem B932683 : Blo 932582 932683 := bstep (se 1 (by rfl) ⟨699512, by rfl⟩ : syracuseStep 932683 = 1399025) B1399025
theorem B932695 : Blo 932582 932695 := bstep (se 1 (by rfl) ⟨699521, by rfl⟩ : syracuseStep 932695 = 1399043) B1399043
theorem B932715 : Blo 932582 932715 := bstep (se 1 (by rfl) ⟨699536, by rfl⟩ : syracuseStep 932715 = 1399073) B1399073
theorem B932727 : Blo 932582 932727 := bstep (se 1 (by rfl) ⟨699545, by rfl⟩ : syracuseStep 932727 = 1399091) B1399091
theorem B998263 : Blo 932582 998263 := bstep (se 1 (by rfl) ⟨748697, by rfl⟩ : syracuseStep 998263 = 1497395) B1497395
theorem B932747 : Blo 932582 932747 := bstep (se 1 (by rfl) ⟨699560, by rfl⟩ : syracuseStep 932747 = 1399121) B1399121
theorem B932759 : Blo 932582 932759 := bstep (se 1 (by rfl) ⟨699569, by rfl⟩ : syracuseStep 932759 = 1399139) B1399139
theorem B932779 : Blo 932582 932779 := bstep (se 1 (by rfl) ⟨699584, by rfl⟩ : syracuseStep 932779 = 1399169) B1399169
theorem B7093169 : Blo 932582 7093169 := bstep (se 2 (by rfl) ⟨2659938, by rfl⟩ : syracuseStep 7093169 = 5319877) B5319877
theorem B932791 : Blo 932582 932791 := bstep (se 1 (by rfl) ⟨699593, by rfl⟩ : syracuseStep 932791 = 1399187) B1399187
theorem B932811 : Blo 932582 932811 := bstep (se 1 (by rfl) ⟨699608, by rfl⟩ : syracuseStep 932811 = 1399217) B1399217
theorem B932823 : Blo 932582 932823 := bstep (se 1 (by rfl) ⟨699617, by rfl⟩ : syracuseStep 932823 = 1399235) B1399235
theorem B932843 : Blo 932582 932843 := bstep (se 1 (by rfl) ⟨699632, by rfl⟩ : syracuseStep 932843 = 1399265) B1399265
theorem B932855 : Blo 932582 932855 := bstep (se 1 (by rfl) ⟨699641, by rfl⟩ : syracuseStep 932855 = 1399283) B1399283
theorem B932875 : Blo 932582 932875 := bstep (se 1 (by rfl) ⟨699656, by rfl⟩ : syracuseStep 932875 = 1399313) B1399313
theorem B932887 : Blo 932582 932887 := bstep (se 1 (by rfl) ⟨699665, by rfl⟩ : syracuseStep 932887 = 1399331) B1399331
theorem B932907 : Blo 932582 932907 := bstep (se 1 (by rfl) ⟨699680, by rfl⟩ : syracuseStep 932907 = 1399361) B1399361
theorem B998443 : Blo 932582 998443 := bstep (se 1 (by rfl) ⟨748832, by rfl⟩ : syracuseStep 998443 = 1497665) B1497665
theorem B932919 : Blo 932582 932919 := bstep (se 1 (by rfl) ⟨699689, by rfl⟩ : syracuseStep 932919 = 1399379) B1399379
theorem B932939 : Blo 932582 932939 := bstep (se 1 (by rfl) ⟨699704, by rfl⟩ : syracuseStep 932939 = 1399409) B1399409
theorem B932951 : Blo 932582 932951 := bstep (se 1 (by rfl) ⟨699713, by rfl⟩ : syracuseStep 932951 = 1399427) B1399427
theorem B932971 : Blo 932582 932971 := bstep (se 1 (by rfl) ⟨699728, by rfl⟩ : syracuseStep 932971 = 1399457) B1399457
theorem B932983 : Blo 932582 932983 := bstep (se 1 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 932983 = 1399475) B1399475
theorem B933003 : Blo 932582 933003 := bstep (se 1 (by rfl) ⟨699752, by rfl⟩ : syracuseStep 933003 = 1399505) B1399505
theorem B6077591 : Blo 932582 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B933015 : Blo 932582 933015 := bstep (se 1 (by rfl) ⟨699761, by rfl⟩ : syracuseStep 933015 = 1399523) B1399523
theorem B933035 : Blo 932582 933035 := bstep (se 1 (by rfl) ⟨699776, by rfl⟩ : syracuseStep 933035 = 1399553) B1399553
theorem B933047 : Blo 932582 933047 := bstep (se 1 (by rfl) ⟨699785, by rfl⟩ : syracuseStep 933047 = 1399571) B1399571
theorem B933067 : Blo 932582 933067 := bstep (se 1 (by rfl) ⟨699800, by rfl⟩ : syracuseStep 933067 = 1399601) B1399601
theorem B933079 : Blo 932582 933079 := bstep (se 1 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 933079 = 1399619) B1399619
theorem B933099 : Blo 932582 933099 := bstep (se 1 (by rfl) ⟨699824, by rfl⟩ : syracuseStep 933099 = 1399649) B1399649
theorem B933111 : Blo 932582 933111 := bstep (se 1 (by rfl) ⟨699833, by rfl⟩ : syracuseStep 933111 = 1399667) B1399667
theorem B933131 : Blo 932582 933131 := bstep (se 1 (by rfl) ⟨699848, by rfl⟩ : syracuseStep 933131 = 1399697) B1399697
theorem B933143 : Blo 932582 933143 := bstep (se 1 (by rfl) ⟨699857, by rfl⟩ : syracuseStep 933143 = 1399715) B1399715
theorem B933163 : Blo 932582 933163 := bstep (se 1 (by rfl) ⟨699872, by rfl⟩ : syracuseStep 933163 = 1399745) B1399745
theorem B933175 : Blo 932582 933175 := bstep (se 1 (by rfl) ⟨699881, by rfl⟩ : syracuseStep 933175 = 1399763) B1399763
theorem B933195 : Blo 932582 933195 := bstep (se 1 (by rfl) ⟨699896, by rfl⟩ : syracuseStep 933195 = 1399793) B1399793
theorem B933207 : Blo 932582 933207 := bstep (se 1 (by rfl) ⟨699905, by rfl⟩ : syracuseStep 933207 = 1399811) B1399811
theorem B933227 : Blo 932582 933227 := bstep (se 1 (by rfl) ⟨699920, by rfl⟩ : syracuseStep 933227 = 1399841) B1399841
theorem B933239 : Blo 932582 933239 := bstep (se 1 (by rfl) ⟨699929, by rfl⟩ : syracuseStep 933239 = 1399859) B1399859
theorem B933259 : Blo 932582 933259 := bstep (se 1 (by rfl) ⟨699944, by rfl⟩ : syracuseStep 933259 = 1399889) B1399889
theorem B933271 : Blo 932582 933271 := bstep (se 1 (by rfl) ⟨699953, by rfl⟩ : syracuseStep 933271 = 1399907) B1399907
theorem B7093655 : Blo 932582 7093655 := bstep (se 1 (by rfl) ⟨5320241, by rfl⟩ : syracuseStep 7093655 = 10640483) B10640483
theorem B3554711 : Blo 932582 3554711 := bstep (se 1 (by rfl) ⟨2666033, by rfl⟩ : syracuseStep 3554711 = 5332067) B5332067
theorem B933291 : Blo 932582 933291 := bstep (se 1 (by rfl) ⟨699968, by rfl⟩ : syracuseStep 933291 = 1399937) B1399937
theorem B933303 : Blo 932582 933303 := bstep (se 1 (by rfl) ⟨699977, by rfl⟩ : syracuseStep 933303 = 1399955) B1399955
theorem B933323 : Blo 932582 933323 := bstep (se 1 (by rfl) ⟨699992, by rfl⟩ : syracuseStep 933323 = 1399985) B1399985
theorem B933335 : Blo 932582 933335 := bstep (se 1 (by rfl) ⟨700001, by rfl⟩ : syracuseStep 933335 = 1400003) B1400003
theorem B933355 : Blo 932582 933355 := bstep (se 1 (by rfl) ⟨700016, by rfl⟩ : syracuseStep 933355 = 1400033) B1400033
theorem B933367 : Blo 932582 933367 := bstep (se 1 (by rfl) ⟨700025, by rfl⟩ : syracuseStep 933367 = 1400051) B1400051
theorem B933387 : Blo 932582 933387 := bstep (se 1 (by rfl) ⟨700040, by rfl⟩ : syracuseStep 933387 = 1400081) B1400081
theorem B933399 : Blo 932582 933399 := bstep (se 1 (by rfl) ⟨700049, by rfl⟩ : syracuseStep 933399 = 1400099) B1400099
theorem B10108451 : Blo 932582 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B933419 : Blo 932582 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B933431 : Blo 932582 933431 := bstep (se 1 (by rfl) ⟨700073, by rfl⟩ : syracuseStep 933431 = 1400147) B1400147
theorem B933451 : Blo 932582 933451 := bstep (se 1 (by rfl) ⟨700088, by rfl⟩ : syracuseStep 933451 = 1400177) B1400177
theorem B933463 : Blo 932582 933463 := bstep (se 1 (by rfl) ⟨700097, by rfl⟩ : syracuseStep 933463 = 1400195) B1400195
theorem B933483 : Blo 932582 933483 := bstep (se 1 (by rfl) ⟨700112, by rfl⟩ : syracuseStep 933483 = 1400225) B1400225
theorem B933495 : Blo 932582 933495 := bstep (se 1 (by rfl) ⟨700121, by rfl⟩ : syracuseStep 933495 = 1400243) B1400243
theorem B933515 : Blo 932582 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B933527 : Blo 932582 933527 := bstep (se 1 (by rfl) ⟨700145, by rfl⟩ : syracuseStep 933527 = 1400291) B1400291
theorem B933547 : Blo 932582 933547 := bstep (se 1 (by rfl) ⟨700160, by rfl⟩ : syracuseStep 933547 = 1400321) B1400321
theorem B933559 : Blo 932582 933559 := bstep (se 1 (by rfl) ⟨700169, by rfl⟩ : syracuseStep 933559 = 1400339) B1400339
theorem B933579 : Blo 932582 933579 := bstep (se 1 (by rfl) ⟨700184, by rfl⟩ : syracuseStep 933579 = 1400369) B1400369
theorem B933591 : Blo 932582 933591 := bstep (se 1 (by rfl) ⟨700193, by rfl⟩ : syracuseStep 933591 = 1400387) B1400387
theorem B933611 : Blo 932582 933611 := bstep (se 1 (by rfl) ⟨700208, by rfl⟩ : syracuseStep 933611 = 1400417) B1400417
theorem B933623 : Blo 932582 933623 := bstep (se 1 (by rfl) ⟨700217, by rfl⟩ : syracuseStep 933623 = 1400435) B1400435
theorem B933643 : Blo 932582 933643 := bstep (se 1 (by rfl) ⟨700232, by rfl⟩ : syracuseStep 933643 = 1400465) B1400465
theorem B933655 : Blo 932582 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B933675 : Blo 932582 933675 := bstep (se 1 (by rfl) ⟨700256, by rfl⟩ : syracuseStep 933675 = 1400513) B1400513
theorem B5062445 : Blo 932582 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B933687 : Blo 932582 933687 := bstep (se 1 (by rfl) ⟨700265, by rfl⟩ : syracuseStep 933687 = 1400531) B1400531
theorem B933707 : Blo 932582 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B933719 : Blo 932582 933719 := bstep (se 1 (by rfl) ⟨700289, by rfl⟩ : syracuseStep 933719 = 1400579) B1400579
theorem B933739 : Blo 932582 933739 := bstep (se 1 (by rfl) ⟨700304, by rfl⟩ : syracuseStep 933739 = 1400609) B1400609
theorem B933751 : Blo 932582 933751 := bstep (se 1 (by rfl) ⟨700313, by rfl⟩ : syracuseStep 933751 = 1400627) B1400627
theorem B933771 : Blo 932582 933771 := bstep (se 1 (by rfl) ⟨700328, by rfl⟩ : syracuseStep 933771 = 1400657) B1400657
theorem B933783 : Blo 932582 933783 := bstep (se 1 (by rfl) ⟨700337, by rfl⟩ : syracuseStep 933783 = 1400675) B1400675
theorem B933803 : Blo 932582 933803 := bstep (se 1 (by rfl) ⟨700352, by rfl⟩ : syracuseStep 933803 = 1400705) B1400705
theorem B933815 : Blo 932582 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B933835 : Blo 932582 933835 := bstep (se 1 (by rfl) ⟨700376, by rfl⟩ : syracuseStep 933835 = 1400753) B1400753
theorem B8536013 : Blo 932582 8536013 := bstep (se 3 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 8536013 = 3201005) B3201005
theorem B933847 : Blo 932582 933847 := bstep (se 1 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 933847 = 1400771) B1400771
theorem B933867 : Blo 932582 933867 := bstep (se 1 (by rfl) ⟨700400, by rfl⟩ : syracuseStep 933867 = 1400801) B1400801
theorem B933879 : Blo 932582 933879 := bstep (se 1 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 933879 = 1400819) B1400819
theorem B933899 : Blo 932582 933899 := bstep (se 1 (by rfl) ⟨700424, by rfl⟩ : syracuseStep 933899 = 1400849) B1400849
theorem B933911 : Blo 932582 933911 := bstep (se 1 (by rfl) ⟨700433, by rfl⟩ : syracuseStep 933911 = 1400867) B1400867
theorem B933931 : Blo 932582 933931 := bstep (se 1 (by rfl) ⟨700448, by rfl⟩ : syracuseStep 933931 = 1400897) B1400897
theorem B933943 : Blo 932582 933943 := bstep (se 1 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 933943 = 1400915) B1400915
theorem B933963 : Blo 932582 933963 := bstep (se 1 (by rfl) ⟨700472, by rfl⟩ : syracuseStep 933963 = 1400945) B1400945
theorem B933975 : Blo 932582 933975 := bstep (se 1 (by rfl) ⟨700481, by rfl⟩ : syracuseStep 933975 = 1400963) B1400963
theorem B933995 : Blo 932582 933995 := bstep (se 1 (by rfl) ⟨700496, by rfl⟩ : syracuseStep 933995 = 1400993) B1400993
theorem B934007 : Blo 932582 934007 := bstep (se 1 (by rfl) ⟨700505, by rfl⟩ : syracuseStep 934007 = 1401011) B1401011
theorem B6733955 : Blo 932582 6733955 := bstep (se 1 (by rfl) ⟨5050466, by rfl⟩ : syracuseStep 6733955 = 10100933) B10100933
theorem B934027 : Blo 932582 934027 := bstep (se 1 (by rfl) ⟨700520, by rfl⟩ : syracuseStep 934027 = 1401041) B1401041
theorem B934039 : Blo 932582 934039 := bstep (se 1 (by rfl) ⟨700529, by rfl⟩ : syracuseStep 934039 = 1401059) B1401059
theorem B934059 : Blo 932582 934059 := bstep (se 1 (by rfl) ⟨700544, by rfl⟩ : syracuseStep 934059 = 1401089) B1401089
theorem B934071 : Blo 932582 934071 := bstep (se 1 (by rfl) ⟨700553, by rfl⟩ : syracuseStep 934071 = 1401107) B1401107
theorem B934091 : Blo 932582 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B934103 : Blo 932582 934103 := bstep (se 1 (by rfl) ⟨700577, by rfl⟩ : syracuseStep 934103 = 1401155) B1401155
theorem B934123 : Blo 932582 934123 := bstep (se 1 (by rfl) ⟨700592, by rfl⟩ : syracuseStep 934123 = 1401185) B1401185
theorem B934135 : Blo 932582 934135 := bstep (se 1 (by rfl) ⟨700601, by rfl⟩ : syracuseStep 934135 = 1401203) B1401203
theorem B7979269 : Blo 932582 7979269 := bstep (se 4 (by rfl) ⟨748056, by rfl⟩ : syracuseStep 7979269 = 1496113) B1496113
theorem B934155 : Blo 932582 934155 := bstep (se 1 (by rfl) ⟨700616, by rfl⟩ : syracuseStep 934155 = 1401233) B1401233
theorem B934167 : Blo 932582 934167 := bstep (se 1 (by rfl) ⟨700625, by rfl⟩ : syracuseStep 934167 = 1401251) B1401251
theorem B934187 : Blo 932582 934187 := bstep (se 1 (by rfl) ⟨700640, by rfl⟩ : syracuseStep 934187 = 1401281) B1401281
theorem B934199 : Blo 932582 934199 := bstep (se 1 (by rfl) ⟨700649, by rfl⟩ : syracuseStep 934199 = 1401299) B1401299
theorem B934219 : Blo 932582 934219 := bstep (se 1 (by rfl) ⟨700664, by rfl⟩ : syracuseStep 934219 = 1401329) B1401329
theorem B934231 : Blo 932582 934231 := bstep (se 1 (by rfl) ⟨700673, by rfl⟩ : syracuseStep 934231 = 1401347) B1401347
theorem B934251 : Blo 932582 934251 := bstep (se 1 (by rfl) ⟨700688, by rfl⟩ : syracuseStep 934251 = 1401377) B1401377
theorem B934263 : Blo 932582 934263 := bstep (se 1 (by rfl) ⟨700697, by rfl⟩ : syracuseStep 934263 = 1401395) B1401395
theorem B934283 : Blo 932582 934283 := bstep (se 1 (by rfl) ⟨700712, by rfl⟩ : syracuseStep 934283 = 1401425) B1401425
theorem B934295 : Blo 932582 934295 := bstep (se 1 (by rfl) ⟨700721, by rfl⟩ : syracuseStep 934295 = 1401443) B1401443
theorem B934315 : Blo 932582 934315 := bstep (se 1 (by rfl) ⟨700736, by rfl⟩ : syracuseStep 934315 = 1401473) B1401473
theorem B934327 : Blo 932582 934327 := bstep (se 1 (by rfl) ⟨700745, by rfl⟩ : syracuseStep 934327 = 1401491) B1401491
theorem B934347 : Blo 932582 934347 := bstep (se 1 (by rfl) ⟨700760, by rfl⟩ : syracuseStep 934347 = 1401521) B1401521
theorem B934359 : Blo 932582 934359 := bstep (se 1 (by rfl) ⟨700769, by rfl⟩ : syracuseStep 934359 = 1401539) B1401539
theorem B934379 : Blo 932582 934379 := bstep (se 1 (by rfl) ⟨700784, by rfl⟩ : syracuseStep 934379 = 1401569) B1401569
theorem B934391 : Blo 932582 934391 := bstep (se 1 (by rfl) ⟨700793, by rfl⟩ : syracuseStep 934391 = 1401587) B1401587
theorem B934411 : Blo 932582 934411 := bstep (se 1 (by rfl) ⟨700808, by rfl⟩ : syracuseStep 934411 = 1401617) B1401617
theorem B934423 : Blo 932582 934423 := bstep (se 1 (by rfl) ⟨700817, by rfl⟩ : syracuseStep 934423 = 1401635) B1401635
theorem B934443 : Blo 932582 934443 := bstep (se 1 (by rfl) ⟨700832, by rfl⟩ : syracuseStep 934443 = 1401665) B1401665
theorem B934455 : Blo 932582 934455 := bstep (se 1 (by rfl) ⟨700841, by rfl⟩ : syracuseStep 934455 = 1401683) B1401683
theorem B934475 : Blo 932582 934475 := bstep (se 1 (by rfl) ⟨700856, by rfl⟩ : syracuseStep 934475 = 1401713) B1401713
theorem B934487 : Blo 932582 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B934507 : Blo 932582 934507 := bstep (se 1 (by rfl) ⟨700880, by rfl⟩ : syracuseStep 934507 = 1401761) B1401761
theorem B934519 : Blo 932582 934519 := bstep (se 1 (by rfl) ⟨700889, by rfl⟩ : syracuseStep 934519 = 1401779) B1401779
theorem B3555971 : Blo 932582 3555971 := bstep (se 1 (by rfl) ⟨2666978, by rfl⟩ : syracuseStep 3555971 = 5333957) B5333957
theorem B934539 : Blo 932582 934539 := bstep (se 1 (by rfl) ⟨700904, by rfl⟩ : syracuseStep 934539 = 1401809) B1401809
theorem B934551 : Blo 932582 934551 := bstep (se 1 (by rfl) ⟨700913, by rfl⟩ : syracuseStep 934551 = 1401827) B1401827
theorem B934571 : Blo 932582 934571 := bstep (se 1 (by rfl) ⟨700928, by rfl⟩ : syracuseStep 934571 = 1401857) B1401857
theorem B934583 : Blo 932582 934583 := bstep (se 1 (by rfl) ⟨700937, by rfl⟩ : syracuseStep 934583 = 1401875) B1401875
theorem B934603 : Blo 932582 934603 := bstep (se 1 (by rfl) ⟨700952, by rfl⟩ : syracuseStep 934603 = 1401905) B1401905
theorem B934615 : Blo 932582 934615 := bstep (se 1 (by rfl) ⟨700961, by rfl⟩ : syracuseStep 934615 = 1401923) B1401923
theorem B934635 : Blo 932582 934635 := bstep (se 1 (by rfl) ⟨700976, by rfl⟩ : syracuseStep 934635 = 1401953) B1401953
theorem B934647 : Blo 932582 934647 := bstep (se 1 (by rfl) ⟨700985, by rfl⟩ : syracuseStep 934647 = 1401971) B1401971
theorem B934667 : Blo 932582 934667 := bstep (se 1 (by rfl) ⟨701000, by rfl⟩ : syracuseStep 934667 = 1402001) B1402001
theorem B934679 : Blo 932582 934679 := bstep (se 1 (by rfl) ⟨701009, by rfl⟩ : syracuseStep 934679 = 1402019) B1402019
theorem B934699 : Blo 932582 934699 := bstep (se 1 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 934699 = 1402049) B1402049
theorem B934711 : Blo 932582 934711 := bstep (se 1 (by rfl) ⟨701033, by rfl⟩ : syracuseStep 934711 = 1402067) B1402067
theorem B934731 : Blo 932582 934731 := bstep (se 1 (by rfl) ⟨701048, by rfl⟩ : syracuseStep 934731 = 1402097) B1402097
theorem B934743 : Blo 932582 934743 := bstep (se 1 (by rfl) ⟨701057, by rfl⟩ : syracuseStep 934743 = 1402115) B1402115
theorem B934763 : Blo 932582 934763 := bstep (se 1 (by rfl) ⟨701072, by rfl⟩ : syracuseStep 934763 = 1402145) B1402145
theorem B934775 : Blo 932582 934775 := bstep (se 1 (by rfl) ⟨701081, by rfl⟩ : syracuseStep 934775 = 1402163) B1402163
theorem B934795 : Blo 932582 934795 := bstep (se 1 (by rfl) ⟨701096, by rfl⟩ : syracuseStep 934795 = 1402193) B1402193
theorem B934807 : Blo 932582 934807 := bstep (se 1 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 934807 = 1402211) B1402211
theorem B934827 : Blo 932582 934827 := bstep (se 1 (by rfl) ⟨701120, by rfl⟩ : syracuseStep 934827 = 1402241) B1402241
theorem B934839 : Blo 932582 934839 := bstep (se 1 (by rfl) ⟨701129, by rfl⟩ : syracuseStep 934839 = 1402259) B1402259
theorem B934859 : Blo 932582 934859 := bstep (se 1 (by rfl) ⟨701144, by rfl⟩ : syracuseStep 934859 = 1402289) B1402289
theorem B934871 : Blo 932582 934871 := bstep (se 1 (by rfl) ⟨701153, by rfl⟩ : syracuseStep 934871 = 1402307) B1402307
theorem B934891 : Blo 932582 934891 := bstep (se 1 (by rfl) ⟨701168, by rfl⟩ : syracuseStep 934891 = 1402337) B1402337
theorem B934903 : Blo 932582 934903 := bstep (se 1 (by rfl) ⟨701177, by rfl⟩ : syracuseStep 934903 = 1402355) B1402355
theorem B934923 : Blo 932582 934923 := bstep (se 1 (by rfl) ⟨701192, by rfl⟩ : syracuseStep 934923 = 1402385) B1402385
theorem B934935 : Blo 932582 934935 := bstep (se 1 (by rfl) ⟨701201, by rfl⟩ : syracuseStep 934935 = 1402403) B1402403
theorem B934955 : Blo 932582 934955 := bstep (se 1 (by rfl) ⟨701216, by rfl⟩ : syracuseStep 934955 = 1402433) B1402433
theorem B934967 : Blo 932582 934967 := bstep (se 1 (by rfl) ⟨701225, by rfl⟩ : syracuseStep 934967 = 1402451) B1402451
theorem B934987 : Blo 932582 934987 := bstep (se 1 (by rfl) ⟨701240, by rfl⟩ : syracuseStep 934987 = 1402481) B1402481
theorem B934999 : Blo 932582 934999 := bstep (se 1 (by rfl) ⟨701249, by rfl⟩ : syracuseStep 934999 = 1402499) B1402499
theorem B4867165 : Blo 932582 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B935019 : Blo 932582 935019 := bstep (se 1 (by rfl) ⟨701264, by rfl⟩ : syracuseStep 935019 = 1402529) B1402529
theorem B935031 : Blo 932582 935031 := bstep (se 1 (by rfl) ⟨701273, by rfl⟩ : syracuseStep 935031 = 1402547) B1402547
theorem B1262731 : Blo 932582 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B935051 : Blo 932582 935051 := bstep (se 1 (by rfl) ⟨701288, by rfl⟩ : syracuseStep 935051 = 1402577) B1402577
theorem B935063 : Blo 932582 935063 := bstep (se 1 (by rfl) ⟨701297, by rfl⟩ : syracuseStep 935063 = 1402595) B1402595
theorem B935083 : Blo 932582 935083 := bstep (se 1 (by rfl) ⟨701312, by rfl⟩ : syracuseStep 935083 = 1402625) B1402625
theorem B935095 : Blo 932582 935095 := bstep (se 1 (by rfl) ⟨701321, by rfl⟩ : syracuseStep 935095 = 1402643) B1402643
theorem B935115 : Blo 932582 935115 := bstep (se 1 (by rfl) ⟨701336, by rfl⟩ : syracuseStep 935115 = 1402673) B1402673
theorem B935127 : Blo 932582 935127 := bstep (se 1 (by rfl) ⟨701345, by rfl⟩ : syracuseStep 935127 = 1402691) B1402691
theorem B935147 : Blo 932582 935147 := bstep (se 1 (by rfl) ⟨701360, by rfl⟩ : syracuseStep 935147 = 1402721) B1402721
theorem B935159 : Blo 932582 935159 := bstep (se 1 (by rfl) ⟨701369, by rfl⟩ : syracuseStep 935159 = 1402739) B1402739
theorem B935179 : Blo 932582 935179 := bstep (se 1 (by rfl) ⟨701384, by rfl⟩ : syracuseStep 935179 = 1402769) B1402769
theorem B935191 : Blo 932582 935191 := bstep (se 1 (by rfl) ⟨701393, by rfl⟩ : syracuseStep 935191 = 1402787) B1402787
theorem B935211 : Blo 932582 935211 := bstep (se 1 (by rfl) ⟨701408, by rfl⟩ : syracuseStep 935211 = 1402817) B1402817
theorem B935223 : Blo 932582 935223 := bstep (se 1 (by rfl) ⟨701417, by rfl⟩ : syracuseStep 935223 = 1402835) B1402835
theorem B935243 : Blo 932582 935243 := bstep (se 1 (by rfl) ⟨701432, by rfl⟩ : syracuseStep 935243 = 1402865) B1402865
theorem B935255 : Blo 932582 935255 := bstep (se 1 (by rfl) ⟨701441, by rfl⟩ : syracuseStep 935255 = 1402883) B1402883
theorem B935275 : Blo 932582 935275 := bstep (se 1 (by rfl) ⟨701456, by rfl⟩ : syracuseStep 935275 = 1402913) B1402913
theorem B935287 : Blo 932582 935287 := bstep (se 1 (by rfl) ⟨701465, by rfl⟩ : syracuseStep 935287 = 1402931) B1402931
theorem B935307 : Blo 932582 935307 := bstep (se 1 (by rfl) ⟨701480, by rfl⟩ : syracuseStep 935307 = 1402961) B1402961
theorem B935319 : Blo 932582 935319 := bstep (se 1 (by rfl) ⟨701489, by rfl⟩ : syracuseStep 935319 = 1402979) B1402979
theorem B935339 : Blo 932582 935339 := bstep (se 1 (by rfl) ⟨701504, by rfl⟩ : syracuseStep 935339 = 1403009) B1403009
theorem B935351 : Blo 932582 935351 := bstep (se 1 (by rfl) ⟨701513, by rfl⟩ : syracuseStep 935351 = 1403027) B1403027
theorem B935371 : Blo 932582 935371 := bstep (se 1 (by rfl) ⟨701528, by rfl⟩ : syracuseStep 935371 = 1403057) B1403057
theorem B935383 : Blo 932582 935383 := bstep (se 1 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 935383 = 1403075) B1403075
theorem B935403 : Blo 932582 935403 := bstep (se 1 (by rfl) ⟨701552, by rfl⟩ : syracuseStep 935403 = 1403105) B1403105
theorem B935415 : Blo 932582 935415 := bstep (se 1 (by rfl) ⟨701561, by rfl⟩ : syracuseStep 935415 = 1403123) B1403123
theorem B935435 : Blo 932582 935435 := bstep (se 1 (by rfl) ⟨701576, by rfl⟩ : syracuseStep 935435 = 1403153) B1403153
theorem B935447 : Blo 932582 935447 := bstep (se 1 (by rfl) ⟨701585, by rfl⟩ : syracuseStep 935447 = 1403171) B1403171
theorem B935467 : Blo 932582 935467 := bstep (se 1 (by rfl) ⟨701600, by rfl⟩ : syracuseStep 935467 = 1403201) B1403201
theorem B935479 : Blo 932582 935479 := bstep (se 1 (by rfl) ⟨701609, by rfl⟩ : syracuseStep 935479 = 1403219) B1403219
theorem B935499 : Blo 932582 935499 := bstep (se 1 (by rfl) ⟨701624, by rfl⟩ : syracuseStep 935499 = 1403249) B1403249
theorem B935511 : Blo 932582 935511 := bstep (se 1 (by rfl) ⟨701633, by rfl⟩ : syracuseStep 935511 = 1403267) B1403267
theorem B935531 : Blo 932582 935531 := bstep (se 1 (by rfl) ⟨701648, by rfl⟩ : syracuseStep 935531 = 1403297) B1403297
theorem B935543 : Blo 932582 935543 := bstep (se 1 (by rfl) ⟨701657, by rfl⟩ : syracuseStep 935543 = 1403315) B1403315
theorem B935563 : Blo 932582 935563 := bstep (se 1 (by rfl) ⟨701672, by rfl⟩ : syracuseStep 935563 = 1403345) B1403345
theorem B10929815 : Blo 932582 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B935575 : Blo 932582 935575 := bstep (se 1 (by rfl) ⟨701681, by rfl⟩ : syracuseStep 935575 = 1403363) B1403363
theorem B935595 : Blo 932582 935595 := bstep (se 1 (by rfl) ⟨701696, by rfl⟩ : syracuseStep 935595 = 1403393) B1403393
theorem B935607 : Blo 932582 935607 := bstep (se 1 (by rfl) ⟨701705, by rfl⟩ : syracuseStep 935607 = 1403411) B1403411
theorem B935627 : Blo 932582 935627 := bstep (se 1 (by rfl) ⟨701720, by rfl⟩ : syracuseStep 935627 = 1403441) B1403441
theorem B935639 : Blo 932582 935639 := bstep (se 1 (by rfl) ⟨701729, by rfl⟩ : syracuseStep 935639 = 1403459) B1403459
theorem B935659 : Blo 932582 935659 := bstep (se 1 (by rfl) ⟨701744, by rfl⟩ : syracuseStep 935659 = 1403489) B1403489
theorem B935671 : Blo 932582 935671 := bstep (se 1 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 935671 = 1403507) B1403507
theorem B935691 : Blo 932582 935691 := bstep (se 1 (by rfl) ⟨701768, by rfl⟩ : syracuseStep 935691 = 1403537) B1403537
theorem B935703 : Blo 932582 935703 := bstep (se 1 (by rfl) ⟨701777, by rfl⟩ : syracuseStep 935703 = 1403555) B1403555
theorem B935723 : Blo 932582 935723 := bstep (se 1 (by rfl) ⟨701792, by rfl⟩ : syracuseStep 935723 = 1403585) B1403585
theorem B935735 : Blo 932582 935735 := bstep (se 1 (by rfl) ⟨701801, by rfl⟩ : syracuseStep 935735 = 1403603) B1403603
theorem B5326667 : Blo 932582 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B935755 : Blo 932582 935755 := bstep (se 1 (by rfl) ⟨701816, by rfl⟩ : syracuseStep 935755 = 1403633) B1403633
theorem B935767 : Blo 932582 935767 := bstep (se 1 (by rfl) ⟨701825, by rfl⟩ : syracuseStep 935767 = 1403651) B1403651
theorem B935787 : Blo 932582 935787 := bstep (se 1 (by rfl) ⟨701840, by rfl⟩ : syracuseStep 935787 = 1403681) B1403681
theorem B935799 : Blo 932582 935799 := bstep (se 1 (by rfl) ⟨701849, by rfl⟩ : syracuseStep 935799 = 1403699) B1403699
theorem B935819 : Blo 932582 935819 := bstep (se 1 (by rfl) ⟨701864, by rfl⟩ : syracuseStep 935819 = 1403729) B1403729
theorem B935831 : Blo 932582 935831 := bstep (se 1 (by rfl) ⟨701873, by rfl⟩ : syracuseStep 935831 = 1403747) B1403747
theorem B935851 : Blo 932582 935851 := bstep (se 1 (by rfl) ⟨701888, by rfl⟩ : syracuseStep 935851 = 1403777) B1403777
theorem B935863 : Blo 932582 935863 := bstep (se 1 (by rfl) ⟨701897, by rfl⟩ : syracuseStep 935863 = 1403795) B1403795
theorem B935883 : Blo 932582 935883 := bstep (se 1 (by rfl) ⟨701912, by rfl⟩ : syracuseStep 935883 = 1403825) B1403825
theorem B935895 : Blo 932582 935895 := bstep (se 1 (by rfl) ⟨701921, by rfl⟩ : syracuseStep 935895 = 1403843) B1403843
theorem B935915 : Blo 932582 935915 := bstep (se 1 (by rfl) ⟨701936, by rfl⟩ : syracuseStep 935915 = 1403873) B1403873
theorem B935927 : Blo 932582 935927 := bstep (se 1 (by rfl) ⟨701945, by rfl⟩ : syracuseStep 935927 = 1403891) B1403891
theorem B935947 : Blo 932582 935947 := bstep (se 1 (by rfl) ⟨701960, by rfl⟩ : syracuseStep 935947 = 1403921) B1403921
theorem B4737041 : Blo 932582 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B935959 : Blo 932582 935959 := bstep (se 1 (by rfl) ⟨701969, by rfl⟩ : syracuseStep 935959 = 1403939) B1403939
theorem B935979 : Blo 932582 935979 := bstep (se 1 (by rfl) ⟨701984, by rfl⟩ : syracuseStep 935979 = 1403969) B1403969
theorem B2246707 : Blo 932582 2246707 := bstep (se 1 (by rfl) ⟨1685030, by rfl⟩ : syracuseStep 2246707 = 3370061) B3370061
theorem B935991 : Blo 932582 935991 := bstep (se 1 (by rfl) ⟨701993, by rfl⟩ : syracuseStep 935991 = 1403987) B1403987
theorem B936011 : Blo 932582 936011 := bstep (se 1 (by rfl) ⟨702008, by rfl⟩ : syracuseStep 936011 = 1404017) B1404017
theorem B936023 : Blo 932582 936023 := bstep (se 1 (by rfl) ⟨702017, by rfl⟩ : syracuseStep 936023 = 1404035) B1404035
theorem B936043 : Blo 932582 936043 := bstep (se 1 (by rfl) ⟨702032, by rfl⟩ : syracuseStep 936043 = 1404065) B1404065
theorem B936055 : Blo 932582 936055 := bstep (se 1 (by rfl) ⟨702041, by rfl⟩ : syracuseStep 936055 = 1404083) B1404083
theorem B936075 : Blo 932582 936075 := bstep (se 1 (by rfl) ⟨702056, by rfl⟩ : syracuseStep 936075 = 1404113) B1404113
theorem B936087 : Blo 932582 936087 := bstep (se 1 (by rfl) ⟨702065, by rfl⟩ : syracuseStep 936087 = 1404131) B1404131
theorem B936107 : Blo 932582 936107 := bstep (se 1 (by rfl) ⟨702080, by rfl⟩ : syracuseStep 936107 = 1404161) B1404161
theorem B4737203 : Blo 932582 4737203 := bstep (se 1 (by rfl) ⟨3552902, by rfl⟩ : syracuseStep 4737203 = 7105805) B7105805
theorem B936119 : Blo 932582 936119 := bstep (se 1 (by rfl) ⟨702089, by rfl⟩ : syracuseStep 936119 = 1404179) B1404179
theorem B936139 : Blo 932582 936139 := bstep (se 1 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 936139 = 1404209) B1404209
theorem B936151 : Blo 932582 936151 := bstep (se 1 (by rfl) ⟨702113, by rfl⟩ : syracuseStep 936151 = 1404227) B1404227
theorem B936171 : Blo 932582 936171 := bstep (se 1 (by rfl) ⟨702128, by rfl⟩ : syracuseStep 936171 = 1404257) B1404257
theorem B15157489 : Blo 932582 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B936183 : Blo 932582 936183 := bstep (se 1 (by rfl) ⟨702137, by rfl⟩ : syracuseStep 936183 = 1404275) B1404275
theorem B936203 : Blo 932582 936203 := bstep (se 1 (by rfl) ⟨702152, by rfl⟩ : syracuseStep 936203 = 1404305) B1404305
theorem B936215 : Blo 932582 936215 := bstep (se 1 (by rfl) ⟨702161, by rfl⟩ : syracuseStep 936215 = 1404323) B1404323
theorem B936235 : Blo 932582 936235 := bstep (se 1 (by rfl) ⟨702176, by rfl⟩ : syracuseStep 936235 = 1404353) B1404353
theorem B936247 : Blo 932582 936247 := bstep (se 1 (by rfl) ⟨702185, by rfl⟩ : syracuseStep 936247 = 1404371) B1404371
theorem B936267 : Blo 932582 936267 := bstep (se 1 (by rfl) ⟨702200, by rfl⟩ : syracuseStep 936267 = 1404401) B1404401
theorem B936279 : Blo 932582 936279 := bstep (se 1 (by rfl) ⟨702209, by rfl⟩ : syracuseStep 936279 = 1404419) B1404419
theorem B936299 : Blo 932582 936299 := bstep (se 1 (by rfl) ⟨702224, by rfl⟩ : syracuseStep 936299 = 1404449) B1404449
theorem B936311 : Blo 932582 936311 := bstep (se 1 (by rfl) ⟨702233, by rfl⟩ : syracuseStep 936311 = 1404467) B1404467
theorem B936331 : Blo 932582 936331 := bstep (se 1 (by rfl) ⟨702248, by rfl⟩ : syracuseStep 936331 = 1404497) B1404497
theorem B3361169 : Blo 932582 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B936343 : Blo 932582 936343 := bstep (se 1 (by rfl) ⟨702257, by rfl⟩ : syracuseStep 936343 = 1404515) B1404515
theorem B936363 : Blo 932582 936363 := bstep (se 1 (by rfl) ⟨702272, by rfl⟩ : syracuseStep 936363 = 1404545) B1404545
theorem B936375 : Blo 932582 936375 := bstep (se 1 (by rfl) ⟨702281, by rfl⟩ : syracuseStep 936375 = 1404563) B1404563
theorem B936395 : Blo 932582 936395 := bstep (se 1 (by rfl) ⟨702296, by rfl⟩ : syracuseStep 936395 = 1404593) B1404593
theorem B936407 : Blo 932582 936407 := bstep (se 1 (by rfl) ⟨702305, by rfl⟩ : syracuseStep 936407 = 1404611) B1404611
theorem B936427 : Blo 932582 936427 := bstep (se 1 (by rfl) ⟨702320, by rfl⟩ : syracuseStep 936427 = 1404641) B1404641
theorem B936439 : Blo 932582 936439 := bstep (se 1 (by rfl) ⟨702329, by rfl⟩ : syracuseStep 936439 = 1404659) B1404659
theorem B936459 : Blo 932582 936459 := bstep (se 1 (by rfl) ⟨702344, by rfl⟩ : syracuseStep 936459 = 1404689) B1404689
theorem B3361297 : Blo 932582 3361297 := bstep (se 2 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 3361297 = 2520973) B2520973
theorem B936471 : Blo 932582 936471 := bstep (se 1 (by rfl) ⟨702353, by rfl⟩ : syracuseStep 936471 = 1404707) B1404707
theorem B936491 : Blo 932582 936491 := bstep (se 1 (by rfl) ⟨702368, by rfl⟩ : syracuseStep 936491 = 1404737) B1404737
theorem B936503 : Blo 932582 936503 := bstep (se 1 (by rfl) ⟨702377, by rfl⟩ : syracuseStep 936503 = 1404755) B1404755
theorem B936523 : Blo 932582 936523 := bstep (se 1 (by rfl) ⟨702392, by rfl⟩ : syracuseStep 936523 = 1404785) B1404785
theorem B936535 : Blo 932582 936535 := bstep (se 1 (by rfl) ⟨702401, by rfl⟩ : syracuseStep 936535 = 1404803) B1404803
theorem B936555 : Blo 932582 936555 := bstep (se 1 (by rfl) ⟨702416, by rfl⟩ : syracuseStep 936555 = 1404833) B1404833
theorem B936567 : Blo 932582 936567 := bstep (se 1 (by rfl) ⟨702425, by rfl⟩ : syracuseStep 936567 = 1404851) B1404851
theorem B7982003 : Blo 932582 7982003 := bstep (se 1 (by rfl) ⟨5986502, by rfl⟩ : syracuseStep 7982003 = 11973005) B11973005
theorem B1919947 : Blo 932582 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B1330391 : Blo 932582 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B3362093 : Blo 932582 3362093 := bstep (se 3 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 3362093 = 1260785) B1260785
theorem B4804019 : Blo 932582 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B2248343 : Blo 932582 2248343 := bstep (se 1 (by rfl) ⟨1686257, by rfl⟩ : syracuseStep 2248343 = 3372515) B3372515
theorem B6246067 : Blo 932582 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B4739147 : Blo 932582 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B1495255 : Blo 932582 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1200523 : Blo 932582 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B34132373 : Blo 932582 34132373 := bstep (se 6 (by rfl) ⟨799977, by rfl⟩ : syracuseStep 34132373 = 1599955) B1599955
theorem B2839063 : Blo 932582 2839063 := bstep (se 1 (by rfl) ⟨2129297, by rfl⟩ : syracuseStep 2839063 = 4258595) B4258595
theorem B1495703 : Blo 932582 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B1921687 : Blo 932582 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B7983917 : Blo 932582 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B1495883 : Blo 932582 1495883 := bstep (se 1 (by rfl) ⟨1121912, by rfl⟩ : syracuseStep 1495883 = 2243825) B2243825
theorem B1496011 : Blo 932582 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B1496075 : Blo 932582 1496075 := bstep (se 1 (by rfl) ⟨1122056, by rfl⟩ : syracuseStep 1496075 = 2244113) B2244113
theorem B3986833 : Blo 932582 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B4052369 : Blo 932582 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B7984601 : Blo 932582 7984601 := bstep (se 2 (by rfl) ⟨2994225, by rfl⟩ : syracuseStep 7984601 = 5988451) B5988451
theorem B97310321 : Blo 932582 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B3364525 : Blo 932582 3364525 := bstep (se 3 (by rfl) ⟨630848, by rfl⟩ : syracuseStep 3364525 = 1261697) B1261697
theorem B4740929 : Blo 932582 4740929 := bstep (se 2 (by rfl) ⟨1777848, by rfl⟩ : syracuseStep 4740929 = 3555697) B3555697
theorem B3200843 : Blo 932582 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1333273 : Blo 932582 1333273 := bstep (se 2 (by rfl) ⟨499977, by rfl⟩ : syracuseStep 1333273 = 999955) B999955
theorem B1595467 : Blo 932582 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1398923 : Blo 932582 1398923 := bstep (se 1 (by rfl) ⟨1049192, by rfl⟩ : syracuseStep 1398923 = 2098385) B2098385
theorem B1398935 : Blo 932582 1398935 := bstep (se 1 (by rfl) ⟨1049201, by rfl⟩ : syracuseStep 1398935 = 2098403) B2098403
theorem B1497241 : Blo 932582 1497241 := bstep (se 2 (by rfl) ⟨561465, by rfl⟩ : syracuseStep 1497241 = 1122931) B1122931
theorem B1399001 : Blo 932582 1399001 := bstep (se 2 (by rfl) ⟨524625, by rfl⟩ : syracuseStep 1399001 = 1049251) B1049251
theorem B1399115 : Blo 932582 1399115 := bstep (se 1 (by rfl) ⟨1049336, by rfl⟩ : syracuseStep 1399115 = 2098673) B2098673
theorem B1399127 : Blo 932582 1399127 := bstep (se 1 (by rfl) ⟨1049345, by rfl⟩ : syracuseStep 1399127 = 2098691) B2098691
theorem B1399193 : Blo 932582 1399193 := bstep (se 2 (by rfl) ⟨524697, by rfl⟩ : syracuseStep 1399193 = 1049395) B1049395
theorem B1399307 : Blo 932582 1399307 := bstep (se 1 (by rfl) ⟨1049480, by rfl⟩ : syracuseStep 1399307 = 2098961) B2098961
theorem B7100945 : Blo 932582 7100945 := bstep (se 2 (by rfl) ⟨2662854, by rfl⟩ : syracuseStep 7100945 = 5325709) B5325709
theorem B1399319 : Blo 932582 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B1399385 : Blo 932582 1399385 := bstep (se 2 (by rfl) ⟨524769, by rfl⟩ : syracuseStep 1399385 = 1049539) B1049539
theorem B3594883 : Blo 932582 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B1399499 : Blo 932582 1399499 := bstep (se 1 (by rfl) ⟨1049624, by rfl⟩ : syracuseStep 1399499 = 2099249) B2099249
theorem B1399511 : Blo 932582 1399511 := bstep (se 1 (by rfl) ⟨1049633, by rfl⟩ : syracuseStep 1399511 = 2099267) B2099267
theorem B1399577 : Blo 932582 1399577 := bstep (se 2 (by rfl) ⟨524841, by rfl⟩ : syracuseStep 1399577 = 1049683) B1049683
theorem B15129461 : Blo 932582 15129461 := bstep (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) B1418387
theorem B1399691 : Blo 932582 1399691 := bstep (se 1 (by rfl) ⟨1049768, by rfl⟩ : syracuseStep 1399691 = 2099537) B2099537
theorem B1399703 : Blo 932582 1399703 := bstep (se 1 (by rfl) ⟨1049777, by rfl⟩ : syracuseStep 1399703 = 2099555) B2099555
theorem B3365783 : Blo 932582 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B1399769 : Blo 932582 1399769 := bstep (se 2 (by rfl) ⟨524913, by rfl⟩ : syracuseStep 1399769 = 1049827) B1049827
theorem B1399883 : Blo 932582 1399883 := bstep (se 1 (by rfl) ⟨1049912, by rfl⟩ : syracuseStep 1399883 = 2099825) B2099825
theorem B1399895 : Blo 932582 1399895 := bstep (se 1 (by rfl) ⟨1049921, by rfl⟩ : syracuseStep 1399895 = 2099843) B2099843
theorem B1399961 : Blo 932582 1399961 := bstep (se 2 (by rfl) ⟨524985, by rfl⟩ : syracuseStep 1399961 = 1049971) B1049971
theorem B1400075 : Blo 932582 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1400087 : Blo 932582 1400087 := bstep (se 1 (by rfl) ⟨1050065, by rfl⟩ : syracuseStep 1400087 = 2100131) B2100131
theorem B1400153 : Blo 932582 1400153 := bstep (se 2 (by rfl) ⟨525057, by rfl⟩ : syracuseStep 1400153 = 1050115) B1050115
theorem B1400267 : Blo 932582 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B1400279 : Blo 932582 1400279 := bstep (se 1 (by rfl) ⟨1050209, by rfl⟩ : syracuseStep 1400279 = 2100419) B2100419
theorem B1400345 : Blo 932582 1400345 := bstep (se 2 (by rfl) ⟨525129, by rfl⟩ : syracuseStep 1400345 = 1050259) B1050259
theorem B5987915 : Blo 932582 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B1400459 : Blo 932582 1400459 := bstep (se 1 (by rfl) ⟨1050344, by rfl⟩ : syracuseStep 1400459 = 2100689) B2100689
theorem B1400471 : Blo 932582 1400471 := bstep (se 1 (by rfl) ⟨1050353, by rfl⟩ : syracuseStep 1400471 = 2100707) B2100707
theorem B1400537 : Blo 932582 1400537 := bstep (se 2 (by rfl) ⟨525201, by rfl⟩ : syracuseStep 1400537 = 1050403) B1050403
theorem B3989209 : Blo 932582 3989209 := bstep (se 2 (by rfl) ⟨1495953, by rfl⟩ : syracuseStep 3989209 = 2991907) B2991907
theorem B3366659 : Blo 932582 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B1400651 : Blo 932582 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B1400663 : Blo 932582 1400663 := bstep (se 1 (by rfl) ⟨1050497, by rfl⟩ : syracuseStep 1400663 = 2100995) B2100995
theorem B7298909 : Blo 932582 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1400729 : Blo 932582 1400729 := bstep (se 2 (by rfl) ⟨525273, by rfl⟩ : syracuseStep 1400729 = 1050547) B1050547
theorem B1400843 : Blo 932582 1400843 := bstep (se 1 (by rfl) ⟨1050632, by rfl⟩ : syracuseStep 1400843 = 2101265) B2101265
theorem B1400855 : Blo 932582 1400855 := bstep (se 1 (by rfl) ⟨1050641, by rfl⟩ : syracuseStep 1400855 = 2101283) B2101283
theorem B6152237 : Blo 932582 6152237 := bstep (se 3 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 6152237 = 2307089) B2307089
theorem B20242507 : Blo 932582 20242507 := bstep (se 1 (by rfl) ⟨15181880, by rfl⟩ : syracuseStep 20242507 = 30363761) B30363761
theorem B1400921 : Blo 932582 1400921 := bstep (se 2 (by rfl) ⟨525345, by rfl⟩ : syracuseStep 1400921 = 1050691) B1050691
theorem B2875571 : Blo 932582 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B1401035 : Blo 932582 1401035 := bstep (se 1 (by rfl) ⟨1050776, by rfl⟩ : syracuseStep 1401035 = 2101553) B2101553
theorem B1401047 : Blo 932582 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B3793169 : Blo 932582 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B1401113 : Blo 932582 1401113 := bstep (se 2 (by rfl) ⟨525417, by rfl⟩ : syracuseStep 1401113 = 1050835) B1050835
theorem B1401227 : Blo 932582 1401227 := bstep (se 1 (by rfl) ⟨1050920, by rfl⟩ : syracuseStep 1401227 = 2101841) B2101841
theorem B1401239 : Blo 932582 1401239 := bstep (se 1 (by rfl) ⟨1050929, by rfl⟩ : syracuseStep 1401239 = 2101859) B2101859
theorem B13459891 : Blo 932582 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B4481497 : Blo 932582 4481497 := bstep (se 2 (by rfl) ⟨1680561, by rfl⟩ : syracuseStep 4481497 = 3361123) B3361123
theorem B1401305 : Blo 932582 1401305 := bstep (se 2 (by rfl) ⟨525489, by rfl⟩ : syracuseStep 1401305 = 1050979) B1050979
theorem B1892929 : Blo 932582 1892929 := bstep (se 2 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 1892929 = 1419697) B1419697
theorem B1401419 : Blo 932582 1401419 := bstep (se 1 (by rfl) ⟨1051064, by rfl⟩ : syracuseStep 1401419 = 2102129) B2102129
theorem B1892951 : Blo 932582 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B1401431 : Blo 932582 1401431 := bstep (se 1 (by rfl) ⟨1051073, by rfl⟩ : syracuseStep 1401431 = 2102147) B2102147
theorem B3990167 : Blo 932582 3990167 := bstep (se 1 (by rfl) ⟨2992625, by rfl⟩ : syracuseStep 3990167 = 5985251) B5985251
theorem B1401497 : Blo 932582 1401497 := bstep (se 2 (by rfl) ⟨525561, by rfl⟩ : syracuseStep 1401497 = 1051123) B1051123
theorem B1401611 : Blo 932582 1401611 := bstep (se 1 (by rfl) ⟨1051208, by rfl⟩ : syracuseStep 1401611 = 2102417) B2102417
theorem B1401623 : Blo 932582 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B1401689 : Blo 932582 1401689 := bstep (se 2 (by rfl) ⟨525633, by rfl⟩ : syracuseStep 1401689 = 1051267) B1051267
theorem B1401803 : Blo 932582 1401803 := bstep (se 1 (by rfl) ⟨1051352, by rfl⟩ : syracuseStep 1401803 = 2102705) B2102705
theorem B1401815 : Blo 932582 1401815 := bstep (se 1 (by rfl) ⟨1051361, by rfl⟩ : syracuseStep 1401815 = 2102723) B2102723
theorem B5694425 : Blo 932582 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B1401881 : Blo 932582 1401881 := bstep (se 2 (by rfl) ⟨525705, by rfl⟩ : syracuseStep 1401881 = 1051411) B1051411
theorem B1401995 : Blo 932582 1401995 := bstep (se 1 (by rfl) ⟨1051496, by rfl⟩ : syracuseStep 1401995 = 2102993) B2102993
theorem B1402007 : Blo 932582 1402007 := bstep (se 1 (by rfl) ⟨1051505, by rfl⟩ : syracuseStep 1402007 = 2103011) B2103011
theorem B1402073 : Blo 932582 1402073 := bstep (se 2 (by rfl) ⟨525777, by rfl⟩ : syracuseStep 1402073 = 1051555) B1051555
theorem B1991947 : Blo 932582 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B1402187 : Blo 932582 1402187 := bstep (se 1 (by rfl) ⟨1051640, by rfl⟩ : syracuseStep 1402187 = 2103281) B2103281
theorem B1402199 : Blo 932582 1402199 := bstep (se 1 (by rfl) ⟨1051649, by rfl⟩ : syracuseStep 1402199 = 2103299) B2103299
theorem B5989783 : Blo 932582 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1402265 : Blo 932582 1402265 := bstep (se 2 (by rfl) ⟨525849, by rfl⟩ : syracuseStep 1402265 = 1051699) B1051699
theorem B3794435 : Blo 932582 3794435 := bstep (se 1 (by rfl) ⟨2845826, by rfl⟩ : syracuseStep 3794435 = 5691653) B5691653
theorem B1402379 : Blo 932582 1402379 := bstep (se 1 (by rfl) ⟨1051784, by rfl⟩ : syracuseStep 1402379 = 2103569) B2103569
theorem B1402391 : Blo 932582 1402391 := bstep (se 1 (by rfl) ⟨1051793, by rfl⟩ : syracuseStep 1402391 = 2103587) B2103587
theorem B1402457 : Blo 932582 1402457 := bstep (se 2 (by rfl) ⟨525921, by rfl⟩ : syracuseStep 1402457 = 1051843) B1051843
theorem B1402571 : Blo 932582 1402571 := bstep (se 1 (by rfl) ⟨1051928, by rfl⟩ : syracuseStep 1402571 = 2103857) B2103857
theorem B1402583 : Blo 932582 1402583 := bstep (se 1 (by rfl) ⟨1051937, by rfl⟩ : syracuseStep 1402583 = 2103875) B2103875
theorem B1795841 : Blo 932582 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B1402649 : Blo 932582 1402649 := bstep (se 2 (by rfl) ⟨525993, by rfl⟩ : syracuseStep 1402649 = 1051987) B1051987
theorem B1402763 : Blo 932582 1402763 := bstep (se 1 (by rfl) ⟨1052072, by rfl⟩ : syracuseStep 1402763 = 2104145) B2104145
theorem B1402775 : Blo 932582 1402775 := bstep (se 1 (by rfl) ⟨1052081, by rfl⟩ : syracuseStep 1402775 = 2104163) B2104163
theorem B3368897 : Blo 932582 3368897 := bstep (se 2 (by rfl) ⟨1263336, by rfl⟩ : syracuseStep 3368897 = 2526673) B2526673
theorem B1402841 : Blo 932582 1402841 := bstep (se 2 (by rfl) ⟨526065, by rfl⟩ : syracuseStep 1402841 = 1052131) B1052131
theorem B1992691 : Blo 932582 1992691 := bstep (se 1 (by rfl) ⟨1494518, by rfl⟩ : syracuseStep 1992691 = 2989037) B2989037
theorem B1402955 : Blo 932582 1402955 := bstep (se 1 (by rfl) ⟨1052216, by rfl⟩ : syracuseStep 1402955 = 2104433) B2104433
theorem B1402967 : Blo 932582 1402967 := bstep (se 1 (by rfl) ⟨1052225, by rfl⟩ : syracuseStep 1402967 = 2104451) B2104451
theorem B2025587 : Blo 932582 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B1403033 : Blo 932582 1403033 := bstep (se 2 (by rfl) ⟨526137, by rfl⟩ : syracuseStep 1403033 = 1052275) B1052275
theorem B1403147 : Blo 932582 1403147 := bstep (se 1 (by rfl) ⟨1052360, by rfl⟩ : syracuseStep 1403147 = 2104721) B2104721
theorem B1403159 : Blo 932582 1403159 := bstep (se 1 (by rfl) ⟨1052369, by rfl⟩ : syracuseStep 1403159 = 2104739) B2104739
theorem B3795245 : Blo 932582 3795245 := bstep (se 3 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 3795245 = 1423217) B1423217
theorem B7104833 : Blo 932582 7104833 := bstep (se 2 (by rfl) ⟨2664312, by rfl⟩ : syracuseStep 7104833 = 5328625) B5328625
theorem B1403225 : Blo 932582 1403225 := bstep (se 2 (by rfl) ⟨526209, by rfl⟩ : syracuseStep 1403225 = 1052419) B1052419
theorem B1403339 : Blo 932582 1403339 := bstep (se 1 (by rfl) ⟨1052504, by rfl⟩ : syracuseStep 1403339 = 2105009) B2105009
theorem B1403351 : Blo 932582 1403351 := bstep (se 1 (by rfl) ⟨1052513, by rfl⟩ : syracuseStep 1403351 = 2105027) B2105027
theorem B1993177 : Blo 932582 1993177 := bstep (se 2 (by rfl) ⟨747441, by rfl⟩ : syracuseStep 1993177 = 1494883) B1494883
theorem B1403417 : Blo 932582 1403417 := bstep (se 2 (by rfl) ⟨526281, by rfl⟩ : syracuseStep 1403417 = 1052563) B1052563
theorem B5991013 : Blo 932582 5991013 := bstep (se 4 (by rfl) ⟨561657, by rfl⟩ : syracuseStep 5991013 = 1123315) B1123315
theorem B1895027 : Blo 932582 1895027 := bstep (se 1 (by rfl) ⟨1421270, by rfl⟩ : syracuseStep 1895027 = 2842541) B2842541
theorem B1403531 : Blo 932582 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B1403543 : Blo 932582 1403543 := bstep (se 1 (by rfl) ⟨1052657, by rfl⟩ : syracuseStep 1403543 = 2105315) B2105315
theorem B3992267 : Blo 932582 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B1403609 : Blo 932582 1403609 := bstep (se 2 (by rfl) ⟨526353, by rfl⟩ : syracuseStep 1403609 = 1052707) B1052707
theorem B1403723 : Blo 932582 1403723 := bstep (se 1 (by rfl) ⟨1052792, by rfl⟩ : syracuseStep 1403723 = 2105585) B2105585
theorem B1403735 : Blo 932582 1403735 := bstep (se 1 (by rfl) ⟨1052801, by rfl⟩ : syracuseStep 1403735 = 2105603) B2105603
theorem B1403801 : Blo 932582 1403801 := bstep (se 2 (by rfl) ⟨526425, by rfl⟩ : syracuseStep 1403801 = 1052851) B1052851
theorem B1403915 : Blo 932582 1403915 := bstep (se 1 (by rfl) ⟨1052936, by rfl⟩ : syracuseStep 1403915 = 2105873) B2105873
theorem B1403927 : Blo 932582 1403927 := bstep (se 1 (by rfl) ⟨1052945, by rfl⟩ : syracuseStep 1403927 = 2105891) B2105891
theorem B3370049 : Blo 932582 3370049 := bstep (se 2 (by rfl) ⟨1263768, by rfl⟩ : syracuseStep 3370049 = 2527537) B2527537
theorem B1403993 : Blo 932582 1403993 := bstep (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) B1052995
theorem B1404107 : Blo 932582 1404107 := bstep (se 1 (by rfl) ⟨1053080, by rfl⟩ : syracuseStep 1404107 = 2106161) B2106161
theorem B1404119 : Blo 932582 1404119 := bstep (se 1 (by rfl) ⟨1053089, by rfl⟩ : syracuseStep 1404119 = 2106179) B2106179
theorem B2026711 : Blo 932582 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B1404185 : Blo 932582 1404185 := bstep (se 2 (by rfl) ⟨526569, by rfl⟩ : syracuseStep 1404185 = 1053139) B1053139
theorem B1404299 : Blo 932582 1404299 := bstep (se 1 (by rfl) ⟨1053224, by rfl⟩ : syracuseStep 1404299 = 2106449) B2106449
theorem B1404311 : Blo 932582 1404311 := bstep (se 1 (by rfl) ⟨1053233, by rfl⟩ : syracuseStep 1404311 = 2106467) B2106467
theorem B1404377 : Blo 932582 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B1404491 : Blo 932582 1404491 := bstep (se 1 (by rfl) ⟨1053368, by rfl⟩ : syracuseStep 1404491 = 2106737) B2106737
theorem B1404503 : Blo 932582 1404503 := bstep (se 1 (by rfl) ⟨1053377, by rfl⟩ : syracuseStep 1404503 = 2106755) B2106755
theorem B1404569 : Blo 932582 1404569 := bstep (se 2 (by rfl) ⟨526713, by rfl⟩ : syracuseStep 1404569 = 1053427) B1053427
theorem B1404683 : Blo 932582 1404683 := bstep (se 1 (by rfl) ⟨1053512, by rfl⟩ : syracuseStep 1404683 = 2107025) B2107025
theorem B1404695 : Blo 932582 1404695 := bstep (se 1 (by rfl) ⟨1053521, by rfl⟩ : syracuseStep 1404695 = 2107043) B2107043
theorem B1404761 : Blo 932582 1404761 := bstep (se 2 (by rfl) ⟨526785, by rfl⟩ : syracuseStep 1404761 = 1053571) B1053571
theorem B1994647 : Blo 932582 1994647 := bstep (se 1 (by rfl) ⟨1495985, by rfl⟩ : syracuseStep 1994647 = 2991971) B2991971
theorem B1994699 : Blo 932582 1994699 := bstep (se 1 (by rfl) ⟨1496024, by rfl⟩ : syracuseStep 1994699 = 2992049) B2992049
theorem B3371159 : Blo 932582 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B7106777 : Blo 932582 7106777 := bstep (se 2 (by rfl) ⟨2665041, by rfl⟩ : syracuseStep 7106777 = 5330083) B5330083
theorem B1896691 : Blo 932582 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B3993907 : Blo 932582 3993907 := bstep (se 1 (by rfl) ⟨2995430, by rfl⟩ : syracuseStep 3993907 = 5990861) B5990861
theorem B3371329 : Blo 932582 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B8516161 : Blo 932582 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B2847383 : Blo 932582 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B2847577 : Blo 932582 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B3994541 : Blo 932582 3994541 := bstep (se 3 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 3994541 = 1497953) B1497953
theorem B17953973 : Blo 932582 17953973 := bstep (se 5 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 17953973 = 1683185) B1683185
theorem B1897931 : Blo 932582 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B1996339 : Blo 932582 1996339 := bstep (se 1 (by rfl) ⟨1497254, by rfl⟩ : syracuseStep 1996339 = 2994509) B2994509
theorem B947927 : Blo 932582 947927 := bstep (se 1 (by rfl) ⟨710945, by rfl⟩ : syracuseStep 947927 = 1421891) B1421891
theorem B4257629 : Blo 932582 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B1996697 : Blo 932582 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B6387673 : Blo 932582 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B7993349 : Blo 932582 7993349 := bstep (se 4 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 7993349 = 1498753) B1498753
theorem B6748717 : Blo 932582 6748717 := bstep (se 3 (by rfl) ⟨1265384, by rfl⟩ : syracuseStep 6748717 = 2530769) B2530769
theorem B5044801 : Blo 932582 5044801 := bstep (se 2 (by rfl) ⟨1891800, by rfl⟩ : syracuseStep 5044801 = 3783601) B3783601
theorem B2522443 : Blo 932582 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B5766551 : Blo 932582 5766551 := bstep (se 1 (by rfl) ⟨4324913, by rfl⟩ : syracuseStep 5766551 = 8649827) B8649827
theorem B7110179 : Blo 932582 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B11959883 : Blo 932582 11959883 := bstep (se 1 (by rfl) ⟨8969912, by rfl⟩ : syracuseStep 11959883 = 17939825) B17939825
theorem B4489091 : Blo 932582 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B1998731 : Blo 932582 1998731 := bstep (se 1 (by rfl) ⟨1499048, by rfl⟩ : syracuseStep 1998731 = 2998097) B2998097
theorem B4489303 : Blo 932582 4489303 := bstep (se 1 (by rfl) ⟨3366977, by rfl⟩ : syracuseStep 4489303 = 6733955) B6733955
theorem B4325647 : Blo 932582 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B14418323 : Blo 932582 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B2523905 : Blo 932582 2523905 := bstep (se 2 (by rfl) ⟨946464, by rfl⟩ : syracuseStep 2523905 = 1892929) B1892929
theorem B1180423 : Blo 932582 1180423 := bstep (se 1 (by rfl) ⟨885317, by rfl⟩ : syracuseStep 1180423 = 1770635) B1770635
theorem B1049359 : Blo 932582 1049359 := bstep (se 1 (by rfl) ⟨787019, by rfl⟩ : syracuseStep 1049359 = 1574039) B1574039
theorem B1573931 : Blo 932582 1573931 := bstep (se 1 (by rfl) ⟨1180448, by rfl⟩ : syracuseStep 1573931 = 2360897) B2360897
theorem B1180919 : Blo 932582 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B1049863 : Blo 932582 1049863 := bstep (se 1 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 1049863 = 1574795) B1574795
theorem B2098475 : Blo 932582 2098475 := bstep (se 1 (by rfl) ⟨1573856, by rfl⟩ : syracuseStep 2098475 = 3147713) B3147713
theorem B1181071 : Blo 932582 1181071 := bstep (se 1 (by rfl) ⟨885803, by rfl⟩ : syracuseStep 1181071 = 1771607) B1771607
theorem B1574329 : Blo 932582 1574329 := bstep (se 2 (by rfl) ⟨590373, by rfl⟩ : syracuseStep 1574329 = 1180747) B1180747
theorem B1050043 : Blo 932582 1050043 := bstep (se 1 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 1050043 = 1575065) B1575065
theorem B6489553 : Blo 932582 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B2885149 : Blo 932582 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1181243 : Blo 932582 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B2360947 : Blo 932582 2360947 := bstep (se 1 (by rfl) ⟨1770710, by rfl⟩ : syracuseStep 2360947 = 3541421) B3541421
theorem B2098835 : Blo 932582 2098835 := bstep (se 1 (by rfl) ⟨1574126, by rfl⟩ : syracuseStep 2098835 = 3148253) B3148253
theorem B2655929 : Blo 932582 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B2098889 : Blo 932582 2098889 := bstep (se 2 (by rfl) ⟨787083, by rfl⟩ : syracuseStep 2098889 = 1574167) B1574167
theorem B2361089 : Blo 932582 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B5998373 : Blo 932582 5998373 := bstep (se 4 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 5998373 = 1124695) B1124695
theorem B1050511 : Blo 932582 1050511 := bstep (se 1 (by rfl) ⟨787883, by rfl⟩ : syracuseStep 1050511 = 1575767) B1575767
theorem B1575031 : Blo 932582 1575031 := bstep (se 1 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 1575031 = 2362547) B2362547
theorem B2558087 : Blo 932582 2558087 := bstep (se 1 (by rfl) ⟨1918565, by rfl⟩ : syracuseStep 2558087 = 3837131) B3837131
theorem B2361545 : Blo 932582 2361545 := bstep (se 2 (by rfl) ⟨885579, by rfl⟩ : syracuseStep 2361545 = 1771159) B1771159
theorem B3148091 : Blo 932582 3148091 := bstep (se 1 (by rfl) ⟨2361068, by rfl⟩ : syracuseStep 3148091 = 4722137) B4722137
theorem B1575227 : Blo 932582 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B1771895 : Blo 932582 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B2099591 : Blo 932582 2099591 := bstep (se 1 (by rfl) ⟨1574693, by rfl⟩ : syracuseStep 2099591 = 3149387) B3149387
theorem B1051015 : Blo 932582 1051015 := bstep (se 1 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 1051015 = 1576523) B1576523
theorem B1182215 : Blo 932582 1182215 := bstep (se 1 (by rfl) ⟨886661, by rfl⟩ : syracuseStep 1182215 = 1773323) B1773323
theorem B1772047 : Blo 932582 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B2361899 : Blo 932582 2361899 := bstep (se 1 (by rfl) ⟨1771424, by rfl⟩ : syracuseStep 2361899 = 3542849) B3542849
theorem B2099771 : Blo 932582 2099771 := bstep (se 1 (by rfl) ⟨1574828, by rfl⟩ : syracuseStep 2099771 = 3149657) B3149657
theorem B1051195 : Blo 932582 1051195 := bstep (se 1 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 1051195 = 1576793) B1576793
theorem B2656921 : Blo 932582 2656921 := bstep (se 2 (by rfl) ⟨996345, by rfl⟩ : syracuseStep 2656921 = 1992691) B1992691
theorem B2099897 : Blo 932582 2099897 := bstep (se 2 (by rfl) ⟨787461, by rfl⟩ : syracuseStep 2099897 = 1574923) B1574923
theorem B1575625 : Blo 932582 1575625 := bstep (se 2 (by rfl) ⟨590859, by rfl⟩ : syracuseStep 1575625 = 1181719) B1181719
theorem B3148577 : Blo 932582 3148577 := bstep (se 2 (by rfl) ⟨1180716, by rfl⟩ : syracuseStep 3148577 = 2361433) B2361433
theorem B13470553 : Blo 932582 13470553 := bstep (se 2 (by rfl) ⟨5051457, by rfl⟩ : syracuseStep 13470553 = 10102915) B10102915
theorem B3541907 : Blo 932582 3541907 := bstep (se 1 (by rfl) ⟨2656430, by rfl⟩ : syracuseStep 3541907 = 5312861) B5312861
theorem B1772435 : Blo 932582 1772435 := bstep (se 1 (by rfl) ⟨1329326, by rfl⟩ : syracuseStep 1772435 = 2658653) B2658653
theorem B45419525 : Blo 932582 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B2100239 : Blo 932582 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B1051663 : Blo 932582 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B2100257 : Blo 932582 2100257 := bstep (se 2 (by rfl) ⟨787596, by rfl⟩ : syracuseStep 2100257 = 1575193) B1575193
theorem B1182863 : Blo 932582 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B40995989 : Blo 932582 40995989 := bstep (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) B1921687
theorem B3149171 : Blo 932582 3149171 := bstep (se 1 (by rfl) ⟨2361878, by rfl⟩ : syracuseStep 3149171 = 4723757) B4723757
theorem B2100599 : Blo 932582 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B1576327 : Blo 932582 1576327 := bstep (se 1 (by rfl) ⟨1182245, by rfl⟩ : syracuseStep 1576327 = 2364491) B2364491
theorem B1052167 : Blo 932582 1052167 := bstep (se 1 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 1052167 = 1578251) B1578251
theorem B2362891 : Blo 932582 2362891 := bstep (se 1 (by rfl) ⟨1772168, by rfl⟩ : syracuseStep 2362891 = 3544337) B3544337
theorem B2100779 : Blo 932582 2100779 := bstep (se 1 (by rfl) ⟨1575584, by rfl⟩ : syracuseStep 2100779 = 3151169) B3151169
theorem B5312087 : Blo 932582 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B2363033 : Blo 932582 2363033 := bstep (se 2 (by rfl) ⟨886137, by rfl⟩ : syracuseStep 2363033 = 1772275) B1772275
theorem B1052347 : Blo 932582 1052347 := bstep (se 1 (by rfl) ⟨789260, by rfl⟩ : syracuseStep 1052347 = 1578521) B1578521
theorem B7573297 : Blo 932582 7573297 := bstep (se 2 (by rfl) ⟨2839986, by rfl⟩ : syracuseStep 7573297 = 5679973) B5679973
theorem B2363195 : Blo 932582 2363195 := bstep (se 1 (by rfl) ⟨1772396, by rfl⟩ : syracuseStep 2363195 = 3544793) B3544793
theorem B2101139 : Blo 932582 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B2559929 : Blo 932582 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B2101193 : Blo 932582 2101193 := bstep (se 2 (by rfl) ⟨787947, by rfl⟩ : syracuseStep 2101193 = 1575895) B1575895
theorem B7999499 : Blo 932582 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1576975 : Blo 932582 1576975 := bstep (se 1 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 1576975 = 2365463) B2365463
theorem B1052815 : Blo 932582 1052815 := bstep (se 1 (by rfl) ⟨789611, by rfl⟩ : syracuseStep 1052815 = 1579223) B1579223
theorem B2363539 : Blo 932582 2363539 := bstep (se 1 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 2363539 = 3545309) B3545309
theorem B1773839 : Blo 932582 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B2363681 : Blo 932582 2363681 := bstep (se 2 (by rfl) ⟨886380, by rfl⟩ : syracuseStep 2363681 = 1772761) B1772761
theorem B1708489 : Blo 932582 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B2658845 : Blo 932582 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B1577515 : Blo 932582 1577515 := bstep (se 1 (by rfl) ⟨1183136, by rfl⟩ : syracuseStep 1577515 = 2366273) B2366273
theorem B2527805 : Blo 932582 2527805 := bstep (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) B947927
theorem B2101895 : Blo 932582 2101895 := bstep (se 1 (by rfl) ⟨1576421, by rfl⟩ : syracuseStep 2101895 = 3152843) B3152843
theorem B1053319 : Blo 932582 1053319 := bstep (se 1 (by rfl) ⟨789989, by rfl⟩ : syracuseStep 1053319 = 1579979) B1579979
theorem B1577657 : Blo 932582 1577657 := bstep (se 2 (by rfl) ⟨591621, by rfl⟩ : syracuseStep 1577657 = 1183243) B1183243
theorem B7574309 : Blo 932582 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B1774379 : Blo 932582 1774379 := bstep (se 1 (by rfl) ⟨1330784, by rfl⟩ : syracuseStep 1774379 = 2661569) B2661569
theorem B2102075 : Blo 932582 2102075 := bstep (se 1 (by rfl) ⟨1576556, by rfl⟩ : syracuseStep 2102075 = 3153113) B3153113
theorem B1053499 : Blo 932582 1053499 := bstep (se 1 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 1053499 = 1580249) B1580249
theorem B8328089 : Blo 932582 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B2102201 : Blo 932582 2102201 := bstep (se 2 (by rfl) ⟨788325, by rfl⟩ : syracuseStep 2102201 = 1576651) B1576651
theorem B2659529 : Blo 932582 2659529 := bstep (se 2 (by rfl) ⟨997323, by rfl⟩ : syracuseStep 2659529 = 1994647) B1994647
theorem B2364673 : Blo 932582 2364673 := bstep (se 2 (by rfl) ⟨886752, by rfl⟩ : syracuseStep 2364673 = 1773505) B1773505
theorem B2102543 : Blo 932582 2102543 := bstep (se 1 (by rfl) ⟨1576907, by rfl⟩ : syracuseStep 2102543 = 3153815) B3153815
theorem B2102561 : Blo 932582 2102561 := bstep (se 2 (by rfl) ⟨788460, by rfl⟩ : syracuseStep 2102561 = 1576921) B1576921
theorem B4101491 : Blo 932582 4101491 := bstep (se 1 (by rfl) ⟨3076118, by rfl⟩ : syracuseStep 4101491 = 6152237) B6152237
theorem B1578359 : Blo 932582 1578359 := bstep (se 1 (by rfl) ⟨1183769, by rfl⟩ : syracuseStep 1578359 = 2367539) B2367539
theorem B7083449 : Blo 932582 7083449 := bstep (se 2 (by rfl) ⟨2656293, by rfl⟩ : syracuseStep 7083449 = 5312587) B5312587
theorem B3544505 : Blo 932582 3544505 := bstep (se 2 (by rfl) ⟨1329189, by rfl⟩ : syracuseStep 3544505 = 2658379) B2658379
theorem B2102903 : Blo 932582 2102903 := bstep (se 1 (by rfl) ⟨1577177, by rfl⟩ : syracuseStep 2102903 = 3154355) B3154355
theorem B2528921 : Blo 932582 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B4495105 : Blo 932582 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B5314319 : Blo 932582 5314319 := bstep (se 1 (by rfl) ⟨3985739, by rfl⟩ : syracuseStep 5314319 = 7971479) B7971479
theorem B2660111 : Blo 932582 2660111 := bstep (se 1 (by rfl) ⟨1995083, by rfl⟩ : syracuseStep 2660111 = 3990167) B3990167
theorem B2103083 : Blo 932582 2103083 := bstep (se 1 (by rfl) ⟨1577312, by rfl⟩ : syracuseStep 2103083 = 3154625) B3154625
theorem B1578811 : Blo 932582 1578811 := bstep (se 1 (by rfl) ⟨1184108, by rfl⟩ : syracuseStep 1578811 = 2368217) B2368217
theorem B2365271 : Blo 932582 2365271 := bstep (se 1 (by rfl) ⟨1773953, by rfl⟩ : syracuseStep 2365271 = 3547907) B3547907
theorem B1775495 : Blo 932582 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B3151763 : Blo 932582 3151763 := bstep (se 1 (by rfl) ⟨2363822, by rfl⟩ : syracuseStep 3151763 = 4727645) B4727645
theorem B1578953 : Blo 932582 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B10622987 : Blo 932582 10622987 := bstep (se 1 (by rfl) ⟨7967240, by rfl⟩ : syracuseStep 10622987 = 15934481) B15934481
theorem B5314571 : Blo 932582 5314571 := bstep (se 1 (by rfl) ⟨3985928, by rfl⟩ : syracuseStep 5314571 = 7971857) B7971857
theorem B2365483 : Blo 932582 2365483 := bstep (se 1 (by rfl) ⟨1774112, by rfl⟩ : syracuseStep 2365483 = 3548225) B3548225
theorem B2103443 : Blo 932582 2103443 := bstep (se 1 (by rfl) ⟨1577582, by rfl⟩ : syracuseStep 2103443 = 3155165) B3155165
theorem B2365625 : Blo 932582 2365625 := bstep (se 2 (by rfl) ⟨887109, by rfl⟩ : syracuseStep 2365625 = 1774219) B1774219
theorem B2103497 : Blo 932582 2103497 := bstep (se 2 (by rfl) ⟨788811, by rfl⟩ : syracuseStep 2103497 = 1577623) B1577623
theorem B20191477 : Blo 932582 20191477 := bstep (se 5 (by rfl) ⟨946475, by rfl⟩ : syracuseStep 20191477 = 1892951) B1892951
theorem B2529623 : Blo 932582 2529623 := bstep (se 1 (by rfl) ⟨1897217, by rfl⟩ : syracuseStep 2529623 = 3794435) B3794435
theorem B1776019 : Blo 932582 1776019 := bstep (se 1 (by rfl) ⟨1332014, by rfl⟩ : syracuseStep 1776019 = 2664029) B2664029
theorem B3545491 : Blo 932582 3545491 := bstep (se 1 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 3545491 = 5318237) B5318237
theorem B1579655 : Blo 932582 1579655 := bstep (se 1 (by rfl) ⟨1184741, by rfl⟩ : syracuseStep 1579655 = 2369483) B2369483
theorem B2530163 : Blo 932582 2530163 := bstep (se 1 (by rfl) ⟨1897622, by rfl⟩ : syracuseStep 2530163 = 3795245) B3795245
theorem B2104199 : Blo 932582 2104199 := bstep (se 1 (by rfl) ⟨1578149, by rfl⟩ : syracuseStep 2104199 = 3156299) B3156299
theorem B2104379 : Blo 932582 2104379 := bstep (se 1 (by rfl) ⟨1578284, by rfl⟩ : syracuseStep 2104379 = 3156569) B3156569
theorem B2661511 : Blo 932582 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B2366617 : Blo 932582 2366617 := bstep (se 2 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 2366617 = 1774963) B1774963
theorem B2104505 : Blo 932582 2104505 := bstep (se 2 (by rfl) ⟨789189, by rfl⟩ : syracuseStep 2104505 = 1578379) B1578379
theorem B5315777 : Blo 932582 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B3153167 : Blo 932582 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B1580303 : Blo 932582 1580303 := bstep (se 1 (by rfl) ⟨1185227, by rfl⟩ : syracuseStep 1580303 = 2370455) B2370455
theorem B2989345 : Blo 932582 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B2366779 : Blo 932582 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B2661785 : Blo 932582 2661785 := bstep (se 2 (by rfl) ⟨998169, by rfl⟩ : syracuseStep 2661785 = 1996339) B1996339
theorem B1973705 : Blo 932582 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B2366921 : Blo 932582 2366921 := bstep (se 2 (by rfl) ⟨887595, by rfl⟩ : syracuseStep 2366921 = 1775191) B1775191
theorem B2104847 : Blo 932582 2104847 := bstep (se 1 (by rfl) ⟨1578635, by rfl⟩ : syracuseStep 2104847 = 3157271) B3157271
theorem B3153437 : Blo 932582 3153437 := bstep (se 3 (by rfl) ⟨591269, by rfl⟩ : syracuseStep 3153437 = 1182539) B1182539
theorem B2104865 : Blo 932582 2104865 := bstep (se 2 (by rfl) ⟨789324, by rfl⟩ : syracuseStep 2104865 = 1578649) B1578649
theorem B1777211 : Blo 932582 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B23076427 : Blo 932582 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B40345229 : Blo 932582 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B2367265 : Blo 932582 2367265 := bstep (se 2 (by rfl) ⟨887724, by rfl⟩ : syracuseStep 2367265 = 1775449) B1775449
theorem B2105207 : Blo 932582 2105207 := bstep (se 1 (by rfl) ⟨1578905, by rfl⟩ : syracuseStep 2105207 = 3157811) B3157811
theorem B4726673 : Blo 932582 4726673 := bstep (se 2 (by rfl) ⟨1772502, by rfl⟩ : syracuseStep 4726673 = 3545005) B3545005
theorem B1777697 : Blo 932582 1777697 := bstep (se 2 (by rfl) ⟨666636, by rfl⟩ : syracuseStep 1777697 = 1333273) B1333273
theorem B2105387 : Blo 932582 2105387 := bstep (se 1 (by rfl) ⟨1579040, by rfl⟩ : syracuseStep 2105387 = 3158081) B3158081
theorem B3547223 : Blo 932582 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B1777963 : Blo 932582 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B2367863 : Blo 932582 2367863 := bstep (se 1 (by rfl) ⟨1775897, by rfl⟩ : syracuseStep 2367863 = 3551795) B3551795
theorem B2105747 : Blo 932582 2105747 := bstep (se 1 (by rfl) ⟨1579310, by rfl⟩ : syracuseStep 2105747 = 3158621) B3158621
theorem B2105801 : Blo 932582 2105801 := bstep (se 2 (by rfl) ⟨789675, by rfl⟩ : syracuseStep 2105801 = 1579351) B1579351
theorem B3547709 : Blo 932582 3547709 := bstep (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) B1330391
theorem B2663027 : Blo 932582 2663027 := bstep (se 1 (by rfl) ⟨1997270, by rfl⟩ : syracuseStep 2663027 = 3994541) B3994541
theorem B6726401 : Blo 932582 6726401 := bstep (se 2 (by rfl) ⟨2522400, by rfl⟩ : syracuseStep 6726401 = 5044801) B5044801
theorem B11969315 : Blo 932582 11969315 := bstep (se 1 (by rfl) ⟨8976986, by rfl⟩ : syracuseStep 11969315 = 17953973) B17953973
theorem B4793177 : Blo 932582 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B3154841 : Blo 932582 3154841 := bstep (se 2 (by rfl) ⟨1183065, by rfl⟩ : syracuseStep 3154841 = 2366131) B2366131
theorem B2106503 : Blo 932582 2106503 := bstep (se 1 (by rfl) ⟨1579877, by rfl⟩ : syracuseStep 2106503 = 3159755) B3159755
theorem B2106683 : Blo 932582 2106683 := bstep (se 1 (by rfl) ⟨1580012, by rfl⟩ : syracuseStep 2106683 = 3160025) B3160025
theorem B2106809 : Blo 932582 2106809 := bstep (se 2 (by rfl) ⟨790053, by rfl⟩ : syracuseStep 2106809 = 1580107) B1580107
theorem B3155543 : Blo 932582 3155543 := bstep (se 1 (by rfl) ⟨2366657, by rfl⟩ : syracuseStep 3155543 = 4733315) B4733315
theorem B2369159 : Blo 932582 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B2369209 : Blo 932582 2369209 := bstep (se 2 (by rfl) ⟨888453, by rfl⟩ : syracuseStep 2369209 = 1776907) B1776907
theorem B2107151 : Blo 932582 2107151 := bstep (se 1 (by rfl) ⟨1580363, by rfl⟩ : syracuseStep 2107151 = 3160727) B3160727
theorem B2107169 : Blo 932582 2107169 := bstep (se 2 (by rfl) ⟨790188, by rfl⟩ : syracuseStep 2107169 = 1580377) B1580377
theorem B5121937 : Blo 932582 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B4728779 : Blo 932582 4728779 := bstep (se 1 (by rfl) ⟨3546584, by rfl⟩ : syracuseStep 4728779 = 7093169) B7093169
theorem B3156029 : Blo 932582 3156029 := bstep (se 3 (by rfl) ⟨591755, by rfl⟩ : syracuseStep 3156029 = 1183511) B1183511
theorem B4729103 : Blo 932582 4729103 := bstep (se 1 (by rfl) ⟨3546827, by rfl⟩ : syracuseStep 4729103 = 7093655) B7093655
theorem B3844367 : Blo 932582 3844367 := bstep (se 1 (by rfl) ⟨2883275, by rfl⟩ : syracuseStep 3844367 = 5766551) B5766551
theorem B2369807 : Blo 932582 2369807 := bstep (se 1 (by rfl) ⟨1777355, by rfl⟩ : syracuseStep 2369807 = 3554711) B3554711
theorem B10627361 : Blo 932582 10627361 := bstep (se 2 (by rfl) ⟨3985260, by rfl⟩ : syracuseStep 10627361 = 7970521) B7970521
theorem B5318945 : Blo 932582 5318945 := bstep (se 2 (by rfl) ⟨1994604, by rfl⟩ : syracuseStep 5318945 = 3989209) B3989209
theorem B7973255 : Blo 932582 7973255 := bstep (se 1 (by rfl) ⟨5979941, by rfl⟩ : syracuseStep 7973255 = 11959883) B11959883
theorem B2992727 : Blo 932582 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B2370505 : Blo 932582 2370505 := bstep (se 2 (by rfl) ⟨888939, by rfl⟩ : syracuseStep 2370505 = 1777879) B1777879
theorem B2665487 : Blo 932582 2665487 := bstep (se 1 (by rfl) ⟨1999115, by rfl⟩ : syracuseStep 2665487 = 3998231) B3998231
theorem B2370647 : Blo 932582 2370647 := bstep (se 1 (by rfl) ⟨1777985, by rfl⟩ : syracuseStep 2370647 = 3555971) B3555971
theorem B5975329 : Blo 932582 5975329 := bstep (se 2 (by rfl) ⟨2240748, by rfl⟩ : syracuseStep 5975329 = 4481497) B4481497
theorem B3157433 : Blo 932582 3157433 := bstep (se 2 (by rfl) ⟨1184037, by rfl⟩ : syracuseStep 3157433 = 2368075) B2368075
theorem B4730561 : Blo 932582 4730561 := bstep (se 2 (by rfl) ⟨1773960, by rfl⟩ : syracuseStep 4730561 = 3547921) B3547921
theorem B7286543 : Blo 932582 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B3551111 : Blo 932582 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B3158027 : Blo 932582 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B3158135 : Blo 932582 3158135 := bstep (se 1 (by rfl) ⟨2368601, by rfl⟩ : syracuseStep 3158135 = 4737203) B4737203
theorem B1683641 : Blo 932582 1683641 := bstep (se 2 (by rfl) ⟨631365, by rfl⟩ : syracuseStep 1683641 = 1262731) B1262731
theorem B2240779 : Blo 932582 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B9089489 : Blo 932582 9089489 := bstep (se 2 (by rfl) ⟨3408558, by rfl⟩ : syracuseStep 9089489 = 6817117) B6817117
theorem B10662353 : Blo 932582 10662353 := bstep (se 2 (by rfl) ⟨3998382, by rfl⟩ : syracuseStep 10662353 = 7996765) B7996765
theorem B5321335 : Blo 932582 5321335 := bstep (se 1 (by rfl) ⟨3991001, by rfl⟩ : syracuseStep 5321335 = 7982003) B7982003
theorem B3158729 : Blo 932582 3158729 := bstep (se 2 (by rfl) ⟨1184523, by rfl⟩ : syracuseStep 3158729 = 2369047) B2369047
theorem B2241395 : Blo 932582 2241395 := bstep (se 1 (by rfl) ⟨1681046, by rfl⟩ : syracuseStep 2241395 = 3362093) B3362093
theorem B4731857 : Blo 932582 4731857 := bstep (se 2 (by rfl) ⟨1774446, by rfl⟩ : syracuseStep 4731857 = 3548893) B3548893
theorem B8991749 : Blo 932582 8991749 := bstep (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) B1685953
theorem B10630277 : Blo 932582 10630277 := bstep (se 4 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 10630277 = 1993177) B1993177
theorem B3159431 : Blo 932582 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B22754915 : Blo 932582 22754915 := bstep (se 1 (by rfl) ⟨17066186, by rfl⟩ : syracuseStep 22754915 = 34132373) B34132373
theorem B3159809 : Blo 932582 3159809 := bstep (se 2 (by rfl) ⟨1184928, by rfl⟩ : syracuseStep 3159809 = 2369857) B2369857
theorem B5322611 : Blo 932582 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B997255 : Blo 932582 997255 := bstep (se 1 (by rfl) ⟨747941, by rfl⟩ : syracuseStep 997255 = 1495883) B1495883
theorem B1685623 : Blo 932582 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B5323067 : Blo 932582 5323067 := bstep (se 1 (by rfl) ⟨3992300, by rfl⟩ : syracuseStep 5323067 = 7984601) B7984601
theorem B3193235 : Blo 932582 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B3160619 : Blo 932582 3160619 := bstep (se 1 (by rfl) ⟨2370464, by rfl⟩ : syracuseStep 3160619 = 4740929) B4740929
theorem B932615 : Blo 932582 932615 := bstep (se 1 (by rfl) ⟨699461, by rfl⟩ : syracuseStep 932615 = 1398923) B1398923
theorem B932623 : Blo 932582 932623 := bstep (se 1 (by rfl) ⟨699467, by rfl⟩ : syracuseStep 932623 = 1398935) B1398935
theorem B5749555 : Blo 932582 5749555 := bstep (se 1 (by rfl) ⟨4312166, by rfl⟩ : syracuseStep 5749555 = 8624333) B8624333
theorem B6404915 : Blo 932582 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B932667 : Blo 932582 932667 := bstep (se 1 (by rfl) ⟨699500, by rfl⟩ : syracuseStep 932667 = 1399001) B1399001
theorem B932743 : Blo 932582 932743 := bstep (se 1 (by rfl) ⟨699557, by rfl⟩ : syracuseStep 932743 = 1399115) B1399115
theorem B932751 : Blo 932582 932751 := bstep (se 1 (by rfl) ⟨699563, by rfl⟩ : syracuseStep 932751 = 1399127) B1399127
theorem B932795 : Blo 932582 932795 := bstep (se 1 (by rfl) ⟨699596, by rfl⟩ : syracuseStep 932795 = 1399193) B1399193
theorem B2702281 : Blo 932582 2702281 := bstep (se 2 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 2702281 = 2026711) B2026711
theorem B932871 : Blo 932582 932871 := bstep (se 1 (by rfl) ⟨699653, by rfl⟩ : syracuseStep 932871 = 1399307) B1399307
theorem B4733963 : Blo 932582 4733963 := bstep (se 1 (by rfl) ⟨3550472, by rfl⟩ : syracuseStep 4733963 = 7100945) B7100945
theorem B932879 : Blo 932582 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B932923 : Blo 932582 932923 := bstep (se 1 (by rfl) ⟨699692, by rfl⟩ : syracuseStep 932923 = 1399385) B1399385
theorem B932999 : Blo 932582 932999 := bstep (se 1 (by rfl) ⟨699749, by rfl⟩ : syracuseStep 932999 = 1399499) B1399499
theorem B933007 : Blo 932582 933007 := bstep (se 1 (by rfl) ⟨699755, by rfl⟩ : syracuseStep 933007 = 1399511) B1399511
theorem B4734125 : Blo 932582 4734125 := bstep (se 3 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 4734125 = 1775297) B1775297
theorem B933051 : Blo 932582 933051 := bstep (se 1 (by rfl) ⟨699788, by rfl⟩ : syracuseStep 933051 = 1399577) B1399577
theorem B933127 : Blo 932582 933127 := bstep (se 1 (by rfl) ⟨699845, by rfl⟩ : syracuseStep 933127 = 1399691) B1399691
theorem B933135 : Blo 932582 933135 := bstep (se 1 (by rfl) ⟨699851, by rfl⟩ : syracuseStep 933135 = 1399703) B1399703
theorem B2243855 : Blo 932582 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B5324069 : Blo 932582 5324069 := bstep (se 4 (by rfl) ⟨499131, by rfl⟩ : syracuseStep 5324069 = 998263) B998263
theorem B933179 : Blo 932582 933179 := bstep (se 1 (by rfl) ⟨699884, by rfl⟩ : syracuseStep 933179 = 1399769) B1399769
theorem B933255 : Blo 932582 933255 := bstep (se 1 (by rfl) ⟨699941, by rfl⟩ : syracuseStep 933255 = 1399883) B1399883
theorem B933263 : Blo 932582 933263 := bstep (se 1 (by rfl) ⟨699947, by rfl⟩ : syracuseStep 933263 = 1399895) B1399895
theorem B933307 : Blo 932582 933307 := bstep (se 1 (by rfl) ⟨699980, by rfl⟩ : syracuseStep 933307 = 1399961) B1399961
theorem B933383 : Blo 932582 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B933391 : Blo 932582 933391 := bstep (se 1 (by rfl) ⟨700043, by rfl⟩ : syracuseStep 933391 = 1400087) B1400087
theorem B8535581 : Blo 932582 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B933435 : Blo 932582 933435 := bstep (se 1 (by rfl) ⟨700076, by rfl⟩ : syracuseStep 933435 = 1400153) B1400153
theorem B933511 : Blo 932582 933511 := bstep (se 1 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 933511 = 1400267) B1400267
theorem B933519 : Blo 932582 933519 := bstep (se 1 (by rfl) ⟨700139, by rfl⟩ : syracuseStep 933519 = 1400279) B1400279
theorem B933563 : Blo 932582 933563 := bstep (se 1 (by rfl) ⟨700172, by rfl⟩ : syracuseStep 933563 = 1400345) B1400345
theorem B5324525 : Blo 932582 5324525 := bstep (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) B1996697
theorem B933639 : Blo 932582 933639 := bstep (se 1 (by rfl) ⟨700229, by rfl⟩ : syracuseStep 933639 = 1400459) B1400459
theorem B933647 : Blo 932582 933647 := bstep (se 1 (by rfl) ⟨700235, by rfl⟩ : syracuseStep 933647 = 1400471) B1400471
theorem B3194657 : Blo 932582 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B933691 : Blo 932582 933691 := bstep (se 1 (by rfl) ⟨700268, by rfl⟩ : syracuseStep 933691 = 1400537) B1400537
theorem B2244439 : Blo 932582 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B933767 : Blo 932582 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B933775 : Blo 932582 933775 := bstep (se 1 (by rfl) ⟨700331, by rfl⟩ : syracuseStep 933775 = 1400663) B1400663
theorem B4865939 : Blo 932582 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B933819 : Blo 932582 933819 := bstep (se 1 (by rfl) ⟨700364, by rfl⟩ : syracuseStep 933819 = 1400729) B1400729
theorem B933895 : Blo 932582 933895 := bstep (se 1 (by rfl) ⟨700421, by rfl⟩ : syracuseStep 933895 = 1400843) B1400843
theorem B933903 : Blo 932582 933903 := bstep (se 1 (by rfl) ⟨700427, by rfl⟩ : syracuseStep 933903 = 1400855) B1400855
theorem B933947 : Blo 932582 933947 := bstep (se 1 (by rfl) ⟨700460, by rfl⟩ : syracuseStep 933947 = 1400921) B1400921
theorem B1917047 : Blo 932582 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B934023 : Blo 932582 934023 := bstep (se 1 (by rfl) ⟨700517, by rfl⟩ : syracuseStep 934023 = 1401035) B1401035
theorem B934031 : Blo 932582 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B934075 : Blo 932582 934075 := bstep (se 1 (by rfl) ⟨700556, by rfl⟩ : syracuseStep 934075 = 1401113) B1401113
theorem B934151 : Blo 932582 934151 := bstep (se 1 (by rfl) ⟨700613, by rfl⟩ : syracuseStep 934151 = 1401227) B1401227
theorem B934159 : Blo 932582 934159 := bstep (se 1 (by rfl) ⟨700619, by rfl⟩ : syracuseStep 934159 = 1401239) B1401239
theorem B2277665 : Blo 932582 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B934203 : Blo 932582 934203 := bstep (se 1 (by rfl) ⟨700652, by rfl⟩ : syracuseStep 934203 = 1401305) B1401305
theorem B934279 : Blo 932582 934279 := bstep (se 1 (by rfl) ⟨700709, by rfl⟩ : syracuseStep 934279 = 1401419) B1401419
theorem B934287 : Blo 932582 934287 := bstep (se 1 (by rfl) ⟨700715, by rfl⟩ : syracuseStep 934287 = 1401431) B1401431
theorem B11977105 : Blo 932582 11977105 := bstep (se 2 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 11977105 = 8982829) B8982829
theorem B5325209 : Blo 932582 5325209 := bstep (se 2 (by rfl) ⟨1996953, by rfl⟩ : syracuseStep 5325209 = 3993907) B3993907
theorem B934331 : Blo 932582 934331 := bstep (se 1 (by rfl) ⟨700748, by rfl⟩ : syracuseStep 934331 = 1401497) B1401497
theorem B934407 : Blo 932582 934407 := bstep (se 1 (by rfl) ⟨700805, by rfl⟩ : syracuseStep 934407 = 1401611) B1401611
theorem B934415 : Blo 932582 934415 := bstep (se 1 (by rfl) ⟨700811, by rfl⟩ : syracuseStep 934415 = 1401623) B1401623
theorem B934459 : Blo 932582 934459 := bstep (se 1 (by rfl) ⟨700844, by rfl⟩ : syracuseStep 934459 = 1401689) B1401689
theorem B934535 : Blo 932582 934535 := bstep (se 1 (by rfl) ⟨700901, by rfl⟩ : syracuseStep 934535 = 1401803) B1401803
theorem B934543 : Blo 932582 934543 := bstep (se 1 (by rfl) ⟨700907, by rfl⟩ : syracuseStep 934543 = 1401815) B1401815
theorem B934587 : Blo 932582 934587 := bstep (se 1 (by rfl) ⟨700940, by rfl⟩ : syracuseStep 934587 = 1401881) B1401881
theorem B3785417 : Blo 932582 3785417 := bstep (se 2 (by rfl) ⟨1419531, by rfl⟩ : syracuseStep 3785417 = 2839063) B2839063
theorem B4735745 : Blo 932582 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B934663 : Blo 932582 934663 := bstep (se 1 (by rfl) ⟨700997, by rfl⟩ : syracuseStep 934663 = 1401995) B1401995
theorem B934671 : Blo 932582 934671 := bstep (se 1 (by rfl) ⟨701003, by rfl⟩ : syracuseStep 934671 = 1402007) B1402007
theorem B934715 : Blo 932582 934715 := bstep (se 1 (by rfl) ⟨701036, by rfl⟩ : syracuseStep 934715 = 1402073) B1402073
theorem B934791 : Blo 932582 934791 := bstep (se 1 (by rfl) ⟨701093, by rfl⟩ : syracuseStep 934791 = 1402187) B1402187
theorem B934799 : Blo 932582 934799 := bstep (se 1 (by rfl) ⟨701099, by rfl⟩ : syracuseStep 934799 = 1402199) B1402199
theorem B934843 : Blo 932582 934843 := bstep (se 1 (by rfl) ⟨701132, by rfl⟩ : syracuseStep 934843 = 1402265) B1402265
theorem B934919 : Blo 932582 934919 := bstep (se 1 (by rfl) ⟨701189, by rfl⟩ : syracuseStep 934919 = 1402379) B1402379
theorem B934927 : Blo 932582 934927 := bstep (se 1 (by rfl) ⟨701195, by rfl⟩ : syracuseStep 934927 = 1402391) B1402391
theorem B934971 : Blo 932582 934971 := bstep (se 1 (by rfl) ⟨701228, by rfl⟩ : syracuseStep 934971 = 1402457) B1402457
theorem B935047 : Blo 932582 935047 := bstep (se 1 (by rfl) ⟨701285, by rfl⟩ : syracuseStep 935047 = 1402571) B1402571
theorem B935055 : Blo 932582 935055 := bstep (se 1 (by rfl) ⟨701291, by rfl⟩ : syracuseStep 935055 = 1402583) B1402583
theorem B1197227 : Blo 932582 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B935099 : Blo 932582 935099 := bstep (se 1 (by rfl) ⟨701324, by rfl⟩ : syracuseStep 935099 = 1402649) B1402649
theorem B1328329 : Blo 932582 1328329 := bstep (se 2 (by rfl) ⟨498123, by rfl⟩ : syracuseStep 1328329 = 996247) B996247
theorem B935175 : Blo 932582 935175 := bstep (se 1 (by rfl) ⟨701381, by rfl⟩ : syracuseStep 935175 = 1402763) B1402763
theorem B935183 : Blo 932582 935183 := bstep (se 1 (by rfl) ⟨701387, by rfl⟩ : syracuseStep 935183 = 1402775) B1402775
theorem B2245931 : Blo 932582 2245931 := bstep (se 1 (by rfl) ⟨1684448, by rfl⟩ : syracuseStep 2245931 = 3368897) B3368897
theorem B6735163 : Blo 932582 6735163 := bstep (se 1 (by rfl) ⟨5051372, by rfl⟩ : syracuseStep 6735163 = 10102745) B10102745
theorem B935227 : Blo 932582 935227 := bstep (se 1 (by rfl) ⟨701420, by rfl⟩ : syracuseStep 935227 = 1402841) B1402841
theorem B935303 : Blo 932582 935303 := bstep (se 1 (by rfl) ⟨701477, by rfl⟩ : syracuseStep 935303 = 1402955) B1402955
theorem B935311 : Blo 932582 935311 := bstep (se 1 (by rfl) ⟨701483, by rfl⟩ : syracuseStep 935311 = 1402967) B1402967
theorem B2999699 : Blo 932582 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B935355 : Blo 932582 935355 := bstep (se 1 (by rfl) ⟨701516, by rfl⟩ : syracuseStep 935355 = 1403033) B1403033
theorem B935431 : Blo 932582 935431 := bstep (se 1 (by rfl) ⟨701573, by rfl⟩ : syracuseStep 935431 = 1403147) B1403147
theorem B935439 : Blo 932582 935439 := bstep (se 1 (by rfl) ⟨701579, by rfl⟩ : syracuseStep 935439 = 1403159) B1403159
theorem B4736555 : Blo 932582 4736555 := bstep (se 1 (by rfl) ⟨3552416, by rfl⟩ : syracuseStep 4736555 = 7104833) B7104833
theorem B935483 : Blo 932582 935483 := bstep (se 1 (by rfl) ⟨701612, by rfl⟩ : syracuseStep 935483 = 1403225) B1403225
theorem B935559 : Blo 932582 935559 := bstep (se 1 (by rfl) ⟨701669, by rfl⟩ : syracuseStep 935559 = 1403339) B1403339
theorem B935567 : Blo 932582 935567 := bstep (se 1 (by rfl) ⟨701675, by rfl⟩ : syracuseStep 935567 = 1403351) B1403351
theorem B1328825 : Blo 932582 1328825 := bstep (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) B996619
theorem B935611 : Blo 932582 935611 := bstep (se 1 (by rfl) ⟨701708, by rfl⟩ : syracuseStep 935611 = 1403417) B1403417
theorem B30295781 : Blo 932582 30295781 := bstep (se 4 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 30295781 = 5680459) B5680459
theorem B935687 : Blo 932582 935687 := bstep (se 1 (by rfl) ⟨701765, by rfl⟩ : syracuseStep 935687 = 1403531) B1403531
theorem B935695 : Blo 932582 935695 := bstep (se 1 (by rfl) ⟨701771, by rfl⟩ : syracuseStep 935695 = 1403543) B1403543
theorem B935739 : Blo 932582 935739 := bstep (se 1 (by rfl) ⟨701804, by rfl⟩ : syracuseStep 935739 = 1403609) B1403609
theorem B935815 : Blo 932582 935815 := bstep (se 1 (by rfl) ⟨701861, by rfl⟩ : syracuseStep 935815 = 1403723) B1403723
theorem B935823 : Blo 932582 935823 := bstep (se 1 (by rfl) ⟨701867, by rfl⟩ : syracuseStep 935823 = 1403735) B1403735
theorem B935867 : Blo 932582 935867 := bstep (se 1 (by rfl) ⟨701900, by rfl⟩ : syracuseStep 935867 = 1403801) B1403801
theorem B935943 : Blo 932582 935943 := bstep (se 1 (by rfl) ⟨701957, by rfl⟩ : syracuseStep 935943 = 1403915) B1403915
theorem B935951 : Blo 932582 935951 := bstep (se 1 (by rfl) ⟨701963, by rfl⟩ : syracuseStep 935951 = 1403927) B1403927
theorem B2246699 : Blo 932582 2246699 := bstep (se 1 (by rfl) ⟨1685024, by rfl⟩ : syracuseStep 2246699 = 3370049) B3370049
theorem B935995 : Blo 932582 935995 := bstep (se 1 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 935995 = 1403993) B1403993
theorem B4048957 : Blo 932582 4048957 := bstep (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) B1518359
theorem B936071 : Blo 932582 936071 := bstep (se 1 (by rfl) ⟨702053, by rfl⟩ : syracuseStep 936071 = 1404107) B1404107
theorem B936079 : Blo 932582 936079 := bstep (se 1 (by rfl) ⟨702059, by rfl⟩ : syracuseStep 936079 = 1404119) B1404119
theorem B64702637 : Blo 932582 64702637 := bstep (se 3 (by rfl) ⟨12131744, by rfl⟩ : syracuseStep 64702637 = 24263489) B24263489
theorem B936123 : Blo 932582 936123 := bstep (se 1 (by rfl) ⟨702092, by rfl⟩ : syracuseStep 936123 = 1404185) B1404185
theorem B4868353 : Blo 932582 4868353 := bstep (se 2 (by rfl) ⟨1825632, by rfl⟩ : syracuseStep 4868353 = 3651265) B3651265
theorem B936199 : Blo 932582 936199 := bstep (se 1 (by rfl) ⟨702149, by rfl⟩ : syracuseStep 936199 = 1404299) B1404299
theorem B936207 : Blo 932582 936207 := bstep (se 1 (by rfl) ⟨702155, by rfl⟩ : syracuseStep 936207 = 1404311) B1404311
theorem B936251 : Blo 932582 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B936327 : Blo 932582 936327 := bstep (se 1 (by rfl) ⟨702245, by rfl⟩ : syracuseStep 936327 = 1404491) B1404491
theorem B936335 : Blo 932582 936335 := bstep (se 1 (by rfl) ⟨702251, by rfl⟩ : syracuseStep 936335 = 1404503) B1404503
theorem B936379 : Blo 932582 936379 := bstep (se 1 (by rfl) ⟨702284, by rfl⟩ : syracuseStep 936379 = 1404569) B1404569
theorem B936455 : Blo 932582 936455 := bstep (se 1 (by rfl) ⟨702341, by rfl⟩ : syracuseStep 936455 = 1404683) B1404683
theorem B936463 : Blo 932582 936463 := bstep (se 1 (by rfl) ⟨702347, by rfl⟩ : syracuseStep 936463 = 1404695) B1404695
theorem B936507 : Blo 932582 936507 := bstep (se 1 (by rfl) ⟨702380, by rfl⟩ : syracuseStep 936507 = 1404761) B1404761
theorem B1329799 : Blo 932582 1329799 := bstep (se 1 (by rfl) ⟨997349, by rfl⟩ : syracuseStep 1329799 = 1994699) B1994699
theorem B2247439 : Blo 932582 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B4737851 : Blo 932582 4737851 := bstep (se 1 (by rfl) ⟨3553388, by rfl⟩ : syracuseStep 4737851 = 7106777) B7106777
theorem B4311923 : Blo 932582 4311923 := bstep (se 1 (by rfl) ⟨3233942, by rfl⟩ : syracuseStep 4311923 = 6467885) B6467885
theorem B4738013 : Blo 932582 4738013 := bstep (se 3 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 4738013 = 1776755) B1776755
theorem B1494217 : Blo 932582 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B4738337 : Blo 932582 4738337 := bstep (se 2 (by rfl) ⟨1776876, by rfl⟩ : syracuseStep 4738337 = 3553753) B3553753
theorem B8998289 : Blo 932582 8998289 := bstep (se 2 (by rfl) ⟨3374358, by rfl⟩ : syracuseStep 8998289 = 6748717) B6748717
theorem B3198475 : Blo 932582 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B1265287 : Blo 932582 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B5689025 : Blo 932582 5689025 := bstep (se 2 (by rfl) ⟨2133384, by rfl⟩ : syracuseStep 5689025 = 4266769) B4266769
theorem B2838419 : Blo 932582 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B5328899 : Blo 932582 5328899 := bstep (se 1 (by rfl) ⟨3996674, by rfl⟩ : syracuseStep 5328899 = 7993349) B7993349
theorem B1331257 : Blo 932582 1331257 := bstep (se 2 (by rfl) ⟨499221, by rfl⟩ : syracuseStep 1331257 = 998443) B998443
theorem B4739309 : Blo 932582 4739309 := bstep (se 3 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 4739309 = 1777241) B1777241
theorem B3363257 : Blo 932582 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B8966609 : Blo 932582 8966609 := bstep (se 2 (by rfl) ⟨3362478, by rfl⟩ : syracuseStep 8966609 = 6724957) B6724957
theorem B4051727 : Blo 932582 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B6738967 : Blo 932582 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B4740119 : Blo 932582 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B1332487 : Blo 932582 1332487 := bstep (se 1 (by rfl) ⟨999365, by rfl⟩ : syracuseStep 1332487 = 1998731) B1998731
theorem B5690675 : Blo 932582 5690675 := bstep (se 1 (by rfl) ⟨4268006, by rfl⟩ : syracuseStep 5690675 = 8536013) B8536013
theorem B5985683 : Blo 932582 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B26990009 : Blo 932582 26990009 := bstep (se 2 (by rfl) ⟨10121253, by rfl⟩ : syracuseStep 26990009 = 20242507) B20242507
theorem B2250283 : Blo 932582 2250283 := bstep (se 1 (by rfl) ⟨1687712, by rfl⟩ : syracuseStep 2250283 = 3375425) B3375425
theorem B11982437 : Blo 932582 11982437 := bstep (se 4 (by rfl) ⟨1123353, by rfl⟩ : syracuseStep 11982437 = 2246707) B2246707
theorem B10639025 : Blo 932582 10639025 := bstep (se 2 (by rfl) ⟨3989634, by rfl⟩ : syracuseStep 10639025 = 7979269) B7979269
theorem B8509157 : Blo 932582 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B17946521 : Blo 932582 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B10115117 : Blo 932582 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B1333307 : Blo 932582 1333307 := bstep (se 1 (by rfl) ⟨999980, by rfl⟩ : syracuseStep 1333307 = 1999961) B1999961
theorem B184440907 : Blo 932582 184440907 := bstep (se 1 (by rfl) ⟨138330680, by rfl⟩ : syracuseStep 184440907 = 276661361) B276661361
theorem B1398971 : Blo 932582 1398971 := bstep (se 1 (by rfl) ⟨1049228, by rfl⟩ : syracuseStep 1398971 = 2098457) B2098457
theorem B1399031 : Blo 932582 1399031 := bstep (se 1 (by rfl) ⟨1049273, by rfl⟩ : syracuseStep 1399031 = 2098547) B2098547
theorem B1399055 : Blo 932582 1399055 := bstep (se 1 (by rfl) ⟨1049291, by rfl⟩ : syracuseStep 1399055 = 2098583) B2098583
theorem B1399097 : Blo 932582 1399097 := bstep (se 2 (by rfl) ⟨524661, by rfl⟩ : syracuseStep 1399097 = 1049323) B1049323
theorem B1399175 : Blo 932582 1399175 := bstep (se 1 (by rfl) ⟨1049381, by rfl⟩ : syracuseStep 1399175 = 2098763) B2098763
theorem B4544903 : Blo 932582 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B1399211 : Blo 932582 1399211 := bstep (se 1 (by rfl) ⟨1049408, by rfl⟩ : syracuseStep 1399211 = 2098817) B2098817
theorem B1399241 : Blo 932582 1399241 := bstep (se 2 (by rfl) ⟨524715, by rfl⟩ : syracuseStep 1399241 = 1049431) B1049431
theorem B1399355 : Blo 932582 1399355 := bstep (se 1 (by rfl) ⟨1049516, by rfl⟩ : syracuseStep 1399355 = 2099033) B2099033
theorem B1399415 : Blo 932582 1399415 := bstep (se 1 (by rfl) ⟨1049561, by rfl⟩ : syracuseStep 1399415 = 2099123) B2099123
theorem B1399439 : Blo 932582 1399439 := bstep (se 1 (by rfl) ⟨1049579, by rfl⟩ : syracuseStep 1399439 = 2099159) B2099159
theorem B1399481 : Blo 932582 1399481 := bstep (se 2 (by rfl) ⟨524805, by rfl⟩ : syracuseStep 1399481 = 1049611) B1049611
theorem B1399559 : Blo 932582 1399559 := bstep (se 1 (by rfl) ⟨1049669, by rfl⟩ : syracuseStep 1399559 = 2099339) B2099339
theorem B1399595 : Blo 932582 1399595 := bstep (se 1 (by rfl) ⟨1049696, by rfl⟩ : syracuseStep 1399595 = 2099393) B2099393
theorem B1399625 : Blo 932582 1399625 := bstep (se 2 (by rfl) ⟨524859, by rfl⟩ : syracuseStep 1399625 = 1049719) B1049719
theorem B1399739 : Blo 932582 1399739 := bstep (se 1 (by rfl) ⟨1049804, by rfl⟩ : syracuseStep 1399739 = 2099609) B2099609
theorem B1399799 : Blo 932582 1399799 := bstep (se 1 (by rfl) ⟨1049849, by rfl⟩ : syracuseStep 1399799 = 2099699) B2099699
theorem B1399823 : Blo 932582 1399823 := bstep (se 1 (by rfl) ⟨1049867, by rfl⟩ : syracuseStep 1399823 = 2099735) B2099735
theorem B1399865 : Blo 932582 1399865 := bstep (se 2 (by rfl) ⟨524949, by rfl⟩ : syracuseStep 1399865 = 1049899) B1049899
theorem B3988541 : Blo 932582 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B1399943 : Blo 932582 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B1399979 : Blo 932582 1399979 := bstep (se 1 (by rfl) ⟨1049984, by rfl⟩ : syracuseStep 1399979 = 2099969) B2099969
theorem B1400009 : Blo 932582 1400009 := bstep (se 2 (by rfl) ⟨525003, by rfl⟩ : syracuseStep 1400009 = 1050007) B1050007
theorem B7986377 : Blo 932582 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B1400123 : Blo 932582 1400123 := bstep (se 1 (by rfl) ⟨1050092, by rfl⟩ : syracuseStep 1400123 = 2100185) B2100185
theorem B1400183 : Blo 932582 1400183 := bstep (se 1 (by rfl) ⟨1050137, by rfl⟩ : syracuseStep 1400183 = 2100275) B2100275
theorem B1400207 : Blo 932582 1400207 := bstep (se 1 (by rfl) ⟨1050155, by rfl⟩ : syracuseStep 1400207 = 2100311) B2100311
theorem B1400249 : Blo 932582 1400249 := bstep (se 2 (by rfl) ⟨525093, by rfl⟩ : syracuseStep 1400249 = 1050187) B1050187
theorem B7101917 : Blo 932582 7101917 := bstep (se 3 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 7101917 = 2663219) B2663219
theorem B1400327 : Blo 932582 1400327 := bstep (se 1 (by rfl) ⟨1050245, by rfl⟩ : syracuseStep 1400327 = 2100491) B2100491
theorem B1400363 : Blo 932582 1400363 := bstep (se 1 (by rfl) ⟨1050272, by rfl⟩ : syracuseStep 1400363 = 2100545) B2100545
theorem B1400393 : Blo 932582 1400393 := bstep (se 2 (by rfl) ⟨525147, by rfl⟩ : syracuseStep 1400393 = 1050295) B1050295
theorem B3202679 : Blo 932582 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1400507 : Blo 932582 1400507 := bstep (se 1 (by rfl) ⟨1050380, by rfl⟩ : syracuseStep 1400507 = 2100761) B2100761
theorem B1400567 : Blo 932582 1400567 := bstep (se 1 (by rfl) ⟨1050425, by rfl⟩ : syracuseStep 1400567 = 2100851) B2100851
theorem B1400591 : Blo 932582 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B1498895 : Blo 932582 1498895 := bstep (se 1 (by rfl) ⟨1124171, by rfl⟩ : syracuseStep 1498895 = 2248343) B2248343
theorem B1400633 : Blo 932582 1400633 := bstep (se 2 (by rfl) ⟨525237, by rfl⟩ : syracuseStep 1400633 = 1050475) B1050475
theorem B1400711 : Blo 932582 1400711 := bstep (se 1 (by rfl) ⟨1050533, by rfl⟩ : syracuseStep 1400711 = 2101067) B2101067
theorem B1400747 : Blo 932582 1400747 := bstep (se 1 (by rfl) ⟨1050560, by rfl⟩ : syracuseStep 1400747 = 2101121) B2101121
theorem B1400777 : Blo 932582 1400777 := bstep (se 2 (by rfl) ⟨525291, by rfl⟩ : syracuseStep 1400777 = 1050583) B1050583
theorem B3989533 : Blo 932582 3989533 := bstep (se 3 (by rfl) ⟨748037, by rfl⟩ : syracuseStep 3989533 = 1496075) B1496075
theorem B1400891 : Blo 932582 1400891 := bstep (se 1 (by rfl) ⟨1050668, by rfl⟩ : syracuseStep 1400891 = 2101337) B2101337
theorem B1400951 : Blo 932582 1400951 := bstep (se 1 (by rfl) ⟨1050713, by rfl⟩ : syracuseStep 1400951 = 2101427) B2101427
theorem B1400975 : Blo 932582 1400975 := bstep (se 1 (by rfl) ⟨1050731, by rfl⟩ : syracuseStep 1400975 = 2101463) B2101463
theorem B1401017 : Blo 932582 1401017 := bstep (se 2 (by rfl) ⟨525381, by rfl⟩ : syracuseStep 1401017 = 1050763) B1050763
theorem B1401095 : Blo 932582 1401095 := bstep (se 1 (by rfl) ⟨1050821, by rfl⟩ : syracuseStep 1401095 = 2101643) B2101643
theorem B1401131 : Blo 932582 1401131 := bstep (se 1 (by rfl) ⟨1050848, by rfl⟩ : syracuseStep 1401131 = 2101697) B2101697
theorem B20209985 : Blo 932582 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B1401161 : Blo 932582 1401161 := bstep (se 2 (by rfl) ⟨525435, by rfl⟩ : syracuseStep 1401161 = 1050871) B1050871
theorem B1401275 : Blo 932582 1401275 := bstep (se 1 (by rfl) ⟨1050956, by rfl⟩ : syracuseStep 1401275 = 2101913) B2101913
theorem B1401335 : Blo 932582 1401335 := bstep (se 1 (by rfl) ⟨1051001, by rfl⟩ : syracuseStep 1401335 = 2102003) B2102003
theorem B1401359 : Blo 932582 1401359 := bstep (se 1 (by rfl) ⟨1051019, by rfl⟩ : syracuseStep 1401359 = 2102039) B2102039
theorem B1401401 : Blo 932582 1401401 := bstep (se 2 (by rfl) ⟨525525, by rfl⟩ : syracuseStep 1401401 = 1051051) B1051051
theorem B1401479 : Blo 932582 1401479 := bstep (se 1 (by rfl) ⟨1051109, by rfl⟩ : syracuseStep 1401479 = 2102219) B2102219
theorem B1401515 : Blo 932582 1401515 := bstep (se 1 (by rfl) ⟨1051136, by rfl⟩ : syracuseStep 1401515 = 2102273) B2102273
theorem B4481729 : Blo 932582 4481729 := bstep (se 2 (by rfl) ⟨1680648, by rfl⟩ : syracuseStep 4481729 = 3361297) B3361297
theorem B1401545 : Blo 932582 1401545 := bstep (se 2 (by rfl) ⟨525579, by rfl⟩ : syracuseStep 1401545 = 1051159) B1051159
theorem B7988017 : Blo 932582 7988017 := bstep (se 2 (by rfl) ⟨2995506, by rfl⟩ : syracuseStep 7988017 = 5991013) B5991013
theorem B1401659 : Blo 932582 1401659 := bstep (se 1 (by rfl) ⟨1051244, by rfl⟩ : syracuseStep 1401659 = 2102489) B2102489
theorem B1401719 : Blo 932582 1401719 := bstep (se 1 (by rfl) ⟨1051289, by rfl⟩ : syracuseStep 1401719 = 2102579) B2102579
theorem B1401743 : Blo 932582 1401743 := bstep (se 1 (by rfl) ⟨1051307, by rfl⟩ : syracuseStep 1401743 = 2102615) B2102615
theorem B1401785 : Blo 932582 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B1401863 : Blo 932582 1401863 := bstep (se 1 (by rfl) ⟨1051397, by rfl⟩ : syracuseStep 1401863 = 2102795) B2102795
theorem B1401899 : Blo 932582 1401899 := bstep (se 1 (by rfl) ⟨1051424, by rfl⟩ : syracuseStep 1401899 = 2102849) B2102849
theorem B10806317 : Blo 932582 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B1401929 : Blo 932582 1401929 := bstep (se 2 (by rfl) ⟨525723, by rfl⟩ : syracuseStep 1401929 = 1051447) B1051447
theorem B64873547 : Blo 932582 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B1402043 : Blo 932582 1402043 := bstep (se 1 (by rfl) ⟨1051532, by rfl⟩ : syracuseStep 1402043 = 2103065) B2103065
theorem B1402103 : Blo 932582 1402103 := bstep (se 1 (by rfl) ⟨1051577, by rfl⟩ : syracuseStep 1402103 = 2103155) B2103155
theorem B1402127 : Blo 932582 1402127 := bstep (se 1 (by rfl) ⟨1051595, by rfl⟩ : syracuseStep 1402127 = 2103191) B2103191
theorem B1402169 : Blo 932582 1402169 := bstep (se 2 (by rfl) ⟨525813, by rfl⟩ : syracuseStep 1402169 = 1051627) B1051627
theorem B1402247 : Blo 932582 1402247 := bstep (se 1 (by rfl) ⟨1051685, by rfl⟩ : syracuseStep 1402247 = 2103371) B2103371
theorem B1402283 : Blo 932582 1402283 := bstep (se 1 (by rfl) ⟨1051712, by rfl⟩ : syracuseStep 1402283 = 2103425) B2103425
theorem B1402313 : Blo 932582 1402313 := bstep (se 2 (by rfl) ⟨525867, by rfl⟩ : syracuseStep 1402313 = 1051735) B1051735
theorem B1402427 : Blo 932582 1402427 := bstep (se 1 (by rfl) ⟨1051820, by rfl⟩ : syracuseStep 1402427 = 2103641) B2103641
theorem B1402487 : Blo 932582 1402487 := bstep (se 1 (by rfl) ⟨1051865, by rfl⟩ : syracuseStep 1402487 = 2103731) B2103731
theorem B1402511 : Blo 932582 1402511 := bstep (se 1 (by rfl) ⟨1051883, by rfl⟩ : syracuseStep 1402511 = 2103767) B2103767
theorem B1402553 : Blo 932582 1402553 := bstep (se 2 (by rfl) ⟨525957, by rfl⟩ : syracuseStep 1402553 = 1051915) B1051915
theorem B1402631 : Blo 932582 1402631 := bstep (se 1 (by rfl) ⟨1051973, by rfl⟩ : syracuseStep 1402631 = 2103947) B2103947
theorem B1402667 : Blo 932582 1402667 := bstep (se 1 (by rfl) ⟨1052000, by rfl⟩ : syracuseStep 1402667 = 2104001) B2104001
theorem B1402697 : Blo 932582 1402697 := bstep (se 2 (by rfl) ⟨526011, by rfl⟩ : syracuseStep 1402697 = 1052023) B1052023
theorem B3991481 : Blo 932582 3991481 := bstep (se 2 (by rfl) ⟨1496805, by rfl⟩ : syracuseStep 3991481 = 2993611) B2993611
theorem B1402811 : Blo 932582 1402811 := bstep (se 1 (by rfl) ⟨1052108, by rfl⟩ : syracuseStep 1402811 = 2104217) B2104217
theorem B1402871 : Blo 932582 1402871 := bstep (se 1 (by rfl) ⟨1052153, by rfl⟩ : syracuseStep 1402871 = 2104307) B2104307
theorem B1402895 : Blo 932582 1402895 := bstep (se 1 (by rfl) ⟨1052171, by rfl⟩ : syracuseStep 1402895 = 2104343) B2104343
theorem B1402937 : Blo 932582 1402937 := bstep (se 2 (by rfl) ⟨526101, by rfl⟩ : syracuseStep 1402937 = 1052203) B1052203
theorem B1403015 : Blo 932582 1403015 := bstep (se 1 (by rfl) ⟨1052261, by rfl⟩ : syracuseStep 1403015 = 2104523) B2104523
theorem B1403051 : Blo 932582 1403051 := bstep (se 1 (by rfl) ⟨1052288, by rfl⟩ : syracuseStep 1403051 = 2104577) B2104577
theorem B1403081 : Blo 932582 1403081 := bstep (se 2 (by rfl) ⟨526155, by rfl⟩ : syracuseStep 1403081 = 1052311) B1052311
theorem B4483343 : Blo 932582 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B1403195 : Blo 932582 1403195 := bstep (se 1 (by rfl) ⟨1052396, by rfl⟩ : syracuseStep 1403195 = 2104793) B2104793
theorem B1403255 : Blo 932582 1403255 := bstep (se 1 (by rfl) ⟨1052441, by rfl⟩ : syracuseStep 1403255 = 2104883) B2104883
theorem B3991943 : Blo 932582 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B1403279 : Blo 932582 1403279 := bstep (se 1 (by rfl) ⟨1052459, by rfl⟩ : syracuseStep 1403279 = 2104919) B2104919
theorem B1403321 : Blo 932582 1403321 := bstep (se 2 (by rfl) ⟨526245, by rfl⟩ : syracuseStep 1403321 = 1052491) B1052491
theorem B1403399 : Blo 932582 1403399 := bstep (se 1 (by rfl) ⟨1052549, by rfl⟩ : syracuseStep 1403399 = 2105099) B2105099
theorem B4483613 : Blo 932582 4483613 := bstep (se 3 (by rfl) ⟨840677, by rfl⟩ : syracuseStep 4483613 = 1681355) B1681355
theorem B1403435 : Blo 932582 1403435 := bstep (se 1 (by rfl) ⟨1052576, by rfl⟩ : syracuseStep 1403435 = 2105153) B2105153
theorem B1403465 : Blo 932582 1403465 := bstep (se 2 (by rfl) ⟨526299, by rfl⟩ : syracuseStep 1403465 = 1052599) B1052599
theorem B1403579 : Blo 932582 1403579 := bstep (se 1 (by rfl) ⟨1052684, by rfl⟩ : syracuseStep 1403579 = 2105369) B2105369
theorem B1403639 : Blo 932582 1403639 := bstep (se 1 (by rfl) ⟨1052729, by rfl⟩ : syracuseStep 1403639 = 2105459) B2105459
theorem B1403663 : Blo 932582 1403663 := bstep (se 1 (by rfl) ⟨1052747, by rfl⟩ : syracuseStep 1403663 = 2105495) B2105495
theorem B1403705 : Blo 932582 1403705 := bstep (se 2 (by rfl) ⟨526389, by rfl⟩ : syracuseStep 1403705 = 1052779) B1052779
theorem B1403783 : Blo 932582 1403783 := bstep (se 1 (by rfl) ⟨1052837, by rfl⟩ : syracuseStep 1403783 = 2105675) B2105675
theorem B1403819 : Blo 932582 1403819 := bstep (se 1 (by rfl) ⟨1052864, by rfl⟩ : syracuseStep 1403819 = 2105729) B2105729
theorem B1993673 : Blo 932582 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B1403849 : Blo 932582 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B5401565 : Blo 932582 5401565 := bstep (se 3 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 5401565 = 2025587) B2025587
theorem B1403963 : Blo 932582 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B1404023 : Blo 932582 1404023 := bstep (se 1 (by rfl) ⟨1053017, by rfl⟩ : syracuseStep 1404023 = 2106035) B2106035
theorem B1404047 : Blo 932582 1404047 := bstep (se 1 (by rfl) ⟨1053035, by rfl⟩ : syracuseStep 1404047 = 2106071) B2106071
theorem B1600697 : Blo 932582 1600697 := bstep (se 2 (by rfl) ⟨600261, by rfl⟩ : syracuseStep 1600697 = 1200523) B1200523
theorem B1404089 : Blo 932582 1404089 := bstep (se 2 (by rfl) ⟨526533, by rfl⟩ : syracuseStep 1404089 = 1053067) B1053067
theorem B1404167 : Blo 932582 1404167 := bstep (se 1 (by rfl) ⟨1053125, by rfl⟩ : syracuseStep 1404167 = 2106251) B2106251
theorem B1404203 : Blo 932582 1404203 := bstep (se 1 (by rfl) ⟨1053152, by rfl⟩ : syracuseStep 1404203 = 2106305) B2106305
theorem B3796283 : Blo 932582 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B1404233 : Blo 932582 1404233 := bstep (se 2 (by rfl) ⟨526587, by rfl⟩ : syracuseStep 1404233 = 1053175) B1053175
theorem B1404347 : Blo 932582 1404347 := bstep (se 1 (by rfl) ⟨1053260, by rfl⟩ : syracuseStep 1404347 = 2106521) B2106521
theorem B1404407 : Blo 932582 1404407 := bstep (se 1 (by rfl) ⟨1053305, by rfl⟩ : syracuseStep 1404407 = 2106611) B2106611
theorem B1404431 : Blo 932582 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B1404473 : Blo 932582 1404473 := bstep (se 2 (by rfl) ⟨526677, by rfl⟩ : syracuseStep 1404473 = 1053355) B1053355
theorem B1404551 : Blo 932582 1404551 := bstep (se 1 (by rfl) ⟨1053413, by rfl⟩ : syracuseStep 1404551 = 2106827) B2106827
theorem B1404587 : Blo 932582 1404587 := bstep (se 1 (by rfl) ⟨1053440, by rfl⟩ : syracuseStep 1404587 = 2106881) B2106881
theorem B945851 : Blo 932582 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B1404617 : Blo 932582 1404617 := bstep (se 2 (by rfl) ⟨526731, by rfl⟩ : syracuseStep 1404617 = 1053463) B1053463
theorem B3796769 : Blo 932582 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B1404731 : Blo 932582 1404731 := bstep (se 1 (by rfl) ⟨1053548, by rfl⟩ : syracuseStep 1404731 = 2107097) B2107097
theorem B20213621 : Blo 932582 20213621 := bstep (se 5 (by rfl) ⟨947513, by rfl⟩ : syracuseStep 20213621 = 1895027) B1895027
theorem B1404791 : Blo 932582 1404791 := bstep (se 1 (by rfl) ⟨1053593, by rfl⟩ : syracuseStep 1404791 = 2107187) B2107187
theorem B1404815 : Blo 932582 1404815 := bstep (se 1 (by rfl) ⟨1053611, by rfl⟩ : syracuseStep 1404815 = 2107223) B2107223
theorem B1994681 : Blo 932582 1994681 := bstep (se 2 (by rfl) ⟨748005, by rfl⟩ : syracuseStep 1994681 = 1496011) B1496011
theorem B1404857 : Blo 932582 1404857 := bstep (se 2 (by rfl) ⟨526821, by rfl⟩ : syracuseStep 1404857 = 1053643) B1053643
theorem B3993857 : Blo 932582 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1995023 : Blo 932582 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B4486033 : Blo 932582 4486033 := bstep (se 2 (by rfl) ⟨1682262, by rfl⟩ : syracuseStep 4486033 = 3364525) B3364525
theorem B45413297 : Blo 932582 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B4486187 : Blo 932582 4486187 := bstep (se 1 (by rfl) ⟨3364640, by rfl⟩ : syracuseStep 4486187 = 6729281) B6729281
theorem B1995835 : Blo 932582 1995835 := bstep (se 1 (by rfl) ⟨1496876, by rfl⟩ : syracuseStep 1995835 = 2993753) B2993753
theorem B8516897 : Blo 932582 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1996321 : Blo 932582 1996321 := bstep (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) B1497241
theorem B3372587 : Blo 932582 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B1799827 : Blo 932582 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B1898255 : Blo 932582 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B1996663 : Blo 932582 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B3373579 : Blo 932582 3373579 := bstep (se 1 (by rfl) ⟨2530184, by rfl⟩ : syracuseStep 3373579 = 5060369) B5060369
theorem B2128531 : Blo 932582 2128531 := bstep (se 1 (by rfl) ⟨1596398, by rfl⟩ : syracuseStep 2128531 = 3192797) B3192797
theorem B7109693 : Blo 932582 7109693 := bstep (se 3 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 7109693 = 2666135) B2666135
theorem B9337943 : Blo 932582 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B3374963 : Blo 932582 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B1278031 : Blo 932582 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B21594437 : Blo 932582 21594437 := bstep (se 4 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 21594437 = 4048957) B4048957
theorem B5767529 : Blo 932582 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B2523611 : Blo 932582 2523611 := bstep (se 1 (by rfl) ⟨1892708, by rfl⟩ : syracuseStep 2523611 = 3785417) B3785417
theorem B1049287 : Blo 932582 1049287 := bstep (se 1 (by rfl) ⟨786965, by rfl⟩ : syracuseStep 1049287 = 1573931) B1573931
theorem B1999799 : Blo 932582 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B1573897 : Blo 932582 1573897 := bstep (se 2 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 1573897 = 1180423) B1180423
theorem B10650689 : Blo 932582 10650689 := bstep (se 2 (by rfl) ⟨3994008, by rfl⟩ : syracuseStep 10650689 = 7988017) B7988017
theorem B1574059 : Blo 932582 1574059 := bstep (se 1 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 1574059 = 2361089) B2361089
theorem B3998915 : Blo 932582 3998915 := bstep (se 1 (by rfl) ⟨2999186, by rfl⟩ : syracuseStep 3998915 = 5998373) B5998373
theorem B1705391 : Blo 932582 1705391 := bstep (se 1 (by rfl) ⟨1279043, by rfl⟩ : syracuseStep 1705391 = 2558087) B2558087
theorem B1574363 : Blo 932582 1574363 := bstep (se 1 (by rfl) ⟨1180772, by rfl⟩ : syracuseStep 1574363 = 2361545) B2361545
theorem B2098727 : Blo 932582 2098727 := bstep (se 1 (by rfl) ⟨1574045, by rfl⟩ : syracuseStep 2098727 = 3148091) B3148091
theorem B1050151 : Blo 932582 1050151 := bstep (se 1 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 1050151 = 1575227) B1575227
theorem B1574599 : Blo 932582 1574599 := bstep (se 1 (by rfl) ⟨1180949, by rfl⟩ : syracuseStep 1574599 = 2361899) B2361899
theorem B8980217 : Blo 932582 8980217 := bstep (se 2 (by rfl) ⟨3367581, by rfl⟩ : syracuseStep 8980217 = 6735163) B6735163
theorem B1574761 : Blo 932582 1574761 := bstep (se 2 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 1574761 = 1181071) B1181071
theorem B2099051 : Blo 932582 2099051 := bstep (se 1 (by rfl) ⟨1574288, by rfl⟩ : syracuseStep 2099051 = 3148577) B3148577
theorem B2099105 : Blo 932582 2099105 := bstep (se 2 (by rfl) ⟨787164, by rfl⟩ : syracuseStep 2099105 = 1574329) B1574329
theorem B2361271 : Blo 932582 2361271 := bstep (se 1 (by rfl) ⟨1770953, by rfl⟩ : syracuseStep 2361271 = 3541907) B3541907
theorem B1181623 : Blo 932582 1181623 := bstep (se 1 (by rfl) ⟨886217, by rfl⟩ : syracuseStep 1181623 = 1772435) B1772435
theorem B8652737 : Blo 932582 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B30279683 : Blo 932582 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B27330659 : Blo 932582 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B3147929 : Blo 932582 3147929 := bstep (se 2 (by rfl) ⟨1180473, by rfl⟩ : syracuseStep 3147929 = 2360947) B2360947
theorem B2099447 : Blo 932582 2099447 := bstep (se 1 (by rfl) ⟨1574585, by rfl⟩ : syracuseStep 2099447 = 3149171) B3149171
theorem B5998859 : Blo 932582 5998859 := bstep (se 1 (by rfl) ⟨4499144, by rfl⟩ : syracuseStep 5998859 = 8998289) B8998289
theorem B3541391 : Blo 932582 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B1575355 : Blo 932582 1575355 := bstep (se 1 (by rfl) ⟨1181516, by rfl⟩ : syracuseStep 1575355 = 2363033) B2363033
theorem B1575463 : Blo 932582 1575463 := bstep (se 1 (by rfl) ⟨1181597, by rfl⟩ : syracuseStep 1575463 = 2363195) B2363195
theorem B2100041 : Blo 932582 2100041 := bstep (se 2 (by rfl) ⟨787515, by rfl⟩ : syracuseStep 2100041 = 1575031) B1575031
theorem B1575787 : Blo 932582 1575787 := bstep (se 1 (by rfl) ⟨1181840, by rfl⟩ : syracuseStep 1575787 = 2363681) B2363681
theorem B6491137 : Blo 932582 6491137 := bstep (se 2 (by rfl) ⟨2434176, by rfl⟩ : syracuseStep 6491137 = 4868353) B4868353
theorem B1051771 : Blo 932582 1051771 := bstep (se 1 (by rfl) ⟨788828, by rfl⟩ : syracuseStep 1051771 = 1577657) B1577657
theorem B5049539 : Blo 932582 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B1182919 : Blo 932582 1182919 := bstep (se 1 (by rfl) ⟨887189, by rfl⟩ : syracuseStep 1182919 = 1774379) B1774379
theorem B3149117 : Blo 932582 3149117 := bstep (se 3 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 3149117 = 1180919) B1180919
theorem B2362729 : Blo 932582 2362729 := bstep (se 2 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 2362729 = 1772047) B1772047
theorem B1773019 : Blo 932582 1773019 := bstep (se 1 (by rfl) ⟨1329764, by rfl⟩ : syracuseStep 1773019 = 2659529) B2659529
theorem B15175133 : Blo 932582 15175133 := bstep (se 3 (by rfl) ⟨2845337, by rfl⟩ : syracuseStep 15175133 = 5690675) B5690675
theorem B1773065 : Blo 932582 1773065 := bstep (se 2 (by rfl) ⟨664899, by rfl⟩ : syracuseStep 1773065 = 1329799) B1329799
theorem B3542561 : Blo 932582 3542561 := bstep (se 2 (by rfl) ⟨1328460, by rfl⟩ : syracuseStep 3542561 = 2656921) B2656921
theorem B1052239 : Blo 932582 1052239 := bstep (se 1 (by rfl) ⟨789179, by rfl⟩ : syracuseStep 1052239 = 1578359) B1578359
theorem B2100833 : Blo 932582 2100833 := bstep (se 2 (by rfl) ⟨787812, by rfl⟩ : syracuseStep 2100833 = 1575625) B1575625
theorem B4722299 : Blo 932582 4722299 := bstep (se 1 (by rfl) ⟨3541724, by rfl⟩ : syracuseStep 4722299 = 7083449) B7083449
theorem B2363003 : Blo 932582 2363003 := bstep (se 1 (by rfl) ⟨1772252, by rfl⟩ : syracuseStep 2363003 = 3544505) B3544505
theorem B17993339 : Blo 932582 17993339 := bstep (se 1 (by rfl) ⟨13495004, by rfl⟩ : syracuseStep 17993339 = 26990009) B26990009
theorem B17960737 : Blo 932582 17960737 := bstep (se 2 (by rfl) ⟨6735276, by rfl⟩ : syracuseStep 17960737 = 13470553) B13470553
theorem B5672771 : Blo 932582 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B3542879 : Blo 932582 3542879 := bstep (se 1 (by rfl) ⟨2657159, by rfl⟩ : syracuseStep 3542879 = 5314319) B5314319
theorem B1773407 : Blo 932582 1773407 := bstep (se 1 (by rfl) ⟨1330055, by rfl⟩ : syracuseStep 1773407 = 2660111) B2660111
theorem B1576847 : Blo 932582 1576847 := bstep (se 1 (by rfl) ⟨1182635, by rfl⟩ : syracuseStep 1576847 = 2365271) B2365271
theorem B1183663 : Blo 932582 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B2101175 : Blo 932582 2101175 := bstep (se 1 (by rfl) ⟨1575881, by rfl⟩ : syracuseStep 2101175 = 3151763) B3151763
theorem B11964347 : Blo 932582 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B1052635 : Blo 932582 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B7081991 : Blo 932582 7081991 := bstep (se 1 (by rfl) ⟨5311493, by rfl⟩ : syracuseStep 7081991 = 10622987) B10622987
theorem B3543047 : Blo 932582 3543047 := bstep (se 1 (by rfl) ⟨2657285, by rfl⟩ : syracuseStep 3543047 = 5314571) B5314571
theorem B1577083 : Blo 932582 1577083 := bstep (se 1 (by rfl) ⟨1182812, by rfl⟩ : syracuseStep 1577083 = 2365625) B2365625
theorem B3149981 : Blo 932582 3149981 := bstep (se 3 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 3149981 = 1181243) B1181243
theorem B7967105 : Blo 932582 7967105 := bstep (se 2 (by rfl) ⟨2987664, by rfl⟩ : syracuseStep 7967105 = 5975329) B5975329
theorem B1053103 : Blo 932582 1053103 := bstep (se 1 (by rfl) ⟨789827, by rfl⟩ : syracuseStep 1053103 = 1579655) B1579655
theorem B7082477 : Blo 932582 7082477 := bstep (se 3 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 7082477 = 2655929) B2655929
theorem B3543533 : Blo 932582 3543533 := bstep (se 3 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 3543533 = 1328825) B1328825
theorem B2101769 : Blo 932582 2101769 := bstep (se 2 (by rfl) ⟨788163, by rfl⟩ : syracuseStep 2101769 = 1576327) B1576327
theorem B3150521 : Blo 932582 3150521 := bstep (se 2 (by rfl) ⟨1181445, by rfl⟩ : syracuseStep 3150521 = 2362891) B2362891
theorem B4264633 : Blo 932582 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B3543851 : Blo 932582 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B2102111 : Blo 932582 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B1053535 : Blo 932582 1053535 := bstep (se 1 (by rfl) ⟨790151, by rfl⟩ : syracuseStep 1053535 = 1580303) B1580303
theorem B1774523 : Blo 932582 1774523 := bstep (se 1 (by rfl) ⟨1330892, by rfl⟩ : syracuseStep 1774523 = 2661785) B2661785
theorem B1577947 : Blo 932582 1577947 := bstep (se 1 (by rfl) ⟨1183460, by rfl⟩ : syracuseStep 1577947 = 2366921) B2366921
theorem B2102291 : Blo 932582 2102291 := bstep (se 1 (by rfl) ⟨1576718, by rfl⟩ : syracuseStep 2102291 = 3153437) B3153437
theorem B1184807 : Blo 932582 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B10097729 : Blo 932582 10097729 := bstep (se 2 (by rfl) ⟨3786648, by rfl⟩ : syracuseStep 10097729 = 7573297) B7573297
theorem B3151115 : Blo 932582 3151115 := bstep (se 1 (by rfl) ⟨2363336, by rfl⟩ : syracuseStep 3151115 = 4726673) B4726673
theorem B2102633 : Blo 932582 2102633 := bstep (se 2 (by rfl) ⟨788487, by rfl⟩ : syracuseStep 2102633 = 1576975) B1576975
theorem B1185131 : Blo 932582 1185131 := bstep (se 1 (by rfl) ⟨888848, by rfl⟩ : syracuseStep 1185131 = 1777697) B1777697
theorem B2364815 : Blo 932582 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B1775009 : Blo 932582 1775009 := bstep (se 2 (by rfl) ⟨665628, by rfl⟩ : syracuseStep 1775009 = 1331257) B1331257
theorem B3151385 : Blo 932582 3151385 := bstep (se 2 (by rfl) ⟨1181769, by rfl⟩ : syracuseStep 3151385 = 2363539) B2363539
theorem B13473323 : Blo 932582 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B1578575 : Blo 932582 1578575 := bstep (se 1 (by rfl) ⟨1183931, by rfl⟩ : syracuseStep 1578575 = 2367863) B2367863
theorem B2987705 : Blo 932582 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B2365139 : Blo 932582 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B1775351 : Blo 932582 1775351 := bstep (se 1 (by rfl) ⟨1331513, by rfl⟩ : syracuseStep 1775351 = 2663027) B2663027
theorem B2987819 : Blo 932582 2987819 := bstep (se 1 (by rfl) ⟨2240864, by rfl⟩ : syracuseStep 2987819 = 4481729) B4481729
theorem B2103227 : Blo 932582 2103227 := bstep (se 1 (by rfl) ⟨1577420, by rfl⟩ : syracuseStep 2103227 = 3154841) B3154841
theorem B2103353 : Blo 932582 2103353 := bstep (se 2 (by rfl) ⟨788757, by rfl⟩ : syracuseStep 2103353 = 1577515) B1577515
theorem B4725053 : Blo 932582 4725053 := bstep (se 3 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 4725053 = 1771895) B1771895
theorem B7084421 : Blo 932582 7084421 := bstep (se 4 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 7084421 = 1328329) B1328329
theorem B2103695 : Blo 932582 2103695 := bstep (se 1 (by rfl) ⟨1577771, by rfl⟩ : syracuseStep 2103695 = 3155543) B3155543
theorem B1579439 : Blo 932582 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B2660987 : Blo 932582 2660987 := bstep (se 1 (by rfl) ⟨1995740, by rfl⟩ : syracuseStep 2660987 = 3991481) B3991481
theorem B3152519 : Blo 932582 3152519 := bstep (se 1 (by rfl) ⟨2364389, by rfl⟩ : syracuseStep 3152519 = 4728779) B4728779
theorem B3152573 : Blo 932582 3152573 := bstep (se 3 (by rfl) ⟨591107, by rfl⟩ : syracuseStep 3152573 = 1182215) B1182215
theorem B2104019 : Blo 932582 2104019 := bstep (se 1 (by rfl) ⟨1578014, by rfl⟩ : syracuseStep 2104019 = 3156029) B3156029
theorem B2661113 : Blo 932582 2661113 := bstep (se 2 (by rfl) ⟨997917, by rfl⟩ : syracuseStep 2661113 = 1995835) B1995835
theorem B2562911 : Blo 932582 2562911 := bstep (se 1 (by rfl) ⟨1922183, by rfl⟩ : syracuseStep 2562911 = 3844367) B3844367
theorem B2988895 : Blo 932582 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B3152735 : Blo 932582 3152735 := bstep (se 1 (by rfl) ⟨2364551, by rfl⟩ : syracuseStep 3152735 = 4729103) B4729103
theorem B1579871 : Blo 932582 1579871 := bstep (se 1 (by rfl) ⟨1184903, by rfl⟩ : syracuseStep 1579871 = 2369807) B2369807
theorem B7084907 : Blo 932582 7084907 := bstep (se 1 (by rfl) ⟨5313680, by rfl⟩ : syracuseStep 7084907 = 10627361) B10627361
theorem B3545963 : Blo 932582 3545963 := bstep (se 1 (by rfl) ⟨2659472, by rfl⟩ : syracuseStep 3545963 = 5318945) B5318945
theorem B2661295 : Blo 932582 2661295 := bstep (se 1 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 2661295 = 3991943) B3991943
theorem B5315503 : Blo 932582 5315503 := bstep (se 1 (by rfl) ⟨3986627, by rfl⟩ : syracuseStep 5315503 = 7973255) B7973255
theorem B3152897 : Blo 932582 3152897 := bstep (se 2 (by rfl) ⟨1182336, by rfl⟩ : syracuseStep 3152897 = 2364673) B2364673
theorem B1776649 : Blo 932582 1776649 := bstep (se 2 (by rfl) ⟨666243, by rfl⟩ : syracuseStep 1776649 = 1332487) B1332487
theorem B2989075 : Blo 932582 2989075 := bstep (se 1 (by rfl) ⟨2241806, by rfl⟩ : syracuseStep 2989075 = 4483613) B4483613
theorem B1776991 : Blo 932582 1776991 := bstep (se 1 (by rfl) ⟨1332743, by rfl⟩ : syracuseStep 1776991 = 2665487) B2665487
theorem B2661761 : Blo 932582 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B1580431 : Blo 932582 1580431 := bstep (se 1 (by rfl) ⟨1185323, by rfl⟩ : syracuseStep 1580431 = 2370647) B2370647
theorem B2530855 : Blo 932582 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B2104955 : Blo 932582 2104955 := bstep (se 1 (by rfl) ⟨1578716, by rfl⟩ : syracuseStep 2104955 = 3157433) B3157433
theorem B2105081 : Blo 932582 2105081 := bstep (se 2 (by rfl) ⟨789405, by rfl⟩ : syracuseStep 2105081 = 1578811) B1578811
theorem B3153707 : Blo 932582 3153707 := bstep (se 1 (by rfl) ⟨2365280, by rfl⟩ : syracuseStep 3153707 = 4730561) B4730561
theorem B2662217 : Blo 932582 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B4857695 : Blo 932582 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B2531179 : Blo 932582 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B5316461 : Blo 932582 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B13475747 : Blo 932582 13475747 := bstep (se 1 (by rfl) ⟨10106810, by rfl⟩ : syracuseStep 13475747 = 20213621) B20213621
theorem B2367407 : Blo 932582 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B2105351 : Blo 932582 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B3153977 : Blo 932582 3153977 := bstep (se 2 (by rfl) ⟨1182741, by rfl⟩ : syracuseStep 3153977 = 2365483) B2365483
theorem B2105423 : Blo 932582 2105423 := bstep (se 1 (by rfl) ⟨1579067, by rfl⟩ : syracuseStep 2105423 = 3158135) B3158135
theorem B1122427 : Blo 932582 1122427 := bstep (se 1 (by rfl) ⟨841820, by rfl⟩ : syracuseStep 1122427 = 1683641) B1683641
theorem B2662571 : Blo 932582 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B3154301 : Blo 932582 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B2105819 : Blo 932582 2105819 := bstep (se 1 (by rfl) ⟨1579364, by rfl⟩ : syracuseStep 2105819 = 3158729) B3158729
theorem B4727321 : Blo 932582 4727321 := bstep (se 2 (by rfl) ⟨1772745, by rfl⟩ : syracuseStep 4727321 = 3545491) B3545491
theorem B2368025 : Blo 932582 2368025 := bstep (se 2 (by rfl) ⟨888009, by rfl⟩ : syracuseStep 2368025 = 1776019) B1776019
theorem B3154571 : Blo 932582 3154571 := bstep (se 1 (by rfl) ⟨2365928, by rfl⟩ : syracuseStep 3154571 = 4731857) B4731857
theorem B4498105 : Blo 932582 4498105 := bstep (se 2 (by rfl) ⟨1686789, by rfl⟩ : syracuseStep 4498105 = 3373579) B3373579
theorem B2990791 : Blo 932582 2990791 := bstep (se 1 (by rfl) ⟨2243093, by rfl⟩ : syracuseStep 2990791 = 4486187) B4486187
theorem B7086851 : Blo 932582 7086851 := bstep (se 1 (by rfl) ⟨5315138, by rfl⟩ : syracuseStep 7086851 = 10630277) B10630277
theorem B5677931 : Blo 932582 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B2106287 : Blo 932582 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B2106539 : Blo 932582 2106539 := bstep (se 1 (by rfl) ⟨1579904, by rfl⟩ : syracuseStep 2106539 = 3159809) B3159809
theorem B3548407 : Blo 932582 3548407 := bstep (se 1 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 3548407 = 5322611) B5322611
theorem B3548681 : Blo 932582 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B3155489 : Blo 932582 3155489 := bstep (se 2 (by rfl) ⟨1183308, by rfl⟩ : syracuseStep 3155489 = 2366617) B2366617
theorem B3548711 : Blo 932582 3548711 := bstep (se 1 (by rfl) ⟨2661533, by rfl⟩ : syracuseStep 3548711 = 5323067) B5323067
theorem B2107079 : Blo 932582 2107079 := bstep (se 1 (by rfl) ⟨1580309, by rfl⟩ : syracuseStep 2107079 = 3160619) B3160619
theorem B3155705 : Blo 932582 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B11970341 : Blo 932582 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B4269943 : Blo 932582 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B3155975 : Blo 932582 3155975 := bstep (se 1 (by rfl) ⟨2366981, by rfl⟩ : syracuseStep 3155975 = 4733963) B4733963
theorem B5318693 : Blo 932582 5318693 := bstep (se 4 (by rfl) ⟨498627, by rfl⟩ : syracuseStep 5318693 = 997255) B997255
theorem B3156083 : Blo 932582 3156083 := bstep (se 1 (by rfl) ⟨2367062, by rfl⟩ : syracuseStep 3156083 = 4734125) B4734125
theorem B3549379 : Blo 932582 3549379 := bstep (se 1 (by rfl) ⟨2662034, by rfl⟩ : syracuseStep 3549379 = 5324069) B5324069
theorem B3156353 : Blo 932582 3156353 := bstep (se 2 (by rfl) ⟨1183632, by rfl⟩ : syracuseStep 3156353 = 2367265) B2367265
theorem B6826477 : Blo 932582 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B3549683 : Blo 932582 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B5319377 : Blo 932582 5319377 := bstep (se 2 (by rfl) ⟨1994766, by rfl⟩ : syracuseStep 5319377 = 3989533) B3989533
theorem B1518443 : Blo 932582 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B9612215 : Blo 932582 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B3550139 : Blo 932582 3550139 := bstep (se 1 (by rfl) ⟨2662604, by rfl⟩ : syracuseStep 3550139 = 5325209) B5325209
theorem B2370617 : Blo 932582 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B1682603 : Blo 932582 1682603 := bstep (se 1 (by rfl) ⟨1261952, by rfl⟩ : syracuseStep 1682603 = 2523905) B2523905
theorem B3157163 : Blo 932582 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B15969473 : Blo 932582 15969473 := bstep (se 2 (by rfl) ⟨5988552, by rfl⟩ : syracuseStep 15969473 = 11977105) B11977105
theorem B4730237 : Blo 932582 4730237 := bstep (se 3 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 4730237 = 1773839) B1773839
theorem B3157703 : Blo 932582 3157703 := bstep (se 1 (by rfl) ⟨2368277, by rfl⟩ : syracuseStep 3157703 = 4736555) B4736555
theorem B20197187 : Blo 932582 20197187 := bstep (se 1 (by rfl) ⟨15147890, by rfl⟩ : syracuseStep 20197187 = 30295781) B30295781
theorem B7090253 : Blo 932582 7090253 := bstep (se 3 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 7090253 = 2658845) B2658845
theorem B43135091 : Blo 932582 43135091 := bstep (se 1 (by rfl) ⟨32351318, by rfl⟩ : syracuseStep 43135091 = 64702637) B64702637
theorem B3158567 : Blo 932582 3158567 := bstep (se 1 (by rfl) ⟨2368925, by rfl⟩ : syracuseStep 3158567 = 4737851) B4737851
theorem B3158675 : Blo 932582 3158675 := bstep (se 1 (by rfl) ⟨2369006, by rfl⟩ : syracuseStep 3158675 = 4738013) B4738013
theorem B3846865 : Blo 932582 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B3158891 : Blo 932582 3158891 := bstep (se 1 (by rfl) ⟨2369168, by rfl⟩ : syracuseStep 3158891 = 4738337) B4738337
theorem B3158945 : Blo 932582 3158945 := bstep (se 2 (by rfl) ⟨1184604, by rfl⟩ : syracuseStep 3158945 = 2369209) B2369209
theorem B3552599 : Blo 932582 3552599 := bstep (se 1 (by rfl) ⟨2664449, by rfl⟩ : syracuseStep 3552599 = 5328899) B5328899
theorem B3159539 : Blo 932582 3159539 := bstep (se 1 (by rfl) ⟨2369654, by rfl⟩ : syracuseStep 3159539 = 4739309) B4739309
theorem B2242171 : Blo 932582 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B5977739 : Blo 932582 5977739 := bstep (se 1 (by rfl) ⟨4483304, by rfl⟩ : syracuseStep 5977739 = 8966609) B8966609
theorem B3192605 : Blo 932582 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B2701151 : Blo 932582 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B5552059 : Blo 932582 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B3160079 : Blo 932582 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B2734327 : Blo 932582 2734327 := bstep (se 1 (by rfl) ⟨2050745, by rfl⟩ : syracuseStep 2734327 = 4101491) B4101491
theorem B2996585 : Blo 932582 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B1685947 : Blo 932582 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B7092683 : Blo 932582 7092683 := bstep (se 1 (by rfl) ⟨5319512, by rfl⟩ : syracuseStep 7092683 = 10639025) B10639025
theorem B3160673 : Blo 932582 3160673 := bstep (se 2 (by rfl) ⟨1185252, by rfl⟩ : syracuseStep 3160673 = 2370505) B2370505
theorem B932647 : Blo 932582 932647 := bstep (se 1 (by rfl) ⟨699485, by rfl⟩ : syracuseStep 932647 = 1398971) B1398971
theorem B932687 : Blo 932582 932687 := bstep (se 1 (by rfl) ⟨699515, by rfl⟩ : syracuseStep 932687 = 1399031) B1399031
theorem B932703 : Blo 932582 932703 := bstep (se 1 (by rfl) ⟨699527, by rfl⟩ : syracuseStep 932703 = 1399055) B1399055
theorem B932731 : Blo 932582 932731 := bstep (se 1 (by rfl) ⟨699548, by rfl⟩ : syracuseStep 932731 = 1399097) B1399097
theorem B1686415 : Blo 932582 1686415 := bstep (se 1 (by rfl) ⟨1264811, by rfl⟩ : syracuseStep 1686415 = 2529623) B2529623
theorem B932783 : Blo 932582 932783 := bstep (se 1 (by rfl) ⟨699587, by rfl⟩ : syracuseStep 932783 = 1399175) B1399175
theorem B3029935 : Blo 932582 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B932807 : Blo 932582 932807 := bstep (se 1 (by rfl) ⟨699605, by rfl⟩ : syracuseStep 932807 = 1399211) B1399211
theorem B932827 : Blo 932582 932827 := bstep (se 1 (by rfl) ⟨699620, by rfl⟩ : syracuseStep 932827 = 1399241) B1399241
theorem B932903 : Blo 932582 932903 := bstep (se 1 (by rfl) ⟨699677, by rfl⟩ : syracuseStep 932903 = 1399355) B1399355
theorem B932943 : Blo 932582 932943 := bstep (se 1 (by rfl) ⟨699707, by rfl⟩ : syracuseStep 932943 = 1399415) B1399415
theorem B932959 : Blo 932582 932959 := bstep (se 1 (by rfl) ⟨699719, by rfl⟩ : syracuseStep 932959 = 1399439) B1399439
theorem B932987 : Blo 932582 932987 := bstep (se 1 (by rfl) ⟨699740, by rfl⟩ : syracuseStep 932987 = 1399481) B1399481
theorem B933039 : Blo 932582 933039 := bstep (se 1 (by rfl) ⟨699779, by rfl⟩ : syracuseStep 933039 = 1399559) B1399559
theorem B933063 : Blo 932582 933063 := bstep (se 1 (by rfl) ⟨699797, by rfl⟩ : syracuseStep 933063 = 1399595) B1399595
theorem B933083 : Blo 932582 933083 := bstep (se 1 (by rfl) ⟨699812, by rfl⟩ : syracuseStep 933083 = 1399625) B1399625
theorem B933159 : Blo 932582 933159 := bstep (se 1 (by rfl) ⟨699869, by rfl⟩ : syracuseStep 933159 = 1399739) B1399739
theorem B933199 : Blo 932582 933199 := bstep (se 1 (by rfl) ⟨699899, by rfl⟩ : syracuseStep 933199 = 1399799) B1399799
theorem B933215 : Blo 932582 933215 := bstep (se 1 (by rfl) ⟨699911, by rfl⟩ : syracuseStep 933215 = 1399823) B1399823
theorem B933243 : Blo 932582 933243 := bstep (se 1 (by rfl) ⟨699932, by rfl⟩ : syracuseStep 933243 = 1399865) B1399865
theorem B5062013 : Blo 932582 5062013 := bstep (se 3 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 5062013 = 1898255) B1898255
theorem B933295 : Blo 932582 933295 := bstep (se 1 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 933295 = 1399943) B1399943
theorem B21052853 : Blo 932582 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B933319 : Blo 932582 933319 := bstep (se 1 (by rfl) ⟨699989, by rfl⟩ : syracuseStep 933319 = 1399979) B1399979
theorem B933339 : Blo 932582 933339 := bstep (se 1 (by rfl) ⟨700004, by rfl⟩ : syracuseStep 933339 = 1400009) B1400009
theorem B5324251 : Blo 932582 5324251 := bstep (se 1 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 5324251 = 7986377) B7986377
theorem B1687049 : Blo 932582 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B933415 : Blo 932582 933415 := bstep (se 1 (by rfl) ⟨700061, by rfl⟩ : syracuseStep 933415 = 1400123) B1400123
theorem B933455 : Blo 932582 933455 := bstep (se 1 (by rfl) ⟨700091, by rfl⟩ : syracuseStep 933455 = 1400183) B1400183
theorem B933471 : Blo 932582 933471 := bstep (se 1 (by rfl) ⟨700103, by rfl⟩ : syracuseStep 933471 = 1400207) B1400207
theorem B933499 : Blo 932582 933499 := bstep (se 1 (by rfl) ⟨700124, by rfl⟩ : syracuseStep 933499 = 1400249) B1400249
theorem B4734611 : Blo 932582 4734611 := bstep (se 1 (by rfl) ⟨3550958, by rfl⟩ : syracuseStep 4734611 = 7101917) B7101917
theorem B933551 : Blo 932582 933551 := bstep (se 1 (by rfl) ⟨700163, by rfl⟩ : syracuseStep 933551 = 1400327) B1400327
theorem B933575 : Blo 932582 933575 := bstep (se 1 (by rfl) ⟨700181, by rfl⟩ : syracuseStep 933575 = 1400363) B1400363
theorem B933595 : Blo 932582 933595 := bstep (se 1 (by rfl) ⟨700196, by rfl⟩ : syracuseStep 933595 = 1400393) B1400393
theorem B933671 : Blo 932582 933671 := bstep (se 1 (by rfl) ⟨700253, by rfl⟩ : syracuseStep 933671 = 1400507) B1400507
theorem B933711 : Blo 932582 933711 := bstep (se 1 (by rfl) ⟨700283, by rfl⟩ : syracuseStep 933711 = 1400567) B1400567
theorem B933727 : Blo 932582 933727 := bstep (se 1 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 933727 = 1400591) B1400591
theorem B999263 : Blo 932582 999263 := bstep (se 1 (by rfl) ⟨749447, by rfl⟩ : syracuseStep 999263 = 1498895) B1498895
theorem B933755 : Blo 932582 933755 := bstep (se 1 (by rfl) ⟨700316, by rfl⟩ : syracuseStep 933755 = 1400633) B1400633
theorem B933807 : Blo 932582 933807 := bstep (se 1 (by rfl) ⟨700355, by rfl⟩ : syracuseStep 933807 = 1400711) B1400711
theorem B933831 : Blo 932582 933831 := bstep (se 1 (by rfl) ⟨700373, by rfl⟩ : syracuseStep 933831 = 1400747) B1400747
theorem B933851 : Blo 932582 933851 := bstep (se 1 (by rfl) ⟨700388, by rfl⟩ : syracuseStep 933851 = 1400777) B1400777
theorem B933927 : Blo 932582 933927 := bstep (se 1 (by rfl) ⟨700445, by rfl⟩ : syracuseStep 933927 = 1400891) B1400891
theorem B933967 : Blo 932582 933967 := bstep (se 1 (by rfl) ⟨700475, by rfl⟩ : syracuseStep 933967 = 1400951) B1400951
theorem B933983 : Blo 932582 933983 := bstep (se 1 (by rfl) ⟨700487, by rfl⟩ : syracuseStep 933983 = 1400975) B1400975
theorem B934011 : Blo 932582 934011 := bstep (se 1 (by rfl) ⟨700508, by rfl⟩ : syracuseStep 934011 = 1401017) B1401017
theorem B3555485 : Blo 932582 3555485 := bstep (se 3 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 3555485 = 1333307) B1333307
theorem B934063 : Blo 932582 934063 := bstep (se 1 (by rfl) ⟨700547, by rfl⟩ : syracuseStep 934063 = 1401095) B1401095
theorem B934087 : Blo 932582 934087 := bstep (se 1 (by rfl) ⟨700565, by rfl⟩ : syracuseStep 934087 = 1401131) B1401131
theorem B934107 : Blo 932582 934107 := bstep (se 1 (by rfl) ⟨700580, by rfl⟩ : syracuseStep 934107 = 1401161) B1401161
theorem B934183 : Blo 932582 934183 := bstep (se 1 (by rfl) ⟨700637, by rfl⟩ : syracuseStep 934183 = 1401275) B1401275
theorem B934223 : Blo 932582 934223 := bstep (se 1 (by rfl) ⟨700667, by rfl⟩ : syracuseStep 934223 = 1401335) B1401335
theorem B934239 : Blo 932582 934239 := bstep (se 1 (by rfl) ⟨700679, by rfl⟩ : syracuseStep 934239 = 1401359) B1401359
theorem B934267 : Blo 932582 934267 := bstep (se 1 (by rfl) ⟨700700, by rfl⟩ : syracuseStep 934267 = 1401401) B1401401
theorem B934319 : Blo 932582 934319 := bstep (se 1 (by rfl) ⟨700739, by rfl⟩ : syracuseStep 934319 = 1401479) B1401479
theorem B934343 : Blo 932582 934343 := bstep (se 1 (by rfl) ⟨700757, by rfl⟩ : syracuseStep 934343 = 1401515) B1401515
theorem B934363 : Blo 932582 934363 := bstep (se 1 (by rfl) ⟨700772, by rfl⟩ : syracuseStep 934363 = 1401545) B1401545
theorem B7979543 : Blo 932582 7979543 := bstep (se 1 (by rfl) ⟨5984657, by rfl⟩ : syracuseStep 7979543 = 11969315) B11969315
theorem B934439 : Blo 932582 934439 := bstep (se 1 (by rfl) ⟨700829, by rfl⟩ : syracuseStep 934439 = 1401659) B1401659
theorem B3195451 : Blo 932582 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B934479 : Blo 932582 934479 := bstep (se 1 (by rfl) ⟨700859, by rfl⟩ : syracuseStep 934479 = 1401719) B1401719
theorem B934495 : Blo 932582 934495 := bstep (se 1 (by rfl) ⟨700871, by rfl⟩ : syracuseStep 934495 = 1401743) B1401743
theorem B2277985 : Blo 932582 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B934523 : Blo 932582 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B934575 : Blo 932582 934575 := bstep (se 1 (by rfl) ⟨700931, by rfl⟩ : syracuseStep 934575 = 1401863) B1401863
theorem B934599 : Blo 932582 934599 := bstep (se 1 (by rfl) ⟨700949, by rfl⟩ : syracuseStep 934599 = 1401899) B1401899
theorem B934619 : Blo 932582 934619 := bstep (se 1 (by rfl) ⟨700964, by rfl⟩ : syracuseStep 934619 = 1401929) B1401929
theorem B934695 : Blo 932582 934695 := bstep (se 1 (by rfl) ⟨701021, by rfl⟩ : syracuseStep 934695 = 1402043) B1402043
theorem B7095113 : Blo 932582 7095113 := bstep (se 2 (by rfl) ⟨2660667, by rfl⟩ : syracuseStep 7095113 = 5321335) B5321335
theorem B934735 : Blo 932582 934735 := bstep (se 1 (by rfl) ⟨701051, by rfl⟩ : syracuseStep 934735 = 1402103) B1402103
theorem B934751 : Blo 932582 934751 := bstep (se 1 (by rfl) ⟨701063, by rfl⟩ : syracuseStep 934751 = 1402127) B1402127
theorem B934779 : Blo 932582 934779 := bstep (se 1 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 934779 = 1402169) B1402169
theorem B934831 : Blo 932582 934831 := bstep (se 1 (by rfl) ⟨701123, by rfl⟩ : syracuseStep 934831 = 1402247) B1402247
theorem B934855 : Blo 932582 934855 := bstep (se 1 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 934855 = 1402283) B1402283
theorem B934875 : Blo 932582 934875 := bstep (se 1 (by rfl) ⟨701156, by rfl⟩ : syracuseStep 934875 = 1402313) B1402313
theorem B934951 : Blo 932582 934951 := bstep (se 1 (by rfl) ⟨701213, by rfl⟩ : syracuseStep 934951 = 1402427) B1402427
theorem B934991 : Blo 932582 934991 := bstep (se 1 (by rfl) ⟨701243, by rfl⟩ : syracuseStep 934991 = 1402487) B1402487
theorem B935007 : Blo 932582 935007 := bstep (se 1 (by rfl) ⟨701255, by rfl⟩ : syracuseStep 935007 = 1402511) B1402511
theorem B935035 : Blo 932582 935035 := bstep (se 1 (by rfl) ⟨701276, by rfl⟩ : syracuseStep 935035 = 1402553) B1402553
theorem B935087 : Blo 932582 935087 := bstep (se 1 (by rfl) ⟨701315, by rfl⟩ : syracuseStep 935087 = 1402631) B1402631
theorem B5981377 : Blo 932582 5981377 := bstep (se 2 (by rfl) ⟨2243016, by rfl⟩ : syracuseStep 5981377 = 4486033) B4486033
theorem B935111 : Blo 932582 935111 := bstep (se 1 (by rfl) ⟨701333, by rfl⟩ : syracuseStep 935111 = 1402667) B1402667
theorem B935131 : Blo 932582 935131 := bstep (se 1 (by rfl) ⟨701348, by rfl⟩ : syracuseStep 935131 = 1402697) B1402697
theorem B935207 : Blo 932582 935207 := bstep (se 1 (by rfl) ⟨701405, by rfl⟩ : syracuseStep 935207 = 1402811) B1402811
theorem B935247 : Blo 932582 935247 := bstep (se 1 (by rfl) ⟨701435, by rfl⟩ : syracuseStep 935247 = 1402871) B1402871
theorem B935263 : Blo 932582 935263 := bstep (se 1 (by rfl) ⟨701447, by rfl⟩ : syracuseStep 935263 = 1402895) B1402895
theorem B935291 : Blo 932582 935291 := bstep (se 1 (by rfl) ⟨701468, by rfl⟩ : syracuseStep 935291 = 1402937) B1402937
theorem B935343 : Blo 932582 935343 := bstep (se 1 (by rfl) ⟨701507, by rfl⟩ : syracuseStep 935343 = 1403015) B1403015
theorem B935367 : Blo 932582 935367 := bstep (se 1 (by rfl) ⟨701525, by rfl⟩ : syracuseStep 935367 = 1403051) B1403051
theorem B935387 : Blo 932582 935387 := bstep (se 1 (by rfl) ⟨701540, by rfl⟩ : syracuseStep 935387 = 1403081) B1403081
theorem B935463 : Blo 932582 935463 := bstep (se 1 (by rfl) ⟨701597, by rfl⟩ : syracuseStep 935463 = 1403195) B1403195
theorem B7980605 : Blo 932582 7980605 := bstep (se 3 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 7980605 = 2992727) B2992727
theorem B935503 : Blo 932582 935503 := bstep (se 1 (by rfl) ⟨701627, by rfl⟩ : syracuseStep 935503 = 1403255) B1403255
theorem B935519 : Blo 932582 935519 := bstep (se 1 (by rfl) ⟨701639, by rfl⟩ : syracuseStep 935519 = 1403279) B1403279
theorem B935547 : Blo 932582 935547 := bstep (se 1 (by rfl) ⟨701660, by rfl⟩ : syracuseStep 935547 = 1403321) B1403321
theorem B935599 : Blo 932582 935599 := bstep (se 1 (by rfl) ⟨701699, by rfl⟩ : syracuseStep 935599 = 1403399) B1403399
theorem B935623 : Blo 932582 935623 := bstep (se 1 (by rfl) ⟨701717, by rfl⟩ : syracuseStep 935623 = 1403435) B1403435
theorem B935643 : Blo 932582 935643 := bstep (se 1 (by rfl) ⟨701732, by rfl⟩ : syracuseStep 935643 = 1403465) B1403465
theorem B935719 : Blo 932582 935719 := bstep (se 1 (by rfl) ⟨701789, by rfl⟩ : syracuseStep 935719 = 1403579) B1403579
theorem B935759 : Blo 932582 935759 := bstep (se 1 (by rfl) ⟨701819, by rfl⟩ : syracuseStep 935759 = 1403639) B1403639
theorem B935775 : Blo 932582 935775 := bstep (se 1 (by rfl) ⟨701831, by rfl⟩ : syracuseStep 935775 = 1403663) B1403663
theorem B935803 : Blo 932582 935803 := bstep (se 1 (by rfl) ⟨701852, by rfl⟩ : syracuseStep 935803 = 1403705) B1403705
theorem B935855 : Blo 932582 935855 := bstep (se 1 (by rfl) ⟨701891, by rfl⟩ : syracuseStep 935855 = 1403783) B1403783
theorem B935879 : Blo 932582 935879 := bstep (se 1 (by rfl) ⟨701909, by rfl⟩ : syracuseStep 935879 = 1403819) B1403819
theorem B935899 : Blo 932582 935899 := bstep (se 1 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 935899 = 1403849) B1403849
theorem B935975 : Blo 932582 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B3000377 : Blo 932582 3000377 := bstep (se 2 (by rfl) ⟨1125141, by rfl⟩ : syracuseStep 3000377 = 2250283) B2250283
theorem B936015 : Blo 932582 936015 := bstep (se 1 (by rfl) ⟨702011, by rfl⟩ : syracuseStep 936015 = 1404023) B1404023
theorem B936031 : Blo 932582 936031 := bstep (se 1 (by rfl) ⟨702023, by rfl⟩ : syracuseStep 936031 = 1404047) B1404047
theorem B1067131 : Blo 932582 1067131 := bstep (se 1 (by rfl) ⟨800348, by rfl⟩ : syracuseStep 1067131 = 1600697) B1600697
theorem B936059 : Blo 932582 936059 := bstep (se 1 (by rfl) ⟨702044, by rfl⟩ : syracuseStep 936059 = 1404089) B1404089
theorem B936111 : Blo 932582 936111 := bstep (se 1 (by rfl) ⟨702083, by rfl⟩ : syracuseStep 936111 = 1404167) B1404167
theorem B936135 : Blo 932582 936135 := bstep (se 1 (by rfl) ⟨702101, by rfl⟩ : syracuseStep 936135 = 1404203) B1404203
theorem B936155 : Blo 932582 936155 := bstep (se 1 (by rfl) ⟨702116, by rfl⟩ : syracuseStep 936155 = 1404233) B1404233
theorem B936231 : Blo 932582 936231 := bstep (se 1 (by rfl) ⟨702173, by rfl⟩ : syracuseStep 936231 = 1404347) B1404347
theorem B936271 : Blo 932582 936271 := bstep (se 1 (by rfl) ⟨702203, by rfl⟩ : syracuseStep 936271 = 1404407) B1404407
theorem B936287 : Blo 932582 936287 := bstep (se 1 (by rfl) ⟨702215, by rfl⟩ : syracuseStep 936287 = 1404431) B1404431
theorem B936315 : Blo 932582 936315 := bstep (se 1 (by rfl) ⟨702236, by rfl⟩ : syracuseStep 936315 = 1404473) B1404473
theorem B936367 : Blo 932582 936367 := bstep (se 1 (by rfl) ⟨702275, by rfl⟩ : syracuseStep 936367 = 1404551) B1404551
theorem B936391 : Blo 932582 936391 := bstep (se 1 (by rfl) ⟨702293, by rfl⟩ : syracuseStep 936391 = 1404587) B1404587
theorem B936411 : Blo 932582 936411 := bstep (se 1 (by rfl) ⟨702308, by rfl⟩ : syracuseStep 936411 = 1404617) B1404617
theorem B936487 : Blo 932582 936487 := bstep (se 1 (by rfl) ⟨702365, by rfl⟩ : syracuseStep 936487 = 1404731) B1404731
theorem B936527 : Blo 932582 936527 := bstep (se 1 (by rfl) ⟨702395, by rfl⟩ : syracuseStep 936527 = 1404791) B1404791
theorem B936543 : Blo 932582 936543 := bstep (se 1 (by rfl) ⟨702407, by rfl⟩ : syracuseStep 936543 = 1404815) B1404815
theorem B1329787 : Blo 932582 1329787 := bstep (se 1 (by rfl) ⟨997340, by rfl⟩ : syracuseStep 1329787 = 1994681) B1994681
theorem B936571 : Blo 932582 936571 := bstep (se 1 (by rfl) ⟨702428, by rfl⟩ : syracuseStep 936571 = 1404857) B1404857
theorem B2247497 : Blo 932582 2247497 := bstep (se 2 (by rfl) ⟨842811, by rfl⟩ : syracuseStep 2247497 = 1685623) B1685623
theorem B10636109 : Blo 932582 10636109 := bstep (se 3 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 10636109 = 3988541) B3988541
theorem B1330015 : Blo 932582 1330015 := bstep (se 1 (by rfl) ⟨997511, by rfl⟩ : syracuseStep 1330015 = 1995023) B1995023
theorem B26921969 : Blo 932582 26921969 := bstep (se 2 (by rfl) ⟨10095738, by rfl⟩ : syracuseStep 26921969 = 20191477) B20191477
theorem B1494263 : Blo 932582 1494263 := bstep (se 1 (by rfl) ⟨1120697, by rfl⟩ : syracuseStep 1494263 = 2241395) B2241395
theorem B2838041 : Blo 932582 2838041 := bstep (se 2 (by rfl) ⟨1064265, by rfl⟩ : syracuseStep 2838041 = 2128531) B2128531
theorem B2248391 : Blo 932582 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B45993845 : Blo 932582 45993845 := bstep (se 5 (by rfl) ⟨2155961, by rfl⟩ : syracuseStep 45993845 = 4311923) B4311923
theorem B23973893 : Blo 932582 23973893 := bstep (se 4 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 23973893 = 4495105) B4495105
theorem B8540477 : Blo 932582 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B3985793 : Blo 932582 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B4739795 : Blo 932582 4739795 := bstep (se 1 (by rfl) ⟨3554846, by rfl⟩ : syracuseStep 4739795 = 7109693) B7109693
theorem B27316997 : Blo 932582 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B1495903 : Blo 932582 1495903 := bstep (se 1 (by rfl) ⟨1121927, by rfl⟩ : syracuseStep 1495903 = 2243855) B2243855
theorem B5690387 : Blo 932582 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B2249975 : Blo 932582 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B5985737 : Blo 932582 5985737 := bstep (se 2 (by rfl) ⟨2244651, by rfl⟩ : syracuseStep 5985737 = 4489303) B4489303
theorem B983684837 : Blo 932582 983684837 := bstep (se 4 (by rfl) ⟨92220453, by rfl⟩ : syracuseStep 983684837 = 184440907) B184440907
theorem B1398983 : Blo 932582 1398983 := bstep (se 1 (by rfl) ⟨1049237, by rfl⟩ : syracuseStep 1398983 = 2098475) B2098475
theorem B1497287 : Blo 932582 1497287 := bstep (se 1 (by rfl) ⟨1122965, by rfl⟩ : syracuseStep 1497287 = 2245931) B2245931
theorem B1399145 : Blo 932582 1399145 := bstep (se 2 (by rfl) ⟨524679, by rfl⟩ : syracuseStep 1399145 = 1049359) B1049359
theorem B1399223 : Blo 932582 1399223 := bstep (se 1 (by rfl) ⟨1049417, by rfl⟩ : syracuseStep 1399223 = 2098835) B2098835
theorem B1399259 : Blo 932582 1399259 := bstep (se 1 (by rfl) ⟨1049444, by rfl⟩ : syracuseStep 1399259 = 2098889) B2098889
theorem B1497799 : Blo 932582 1497799 := bstep (se 1 (by rfl) ⟨1123349, by rfl⟩ : syracuseStep 1497799 = 2246699) B2246699
theorem B6740813 : Blo 932582 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B1399727 : Blo 932582 1399727 := bstep (se 1 (by rfl) ⟨1049795, by rfl⟩ : syracuseStep 1399727 = 2099591) B2099591
theorem B1399817 : Blo 932582 1399817 := bstep (se 2 (by rfl) ⟨524931, by rfl⟩ : syracuseStep 1399817 = 1049863) B1049863
theorem B1399847 : Blo 932582 1399847 := bstep (se 1 (by rfl) ⟨1049885, by rfl⟩ : syracuseStep 1399847 = 2099771) B2099771
theorem B1399931 : Blo 932582 1399931 := bstep (se 1 (by rfl) ⟨1049948, by rfl⟩ : syracuseStep 1399931 = 2099897) B2099897
theorem B1400057 : Blo 932582 1400057 := bstep (se 2 (by rfl) ⟨525021, by rfl⟩ : syracuseStep 1400057 = 1050043) B1050043
theorem B1400159 : Blo 932582 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B1400171 : Blo 932582 1400171 := bstep (se 1 (by rfl) ⟨1050128, by rfl⟩ : syracuseStep 1400171 = 2100257) B2100257
theorem B1400399 : Blo 932582 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B1400519 : Blo 932582 1400519 := bstep (se 1 (by rfl) ⟨1050389, by rfl⟩ : syracuseStep 1400519 = 2100779) B2100779
theorem B3792683 : Blo 932582 3792683 := bstep (se 1 (by rfl) ⟨2844512, by rfl⟩ : syracuseStep 3792683 = 5689025) B5689025
theorem B1400681 : Blo 932582 1400681 := bstep (se 2 (by rfl) ⟨525255, by rfl⟩ : syracuseStep 1400681 = 1050511) B1050511
theorem B1892279 : Blo 932582 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B1400759 : Blo 932582 1400759 := bstep (se 1 (by rfl) ⟨1050569, by rfl⟩ : syracuseStep 1400759 = 2101139) B2101139
theorem B1400795 : Blo 932582 1400795 := bstep (se 1 (by rfl) ⟨1050596, by rfl⟩ : syracuseStep 1400795 = 2101193) B2101193
theorem B5332999 : Blo 932582 5332999 := bstep (se 1 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 5332999 = 7999499) B7999499
theorem B1401263 : Blo 932582 1401263 := bstep (se 1 (by rfl) ⟨1050947, by rfl⟩ : syracuseStep 1401263 = 2101895) B2101895
theorem B1401353 : Blo 932582 1401353 := bstep (se 2 (by rfl) ⟨525507, by rfl⟩ : syracuseStep 1401353 = 1051015) B1051015
theorem B1401383 : Blo 932582 1401383 := bstep (se 1 (by rfl) ⟨1051037, by rfl⟩ : syracuseStep 1401383 = 2102075) B2102075
theorem B1401467 : Blo 932582 1401467 := bstep (se 1 (by rfl) ⟨1051100, by rfl⟩ : syracuseStep 1401467 = 2102201) B2102201
theorem B1401593 : Blo 932582 1401593 := bstep (se 2 (by rfl) ⟨525597, by rfl⟩ : syracuseStep 1401593 = 1051195) B1051195
theorem B1401695 : Blo 932582 1401695 := bstep (se 1 (by rfl) ⟨1051271, by rfl⟩ : syracuseStep 1401695 = 2102543) B2102543
theorem B1401707 : Blo 932582 1401707 := bstep (se 1 (by rfl) ⟨1051280, by rfl⟩ : syracuseStep 1401707 = 2102561) B2102561
theorem B3990455 : Blo 932582 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B7988291 : Blo 932582 7988291 := bstep (se 1 (by rfl) ⟨5991218, by rfl⟩ : syracuseStep 7988291 = 11982437) B11982437
theorem B1401935 : Blo 932582 1401935 := bstep (se 1 (by rfl) ⟨1051451, by rfl⟩ : syracuseStep 1401935 = 2102903) B2102903
theorem B1402055 : Blo 932582 1402055 := bstep (se 1 (by rfl) ⟨1051541, by rfl⟩ : syracuseStep 1402055 = 2103083) B2103083
theorem B1402217 : Blo 932582 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B6743411 : Blo 932582 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B1402295 : Blo 932582 1402295 := bstep (se 1 (by rfl) ⟨1051721, by rfl⟩ : syracuseStep 1402295 = 2103443) B2103443
theorem B1402331 : Blo 932582 1402331 := bstep (se 1 (by rfl) ⟨1051748, by rfl⟩ : syracuseStep 1402331 = 2103497) B2103497
theorem B1992289 : Blo 932582 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B1402799 : Blo 932582 1402799 := bstep (se 1 (by rfl) ⟨1052099, by rfl⟩ : syracuseStep 1402799 = 2104199) B2104199
theorem B1402889 : Blo 932582 1402889 := bstep (se 2 (by rfl) ⟨526083, by rfl⟩ : syracuseStep 1402889 = 1052167) B1052167
theorem B1402919 : Blo 932582 1402919 := bstep (se 1 (by rfl) ⟨1052189, by rfl⟩ : syracuseStep 1402919 = 2104379) B2104379
theorem B1403003 : Blo 932582 1403003 := bstep (se 1 (by rfl) ⟨1052252, by rfl⟩ : syracuseStep 1403003 = 2104505) B2104505
theorem B1403129 : Blo 932582 1403129 := bstep (se 2 (by rfl) ⟨526173, by rfl⟩ : syracuseStep 1403129 = 1052347) B1052347
theorem B1403231 : Blo 932582 1403231 := bstep (se 1 (by rfl) ⟨1052423, by rfl⟩ : syracuseStep 1403231 = 2104847) B2104847
theorem B1403243 : Blo 932582 1403243 := bstep (se 1 (by rfl) ⟨1052432, by rfl⟩ : syracuseStep 1403243 = 2104865) B2104865
theorem B26896819 : Blo 932582 26896819 := bstep (se 1 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 26896819 = 40345229) B40345229
theorem B1403471 : Blo 932582 1403471 := bstep (se 1 (by rfl) ⟨1052603, by rfl⟩ : syracuseStep 1403471 = 2105207) B2105207
theorem B1403591 : Blo 932582 1403591 := bstep (se 1 (by rfl) ⟨1052693, by rfl⟩ : syracuseStep 1403591 = 2105387) B2105387
theorem B35941157 : Blo 932582 35941157 := bstep (se 4 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 35941157 = 6738967) B6738967
theorem B1403753 : Blo 932582 1403753 := bstep (se 2 (by rfl) ⟨526407, by rfl⟩ : syracuseStep 1403753 = 1052815) B1052815
theorem B1403831 : Blo 932582 1403831 := bstep (se 1 (by rfl) ⟨1052873, by rfl⟩ : syracuseStep 1403831 = 2105747) B2105747
theorem B1403867 : Blo 932582 1403867 := bstep (se 1 (by rfl) ⟨1052900, by rfl⟩ : syracuseStep 1403867 = 2105801) B2105801
theorem B4484267 : Blo 932582 4484267 := bstep (se 1 (by rfl) ⟨3363200, by rfl⟩ : syracuseStep 4484267 = 6726401) B6726401
theorem B7204211 : Blo 932582 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B43249031 : Blo 932582 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B1404335 : Blo 932582 1404335 := bstep (se 1 (by rfl) ⟨1053251, by rfl⟩ : syracuseStep 1404335 = 2106503) B2106503
theorem B1404425 : Blo 932582 1404425 := bstep (se 2 (by rfl) ⟨526659, by rfl⟩ : syracuseStep 1404425 = 1053319) B1053319
theorem B1404455 : Blo 932582 1404455 := bstep (se 1 (by rfl) ⟨1053341, by rfl⟩ : syracuseStep 1404455 = 2106683) B2106683
theorem B1404539 : Blo 932582 1404539 := bstep (se 1 (by rfl) ⟨1053404, by rfl⟩ : syracuseStep 1404539 = 2106809) B2106809
theorem B1404665 : Blo 932582 1404665 := bstep (se 2 (by rfl) ⟨526749, by rfl⟩ : syracuseStep 1404665 = 1053499) B1053499
theorem B1404767 : Blo 932582 1404767 := bstep (se 1 (by rfl) ⟨1053575, by rfl⟩ : syracuseStep 1404767 = 2107151) B2107151
theorem B1404779 : Blo 932582 1404779 := bstep (se 1 (by rfl) ⟨1053584, by rfl⟩ : syracuseStep 1404779 = 2107169) B2107169
theorem B3601043 : Blo 932582 3601043 := bstep (se 1 (by rfl) ⟨2700782, by rfl⟩ : syracuseStep 3601043 = 5401565) B5401565
theorem B6747101 : Blo 932582 6747101 := bstep (se 3 (by rfl) ⟨1265081, by rfl⟩ : syracuseStep 6747101 = 2530163) B2530163
theorem B6059659 : Blo 932582 6059659 := bstep (se 1 (by rfl) ⟨4544744, by rfl⟩ : syracuseStep 6059659 = 9089489) B9089489
theorem B7108235 : Blo 932582 7108235 := bstep (se 1 (by rfl) ⟨5331176, by rfl⟩ : syracuseStep 7108235 = 10662353) B10662353
theorem B30275531 : Blo 932582 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B5994499 : Blo 932582 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B9599077 : Blo 932582 9599077 := bstep (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) B1799827
theorem B15169943 : Blo 932582 15169943 := bstep (se 1 (by rfl) ⟨11377457, by rfl⟩ : syracuseStep 15169943 = 22754915) B22754915
theorem B7666073 : Blo 932582 7666073 := bstep (se 2 (by rfl) ⟨2874777, by rfl⟩ : syracuseStep 7666073 = 5749555) B5749555
theorem B3603041 : Blo 932582 3603041 := bstep (se 2 (by rfl) ⟨1351140, by rfl⟩ : syracuseStep 3603041 = 2702281) B2702281
theorem B2128823 : Blo 932582 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B2522269 : Blo 932582 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B6225295 : Blo 932582 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B30768569 : Blo 932582 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B2129771 : Blo 932582 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B3243959 : Blo 932582 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B7110665 : Blo 932582 7110665 := bstep (se 2 (by rfl) ⟨2666499, by rfl⟩ : syracuseStep 7110665 = 5332999) B5332999
theorem B1704041 : Blo 932582 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B4260601 : Blo 932582 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B5997473 : Blo 932582 5997473 := bstep (se 2 (by rfl) ⟨2249052, by rfl⟩ : syracuseStep 5997473 = 4498105) B4498105
theorem B1049575 : Blo 932582 1049575 := bstep (se 1 (by rfl) ⟨787181, by rfl⟩ : syracuseStep 1049575 = 1574363) B1574363
theorem B14583077 : Blo 932582 14583077 := bstep (se 4 (by rfl) ⟨1367163, by rfl⟩ : syracuseStep 14583077 = 2734327) B2734327
theorem B5768491 : Blo 932582 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B20186455 : Blo 932582 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B2098529 : Blo 932582 2098529 := bstep (se 2 (by rfl) ⟨786948, by rfl⟩ : syracuseStep 2098529 = 1573897) B1573897
theorem B2000251 : Blo 932582 2000251 := bstep (se 1 (by rfl) ⟨1500188, by rfl⟩ : syracuseStep 2000251 = 3000377) B3000377
theorem B18220439 : Blo 932582 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B2098619 : Blo 932582 2098619 := bstep (se 1 (by rfl) ⟨1573964, by rfl⟩ : syracuseStep 2098619 = 3147929) B3147929
theorem B3999239 : Blo 932582 3999239 := bstep (se 1 (by rfl) ⟨2999429, by rfl⟩ : syracuseStep 3999239 = 5998859) B5998859
theorem B2098745 : Blo 932582 2098745 := bstep (se 2 (by rfl) ⟨787029, by rfl⟩ : syracuseStep 2098745 = 1574059) B1574059
theorem B2360927 : Blo 932582 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B2656385 : Blo 932582 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B2099411 : Blo 932582 2099411 := bstep (se 1 (by rfl) ⟨1574558, by rfl⟩ : syracuseStep 2099411 = 3149117) B3149117
theorem B2099465 : Blo 932582 2099465 := bstep (se 2 (by rfl) ⟨787299, by rfl⟩ : syracuseStep 2099465 = 1574599) B1574599
theorem B1182043 : Blo 932582 1182043 := bstep (se 1 (by rfl) ⟨886532, by rfl⟩ : syracuseStep 1182043 = 1773065) B1773065
theorem B2361707 : Blo 932582 2361707 := bstep (se 1 (by rfl) ⟨1771280, by rfl⟩ : syracuseStep 2361707 = 3542561) B3542561
theorem B3148199 : Blo 932582 3148199 := bstep (se 1 (by rfl) ⟨2361149, by rfl⟩ : syracuseStep 3148199 = 4722299) B4722299
theorem B1575335 : Blo 932582 1575335 := bstep (se 1 (by rfl) ⟨1181501, by rfl⟩ : syracuseStep 1575335 = 2363003) B2363003
theorem B11995559 : Blo 932582 11995559 := bstep (se 1 (by rfl) ⟨8996669, by rfl⟩ : syracuseStep 11995559 = 17993339) B17993339
theorem B2099681 : Blo 932582 2099681 := bstep (se 2 (by rfl) ⟨787380, by rfl⟩ : syracuseStep 2099681 = 1574761) B1574761
theorem B2361919 : Blo 932582 2361919 := bstep (se 1 (by rfl) ⟨1771439, by rfl⟩ : syracuseStep 2361919 = 3542879) B3542879
theorem B1182271 : Blo 932582 1182271 := bstep (se 1 (by rfl) ⟨886703, by rfl⟩ : syracuseStep 1182271 = 1773407) B1773407
theorem B3148361 : Blo 932582 3148361 := bstep (se 2 (by rfl) ⟨1180635, by rfl⟩ : syracuseStep 3148361 = 2361271) B2361271
theorem B1575497 : Blo 932582 1575497 := bstep (se 2 (by rfl) ⟨590811, by rfl⟩ : syracuseStep 1575497 = 1181623) B1181623
theorem B1051231 : Blo 932582 1051231 := bstep (se 1 (by rfl) ⟨788423, by rfl⟩ : syracuseStep 1051231 = 1576847) B1576847
theorem B4721327 : Blo 932582 4721327 := bstep (se 1 (by rfl) ⟨3540995, by rfl⟩ : syracuseStep 4721327 = 7081991) B7081991
theorem B2362031 : Blo 932582 2362031 := bstep (se 1 (by rfl) ⟨1771523, by rfl⟩ : syracuseStep 2362031 = 3543047) B3543047
theorem B2099987 : Blo 932582 2099987 := bstep (se 1 (by rfl) ⟨1574990, by rfl⟩ : syracuseStep 2099987 = 3149981) B3149981
theorem B5311403 : Blo 932582 5311403 := bstep (se 1 (by rfl) ⟨3983552, by rfl⟩ : syracuseStep 5311403 = 7967105) B7967105
theorem B2657195 : Blo 932582 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B4721651 : Blo 932582 4721651 := bstep (se 1 (by rfl) ⟨3541238, by rfl⟩ : syracuseStep 4721651 = 7082477) B7082477
theorem B2362355 : Blo 932582 2362355 := bstep (se 1 (by rfl) ⟨1771766, by rfl⟩ : syracuseStep 2362355 = 3543533) B3543533
theorem B2100347 : Blo 932582 2100347 := bstep (se 1 (by rfl) ⟨1575260, by rfl⟩ : syracuseStep 2100347 = 3150521) B3150521
theorem B2362567 : Blo 932582 2362567 := bstep (se 1 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 2362567 = 3543851) B3543851
theorem B2100473 : Blo 932582 2100473 := bstep (se 2 (by rfl) ⟨787677, by rfl⟩ : syracuseStep 2100473 = 1575355) B1575355
theorem B1183015 : Blo 932582 1183015 := bstep (se 1 (by rfl) ⟨887261, by rfl⟩ : syracuseStep 1183015 = 1774523) B1774523
theorem B5999933 : Blo 932582 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B2100617 : Blo 932582 2100617 := bstep (se 2 (by rfl) ⟨787731, by rfl⟩ : syracuseStep 2100617 = 1575463) B1575463
theorem B2100743 : Blo 932582 2100743 := bstep (se 1 (by rfl) ⟨1575557, by rfl⟩ : syracuseStep 2100743 = 3151115) B3151115
theorem B1576543 : Blo 932582 1576543 := bstep (se 1 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 1576543 = 2364815) B2364815
theorem B1183339 : Blo 932582 1183339 := bstep (se 1 (by rfl) ⟨887504, by rfl⟩ : syracuseStep 1183339 = 1775009) B1775009
theorem B22744709 : Blo 932582 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B2100923 : Blo 932582 2100923 := bstep (se 1 (by rfl) ⟨1575692, by rfl⟩ : syracuseStep 2100923 = 3151385) B3151385
theorem B8982215 : Blo 932582 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B1052383 : Blo 932582 1052383 := bstep (se 1 (by rfl) ⟨789287, by rfl⟩ : syracuseStep 1052383 = 1578575) B1578575
theorem B1773353 : Blo 932582 1773353 := bstep (se 2 (by rfl) ⟨665007, by rfl⟩ : syracuseStep 1773353 = 1330015) B1330015
theorem B1576759 : Blo 932582 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B2101049 : Blo 932582 2101049 := bstep (se 2 (by rfl) ⟨787893, by rfl⟩ : syracuseStep 2101049 = 1575787) B1575787
theorem B655789891 : Blo 932582 655789891 := bstep (se 1 (by rfl) ⟨491842418, by rfl⟩ : syracuseStep 655789891 = 983684837) B983684837
theorem B1183567 : Blo 932582 1183567 := bstep (se 1 (by rfl) ⟨887675, by rfl⟩ : syracuseStep 1183567 = 1775351) B1775351
theorem B8654849 : Blo 932582 8654849 := bstep (se 2 (by rfl) ⟨3245568, by rfl⟩ : syracuseStep 8654849 = 6491137) B6491137
theorem B3150035 : Blo 932582 3150035 := bstep (se 1 (by rfl) ⟨2362526, by rfl⟩ : syracuseStep 3150035 = 4725053) B4725053
theorem B4722947 : Blo 932582 4722947 := bstep (se 1 (by rfl) ⟨3542210, by rfl⟩ : syracuseStep 4722947 = 7084421) B7084421
theorem B1577225 : Blo 932582 1577225 := bstep (se 2 (by rfl) ⟨591459, by rfl⟩ : syracuseStep 1577225 = 1182919) B1182919
theorem B1052959 : Blo 932582 1052959 := bstep (se 1 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 1052959 = 1579439) B1579439
theorem B1773991 : Blo 932582 1773991 := bstep (se 1 (by rfl) ⟨1330493, by rfl⟩ : syracuseStep 1773991 = 2660987) B2660987
theorem B2101679 : Blo 932582 2101679 := bstep (se 1 (by rfl) ⟨1576259, by rfl⟩ : syracuseStep 2101679 = 3152519) B3152519
theorem B2101715 : Blo 932582 2101715 := bstep (se 1 (by rfl) ⟨1576286, by rfl⟩ : syracuseStep 2101715 = 3152573) B3152573
theorem B3150305 : Blo 932582 3150305 := bstep (se 2 (by rfl) ⟨1181364, by rfl⟩ : syracuseStep 3150305 = 2362729) B2362729
theorem B1774075 : Blo 932582 1774075 := bstep (se 1 (by rfl) ⟨1330556, by rfl⟩ : syracuseStep 1774075 = 2661113) B2661113
theorem B4493875 : Blo 932582 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B2101823 : Blo 932582 2101823 := bstep (se 1 (by rfl) ⟨1576367, by rfl⟩ : syracuseStep 2101823 = 3152735) B3152735
theorem B1708607 : Blo 932582 1708607 := bstep (se 1 (by rfl) ⟨1281455, by rfl⟩ : syracuseStep 1708607 = 2562911) B2562911
theorem B1053247 : Blo 932582 1053247 := bstep (se 1 (by rfl) ⟨789935, by rfl⟩ : syracuseStep 1053247 = 1579871) B1579871
theorem B4723271 : Blo 932582 4723271 := bstep (se 1 (by rfl) ⟨3542453, by rfl⟩ : syracuseStep 4723271 = 7084907) B7084907
theorem B2363975 : Blo 932582 2363975 := bstep (se 1 (by rfl) ⟨1772981, by rfl⟩ : syracuseStep 2363975 = 3545963) B3545963
theorem B2364025 : Blo 932582 2364025 := bstep (se 2 (by rfl) ⟨886509, by rfl⟩ : syracuseStep 2364025 = 1773019) B1773019
theorem B2101931 : Blo 932582 2101931 := bstep (se 1 (by rfl) ⟨1576448, by rfl⟩ : syracuseStep 2101931 = 3152897) B3152897
theorem B2102471 : Blo 932582 2102471 := bstep (se 1 (by rfl) ⟨1576853, by rfl⟩ : syracuseStep 2102471 = 3153707) B3153707
theorem B2528455 : Blo 932582 2528455 := bstep (se 1 (by rfl) ⟨1896341, by rfl⟩ : syracuseStep 2528455 = 3792683) B3792683
theorem B1774811 : Blo 932582 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B1578217 : Blo 932582 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B3544307 : Blo 932582 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B8983831 : Blo 932582 8983831 := bstep (se 1 (by rfl) ⟨6737873, by rfl⟩ : syracuseStep 8983831 = 13475747) B13475747
theorem B1578271 : Blo 932582 1578271 := bstep (se 1 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 1578271 = 2367407) B2367407
theorem B2102651 : Blo 932582 2102651 := bstep (se 1 (by rfl) ⟨1576988, by rfl⟩ : syracuseStep 2102651 = 3153977) B3153977
theorem B1775047 : Blo 932582 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B2102777 : Blo 932582 2102777 := bstep (se 2 (by rfl) ⟨788541, by rfl⟩ : syracuseStep 2102777 = 1577083) B1577083
theorem B2102867 : Blo 932582 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B3151547 : Blo 932582 3151547 := bstep (se 1 (by rfl) ⟨2363660, by rfl⟩ : syracuseStep 3151547 = 4727321) B4727321
theorem B1578683 : Blo 932582 1578683 := bstep (se 1 (by rfl) ⟨1184012, by rfl⟩ : syracuseStep 1578683 = 2368025) B2368025
theorem B2103047 : Blo 932582 2103047 := bstep (se 1 (by rfl) ⟨1577285, by rfl⟩ : syracuseStep 2103047 = 3154571) B3154571
theorem B4724567 : Blo 932582 4724567 := bstep (se 1 (by rfl) ⟨3543425, by rfl⟩ : syracuseStep 4724567 = 7086851) B7086851
theorem B2660303 : Blo 932582 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B4495607 : Blo 932582 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B2365787 : Blo 932582 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B2103659 : Blo 932582 2103659 := bstep (se 1 (by rfl) ⟨1577744, by rfl⟩ : syracuseStep 2103659 = 3155489) B3155489
theorem B2365807 : Blo 932582 2365807 := bstep (se 1 (by rfl) ⟨1774355, by rfl⟩ : syracuseStep 2365807 = 3548711) B3548711
theorem B2103803 : Blo 932582 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B2103929 : Blo 932582 2103929 := bstep (se 2 (by rfl) ⟨788973, by rfl⟩ : syracuseStep 2103929 = 1577947) B1577947
theorem B2103983 : Blo 932582 2103983 := bstep (se 1 (by rfl) ⟨1577987, by rfl⟩ : syracuseStep 2103983 = 3155975) B3155975
theorem B3545795 : Blo 932582 3545795 := bstep (se 1 (by rfl) ⟨2659346, by rfl⟩ : syracuseStep 3545795 = 5318693) B5318693
theorem B2104055 : Blo 932582 2104055 := bstep (se 1 (by rfl) ⟨1578041, by rfl⟩ : syracuseStep 2104055 = 3156083) B3156083
theorem B2104235 : Blo 932582 2104235 := bstep (se 1 (by rfl) ⟨1578176, by rfl⟩ : syracuseStep 2104235 = 3156353) B3156353
theorem B2366455 : Blo 932582 2366455 := bstep (se 1 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 2366455 = 3549683) B3549683
theorem B3546251 : Blo 932582 3546251 := bstep (se 1 (by rfl) ⟨2659688, by rfl⟩ : syracuseStep 3546251 = 5319377) B5319377
theorem B23960771 : Blo 932582 23960771 := bstep (se 1 (by rfl) ⟨17970578, by rfl⟩ : syracuseStep 23960771 = 35941157) B35941157
theorem B2366759 : Blo 932582 2366759 := bstep (se 1 (by rfl) ⟨1775069, by rfl⟩ : syracuseStep 2366759 = 3550139) B3550139
theorem B1580411 : Blo 932582 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B2989511 : Blo 932582 2989511 := bstep (se 1 (by rfl) ⟨2242133, by rfl⟩ : syracuseStep 2989511 = 4484267) B4484267
theorem B1121735 : Blo 932582 1121735 := bstep (se 1 (by rfl) ⟨841301, by rfl⟩ : syracuseStep 1121735 = 1682603) B1682603
theorem B2104775 : Blo 932582 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B2989561 : Blo 932582 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B3153491 : Blo 932582 3153491 := bstep (se 1 (by rfl) ⟨2365118, by rfl⟩ : syracuseStep 3153491 = 4730237) B4730237
theorem B2105135 : Blo 932582 2105135 := bstep (se 1 (by rfl) ⟨1578851, by rfl⟩ : syracuseStep 2105135 = 3157703) B3157703
theorem B4726835 : Blo 932582 4726835 := bstep (se 1 (by rfl) ⟨3545126, by rfl⟩ : syracuseStep 4726835 = 7090253) B7090253
theorem B2105711 : Blo 932582 2105711 := bstep (se 1 (by rfl) ⟨1579283, by rfl⟩ : syracuseStep 2105711 = 3158567) B3158567
theorem B2400695 : Blo 932582 2400695 := bstep (se 1 (by rfl) ⟨1800521, by rfl⟩ : syracuseStep 2400695 = 3601043) B3601043
theorem B2105783 : Blo 932582 2105783 := bstep (se 1 (by rfl) ⟨1579337, by rfl⟩ : syracuseStep 2105783 = 3158675) B3158675
theorem B2105927 : Blo 932582 2105927 := bstep (se 1 (by rfl) ⟨1579445, by rfl⟩ : syracuseStep 2105927 = 3158891) B3158891
theorem B2105963 : Blo 932582 2105963 := bstep (se 1 (by rfl) ⟨1579472, by rfl⟩ : syracuseStep 2105963 = 3158945) B3158945
theorem B4498067 : Blo 932582 4498067 := bstep (se 1 (by rfl) ⟨3373550, by rfl⟩ : syracuseStep 4498067 = 6747101) B6747101
theorem B2368399 : Blo 932582 2368399 := bstep (se 1 (by rfl) ⟨1776299, by rfl⟩ : syracuseStep 2368399 = 3552599) B3552599
theorem B2106359 : Blo 932582 2106359 := bstep (se 1 (by rfl) ⟨1579769, by rfl⟩ : syracuseStep 2106359 = 3159539) B3159539
theorem B4039913 : Blo 932582 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B7087337 : Blo 932582 7087337 := bstep (se 2 (by rfl) ⟨2657751, by rfl⟩ : syracuseStep 7087337 = 5315503) B5315503
theorem B3548393 : Blo 932582 3548393 := bstep (se 2 (by rfl) ⟨1330647, by rfl⟩ : syracuseStep 3548393 = 2661295) B2661295
theorem B2106719 : Blo 932582 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B2368865 : Blo 932582 2368865 := bstep (se 2 (by rfl) ⟨888324, by rfl⟩ : syracuseStep 2368865 = 1776649) B1776649
theorem B4728455 : Blo 932582 4728455 := bstep (se 1 (by rfl) ⟨3546341, by rfl⟩ : syracuseStep 4728455 = 7092683) B7092683
theorem B2402027 : Blo 932582 2402027 := bstep (se 1 (by rfl) ⟨1801520, by rfl⟩ : syracuseStep 2402027 = 3603041) B3603041
theorem B2107115 : Blo 932582 2107115 := bstep (se 1 (by rfl) ⟨1580336, by rfl⟩ : syracuseStep 2107115 = 3160673) B3160673
theorem B2369321 : Blo 932582 2369321 := bstep (se 2 (by rfl) ⟨888495, by rfl⟩ : syracuseStep 2369321 = 1776991) B1776991
theorem B8300393 : Blo 932582 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B2107241 : Blo 932582 2107241 := bstep (se 2 (by rfl) ⟨790215, by rfl⟩ : syracuseStep 2107241 = 1580431) B1580431
theorem B1419215 : Blo 932582 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B2664701 : Blo 932582 2664701 := bstep (se 3 (by rfl) ⟨499631, by rfl⟩ : syracuseStep 2664701 = 999263) B999263
theorem B5679389 : Blo 932582 5679389 := bstep (se 3 (by rfl) ⟨1064885, by rfl⟩ : syracuseStep 5679389 = 2129771) B2129771
theorem B14035235 : Blo 932582 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B1124699 : Blo 932582 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B3156407 : Blo 932582 3156407 := bstep (se 1 (by rfl) ⟨2367305, by rfl⟩ : syracuseStep 3156407 = 4734611) B4734611
theorem B2370323 : Blo 932582 2370323 := bstep (se 1 (by rfl) ⟨1777742, by rfl⟩ : syracuseStep 2370323 = 3555485) B3555485
theorem B14396291 : Blo 932582 14396291 := bstep (se 1 (by rfl) ⟨10797218, by rfl⟩ : syracuseStep 14396291 = 21594437) B21594437
theorem B1682407 : Blo 932582 1682407 := bstep (se 1 (by rfl) ⟨1261805, by rfl⟩ : syracuseStep 1682407 = 2523611) B2523611
theorem B5319695 : Blo 932582 5319695 := bstep (se 1 (by rfl) ⟨3989771, by rfl⟩ : syracuseStep 5319695 = 7979543) B7979543
theorem B4730075 : Blo 932582 4730075 := bstep (se 1 (by rfl) ⟨3547556, by rfl⟩ : syracuseStep 4730075 = 7095113) B7095113
theorem B2665943 : Blo 932582 2665943 := bstep (se 1 (by rfl) ⟨1999457, by rfl⟩ : syracuseStep 2665943 = 3998915) B3998915
theorem B15380077 : Blo 932582 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B5320403 : Blo 932582 5320403 := bstep (se 1 (by rfl) ⟨3990302, by rfl⟩ : syracuseStep 5320403 = 7980605) B7980605
theorem B7975169 : Blo 932582 7975169 := bstep (se 2 (by rfl) ⟨2990688, by rfl⟩ : syracuseStep 7975169 = 5981377) B5981377
theorem B4731209 : Blo 932582 4731209 := bstep (se 2 (by rfl) ⟨1774203, by rfl⟩ : syracuseStep 4731209 = 3548407) B3548407
theorem B7090739 : Blo 932582 7090739 := bstep (se 1 (by rfl) ⟨5318054, by rfl⟩ : syracuseStep 7090739 = 10636109) B10636109
theorem B996175 : Blo 932582 996175 := bstep (se 1 (by rfl) ⟨747131, by rfl⟩ : syracuseStep 996175 = 1494263) B1494263
theorem B3781847 : Blo 932582 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B7976231 : Blo 932582 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B3159485 : Blo 932582 3159485 := bstep (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) B1184807
theorem B1422841 : Blo 932582 1422841 := bstep (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) B1067131
theorem B4732505 : Blo 932582 4732505 := bstep (se 2 (by rfl) ⟨1774689, by rfl⟩ : syracuseStep 4732505 = 3549379) B3549379
theorem B3159863 : Blo 932582 3159863 := bstep (se 1 (by rfl) ⟨2369897, by rfl⟩ : syracuseStep 3159863 = 4739795) B4739795
theorem B35862425 : Blo 932582 35862425 := bstep (se 2 (by rfl) ⟨13448409, by rfl⟩ : syracuseStep 35862425 = 26896819) B26896819
theorem B7092197 : Blo 932582 7092197 := bstep (se 4 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 7092197 = 1329787) B1329787
theorem B6731819 : Blo 932582 6731819 := bstep (se 1 (by rfl) ⟨5048864, by rfl⟩ : syracuseStep 6731819 = 10097729) B10097729
theorem B3160349 : Blo 932582 3160349 := bstep (se 3 (by rfl) ⟨592565, by rfl⟩ : syracuseStep 3160349 = 1185131) B1185131
theorem B932655 : Blo 932582 932655 := bstep (se 1 (by rfl) ⟨699491, by rfl⟩ : syracuseStep 932655 = 1398983) B1398983
theorem B998191 : Blo 932582 998191 := bstep (se 1 (by rfl) ⟨748643, by rfl⟩ : syracuseStep 998191 = 1497287) B1497287
theorem B932763 : Blo 932582 932763 := bstep (se 1 (by rfl) ⟨699572, by rfl⟩ : syracuseStep 932763 = 1399145) B1399145
theorem B932815 : Blo 932582 932815 := bstep (se 1 (by rfl) ⟨699611, by rfl⟩ : syracuseStep 932815 = 1399223) B1399223
theorem B932839 : Blo 932582 932839 := bstep (se 1 (by rfl) ⟨699629, by rfl⟩ : syracuseStep 932839 = 1399259) B1399259
theorem B933151 : Blo 932582 933151 := bstep (se 1 (by rfl) ⟨699863, by rfl⟩ : syracuseStep 933151 = 1399727) B1399727
theorem B933211 : Blo 932582 933211 := bstep (se 1 (by rfl) ⟨699908, by rfl⟩ : syracuseStep 933211 = 1399817) B1399817
theorem B933231 : Blo 932582 933231 := bstep (se 1 (by rfl) ⟨699923, by rfl⟩ : syracuseStep 933231 = 1399847) B1399847
theorem B933287 : Blo 932582 933287 := bstep (se 1 (by rfl) ⟨699965, by rfl⟩ : syracuseStep 933287 = 1399931) B1399931
theorem B933371 : Blo 932582 933371 := bstep (se 1 (by rfl) ⟨700028, by rfl⟩ : syracuseStep 933371 = 1400057) B1400057
theorem B933439 : Blo 932582 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B933447 : Blo 932582 933447 := bstep (se 1 (by rfl) ⟨700085, by rfl⟩ : syracuseStep 933447 = 1400171) B1400171
theorem B933599 : Blo 932582 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B933679 : Blo 932582 933679 := bstep (se 1 (by rfl) ⟨700259, by rfl⟩ : syracuseStep 933679 = 1400519) B1400519
theorem B933787 : Blo 932582 933787 := bstep (se 1 (by rfl) ⟨700340, by rfl⟩ : syracuseStep 933787 = 1400681) B1400681
theorem B933839 : Blo 932582 933839 := bstep (se 1 (by rfl) ⟨700379, by rfl⟩ : syracuseStep 933839 = 1400759) B1400759
theorem B933863 : Blo 932582 933863 := bstep (se 1 (by rfl) ⟨700397, by rfl⟩ : syracuseStep 933863 = 1400795) B1400795
theorem B934175 : Blo 932582 934175 := bstep (se 1 (by rfl) ⟨700631, by rfl⟩ : syracuseStep 934175 = 1401263) B1401263
theorem B934235 : Blo 932582 934235 := bstep (se 1 (by rfl) ⟨700676, by rfl⟩ : syracuseStep 934235 = 1401353) B1401353
theorem B934255 : Blo 932582 934255 := bstep (se 1 (by rfl) ⟨700691, by rfl⟩ : syracuseStep 934255 = 1401383) B1401383
theorem B934311 : Blo 932582 934311 := bstep (se 1 (by rfl) ⟨700733, by rfl⟩ : syracuseStep 934311 = 1401467) B1401467
theorem B934395 : Blo 932582 934395 := bstep (se 1 (by rfl) ⟨700796, by rfl⟩ : syracuseStep 934395 = 1401593) B1401593
theorem B934463 : Blo 932582 934463 := bstep (se 1 (by rfl) ⟨700847, by rfl⟩ : syracuseStep 934463 = 1401695) B1401695
theorem B3785287 : Blo 932582 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B934471 : Blo 932582 934471 := bstep (se 1 (by rfl) ⟨700853, by rfl⟩ : syracuseStep 934471 = 1401707) B1401707
theorem B5325527 : Blo 932582 5325527 := bstep (se 1 (by rfl) ⟨3994145, by rfl⟩ : syracuseStep 5325527 = 7988291) B7988291
theorem B934623 : Blo 932582 934623 := bstep (se 1 (by rfl) ⟨700967, by rfl⟩ : syracuseStep 934623 = 1401935) B1401935
theorem B934703 : Blo 932582 934703 := bstep (se 1 (by rfl) ⟨701027, by rfl⟩ : syracuseStep 934703 = 1402055) B1402055
theorem B13452101 : Blo 932582 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B934811 : Blo 932582 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B5129153 : Blo 932582 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B934863 : Blo 932582 934863 := bstep (se 1 (by rfl) ⟨701147, by rfl⟩ : syracuseStep 934863 = 1402295) B1402295
theorem B934887 : Blo 932582 934887 := bstep (se 1 (by rfl) ⟨701165, by rfl⟩ : syracuseStep 934887 = 1402331) B1402331
theorem B40453181 : Blo 932582 40453181 := bstep (se 3 (by rfl) ⟨7584971, by rfl⟩ : syracuseStep 40453181 = 15169943) B15169943
theorem B7980227 : Blo 932582 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B935199 : Blo 932582 935199 := bstep (se 1 (by rfl) ⟨701399, by rfl⟩ : syracuseStep 935199 = 1402799) B1402799
theorem B935259 : Blo 932582 935259 := bstep (se 1 (by rfl) ⟨701444, by rfl⟩ : syracuseStep 935259 = 1402889) B1402889
theorem B935279 : Blo 932582 935279 := bstep (se 1 (by rfl) ⟨701459, by rfl⟩ : syracuseStep 935279 = 1402919) B1402919
theorem B935335 : Blo 932582 935335 := bstep (se 1 (by rfl) ⟨701501, by rfl⟩ : syracuseStep 935335 = 1403003) B1403003
theorem B935419 : Blo 932582 935419 := bstep (se 1 (by rfl) ⟨701564, by rfl⟩ : syracuseStep 935419 = 1403129) B1403129
theorem B935487 : Blo 932582 935487 := bstep (se 1 (by rfl) ⟨701615, by rfl⟩ : syracuseStep 935487 = 1403231) B1403231
theorem B935495 : Blo 932582 935495 := bstep (se 1 (by rfl) ⟨701621, by rfl⟩ : syracuseStep 935495 = 1403243) B1403243
theorem B935647 : Blo 932582 935647 := bstep (se 1 (by rfl) ⟨701735, by rfl⟩ : syracuseStep 935647 = 1403471) B1403471
theorem B935727 : Blo 932582 935727 := bstep (se 1 (by rfl) ⟨701795, by rfl⟩ : syracuseStep 935727 = 1403591) B1403591
theorem B935835 : Blo 932582 935835 := bstep (se 1 (by rfl) ⟨701876, by rfl⟩ : syracuseStep 935835 = 1403753) B1403753
theorem B935887 : Blo 932582 935887 := bstep (se 1 (by rfl) ⟨701915, by rfl⟩ : syracuseStep 935887 = 1403831) B1403831
theorem B6408143 : Blo 932582 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B935911 : Blo 932582 935911 := bstep (se 1 (by rfl) ⟨701933, by rfl⟩ : syracuseStep 935911 = 1403867) B1403867
theorem B8079545 : Blo 932582 8079545 := bstep (se 2 (by rfl) ⟨3029829, by rfl⟩ : syracuseStep 8079545 = 6059659) B6059659
theorem B4802807 : Blo 932582 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B936223 : Blo 932582 936223 := bstep (se 1 (by rfl) ⟨702167, by rfl⟩ : syracuseStep 936223 = 1404335) B1404335
theorem B936283 : Blo 932582 936283 := bstep (se 1 (by rfl) ⟨702212, by rfl⟩ : syracuseStep 936283 = 1404425) B1404425
theorem B936303 : Blo 932582 936303 := bstep (se 1 (by rfl) ⟨702227, by rfl⟩ : syracuseStep 936303 = 1404455) B1404455
theorem B936359 : Blo 932582 936359 := bstep (se 1 (by rfl) ⟨702269, by rfl⟩ : syracuseStep 936359 = 1404539) B1404539
theorem B936443 : Blo 932582 936443 := bstep (se 1 (by rfl) ⟨702332, by rfl⟩ : syracuseStep 936443 = 1404665) B1404665
theorem B936511 : Blo 932582 936511 := bstep (se 1 (by rfl) ⟨702383, by rfl⟩ : syracuseStep 936511 = 1404767) B1404767
theorem B936519 : Blo 932582 936519 := bstep (se 1 (by rfl) ⟨702389, by rfl⟩ : syracuseStep 936519 = 1404779) B1404779
theorem B28756727 : Blo 932582 28756727 := bstep (se 1 (by rfl) ⟨21567545, by rfl⟩ : syracuseStep 28756727 = 43135091) B43135091
theorem B12798769 : Blo 932582 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B2247929 : Blo 932582 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B7098029 : Blo 932582 7098029 := bstep (se 3 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 7098029 = 2661761) B2661761
theorem B3985159 : Blo 932582 3985159 := bstep (se 1 (by rfl) ⟨2988869, by rfl⟩ : syracuseStep 3985159 = 5977739) B5977739
theorem B4738823 : Blo 932582 4738823 := bstep (se 1 (by rfl) ⟨3554117, by rfl⟩ : syracuseStep 4738823 = 7108235) B7108235
theorem B3985193 : Blo 932582 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B2248553 : Blo 932582 2248553 := bstep (se 2 (by rfl) ⟨843207, by rfl⟩ : syracuseStep 2248553 = 1686415) B1686415
theorem B3985433 : Blo 932582 3985433 := bstep (se 2 (by rfl) ⟨1494537, by rfl⟩ : syracuseStep 3985433 = 2989075) B2989075
theorem B7099001 : Blo 932582 7099001 := bstep (se 2 (by rfl) ⟨2662125, by rfl⟩ : syracuseStep 7099001 = 5324251) B5324251
theorem B1496569 : Blo 932582 1496569 := bstep (se 2 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 1496569 = 1122427) B1122427
theorem B1333199 : Blo 932582 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B7100459 : Blo 932582 7100459 := bstep (se 1 (by rfl) ⟨5325344, by rfl⟩ : syracuseStep 7100459 = 10650689) B10650689
theorem B3037313 : Blo 932582 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B1399049 : Blo 932582 1399049 := bstep (se 2 (by rfl) ⟨524643, by rfl⟩ : syracuseStep 1399049 = 1049287) B1049287
theorem B3987721 : Blo 932582 3987721 := bstep (se 2 (by rfl) ⟨1495395, by rfl⟩ : syracuseStep 3987721 = 2990791) B2990791
theorem B1136927 : Blo 932582 1136927 := bstep (se 1 (by rfl) ⟨852695, by rfl⟩ : syracuseStep 1136927 = 1705391) B1705391
theorem B1399151 : Blo 932582 1399151 := bstep (se 1 (by rfl) ⟨1049363, by rfl⟩ : syracuseStep 1399151 = 2098727) B2098727
theorem B5986811 : Blo 932582 5986811 := bstep (se 1 (by rfl) ⟨4490108, by rfl⟩ : syracuseStep 5986811 = 8980217) B8980217
theorem B1399367 : Blo 932582 1399367 := bstep (se 1 (by rfl) ⟨1049525, by rfl⟩ : syracuseStep 1399367 = 2099051) B2099051
theorem B1399403 : Blo 932582 1399403 := bstep (se 1 (by rfl) ⟨1049552, by rfl⟩ : syracuseStep 1399403 = 2099105) B2099105
theorem B1399631 : Blo 932582 1399631 := bstep (se 1 (by rfl) ⟨1049723, by rfl⟩ : syracuseStep 1399631 = 2099447) B2099447
theorem B1400027 : Blo 932582 1400027 := bstep (se 1 (by rfl) ⟨1050020, by rfl⟩ : syracuseStep 1400027 = 2100041) B2100041
theorem B1498331 : Blo 932582 1498331 := bstep (se 1 (by rfl) ⟨1123748, by rfl⟩ : syracuseStep 1498331 = 2247497) B2247497
theorem B17947979 : Blo 932582 17947979 := bstep (se 1 (by rfl) ⟨13460984, by rfl⟩ : syracuseStep 17947979 = 26921969) B26921969
theorem B1400201 : Blo 932582 1400201 := bstep (se 2 (by rfl) ⟨525075, by rfl⟩ : syracuseStep 1400201 = 1050151) B1050151
theorem B3366359 : Blo 932582 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B10116755 : Blo 932582 10116755 := bstep (se 1 (by rfl) ⟨7587566, by rfl⟩ : syracuseStep 10116755 = 15175133) B15175133
theorem B1892027 : Blo 932582 1892027 := bstep (se 1 (by rfl) ⟨1419020, by rfl⟩ : syracuseStep 1892027 = 2838041) B2838041
theorem B1400555 : Blo 932582 1400555 := bstep (se 1 (by rfl) ⟨1050416, by rfl⟩ : syracuseStep 1400555 = 2100833) B2100833
theorem B1498927 : Blo 932582 1498927 := bstep (se 1 (by rfl) ⟨1124195, by rfl⟩ : syracuseStep 1498927 = 2248391) B2248391
theorem B5693257 : Blo 932582 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B1400783 : Blo 932582 1400783 := bstep (se 1 (by rfl) ⟨1050587, by rfl⟩ : syracuseStep 1400783 = 2101175) B2101175
theorem B15982595 : Blo 932582 15982595 := bstep (se 1 (by rfl) ⟨11986946, by rfl⟩ : syracuseStep 15982595 = 23973893) B23973893
theorem B5693651 : Blo 932582 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1401179 : Blo 932582 1401179 := bstep (se 1 (by rfl) ⟨1050884, by rfl⟩ : syracuseStep 1401179 = 2101769) B2101769
theorem B18211331 : Blo 932582 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B1401407 : Blo 932582 1401407 := bstep (se 1 (by rfl) ⟨1051055, by rfl⟩ : syracuseStep 1401407 = 2102111) B2102111
theorem B9101969 : Blo 932582 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B1401527 : Blo 932582 1401527 := bstep (se 1 (by rfl) ⟨1051145, by rfl⟩ : syracuseStep 1401527 = 2102291) B2102291
theorem B3793591 : Blo 932582 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B1401755 : Blo 932582 1401755 := bstep (se 1 (by rfl) ⟨1051316, by rfl⟩ : syracuseStep 1401755 = 2102633) B2102633
theorem B3990491 : Blo 932582 3990491 := bstep (se 1 (by rfl) ⟨2992868, by rfl⟩ : syracuseStep 3990491 = 5985737) B5985737
theorem B1991803 : Blo 932582 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B1991879 : Blo 932582 1991879 := bstep (se 1 (by rfl) ⟨1493909, by rfl⟩ : syracuseStep 1991879 = 2987819) B2987819
theorem B1402151 : Blo 932582 1402151 := bstep (se 1 (by rfl) ⟨1051613, by rfl⟩ : syracuseStep 1402151 = 2103227) B2103227
theorem B1402235 : Blo 932582 1402235 := bstep (se 1 (by rfl) ⟨1051676, by rfl⟩ : syracuseStep 1402235 = 2103353) B2103353
theorem B1402361 : Blo 932582 1402361 := bstep (se 2 (by rfl) ⟨525885, by rfl⟩ : syracuseStep 1402361 = 1051771) B1051771
theorem B1402463 : Blo 932582 1402463 := bstep (se 1 (by rfl) ⟨1051847, by rfl⟩ : syracuseStep 1402463 = 2103695) B2103695
theorem B1402679 : Blo 932582 1402679 := bstep (se 1 (by rfl) ⟨1052009, by rfl⟩ : syracuseStep 1402679 = 2104019) B2104019
theorem B1402985 : Blo 932582 1402985 := bstep (se 2 (by rfl) ⟨526119, by rfl⟩ : syracuseStep 1402985 = 1052239) B1052239
theorem B23947649 : Blo 932582 23947649 := bstep (se 2 (by rfl) ⟨8980368, by rfl⟩ : syracuseStep 23947649 = 17960737) B17960737
theorem B1403303 : Blo 932582 1403303 := bstep (se 1 (by rfl) ⟨1052477, by rfl⟩ : syracuseStep 1403303 = 2104955) B2104955
theorem B1403387 : Blo 932582 1403387 := bstep (se 1 (by rfl) ⟨1052540, by rfl⟩ : syracuseStep 1403387 = 2105081) B2105081
theorem B3238463 : Blo 932582 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B1403513 : Blo 932582 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B1403567 : Blo 932582 1403567 := bstep (se 1 (by rfl) ⟨1052675, by rfl⟩ : syracuseStep 1403567 = 2105351) B2105351
theorem B1403615 : Blo 932582 1403615 := bstep (se 1 (by rfl) ⟨1052711, by rfl⟩ : syracuseStep 1403615 = 2105423) B2105423
theorem B1403879 : Blo 932582 1403879 := bstep (se 1 (by rfl) ⟨1052909, by rfl⟩ : syracuseStep 1403879 = 2105819) B2105819
theorem B1404137 : Blo 932582 1404137 := bstep (se 2 (by rfl) ⟨526551, by rfl⟩ : syracuseStep 1404137 = 1053103) B1053103
theorem B1404191 : Blo 932582 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B1404359 : Blo 932582 1404359 := bstep (se 1 (by rfl) ⟨1053269, by rfl⟩ : syracuseStep 1404359 = 2106539) B2106539
theorem B1994537 : Blo 932582 1994537 := bstep (se 2 (by rfl) ⟨747951, by rfl⟩ : syracuseStep 1994537 = 1495903) B1495903
theorem B1404713 : Blo 932582 1404713 := bstep (se 2 (by rfl) ⟨526767, by rfl⟩ : syracuseStep 1404713 = 1053535) B1053535
theorem B1404719 : Blo 932582 1404719 := bstep (se 1 (by rfl) ⟨1053539, by rfl⟩ : syracuseStep 1404719 = 2107079) B2107079
theorem B1012295 : Blo 932582 1012295 := bstep (se 1 (by rfl) ⟨759221, by rfl⟩ : syracuseStep 1012295 = 1518443) B1518443
theorem B10646315 : Blo 932582 10646315 := bstep (se 1 (by rfl) ⟨7984736, by rfl⟩ : syracuseStep 10646315 = 15969473) B15969473
theorem B28832687 : Blo 932582 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B13464791 : Blo 932582 13464791 := bstep (se 1 (by rfl) ⟨10098593, by rfl⟩ : syracuseStep 13464791 = 20197187) B20197187
theorem B7402745 : Blo 932582 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B7992665 : Blo 932582 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B1997065 : Blo 932582 1997065 := bstep (se 2 (by rfl) ⟨748899, by rfl⟩ : syracuseStep 1997065 = 1497799) B1497799
theorem B2128403 : Blo 932582 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B1800767 : Blo 932582 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B20183687 : Blo 932582 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B1997723 : Blo 932582 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B5110715 : Blo 932582 5110715 := bstep (se 1 (by rfl) ⟨3833036, by rfl⟩ : syracuseStep 5110715 = 7666073) B7666073
theorem B13499621 : Blo 932582 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B3374473 : Blo 932582 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B3374675 : Blo 932582 3374675 := bstep (se 1 (by rfl) ⟨2531006, by rfl⟩ : syracuseStep 3374675 = 5062013) B5062013
theorem B20512379 : Blo 932582 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B122650253 : Blo 932582 122650253 := bstep (se 3 (by rfl) ⟨22996922, by rfl⟩ : syracuseStep 122650253 = 45993845) B45993845
theorem B5046077 : Blo 932582 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B2162639 : Blo 932582 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B3998315 : Blo 932582 3998315 := bstep (se 1 (by rfl) ⟨2998736, by rfl⟩ : syracuseStep 3998315 = 5997473) B5997473
theorem B26968787 : Blo 932582 26968787 := bstep (se 1 (by rfl) ⟨20226590, by rfl⟩ : syracuseStep 26968787 = 40453181) B40453181
theorem B5047049 : Blo 932582 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B1573951 : Blo 932582 1573951 := bstep (se 1 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 1573951 = 2360927) B2360927
theorem B1770923 : Blo 932582 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B2655737 : Blo 932582 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B1574471 : Blo 932582 1574471 := bstep (se 1 (by rfl) ⟨1180853, by rfl⟩ : syracuseStep 1574471 = 2361707) B2361707
theorem B2098799 : Blo 932582 2098799 := bstep (se 1 (by rfl) ⟨1574099, by rfl⟩ : syracuseStep 2098799 = 3148199) B3148199
theorem B1050223 : Blo 932582 1050223 := bstep (se 1 (by rfl) ⟨787667, by rfl⟩ : syracuseStep 1050223 = 1575335) B1575335
theorem B7997039 : Blo 932582 7997039 := bstep (se 1 (by rfl) ⟨5997779, by rfl⟩ : syracuseStep 7997039 = 11995559) B11995559
theorem B2098907 : Blo 932582 2098907 := bstep (se 1 (by rfl) ⟨1574180, by rfl⟩ : syracuseStep 2098907 = 3148361) B3148361
theorem B1050331 : Blo 932582 1050331 := bstep (se 1 (by rfl) ⟨787748, by rfl⟩ : syracuseStep 1050331 = 1575497) B1575497
theorem B3147551 : Blo 932582 3147551 := bstep (se 1 (by rfl) ⟨2360663, by rfl⟩ : syracuseStep 3147551 = 4721327) B4721327
theorem B1574687 : Blo 932582 1574687 := bstep (se 1 (by rfl) ⟨1181015, by rfl⟩ : syracuseStep 1574687 = 2362031) B2362031
theorem B19171151 : Blo 932582 19171151 := bstep (se 1 (by rfl) ⟨14378363, by rfl⟩ : syracuseStep 19171151 = 28756727) B28756727
theorem B3540935 : Blo 932582 3540935 := bstep (se 1 (by rfl) ⟨2655701, by rfl⟩ : syracuseStep 3540935 = 5311403) B5311403
theorem B1771463 : Blo 932582 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B1574903 : Blo 932582 1574903 := bstep (se 1 (by rfl) ⟨1181177, by rfl⟩ : syracuseStep 1574903 = 2362355) B2362355
theorem B3147767 : Blo 932582 3147767 := bstep (se 1 (by rfl) ⟨2360825, by rfl⟩ : syracuseStep 3147767 = 4721651) B4721651
theorem B3999955 : Blo 932582 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B2656795 : Blo 932582 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B5769899 : Blo 932582 5769899 := bstep (se 1 (by rfl) ⟨4327424, by rfl⟩ : syracuseStep 5769899 = 8654849) B8654849
theorem B2656955 : Blo 932582 2656955 := bstep (se 1 (by rfl) ⟨1992716, by rfl⟩ : syracuseStep 2656955 = 3985433) B3985433
theorem B2100023 : Blo 932582 2100023 := bstep (se 1 (by rfl) ⟨1575017, by rfl⟩ : syracuseStep 2100023 = 3150035) B3150035
theorem B3148631 : Blo 932582 3148631 := bstep (se 1 (by rfl) ⟨2361473, by rfl⟩ : syracuseStep 3148631 = 4722947) B4722947
theorem B1051483 : Blo 932582 1051483 := bstep (se 1 (by rfl) ⟨788612, by rfl⟩ : syracuseStep 1051483 = 1577225) B1577225
theorem B2100203 : Blo 932582 2100203 := bstep (se 1 (by rfl) ⟨1575152, by rfl⟩ : syracuseStep 2100203 = 3150305) B3150305
theorem B3148847 : Blo 932582 3148847 := bstep (se 1 (by rfl) ⟨2361635, by rfl⟩ : syracuseStep 3148847 = 4723271) B4723271
theorem B1575983 : Blo 932582 1575983 := bstep (se 1 (by rfl) ⟨1181987, by rfl⟩ : syracuseStep 1575983 = 2363975) B2363975
theorem B1576057 : Blo 932582 1576057 := bstep (se 2 (by rfl) ⟨591021, by rfl⟩ : syracuseStep 1576057 = 1182043) B1182043
theorem B3149225 : Blo 932582 3149225 := bstep (se 2 (by rfl) ⟨1180959, by rfl⟩ : syracuseStep 3149225 = 2361919) B2361919
theorem B1576361 : Blo 932582 1576361 := bstep (se 2 (by rfl) ⟨591135, by rfl⟩ : syracuseStep 1576361 = 1182271) B1182271
theorem B2362871 : Blo 932582 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B2101031 : Blo 932582 2101031 := bstep (se 1 (by rfl) ⟨1575773, by rfl⟩ : syracuseStep 2101031 = 3151547) B3151547
theorem B1052455 : Blo 932582 1052455 := bstep (se 1 (by rfl) ⟨789341, by rfl⟩ : syracuseStep 1052455 = 1578683) B1578683
theorem B3149711 : Blo 932582 3149711 := bstep (se 1 (by rfl) ⟨2362283, by rfl⟩ : syracuseStep 3149711 = 4724567) B4724567
theorem B1577191 : Blo 932582 1577191 := bstep (se 1 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 1577191 = 2365787) B2365787
theorem B3150089 : Blo 932582 3150089 := bstep (se 2 (by rfl) ⟨1181283, by rfl⟩ : syracuseStep 3150089 = 2362567) B2362567
theorem B1577353 : Blo 932582 1577353 := bstep (se 2 (by rfl) ⟨591507, by rfl⟩ : syracuseStep 1577353 = 1183015) B1183015
theorem B2363863 : Blo 932582 2363863 := bstep (se 1 (by rfl) ⟨1772897, by rfl⟩ : syracuseStep 2363863 = 3545795) B3545795
theorem B2364167 : Blo 932582 2364167 := bstep (se 1 (by rfl) ⟨1773125, by rfl⟩ : syracuseStep 2364167 = 3546251) B3546251
theorem B2102057 : Blo 932582 2102057 := bstep (se 2 (by rfl) ⟨788271, by rfl⟩ : syracuseStep 2102057 = 1576543) B1576543
theorem B1577785 : Blo 932582 1577785 := bstep (se 2 (by rfl) ⟨591669, by rfl⟩ : syracuseStep 1577785 = 1183339) B1183339
theorem B1577839 : Blo 932582 1577839 := bstep (se 1 (by rfl) ⟨1183379, by rfl⟩ : syracuseStep 1577839 = 2366759) B2366759
theorem B11965319 : Blo 932582 11965319 := bstep (se 1 (by rfl) ⟨8973989, by rfl⟩ : syracuseStep 11965319 = 17947979) B17947979
theorem B1053607 : Blo 932582 1053607 := bstep (se 1 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 1053607 = 1580411) B1580411
theorem B5313545 : Blo 932582 5313545 := bstep (se 2 (by rfl) ⟨1992579, by rfl⟩ : syracuseStep 5313545 = 3985159) B3985159
theorem B2102327 : Blo 932582 2102327 := bstep (se 1 (by rfl) ⟨1576745, by rfl⟩ : syracuseStep 2102327 = 3153491) B3153491
theorem B2102345 : Blo 932582 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B874386521 : Blo 932582 874386521 := bstep (se 2 (by rfl) ⟨327894945, by rfl⟩ : syracuseStep 874386521 = 655789891) B655789891
theorem B1578089 : Blo 932582 1578089 := bstep (se 2 (by rfl) ⟨591783, by rfl⟩ : syracuseStep 1578089 = 1183567) B1183567
theorem B10655063 : Blo 932582 10655063 := bstep (se 1 (by rfl) ⟨7991297, by rfl⟩ : syracuseStep 10655063 = 15982595) B15982595
theorem B3151223 : Blo 932582 3151223 := bstep (se 1 (by rfl) ⟨2363417, by rfl⟩ : syracuseStep 3151223 = 4726835) B4726835
theorem B6067979 : Blo 932582 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B2365321 : Blo 932582 2365321 := bstep (se 2 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 2365321 = 1773991) B1773991
theorem B2660327 : Blo 932582 2660327 := bstep (se 1 (by rfl) ⟨1995245, by rfl⟩ : syracuseStep 2660327 = 3990491) B3990491
theorem B2365433 : Blo 932582 2365433 := bstep (se 2 (by rfl) ⟨887037, by rfl⟩ : syracuseStep 2365433 = 1774075) B1774075
theorem B37427293 : Blo 932582 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B4724891 : Blo 932582 4724891 := bstep (se 1 (by rfl) ⟨3543668, by rfl⟩ : syracuseStep 4724891 = 7087337) B7087337
theorem B2365595 : Blo 932582 2365595 := bstep (se 1 (by rfl) ⟨1774196, by rfl⟩ : syracuseStep 2365595 = 3548393) B3548393
theorem B3152033 : Blo 932582 3152033 := bstep (se 2 (by rfl) ⟨1182012, by rfl⟩ : syracuseStep 3152033 = 2364025) B2364025
theorem B1579243 : Blo 932582 1579243 := bstep (se 1 (by rfl) ⟨1184432, by rfl⟩ : syracuseStep 1579243 = 2368865) B2368865
theorem B3152303 : Blo 932582 3152303 := bstep (se 1 (by rfl) ⟨2364227, by rfl⟩ : syracuseStep 3152303 = 4728455) B4728455
theorem B1579547 : Blo 932582 1579547 := bstep (se 1 (by rfl) ⟨1184660, by rfl⟩ : syracuseStep 1579547 = 2369321) B2369321
theorem B5675741 : Blo 932582 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B1776467 : Blo 932582 1776467 := bstep (se 1 (by rfl) ⟨1332350, by rfl⟩ : syracuseStep 1776467 = 2664701) B2664701
theorem B15965099 : Blo 932582 15965099 := bstep (se 1 (by rfl) ⟨11973824, by rfl⟩ : syracuseStep 15965099 = 23947649) B23947649
theorem B2104271 : Blo 932582 2104271 := bstep (se 1 (by rfl) ⟨1578203, by rfl⟩ : syracuseStep 2104271 = 3156407) B3156407
theorem B2104289 : Blo 932582 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B2104361 : Blo 932582 2104361 := bstep (se 2 (by rfl) ⟨789135, by rfl⟩ : syracuseStep 2104361 = 1578271) B1578271
theorem B1580215 : Blo 932582 1580215 := bstep (se 1 (by rfl) ⟨1185161, by rfl⟩ : syracuseStep 1580215 = 2370323) B2370323
theorem B2366729 : Blo 932582 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B3546463 : Blo 932582 3546463 := bstep (se 1 (by rfl) ⟨2659847, by rfl⟩ : syracuseStep 3546463 = 5319695) B5319695
theorem B3153383 : Blo 932582 3153383 := bstep (se 1 (by rfl) ⟨2365037, by rfl⟩ : syracuseStep 3153383 = 4730075) B4730075
theorem B1777295 : Blo 932582 1777295 := bstep (se 1 (by rfl) ⟨1332971, by rfl⟩ : syracuseStep 1777295 = 2665943) B2665943
theorem B3546935 : Blo 932582 3546935 := bstep (se 1 (by rfl) ⟨2660201, by rfl⟩ : syracuseStep 3546935 = 5320403) B5320403
theorem B5316779 : Blo 932582 5316779 := bstep (se 1 (by rfl) ⟨3987584, by rfl⟩ : syracuseStep 5316779 = 7975169) B7975169
theorem B3154139 : Blo 932582 3154139 := bstep (se 1 (by rfl) ⟨2365604, by rfl⟩ : syracuseStep 3154139 = 4731209) B4731209
theorem B5316961 : Blo 932582 5316961 := bstep (se 2 (by rfl) ⟨1993860, by rfl⟩ : syracuseStep 5316961 = 3987721) B3987721
theorem B2662753 : Blo 932582 2662753 := bstep (se 2 (by rfl) ⟨998532, by rfl⟩ : syracuseStep 2662753 = 1997065) B1997065
theorem B4727159 : Blo 932582 4727159 := bstep (se 1 (by rfl) ⟨3545369, by rfl⟩ : syracuseStep 4727159 = 7090739) B7090739
theorem B3154409 : Blo 932582 3154409 := bstep (se 2 (by rfl) ⟨1182903, by rfl⟩ : syracuseStep 3154409 = 2365807) B2365807
theorem B5317487 : Blo 932582 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B2106323 : Blo 932582 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B3155003 : Blo 932582 3155003 := bstep (se 1 (by rfl) ⟨2366252, by rfl⟩ : syracuseStep 3155003 = 4732505) B4732505
theorem B2991293 : Blo 932582 2991293 := bstep (se 3 (by rfl) ⟨560867, by rfl⟩ : syracuseStep 2991293 = 1121735) B1121735
theorem B2106575 : Blo 932582 2106575 := bstep (se 1 (by rfl) ⟨1579931, by rfl⟩ : syracuseStep 2106575 = 3159863) B3159863
theorem B4728131 : Blo 932582 4728131 := bstep (se 1 (by rfl) ⟨3546098, by rfl⟩ : syracuseStep 4728131 = 7092197) B7092197
theorem B3155273 : Blo 932582 3155273 := bstep (se 2 (by rfl) ⟨1183227, by rfl⟩ : syracuseStep 3155273 = 2366455) B2366455
theorem B2106899 : Blo 932582 2106899 := bstep (se 1 (by rfl) ⟨1580174, by rfl⟩ : syracuseStep 2106899 = 3160349) B3160349
theorem B4499297 : Blo 932582 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B4728941 : Blo 932582 4728941 := bstep (se 3 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 4728941 = 1773353) B1773353
theorem B13674919 : Blo 932582 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B81766835 : Blo 932582 81766835 := bstep (se 1 (by rfl) ⟨61325126, by rfl⟩ : syracuseStep 81766835 = 122650253) B122650253
theorem B3550351 : Blo 932582 3550351 := bstep (se 1 (by rfl) ⟨2662763, by rfl⟩ : syracuseStep 3550351 = 5325527) B5325527
theorem B3419435 : Blo 932582 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B5320151 : Blo 932582 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B5058121 : Blo 932582 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B5680801 : Blo 932582 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B2666159 : Blo 932582 2666159 := bstep (se 1 (by rfl) ⟨1999619, by rfl⟩ : syracuseStep 2666159 = 3999239) B3999239
theorem B3157865 : Blo 932582 3157865 := bstep (se 2 (by rfl) ⟨1184199, by rfl⟩ : syracuseStep 3157865 = 2368399) B2368399
theorem B4272095 : Blo 932582 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B2699453 : Blo 932582 2699453 := bstep (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) B1012295
theorem B26915273 : Blo 932582 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B2667001 : Blo 932582 2667001 := bstep (se 2 (by rfl) ⟨1000125, by rfl⟩ : syracuseStep 2667001 = 2000251) B2000251
theorem B4732019 : Blo 932582 4732019 := bstep (se 1 (by rfl) ⟨3549014, by rfl⟩ : syracuseStep 4732019 = 7098029) B7098029
theorem B3159215 : Blo 932582 3159215 := bstep (se 1 (by rfl) ⟨2369411, by rfl⟩ : syracuseStep 3159215 = 4738823) B4738823
theorem B4732667 : Blo 932582 4732667 := bstep (se 1 (by rfl) ⟨3549500, by rfl⟩ : syracuseStep 4732667 = 7099001) B7099001
theorem B4732829 : Blo 932582 4732829 := bstep (se 3 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 4732829 = 1774811) B1774811
theorem B2243209 : Blo 932582 2243209 := bstep (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) B1682407
theorem B4733639 : Blo 932582 4733639 := bstep (se 1 (by rfl) ⟨3550229, by rfl⟩ : syracuseStep 4733639 = 7100459) B7100459
theorem B2997071 : Blo 932582 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B932699 : Blo 932582 932699 := bstep (se 1 (by rfl) ⟨699524, by rfl⟩ : syracuseStep 932699 = 1399049) B1399049
theorem B932767 : Blo 932582 932767 := bstep (se 1 (by rfl) ⟨699575, by rfl⟩ : syracuseStep 932767 = 1399151) B1399151
theorem B932911 : Blo 932582 932911 := bstep (se 1 (by rfl) ⟨699683, by rfl⟩ : syracuseStep 932911 = 1399367) B1399367
theorem B932935 : Blo 932582 932935 := bstep (se 1 (by rfl) ⟨699701, by rfl⟩ : syracuseStep 932935 = 1399403) B1399403
theorem B933087 : Blo 932582 933087 := bstep (se 1 (by rfl) ⟨699815, by rfl⟩ : syracuseStep 933087 = 1399631) B1399631
theorem B15973847 : Blo 932582 15973847 := bstep (se 1 (by rfl) ⟨11980385, by rfl⟩ : syracuseStep 15973847 = 23960771) B23960771
theorem B933351 : Blo 932582 933351 := bstep (se 1 (by rfl) ⟨700013, by rfl⟩ : syracuseStep 933351 = 1400027) B1400027
theorem B998887 : Blo 932582 998887 := bstep (se 1 (by rfl) ⟨749165, by rfl⟩ : syracuseStep 998887 = 1498331) B1498331
theorem B933467 : Blo 932582 933467 := bstep (se 1 (by rfl) ⟨700100, by rfl⟩ : syracuseStep 933467 = 1400201) B1400201
theorem B2244239 : Blo 932582 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B1261351 : Blo 932582 1261351 := bstep (se 1 (by rfl) ⟨946013, by rfl⟩ : syracuseStep 1261351 = 1892027) B1892027
theorem B933703 : Blo 932582 933703 := bstep (se 1 (by rfl) ⟨700277, by rfl⟩ : syracuseStep 933703 = 1400555) B1400555
theorem B3784573 : Blo 932582 3784573 := bstep (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) B1419215
theorem B7094141 : Blo 932582 7094141 := bstep (se 3 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 7094141 = 2660303) B2660303
theorem B3555197 : Blo 932582 3555197 := bstep (se 3 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 3555197 = 1333199) B1333199
theorem B933855 : Blo 932582 933855 := bstep (se 1 (by rfl) ⟨700391, by rfl⟩ : syracuseStep 933855 = 1400783) B1400783
theorem B934119 : Blo 932582 934119 := bstep (se 1 (by rfl) ⟨700589, by rfl⟩ : syracuseStep 934119 = 1401179) B1401179
theorem B12140887 : Blo 932582 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B934271 : Blo 932582 934271 := bstep (se 1 (by rfl) ⟨700703, by rfl⟩ : syracuseStep 934271 = 1401407) B1401407
theorem B2998711 : Blo 932582 2998711 := bstep (se 1 (by rfl) ⟨2249033, by rfl⟩ : syracuseStep 2998711 = 4498067) B4498067
theorem B934351 : Blo 932582 934351 := bstep (se 1 (by rfl) ⟨700763, by rfl⟩ : syracuseStep 934351 = 1401527) B1401527
theorem B21545453 : Blo 932582 21545453 := bstep (se 3 (by rfl) ⟨4039772, by rfl⟩ : syracuseStep 21545453 = 8079545) B8079545
theorem B934503 : Blo 932582 934503 := bstep (se 1 (by rfl) ⟨700877, by rfl⟩ : syracuseStep 934503 = 1401755) B1401755
theorem B3031805 : Blo 932582 3031805 := bstep (se 3 (by rfl) ⟨568463, by rfl⟩ : syracuseStep 3031805 = 1136927) B1136927
theorem B1327919 : Blo 932582 1327919 := bstep (se 1 (by rfl) ⟨995939, by rfl⟩ : syracuseStep 1327919 = 1991879) B1991879
theorem B934767 : Blo 932582 934767 := bstep (se 1 (by rfl) ⟨701075, by rfl⟩ : syracuseStep 934767 = 1402151) B1402151
theorem B2999197 : Blo 932582 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B934823 : Blo 932582 934823 := bstep (se 1 (by rfl) ⟨701117, by rfl⟩ : syracuseStep 934823 = 1402235) B1402235
theorem B934907 : Blo 932582 934907 := bstep (se 1 (by rfl) ⟨701180, by rfl⟩ : syracuseStep 934907 = 1402361) B1402361
theorem B934975 : Blo 932582 934975 := bstep (se 1 (by rfl) ⟨701231, by rfl⟩ : syracuseStep 934975 = 1402463) B1402463
theorem B1328233 : Blo 932582 1328233 := bstep (se 2 (by rfl) ⟨498087, by rfl⟩ : syracuseStep 1328233 = 996175) B996175
theorem B935119 : Blo 932582 935119 := bstep (se 1 (by rfl) ⟨701339, by rfl⟩ : syracuseStep 935119 = 1402679) B1402679
theorem B935323 : Blo 932582 935323 := bstep (se 1 (by rfl) ⟨701492, by rfl⟩ : syracuseStep 935323 = 1402985) B1402985
theorem B8635901 : Blo 932582 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B3786259 : Blo 932582 3786259 := bstep (se 1 (by rfl) ⟨2839694, by rfl⟩ : syracuseStep 3786259 = 5679389) B5679389
theorem B935535 : Blo 932582 935535 := bstep (se 1 (by rfl) ⟨701651, by rfl⟩ : syracuseStep 935535 = 1403303) B1403303
theorem B935591 : Blo 932582 935591 := bstep (se 1 (by rfl) ⟨701693, by rfl⟩ : syracuseStep 935591 = 1403387) B1403387
theorem B11978441 : Blo 932582 11978441 := bstep (se 2 (by rfl) ⟨4491915, by rfl⟩ : syracuseStep 11978441 = 8983831) B8983831
theorem B935675 : Blo 932582 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B935711 : Blo 932582 935711 := bstep (se 1 (by rfl) ⟨701783, by rfl⟩ : syracuseStep 935711 = 1403567) B1403567
theorem B935743 : Blo 932582 935743 := bstep (se 1 (by rfl) ⟨701807, by rfl⟩ : syracuseStep 935743 = 1403615) B1403615
theorem B935919 : Blo 932582 935919 := bstep (se 1 (by rfl) ⟨701939, by rfl⟩ : syracuseStep 935919 = 1403879) B1403879
theorem B936091 : Blo 932582 936091 := bstep (se 1 (by rfl) ⟨702068, by rfl⟩ : syracuseStep 936091 = 1404137) B1404137
theorem B936127 : Blo 932582 936127 := bstep (se 1 (by rfl) ⟨702095, by rfl⟩ : syracuseStep 936127 = 1404191) B1404191
theorem B936239 : Blo 932582 936239 := bstep (se 1 (by rfl) ⟨702179, by rfl⟩ : syracuseStep 936239 = 1404359) B1404359
theorem B1329691 : Blo 932582 1329691 := bstep (se 1 (by rfl) ⟨997268, by rfl⟩ : syracuseStep 1329691 = 1994537) B1994537
theorem B936475 : Blo 932582 936475 := bstep (se 1 (by rfl) ⟨702356, by rfl⟩ : syracuseStep 936475 = 1404713) B1404713
theorem B936479 : Blo 932582 936479 := bstep (se 1 (by rfl) ⟨702359, by rfl⟩ : syracuseStep 936479 = 1404719) B1404719
theorem B7097543 : Blo 932582 7097543 := bstep (se 1 (by rfl) ⟨5323157, by rfl⟩ : syracuseStep 7097543 = 10646315) B10646315
theorem B19221791 : Blo 932582 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B4935163 : Blo 932582 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B5328443 : Blo 932582 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B1330921 : Blo 932582 1330921 := bstep (se 2 (by rfl) ⟨499095, by rfl⟩ : syracuseStep 1330921 = 998191) B998191
theorem B23908283 : Blo 932582 23908283 := bstep (se 1 (by rfl) ⟨17931212, by rfl⟩ : syracuseStep 23908283 = 35862425) B35862425
theorem B1200511 : Blo 932582 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B13455791 : Blo 932582 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B1331815 : Blo 932582 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B3986081 : Blo 932582 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B8999747 : Blo 932582 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B2249783 : Blo 932582 2249783 := bstep (se 1 (by rfl) ⟨1687337, by rfl⟩ : syracuseStep 2249783 = 3374675) B3374675
theorem B7591009 : Blo 932582 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B3364051 : Blo 932582 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B4740443 : Blo 932582 4740443 := bstep (se 1 (by rfl) ⟨3555332, by rfl⟩ : syracuseStep 4740443 = 7110665) B7110665
theorem B1136027 : Blo 932582 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B8968067 : Blo 932582 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B9722051 : Blo 932582 9722051 := bstep (se 1 (by rfl) ⟨7291538, by rfl⟩ : syracuseStep 9722051 = 14583077) B14583077
theorem B1399019 : Blo 932582 1399019 := bstep (se 1 (by rfl) ⟨1049264, by rfl⟩ : syracuseStep 1399019 = 2098529) B2098529
theorem B12146959 : Blo 932582 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B1399079 : Blo 932582 1399079 := bstep (se 1 (by rfl) ⟨1049309, by rfl⟩ : syracuseStep 1399079 = 2098619) B2098619
theorem B1399163 : Blo 932582 1399163 := bstep (se 1 (by rfl) ⟨1049372, by rfl⟩ : syracuseStep 1399163 = 2098745) B2098745
theorem B1399433 : Blo 932582 1399433 := bstep (se 2 (by rfl) ⟨524787, by rfl⟩ : syracuseStep 1399433 = 1049575) B1049575
theorem B1399607 : Blo 932582 1399607 := bstep (se 1 (by rfl) ⟨1049705, by rfl⟩ : syracuseStep 1399607 = 2099411) B2099411
theorem B3201871 : Blo 932582 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B1399643 : Blo 932582 1399643 := bstep (se 1 (by rfl) ⟨1049732, by rfl⟩ : syracuseStep 1399643 = 2099465) B2099465
theorem B1399787 : Blo 932582 1399787 := bstep (se 1 (by rfl) ⟨1049840, by rfl⟩ : syracuseStep 1399787 = 2099681) B2099681
theorem B7691321 : Blo 932582 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B1399991 : Blo 932582 1399991 := bstep (se 1 (by rfl) ⟨1049993, by rfl⟩ : syracuseStep 1399991 = 2099987) B2099987
theorem B1400231 : Blo 932582 1400231 := bstep (se 1 (by rfl) ⟨1050173, by rfl⟩ : syracuseStep 1400231 = 2100347) B2100347
theorem B1400315 : Blo 932582 1400315 := bstep (se 1 (by rfl) ⟨1050236, by rfl⟩ : syracuseStep 1400315 = 2100473) B2100473
theorem B1498619 : Blo 932582 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B1400411 : Blo 932582 1400411 := bstep (se 1 (by rfl) ⟨1050308, by rfl⟩ : syracuseStep 1400411 = 2100617) B2100617
theorem B1400495 : Blo 932582 1400495 := bstep (se 1 (by rfl) ⟨1050371, by rfl⟩ : syracuseStep 1400495 = 2100743) B2100743
theorem B15163139 : Blo 932582 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B1400615 : Blo 932582 1400615 := bstep (se 1 (by rfl) ⟨1050461, by rfl⟩ : syracuseStep 1400615 = 2100923) B2100923
theorem B5988143 : Blo 932582 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B1400699 : Blo 932582 1400699 := bstep (se 1 (by rfl) ⟨1050524, by rfl⟩ : syracuseStep 1400699 = 2101049) B2101049
theorem B1499035 : Blo 932582 1499035 := bstep (se 1 (by rfl) ⟨1124276, by rfl⟩ : syracuseStep 1499035 = 2248553) B2248553
theorem B1401119 : Blo 932582 1401119 := bstep (se 1 (by rfl) ⟨1050839, by rfl⟩ : syracuseStep 1401119 = 2101679) B2101679
theorem B1401143 : Blo 932582 1401143 := bstep (se 1 (by rfl) ⟨1050857, by rfl⟩ : syracuseStep 1401143 = 2101715) B2101715
theorem B1401215 : Blo 932582 1401215 := bstep (se 1 (by rfl) ⟨1050911, by rfl⟩ : syracuseStep 1401215 = 2101823) B2101823
theorem B1139071 : Blo 932582 1139071 := bstep (se 1 (by rfl) ⟨854303, by rfl⟩ : syracuseStep 1139071 = 1708607) B1708607
theorem B1401287 : Blo 932582 1401287 := bstep (se 1 (by rfl) ⟨1050965, by rfl⟩ : syracuseStep 1401287 = 2101931) B2101931
theorem B10084925 : Blo 932582 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B10773101 : Blo 932582 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B1401641 : Blo 932582 1401641 := bstep (se 2 (by rfl) ⟨525615, by rfl⟩ : syracuseStep 1401641 = 1051231) B1051231
theorem B1401647 : Blo 932582 1401647 := bstep (se 1 (by rfl) ⟨1051235, by rfl⟩ : syracuseStep 1401647 = 2102471) B2102471
theorem B1401767 : Blo 932582 1401767 := bstep (se 1 (by rfl) ⟨1051325, by rfl⟩ : syracuseStep 1401767 = 2102651) B2102651
theorem B1401851 : Blo 932582 1401851 := bstep (se 1 (by rfl) ⟨1051388, by rfl⟩ : syracuseStep 1401851 = 2102777) B2102777
theorem B1401911 : Blo 932582 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B17065025 : Blo 932582 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B1402031 : Blo 932582 1402031 := bstep (se 1 (by rfl) ⟨1051523, by rfl⟩ : syracuseStep 1402031 = 2103047) B2103047
theorem B2024875 : Blo 932582 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B1402439 : Blo 932582 1402439 := bstep (se 1 (by rfl) ⟨1051829, by rfl⟩ : syracuseStep 1402439 = 2103659) B2103659
theorem B3991207 : Blo 932582 3991207 := bstep (se 1 (by rfl) ⟨2993405, by rfl⟩ : syracuseStep 3991207 = 5986811) B5986811
theorem B1402535 : Blo 932582 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B1402619 : Blo 932582 1402619 := bstep (se 1 (by rfl) ⟨1051964, by rfl⟩ : syracuseStep 1402619 = 2103929) B2103929
theorem B1402655 : Blo 932582 1402655 := bstep (se 1 (by rfl) ⟨1051991, by rfl⟩ : syracuseStep 1402655 = 2103983) B2103983
theorem B1402703 : Blo 932582 1402703 := bstep (se 1 (by rfl) ⟨1052027, by rfl⟩ : syracuseStep 1402703 = 2104055) B2104055
theorem B1402823 : Blo 932582 1402823 := bstep (se 1 (by rfl) ⟨1052117, by rfl⟩ : syracuseStep 1402823 = 2104235) B2104235
theorem B20506769 : Blo 932582 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B1403177 : Blo 932582 1403177 := bstep (se 2 (by rfl) ⟨526191, by rfl⟩ : syracuseStep 1403177 = 1052383) B1052383
theorem B1993007 : Blo 932582 1993007 := bstep (se 1 (by rfl) ⟨1494755, by rfl⟩ : syracuseStep 1993007 = 2989511) B2989511
theorem B1403183 : Blo 932582 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B6744503 : Blo 932582 6744503 := bstep (se 1 (by rfl) ⟨5058377, by rfl⟩ : syracuseStep 6744503 = 10116755) B10116755
theorem B1403423 : Blo 932582 1403423 := bstep (se 1 (by rfl) ⟨1052567, by rfl⟩ : syracuseStep 1403423 = 2105135) B2105135
theorem B3795767 : Blo 932582 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B1403807 : Blo 932582 1403807 := bstep (se 1 (by rfl) ⟨1052855, by rfl⟩ : syracuseStep 1403807 = 2105711) B2105711
theorem B1600463 : Blo 932582 1600463 := bstep (se 1 (by rfl) ⟨1200347, by rfl⟩ : syracuseStep 1600463 = 2400695) B2400695
theorem B1403855 : Blo 932582 1403855 := bstep (se 1 (by rfl) ⟨1052891, by rfl⟩ : syracuseStep 1403855 = 2105783) B2105783
theorem B1403945 : Blo 932582 1403945 := bstep (se 2 (by rfl) ⟨526479, by rfl⟩ : syracuseStep 1403945 = 1052959) B1052959
theorem B1403951 : Blo 932582 1403951 := bstep (se 1 (by rfl) ⟨1052963, by rfl⟩ : syracuseStep 1403951 = 2105927) B2105927
theorem B1403975 : Blo 932582 1403975 := bstep (se 1 (by rfl) ⟨1052981, by rfl⟩ : syracuseStep 1403975 = 2105963) B2105963
theorem B1404239 : Blo 932582 1404239 := bstep (se 1 (by rfl) ⟨1053179, by rfl⟩ : syracuseStep 1404239 = 2106359) B2106359
theorem B5991833 : Blo 932582 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B1404329 : Blo 932582 1404329 := bstep (se 2 (by rfl) ⟨526623, by rfl⟩ : syracuseStep 1404329 = 1053247) B1053247
theorem B1404479 : Blo 932582 1404479 := bstep (se 1 (by rfl) ⟨1053359, by rfl⟩ : syracuseStep 1404479 = 2106719) B2106719
theorem B1601351 : Blo 932582 1601351 := bstep (se 1 (by rfl) ⟨1201013, by rfl⟩ : syracuseStep 1601351 = 2402027) B2402027
theorem B1404743 : Blo 932582 1404743 := bstep (se 1 (by rfl) ⟨1053557, by rfl⟩ : syracuseStep 1404743 = 2107115) B2107115
theorem B5533595 : Blo 932582 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B1404827 : Blo 932582 1404827 := bstep (se 1 (by rfl) ⟨1053620, by rfl⟩ : syracuseStep 1404827 = 2107241) B2107241
theorem B3371273 : Blo 932582 3371273 := bstep (se 2 (by rfl) ⟨1264227, by rfl⟩ : syracuseStep 3371273 = 2528455) B2528455
theorem B9597527 : Blo 932582 9597527 := bstep (se 1 (by rfl) ⟨7198145, by rfl⟩ : syracuseStep 9597527 = 14396291) B14396291
theorem B1995425 : Blo 932582 1995425 := bstep (se 2 (by rfl) ⟨748284, by rfl⟩ : syracuseStep 1995425 = 1496569) B1496569
theorem B1897121 : Blo 932582 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B13628573 : Blo 932582 13628573 := bstep (se 3 (by rfl) ⟨2555357, by rfl⟩ : syracuseStep 13628573 = 5110715) B5110715
theorem B8976527 : Blo 932582 8976527 := bstep (se 1 (by rfl) ⟨6732395, by rfl⟩ : syracuseStep 8976527 = 13464791) B13464791
theorem B4487879 : Blo 932582 4487879 := bstep (se 1 (by rfl) ⟨3365909, by rfl⟩ : syracuseStep 4487879 = 6731819) B6731819
theorem B1998569 : Blo 932582 1998569 := bstep (se 2 (by rfl) ⟨749463, by rfl⟩ : syracuseStep 1998569 = 1498927) B1498927
theorem B5767037 : Blo 932582 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B16187849 : Blo 932582 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B3998281 : Blo 932582 3998281 := bstep (se 2 (by rfl) ⟨1499355, by rfl⟩ : syracuseStep 3998281 = 2998711) B2998711
theorem B1770491 : Blo 932582 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B1049647 : Blo 932582 1049647 := bstep (se 1 (by rfl) ⟨787235, by rfl⟩ : syracuseStep 1049647 = 1574471) B1574471
theorem B2098367 : Blo 932582 2098367 := bstep (se 1 (by rfl) ⟨1573775, by rfl⟩ : syracuseStep 2098367 = 3147551) B3147551
theorem B1049791 : Blo 932582 1049791 := bstep (se 1 (by rfl) ⟨787343, by rfl⟩ : syracuseStep 1049791 = 1574687) B1574687
theorem B12780767 : Blo 932582 12780767 := bstep (se 1 (by rfl) ⟨9585575, by rfl⟩ : syracuseStep 12780767 = 19171151) B19171151
theorem B2360623 : Blo 932582 2360623 := bstep (se 1 (by rfl) ⟨1770467, by rfl⟩ : syracuseStep 2360623 = 3540935) B3540935
theorem B1180975 : Blo 932582 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B2098511 : Blo 932582 2098511 := bstep (se 1 (by rfl) ⟨1573883, by rfl⟩ : syracuseStep 2098511 = 3147767) B3147767
theorem B1049935 : Blo 932582 1049935 := bstep (se 1 (by rfl) ⟨787451, by rfl⟩ : syracuseStep 1049935 = 1574903) B1574903
theorem B2098601 : Blo 932582 2098601 := bstep (se 2 (by rfl) ⟨786975, by rfl⟩ : syracuseStep 2098601 = 1573951) B1573951
theorem B1770977 : Blo 932582 1770977 := bstep (se 2 (by rfl) ⟨664116, by rfl⟩ : syracuseStep 1770977 = 1328233) B1328233
theorem B1771303 : Blo 932582 1771303 := bstep (se 1 (by rfl) ⟨1328477, by rfl⟩ : syracuseStep 1771303 = 2656955) B2656955
theorem B2099087 : Blo 932582 2099087 := bstep (se 1 (by rfl) ⟨1574315, by rfl⟩ : syracuseStep 2099087 = 3148631) B3148631
theorem B5048345 : Blo 932582 5048345 := bstep (se 2 (by rfl) ⟨1893129, by rfl⟩ : syracuseStep 5048345 = 3786259) B3786259
theorem B2099231 : Blo 932582 2099231 := bstep (se 1 (by rfl) ⟨1574423, by rfl⟩ : syracuseStep 2099231 = 3148847) B3148847
theorem B1050655 : Blo 932582 1050655 := bstep (se 1 (by rfl) ⟨787991, by rfl⟩ : syracuseStep 1050655 = 1575983) B1575983
theorem B3541117 : Blo 932582 3541117 := bstep (se 3 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 3541117 = 1327919) B1327919
theorem B2099483 : Blo 932582 2099483 := bstep (se 1 (by rfl) ⟨1574612, by rfl⟩ : syracuseStep 2099483 = 3149225) B3149225
theorem B1050907 : Blo 932582 1050907 := bstep (se 1 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 1050907 = 1576361) B1576361
theorem B1575247 : Blo 932582 1575247 := bstep (se 1 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 1575247 = 2362871) B2362871
theorem B2099807 : Blo 932582 2099807 := bstep (se 1 (by rfl) ⟨1574855, by rfl⟩ : syracuseStep 2099807 = 3149711) B3149711
theorem B2100059 : Blo 932582 2100059 := bstep (se 1 (by rfl) ⟨1575044, by rfl⟩ : syracuseStep 2100059 = 3150089) B3150089
theorem B68324309 : Blo 932582 68324309 := bstep (se 7 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 68324309 = 1601351) B1601351
theorem B2657387 : Blo 932582 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B1576111 : Blo 932582 1576111 := bstep (se 1 (by rfl) ⟨1182083, by rfl⟩ : syracuseStep 1576111 = 2364167) B2364167
theorem B5999831 : Blo 932582 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B3542363 : Blo 932582 3542363 := bstep (se 1 (by rfl) ⟨2656772, by rfl⟩ : syracuseStep 3542363 = 5313545) B5313545
theorem B3542393 : Blo 932582 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B1772921 : Blo 932582 1772921 := bstep (se 2 (by rfl) ⟨664845, by rfl⟩ : syracuseStep 1772921 = 1329691) B1329691
theorem B1052059 : Blo 932582 1052059 := bstep (se 1 (by rfl) ⟨789044, by rfl⟩ : syracuseStep 1052059 = 1578089) B1578089
theorem B2100815 : Blo 932582 2100815 := bstep (se 1 (by rfl) ⟨1575611, by rfl⟩ : syracuseStep 2100815 = 3151223) B3151223
theorem B4722461 : Blo 932582 4722461 := bstep (se 3 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 4722461 = 1770923) B1770923
theorem B1773551 : Blo 932582 1773551 := bstep (se 1 (by rfl) ⟨1330163, by rfl⟩ : syracuseStep 1773551 = 2660327) B2660327
theorem B1576955 : Blo 932582 1576955 := bstep (se 1 (by rfl) ⟨1182716, by rfl⟩ : syracuseStep 1576955 = 2365433) B2365433
theorem B3149927 : Blo 932582 3149927 := bstep (se 1 (by rfl) ⟨2362445, by rfl⟩ : syracuseStep 3149927 = 4724891) B4724891
theorem B1577063 : Blo 932582 1577063 := bstep (se 1 (by rfl) ⟨1182797, by rfl⟩ : syracuseStep 1577063 = 2365595) B2365595
theorem B2101355 : Blo 932582 2101355 := bstep (se 1 (by rfl) ⟨1576016, by rfl⟩ : syracuseStep 2101355 = 3152033) B3152033
theorem B2101409 : Blo 932582 2101409 := bstep (se 2 (by rfl) ⟨788028, by rfl⟩ : syracuseStep 2101409 = 1576057) B1576057
theorem B2101535 : Blo 932582 2101535 := bstep (se 1 (by rfl) ⟨1576151, by rfl⟩ : syracuseStep 2101535 = 3152303) B3152303
theorem B1053031 : Blo 932582 1053031 := bstep (se 1 (by rfl) ⟨789773, by rfl⟩ : syracuseStep 1053031 = 1579547) B1579547
theorem B1184311 : Blo 932582 1184311 := bstep (se 1 (by rfl) ⟨888233, by rfl⟩ : syracuseStep 1184311 = 1776467) B1776467
theorem B15995717 : Blo 932582 15995717 := bstep (se 4 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 15995717 = 2999197) B2999197
theorem B1577819 : Blo 932582 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B7574401 : Blo 932582 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B1774561 : Blo 932582 1774561 := bstep (se 2 (by rfl) ⟨665460, by rfl⟩ : syracuseStep 1774561 = 1330921) B1330921
theorem B2102255 : Blo 932582 2102255 := bstep (se 1 (by rfl) ⟨1576691, by rfl⟩ : syracuseStep 2102255 = 3153383) B3153383
theorem B1184863 : Blo 932582 1184863 := bstep (se 1 (by rfl) ⟨888647, by rfl⟩ : syracuseStep 1184863 = 1777295) B1777295
theorem B2364623 : Blo 932582 2364623 := bstep (se 1 (by rfl) ⟨1773467, by rfl⟩ : syracuseStep 2364623 = 3546935) B3546935
theorem B3544519 : Blo 932582 3544519 := bstep (se 1 (by rfl) ⟨2658389, by rfl⟩ : syracuseStep 3544519 = 5316779) B5316779
theorem B2102759 : Blo 932582 2102759 := bstep (se 1 (by rfl) ⟨1577069, by rfl⟩ : syracuseStep 2102759 = 3154139) B3154139
theorem B3151439 : Blo 932582 3151439 := bstep (se 1 (by rfl) ⟨2363579, by rfl⟩ : syracuseStep 3151439 = 4727159) B4727159
theorem B2102921 : Blo 932582 2102921 := bstep (se 2 (by rfl) ⟨788595, by rfl⟩ : syracuseStep 2102921 = 1577191) B1577191
theorem B2102939 : Blo 932582 2102939 := bstep (se 1 (by rfl) ⟨1577204, by rfl⟩ : syracuseStep 2102939 = 3154409) B3154409
theorem B6723283 : Blo 932582 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B7182067 : Blo 932582 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B2103137 : Blo 932582 2103137 := bstep (se 2 (by rfl) ⟨788676, by rfl⟩ : syracuseStep 2103137 = 1577353) B1577353
theorem B3544991 : Blo 932582 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B3151817 : Blo 932582 3151817 := bstep (se 2 (by rfl) ⟨1181931, by rfl⟩ : syracuseStep 3151817 = 2363863) B2363863
theorem B2103335 : Blo 932582 2103335 := bstep (se 1 (by rfl) ⟨1577501, by rfl⟩ : syracuseStep 2103335 = 3155003) B3155003
theorem B11376683 : Blo 932582 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B1775753 : Blo 932582 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B3152087 : Blo 932582 3152087 := bstep (se 1 (by rfl) ⟨2364065, by rfl⟩ : syracuseStep 3152087 = 4728131) B4728131
theorem B2103515 : Blo 932582 2103515 := bstep (se 1 (by rfl) ⟨1577636, by rfl⟩ : syracuseStep 2103515 = 3155273) B3155273
theorem B2103713 : Blo 932582 2103713 := bstep (se 2 (by rfl) ⟨788892, by rfl⟩ : syracuseStep 2103713 = 1577785) B1577785
theorem B2103785 : Blo 932582 2103785 := bstep (se 2 (by rfl) ⟨788919, by rfl⟩ : syracuseStep 2103785 = 1577839) B1577839
theorem B3152627 : Blo 932582 3152627 := bstep (se 1 (by rfl) ⟨2364470, by rfl⟩ : syracuseStep 3152627 = 4728941) B4728941
theorem B13671179 : Blo 932582 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B2530511 : Blo 932582 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B3546767 : Blo 932582 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B1777439 : Blo 932582 1777439 := bstep (se 1 (by rfl) ⟨1333079, by rfl⟩ : syracuseStep 1777439 = 2666159) B2666159
theorem B3153761 : Blo 932582 3153761 := bstep (se 2 (by rfl) ⟨1182660, by rfl⟩ : syracuseStep 3153761 = 2365321) B2365321
theorem B2105243 : Blo 932582 2105243 := bstep (se 1 (by rfl) ⟨1578932, by rfl⟩ : syracuseStep 2105243 = 3157865) B3157865
theorem B2105657 : Blo 932582 2105657 := bstep (se 2 (by rfl) ⟨789621, by rfl⟩ : syracuseStep 2105657 = 1579243) B1579243
theorem B16195945 : Blo 932582 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B6398351 : Blo 932582 6398351 := bstep (se 1 (by rfl) ⟨4798763, by rfl⟩ : syracuseStep 6398351 = 9597527) B9597527
theorem B3154679 : Blo 932582 3154679 := bstep (se 1 (by rfl) ⟨2366009, by rfl⟩ : syracuseStep 3154679 = 4732019) B4732019
theorem B51258109 : Blo 932582 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B9085715 : Blo 932582 9085715 := bstep (se 1 (by rfl) ⟨6814286, by rfl⟩ : syracuseStep 9085715 = 13628573) B13628573
theorem B9118493 : Blo 932582 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B2106143 : Blo 932582 2106143 := bstep (se 1 (by rfl) ⟨1579607, by rfl⟩ : syracuseStep 2106143 = 3159215) B3159215
theorem B2990945 : Blo 932582 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B4269161 : Blo 932582 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B3155111 : Blo 932582 3155111 := bstep (se 1 (by rfl) ⟨2366333, by rfl⟩ : syracuseStep 3155111 = 4732667) B4732667
theorem B3155219 : Blo 932582 3155219 := bstep (se 1 (by rfl) ⟨2366414, by rfl⟩ : syracuseStep 3155219 = 4732829) B4732829
theorem B6727205 : Blo 932582 6727205 := bstep (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) B1261351
theorem B2106953 : Blo 932582 2106953 := bstep (se 2 (by rfl) ⟨790107, by rfl⟩ : syracuseStep 2106953 = 1580215) B1580215
theorem B4728617 : Blo 932582 4728617 := bstep (se 2 (by rfl) ⟨1773231, by rfl⟩ : syracuseStep 4728617 = 3546463) B3546463
theorem B2991919 : Blo 932582 2991919 := bstep (se 1 (by rfl) ⟨2243939, by rfl⟩ : syracuseStep 2991919 = 4487879) B4487879
theorem B3155759 : Blo 932582 3155759 := bstep (se 1 (by rfl) ⟨2366819, by rfl⟩ : syracuseStep 3155759 = 4733639) B4733639
theorem B4729427 : Blo 932582 4729427 := bstep (se 1 (by rfl) ⟨3547070, by rfl⟩ : syracuseStep 4729427 = 7094141) B7094141
theorem B3844691 : Blo 932582 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B2370131 : Blo 932582 2370131 := bstep (se 1 (by rfl) ⟨1777598, by rfl⟩ : syracuseStep 2370131 = 3555197) B3555197
theorem B2665543 : Blo 932582 2665543 := bstep (se 1 (by rfl) ⟨1999157, by rfl⟩ : syracuseStep 2665543 = 3998315) B3998315
theorem B7089281 : Blo 932582 7089281 := bstep (se 2 (by rfl) ⟨2658480, by rfl⟩ : syracuseStep 7089281 = 5316961) B5316961
theorem B3550337 : Blo 932582 3550337 := bstep (se 2 (by rfl) ⟨1331376, by rfl⟩ : syracuseStep 3550337 = 2662753) B2662753
theorem B1518761 : Blo 932582 1518761 := bstep (se 2 (by rfl) ⟨569535, by rfl⟩ : syracuseStep 1518761 = 1139071) B1139071
theorem B57454541 : Blo 932582 57454541 := bstep (se 3 (by rfl) ⟨10772726, by rfl⟩ : syracuseStep 57454541 = 21545453) B21545453
theorem B3846599 : Blo 932582 3846599 := bstep (se 1 (by rfl) ⟨2884949, by rfl⟩ : syracuseStep 3846599 = 5769899) B5769899
theorem B2699833 : Blo 932582 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B6402725 : Blo 932582 6402725 := bstep (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) B1200511
theorem B4731695 : Blo 932582 4731695 := bstep (se 1 (by rfl) ⟨3548771, by rfl⟩ : syracuseStep 4731695 = 7097543) B7097543
theorem B5321609 : Blo 932582 5321609 := bstep (se 2 (by rfl) ⟨1995603, by rfl⟩ : syracuseStep 5321609 = 3991207) B3991207
theorem B3552295 : Blo 932582 3552295 := bstep (se 1 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 3552295 = 5328443) B5328443
theorem B15938855 : Blo 932582 15938855 := bstep (se 1 (by rfl) ⟨11954141, by rfl⟩ : syracuseStep 15938855 = 23908283) B23908283
theorem B18233225 : Blo 932582 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B7976879 : Blo 932582 7976879 := bstep (se 1 (by rfl) ⟨5982659, by rfl⟩ : syracuseStep 7976879 = 11965319) B11965319
theorem B582924347 : Blo 932582 582924347 := bstep (se 1 (by rfl) ⟨437193260, by rfl⟩ : syracuseStep 582924347 = 874386521) B874386521
theorem B3160295 : Blo 932582 3160295 := bstep (se 1 (by rfl) ⟨2370221, by rfl⟩ : syracuseStep 3160295 = 4740443) B4740443
theorem B3029405 : Blo 932582 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B4045319 : Blo 932582 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B5978711 : Blo 932582 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B932679 : Blo 932582 932679 := bstep (se 1 (by rfl) ⟨699509, by rfl⟩ : syracuseStep 932679 = 1399019) B1399019
theorem B4733801 : Blo 932582 4733801 := bstep (se 2 (by rfl) ⟨1775175, by rfl⟩ : syracuseStep 4733801 = 3550351) B3550351
theorem B932719 : Blo 932582 932719 := bstep (se 1 (by rfl) ⟨699539, by rfl⟩ : syracuseStep 932719 = 1399079) B1399079
theorem B932775 : Blo 932582 932775 := bstep (se 1 (by rfl) ⟨699581, by rfl⟩ : syracuseStep 932775 = 1399163) B1399163
theorem B932955 : Blo 932582 932955 := bstep (se 1 (by rfl) ⟨699716, by rfl⟩ : syracuseStep 932955 = 1399433) B1399433
theorem B3783827 : Blo 932582 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B933071 : Blo 932582 933071 := bstep (se 1 (by rfl) ⟨699803, by rfl⟩ : syracuseStep 933071 = 1399607) B1399607
theorem B933095 : Blo 932582 933095 := bstep (se 1 (by rfl) ⟨699821, by rfl⟩ : syracuseStep 933095 = 1399643) B1399643
theorem B933191 : Blo 932582 933191 := bstep (se 1 (by rfl) ⟨699893, by rfl⟩ : syracuseStep 933191 = 1399787) B1399787
theorem B5127547 : Blo 932582 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B933327 : Blo 932582 933327 := bstep (se 1 (by rfl) ⟨699995, by rfl⟩ : syracuseStep 933327 = 1399991) B1399991
theorem B933487 : Blo 932582 933487 := bstep (se 1 (by rfl) ⟨700115, by rfl⟩ : syracuseStep 933487 = 1400231) B1400231
theorem B933543 : Blo 932582 933543 := bstep (se 1 (by rfl) ⟨700157, by rfl⟩ : syracuseStep 933543 = 1400315) B1400315
theorem B933607 : Blo 932582 933607 := bstep (se 1 (by rfl) ⟨700205, by rfl⟩ : syracuseStep 933607 = 1400411) B1400411
theorem B933663 : Blo 932582 933663 := bstep (se 1 (by rfl) ⟨700247, by rfl⟩ : syracuseStep 933663 = 1400495) B1400495
theorem B10108759 : Blo 932582 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B933743 : Blo 932582 933743 := bstep (se 1 (by rfl) ⟨700307, by rfl⟩ : syracuseStep 933743 = 1400615) B1400615
theorem B933799 : Blo 932582 933799 := bstep (se 1 (by rfl) ⟨700349, by rfl⟩ : syracuseStep 933799 = 1400699) B1400699
theorem B934079 : Blo 932582 934079 := bstep (se 1 (by rfl) ⟨700559, by rfl⟩ : syracuseStep 934079 = 1401119) B1401119
theorem B934095 : Blo 932582 934095 := bstep (se 1 (by rfl) ⟨700571, by rfl⟩ : syracuseStep 934095 = 1401143) B1401143
theorem B934143 : Blo 932582 934143 := bstep (se 1 (by rfl) ⟨700607, by rfl⟩ : syracuseStep 934143 = 1401215) B1401215
theorem B934191 : Blo 932582 934191 := bstep (se 1 (by rfl) ⟨700643, by rfl⟩ : syracuseStep 934191 = 1401287) B1401287
theorem B934427 : Blo 932582 934427 := bstep (se 1 (by rfl) ⟨700820, by rfl⟩ : syracuseStep 934427 = 1401641) B1401641
theorem B934431 : Blo 932582 934431 := bstep (se 1 (by rfl) ⟨700823, by rfl⟩ : syracuseStep 934431 = 1401647) B1401647
theorem B934511 : Blo 932582 934511 := bstep (se 1 (by rfl) ⟨700883, by rfl⟩ : syracuseStep 934511 = 1401767) B1401767
theorem B3556001 : Blo 932582 3556001 := bstep (se 2 (by rfl) ⟨1333500, by rfl⟩ : syracuseStep 3556001 = 2667001) B2667001
theorem B934567 : Blo 932582 934567 := bstep (se 1 (by rfl) ⟨700925, by rfl⟩ : syracuseStep 934567 = 1401851) B1401851
theorem B934607 : Blo 932582 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B934687 : Blo 932582 934687 := bstep (se 1 (by rfl) ⟨701015, by rfl⟩ : syracuseStep 934687 = 1402031) B1402031
theorem B934959 : Blo 932582 934959 := bstep (se 1 (by rfl) ⟨701219, by rfl⟩ : syracuseStep 934959 = 1402439) B1402439
theorem B935023 : Blo 932582 935023 := bstep (se 1 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 935023 = 1402535) B1402535
theorem B935079 : Blo 932582 935079 := bstep (se 1 (by rfl) ⟨701309, by rfl⟩ : syracuseStep 935079 = 1402619) B1402619
theorem B935103 : Blo 932582 935103 := bstep (se 1 (by rfl) ⟨701327, by rfl⟩ : syracuseStep 935103 = 1402655) B1402655
theorem B935135 : Blo 932582 935135 := bstep (se 1 (by rfl) ⟨701351, by rfl⟩ : syracuseStep 935135 = 1402703) B1402703
theorem B2999531 : Blo 932582 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B935215 : Blo 932582 935215 := bstep (se 1 (by rfl) ⟨701411, by rfl⟩ : syracuseStep 935215 = 1402823) B1402823
theorem B935451 : Blo 932582 935451 := bstep (se 1 (by rfl) ⟨701588, by rfl⟩ : syracuseStep 935451 = 1403177) B1403177
theorem B1328671 : Blo 932582 1328671 := bstep (se 1 (by rfl) ⟨996503, by rfl⟩ : syracuseStep 1328671 = 1993007) B1993007
theorem B935455 : Blo 932582 935455 := bstep (se 1 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 935455 = 1403183) B1403183
theorem B54511223 : Blo 932582 54511223 := bstep (se 1 (by rfl) ⟨40883417, by rfl⟩ : syracuseStep 54511223 = 81766835) B81766835
theorem B935615 : Blo 932582 935615 := bstep (se 1 (by rfl) ⟨701711, by rfl⟩ : syracuseStep 935615 = 1403423) B1403423
theorem B935871 : Blo 932582 935871 := bstep (se 1 (by rfl) ⟨701903, by rfl⟩ : syracuseStep 935871 = 1403807) B1403807
theorem B1066975 : Blo 932582 1066975 := bstep (se 1 (by rfl) ⟨800231, by rfl⟩ : syracuseStep 1066975 = 1600463) B1600463
theorem B935903 : Blo 932582 935903 := bstep (se 1 (by rfl) ⟨701927, by rfl⟩ : syracuseStep 935903 = 1403855) B1403855
theorem B935963 : Blo 932582 935963 := bstep (se 1 (by rfl) ⟨701972, by rfl⟩ : syracuseStep 935963 = 1403945) B1403945
theorem B935967 : Blo 932582 935967 := bstep (se 1 (by rfl) ⟨701975, by rfl⟩ : syracuseStep 935967 = 1403951) B1403951
theorem B935983 : Blo 932582 935983 := bstep (se 1 (by rfl) ⟨701987, by rfl⟩ : syracuseStep 935983 = 1403975) B1403975
theorem B936159 : Blo 932582 936159 := bstep (se 1 (by rfl) ⟨702119, by rfl⟩ : syracuseStep 936159 = 1404239) B1404239
theorem B936219 : Blo 932582 936219 := bstep (se 1 (by rfl) ⟨702164, by rfl⟩ : syracuseStep 936219 = 1404329) B1404329
theorem B936319 : Blo 932582 936319 := bstep (se 1 (by rfl) ⟨702239, by rfl⟩ : syracuseStep 936319 = 1404479) B1404479
theorem B936495 : Blo 932582 936495 := bstep (se 1 (by rfl) ⟨702371, by rfl⟩ : syracuseStep 936495 = 1404743) B1404743
theorem B3689063 : Blo 932582 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B936551 : Blo 932582 936551 := bstep (se 1 (by rfl) ⟨702413, by rfl⟩ : syracuseStep 936551 = 1404827) B1404827
theorem B2247515 : Blo 932582 2247515 := bstep (se 1 (by rfl) ⟨1685636, by rfl⟩ : syracuseStep 2247515 = 3371273) B3371273
theorem B17943515 : Blo 932582 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B1330283 : Blo 932582 1330283 := bstep (se 1 (by rfl) ⟨997712, by rfl⟩ : syracuseStep 1330283 = 1995425) B1995425
theorem B1264747 : Blo 932582 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B15978221 : Blo 932582 15978221 := bstep (se 3 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 15978221 = 5991833) B5991833
theorem B5984351 : Blo 932582 5984351 := bstep (se 1 (by rfl) ⟨4488263, by rfl⟩ : syracuseStep 5984351 = 8976527) B8976527
theorem B1331849 : Blo 932582 1331849 := bstep (se 2 (by rfl) ⟨499443, by rfl⟩ : syracuseStep 1331849 = 998887) B998887
theorem B1496159 : Blo 932582 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B1332379 : Blo 932582 1332379 := bstep (se 1 (by rfl) ⟨999284, by rfl⟩ : syracuseStep 1332379 = 1998569) B1998569
theorem B17979191 : Blo 932582 17979191 := bstep (se 1 (by rfl) ⟨13484393, by rfl⟩ : syracuseStep 17979191 = 26968787) B26968787
theorem B7198541 : Blo 932582 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B2021203 : Blo 932582 2021203 := bstep (se 1 (by rfl) ⟨1515902, by rfl⟩ : syracuseStep 2021203 = 3031805) B3031805
theorem B1399199 : Blo 932582 1399199 := bstep (se 1 (by rfl) ⟨1049399, by rfl⟩ : syracuseStep 1399199 = 2098799) B2098799
theorem B5331359 : Blo 932582 5331359 := bstep (se 1 (by rfl) ⟨3998519, by rfl⟩ : syracuseStep 5331359 = 7997039) B7997039
theorem B7985627 : Blo 932582 7985627 := bstep (se 1 (by rfl) ⟨5989220, by rfl⟩ : syracuseStep 7985627 = 11978441) B11978441
theorem B1399271 : Blo 932582 1399271 := bstep (se 1 (by rfl) ⟨1049453, by rfl⟩ : syracuseStep 1399271 = 2098907) B2098907
theorem B1400015 : Blo 932582 1400015 := bstep (se 1 (by rfl) ⟨1050011, by rfl⟩ : syracuseStep 1400015 = 2100023) B2100023
theorem B1400135 : Blo 932582 1400135 := bstep (se 1 (by rfl) ⟨1050101, by rfl⟩ : syracuseStep 1400135 = 2100203) B2100203
theorem B13458797 : Blo 932582 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B1400297 : Blo 932582 1400297 := bstep (se 2 (by rfl) ⟨525111, by rfl⟩ : syracuseStep 1400297 = 1050223) B1050223
theorem B1400441 : Blo 932582 1400441 := bstep (se 2 (by rfl) ⟨525165, by rfl⟩ : syracuseStep 1400441 = 1050331) B1050331
theorem B1400687 : Blo 932582 1400687 := bstep (se 1 (by rfl) ⟨1050515, by rfl⟩ : syracuseStep 1400687 = 2101031) B2101031
theorem B5333273 : Blo 932582 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B8970527 : Blo 932582 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B1401371 : Blo 932582 1401371 := bstep (se 1 (by rfl) ⟨1051028, by rfl⟩ : syracuseStep 1401371 = 2102057) B2102057
theorem B1401551 : Blo 932582 1401551 := bstep (se 1 (by rfl) ⟨1051163, by rfl⟩ : syracuseStep 1401551 = 2102327) B2102327
theorem B1499855 : Blo 932582 1499855 := bstep (se 1 (by rfl) ⟨1124891, by rfl⟩ : syracuseStep 1499855 = 2249783) B2249783
theorem B1401563 : Blo 932582 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B7103375 : Blo 932582 7103375 := bstep (se 1 (by rfl) ⟨5327531, by rfl⟩ : syracuseStep 7103375 = 10655063) B10655063
theorem B1401977 : Blo 932582 1401977 := bstep (se 2 (by rfl) ⟨525741, by rfl⟩ : syracuseStep 1401977 = 1051483) B1051483
theorem B23029069 : Blo 932582 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B6481367 : Blo 932582 6481367 := bstep (se 1 (by rfl) ⟨4861025, by rfl⟩ : syracuseStep 6481367 = 9722051) B9722051
theorem B10643399 : Blo 932582 10643399 := bstep (se 1 (by rfl) ⟨7982549, by rfl⟩ : syracuseStep 10643399 = 15965099) B15965099
theorem B1402847 : Blo 932582 1402847 := bstep (se 1 (by rfl) ⟨1052135, by rfl⟩ : syracuseStep 1402847 = 2104271) B2104271
theorem B1402859 : Blo 932582 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B6580217 : Blo 932582 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B1402907 : Blo 932582 1402907 := bstep (se 1 (by rfl) ⟨1052180, by rfl⟩ : syracuseStep 1402907 = 2104361) B2104361
theorem B6744161 : Blo 932582 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B1403273 : Blo 932582 1403273 := bstep (se 2 (by rfl) ⟨526227, by rfl⟩ : syracuseStep 1403273 = 1052455) B1052455
theorem B3992095 : Blo 932582 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B1404215 : Blo 932582 1404215 := bstep (se 1 (by rfl) ⟨1053161, by rfl⟩ : syracuseStep 1404215 = 2106323) B2106323
theorem B1994195 : Blo 932582 1994195 := bstep (se 1 (by rfl) ⟨1495646, by rfl⟩ : syracuseStep 1994195 = 2991293) B2991293
theorem B1404383 : Blo 932582 1404383 := bstep (se 1 (by rfl) ⟨1053287, by rfl⟩ : syracuseStep 1404383 = 2106575) B2106575
theorem B1404599 : Blo 932582 1404599 := bstep (se 1 (by rfl) ⟨1053449, by rfl⟩ : syracuseStep 1404599 = 2106899) B2106899
theorem B17985341 : Blo 932582 17985341 := bstep (se 3 (by rfl) ⟨3372251, by rfl⟩ : syracuseStep 17985341 = 6744503) B6744503
theorem B1404809 : Blo 932582 1404809 := bstep (se 2 (by rfl) ⟨526803, by rfl⟩ : syracuseStep 1404809 = 1053607) B1053607
theorem B10121345 : Blo 932582 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B4485401 : Blo 932582 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B2848063 : Blo 932582 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B49903057 : Blo 932582 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B3996317 : Blo 932582 3996317 := bstep (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) B1498619
theorem B1998047 : Blo 932582 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B10649231 : Blo 932582 10649231 := bstep (se 1 (by rfl) ⟨7986923, by rfl⟩ : syracuseStep 10649231 = 15973847) B15973847
theorem B5046097 : Blo 932582 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B1998713 : Blo 932582 1998713 := bstep (se 2 (by rfl) ⟨749517, by rfl⟩ : syracuseStep 1998713 = 1499035) B1499035
theorem B21594593 : Blo 932582 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B1180327 : Blo 932582 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B23921405 : Blo 932582 23921405 := bstep (se 3 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 23921405 = 8970527) B8970527
theorem B8520511 : Blo 932582 8520511 := bstep (se 1 (by rfl) ⟨6390383, by rfl⟩ : syracuseStep 8520511 = 12780767) B12780767
theorem B1180651 : Blo 932582 1180651 := bstep (se 1 (by rfl) ⟨885488, by rfl⟩ : syracuseStep 1180651 = 1770977) B1770977
theorem B3147497 : Blo 932582 3147497 := bstep (se 2 (by rfl) ⟨1180311, by rfl⟩ : syracuseStep 3147497 = 2360623) B2360623
theorem B1574633 : Blo 932582 1574633 := bstep (se 2 (by rfl) ⟨590487, by rfl⟩ : syracuseStep 1574633 = 1180975) B1180975
theorem B2459375 : Blo 932582 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B30705425 : Blo 932582 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B3999613 : Blo 932582 3999613 := bstep (se 3 (by rfl) ⟨749927, by rfl⟩ : syracuseStep 3999613 = 1499855) B1499855
theorem B45549539 : Blo 932582 45549539 := bstep (se 1 (by rfl) ⟨34162154, by rfl⟩ : syracuseStep 45549539 = 68324309) B68324309
theorem B11962343 : Blo 932582 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B1771561 : Blo 932582 1771561 := bstep (se 2 (by rfl) ⟨664335, by rfl⟩ : syracuseStep 1771561 = 1328671) B1328671
theorem B3999887 : Blo 932582 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B2361575 : Blo 932582 2361575 := bstep (se 1 (by rfl) ⟨1771181, by rfl⟩ : syracuseStep 2361575 = 3542363) B3542363
theorem B2361595 : Blo 932582 2361595 := bstep (se 1 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 2361595 = 3542393) B3542393
theorem B1181947 : Blo 932582 1181947 := bstep (se 1 (by rfl) ⟨886460, by rfl⟩ : syracuseStep 1181947 = 1772921) B1772921
theorem B2361737 : Blo 932582 2361737 := bstep (se 2 (by rfl) ⟨885651, by rfl⟩ : syracuseStep 2361737 = 1771303) B1771303
theorem B10652147 : Blo 932582 10652147 := bstep (se 1 (by rfl) ⟨7989110, by rfl⟩ : syracuseStep 10652147 = 15978221) B15978221
theorem B3148307 : Blo 932582 3148307 := bstep (se 1 (by rfl) ⟨2361230, by rfl⟩ : syracuseStep 3148307 = 4722461) B4722461
theorem B1182367 : Blo 932582 1182367 := bstep (se 1 (by rfl) ⟨886775, by rfl⟩ : syracuseStep 1182367 = 1773551) B1773551
theorem B1051303 : Blo 932582 1051303 := bstep (se 1 (by rfl) ⟨788477, by rfl⟩ : syracuseStep 1051303 = 1576955) B1576955
theorem B2099951 : Blo 932582 2099951 := bstep (se 1 (by rfl) ⟨1574963, by rfl⟩ : syracuseStep 2099951 = 3149927) B3149927
theorem B1051375 : Blo 932582 1051375 := bstep (se 1 (by rfl) ⟨788531, by rfl⟩ : syracuseStep 1051375 = 1577063) B1577063
theorem B4721489 : Blo 932582 4721489 := bstep (se 2 (by rfl) ⟨1770558, by rfl⟩ : syracuseStep 4721489 = 3541117) B3541117
theorem B2100329 : Blo 932582 2100329 := bstep (se 2 (by rfl) ⟨787623, by rfl⟩ : syracuseStep 2100329 = 1575247) B1575247
theorem B1051879 : Blo 932582 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B7998749 : Blo 932582 7998749 := bstep (se 3 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 7998749 = 2999531) B2999531
theorem B1576415 : Blo 932582 1576415 := bstep (se 1 (by rfl) ⟨1182311, by rfl⟩ : syracuseStep 1576415 = 2364623) B2364623
theorem B2100959 : Blo 932582 2100959 := bstep (se 1 (by rfl) ⟨1575719, by rfl⟩ : syracuseStep 2100959 = 3151439) B3151439
theorem B2363327 : Blo 932582 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B2101211 : Blo 932582 2101211 := bstep (se 1 (by rfl) ⟨1575908, by rfl⟩ : syracuseStep 2101211 = 3151817) B3151817
theorem B1183835 : Blo 932582 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B2101391 : Blo 932582 2101391 := bstep (se 1 (by rfl) ⟨1576043, by rfl⟩ : syracuseStep 2101391 = 3152087) B3152087
theorem B2101481 : Blo 932582 2101481 := bstep (se 2 (by rfl) ⟨788055, by rfl⟩ : syracuseStep 2101481 = 1576111) B1576111
theorem B145363261 : Blo 932582 145363261 := bstep (se 3 (by rfl) ⟨27255611, by rfl⟩ : syracuseStep 145363261 = 54511223) B54511223
theorem B2101751 : Blo 932582 2101751 := bstep (se 1 (by rfl) ⟨1576313, by rfl⟩ : syracuseStep 2101751 = 3152627) B3152627
theorem B9114119 : Blo 932582 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B2364511 : Blo 932582 2364511 := bstep (se 1 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 2364511 = 3546767) B3546767
theorem B1184959 : Blo 932582 1184959 := bstep (se 1 (by rfl) ⟨888719, by rfl⟩ : syracuseStep 1184959 = 1777439) B1777439
theorem B2102507 : Blo 932582 2102507 := bstep (se 1 (by rfl) ⟨1576880, by rfl⟩ : syracuseStep 2102507 = 3153761) B3153761
theorem B4265567 : Blo 932582 4265567 := bstep (se 1 (by rfl) ⟨3199175, by rfl⟩ : syracuseStep 4265567 = 6398351) B6398351
theorem B2103119 : Blo 932582 2103119 := bstep (se 1 (by rfl) ⟨1577339, by rfl⟩ : syracuseStep 2103119 = 3154679) B3154679
theorem B1579081 : Blo 932582 1579081 := bstep (se 2 (by rfl) ⟨592155, by rfl⟩ : syracuseStep 1579081 = 1184311) B1184311
theorem B2103407 : Blo 932582 2103407 := bstep (se 1 (by rfl) ⟨1577555, by rfl⟩ : syracuseStep 2103407 = 3155111) B3155111
theorem B2103479 : Blo 932582 2103479 := bstep (se 1 (by rfl) ⟨1577609, by rfl⟩ : syracuseStep 2103479 = 3155219) B3155219
theorem B10099201 : Blo 932582 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B3152411 : Blo 932582 3152411 := bstep (se 1 (by rfl) ⟨2364308, by rfl⟩ : syracuseStep 3152411 = 4728617) B4728617
theorem B2103839 : Blo 932582 2103839 := bstep (se 1 (by rfl) ⟨1577879, by rfl⟩ : syracuseStep 2103839 = 3155759) B3155759
theorem B2366081 : Blo 932582 2366081 := bstep (se 2 (by rfl) ⟨887280, by rfl⟩ : syracuseStep 2366081 = 1774561) B1774561
theorem B4496107 : Blo 932582 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B1579817 : Blo 932582 1579817 := bstep (se 2 (by rfl) ⟨592431, by rfl⟩ : syracuseStep 1579817 = 1184863) B1184863
theorem B1776505 : Blo 932582 1776505 := bstep (se 2 (by rfl) ⟨666189, by rfl⟩ : syracuseStep 1776505 = 1332379) B1332379
theorem B3152951 : Blo 932582 3152951 := bstep (se 1 (by rfl) ⟨2364713, by rfl⟩ : syracuseStep 3152951 = 4729427) B4729427
theorem B2563127 : Blo 932582 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B1580087 : Blo 932582 1580087 := bstep (se 1 (by rfl) ⟨1185065, by rfl⟩ : syracuseStep 1580087 = 2370131) B2370131
theorem B4726025 : Blo 932582 4726025 := bstep (se 2 (by rfl) ⟨1772259, by rfl⟩ : syracuseStep 4726025 = 3544519) B3544519
theorem B4726187 : Blo 932582 4726187 := bstep (se 1 (by rfl) ⟨3544640, by rfl⟩ : syracuseStep 4726187 = 7089281) B7089281
theorem B2366891 : Blo 932582 2366891 := bstep (se 1 (by rfl) ⟨1775168, by rfl⟩ : syracuseStep 2366891 = 3550337) B3550337
theorem B9576089 : Blo 932582 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B2694937 : Blo 932582 2694937 := bstep (se 2 (by rfl) ⟨1010601, by rfl⟩ : syracuseStep 2694937 = 2021203) B2021203
theorem B2990267 : Blo 932582 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B7086365 : Blo 932582 7086365 := bstep (se 3 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 7086365 = 2657387) B2657387
theorem B3547421 : Blo 932582 3547421 := bstep (se 3 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 3547421 = 1330283) B1330283
theorem B2564399 : Blo 932582 2564399 := bstep (se 1 (by rfl) ⟨1923299, by rfl⟩ : syracuseStep 2564399 = 3846599) B3846599
theorem B4268483 : Blo 932582 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B3154463 : Blo 932582 3154463 := bstep (se 1 (by rfl) ⟨2365847, by rfl⟩ : syracuseStep 3154463 = 4731695) B4731695
theorem B3547739 : Blo 932582 3547739 := bstep (se 1 (by rfl) ⟨2660804, by rfl⟩ : syracuseStep 3547739 = 5321609) B5321609
theorem B10625903 : Blo 932582 10625903 := bstep (se 1 (by rfl) ⟨7969427, by rfl⟩ : syracuseStep 10625903 = 15938855) B15938855
theorem B5317919 : Blo 932582 5317919 := bstep (se 1 (by rfl) ⟨3988439, by rfl⟩ : syracuseStep 5317919 = 7976879) B7976879
theorem B2106863 : Blo 932582 2106863 := bstep (se 1 (by rfl) ⟨1580147, by rfl⟩ : syracuseStep 2106863 = 3160295) B3160295
theorem B2696879 : Blo 932582 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B2664211 : Blo 932582 2664211 := bstep (se 1 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 2664211 = 3996317) B3996317
theorem B3155867 : Blo 932582 3155867 := bstep (se 1 (by rfl) ⟨2366900, by rfl⟩ : syracuseStep 3155867 = 4733801) B4733801
theorem B6728129 : Blo 932582 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B13478345 : Blo 932582 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B10791899 : Blo 932582 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B2370667 : Blo 932582 2370667 := bstep (se 1 (by rfl) ⟨1778000, by rfl⟩ : syracuseStep 2370667 = 3556001) B3556001
theorem B3551597 : Blo 932582 3551597 := bstep (se 3 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 3551597 = 1331849) B1331849
theorem B7975853 : Blo 932582 7975853 := bstep (se 3 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 7975853 = 2990945) B2990945
theorem B10663811 : Blo 932582 10663811 := bstep (se 1 (by rfl) ⟨7997858, by rfl⟩ : syracuseStep 10663811 = 15995717) B15995717
theorem B5322793 : Blo 932582 5322793 := bstep (se 2 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 5322793 = 3992095) B3992095
theorem B997439 : Blo 932582 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B4799027 : Blo 932582 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B7584455 : Blo 932582 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B3554057 : Blo 932582 3554057 := bstep (se 2 (by rfl) ⟨1332771, by rfl⟩ : syracuseStep 3554057 = 2665543) B2665543
theorem B1686329 : Blo 932582 1686329 := bstep (se 2 (by rfl) ⟨632373, by rfl⟩ : syracuseStep 1686329 = 1264747) B1264747
theorem B932799 : Blo 932582 932799 := bstep (se 1 (by rfl) ⟨699599, by rfl⟩ : syracuseStep 932799 = 1399199) B1399199
theorem B3554239 : Blo 932582 3554239 := bstep (se 1 (by rfl) ⟨2665679, by rfl⟩ : syracuseStep 3554239 = 5331359) B5331359
theorem B5323751 : Blo 932582 5323751 := bstep (se 1 (by rfl) ⟨3992813, by rfl⟩ : syracuseStep 5323751 = 7985627) B7985627
theorem B932847 : Blo 932582 932847 := bstep (se 1 (by rfl) ⟨699635, by rfl⟩ : syracuseStep 932847 = 1399271) B1399271
theorem B933343 : Blo 932582 933343 := bstep (se 1 (by rfl) ⟨700007, by rfl⟩ : syracuseStep 933343 = 1400015) B1400015
theorem B1687007 : Blo 932582 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B933423 : Blo 932582 933423 := bstep (se 1 (by rfl) ⟨700067, by rfl⟩ : syracuseStep 933423 = 1400135) B1400135
theorem B933531 : Blo 932582 933531 := bstep (se 1 (by rfl) ⟨700148, by rfl⟩ : syracuseStep 933531 = 1400297) B1400297
theorem B933627 : Blo 932582 933627 := bstep (se 1 (by rfl) ⟨700220, by rfl⟩ : syracuseStep 933627 = 1400441) B1400441
theorem B933791 : Blo 932582 933791 := bstep (se 1 (by rfl) ⟨700343, by rfl⟩ : syracuseStep 933791 = 1400687) B1400687
theorem B3555515 : Blo 932582 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B934247 : Blo 932582 934247 := bstep (se 1 (by rfl) ⟨700685, by rfl⟩ : syracuseStep 934247 = 1401371) B1401371
theorem B934367 : Blo 932582 934367 := bstep (se 1 (by rfl) ⟨700775, by rfl⟩ : syracuseStep 934367 = 1401551) B1401551
theorem B934375 : Blo 932582 934375 := bstep (se 1 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 934375 = 1401563) B1401563
theorem B6078995 : Blo 932582 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B4735583 : Blo 932582 4735583 := bstep (se 1 (by rfl) ⟨3551687, by rfl⟩ : syracuseStep 4735583 = 7103375) B7103375
theorem B934651 : Blo 932582 934651 := bstep (se 1 (by rfl) ⟨700988, by rfl⟩ : syracuseStep 934651 = 1401977) B1401977
theorem B8078413 : Blo 932582 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B7095599 : Blo 932582 7095599 := bstep (se 1 (by rfl) ⟨5321699, by rfl⟩ : syracuseStep 7095599 = 10643399) B10643399
theorem B935231 : Blo 932582 935231 := bstep (se 1 (by rfl) ⟨701423, by rfl⟩ : syracuseStep 935231 = 1402847) B1402847
theorem B935239 : Blo 932582 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B935271 : Blo 932582 935271 := bstep (se 1 (by rfl) ⟨701453, by rfl⟩ : syracuseStep 935271 = 1402907) B1402907
theorem B4736393 : Blo 932582 4736393 := bstep (se 2 (by rfl) ⟨1776147, by rfl⟩ : syracuseStep 4736393 = 3552295) B3552295
theorem B15943229 : Blo 932582 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B935515 : Blo 932582 935515 := bstep (se 1 (by rfl) ⟨701636, by rfl⟩ : syracuseStep 935515 = 1403273) B1403273
theorem B66537409 : Blo 932582 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B936143 : Blo 932582 936143 := bstep (se 1 (by rfl) ⟨702107, by rfl⟩ : syracuseStep 936143 = 1404215) B1404215
theorem B8964377 : Blo 932582 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B1329463 : Blo 932582 1329463 := bstep (se 1 (by rfl) ⟨997097, by rfl⟩ : syracuseStep 1329463 = 1994195) B1994195
theorem B936255 : Blo 932582 936255 := bstep (se 1 (by rfl) ⟨702191, by rfl⟩ : syracuseStep 936255 = 1404383) B1404383
theorem B936399 : Blo 932582 936399 := bstep (se 1 (by rfl) ⟨702299, by rfl⟩ : syracuseStep 936399 = 1404599) B1404599
theorem B936539 : Blo 932582 936539 := bstep (se 1 (by rfl) ⟨702404, by rfl⟩ : syracuseStep 936539 = 1404809) B1404809
theorem B5328125 : Blo 932582 5328125 := bstep (se 3 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 5328125 = 1998047) B1998047
theorem B388616231 : Blo 932582 388616231 := bstep (se 1 (by rfl) ⟨291462173, by rfl⟩ : syracuseStep 388616231 = 582924347) B582924347
theorem B6836729 : Blo 932582 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B5329901 : Blo 932582 5329901 := bstep (se 3 (by rfl) ⟨999356, by rfl⟩ : syracuseStep 5329901 = 1998713) B1998713
theorem B7099487 : Blo 932582 7099487 := bstep (se 1 (by rfl) ⟨5324615, by rfl⟩ : syracuseStep 7099487 = 10649231) B10649231
theorem B5690533 : Blo 932582 5690533 := bstep (se 4 (by rfl) ⟨533487, by rfl⟩ : syracuseStep 5690533 = 1066975) B1066975
theorem B5331041 : Blo 932582 5331041 := bstep (se 2 (by rfl) ⟨1999140, by rfl⟩ : syracuseStep 5331041 = 3998281) B3998281
theorem B1398911 : Blo 932582 1398911 := bstep (se 1 (by rfl) ⟨1049183, by rfl⟩ : syracuseStep 1398911 = 2098367) B2098367
theorem B1399007 : Blo 932582 1399007 := bstep (se 1 (by rfl) ⟨1049255, by rfl⟩ : syracuseStep 1399007 = 2098511) B2098511
theorem B1399067 : Blo 932582 1399067 := bstep (se 1 (by rfl) ⟨1049300, by rfl⟩ : syracuseStep 1399067 = 2098601) B2098601
theorem B68344145 : Blo 932582 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B1399391 : Blo 932582 1399391 := bstep (se 1 (by rfl) ⟨1049543, by rfl⟩ : syracuseStep 1399391 = 2099087) B2099087
theorem B3365563 : Blo 932582 3365563 := bstep (se 1 (by rfl) ⟨2524172, by rfl⟩ : syracuseStep 3365563 = 5048345) B5048345
theorem B1399487 : Blo 932582 1399487 := bstep (se 1 (by rfl) ⟨1049615, by rfl⟩ : syracuseStep 1399487 = 2099231) B2099231
theorem B1399529 : Blo 932582 1399529 := bstep (se 2 (by rfl) ⟨524823, by rfl⟩ : syracuseStep 1399529 = 1049647) B1049647
theorem B1399655 : Blo 932582 1399655 := bstep (se 1 (by rfl) ⟨1049741, by rfl⟩ : syracuseStep 1399655 = 2099483) B2099483
theorem B1399721 : Blo 932582 1399721 := bstep (se 2 (by rfl) ⟨524895, by rfl⟩ : syracuseStep 1399721 = 1049791) B1049791
theorem B1399871 : Blo 932582 1399871 := bstep (se 1 (by rfl) ⟨1049903, by rfl⟩ : syracuseStep 1399871 = 2099807) B2099807
theorem B1399913 : Blo 932582 1399913 := bstep (se 2 (by rfl) ⟨524967, by rfl⟩ : syracuseStep 1399913 = 1049935) B1049935
theorem B1400039 : Blo 932582 1400039 := bstep (se 1 (by rfl) ⟨1050029, by rfl⟩ : syracuseStep 1400039 = 2100059) B2100059
theorem B1498343 : Blo 932582 1498343 := bstep (se 1 (by rfl) ⟨1123757, by rfl⟩ : syracuseStep 1498343 = 2247515) B2247515
theorem B1400543 : Blo 932582 1400543 := bstep (se 1 (by rfl) ⟨1050407, by rfl⟩ : syracuseStep 1400543 = 2100815) B2100815
theorem B3989225 : Blo 932582 3989225 := bstep (se 2 (by rfl) ⟨1495959, by rfl⟩ : syracuseStep 3989225 = 2991919) B2991919
theorem B1400873 : Blo 932582 1400873 := bstep (se 2 (by rfl) ⟨525327, by rfl⟩ : syracuseStep 1400873 = 1050655) B1050655
theorem B3989567 : Blo 932582 3989567 := bstep (se 1 (by rfl) ⟨2992175, by rfl⟩ : syracuseStep 3989567 = 5984351) B5984351
theorem B1400903 : Blo 932582 1400903 := bstep (se 1 (by rfl) ⟨1050677, by rfl⟩ : syracuseStep 1400903 = 2101355) B2101355
theorem B1400939 : Blo 932582 1400939 := bstep (se 1 (by rfl) ⟨1050704, by rfl⟩ : syracuseStep 1400939 = 2101409) B2101409
theorem B1401023 : Blo 932582 1401023 := bstep (se 1 (by rfl) ⟨1050767, by rfl⟩ : syracuseStep 1401023 = 2101535) B2101535
theorem B1401209 : Blo 932582 1401209 := bstep (se 2 (by rfl) ⟨525453, by rfl⟩ : syracuseStep 1401209 = 1050907) B1050907
theorem B1401503 : Blo 932582 1401503 := bstep (se 1 (by rfl) ⟨1051127, by rfl⟩ : syracuseStep 1401503 = 2102255) B2102255
theorem B1401839 : Blo 932582 1401839 := bstep (se 1 (by rfl) ⟨1051379, by rfl⟩ : syracuseStep 1401839 = 2102759) B2102759
theorem B1401947 : Blo 932582 1401947 := bstep (se 1 (by rfl) ⟨1051460, by rfl⟩ : syracuseStep 1401947 = 2102921) B2102921
theorem B1401959 : Blo 932582 1401959 := bstep (se 1 (by rfl) ⟨1051469, by rfl⟩ : syracuseStep 1401959 = 2102939) B2102939
theorem B11986127 : Blo 932582 11986127 := bstep (se 1 (by rfl) ⟨8989595, by rfl⟩ : syracuseStep 11986127 = 17979191) B17979191
theorem B1402091 : Blo 932582 1402091 := bstep (se 1 (by rfl) ⟨1051568, by rfl⟩ : syracuseStep 1402091 = 2103137) B2103137
theorem B1402223 : Blo 932582 1402223 := bstep (se 1 (by rfl) ⟨1051667, by rfl⟩ : syracuseStep 1402223 = 2103335) B2103335
theorem B1402343 : Blo 932582 1402343 := bstep (se 1 (by rfl) ⟨1051757, by rfl⟩ : syracuseStep 1402343 = 2103515) B2103515
theorem B1402475 : Blo 932582 1402475 := bstep (se 1 (by rfl) ⟨1051856, by rfl⟩ : syracuseStep 1402475 = 2103713) B2103713
theorem B1402523 : Blo 932582 1402523 := bstep (se 1 (by rfl) ⟨1051892, by rfl⟩ : syracuseStep 1402523 = 2103785) B2103785
theorem B1402745 : Blo 932582 1402745 := bstep (se 2 (by rfl) ⟨526029, by rfl⟩ : syracuseStep 1402745 = 1052059) B1052059
theorem B8972531 : Blo 932582 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B1403495 : Blo 932582 1403495 := bstep (se 1 (by rfl) ⟨1052621, by rfl⟩ : syracuseStep 1403495 = 2105243) B2105243
theorem B1403771 : Blo 932582 1403771 := bstep (se 1 (by rfl) ⟨1052828, by rfl⟩ : syracuseStep 1403771 = 2105657) B2105657
theorem B1404041 : Blo 932582 1404041 := bstep (se 2 (by rfl) ⟨526515, by rfl⟩ : syracuseStep 1404041 = 1053031) B1053031
theorem B6057143 : Blo 932582 6057143 := bstep (se 1 (by rfl) ⟨4542857, by rfl⟩ : syracuseStep 6057143 = 9085715) B9085715
theorem B1404095 : Blo 932582 1404095 := bstep (se 1 (by rfl) ⟨1053071, by rfl⟩ : syracuseStep 1404095 = 2106143) B2106143
theorem B2846107 : Blo 932582 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B3599777 : Blo 932582 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B4320911 : Blo 932582 4320911 := bstep (se 1 (by rfl) ⟨3240683, by rfl⟩ : syracuseStep 4320911 = 6481367) B6481367
theorem B4484803 : Blo 932582 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B1404635 : Blo 932582 1404635 := bstep (se 1 (by rfl) ⟨1053476, by rfl⟩ : syracuseStep 1404635 = 2106953) B2106953
theorem B4386811 : Blo 932582 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B3797417 : Blo 932582 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B1012507 : Blo 932582 1012507 := bstep (se 1 (by rfl) ⟨759380, by rfl⟩ : syracuseStep 1012507 = 1518761) B1518761
theorem B11990227 : Blo 932582 11990227 := bstep (se 1 (by rfl) ⟨8992670, by rfl⟩ : syracuseStep 11990227 = 17985341) B17985341
theorem B38303027 : Blo 932582 38303027 := bstep (se 1 (by rfl) ⟨28727270, by rfl⟩ : syracuseStep 38303027 = 57454541) B57454541
theorem B6747563 : Blo 932582 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B12155483 : Blo 932582 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B2522551 : Blo 932582 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1573769 : Blo 932582 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B2098331 : Blo 932582 2098331 := bstep (se 1 (by rfl) ⟨1573748, by rfl⟩ : syracuseStep 2098331 = 3147497) B3147497
theorem B1049755 : Blo 932582 1049755 := bstep (se 1 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 1049755 = 1574633) B1574633
theorem B1639583 : Blo 932582 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B1574201 : Blo 932582 1574201 := bstep (se 2 (by rfl) ⟨590325, by rfl⟩ : syracuseStep 1574201 = 1180651) B1180651
theorem B1574383 : Blo 932582 1574383 := bstep (se 1 (by rfl) ⟨1180787, by rfl⟩ : syracuseStep 1574383 = 2361575) B2361575
theorem B1574491 : Blo 932582 1574491 := bstep (se 1 (by rfl) ⟨1180868, by rfl⟩ : syracuseStep 1574491 = 2361737) B2361737
theorem B2098871 : Blo 932582 2098871 := bstep (se 1 (by rfl) ⟨1574153, by rfl⟩ : syracuseStep 2098871 = 3148307) B3148307
theorem B3147659 : Blo 932582 3147659 := bstep (se 1 (by rfl) ⟨2360744, by rfl⟩ : syracuseStep 3147659 = 4721489) B4721489
theorem B1050943 : Blo 932582 1050943 := bstep (se 1 (by rfl) ⟨788207, by rfl⟩ : syracuseStep 1050943 = 1576415) B1576415
theorem B1575551 : Blo 932582 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B2362081 : Blo 932582 2362081 := bstep (se 2 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 2362081 = 1771561) B1771561
theorem B3148793 : Blo 932582 3148793 := bstep (se 2 (by rfl) ⟨1180797, by rfl⟩ : syracuseStep 3148793 = 2361595) B2361595
theorem B1575929 : Blo 932582 1575929 := bstep (se 2 (by rfl) ⟨590973, by rfl⟩ : syracuseStep 1575929 = 1181947) B1181947
theorem B1772617 : Blo 932582 1772617 := bstep (se 2 (by rfl) ⟨664731, by rfl⟩ : syracuseStep 1772617 = 1329463) B1329463
theorem B1576489 : Blo 932582 1576489 := bstep (se 2 (by rfl) ⟨591183, by rfl⟩ : syracuseStep 1576489 = 1182367) B1182367
theorem B2101607 : Blo 932582 2101607 := bstep (se 1 (by rfl) ⟨1576205, by rfl⟩ : syracuseStep 2101607 = 3152411) B3152411
theorem B1577387 : Blo 932582 1577387 := bstep (se 1 (by rfl) ⟨1183040, by rfl⟩ : syracuseStep 1577387 = 2366081) B2366081
theorem B1053211 : Blo 932582 1053211 := bstep (se 1 (by rfl) ⟨789908, by rfl⟩ : syracuseStep 1053211 = 1579817) B1579817
theorem B2101967 : Blo 932582 2101967 := bstep (se 1 (by rfl) ⟨1576475, by rfl⟩ : syracuseStep 2101967 = 3152951) B3152951
theorem B1053391 : Blo 932582 1053391 := bstep (se 1 (by rfl) ⟨790043, by rfl⟩ : syracuseStep 1053391 = 1580087) B1580087
theorem B3150683 : Blo 932582 3150683 := bstep (se 1 (by rfl) ⟨2363012, by rfl⟩ : syracuseStep 3150683 = 4726025) B4726025
theorem B3150791 : Blo 932582 3150791 := bstep (se 1 (by rfl) ⟨2363093, by rfl⟩ : syracuseStep 3150791 = 4726187) B4726187
theorem B1577927 : Blo 932582 1577927 := bstep (se 1 (by rfl) ⟨1183445, by rfl⟩ : syracuseStep 1577927 = 2366891) B2366891
theorem B2659483 : Blo 932582 2659483 := bstep (se 1 (by rfl) ⟨1994612, by rfl⟩ : syracuseStep 2659483 = 3989225) B3989225
theorem B2659711 : Blo 932582 2659711 := bstep (se 1 (by rfl) ⟨1994783, by rfl⟩ : syracuseStep 2659711 = 3989567) B3989567
theorem B2659837 : Blo 932582 2659837 := bstep (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) B997439
theorem B4724243 : Blo 932582 4724243 := bstep (se 1 (by rfl) ⟨3543182, by rfl⟩ : syracuseStep 4724243 = 7086365) B7086365
theorem B2364947 : Blo 932582 2364947 := bstep (se 1 (by rfl) ⟨1773710, by rfl⟩ : syracuseStep 2364947 = 3547421) B3547421
theorem B1709599 : Blo 932582 1709599 := bstep (se 1 (by rfl) ⟨1282199, by rfl⟩ : syracuseStep 1709599 = 2564399) B2564399
theorem B2102975 : Blo 932582 2102975 := bstep (se 1 (by rfl) ⟨1577231, by rfl⟩ : syracuseStep 2102975 = 3154463) B3154463
theorem B2365159 : Blo 932582 2365159 := bstep (se 1 (by rfl) ⟨1773869, by rfl⟩ : syracuseStep 2365159 = 3547739) B3547739
theorem B7083935 : Blo 932582 7083935 := bstep (se 1 (by rfl) ⟨5312951, by rfl⟩ : syracuseStep 7083935 = 10625903) B10625903
theorem B3545279 : Blo 932582 3545279 := bstep (se 1 (by rfl) ⟨2658959, by rfl⟩ : syracuseStep 3545279 = 5317919) B5317919
theorem B2103911 : Blo 932582 2103911 := bstep (se 1 (by rfl) ⟨1577933, by rfl⟩ : syracuseStep 2103911 = 3155867) B3155867
theorem B3152681 : Blo 932582 3152681 := bstep (se 2 (by rfl) ⟨1182255, by rfl⟩ : syracuseStep 3152681 = 2364511) B2364511
theorem B1579945 : Blo 932582 1579945 := bstep (se 2 (by rfl) ⟨592479, by rfl⟩ : syracuseStep 1579945 = 1184959) B1184959
theorem B8985563 : Blo 932582 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B4038095 : Blo 932582 4038095 := bstep (se 1 (by rfl) ⟨3028571, by rfl⟩ : syracuseStep 4038095 = 6057143) B6057143
theorem B15179237 : Blo 932582 15179237 := bstep (se 4 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 15179237 = 2846107) B2846107
theorem B2399851 : Blo 932582 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B2105441 : Blo 932582 2105441 := bstep (se 2 (by rfl) ⟨789540, by rfl⟩ : syracuseStep 2105441 = 1579081) B1579081
theorem B2367731 : Blo 932582 2367731 := bstep (se 1 (by rfl) ⟨1775798, by rfl⟩ : syracuseStep 2367731 = 3551597) B3551597
theorem B2531611 : Blo 932582 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B5317235 : Blo 932582 5317235 := bstep (se 1 (by rfl) ⟨3987926, by rfl⟩ : syracuseStep 5317235 = 7975853) B7975853
theorem B25535351 : Blo 932582 25535351 := bstep (se 1 (by rfl) ⟨19151513, by rfl⟩ : syracuseStep 25535351 = 38303027) B38303027
theorem B4498375 : Blo 932582 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B2368673 : Blo 932582 2368673 := bstep (se 2 (by rfl) ⟨888252, by rfl⟩ : syracuseStep 2368673 = 1776505) B1776505
theorem B8103655 : Blo 932582 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B5056303 : Blo 932582 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B2369371 : Blo 932582 2369371 := bstep (se 1 (by rfl) ⟨1777028, by rfl⟩ : syracuseStep 2369371 = 3554057) B3554057
theorem B1124219 : Blo 932582 1124219 := bstep (se 1 (by rfl) ⟨843164, by rfl⟩ : syracuseStep 1124219 = 1686329) B1686329
theorem B3549167 : Blo 932582 3549167 := bstep (se 1 (by rfl) ⟨2661875, by rfl⟩ : syracuseStep 3549167 = 5323751) B5323751
theorem B1124671 : Blo 932582 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B2370343 : Blo 932582 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B3156893 : Blo 932582 3156893 := bstep (se 3 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 3156893 = 1183835) B1183835
theorem B14396395 : Blo 932582 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B3157055 : Blo 932582 3157055 := bstep (se 1 (by rfl) ⟨2367791, by rfl⟩ : syracuseStep 3157055 = 4735583) B4735583
theorem B27340021 : Blo 932582 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B4730399 : Blo 932582 4730399 := bstep (se 1 (by rfl) ⟨3547799, by rfl⟩ : syracuseStep 4730399 = 7095599) B7095599
theorem B3157595 : Blo 932582 3157595 := bstep (se 1 (by rfl) ⟨2368196, by rfl⟩ : syracuseStep 3157595 = 4736393) B4736393
theorem B10628819 : Blo 932582 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B18231277 : Blo 932582 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B7974895 : Blo 932582 7974895 := bstep (se 1 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 7974895 = 11962343) B11962343
theorem B2666591 : Blo 932582 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B5976251 : Blo 932582 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B3552083 : Blo 932582 3552083 := bstep (se 1 (by rfl) ⟨2664062, by rfl⟩ : syracuseStep 3552083 = 5328125) B5328125
theorem B3552281 : Blo 932582 3552281 := bstep (se 2 (by rfl) ⟨1332105, by rfl⟩ : syracuseStep 3552281 = 2664211) B2664211
theorem B88716545 : Blo 932582 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B259077487 : Blo 932582 259077487 := bstep (se 1 (by rfl) ⟨194308115, by rfl⟩ : syracuseStep 259077487 = 388616231) B388616231
theorem B6076079 : Blo 932582 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B3553267 : Blo 932582 3553267 := bstep (se 1 (by rfl) ⟨2664950, by rfl⟩ : syracuseStep 3553267 = 5329901) B5329901
theorem B4732991 : Blo 932582 4732991 := bstep (se 1 (by rfl) ⟨3549743, by rfl⟩ : syracuseStep 4732991 = 7099487) B7099487
theorem B3554027 : Blo 932582 3554027 := bstep (se 1 (by rfl) ⟨2665520, by rfl⟩ : syracuseStep 3554027 = 5331041) B5331041
theorem B932607 : Blo 932582 932607 := bstep (se 1 (by rfl) ⟨699455, by rfl⟩ : syracuseStep 932607 = 1398911) B1398911
theorem B3160889 : Blo 932582 3160889 := bstep (se 2 (by rfl) ⟨1185333, by rfl⟩ : syracuseStep 3160889 = 2370667) B2370667
theorem B932671 : Blo 932582 932671 := bstep (se 1 (by rfl) ⟨699503, by rfl⟩ : syracuseStep 932671 = 1399007) B1399007
theorem B932711 : Blo 932582 932711 := bstep (se 1 (by rfl) ⟨699533, by rfl⟩ : syracuseStep 932711 = 1399067) B1399067
theorem B45562763 : Blo 932582 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B932927 : Blo 932582 932927 := bstep (se 1 (by rfl) ⟨699695, by rfl⟩ : syracuseStep 932927 = 1399391) B1399391
theorem B932991 : Blo 932582 932991 := bstep (se 1 (by rfl) ⟨699743, by rfl⟩ : syracuseStep 932991 = 1399487) B1399487
theorem B933019 : Blo 932582 933019 := bstep (se 1 (by rfl) ⟨699764, by rfl⟩ : syracuseStep 933019 = 1399529) B1399529
theorem B933103 : Blo 932582 933103 := bstep (se 1 (by rfl) ⟨699827, by rfl⟩ : syracuseStep 933103 = 1399655) B1399655
theorem B933147 : Blo 932582 933147 := bstep (se 1 (by rfl) ⟨699860, by rfl⟩ : syracuseStep 933147 = 1399721) B1399721
theorem B933247 : Blo 932582 933247 := bstep (se 1 (by rfl) ⟨699935, by rfl⟩ : syracuseStep 933247 = 1399871) B1399871
theorem B933275 : Blo 932582 933275 := bstep (se 1 (by rfl) ⟨699956, by rfl⟩ : syracuseStep 933275 = 1399913) B1399913
theorem B933359 : Blo 932582 933359 := bstep (se 1 (by rfl) ⟨700019, by rfl⟩ : syracuseStep 933359 = 1400039) B1400039
theorem B5979737 : Blo 932582 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B933695 : Blo 932582 933695 := bstep (se 1 (by rfl) ⟨700271, by rfl⟩ : syracuseStep 933695 = 1400543) B1400543
theorem B5849081 : Blo 932582 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B933915 : Blo 932582 933915 := bstep (se 1 (by rfl) ⟨700436, by rfl⟩ : syracuseStep 933915 = 1400873) B1400873
theorem B933935 : Blo 932582 933935 := bstep (se 1 (by rfl) ⟨700451, by rfl⟩ : syracuseStep 933935 = 1400903) B1400903
theorem B933959 : Blo 932582 933959 := bstep (se 1 (by rfl) ⟨700469, by rfl⟩ : syracuseStep 933959 = 1400939) B1400939
theorem B934015 : Blo 932582 934015 := bstep (se 1 (by rfl) ⟨700511, by rfl⟩ : syracuseStep 934015 = 1401023) B1401023
theorem B934139 : Blo 932582 934139 := bstep (se 1 (by rfl) ⟨700604, by rfl⟩ : syracuseStep 934139 = 1401209) B1401209
theorem B934335 : Blo 932582 934335 := bstep (se 1 (by rfl) ⟨700751, by rfl⟩ : syracuseStep 934335 = 1401503) B1401503
theorem B934559 : Blo 932582 934559 := bstep (se 1 (by rfl) ⟨700919, by rfl⟩ : syracuseStep 934559 = 1401839) B1401839
theorem B934631 : Blo 932582 934631 := bstep (se 1 (by rfl) ⟨700973, by rfl⟩ : syracuseStep 934631 = 1401947) B1401947
theorem B934639 : Blo 932582 934639 := bstep (se 1 (by rfl) ⟨700979, by rfl⟩ : syracuseStep 934639 = 1401959) B1401959
theorem B934727 : Blo 932582 934727 := bstep (se 1 (by rfl) ⟨701045, by rfl⟩ : syracuseStep 934727 = 1402091) B1402091
theorem B934815 : Blo 932582 934815 := bstep (se 1 (by rfl) ⟨701111, by rfl⟩ : syracuseStep 934815 = 1402223) B1402223
theorem B934895 : Blo 932582 934895 := bstep (se 1 (by rfl) ⟨701171, by rfl⟩ : syracuseStep 934895 = 1402343) B1402343
theorem B934983 : Blo 932582 934983 := bstep (se 1 (by rfl) ⟨701237, by rfl⟩ : syracuseStep 934983 = 1402475) B1402475
theorem B935015 : Blo 932582 935015 := bstep (se 1 (by rfl) ⟨701261, by rfl⟩ : syracuseStep 935015 = 1402523) B1402523
theorem B935163 : Blo 932582 935163 := bstep (se 1 (by rfl) ⟨701372, by rfl⟩ : syracuseStep 935163 = 1402745) B1402745
theorem B5981687 : Blo 932582 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B7587377 : Blo 932582 7587377 := bstep (se 2 (by rfl) ⟨2845266, by rfl⟩ : syracuseStep 7587377 = 5690533) B5690533
theorem B935663 : Blo 932582 935663 := bstep (se 1 (by rfl) ⟨701747, by rfl⟩ : syracuseStep 935663 = 1403495) B1403495
theorem B935847 : Blo 932582 935847 := bstep (se 1 (by rfl) ⟨701885, by rfl⟩ : syracuseStep 935847 = 1403771) B1403771
theorem B7194599 : Blo 932582 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B936027 : Blo 932582 936027 := bstep (se 1 (by rfl) ⟨702020, by rfl⟩ : syracuseStep 936027 = 1404041) B1404041
theorem B936063 : Blo 932582 936063 := bstep (se 1 (by rfl) ⟨702047, by rfl⟩ : syracuseStep 936063 = 1404095) B1404095
theorem B936423 : Blo 932582 936423 := bstep (se 1 (by rfl) ⟨702317, by rfl⟩ : syracuseStep 936423 = 1404635) B1404635
theorem B7097057 : Blo 932582 7097057 := bstep (se 2 (by rfl) ⟨2661396, by rfl⟩ : syracuseStep 7097057 = 5322793) B5322793
theorem B4738985 : Blo 932582 4738985 := bstep (se 2 (by rfl) ⟨1777119, by rfl⟩ : syracuseStep 4738985 = 3554239) B3554239
theorem B3199351 : Blo 932582 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B3363401 : Blo 932582 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B3593249 : Blo 932582 3593249 := bstep (se 2 (by rfl) ⟨1347468, by rfl⟩ : syracuseStep 3593249 = 2694937) B2694937
theorem B4052663 : Blo 932582 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B15947603 : Blo 932582 15947603 := bstep (se 1 (by rfl) ⟨11960702, by rfl⟩ : syracuseStep 15947603 = 23921405) B23921405
theorem B11360681 : Blo 932582 11360681 := bstep (se 2 (by rfl) ⟨4260255, by rfl⟩ : syracuseStep 11360681 = 8520511) B8520511
theorem B20470283 : Blo 932582 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B30366359 : Blo 932582 30366359 := bstep (se 1 (by rfl) ⟨22774769, by rfl⟩ : syracuseStep 30366359 = 45549539) B45549539
theorem B10771217 : Blo 932582 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B7101431 : Blo 932582 7101431 := bstep (se 1 (by rfl) ⟨5326073, by rfl⟩ : syracuseStep 7101431 = 10652147) B10652147
theorem B1399967 : Blo 932582 1399967 := bstep (se 1 (by rfl) ⟨1049975, by rfl⟩ : syracuseStep 1399967 = 2099951) B2099951
theorem B1400219 : Blo 932582 1400219 := bstep (se 1 (by rfl) ⟨1050164, by rfl⟩ : syracuseStep 1400219 = 2100329) B2100329
theorem B5332499 : Blo 932582 5332499 := bstep (se 1 (by rfl) ⟨3999374, by rfl⟩ : syracuseStep 5332499 = 7998749) B7998749
theorem B1400639 : Blo 932582 1400639 := bstep (se 1 (by rfl) ⟨1050479, by rfl⟩ : syracuseStep 1400639 = 2100959) B2100959
theorem B5332817 : Blo 932582 5332817 := bstep (se 2 (by rfl) ⟨1999806, by rfl⟩ : syracuseStep 5332817 = 3999613) B3999613
theorem B1400807 : Blo 932582 1400807 := bstep (se 1 (by rfl) ⟨1050605, by rfl⟩ : syracuseStep 1400807 = 2101211) B2101211
theorem B1400927 : Blo 932582 1400927 := bstep (se 1 (by rfl) ⟨1050695, by rfl⟩ : syracuseStep 1400927 = 2101391) B2101391
theorem B1400987 : Blo 932582 1400987 := bstep (se 1 (by rfl) ⟨1050740, by rfl⟩ : syracuseStep 1400987 = 2101481) B2101481
theorem B1401167 : Blo 932582 1401167 := bstep (se 1 (by rfl) ⟨1050875, by rfl⟩ : syracuseStep 1401167 = 2101751) B2101751
theorem B1401671 : Blo 932582 1401671 := bstep (se 1 (by rfl) ⟨1051253, by rfl⟩ : syracuseStep 1401671 = 2102507) B2102507
theorem B1401737 : Blo 932582 1401737 := bstep (se 2 (by rfl) ⟨525651, by rfl⟩ : syracuseStep 1401737 = 1051303) B1051303
theorem B1401833 : Blo 932582 1401833 := bstep (se 2 (by rfl) ⟨525687, by rfl⟩ : syracuseStep 1401833 = 1051375) B1051375
theorem B2843711 : Blo 932582 2843711 := bstep (se 1 (by rfl) ⟨2132783, by rfl⟩ : syracuseStep 2843711 = 4265567) B4265567
theorem B1402079 : Blo 932582 1402079 := bstep (se 1 (by rfl) ⟨1051559, by rfl⟩ : syracuseStep 1402079 = 2103119) B2103119
theorem B1402271 : Blo 932582 1402271 := bstep (se 1 (by rfl) ⟨1051703, by rfl⟩ : syracuseStep 1402271 = 2103407) B2103407
theorem B1402319 : Blo 932582 1402319 := bstep (se 1 (by rfl) ⟨1051739, by rfl⟩ : syracuseStep 1402319 = 2103479) B2103479
theorem B5400037 : Blo 932582 5400037 := bstep (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) B1012507
theorem B1402505 : Blo 932582 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B1402559 : Blo 932582 1402559 := bstep (se 1 (by rfl) ⟨1051919, by rfl⟩ : syracuseStep 1402559 = 2103839) B2103839
theorem B6384059 : Blo 932582 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B1993511 : Blo 932582 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B2845655 : Blo 932582 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B193817681 : Blo 932582 193817681 := bstep (se 2 (by rfl) ⟨72681630, by rfl⟩ : syracuseStep 193817681 = 145363261) B145363261
theorem B7990751 : Blo 932582 7990751 := bstep (se 1 (by rfl) ⟨5993063, by rfl⟩ : syracuseStep 7990751 = 11986127) B11986127
theorem B1404575 : Blo 932582 1404575 := bstep (se 1 (by rfl) ⟨1053431, by rfl⟩ : syracuseStep 1404575 = 2106863) B2106863
theorem B1797919 : Blo 932582 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B15986969 : Blo 932582 15986969 := bstep (se 2 (by rfl) ⟨5995113, by rfl⟩ : syracuseStep 15986969 = 11990227) B11990227
theorem B4485419 : Blo 932582 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B2880607 : Blo 932582 2880607 := bstep (se 1 (by rfl) ⟨2160455, by rfl⟩ : syracuseStep 2880607 = 4320911) B4320911
theorem B3995581 : Blo 932582 3995581 := bstep (se 3 (by rfl) ⟨749171, by rfl⟩ : syracuseStep 3995581 = 1498343) B1498343
theorem B13465601 : Blo 932582 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B4487417 : Blo 932582 4487417 := bstep (se 2 (by rfl) ⟨1682781, by rfl⟩ : syracuseStep 4487417 = 3365563) B3365563
theorem B5994809 : Blo 932582 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B7109207 : Blo 932582 7109207 := bstep (se 1 (by rfl) ⟨5331905, by rfl⟩ : syracuseStep 7109207 = 10663811) B10663811
theorem B3375481 : Blo 932582 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B1049179 : Blo 932582 1049179 := bstep (se 1 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 1049179 = 1573769) B1573769
theorem B1049467 : Blo 932582 1049467 := bstep (se 1 (by rfl) ⟨787100, by rfl⟩ : syracuseStep 1049467 = 1574201) B1574201
theorem B2098439 : Blo 932582 2098439 := bstep (se 1 (by rfl) ⟨1573829, by rfl⟩ : syracuseStep 2098439 = 3147659) B3147659
theorem B5997833 : Blo 932582 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B1050367 : Blo 932582 1050367 := bstep (se 1 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 1050367 = 1575551) B1575551
theorem B2099177 : Blo 932582 2099177 := bstep (se 2 (by rfl) ⟨787191, by rfl⟩ : syracuseStep 2099177 = 1574383) B1574383
theorem B2099195 : Blo 932582 2099195 := bstep (se 1 (by rfl) ⟨1574396, by rfl⟩ : syracuseStep 2099195 = 3148793) B3148793
theorem B1050619 : Blo 932582 1050619 := bstep (se 1 (by rfl) ⟨787964, by rfl⟩ : syracuseStep 1050619 = 1575929) B1575929
theorem B2099321 : Blo 932582 2099321 := bstep (se 2 (by rfl) ⟨787245, by rfl⟩ : syracuseStep 2099321 = 1574491) B1574491
theorem B1051591 : Blo 932582 1051591 := bstep (se 1 (by rfl) ⟨788693, by rfl⟩ : syracuseStep 1051591 = 1577387) B1577387
theorem B2100455 : Blo 932582 2100455 := bstep (se 1 (by rfl) ⟨1575341, by rfl⟩ : syracuseStep 2100455 = 3150683) B3150683
theorem B2100527 : Blo 932582 2100527 := bstep (se 1 (by rfl) ⟨1575395, by rfl⟩ : syracuseStep 2100527 = 3150791) B3150791
theorem B1051951 : Blo 932582 1051951 := bstep (se 1 (by rfl) ⟨788963, by rfl⟩ : syracuseStep 1051951 = 1577927) B1577927
theorem B2395499 : Blo 932582 2395499 := bstep (se 1 (by rfl) ⟨1796624, by rfl⟩ : syracuseStep 2395499 = 3593249) B3593249
theorem B3149441 : Blo 932582 3149441 := bstep (se 2 (by rfl) ⟨1181040, by rfl⟩ : syracuseStep 3149441 = 2362081) B2362081
theorem B3149495 : Blo 932582 3149495 := bstep (se 1 (by rfl) ⟨2362121, by rfl⟩ : syracuseStep 3149495 = 4724243) B4724243
theorem B1576631 : Blo 932582 1576631 := bstep (se 1 (by rfl) ⟨1182473, by rfl⟩ : syracuseStep 1576631 = 2364947) B2364947
theorem B4722623 : Blo 932582 4722623 := bstep (se 1 (by rfl) ⟨3541967, by rfl⟩ : syracuseStep 4722623 = 7083935) B7083935
theorem B2363489 : Blo 932582 2363489 := bstep (se 2 (by rfl) ⟨886308, by rfl⟩ : syracuseStep 2363489 = 1772617) B1772617
theorem B2363519 : Blo 932582 2363519 := bstep (se 1 (by rfl) ⟨1772639, by rfl⟩ : syracuseStep 2363519 = 3545279) B3545279
theorem B7573787 : Blo 932582 7573787 := bstep (se 1 (by rfl) ⟨5680340, by rfl⟩ : syracuseStep 7573787 = 11360681) B11360681
theorem B7180811 : Blo 932582 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B2101787 : Blo 932582 2101787 := bstep (se 1 (by rfl) ⟨1576340, by rfl⟩ : syracuseStep 2101787 = 3152681) B3152681
theorem B2101985 : Blo 932582 2101985 := bstep (se 2 (by rfl) ⟨788244, by rfl⟩ : syracuseStep 2101985 = 1576489) B1576489
theorem B2692063 : Blo 932582 2692063 := bstep (se 1 (by rfl) ⟨2019047, by rfl⟩ : syracuseStep 2692063 = 4038095) B4038095
theorem B1578487 : Blo 932582 1578487 := bstep (se 1 (by rfl) ⟨1183865, by rfl⟩ : syracuseStep 1578487 = 2367731) B2367731
theorem B3544823 : Blo 932582 3544823 := bstep (se 1 (by rfl) ⟨2658617, by rfl⟩ : syracuseStep 3544823 = 5317235) B5317235
theorem B4265801 : Blo 932582 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B1579115 : Blo 932582 1579115 := bstep (se 1 (by rfl) ⟨1184336, by rfl⟩ : syracuseStep 1579115 = 2368673) B2368673
theorem B2366111 : Blo 932582 2366111 := bstep (se 1 (by rfl) ⟨1774583, by rfl⟩ : syracuseStep 2366111 = 3549167) B3549167
theorem B3840809 : Blo 932582 3840809 := bstep (se 2 (by rfl) ⟨1440303, by rfl⟩ : syracuseStep 3840809 = 2880607) B2880607
theorem B3545977 : Blo 932582 3545977 := bstep (se 2 (by rfl) ⟨1329741, by rfl⟩ : syracuseStep 3545977 = 2659483) B2659483
theorem B3546281 : Blo 932582 3546281 := bstep (se 2 (by rfl) ⟨1329855, by rfl⟩ : syracuseStep 3546281 = 2659711) B2659711
theorem B2104595 : Blo 932582 2104595 := bstep (se 1 (by rfl) ⟨1578446, by rfl⟩ : syracuseStep 2104595 = 3156893) B3156893
theorem B3546449 : Blo 932582 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B2104703 : Blo 932582 2104703 := bstep (se 1 (by rfl) ⟨1578527, by rfl⟩ : syracuseStep 2104703 = 3157055) B3157055
theorem B129211787 : Blo 932582 129211787 := bstep (se 1 (by rfl) ⟨96908840, by rfl⟩ : syracuseStep 129211787 = 193817681) B193817681
theorem B5316029 : Blo 932582 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B3153545 : Blo 932582 3153545 := bstep (se 2 (by rfl) ⟨1182579, by rfl⟩ : syracuseStep 3153545 = 2365159) B2365159
theorem B3153599 : Blo 932582 3153599 := bstep (se 1 (by rfl) ⟨2365199, by rfl⟩ : syracuseStep 3153599 = 4730399) B4730399
theorem B2105063 : Blo 932582 2105063 := bstep (se 1 (by rfl) ⟨1578797, by rfl⟩ : syracuseStep 2105063 = 3157595) B3157595
theorem B7085879 : Blo 932582 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B1777727 : Blo 932582 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B10657979 : Blo 932582 10657979 := bstep (se 1 (by rfl) ⟨7993484, by rfl⟩ : syracuseStep 10657979 = 15986969) B15986969
theorem B2990279 : Blo 932582 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B2368055 : Blo 932582 2368055 := bstep (se 1 (by rfl) ⟨1776041, by rfl⟩ : syracuseStep 2368055 = 3552083) B3552083
theorem B2368187 : Blo 932582 2368187 := bstep (se 1 (by rfl) ⟨1776140, by rfl⟩ : syracuseStep 2368187 = 3552281) B3552281
theorem B2106593 : Blo 932582 2106593 := bstep (se 2 (by rfl) ⟨789972, by rfl⟩ : syracuseStep 2106593 = 1579945) B1579945
theorem B3155327 : Blo 932582 3155327 := bstep (se 1 (by rfl) ⟨2366495, by rfl⟩ : syracuseStep 3155327 = 4732991) B4732991
theorem B2991611 : Blo 932582 2991611 := bstep (se 1 (by rfl) ⟨2243708, by rfl⟩ : syracuseStep 2991611 = 4487417) B4487417
theorem B2369351 : Blo 932582 2369351 := bstep (se 1 (by rfl) ⟨1777013, by rfl⟩ : syracuseStep 2369351 = 3554027) B3554027
theorem B2107259 : Blo 932582 2107259 := bstep (se 1 (by rfl) ⟨1580444, by rfl⟩ : syracuseStep 2107259 = 3160889) B3160889
theorem B5058251 : Blo 932582 5058251 := bstep (se 1 (by rfl) ⟨3793688, by rfl⟩ : syracuseStep 5058251 = 7587377) B7587377
theorem B4796399 : Blo 932582 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B4731371 : Blo 932582 4731371 := bstep (se 1 (by rfl) ⟨3548528, by rfl⟩ : syracuseStep 4731371 = 7097057) B7097057
theorem B3159161 : Blo 932582 3159161 := bstep (se 2 (by rfl) ⟨1184685, by rfl⟩ : syracuseStep 3159161 = 2369371) B2369371
theorem B3159323 : Blo 932582 3159323 := bstep (se 1 (by rfl) ⟨2369492, by rfl⟩ : syracuseStep 3159323 = 4738985) B4738985
theorem B3160457 : Blo 932582 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B2701775 : Blo 932582 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B10631735 : Blo 932582 10631735 := bstep (se 1 (by rfl) ⟨7973801, by rfl⟩ : syracuseStep 10631735 = 15947603) B15947603
theorem B36453361 : Blo 932582 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B13646855 : Blo 932582 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B4734287 : Blo 932582 4734287 := bstep (se 1 (by rfl) ⟨3550715, by rfl⟩ : syracuseStep 4734287 = 7101431) B7101431
theorem B933311 : Blo 932582 933311 := bstep (se 1 (by rfl) ⟨699983, by rfl⟩ : syracuseStep 933311 = 1399967) B1399967
theorem B933479 : Blo 932582 933479 := bstep (se 1 (by rfl) ⟨700109, by rfl⟩ : syracuseStep 933479 = 1400219) B1400219
theorem B2997917 : Blo 932582 2997917 := bstep (se 3 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 2997917 = 1124219) B1124219
theorem B3554999 : Blo 932582 3554999 := bstep (se 1 (by rfl) ⟨2666249, by rfl⟩ : syracuseStep 3554999 = 5332499) B5332499
theorem B933759 : Blo 932582 933759 := bstep (se 1 (by rfl) ⟨700319, by rfl⟩ : syracuseStep 933759 = 1400639) B1400639
theorem B3555211 : Blo 932582 3555211 := bstep (se 1 (by rfl) ⟨2666408, by rfl⟩ : syracuseStep 3555211 = 5332817) B5332817
theorem B10633193 : Blo 932582 10633193 := bstep (se 2 (by rfl) ⟨3987447, by rfl⟩ : syracuseStep 10633193 = 7974895) B7974895
theorem B933871 : Blo 932582 933871 := bstep (se 1 (by rfl) ⟨700403, by rfl⟩ : syracuseStep 933871 = 1400807) B1400807
theorem B933951 : Blo 932582 933951 := bstep (se 1 (by rfl) ⟨700463, by rfl⟩ : syracuseStep 933951 = 1400927) B1400927
theorem B933991 : Blo 932582 933991 := bstep (se 1 (by rfl) ⟨700493, by rfl⟩ : syracuseStep 933991 = 1400987) B1400987
theorem B934111 : Blo 932582 934111 := bstep (se 1 (by rfl) ⟨700583, by rfl⟩ : syracuseStep 934111 = 1401167) B1401167
theorem B934447 : Blo 932582 934447 := bstep (se 1 (by rfl) ⟨700835, by rfl⟩ : syracuseStep 934447 = 1401671) B1401671
theorem B17023567 : Blo 932582 17023567 := bstep (se 1 (by rfl) ⟨12767675, by rfl⟩ : syracuseStep 17023567 = 25535351) B25535351
theorem B934491 : Blo 932582 934491 := bstep (se 1 (by rfl) ⟨700868, by rfl⟩ : syracuseStep 934491 = 1401737) B1401737
theorem B934555 : Blo 932582 934555 := bstep (se 1 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 934555 = 1401833) B1401833
theorem B934719 : Blo 932582 934719 := bstep (se 1 (by rfl) ⟨701039, by rfl⟩ : syracuseStep 934719 = 1402079) B1402079
theorem B934847 : Blo 932582 934847 := bstep (se 1 (by rfl) ⟨701135, by rfl⟩ : syracuseStep 934847 = 1402271) B1402271
theorem B934879 : Blo 932582 934879 := bstep (se 1 (by rfl) ⟨701159, by rfl⟩ : syracuseStep 934879 = 1402319) B1402319
theorem B935003 : Blo 932582 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B935039 : Blo 932582 935039 := bstep (se 1 (by rfl) ⟨701279, by rfl⟩ : syracuseStep 935039 = 1402559) B1402559
theorem B2279465 : Blo 932582 2279465 := bstep (se 2 (by rfl) ⟨854799, by rfl⟩ : syracuseStep 2279465 = 1709599) B1709599
theorem B5327167 : Blo 932582 5327167 := bstep (se 1 (by rfl) ⟨3995375, by rfl⟩ : syracuseStep 5327167 = 7990751) B7990751
theorem B936383 : Blo 932582 936383 := bstep (se 1 (by rfl) ⟨702287, by rfl⟩ : syracuseStep 936383 = 1404575) B1404575
theorem B5327441 : Blo 932582 5327441 := bstep (se 2 (by rfl) ⟨1997790, by rfl⟩ : syracuseStep 5327441 = 3995581) B3995581
theorem B4737689 : Blo 932582 4737689 := bstep (se 2 (by rfl) ⟨1776633, by rfl⟩ : syracuseStep 4737689 = 3553267) B3553267
theorem B3984167 : Blo 932582 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B12799205 : Blo 932582 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B4050719 : Blo 932582 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B9588901 : Blo 932582 9588901 := bstep (se 4 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 9588901 = 1797919) B1797919
theorem B4739471 : Blo 932582 4739471 := bstep (se 1 (by rfl) ⟨3554603, by rfl⟩ : syracuseStep 4739471 = 7109207) B7109207
theorem B3986491 : Blo 932582 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B1398887 : Blo 932582 1398887 := bstep (se 1 (by rfl) ⟨1049165, by rfl⟩ : syracuseStep 1398887 = 2098331) B2098331
theorem B3987791 : Blo 932582 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B1399247 : Blo 932582 1399247 := bstep (se 1 (by rfl) ⟨1049435, by rfl⟩ : syracuseStep 1399247 = 2098871) B2098871
theorem B8969069 : Blo 932582 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B1399673 : Blo 932582 1399673 := bstep (se 2 (by rfl) ⟨524877, by rfl⟩ : syracuseStep 1399673 = 1049755) B1049755
theorem B17488885 : Blo 932582 17488885 := bstep (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) B1639583
theorem B7200049 : Blo 932582 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B6741737 : Blo 932582 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B1401071 : Blo 932582 1401071 := bstep (se 1 (by rfl) ⟨1050803, by rfl⟩ : syracuseStep 1401071 = 2101607) B2101607
theorem B1401257 : Blo 932582 1401257 := bstep (se 2 (by rfl) ⟨525471, by rfl⟩ : syracuseStep 1401257 = 1050943) B1050943
theorem B1499561 : Blo 932582 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B1401311 : Blo 932582 1401311 := bstep (se 1 (by rfl) ⟨1050983, by rfl⟩ : syracuseStep 1401311 = 2101967) B2101967
theorem B1401983 : Blo 932582 1401983 := bstep (se 1 (by rfl) ⟨1051487, by rfl⟩ : syracuseStep 1401983 = 2102975) B2102975
theorem B19195193 : Blo 932582 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B1402607 : Blo 932582 1402607 := bstep (se 1 (by rfl) ⟨1051955, by rfl⟩ : syracuseStep 1402607 = 2103911) B2103911
theorem B20244239 : Blo 932582 20244239 := bstep (se 1 (by rfl) ⟨15183179, by rfl⟩ : syracuseStep 20244239 = 30366359) B30366359
theorem B5990375 : Blo 932582 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B10119491 : Blo 932582 10119491 := bstep (se 1 (by rfl) ⟨7589618, by rfl⟩ : syracuseStep 10119491 = 15179237) B15179237
theorem B24308369 : Blo 932582 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B1403627 : Blo 932582 1403627 := bstep (se 1 (by rfl) ⟨1052720, by rfl⟩ : syracuseStep 1403627 = 2105441) B2105441
theorem B1404281 : Blo 932582 1404281 := bstep (se 2 (by rfl) ⟨526605, by rfl⟩ : syracuseStep 1404281 = 1053211) B1053211
theorem B1895807 : Blo 932582 1895807 := bstep (se 1 (by rfl) ⟨1421855, by rfl⟩ : syracuseStep 1895807 = 2843711) B2843711
theorem B1404521 : Blo 932582 1404521 := bstep (se 2 (by rfl) ⟨526695, by rfl⟩ : syracuseStep 1404521 = 1053391) B1053391
theorem B4256039 : Blo 932582 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B345436649 : Blo 932582 345436649 := bstep (se 2 (by rfl) ⟨129538743, by rfl⟩ : syracuseStep 345436649 = 259077487) B259077487
theorem B1897103 : Blo 932582 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B59144363 : Blo 932582 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B43219493 : Blo 932582 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B8977067 : Blo 932582 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B3996539 : Blo 932582 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B30375175 : Blo 932582 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B3899387 : Blo 932582 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B3998555 : Blo 932582 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B2099627 : Blo 932582 2099627 := bstep (se 1 (by rfl) ⟨1574720, by rfl⟩ : syracuseStep 2099627 = 3149441) B3149441
theorem B2099663 : Blo 932582 2099663 := bstep (se 1 (by rfl) ⟨1574747, by rfl⟩ : syracuseStep 2099663 = 3149495) B3149495
theorem B1051087 : Blo 932582 1051087 := bstep (se 1 (by rfl) ⟨788315, by rfl⟩ : syracuseStep 1051087 = 1576631) B1576631
theorem B3148415 : Blo 932582 3148415 := bstep (se 1 (by rfl) ⟨2361311, by rfl⟩ : syracuseStep 3148415 = 4722623) B4722623
theorem B1575659 : Blo 932582 1575659 := bstep (se 1 (by rfl) ⟨1181744, by rfl⟩ : syracuseStep 1575659 = 2363489) B2363489
theorem B1575679 : Blo 932582 1575679 := bstep (se 1 (by rfl) ⟨1181759, by rfl⟩ : syracuseStep 1575679 = 2363519) B2363519
theorem B5049191 : Blo 932582 5049191 := bstep (se 1 (by rfl) ⟨3786893, by rfl⟩ : syracuseStep 5049191 = 7573787) B7573787
theorem B4787207 : Blo 932582 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B2363215 : Blo 932582 2363215 := bstep (se 1 (by rfl) ⟨1772411, by rfl⟩ : syracuseStep 2363215 = 3544823) B3544823
theorem B1052743 : Blo 932582 1052743 := bstep (se 1 (by rfl) ⟨789557, by rfl⟩ : syracuseStep 1052743 = 1579115) B1579115
theorem B2658527 : Blo 932582 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B1577407 : Blo 932582 1577407 := bstep (se 1 (by rfl) ⟨1183055, by rfl⟩ : syracuseStep 1577407 = 2366111) B2366111
theorem B2364187 : Blo 932582 2364187 := bstep (se 1 (by rfl) ⟨1773140, by rfl⟩ : syracuseStep 2364187 = 3546281) B3546281
theorem B2364299 : Blo 932582 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B3544019 : Blo 932582 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B2102363 : Blo 932582 2102363 := bstep (se 1 (by rfl) ⟨1576772, by rfl⟩ : syracuseStep 2102363 = 3153545) B3153545
theorem B2102399 : Blo 932582 2102399 := bstep (se 1 (by rfl) ⟨1576799, by rfl⟩ : syracuseStep 2102399 = 3153599) B3153599
theorem B4494491 : Blo 932582 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B4723919 : Blo 932582 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B12785201 : Blo 932582 12785201 := bstep (se 2 (by rfl) ⟨4794450, by rfl⟩ : syracuseStep 12785201 = 9588901) B9588901
theorem B1578703 : Blo 932582 1578703 := bstep (se 1 (by rfl) ⟨1184027, by rfl⟩ : syracuseStep 1578703 = 2368055) B2368055
theorem B1578791 : Blo 932582 1578791 := bstep (se 1 (by rfl) ⟨1184093, by rfl⟩ : syracuseStep 1578791 = 2368187) B2368187
theorem B2103551 : Blo 932582 2103551 := bstep (se 1 (by rfl) ⟨1577663, by rfl⟩ : syracuseStep 2103551 = 3155327) B3155327
theorem B1579567 : Blo 932582 1579567 := bstep (se 1 (by rfl) ⟨1184675, by rfl⟩ : syracuseStep 1579567 = 2369351) B2369351
theorem B5315321 : Blo 932582 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B2104649 : Blo 932582 2104649 := bstep (se 2 (by rfl) ⟨789243, by rfl⟩ : syracuseStep 2104649 = 1578487) B1578487
theorem B10624445 : Blo 932582 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B3154247 : Blo 932582 3154247 := bstep (se 1 (by rfl) ⟨2365685, by rfl⟩ : syracuseStep 3154247 = 4731371) B4731371
theorem B2106107 : Blo 932582 2106107 := bstep (se 1 (by rfl) ⟨1579580, by rfl⟩ : syracuseStep 2106107 = 3159161) B3159161
theorem B2106215 : Blo 932582 2106215 := bstep (se 1 (by rfl) ⟨1579661, by rfl⟩ : syracuseStep 2106215 = 3159323) B3159323
theorem B4727969 : Blo 932582 4727969 := bstep (se 2 (by rfl) ⟨1772988, by rfl⟩ : syracuseStep 4727969 = 3545977) B3545977
theorem B48604481 : Blo 932582 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B39429575 : Blo 932582 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B2106971 : Blo 932582 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B28812995 : Blo 932582 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B7087823 : Blo 932582 7087823 := bstep (se 1 (by rfl) ⟨5315867, by rfl⟩ : syracuseStep 7087823 = 10631735) B10631735
theorem B2664359 : Blo 932582 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B3156191 : Blo 932582 3156191 := bstep (se 1 (by rfl) ⟨2367143, by rfl⟩ : syracuseStep 3156191 = 4734287) B4734287
theorem B2369999 : Blo 932582 2369999 := bstep (se 1 (by rfl) ⟨1777499, by rfl⟩ : syracuseStep 2369999 = 3554999) B3554999
theorem B7088795 : Blo 932582 7088795 := bstep (se 1 (by rfl) ⟨5316596, by rfl⟩ : syracuseStep 7088795 = 10633193) B10633193
theorem B10398365 : Blo 932582 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B4500641 : Blo 932582 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B1519643 : Blo 932582 1519643 := bstep (se 1 (by rfl) ⟨1139732, by rfl⟩ : syracuseStep 1519643 = 2279465) B2279465
theorem B5058941 : Blo 932582 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B3551627 : Blo 932582 3551627 := bstep (se 1 (by rfl) ⟨2663720, by rfl⟩ : syracuseStep 3551627 = 5327441) B5327441
theorem B3158459 : Blo 932582 3158459 := bstep (se 1 (by rfl) ⟨2368844, by rfl⟩ : syracuseStep 3158459 = 4737689) B4737689
theorem B8532803 : Blo 932582 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B2700479 : Blo 932582 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B3159647 : Blo 932582 3159647 := bstep (se 1 (by rfl) ⟨2369735, by rfl⟩ : syracuseStep 3159647 = 4739471) B4739471
theorem B7977629 : Blo 932582 7977629 := bstep (se 3 (by rfl) ⟨1495805, by rfl⟩ : syracuseStep 7977629 = 2991611) B2991611
theorem B932591 : Blo 932582 932591 := bstep (se 1 (by rfl) ⟨699443, by rfl⟩ : syracuseStep 932591 = 1398887) B1398887
theorem B932831 : Blo 932582 932831 := bstep (se 1 (by rfl) ⟨699623, by rfl⟩ : syracuseStep 932831 = 1399247) B1399247
theorem B5979379 : Blo 932582 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B933115 : Blo 932582 933115 := bstep (se 1 (by rfl) ⟨699836, by rfl⟩ : syracuseStep 933115 = 1399673) B1399673
theorem B934047 : Blo 932582 934047 := bstep (se 1 (by rfl) ⟨700535, by rfl⟩ : syracuseStep 934047 = 1401071) B1401071
theorem B934171 : Blo 932582 934171 := bstep (se 1 (by rfl) ⟨700628, by rfl⟩ : syracuseStep 934171 = 1401257) B1401257
theorem B999707 : Blo 932582 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B934207 : Blo 932582 934207 := bstep (se 1 (by rfl) ⟨700655, by rfl⟩ : syracuseStep 934207 = 1401311) B1401311
theorem B934655 : Blo 932582 934655 := bstep (se 1 (by rfl) ⟨700991, by rfl⟩ : syracuseStep 934655 = 1401983) B1401983
theorem B12796795 : Blo 932582 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B935071 : Blo 932582 935071 := bstep (se 1 (by rfl) ⟨701303, by rfl⟩ : syracuseStep 935071 = 1402607) B1402607
theorem B3589417 : Blo 932582 3589417 := bstep (se 2 (by rfl) ⟨1346031, by rfl⟩ : syracuseStep 3589417 = 2692063) B2692063
theorem B16205579 : Blo 932582 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B935751 : Blo 932582 935751 := bstep (se 1 (by rfl) ⟨701813, by rfl⟩ : syracuseStep 935751 = 1403627) B1403627
theorem B10242157 : Blo 932582 10242157 := bstep (se 3 (by rfl) ⟨1920404, by rfl⟩ : syracuseStep 10242157 = 3840809) B3840809
theorem B936187 : Blo 932582 936187 := bstep (se 1 (by rfl) ⟨702140, by rfl⟩ : syracuseStep 936187 = 1404281) B1404281
theorem B1263871 : Blo 932582 1263871 := bstep (se 1 (by rfl) ⟨947903, by rfl⟩ : syracuseStep 1263871 = 1895807) B1895807
theorem B936347 : Blo 932582 936347 := bstep (se 1 (by rfl) ⟨702260, by rfl⟩ : syracuseStep 936347 = 1404521) B1404521
theorem B3197599 : Blo 932582 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B2837359 : Blo 932582 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B23318513 : Blo 932582 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B5984711 : Blo 932582 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B9097903 : Blo 932582 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B4740281 : Blo 932582 4740281 := bstep (se 2 (by rfl) ⟨1777605, by rfl⟩ : syracuseStep 4740281 = 3555211) B3555211
theorem B4740605 : Blo 932582 4740605 := bstep (se 3 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 4740605 = 1777727) B1777727
theorem B22698089 : Blo 932582 22698089 := bstep (se 2 (by rfl) ⟨8511783, by rfl⟩ : syracuseStep 22698089 = 17023567) B17023567
theorem B1398905 : Blo 932582 1398905 := bstep (se 2 (by rfl) ⟨524589, by rfl⟩ : syracuseStep 1398905 = 1049179) B1049179
theorem B1398959 : Blo 932582 1398959 := bstep (se 1 (by rfl) ⟨1049219, by rfl⟩ : syracuseStep 1398959 = 2098439) B2098439
theorem B1399289 : Blo 932582 1399289 := bstep (se 2 (by rfl) ⟨524733, by rfl⟩ : syracuseStep 1399289 = 1049467) B1049467
theorem B1399451 : Blo 932582 1399451 := bstep (se 1 (by rfl) ⟨1049588, by rfl⟩ : syracuseStep 1399451 = 2099177) B2099177
theorem B1399463 : Blo 932582 1399463 := bstep (se 1 (by rfl) ⟨1049597, by rfl⟩ : syracuseStep 1399463 = 2099195) B2099195
theorem B1399547 : Blo 932582 1399547 := bstep (se 1 (by rfl) ⟨1049660, by rfl⟩ : syracuseStep 1399547 = 2099321) B2099321
theorem B1400303 : Blo 932582 1400303 := bstep (se 1 (by rfl) ⟨1050227, by rfl⟩ : syracuseStep 1400303 = 2100455) B2100455
theorem B1400351 : Blo 932582 1400351 := bstep (se 1 (by rfl) ⟨1050263, by rfl⟩ : syracuseStep 1400351 = 2100527) B2100527
theorem B1400489 : Blo 932582 1400489 := bstep (se 2 (by rfl) ⟨525183, by rfl⟩ : syracuseStep 1400489 = 1050367) B1050367
theorem B1400825 : Blo 932582 1400825 := bstep (se 2 (by rfl) ⟨525309, by rfl⟩ : syracuseStep 1400825 = 1050619) B1050619
theorem B1401191 : Blo 932582 1401191 := bstep (se 1 (by rfl) ⟨1050893, by rfl⟩ : syracuseStep 1401191 = 2101787) B2101787
theorem B7102889 : Blo 932582 7102889 := bstep (se 2 (by rfl) ⟨2663583, by rfl⟩ : syracuseStep 7102889 = 5327167) B5327167
theorem B1401323 : Blo 932582 1401323 := bstep (se 1 (by rfl) ⟨1050992, by rfl⟩ : syracuseStep 1401323 = 2101985) B2101985
theorem B2843867 : Blo 932582 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B1402121 : Blo 932582 1402121 := bstep (se 2 (by rfl) ⟨525795, by rfl⟩ : syracuseStep 1402121 = 1051591) B1051591
theorem B1402601 : Blo 932582 1402601 := bstep (se 2 (by rfl) ⟨525975, by rfl⟩ : syracuseStep 1402601 = 1051951) B1051951
theorem B1403063 : Blo 932582 1403063 := bstep (se 1 (by rfl) ⟨1052297, by rfl⟩ : syracuseStep 1403063 = 2104595) B2104595
theorem B1403135 : Blo 932582 1403135 := bstep (se 1 (by rfl) ⟨1052351, by rfl⟩ : syracuseStep 1403135 = 2104703) B2104703
theorem B86141191 : Blo 932582 86141191 := bstep (se 1 (by rfl) ⟨64605893, by rfl⟩ : syracuseStep 86141191 = 129211787) B129211787
theorem B1403375 : Blo 932582 1403375 := bstep (se 1 (by rfl) ⟨1052531, by rfl⟩ : syracuseStep 1403375 = 2105063) B2105063
theorem B7105319 : Blo 932582 7105319 := bstep (se 1 (by rfl) ⟨5328989, by rfl⟩ : syracuseStep 7105319 = 10657979) B10657979
theorem B1993519 : Blo 932582 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B1404395 : Blo 932582 1404395 := bstep (se 1 (by rfl) ⟨1053296, by rfl⟩ : syracuseStep 1404395 = 2106593) B2106593
theorem B13496159 : Blo 932582 13496159 := bstep (se 1 (by rfl) ⟨10122119, by rfl⟩ : syracuseStep 13496159 = 20244239) B20244239
theorem B1404839 : Blo 932582 1404839 := bstep (se 1 (by rfl) ⟨1053629, by rfl⟩ : syracuseStep 1404839 = 2107259) B2107259
theorem B3993583 : Blo 932582 3993583 := bstep (se 1 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 3993583 = 5990375) B5990375
theorem B6746327 : Blo 932582 6746327 := bstep (se 1 (by rfl) ⟨5059745, by rfl⟩ : syracuseStep 6746327 = 10119491) B10119491
theorem B3372167 : Blo 932582 3372167 := bstep (se 1 (by rfl) ⟨2529125, by rfl⟩ : syracuseStep 3372167 = 5058251) B5058251
theorem B230291099 : Blo 932582 230291099 := bstep (se 1 (by rfl) ⟨172718324, by rfl⟩ : syracuseStep 230291099 = 345436649) B345436649
theorem B6387997 : Blo 932582 6387997 := bstep (se 3 (by rfl) ⟨1197749, by rfl⟩ : syracuseStep 6387997 = 2395499) B2395499
theorem B1801183 : Blo 932582 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B40500233 : Blo 932582 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B9600065 : Blo 932582 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B1998611 : Blo 932582 1998611 := bstep (se 1 (by rfl) ⟨1498958, by rfl⟩ : syracuseStep 1998611 = 2997917) B2997917
theorem B4785889 : Blo 932582 4785889 := bstep (se 2 (by rfl) ⟨1794708, by rfl⟩ : syracuseStep 4785889 = 3589417) B3589417
theorem B2098943 : Blo 932582 2098943 := bstep (se 1 (by rfl) ⟨1574207, by rfl⟩ : syracuseStep 2098943 = 3148415) B3148415
theorem B1050439 : Blo 932582 1050439 := bstep (se 1 (by rfl) ⟨787829, by rfl⟩ : syracuseStep 1050439 = 1575659) B1575659
theorem B1772351 : Blo 932582 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B114854921 : Blo 932582 114854921 := bstep (se 2 (by rfl) ⟨43070595, by rfl⟩ : syracuseStep 114854921 = 86141191) B86141191
theorem B1576199 : Blo 932582 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B2362679 : Blo 932582 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B3149279 : Blo 932582 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B2100905 : Blo 932582 2100905 := bstep (se 2 (by rfl) ⟨787839, by rfl⟩ : syracuseStep 2100905 = 1575679) B1575679
theorem B8523467 : Blo 932582 8523467 := bstep (se 1 (by rfl) ⟨6392600, by rfl⟩ : syracuseStep 8523467 = 12785201) B12785201
theorem B2658025 : Blo 932582 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B1052527 : Blo 932582 1052527 := bstep (se 1 (by rfl) ⟨789395, by rfl⟩ : syracuseStep 1052527 = 1578791) B1578791
theorem B3543547 : Blo 932582 3543547 := bstep (se 1 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 3543547 = 5315321) B5315321
theorem B7082963 : Blo 932582 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B3150953 : Blo 932582 3150953 := bstep (se 2 (by rfl) ⟨1181607, by rfl⟩ : syracuseStep 3150953 = 2363215) B2363215
theorem B2102831 : Blo 932582 2102831 := bstep (se 1 (by rfl) ⟨1577123, by rfl⟩ : syracuseStep 2102831 = 3154247) B3154247
theorem B2103209 : Blo 932582 2103209 := bstep (se 2 (by rfl) ⟨788703, by rfl⟩ : syracuseStep 2103209 = 1577407) B1577407
theorem B3151979 : Blo 932582 3151979 := bstep (se 1 (by rfl) ⟨2363984, by rfl⟩ : syracuseStep 3151979 = 4727969) B4727969
theorem B26286383 : Blo 932582 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B3152249 : Blo 932582 3152249 := bstep (se 2 (by rfl) ⟨1182093, by rfl⟩ : syracuseStep 3152249 = 2364187) B2364187
theorem B19208663 : Blo 932582 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B4725215 : Blo 932582 4725215 := bstep (se 1 (by rfl) ⟨3543911, by rfl⟩ : syracuseStep 4725215 = 7087823) B7087823
theorem B1776239 : Blo 932582 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B2104127 : Blo 932582 2104127 := bstep (se 1 (by rfl) ⟨1578095, by rfl⟩ : syracuseStep 2104127 = 3156191) B3156191
theorem B1579999 : Blo 932582 1579999 := bstep (se 1 (by rfl) ⟨1184999, by rfl⟩ : syracuseStep 1579999 = 2369999) B2369999
theorem B4725863 : Blo 932582 4725863 := bstep (se 1 (by rfl) ⟨3544397, by rfl⟩ : syracuseStep 4725863 = 7088795) B7088795
theorem B2104937 : Blo 932582 2104937 := bstep (se 2 (by rfl) ⟨789351, by rfl⟩ : syracuseStep 2104937 = 1578703) B1578703
theorem B4497551 : Blo 932582 4497551 := bstep (se 1 (by rfl) ⟨3373163, by rfl⟩ : syracuseStep 4497551 = 6746327) B6746327
theorem B2367751 : Blo 932582 2367751 := bstep (se 1 (by rfl) ⟨1775813, by rfl⟩ : syracuseStep 2367751 = 3551627) B3551627
theorem B2105639 : Blo 932582 2105639 := bstep (se 1 (by rfl) ⟨1579229, by rfl⟩ : syracuseStep 2105639 = 3158459) B3158459
theorem B12001709 : Blo 932582 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B2106089 : Blo 932582 2106089 := bstep (se 2 (by rfl) ⟨789783, by rfl⟩ : syracuseStep 2106089 = 1579567) B1579567
theorem B2106431 : Blo 932582 2106431 := bstep (se 1 (by rfl) ⟨1579823, by rfl⟩ : syracuseStep 2106431 = 3159647) B3159647
theorem B153527399 : Blo 932582 153527399 := bstep (se 1 (by rfl) ⟨115145549, by rfl⟩ : syracuseStep 153527399 = 230291099) B230291099
theorem B2401577 : Blo 932582 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B7972505 : Blo 932582 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B5318419 : Blo 932582 5318419 := bstep (se 1 (by rfl) ⟨3988814, by rfl⟩ : syracuseStep 5318419 = 7977629) B7977629
theorem B6400043 : Blo 932582 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B2665703 : Blo 932582 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B2665885 : Blo 932582 2665885 := bstep (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) B999707
theorem B3191471 : Blo 932582 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B22754141 : Blo 932582 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B15545675 : Blo 932582 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B1685161 : Blo 932582 1685161 := bstep (se 2 (by rfl) ⟨631935, by rfl⟩ : syracuseStep 1685161 = 1263871) B1263871
theorem B7583645 : Blo 932582 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B2996327 : Blo 932582 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B3160187 : Blo 932582 3160187 := bstep (se 1 (by rfl) ⟨2370140, by rfl⟩ : syracuseStep 3160187 = 4740281) B4740281
theorem B17053861 : Blo 932582 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B3160403 : Blo 932582 3160403 := bstep (se 1 (by rfl) ⟨2370302, by rfl⟩ : syracuseStep 3160403 = 4740605) B4740605
theorem B932603 : Blo 932582 932603 := bstep (se 1 (by rfl) ⟨699452, by rfl⟩ : syracuseStep 932603 = 1398905) B1398905
theorem B932639 : Blo 932582 932639 := bstep (se 1 (by rfl) ⟨699479, by rfl⟩ : syracuseStep 932639 = 1398959) B1398959
theorem B932859 : Blo 932582 932859 := bstep (se 1 (by rfl) ⟨699644, by rfl⟩ : syracuseStep 932859 = 1399289) B1399289
theorem B932967 : Blo 932582 932967 := bstep (se 1 (by rfl) ⟨699725, by rfl⟩ : syracuseStep 932967 = 1399451) B1399451
theorem B932975 : Blo 932582 932975 := bstep (se 1 (by rfl) ⟨699731, by rfl⟩ : syracuseStep 932975 = 1399463) B1399463
theorem B933031 : Blo 932582 933031 := bstep (se 1 (by rfl) ⟨699773, by rfl⟩ : syracuseStep 933031 = 1399547) B1399547
theorem B933535 : Blo 932582 933535 := bstep (se 1 (by rfl) ⟨700151, by rfl⟩ : syracuseStep 933535 = 1400303) B1400303
theorem B933567 : Blo 932582 933567 := bstep (se 1 (by rfl) ⟨700175, by rfl⟩ : syracuseStep 933567 = 1400351) B1400351
theorem B933659 : Blo 932582 933659 := bstep (se 1 (by rfl) ⟨700244, by rfl⟩ : syracuseStep 933659 = 1400489) B1400489
theorem B5324777 : Blo 932582 5324777 := bstep (se 2 (by rfl) ⟨1996791, by rfl⟩ : syracuseStep 5324777 = 3993583) B3993583
theorem B933883 : Blo 932582 933883 := bstep (se 1 (by rfl) ⟨700412, by rfl⟩ : syracuseStep 933883 = 1400825) B1400825
theorem B934127 : Blo 932582 934127 := bstep (se 1 (by rfl) ⟨700595, by rfl⟩ : syracuseStep 934127 = 1401191) B1401191
theorem B4735259 : Blo 932582 4735259 := bstep (se 1 (by rfl) ⟨3551444, by rfl⟩ : syracuseStep 4735259 = 7102889) B7102889
theorem B934215 : Blo 932582 934215 := bstep (se 1 (by rfl) ⟨700661, by rfl⟩ : syracuseStep 934215 = 1401323) B1401323
theorem B934747 : Blo 932582 934747 := bstep (se 1 (by rfl) ⟨701060, by rfl⟩ : syracuseStep 934747 = 1402121) B1402121
theorem B935067 : Blo 932582 935067 := bstep (se 1 (by rfl) ⟨701300, by rfl⟩ : syracuseStep 935067 = 1402601) B1402601
theorem B935375 : Blo 932582 935375 := bstep (se 1 (by rfl) ⟨701531, by rfl⟩ : syracuseStep 935375 = 1403063) B1403063
theorem B935423 : Blo 932582 935423 := bstep (se 1 (by rfl) ⟨701567, by rfl⟩ : syracuseStep 935423 = 1403135) B1403135
theorem B935583 : Blo 932582 935583 := bstep (se 1 (by rfl) ⟨701687, by rfl⟩ : syracuseStep 935583 = 1403375) B1403375
theorem B6932243 : Blo 932582 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B4736879 : Blo 932582 4736879 := bstep (se 1 (by rfl) ⟨3552659, by rfl⟩ : syracuseStep 4736879 = 7105319) B7105319
theorem B936263 : Blo 932582 936263 := bstep (se 1 (by rfl) ⟨702197, by rfl⟩ : syracuseStep 936263 = 1404395) B1404395
theorem B8997439 : Blo 932582 8997439 := bstep (se 1 (by rfl) ⟨6748079, by rfl⟩ : syracuseStep 8997439 = 13496159) B13496159
theorem B936559 : Blo 932582 936559 := bstep (se 1 (by rfl) ⟨702419, by rfl⟩ : syracuseStep 936559 = 1404839) B1404839
theorem B2248111 : Blo 932582 2248111 := bstep (se 1 (by rfl) ⟨1686083, by rfl⟩ : syracuseStep 2248111 = 3372167) B3372167
theorem B1332407 : Blo 932582 1332407 := bstep (se 1 (by rfl) ⟨999305, by rfl⟩ : syracuseStep 1332407 = 1998611) B1998611
theorem B13490509 : Blo 932582 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B10803719 : Blo 932582 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B1399751 : Blo 932582 1399751 := bstep (se 1 (by rfl) ⟨1049813, by rfl⟩ : syracuseStep 1399751 = 2099627) B2099627
theorem B1399775 : Blo 932582 1399775 := bstep (se 1 (by rfl) ⟨1049831, by rfl⟩ : syracuseStep 1399775 = 2099663) B2099663
theorem B3366127 : Blo 932582 3366127 := bstep (se 1 (by rfl) ⟨2524595, by rfl⟩ : syracuseStep 3366127 = 5049191) B5049191
theorem B13656209 : Blo 932582 13656209 := bstep (se 2 (by rfl) ⟨5121078, by rfl⟩ : syracuseStep 13656209 = 10242157) B10242157
theorem B3989807 : Blo 932582 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B7201277 : Blo 932582 7201277 := bstep (se 3 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 7201277 = 2700479) B2700479
theorem B1401449 : Blo 932582 1401449 := bstep (se 2 (by rfl) ⟨525543, by rfl⟩ : syracuseStep 1401449 = 1051087) B1051087
theorem B1401575 : Blo 932582 1401575 := bstep (se 1 (by rfl) ⟨1051181, by rfl⟩ : syracuseStep 1401575 = 2102363) B2102363
theorem B1401599 : Blo 932582 1401599 := bstep (se 1 (by rfl) ⟨1051199, by rfl⟩ : syracuseStep 1401599 = 2102399) B2102399
theorem B48522149 : Blo 932582 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B15132059 : Blo 932582 15132059 := bstep (se 1 (by rfl) ⟨11349044, by rfl⟩ : syracuseStep 15132059 = 22698089) B22698089
theorem B1402367 : Blo 932582 1402367 := bstep (se 1 (by rfl) ⟨1051775, by rfl⟩ : syracuseStep 1402367 = 2103551) B2103551
theorem B15132581 : Blo 932582 15132581 := bstep (se 4 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 15132581 = 2837359) B2837359
theorem B68249573 : Blo 932582 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B1403099 : Blo 932582 1403099 := bstep (se 1 (by rfl) ⟨1052324, by rfl⟩ : syracuseStep 1403099 = 2104649) B2104649
theorem B1403657 : Blo 932582 1403657 := bstep (se 2 (by rfl) ⟨526371, by rfl⟩ : syracuseStep 1403657 = 1052743) B1052743
theorem B1404071 : Blo 932582 1404071 := bstep (se 1 (by rfl) ⟨1053053, by rfl⟩ : syracuseStep 1404071 = 2106107) B2106107
theorem B1404143 : Blo 932582 1404143 := bstep (se 1 (by rfl) ⟨1053107, by rfl⟩ : syracuseStep 1404143 = 2106215) B2106215
theorem B32402987 : Blo 932582 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B1404647 : Blo 932582 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B1013095 : Blo 932582 1013095 := bstep (se 1 (by rfl) ⟨759821, by rfl⟩ : syracuseStep 1013095 = 1519643) B1519643
theorem B8517329 : Blo 932582 8517329 := bstep (se 2 (by rfl) ⟨3193998, by rfl⟩ : syracuseStep 8517329 = 6387997) B6387997
theorem B27000155 : Blo 932582 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B1181567 : Blo 932582 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B1050799 : Blo 932582 1050799 := bstep (se 1 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 1050799 = 1576199) B1576199
theorem B1575119 : Blo 932582 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B2099519 : Blo 932582 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B4721975 : Blo 932582 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B2100635 : Blo 932582 2100635 := bstep (se 1 (by rfl) ⟨1575476, by rfl⟩ : syracuseStep 2100635 = 3150953) B3150953
theorem B11996585 : Blo 932582 11996585 := bstep (se 2 (by rfl) ⟨4498719, by rfl⟩ : syracuseStep 11996585 = 8997439) B8997439
theorem B2101319 : Blo 932582 2101319 := bstep (se 1 (by rfl) ⟨1575989, by rfl⟩ : syracuseStep 2101319 = 3151979) B3151979
theorem B2101499 : Blo 932582 2101499 := bstep (se 1 (by rfl) ⟨1576124, by rfl⟩ : syracuseStep 2101499 = 3152249) B3152249
theorem B3150143 : Blo 932582 3150143 := bstep (se 1 (by rfl) ⟨2362607, by rfl⟩ : syracuseStep 3150143 = 4725215) B4725215
theorem B1184159 : Blo 932582 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B18485981 : Blo 932582 18485981 := bstep (se 3 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 18485981 = 6932243) B6932243
theorem B3150575 : Blo 932582 3150575 := bstep (se 1 (by rfl) ⟨2362931, by rfl⟩ : syracuseStep 3150575 = 4725863) B4725863
theorem B3544033 : Blo 932582 3544033 := bstep (se 2 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 3544033 = 2658025) B2658025
theorem B20223053 : Blo 932582 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B2659871 : Blo 932582 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B8001139 : Blo 932582 8001139 := bstep (se 1 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 8001139 = 12001709) B12001709
theorem B32348099 : Blo 932582 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B4724729 : Blo 932582 4724729 := bstep (se 2 (by rfl) ⟨1771773, by rfl⟩ : syracuseStep 4724729 = 3543547) B3543547
theorem B5315003 : Blo 932582 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B28809917 : Blo 932582 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B4266695 : Blo 932582 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B1777135 : Blo 932582 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B21601991 : Blo 932582 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B10363783 : Blo 932582 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B5678219 : Blo 932582 5678219 := bstep (se 1 (by rfl) ⟨4258664, by rfl⟩ : syracuseStep 5678219 = 8517329) B8517329
theorem B2106665 : Blo 932582 2106665 := bstep (se 2 (by rfl) ⟨789999, by rfl⟩ : syracuseStep 2106665 = 1579999) B1579999
theorem B2106791 : Blo 932582 2106791 := bstep (se 1 (by rfl) ⟨1580093, by rfl⟩ : syracuseStep 2106791 = 3160187) B3160187
theorem B2106935 : Blo 932582 2106935 := bstep (se 1 (by rfl) ⟨1580201, by rfl⟩ : syracuseStep 2106935 = 3160403) B3160403
theorem B18000103 : Blo 932582 18000103 := bstep (se 1 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 18000103 = 27000155) B27000155
theorem B3549851 : Blo 932582 3549851 := bstep (se 1 (by rfl) ⟨2662388, by rfl⟩ : syracuseStep 3549851 = 5324777) B5324777
theorem B3156839 : Blo 932582 3156839 := bstep (se 1 (by rfl) ⟨2367629, by rfl⟩ : syracuseStep 3156839 = 4735259) B4735259
theorem B3157001 : Blo 932582 3157001 := bstep (se 2 (by rfl) ⟨1183875, by rfl⟩ : syracuseStep 3157001 = 2367751) B2367751
theorem B36416557 : Blo 932582 36416557 := bstep (se 3 (by rfl) ⟨6828104, by rfl⟩ : syracuseStep 36416557 = 13656209) B13656209
theorem B3157919 : Blo 932582 3157919 := bstep (se 1 (by rfl) ⟨2368439, by rfl⟩ : syracuseStep 3157919 = 4736879) B4736879
theorem B7091225 : Blo 932582 7091225 := bstep (se 2 (by rfl) ⟨2659209, by rfl⟩ : syracuseStep 7091225 = 5318419) B5318419
theorem B5682311 : Blo 932582 5682311 := bstep (se 1 (by rfl) ⟨4261733, by rfl⟩ : syracuseStep 5682311 = 8523467) B8523467
theorem B3553085 : Blo 932582 3553085 := bstep (se 3 (by rfl) ⟨666203, by rfl⟩ : syracuseStep 3553085 = 1332407) B1332407
theorem B3554513 : Blo 932582 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B2997481 : Blo 932582 2997481 := bstep (se 2 (by rfl) ⟨1124055, by rfl⟩ : syracuseStep 2997481 = 2248111) B2248111
theorem B933167 : Blo 932582 933167 := bstep (se 1 (by rfl) ⟨699875, by rfl⟩ : syracuseStep 933167 = 1399751) B1399751
theorem B933183 : Blo 932582 933183 := bstep (se 1 (by rfl) ⟨699887, by rfl⟩ : syracuseStep 933183 = 1399775) B1399775
theorem B2998367 : Blo 932582 2998367 := bstep (se 1 (by rfl) ⟨2248775, by rfl⟩ : syracuseStep 2998367 = 4497551) B4497551
theorem B4800851 : Blo 932582 4800851 := bstep (se 1 (by rfl) ⟨3600638, by rfl⟩ : syracuseStep 4800851 = 7201277) B7201277
theorem B934299 : Blo 932582 934299 := bstep (se 1 (by rfl) ⟨700724, by rfl⟩ : syracuseStep 934299 = 1401449) B1401449
theorem B934383 : Blo 932582 934383 := bstep (se 1 (by rfl) ⟨700787, by rfl⟩ : syracuseStep 934383 = 1401575) B1401575
theorem B934399 : Blo 932582 934399 := bstep (se 1 (by rfl) ⟨700799, by rfl⟩ : syracuseStep 934399 = 1401599) B1401599
theorem B102351599 : Blo 932582 102351599 := bstep (se 1 (by rfl) ⟨76763699, by rfl⟩ : syracuseStep 102351599 = 153527399) B153527399
theorem B934911 : Blo 932582 934911 := bstep (se 1 (by rfl) ⟨701183, by rfl⟩ : syracuseStep 934911 = 1402367) B1402367
theorem B45499715 : Blo 932582 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B935399 : Blo 932582 935399 := bstep (se 1 (by rfl) ⟨701549, by rfl⟩ : syracuseStep 935399 = 1403099) B1403099
theorem B935771 : Blo 932582 935771 := bstep (se 1 (by rfl) ⟨701828, by rfl⟩ : syracuseStep 935771 = 1403657) B1403657
theorem B936047 : Blo 932582 936047 := bstep (se 1 (by rfl) ⟨702035, by rfl⟩ : syracuseStep 936047 = 1404071) B1404071
theorem B936095 : Blo 932582 936095 := bstep (se 1 (by rfl) ⟨702071, by rfl⟩ : syracuseStep 936095 = 1404143) B1404143
theorem B2246881 : Blo 932582 2246881 := bstep (se 2 (by rfl) ⟨842580, by rfl⟩ : syracuseStep 2246881 = 1685161) B1685161
theorem B936431 : Blo 932582 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B1399295 : Blo 932582 1399295 := bstep (se 1 (by rfl) ⟨1049471, by rfl⟩ : syracuseStep 1399295 = 2098943) B2098943
theorem B76569947 : Blo 932582 76569947 := bstep (se 1 (by rfl) ⟨57427460, by rfl⟩ : syracuseStep 76569947 = 114854921) B114854921
theorem B6381185 : Blo 932582 6381185 := bstep (se 2 (by rfl) ⟨2392944, by rfl⟩ : syracuseStep 6381185 = 4785889) B4785889
theorem B1400585 : Blo 932582 1400585 := bstep (se 2 (by rfl) ⟨525219, by rfl⟩ : syracuseStep 1400585 = 1050439) B1050439
theorem B1400603 : Blo 932582 1400603 := bstep (se 1 (by rfl) ⟨1050452, by rfl⟩ : syracuseStep 1400603 = 2100905) B2100905
theorem B1401887 : Blo 932582 1401887 := bstep (se 1 (by rfl) ⟨1051415, by rfl⟩ : syracuseStep 1401887 = 2102831) B2102831
theorem B1402139 : Blo 932582 1402139 := bstep (se 1 (by rfl) ⟨1051604, by rfl⟩ : syracuseStep 1402139 = 2103209) B2103209
theorem B17524255 : Blo 932582 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B12805775 : Blo 932582 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B1402751 : Blo 932582 1402751 := bstep (se 1 (by rfl) ⟨1052063, by rfl⟩ : syracuseStep 1402751 = 2104127) B2104127
theorem B1403291 : Blo 932582 1403291 := bstep (se 1 (by rfl) ⟨1052468, by rfl⟩ : syracuseStep 1403291 = 2104937) B2104937
theorem B1403369 : Blo 932582 1403369 := bstep (se 2 (by rfl) ⟨526263, by rfl⟩ : syracuseStep 1403369 = 1052527) B1052527
theorem B1403759 : Blo 932582 1403759 := bstep (se 1 (by rfl) ⟨1052819, by rfl⟩ : syracuseStep 1403759 = 2105639) B2105639
theorem B1404059 : Blo 932582 1404059 := bstep (se 1 (by rfl) ⟨1053044, by rfl⟩ : syracuseStep 1404059 = 2106089) B2106089
theorem B1404287 : Blo 932582 1404287 := bstep (se 1 (by rfl) ⟨1053215, by rfl⟩ : syracuseStep 1404287 = 2106431) B2106431
theorem B1601051 : Blo 932582 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B10088039 : Blo 932582 10088039 := bstep (se 1 (by rfl) ⟨7566029, by rfl⟩ : syracuseStep 10088039 = 15132059) B15132059
theorem B10088387 : Blo 932582 10088387 := bstep (se 1 (by rfl) ⟨7566290, by rfl⟩ : syracuseStep 10088387 = 15132581) B15132581
theorem B5403173 : Blo 932582 5403173 := bstep (se 4 (by rfl) ⟨506547, by rfl⟩ : syracuseStep 5403173 = 1013095) B1013095
theorem B22738481 : Blo 932582 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B17987345 : Blo 932582 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B2127647 : Blo 932582 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B15169427 : Blo 932582 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B1997551 : Blo 932582 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B4488169 : Blo 932582 4488169 := bstep (se 2 (by rfl) ⟨1683063, by rfl⟩ : syracuseStep 4488169 = 3366127) B3366127
theorem B1998911 : Blo 932582 1998911 := bstep (se 1 (by rfl) ⟨1499183, by rfl⟩ : syracuseStep 1998911 = 2998367) B2998367
theorem B1050079 : Blo 932582 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B23365673 : Blo 932582 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B3147983 : Blo 932582 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B7997723 : Blo 932582 7997723 := bstep (se 1 (by rfl) ⟨5998292, by rfl⟩ : syracuseStep 7997723 = 11996585) B11996585
theorem B2100095 : Blo 932582 2100095 := bstep (se 1 (by rfl) ⟨1575071, by rfl⟩ : syracuseStep 2100095 = 3150143) B3150143
theorem B15141917 : Blo 932582 15141917 := bstep (se 3 (by rfl) ⟨2839109, by rfl⟩ : syracuseStep 15141917 = 5678219) B5678219
theorem B12323987 : Blo 932582 12323987 := bstep (se 1 (by rfl) ⟨9242990, by rfl⟩ : syracuseStep 12323987 = 18485981) B18485981
theorem B2100383 : Blo 932582 2100383 := bstep (se 1 (by rfl) ⟨1575287, by rfl⟩ : syracuseStep 2100383 = 3150575) B3150575
theorem B1773247 : Blo 932582 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B10653605 : Blo 932582 10653605 := bstep (se 4 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 10653605 = 1997551) B1997551
theorem B3149819 : Blo 932582 3149819 := bstep (se 1 (by rfl) ⟨2362364, by rfl⟩ : syracuseStep 3149819 = 4724729) B4724729
theorem B3543335 : Blo 932582 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B19206611 : Blo 932582 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B5673725 : Blo 932582 5673725 := bstep (se 3 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 5673725 = 2127647) B2127647
theorem B3150845 : Blo 932582 3150845 := bstep (se 3 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 3150845 = 1181567) B1181567
theorem B4725377 : Blo 932582 4725377 := bstep (se 2 (by rfl) ⟨1772016, by rfl⟩ : syracuseStep 4725377 = 3544033) B3544033
theorem B2366567 : Blo 932582 2366567 := bstep (se 1 (by rfl) ⟨1774925, by rfl⟩ : syracuseStep 2366567 = 3549851) B3549851
theorem B11377853 : Blo 932582 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B2104559 : Blo 932582 2104559 := bstep (se 1 (by rfl) ⟨1578419, by rfl⟩ : syracuseStep 2104559 = 3156839) B3156839
theorem B2104667 : Blo 932582 2104667 := bstep (se 1 (by rfl) ⟨1578500, by rfl⟩ : syracuseStep 2104667 = 3157001) B3157001
theorem B6725359 : Blo 932582 6725359 := bstep (se 1 (by rfl) ⟨5044019, by rfl⟩ : syracuseStep 6725359 = 10088039) B10088039
theorem B2105279 : Blo 932582 2105279 := bstep (se 1 (by rfl) ⟨1578959, by rfl⟩ : syracuseStep 2105279 = 3157919) B3157919
theorem B6725591 : Blo 932582 6725591 := bstep (se 1 (by rfl) ⟨5044193, by rfl⟩ : syracuseStep 6725591 = 10088387) B10088387
theorem B4727483 : Blo 932582 4727483 := bstep (se 1 (by rfl) ⟨3545612, by rfl⟩ : syracuseStep 4727483 = 7091225) B7091225
theorem B2368723 : Blo 932582 2368723 := bstep (se 1 (by rfl) ⟨1776542, by rfl⟩ : syracuseStep 2368723 = 3553085) B3553085
theorem B4269469 : Blo 932582 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B17016493 : Blo 932582 17016493 := bstep (se 3 (by rfl) ⟨3190592, by rfl⟩ : syracuseStep 17016493 = 6381185) B6381185
theorem B2369513 : Blo 932582 2369513 := bstep (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) B1777135
theorem B2369675 : Blo 932582 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B68234399 : Blo 932582 68234399 := bstep (se 1 (by rfl) ⟨51175799, by rfl⟩ : syracuseStep 68234399 = 102351599) B102351599
theorem B3157757 : Blo 932582 3157757 := bstep (se 3 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 3157757 = 1184159) B1184159
theorem B2995841 : Blo 932582 2995841 := bstep (se 2 (by rfl) ⟨1123440, by rfl⟩ : syracuseStep 2995841 = 2246881) B2246881
theorem B24000137 : Blo 932582 24000137 := bstep (se 2 (by rfl) ⟨9000051, by rfl⟩ : syracuseStep 24000137 = 18000103) B18000103
theorem B13482035 : Blo 932582 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B932863 : Blo 932582 932863 := bstep (se 1 (by rfl) ⟨699647, by rfl⟩ : syracuseStep 932863 = 1399295) B1399295
theorem B14401327 : Blo 932582 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B933723 : Blo 932582 933723 := bstep (se 1 (by rfl) ⟨700292, by rfl⟩ : syracuseStep 933723 = 1400585) B1400585
theorem B86261597 : Blo 932582 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B933735 : Blo 932582 933735 := bstep (se 1 (by rfl) ⟨700301, by rfl⟩ : syracuseStep 933735 = 1400603) B1400603
theorem B934591 : Blo 932582 934591 := bstep (se 1 (by rfl) ⟨700943, by rfl⟩ : syracuseStep 934591 = 1401887) B1401887
theorem B934759 : Blo 932582 934759 := bstep (se 1 (by rfl) ⟨701069, by rfl⟩ : syracuseStep 934759 = 1402139) B1402139
theorem B8537183 : Blo 932582 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B935167 : Blo 932582 935167 := bstep (se 1 (by rfl) ⟨701375, by rfl⟩ : syracuseStep 935167 = 1402751) B1402751
theorem B935527 : Blo 932582 935527 := bstep (se 1 (by rfl) ⟨701645, by rfl⟩ : syracuseStep 935527 = 1403291) B1403291
theorem B935579 : Blo 932582 935579 := bstep (se 1 (by rfl) ⟨701684, by rfl⟩ : syracuseStep 935579 = 1403369) B1403369
theorem B935839 : Blo 932582 935839 := bstep (se 1 (by rfl) ⟨701879, by rfl⟩ : syracuseStep 935839 = 1403759) B1403759
theorem B936039 : Blo 932582 936039 := bstep (se 1 (by rfl) ⟨702029, by rfl⟩ : syracuseStep 936039 = 1404059) B1404059
theorem B10668185 : Blo 932582 10668185 := bstep (se 2 (by rfl) ⟨4000569, by rfl⟩ : syracuseStep 10668185 = 8001139) B8001139
theorem B936191 : Blo 932582 936191 := bstep (se 1 (by rfl) ⟨702143, by rfl⟩ : syracuseStep 936191 = 1404287) B1404287
theorem B3788207 : Blo 932582 3788207 := bstep (se 1 (by rfl) ⟨2841155, by rfl⟩ : syracuseStep 3788207 = 5682311) B5682311
theorem B15158987 : Blo 932582 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B10112951 : Blo 932582 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B5984225 : Blo 932582 5984225 := bstep (se 2 (by rfl) ⟨2244084, by rfl⟩ : syracuseStep 5984225 = 4488169) B4488169
theorem B3200567 : Blo 932582 3200567 := bstep (se 1 (by rfl) ⟨2400425, by rfl⟩ : syracuseStep 3200567 = 4800851) B4800851
theorem B30333143 : Blo 932582 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B13818377 : Blo 932582 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B14408461 : Blo 932582 14408461 := bstep (se 3 (by rfl) ⟨2701586, by rfl⟩ : syracuseStep 14408461 = 5403173) B5403173
theorem B1399679 : Blo 932582 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B1400423 : Blo 932582 1400423 := bstep (se 1 (by rfl) ⟨1050317, by rfl⟩ : syracuseStep 1400423 = 2100635) B2100635
theorem B1400879 : Blo 932582 1400879 := bstep (se 1 (by rfl) ⟨1050659, by rfl⟩ : syracuseStep 1400879 = 2101319) B2101319
theorem B1400999 : Blo 932582 1400999 := bstep (se 1 (by rfl) ⟨1050749, by rfl⟩ : syracuseStep 1400999 = 2101499) B2101499
theorem B1401065 : Blo 932582 1401065 := bstep (se 2 (by rfl) ⟨525399, by rfl⟩ : syracuseStep 1401065 = 1050799) B1050799
theorem B48555409 : Blo 932582 48555409 := bstep (se 2 (by rfl) ⟨18208278, by rfl⟩ : syracuseStep 48555409 = 36416557) B36416557
theorem B51046631 : Blo 932582 51046631 := bstep (se 1 (by rfl) ⟨38284973, by rfl⟩ : syracuseStep 51046631 = 76569947) B76569947
theorem B1404443 : Blo 932582 1404443 := bstep (se 1 (by rfl) ⟨1053332, by rfl⟩ : syracuseStep 1404443 = 2106665) B2106665
theorem B1404527 : Blo 932582 1404527 := bstep (se 1 (by rfl) ⟨1053395, by rfl⟩ : syracuseStep 1404527 = 2106791) B2106791
theorem B1404623 : Blo 932582 1404623 := bstep (se 1 (by rfl) ⟨1053467, by rfl⟩ : syracuseStep 1404623 = 2106935) B2106935
theorem B11991563 : Blo 932582 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B3996641 : Blo 932582 3996641 := bstep (se 2 (by rfl) ⟨1498740, by rfl⟩ : syracuseStep 3996641 = 2997481) B2997481
theorem B7112123 : Blo 932582 7112123 := bstep (se 1 (by rfl) ⟨5334092, by rfl⟩ : syracuseStep 7112123 = 10668185) B10668185
theorem B2098655 : Blo 932582 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B2525471 : Blo 932582 2525471 := bstep (se 1 (by rfl) ⟨1894103, by rfl⟩ : syracuseStep 2525471 = 3788207) B3788207
theorem B2099879 : Blo 932582 2099879 := bstep (se 1 (by rfl) ⟨1574909, by rfl⟩ : syracuseStep 2099879 = 3149819) B3149819
theorem B2362223 : Blo 932582 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B2100563 : Blo 932582 2100563 := bstep (se 1 (by rfl) ⟨1575422, by rfl⟩ : syracuseStep 2100563 = 3150845) B3150845
theorem B76845125 : Blo 932582 76845125 := bstep (se 4 (by rfl) ⟨7204230, by rfl⟩ : syracuseStep 76845125 = 14408461) B14408461
theorem B20222095 : Blo 932582 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B3150251 : Blo 932582 3150251 := bstep (se 1 (by rfl) ⟨2362688, by rfl⟩ : syracuseStep 3150251 = 4725377) B4725377
theorem B1577711 : Blo 932582 1577711 := bstep (se 1 (by rfl) ⟨1183283, by rfl⟩ : syracuseStep 1577711 = 2366567) B2366567
theorem B2364329 : Blo 932582 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B3151655 : Blo 932582 3151655 := bstep (se 1 (by rfl) ⟨2363741, by rfl⟩ : syracuseStep 3151655 = 4727483) B4727483
theorem B1579675 : Blo 932582 1579675 := bstep (se 1 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 1579675 = 2369513) B2369513
theorem B1579783 : Blo 932582 1579783 := bstep (se 1 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 1579783 = 2369675) B2369675
theorem B45489599 : Blo 932582 45489599 := bstep (se 1 (by rfl) ⟨34117199, by rfl⟩ : syracuseStep 45489599 = 68234399) B68234399
theorem B2105171 : Blo 932582 2105171 := bstep (se 1 (by rfl) ⟨1578878, by rfl⟩ : syracuseStep 2105171 = 3157757) B3157757
theorem B40378445 : Blo 932582 40378445 := bstep (se 3 (by rfl) ⟨7570958, by rfl⟩ : syracuseStep 40378445 = 15141917) B15141917
theorem B16000091 : Blo 932582 16000091 := bstep (se 1 (by rfl) ⟨12000068, by rfl⟩ : syracuseStep 16000091 = 24000137) B24000137
theorem B8988023 : Blo 932582 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B2664427 : Blo 932582 2664427 := bstep (se 1 (by rfl) ⟨1998320, by rfl⟩ : syracuseStep 2664427 = 3996641) B3996641
theorem B15577115 : Blo 932582 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B3158297 : Blo 932582 3158297 := bstep (se 2 (by rfl) ⟨1184361, by rfl⟩ : syracuseStep 3158297 = 2368723) B2368723
theorem B22688657 : Blo 932582 22688657 := bstep (se 2 (by rfl) ⟨8508246, by rfl⟩ : syracuseStep 22688657 = 17016493) B17016493
theorem B10105991 : Blo 932582 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B3782483 : Blo 932582 3782483 := bstep (se 1 (by rfl) ⟨2836862, by rfl⟩ : syracuseStep 3782483 = 5673725) B5673725
theorem B8534845 : Blo 932582 8534845 := bstep (se 3 (by rfl) ⟨1600283, by rfl⟩ : syracuseStep 8534845 = 3200567) B3200567
theorem B933119 : Blo 932582 933119 := bstep (se 1 (by rfl) ⟨699839, by rfl⟩ : syracuseStep 933119 = 1399679) B1399679
theorem B7585235 : Blo 932582 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B933615 : Blo 932582 933615 := bstep (se 1 (by rfl) ⟨700211, by rfl⟩ : syracuseStep 933615 = 1400423) B1400423
theorem B933919 : Blo 932582 933919 := bstep (se 1 (by rfl) ⟨700439, by rfl⟩ : syracuseStep 933919 = 1400879) B1400879
theorem B933999 : Blo 932582 933999 := bstep (se 1 (by rfl) ⟨700499, by rfl⟩ : syracuseStep 933999 = 1400999) B1400999
theorem B934043 : Blo 932582 934043 := bstep (se 1 (by rfl) ⟨700532, by rfl⟩ : syracuseStep 934043 = 1401065) B1401065
theorem B36849005 : Blo 932582 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B34031087 : Blo 932582 34031087 := bstep (se 1 (by rfl) ⟨25523315, by rfl⟩ : syracuseStep 34031087 = 51046631) B51046631
theorem B936295 : Blo 932582 936295 := bstep (se 1 (by rfl) ⟨702221, by rfl⟩ : syracuseStep 936295 = 1404443) B1404443
theorem B936351 : Blo 932582 936351 := bstep (se 1 (by rfl) ⟨702263, by rfl⟩ : syracuseStep 936351 = 1404527) B1404527
theorem B936415 : Blo 932582 936415 := bstep (se 1 (by rfl) ⟨702311, by rfl⟩ : syracuseStep 936415 = 1404623) B1404623
theorem B8967145 : Blo 932582 8967145 := bstep (se 2 (by rfl) ⟨3362679, by rfl⟩ : syracuseStep 8967145 = 6725359) B6725359
theorem B1332607 : Blo 932582 1332607 := bstep (se 1 (by rfl) ⟨999455, by rfl⟩ : syracuseStep 1332607 = 1998911) B1998911
theorem B5691455 : Blo 932582 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B5331815 : Blo 932582 5331815 := bstep (se 1 (by rfl) ⟨3998861, by rfl⟩ : syracuseStep 5331815 = 7997723) B7997723
theorem B64740545 : Blo 932582 64740545 := bstep (se 2 (by rfl) ⟨24277704, by rfl⟩ : syracuseStep 64740545 = 48555409) B48555409
theorem B5692625 : Blo 932582 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B1400063 : Blo 932582 1400063 := bstep (se 1 (by rfl) ⟨1050047, by rfl⟩ : syracuseStep 1400063 = 2100095) B2100095
theorem B1400105 : Blo 932582 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B8215991 : Blo 932582 8215991 := bstep (se 1 (by rfl) ⟨6161993, by rfl⟩ : syracuseStep 8215991 = 12323987) B12323987
theorem B1400255 : Blo 932582 1400255 := bstep (se 1 (by rfl) ⟨1050191, by rfl⟩ : syracuseStep 1400255 = 2100383) B2100383
theorem B7102403 : Blo 932582 7102403 := bstep (se 1 (by rfl) ⟨5326802, by rfl⟩ : syracuseStep 7102403 = 10653605) B10653605
theorem B6741967 : Blo 932582 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B3989483 : Blo 932582 3989483 := bstep (se 1 (by rfl) ⟨2992112, by rfl⟩ : syracuseStep 3989483 = 5984225) B5984225
theorem B12804407 : Blo 932582 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B1403039 : Blo 932582 1403039 := bstep (se 1 (by rfl) ⟨1052279, by rfl⟩ : syracuseStep 1403039 = 2104559) B2104559
theorem B1403111 : Blo 932582 1403111 := bstep (se 1 (by rfl) ⟨1052333, by rfl⟩ : syracuseStep 1403111 = 2104667) B2104667
theorem B1403519 : Blo 932582 1403519 := bstep (se 1 (by rfl) ⟨1052639, by rfl⟩ : syracuseStep 1403519 = 2105279) B2105279
theorem B4483727 : Blo 932582 4483727 := bstep (se 1 (by rfl) ⟨3362795, by rfl⟩ : syracuseStep 4483727 = 6725591) B6725591
theorem B1997227 : Blo 932582 1997227 := bstep (se 1 (by rfl) ⟨1497920, by rfl⟩ : syracuseStep 1997227 = 2995841) B2995841
theorem B7994375 : Blo 932582 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B19201769 : Blo 932582 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B57507731 : Blo 932582 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B1574815 : Blo 932582 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B2100167 : Blo 932582 2100167 := bstep (se 1 (by rfl) ⟨1575125, by rfl⟩ : syracuseStep 2100167 = 3150251) B3150251
theorem B1051807 : Blo 932582 1051807 := bstep (se 1 (by rfl) ⟨788855, by rfl⟩ : syracuseStep 1051807 = 1577711) B1577711
theorem B1576219 : Blo 932582 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B2101103 : Blo 932582 2101103 := bstep (se 1 (by rfl) ⟨1575827, by rfl⟩ : syracuseStep 2101103 = 3151655) B3151655
theorem B43160363 : Blo 932582 43160363 := bstep (se 1 (by rfl) ⟨32370272, by rfl⟩ : syracuseStep 43160363 = 64740545) B64740545
theorem B5477327 : Blo 932582 5477327 := bstep (se 1 (by rfl) ⟨4107995, by rfl⟩ : syracuseStep 5477327 = 8215991) B8215991
theorem B2659655 : Blo 932582 2659655 := bstep (se 1 (by rfl) ⟨1994741, by rfl⟩ : syracuseStep 2659655 = 3989483) B3989483
theorem B2989151 : Blo 932582 2989151 := bstep (se 1 (by rfl) ⟨2241863, by rfl⟩ : syracuseStep 2989151 = 4483727) B4483727
theorem B1776809 : Blo 932582 1776809 := bstep (se 2 (by rfl) ⟨666303, by rfl⟩ : syracuseStep 1776809 = 1332607) B1332607
theorem B2105531 : Blo 932582 2105531 := bstep (se 1 (by rfl) ⟨1579148, by rfl⟩ : syracuseStep 2105531 = 3158297) B3158297
theorem B2662969 : Blo 932582 2662969 := bstep (se 2 (by rfl) ⟨998613, by rfl⟩ : syracuseStep 2662969 = 1997227) B1997227
theorem B2106233 : Blo 932582 2106233 := bstep (se 2 (by rfl) ⟨789837, by rfl⟩ : syracuseStep 2106233 = 1579675) B1579675
theorem B2106377 : Blo 932582 2106377 := bstep (se 2 (by rfl) ⟨789891, by rfl⟩ : syracuseStep 2106377 = 1579783) B1579783
theorem B11379793 : Blo 932582 11379793 := bstep (se 2 (by rfl) ⟨4267422, by rfl⟩ : syracuseStep 11379793 = 8534845) B8534845
theorem B5056823 : Blo 932582 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B8989289 : Blo 932582 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B22687391 : Blo 932582 22687391 := bstep (se 1 (by rfl) ⟨17015543, by rfl⟩ : syracuseStep 22687391 = 34031087) B34031087
theorem B1683647 : Blo 932582 1683647 := bstep (se 1 (by rfl) ⟨1262735, by rfl⟩ : syracuseStep 1683647 = 2525471) B2525471
theorem B3552569 : Blo 932582 3552569 := bstep (se 2 (by rfl) ⟨1332213, by rfl⟩ : syracuseStep 3552569 = 2664427) B2664427
theorem B51230083 : Blo 932582 51230083 := bstep (se 1 (by rfl) ⟨38422562, by rfl⟩ : syracuseStep 51230083 = 76845125) B76845125
theorem B3554543 : Blo 932582 3554543 := bstep (se 1 (by rfl) ⟨2665907, by rfl⟩ : syracuseStep 3554543 = 5331815) B5331815
theorem B933375 : Blo 932582 933375 := bstep (se 1 (by rfl) ⟨700031, by rfl⟩ : syracuseStep 933375 = 1400063) B1400063
theorem B933403 : Blo 932582 933403 := bstep (se 1 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 933403 = 1400105) B1400105
theorem B933503 : Blo 932582 933503 := bstep (se 1 (by rfl) ⟨700127, by rfl⟩ : syracuseStep 933503 = 1400255) B1400255
theorem B30326399 : Blo 932582 30326399 := bstep (se 1 (by rfl) ⟨22744799, by rfl⟩ : syracuseStep 30326399 = 45489599) B45489599
theorem B4734935 : Blo 932582 4734935 := bstep (se 1 (by rfl) ⟨3551201, by rfl⟩ : syracuseStep 4734935 = 7102403) B7102403
theorem B26918963 : Blo 932582 26918963 := bstep (se 1 (by rfl) ⟨20189222, by rfl⟩ : syracuseStep 26918963 = 40378445) B40378445
theorem B8536271 : Blo 932582 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B10666727 : Blo 932582 10666727 := bstep (se 1 (by rfl) ⟨8000045, by rfl⟩ : syracuseStep 10666727 = 16000091) B16000091
theorem B935359 : Blo 932582 935359 := bstep (se 1 (by rfl) ⟨701519, by rfl⟩ : syracuseStep 935359 = 1403039) B1403039
theorem B935407 : Blo 932582 935407 := bstep (se 1 (by rfl) ⟨701555, by rfl⟩ : syracuseStep 935407 = 1403111) B1403111
theorem B935679 : Blo 932582 935679 := bstep (se 1 (by rfl) ⟨701759, by rfl⟩ : syracuseStep 935679 = 1403519) B1403519
theorem B15125771 : Blo 932582 15125771 := bstep (se 1 (by rfl) ⟨11344328, by rfl⟩ : syracuseStep 15125771 = 22688657) B22688657
theorem B6737327 : Blo 932582 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B5329583 : Blo 932582 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B12801179 : Blo 932582 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B41538973 : Blo 932582 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B24566003 : Blo 932582 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B4741415 : Blo 932582 4741415 := bstep (se 1 (by rfl) ⟨3556061, by rfl⟩ : syracuseStep 4741415 = 7112123) B7112123
theorem B1399103 : Blo 932582 1399103 := bstep (se 1 (by rfl) ⟨1049327, by rfl⟩ : syracuseStep 1399103 = 2098655) B2098655
theorem B1399919 : Blo 932582 1399919 := bstep (se 1 (by rfl) ⟨1049939, by rfl⟩ : syracuseStep 1399919 = 2099879) B2099879
theorem B1400375 : Blo 932582 1400375 := bstep (se 1 (by rfl) ⟨1050281, by rfl⟩ : syracuseStep 1400375 = 2100563) B2100563
theorem B3794303 : Blo 932582 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B3795083 : Blo 932582 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B1403447 : Blo 932582 1403447 := bstep (se 1 (by rfl) ⟨1052585, by rfl⟩ : syracuseStep 1403447 = 2105171) B2105171
theorem B26962793 : Blo 932582 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B5992015 : Blo 932582 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B11956193 : Blo 932582 11956193 := bstep (se 2 (by rfl) ⟨4483572, by rfl⟩ : syracuseStep 11956193 = 8967145) B8967145
theorem B2521655 : Blo 932582 2521655 := bstep (se 1 (by rfl) ⟨1891241, by rfl⟩ : syracuseStep 2521655 = 3782483) B3782483
theorem B38338487 : Blo 932582 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B7111151 : Blo 932582 7111151 := bstep (se 1 (by rfl) ⟨5333363, by rfl⟩ : syracuseStep 7111151 = 10666727) B10666727
theorem B15173057 : Blo 932582 15173057 := bstep (se 2 (by rfl) ⟨5689896, by rfl⟩ : syracuseStep 15173057 = 11379793) B11379793
theorem B4491551 : Blo 932582 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B2099753 : Blo 932582 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B28773575 : Blo 932582 28773575 := bstep (se 1 (by rfl) ⟨21580181, by rfl⟩ : syracuseStep 28773575 = 43160363) B43160363
theorem B1773103 : Blo 932582 1773103 := bstep (se 1 (by rfl) ⟨1329827, by rfl⟩ : syracuseStep 1773103 = 2659655) B2659655
theorem B2101625 : Blo 932582 2101625 := bstep (se 2 (by rfl) ⟨788109, by rfl⟩ : syracuseStep 2101625 = 1576219) B1576219
theorem B1184539 : Blo 932582 1184539 := bstep (se 1 (by rfl) ⟨888404, by rfl⟩ : syracuseStep 1184539 = 1776809) B1776809
theorem B2530055 : Blo 932582 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B55385297 : Blo 932582 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B7970795 : Blo 932582 7970795 := bstep (se 1 (by rfl) ⟨5978096, by rfl⟩ : syracuseStep 7970795 = 11956193) B11956193
theorem B1122431 : Blo 932582 1122431 := bstep (se 1 (by rfl) ⟨841823, by rfl⟩ : syracuseStep 1122431 = 1683647) B1683647
theorem B2368379 : Blo 932582 2368379 := bstep (se 1 (by rfl) ⟨1776284, by rfl⟩ : syracuseStep 2368379 = 3552569) B3552569
theorem B1681103 : Blo 932582 1681103 := bstep (se 1 (by rfl) ⟨1260827, by rfl⟩ : syracuseStep 1681103 = 2521655) B2521655
theorem B2369695 : Blo 932582 2369695 := bstep (se 1 (by rfl) ⟨1777271, by rfl⟩ : syracuseStep 2369695 = 3554543) B3554543
theorem B3156623 : Blo 932582 3156623 := bstep (se 1 (by rfl) ⟨2367467, by rfl⟩ : syracuseStep 3156623 = 4734935) B4734935
theorem B3550625 : Blo 932582 3550625 := bstep (se 2 (by rfl) ⟨1331484, by rfl⟩ : syracuseStep 3550625 = 2662969) B2662969
theorem B3553055 : Blo 932582 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B3651551 : Blo 932582 3651551 := bstep (se 1 (by rfl) ⟨2738663, by rfl⟩ : syracuseStep 3651551 = 5477327) B5477327
theorem B8534119 : Blo 932582 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B3160943 : Blo 932582 3160943 := bstep (se 1 (by rfl) ⟨2370707, by rfl⟩ : syracuseStep 3160943 = 4741415) B4741415
theorem B932735 : Blo 932582 932735 := bstep (se 1 (by rfl) ⟨699551, by rfl⟩ : syracuseStep 932735 = 1399103) B1399103
theorem B933279 : Blo 932582 933279 := bstep (se 1 (by rfl) ⟨699959, by rfl⟩ : syracuseStep 933279 = 1399919) B1399919
theorem B933583 : Blo 932582 933583 := bstep (se 1 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 933583 = 1400375) B1400375
theorem B935631 : Blo 932582 935631 := bstep (se 1 (by rfl) ⟨701723, by rfl⟩ : syracuseStep 935631 = 1403447) B1403447
theorem B68306777 : Blo 932582 68306777 := bstep (se 2 (by rfl) ⟨25615041, by rfl⟩ : syracuseStep 68306777 = 51230083) B51230083
theorem B17975195 : Blo 932582 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B15124927 : Blo 932582 15124927 := bstep (se 1 (by rfl) ⟨11343695, by rfl⟩ : syracuseStep 15124927 = 22687391) B22687391
theorem B17945975 : Blo 932582 17945975 := bstep (se 1 (by rfl) ⟨13459481, by rfl⟩ : syracuseStep 17945975 = 26918963) B26918963
theorem B1400111 : Blo 932582 1400111 := bstep (se 1 (by rfl) ⟨1050083, by rfl⟩ : syracuseStep 1400111 = 2100167) B2100167
theorem B91053557 : Blo 932582 91053557 := bstep (se 5 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 91053557 = 8536271) B8536271
theorem B10083847 : Blo 932582 10083847 := bstep (se 1 (by rfl) ⟨7562885, by rfl⟩ : syracuseStep 10083847 = 15125771) B15125771
theorem B1400735 : Blo 932582 1400735 := bstep (se 1 (by rfl) ⟨1050551, by rfl⟩ : syracuseStep 1400735 = 2101103) B2101103
theorem B10118141 : Blo 932582 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B16377335 : Blo 932582 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B1402409 : Blo 932582 1402409 := bstep (se 2 (by rfl) ⟨525903, by rfl⟩ : syracuseStep 1402409 = 1051807) B1051807
theorem B1992767 : Blo 932582 1992767 := bstep (se 1 (by rfl) ⟨1494575, by rfl⟩ : syracuseStep 1992767 = 2989151) B2989151
theorem B7989353 : Blo 932582 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B1403687 : Blo 932582 1403687 := bstep (se 1 (by rfl) ⟨1052765, by rfl⟩ : syracuseStep 1403687 = 2105531) B2105531
theorem B1404155 : Blo 932582 1404155 := bstep (se 1 (by rfl) ⟨1053116, by rfl⟩ : syracuseStep 1404155 = 2106233) B2106233
theorem B1404251 : Blo 932582 1404251 := bstep (se 1 (by rfl) ⟨1053188, by rfl⟩ : syracuseStep 1404251 = 2106377) B2106377
theorem B3371215 : Blo 932582 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B5992859 : Blo 932582 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B20217599 : Blo 932582 20217599 := bstep (se 1 (by rfl) ⟨15163199, by rfl⟩ : syracuseStep 20217599 = 30326399) B30326399
theorem B25558991 : Blo 932582 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B11963983 : Blo 932582 11963983 := bstep (se 1 (by rfl) ⟨8972987, by rfl⟩ : syracuseStep 11963983 = 17945975) B17945975
theorem B2364137 : Blo 932582 2364137 := bstep (se 2 (by rfl) ⟨886551, by rfl⟩ : syracuseStep 2364137 = 1773103) B1773103
theorem B5313863 : Blo 932582 5313863 := bstep (se 1 (by rfl) ⟨3985397, by rfl⟩ : syracuseStep 5313863 = 7970795) B7970795
theorem B5314045 : Blo 932582 5314045 := bstep (se 3 (by rfl) ⟨996383, by rfl⟩ : syracuseStep 5314045 = 1992767) B1992767
theorem B4494953 : Blo 932582 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B1578919 : Blo 932582 1578919 := bstep (se 1 (by rfl) ⟨1184189, by rfl⟩ : syracuseStep 1578919 = 2368379) B2368379
theorem B10918223 : Blo 932582 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B1579385 : Blo 932582 1579385 := bstep (se 2 (by rfl) ⟨592269, by rfl⟩ : syracuseStep 1579385 = 1184539) B1184539
theorem B1120735 : Blo 932582 1120735 := bstep (se 1 (by rfl) ⟨840551, by rfl⟩ : syracuseStep 1120735 = 1681103) B1681103
theorem B2104415 : Blo 932582 2104415 := bstep (se 1 (by rfl) ⟨1578311, by rfl⟩ : syracuseStep 2104415 = 3156623) B3156623
theorem B2367083 : Blo 932582 2367083 := bstep (se 1 (by rfl) ⟨1775312, by rfl⟩ : syracuseStep 2367083 = 3550625) B3550625
theorem B11378825 : Blo 932582 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B2368703 : Blo 932582 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B2434367 : Blo 932582 2434367 := bstep (se 1 (by rfl) ⟨1825775, by rfl⟩ : syracuseStep 2434367 = 3651551) B3651551
theorem B2107295 : Blo 932582 2107295 := bstep (se 1 (by rfl) ⟨1580471, by rfl⟩ : syracuseStep 2107295 = 3160943) B3160943
theorem B13445129 : Blo 932582 13445129 := bstep (se 2 (by rfl) ⟨5041923, by rfl⟩ : syracuseStep 13445129 = 10083847) B10083847
theorem B13478399 : Blo 932582 13478399 := bstep (se 1 (by rfl) ⟨10108799, by rfl⟩ : syracuseStep 13478399 = 20217599) B20217599
theorem B2993149 : Blo 932582 2993149 := bstep (se 3 (by rfl) ⟨561215, by rfl⟩ : syracuseStep 2993149 = 1122431) B1122431
theorem B19182383 : Blo 932582 19182383 := bstep (se 1 (by rfl) ⟨14386787, by rfl⟩ : syracuseStep 19182383 = 28773575) B28773575
theorem B3159593 : Blo 932582 3159593 := bstep (se 2 (by rfl) ⟨1184847, by rfl⟩ : syracuseStep 3159593 = 2369695) B2369695
theorem B20166569 : Blo 932582 20166569 := bstep (se 2 (by rfl) ⟨7562463, by rfl⟩ : syracuseStep 20166569 = 15124927) B15124927
theorem B933407 : Blo 932582 933407 := bstep (se 1 (by rfl) ⟨700055, by rfl⟩ : syracuseStep 933407 = 1400111) B1400111
theorem B60702371 : Blo 932582 60702371 := bstep (se 1 (by rfl) ⟨45526778, by rfl⟩ : syracuseStep 60702371 = 91053557) B91053557
theorem B933823 : Blo 932582 933823 := bstep (se 1 (by rfl) ⟨700367, by rfl⟩ : syracuseStep 933823 = 1400735) B1400735
theorem B11977469 : Blo 932582 11977469 := bstep (se 3 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 11977469 = 4491551) B4491551
theorem B934939 : Blo 932582 934939 := bstep (se 1 (by rfl) ⟨701204, by rfl⟩ : syracuseStep 934939 = 1402409) B1402409
theorem B5326235 : Blo 932582 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B935791 : Blo 932582 935791 := bstep (se 1 (by rfl) ⟨701843, by rfl⟩ : syracuseStep 935791 = 1403687) B1403687
theorem B936103 : Blo 932582 936103 := bstep (se 1 (by rfl) ⟨702077, by rfl⟩ : syracuseStep 936103 = 1404155) B1404155
theorem B936167 : Blo 932582 936167 := bstep (se 1 (by rfl) ⟨702125, by rfl⟩ : syracuseStep 936167 = 1404251) B1404251
theorem B4740767 : Blo 932582 4740767 := bstep (se 1 (by rfl) ⟨3555575, by rfl⟩ : syracuseStep 4740767 = 7111151) B7111151
theorem B10115371 : Blo 932582 10115371 := bstep (se 1 (by rfl) ⟨7586528, by rfl⟩ : syracuseStep 10115371 = 15173057) B15173057
theorem B45537851 : Blo 932582 45537851 := bstep (se 1 (by rfl) ⟨34153388, by rfl⟩ : syracuseStep 45537851 = 68306777) B68306777
theorem B11983463 : Blo 932582 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B1399835 : Blo 932582 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B1401083 : Blo 932582 1401083 := bstep (se 1 (by rfl) ⟨1050812, by rfl⟩ : syracuseStep 1401083 = 2101625) B2101625
theorem B36923531 : Blo 932582 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B6745427 : Blo 932582 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B6746813 : Blo 932582 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B3995239 : Blo 932582 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B17039327 : Blo 932582 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B1576091 : Blo 932582 1576091 := bstep (se 1 (by rfl) ⟨1182068, by rfl⟩ : syracuseStep 1576091 = 2364137) B2364137
theorem B3542575 : Blo 932582 3542575 := bstep (se 1 (by rfl) ⟨2656931, by rfl⟩ : syracuseStep 3542575 = 5313863) B5313863
theorem B7278815 : Blo 932582 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B1052923 : Blo 932582 1052923 := bstep (se 1 (by rfl) ⟨789692, by rfl⟩ : syracuseStep 1052923 = 1579385) B1579385
theorem B1578055 : Blo 932582 1578055 := bstep (se 1 (by rfl) ⟨1183541, by rfl⟩ : syracuseStep 1578055 = 2367083) B2367083
theorem B1579135 : Blo 932582 1579135 := bstep (se 1 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 1579135 = 2368703) B2368703
theorem B8985599 : Blo 932582 8985599 := bstep (se 1 (by rfl) ⟨6739199, by rfl⟩ : syracuseStep 8985599 = 13478399) B13478399
theorem B7085393 : Blo 932582 7085393 := bstep (se 2 (by rfl) ⟨2657022, by rfl⟩ : syracuseStep 7085393 = 5314045) B5314045
theorem B4496951 : Blo 932582 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B2105225 : Blo 932582 2105225 := bstep (se 2 (by rfl) ⟨789459, by rfl⟩ : syracuseStep 2105225 = 1578919) B1578919
theorem B4497875 : Blo 932582 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B12788255 : Blo 932582 12788255 := bstep (se 1 (by rfl) ⟨9591191, by rfl⟩ : syracuseStep 12788255 = 19182383) B19182383
theorem B2106395 : Blo 932582 2106395 := bstep (se 1 (by rfl) ⟨1579796, by rfl⟩ : syracuseStep 2106395 = 3159593) B3159593
theorem B13444379 : Blo 932582 13444379 := bstep (se 1 (by rfl) ⟨10083284, by rfl⟩ : syracuseStep 13444379 = 20166569) B20166569
theorem B3550823 : Blo 932582 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B5977253 : Blo 932582 5977253 := bstep (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) B1120735
theorem B2996635 : Blo 932582 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B3160511 : Blo 932582 3160511 := bstep (se 1 (by rfl) ⟨2370383, by rfl⟩ : syracuseStep 3160511 = 4740767) B4740767
theorem B30358567 : Blo 932582 30358567 := bstep (se 1 (by rfl) ⟨22768925, by rfl⟩ : syracuseStep 30358567 = 45537851) B45537851
theorem B933223 : Blo 932582 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B7585883 : Blo 932582 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B934055 : Blo 932582 934055 := bstep (se 1 (by rfl) ⟨700541, by rfl⟩ : syracuseStep 934055 = 1401083) B1401083
theorem B1622911 : Blo 932582 1622911 := bstep (se 1 (by rfl) ⟨1217183, by rfl⟩ : syracuseStep 1622911 = 2434367) B2434367
theorem B8963419 : Blo 932582 8963419 := bstep (se 1 (by rfl) ⟨6722564, by rfl⟩ : syracuseStep 8963419 = 13445129) B13445129
theorem B5326985 : Blo 932582 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B13487161 : Blo 932582 13487161 := bstep (se 2 (by rfl) ⟨5057685, by rfl⟩ : syracuseStep 13487161 = 10115371) B10115371
theorem B181752821 : Blo 932582 181752821 := bstep (se 5 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 181752821 = 17039327) B17039327
theorem B7984979 : Blo 932582 7984979 := bstep (se 1 (by rfl) ⟨5988734, by rfl⟩ : syracuseStep 7984979 = 11977469) B11977469
theorem B3990865 : Blo 932582 3990865 := bstep (se 2 (by rfl) ⟨1496574, by rfl⟩ : syracuseStep 3990865 = 2993149) B2993149
theorem B7988975 : Blo 932582 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B1402943 : Blo 932582 1402943 := bstep (se 1 (by rfl) ⟨1052207, by rfl⟩ : syracuseStep 1402943 = 2104415) B2104415
theorem B15951977 : Blo 932582 15951977 := bstep (se 2 (by rfl) ⟨5981991, by rfl⟩ : syracuseStep 15951977 = 11963983) B11963983
theorem B98462749 : Blo 932582 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B1404863 : Blo 932582 1404863 := bstep (se 1 (by rfl) ⟨1053647, by rfl⟩ : syracuseStep 1404863 = 2107295) B2107295
theorem B40468247 : Blo 932582 40468247 := bstep (se 1 (by rfl) ⟨30351185, by rfl⟩ : syracuseStep 40468247 = 60702371) B60702371
theorem B2163881 : Blo 932582 2163881 := bstep (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) B1622911
theorem B1050727 : Blo 932582 1050727 := bstep (se 1 (by rfl) ⟨788045, by rfl⟩ : syracuseStep 1050727 = 1576091) B1576091
theorem B4852543 : Blo 932582 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B4723433 : Blo 932582 4723433 := bstep (se 2 (by rfl) ⟨1771287, by rfl⟩ : syracuseStep 4723433 = 3542575) B3542575
theorem B4723595 : Blo 932582 4723595 := bstep (se 1 (by rfl) ⟨3542696, by rfl⟩ : syracuseStep 4723595 = 7085393) B7085393
theorem B8525503 : Blo 932582 8525503 := bstep (se 1 (by rfl) ⟨6394127, by rfl⟩ : syracuseStep 8525503 = 12788255) B12788255
theorem B2104073 : Blo 932582 2104073 := bstep (se 2 (by rfl) ⟨789027, by rfl⟩ : syracuseStep 2104073 = 1578055) B1578055
theorem B2367215 : Blo 932582 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B2105513 : Blo 932582 2105513 := bstep (se 2 (by rfl) ⟨789567, by rfl⟩ : syracuseStep 2105513 = 1579135) B1579135
theorem B40478089 : Blo 932582 40478089 := bstep (se 2 (by rfl) ⟨15179283, by rfl⟩ : syracuseStep 40478089 = 30358567) B30358567
theorem B2107007 : Blo 932582 2107007 := bstep (se 1 (by rfl) ⟨1580255, by rfl⟩ : syracuseStep 2107007 = 3160511) B3160511
theorem B26978831 : Blo 932582 26978831 := bstep (se 1 (by rfl) ⟨20234123, by rfl⟩ : syracuseStep 26978831 = 40468247) B40468247
theorem B5057255 : Blo 932582 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B3551323 : Blo 932582 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B5321153 : Blo 932582 5321153 := bstep (se 2 (by rfl) ⟨1995432, by rfl⟩ : syracuseStep 5321153 = 3990865) B3990865
theorem B5323319 : Blo 932582 5323319 := bstep (se 1 (by rfl) ⟨3992489, by rfl⟩ : syracuseStep 5323319 = 7984979) B7984979
theorem B131283665 : Blo 932582 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B2997967 : Blo 932582 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B2998583 : Blo 932582 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B8962919 : Blo 932582 8962919 := bstep (se 1 (by rfl) ⟨6722189, by rfl⟩ : syracuseStep 8962919 = 13444379) B13444379
theorem B5325983 : Blo 932582 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B935295 : Blo 932582 935295 := bstep (se 1 (by rfl) ⟨701471, by rfl⟩ : syracuseStep 935295 = 1402943) B1402943
theorem B10634651 : Blo 932582 10634651 := bstep (se 1 (by rfl) ⟨7975988, by rfl⟩ : syracuseStep 10634651 = 15951977) B15951977
theorem B936575 : Blo 932582 936575 := bstep (se 1 (by rfl) ⟨702431, by rfl⟩ : syracuseStep 936575 = 1404863) B1404863
theorem B3984835 : Blo 932582 3984835 := bstep (se 1 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 3984835 = 5977253) B5977253
theorem B11951225 : Blo 932582 11951225 := bstep (se 2 (by rfl) ⟨4481709, by rfl⟩ : syracuseStep 11951225 = 8963419) B8963419
theorem B121168547 : Blo 932582 121168547 := bstep (se 1 (by rfl) ⟨90876410, by rfl⟩ : syracuseStep 121168547 = 181752821) B181752821
theorem B17982881 : Blo 932582 17982881 := bstep (se 2 (by rfl) ⟨6743580, by rfl⟩ : syracuseStep 17982881 = 13487161) B13487161
theorem B5990399 : Blo 932582 5990399 := bstep (se 1 (by rfl) ⟨4492799, by rfl⟩ : syracuseStep 5990399 = 8985599) B8985599
theorem B1403483 : Blo 932582 1403483 := bstep (se 1 (by rfl) ⟨1052612, by rfl⟩ : syracuseStep 1403483 = 2105225) B2105225
theorem B1403897 : Blo 932582 1403897 := bstep (se 2 (by rfl) ⟨526461, by rfl⟩ : syracuseStep 1403897 = 1052923) B1052923
theorem B1404263 : Blo 932582 1404263 := bstep (se 1 (by rfl) ⟨1053197, by rfl⟩ : syracuseStep 1404263 = 2106395) B2106395
theorem B3995513 : Blo 932582 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B1999055 : Blo 932582 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B53970785 : Blo 932582 53970785 := bstep (se 2 (by rfl) ⟨20239044, by rfl⟩ : syracuseStep 53970785 = 40478089) B40478089
theorem B5770349 : Blo 932582 5770349 := bstep (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) B2163881
theorem B3148955 : Blo 932582 3148955 := bstep (se 1 (by rfl) ⟨2361716, by rfl⟩ : syracuseStep 3148955 = 4723433) B4723433
theorem B3149063 : Blo 932582 3149063 := bstep (se 1 (by rfl) ⟨2361797, by rfl⟩ : syracuseStep 3149063 = 4723595) B4723595
theorem B5313113 : Blo 932582 5313113 := bstep (se 2 (by rfl) ⟨1992417, by rfl⟩ : syracuseStep 5313113 = 3984835) B3984835
theorem B7967483 : Blo 932582 7967483 := bstep (se 1 (by rfl) ⟨5975612, by rfl⟩ : syracuseStep 7967483 = 11951225) B11951225
theorem B1578143 : Blo 932582 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B80779031 : Blo 932582 80779031 := bstep (se 1 (by rfl) ⟨60584273, by rfl⟩ : syracuseStep 80779031 = 121168547) B121168547
theorem B3547435 : Blo 932582 3547435 := bstep (se 1 (by rfl) ⟨2660576, by rfl⟩ : syracuseStep 3547435 = 5321153) B5321153
theorem B2663675 : Blo 932582 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B3548879 : Blo 932582 3548879 := bstep (se 1 (by rfl) ⟨2661659, by rfl⟩ : syracuseStep 3548879 = 5323319) B5323319
theorem B5975279 : Blo 932582 5975279 := bstep (se 1 (by rfl) ⟨4481459, by rfl⟩ : syracuseStep 5975279 = 8962919) B8962919
theorem B3550655 : Blo 932582 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B7089767 : Blo 932582 7089767 := bstep (se 1 (by rfl) ⟨5317325, by rfl⟩ : syracuseStep 7089767 = 10634651) B10634651
theorem B6470057 : Blo 932582 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B4735097 : Blo 932582 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B935655 : Blo 932582 935655 := bstep (se 1 (by rfl) ⟨701741, by rfl⟩ : syracuseStep 935655 = 1403483) B1403483
theorem B13486013 : Blo 932582 13486013 := bstep (se 3 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 13486013 = 5057255) B5057255
theorem B935931 : Blo 932582 935931 := bstep (se 1 (by rfl) ⟨701948, by rfl⟩ : syracuseStep 935931 = 1403897) B1403897
theorem B936175 : Blo 932582 936175 := bstep (se 1 (by rfl) ⟨702131, by rfl⟩ : syracuseStep 936175 = 1404263) B1404263
theorem B45469349 : Blo 932582 45469349 := bstep (se 4 (by rfl) ⟨4262751, by rfl⟩ : syracuseStep 45469349 = 8525503) B8525503
theorem B1400969 : Blo 932582 1400969 := bstep (se 2 (by rfl) ⟨525363, by rfl⟩ : syracuseStep 1400969 = 1050727) B1050727
theorem B1402715 : Blo 932582 1402715 := bstep (se 1 (by rfl) ⟨1052036, by rfl⟩ : syracuseStep 1402715 = 2104073) B2104073
theorem B1403675 : Blo 932582 1403675 := bstep (se 1 (by rfl) ⟨1052756, by rfl⟩ : syracuseStep 1403675 = 2105513) B2105513
theorem B11988587 : Blo 932582 11988587 := bstep (se 1 (by rfl) ⟨8991440, by rfl⟩ : syracuseStep 11988587 = 17982881) B17982881
theorem B1404671 : Blo 932582 1404671 := bstep (se 1 (by rfl) ⟨1053503, by rfl⟩ : syracuseStep 1404671 = 2107007) B2107007
theorem B3993599 : Blo 932582 3993599 := bstep (se 1 (by rfl) ⟨2995199, by rfl⟩ : syracuseStep 3993599 = 5990399) B5990399
theorem B17985887 : Blo 932582 17985887 := bstep (se 1 (by rfl) ⟨13489415, by rfl⟩ : syracuseStep 17985887 = 26978831) B26978831
theorem B87522443 : Blo 932582 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B3997289 : Blo 932582 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B35980523 : Blo 932582 35980523 := bstep (se 1 (by rfl) ⟨26985392, by rfl⟩ : syracuseStep 35980523 = 53970785) B53970785
theorem B2099303 : Blo 932582 2099303 := bstep (se 1 (by rfl) ⟨1574477, by rfl⟩ : syracuseStep 2099303 = 3148955) B3148955
theorem B2099375 : Blo 932582 2099375 := bstep (se 1 (by rfl) ⟨1574531, by rfl⟩ : syracuseStep 2099375 = 3149063) B3149063
theorem B30312899 : Blo 932582 30312899 := bstep (se 1 (by rfl) ⟨22734674, by rfl⟩ : syracuseStep 30312899 = 45469349) B45469349
theorem B3542075 : Blo 932582 3542075 := bstep (se 1 (by rfl) ⟨2656556, by rfl⟩ : syracuseStep 3542075 = 5313113) B5313113
theorem B5311655 : Blo 932582 5311655 := bstep (se 1 (by rfl) ⟨3983741, by rfl⟩ : syracuseStep 5311655 = 7967483) B7967483
theorem B1052095 : Blo 932582 1052095 := bstep (se 1 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 1052095 = 1578143) B1578143
theorem B1775783 : Blo 932582 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B2365919 : Blo 932582 2365919 := bstep (se 1 (by rfl) ⟨1774439, by rfl⟩ : syracuseStep 2365919 = 3548879) B3548879
theorem B2367103 : Blo 932582 2367103 := bstep (se 1 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 2367103 = 3550655) B3550655
theorem B4726511 : Blo 932582 4726511 := bstep (se 1 (by rfl) ⟨3544883, by rfl⟩ : syracuseStep 4726511 = 7089767) B7089767
theorem B2662399 : Blo 932582 2662399 := bstep (se 1 (by rfl) ⟨1996799, by rfl⟩ : syracuseStep 2662399 = 3993599) B3993599
theorem B10659437 : Blo 932582 10659437 := bstep (se 3 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 10659437 = 3997289) B3997289
theorem B3156731 : Blo 932582 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B4729913 : Blo 932582 4729913 := bstep (se 2 (by rfl) ⟨1773717, by rfl⟩ : syracuseStep 4729913 = 3547435) B3547435
theorem B8990675 : Blo 932582 8990675 := bstep (se 1 (by rfl) ⟨6743006, by rfl⟩ : syracuseStep 8990675 = 13486013) B13486013
theorem B3846899 : Blo 932582 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B53852687 : Blo 932582 53852687 := bstep (se 1 (by rfl) ⟨40389515, by rfl⟩ : syracuseStep 53852687 = 80779031) B80779031
theorem B933979 : Blo 932582 933979 := bstep (se 1 (by rfl) ⟨700484, by rfl⟩ : syracuseStep 933979 = 1400969) B1400969
theorem B17253485 : Blo 932582 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B935143 : Blo 932582 935143 := bstep (se 1 (by rfl) ⟨701357, by rfl⟩ : syracuseStep 935143 = 1402715) B1402715
theorem B935783 : Blo 932582 935783 := bstep (se 1 (by rfl) ⟨701837, by rfl⟩ : syracuseStep 935783 = 1403675) B1403675
theorem B3983519 : Blo 932582 3983519 := bstep (se 1 (by rfl) ⟨2987639, by rfl⟩ : syracuseStep 3983519 = 5975279) B5975279
theorem B936447 : Blo 932582 936447 := bstep (se 1 (by rfl) ⟨702335, by rfl⟩ : syracuseStep 936447 = 1404671) B1404671
theorem B58348295 : Blo 932582 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B1332703 : Blo 932582 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B7992391 : Blo 932582 7992391 := bstep (se 1 (by rfl) ⟨5994293, by rfl⟩ : syracuseStep 7992391 = 11988587) B11988587
theorem B11990591 : Blo 932582 11990591 := bstep (se 1 (by rfl) ⟨8992943, by rfl⟩ : syracuseStep 11990591 = 17985887) B17985887
theorem B11502323 : Blo 932582 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B23987015 : Blo 932582 23987015 := bstep (se 1 (by rfl) ⟨17990261, by rfl⟩ : syracuseStep 23987015 = 35980523) B35980523
theorem B2655679 : Blo 932582 2655679 := bstep (se 1 (by rfl) ⟨1991759, by rfl⟩ : syracuseStep 2655679 = 3983519) B3983519
theorem B10258397 : Blo 932582 10258397 := bstep (se 3 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 10258397 = 3846899) B3846899
theorem B2361383 : Blo 932582 2361383 := bstep (se 1 (by rfl) ⟨1771037, by rfl⟩ : syracuseStep 2361383 = 3542075) B3542075
theorem B3541103 : Blo 932582 3541103 := bstep (se 1 (by rfl) ⟨2655827, by rfl⟩ : syracuseStep 3541103 = 5311655) B5311655
theorem B38898863 : Blo 932582 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B1577279 : Blo 932582 1577279 := bstep (se 1 (by rfl) ⟨1182959, by rfl⟩ : syracuseStep 1577279 = 2365919) B2365919
theorem B3151007 : Blo 932582 3151007 := bstep (se 1 (by rfl) ⟨2363255, by rfl⟩ : syracuseStep 3151007 = 4726511) B4726511
theorem B10656521 : Blo 932582 10656521 := bstep (se 2 (by rfl) ⟨3996195, by rfl⟩ : syracuseStep 10656521 = 7992391) B7992391
theorem B2104487 : Blo 932582 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B3153275 : Blo 932582 3153275 := bstep (se 1 (by rfl) ⟨2364956, by rfl⟩ : syracuseStep 3153275 = 4729913) B4729913
theorem B3156137 : Blo 932582 3156137 := bstep (se 2 (by rfl) ⟨1183551, by rfl⟩ : syracuseStep 3156137 = 2367103) B2367103
theorem B3549865 : Blo 932582 3549865 := bstep (se 2 (by rfl) ⟨1331199, by rfl⟩ : syracuseStep 3549865 = 2662399) B2662399
theorem B4735421 : Blo 932582 4735421 := bstep (se 3 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 4735421 = 1775783) B1775783
theorem B35901791 : Blo 932582 35901791 := bstep (se 1 (by rfl) ⟨26926343, by rfl⟩ : syracuseStep 35901791 = 53852687) B53852687
theorem B1399535 : Blo 932582 1399535 := bstep (se 1 (by rfl) ⟨1049651, by rfl⟩ : syracuseStep 1399535 = 2099303) B2099303
theorem B1399583 : Blo 932582 1399583 := bstep (se 1 (by rfl) ⟨1049687, by rfl⟩ : syracuseStep 1399583 = 2099375) B2099375
theorem B20208599 : Blo 932582 20208599 := bstep (se 1 (by rfl) ⟨15156449, by rfl⟩ : syracuseStep 20208599 = 30312899) B30312899
theorem B1402793 : Blo 932582 1402793 := bstep (se 2 (by rfl) ⟨526047, by rfl⟩ : syracuseStep 1402793 = 1052095) B1052095
theorem B7106291 : Blo 932582 7106291 := bstep (se 1 (by rfl) ⟨5329718, by rfl⟩ : syracuseStep 7106291 = 10659437) B10659437
theorem B7107749 : Blo 932582 7107749 := bstep (se 4 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 7107749 = 1332703) B1332703
theorem B5993783 : Blo 932582 5993783 := bstep (se 1 (by rfl) ⟨4495337, by rfl⟩ : syracuseStep 5993783 = 8990675) B8990675
theorem B7993727 : Blo 932582 7993727 := bstep (se 1 (by rfl) ⟨5995295, by rfl⟩ : syracuseStep 7993727 = 11990591) B11990591
theorem B7668215 : Blo 932582 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B15991343 : Blo 932582 15991343 := bstep (se 1 (by rfl) ⟨11993507, by rfl⟩ : syracuseStep 15991343 = 23987015) B23987015
theorem B1574255 : Blo 932582 1574255 := bstep (se 1 (by rfl) ⟨1180691, by rfl⟩ : syracuseStep 1574255 = 2361383) B2361383
theorem B2360735 : Blo 932582 2360735 := bstep (se 1 (by rfl) ⟨1770551, by rfl⟩ : syracuseStep 2360735 = 3541103) B3541103
theorem B3540905 : Blo 932582 3540905 := bstep (se 2 (by rfl) ⟨1327839, by rfl⟩ : syracuseStep 3540905 = 2655679) B2655679
theorem B1051519 : Blo 932582 1051519 := bstep (se 1 (by rfl) ⟨788639, by rfl⟩ : syracuseStep 1051519 = 1577279) B1577279
theorem B2100671 : Blo 932582 2100671 := bstep (se 1 (by rfl) ⟨1575503, by rfl⟩ : syracuseStep 2100671 = 3151007) B3151007
theorem B13472399 : Blo 932582 13472399 := bstep (se 1 (by rfl) ⟨10104299, by rfl⟩ : syracuseStep 13472399 = 20208599) B20208599
theorem B2102183 : Blo 932582 2102183 := bstep (se 1 (by rfl) ⟨1576637, by rfl⟩ : syracuseStep 2102183 = 3153275) B3153275
theorem B2104091 : Blo 932582 2104091 := bstep (se 1 (by rfl) ⟨1578068, by rfl⟩ : syracuseStep 2104091 = 3156137) B3156137
theorem B3156947 : Blo 932582 3156947 := bstep (se 1 (by rfl) ⟨2367710, by rfl⟩ : syracuseStep 3156947 = 4735421) B4735421
theorem B25932575 : Blo 932582 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B23934527 : Blo 932582 23934527 := bstep (se 1 (by rfl) ⟨17950895, by rfl⟩ : syracuseStep 23934527 = 35901791) B35901791
theorem B4733153 : Blo 932582 4733153 := bstep (se 2 (by rfl) ⟨1774932, by rfl⟩ : syracuseStep 4733153 = 3549865) B3549865
theorem B933023 : Blo 932582 933023 := bstep (se 1 (by rfl) ⟨699767, by rfl⟩ : syracuseStep 933023 = 1399535) B1399535
theorem B933055 : Blo 932582 933055 := bstep (se 1 (by rfl) ⟨699791, by rfl⟩ : syracuseStep 933055 = 1399583) B1399583
theorem B935195 : Blo 932582 935195 := bstep (se 1 (by rfl) ⟨701396, by rfl⟩ : syracuseStep 935195 = 1402793) B1402793
theorem B4737527 : Blo 932582 4737527 := bstep (se 1 (by rfl) ⟨3553145, by rfl⟩ : syracuseStep 4737527 = 7106291) B7106291
theorem B4738499 : Blo 932582 4738499 := bstep (se 1 (by rfl) ⟨3553874, by rfl⟩ : syracuseStep 4738499 = 7107749) B7107749
theorem B5329151 : Blo 932582 5329151 := bstep (se 1 (by rfl) ⟨3996863, by rfl⟩ : syracuseStep 5329151 = 7993727) B7993727
theorem B6838931 : Blo 932582 6838931 := bstep (se 1 (by rfl) ⟨5129198, by rfl⟩ : syracuseStep 6838931 = 10258397) B10258397
theorem B7104347 : Blo 932582 7104347 := bstep (se 1 (by rfl) ⟨5328260, by rfl⟩ : syracuseStep 7104347 = 10656521) B10656521
theorem B1402991 : Blo 932582 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B3995855 : Blo 932582 3995855 := bstep (se 1 (by rfl) ⟨2996891, by rfl⟩ : syracuseStep 3995855 = 5993783) B5993783
theorem B5112143 : Blo 932582 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B1049503 : Blo 932582 1049503 := bstep (se 1 (by rfl) ⟨787127, by rfl⟩ : syracuseStep 1049503 = 1574255) B1574255
theorem B1573823 : Blo 932582 1573823 := bstep (se 1 (by rfl) ⟨1180367, by rfl⟩ : syracuseStep 1573823 = 2360735) B2360735
theorem B2360603 : Blo 932582 2360603 := bstep (se 1 (by rfl) ⟨1770452, by rfl⟩ : syracuseStep 2360603 = 3540905) B3540905
theorem B8981599 : Blo 932582 8981599 := bstep (se 1 (by rfl) ⟨6736199, by rfl⟩ : syracuseStep 8981599 = 13472399) B13472399
theorem B2104631 : Blo 932582 2104631 := bstep (se 1 (by rfl) ⟨1578473, by rfl⟩ : syracuseStep 2104631 = 3156947) B3156947
theorem B2663903 : Blo 932582 2663903 := bstep (se 1 (by rfl) ⟨1997927, by rfl⟩ : syracuseStep 2663903 = 3995855) B3995855
theorem B3155435 : Blo 932582 3155435 := bstep (se 1 (by rfl) ⟨2366576, by rfl⟩ : syracuseStep 3155435 = 4733153) B4733153
theorem B10660895 : Blo 932582 10660895 := bstep (se 1 (by rfl) ⟨7995671, by rfl⟩ : syracuseStep 10660895 = 15991343) B15991343
theorem B3158351 : Blo 932582 3158351 := bstep (se 1 (by rfl) ⟨2368763, by rfl⟩ : syracuseStep 3158351 = 4737527) B4737527
theorem B69153533 : Blo 932582 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B3158999 : Blo 932582 3158999 := bstep (se 1 (by rfl) ⟨2369249, by rfl⟩ : syracuseStep 3158999 = 4738499) B4738499
theorem B3552767 : Blo 932582 3552767 := bstep (se 1 (by rfl) ⟨2664575, by rfl⟩ : syracuseStep 3552767 = 5329151) B5329151
theorem B4736231 : Blo 932582 4736231 := bstep (se 1 (by rfl) ⟨3552173, by rfl⟩ : syracuseStep 4736231 = 7104347) B7104347
theorem B935327 : Blo 932582 935327 := bstep (se 1 (by rfl) ⟨701495, by rfl⟩ : syracuseStep 935327 = 1402991) B1402991
theorem B18237149 : Blo 932582 18237149 := bstep (se 3 (by rfl) ⟨3419465, by rfl⟩ : syracuseStep 18237149 = 6838931) B6838931
theorem B1400447 : Blo 932582 1400447 := bstep (se 1 (by rfl) ⟨1050335, by rfl⟩ : syracuseStep 1400447 = 2100671) B2100671
theorem B1401455 : Blo 932582 1401455 := bstep (se 1 (by rfl) ⟨1051091, by rfl⟩ : syracuseStep 1401455 = 2102183) B2102183
theorem B1402025 : Blo 932582 1402025 := bstep (se 2 (by rfl) ⟨525759, by rfl⟩ : syracuseStep 1402025 = 1051519) B1051519
theorem B1402727 : Blo 932582 1402727 := bstep (se 1 (by rfl) ⟨1052045, by rfl⟩ : syracuseStep 1402727 = 2104091) B2104091
theorem B15956351 : Blo 932582 15956351 := bstep (se 1 (by rfl) ⟨11967263, by rfl⟩ : syracuseStep 15956351 = 23934527) B23934527
theorem B3408095 : Blo 932582 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B1049215 : Blo 932582 1049215 := bstep (se 1 (by rfl) ⟨786911, by rfl⟩ : syracuseStep 1049215 = 1573823) B1573823
theorem B1573735 : Blo 932582 1573735 := bstep (se 1 (by rfl) ⟨1180301, by rfl⟩ : syracuseStep 1573735 = 2360603) B2360603
theorem B12158099 : Blo 932582 12158099 := bstep (se 1 (by rfl) ⟨9118574, by rfl⟩ : syracuseStep 12158099 = 18237149) B18237149
theorem B1775935 : Blo 932582 1775935 := bstep (se 1 (by rfl) ⟨1331951, by rfl⟩ : syracuseStep 1775935 = 2663903) B2663903
theorem B2103623 : Blo 932582 2103623 := bstep (se 1 (by rfl) ⟨1577717, by rfl⟩ : syracuseStep 2103623 = 3155435) B3155435
theorem B2105567 : Blo 932582 2105567 := bstep (se 1 (by rfl) ⟨1579175, by rfl⟩ : syracuseStep 2105567 = 3158351) B3158351
theorem B2105999 : Blo 932582 2105999 := bstep (se 1 (by rfl) ⟨1579499, by rfl⟩ : syracuseStep 2105999 = 3158999) B3158999
theorem B2368511 : Blo 932582 2368511 := bstep (se 1 (by rfl) ⟨1776383, by rfl⟩ : syracuseStep 2368511 = 3552767) B3552767
theorem B3157487 : Blo 932582 3157487 := bstep (se 1 (by rfl) ⟨2368115, by rfl⟩ : syracuseStep 3157487 = 4736231) B4736231
theorem B11975465 : Blo 932582 11975465 := bstep (se 2 (by rfl) ⟨4490799, by rfl⟩ : syracuseStep 11975465 = 8981599) B8981599
theorem B933631 : Blo 932582 933631 := bstep (se 1 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 933631 = 1400447) B1400447
theorem B934303 : Blo 932582 934303 := bstep (se 1 (by rfl) ⟨700727, by rfl⟩ : syracuseStep 934303 = 1401455) B1401455
theorem B934683 : Blo 932582 934683 := bstep (se 1 (by rfl) ⟨701012, by rfl⟩ : syracuseStep 934683 = 1402025) B1402025
theorem B935151 : Blo 932582 935151 := bstep (se 1 (by rfl) ⟨701363, by rfl⟩ : syracuseStep 935151 = 1402727) B1402727
theorem B10637567 : Blo 932582 10637567 := bstep (se 1 (by rfl) ⟨7978175, by rfl⟩ : syracuseStep 10637567 = 15956351) B15956351
theorem B1399337 : Blo 932582 1399337 := bstep (se 2 (by rfl) ⟨524751, by rfl⟩ : syracuseStep 1399337 = 1049503) B1049503
theorem B1403087 : Blo 932582 1403087 := bstep (se 1 (by rfl) ⟨1052315, by rfl⟩ : syracuseStep 1403087 = 2104631) B2104631
theorem B7107263 : Blo 932582 7107263 := bstep (se 1 (by rfl) ⟨5330447, by rfl⟩ : syracuseStep 7107263 = 10660895) B10660895
theorem B46102355 : Blo 932582 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B2098313 : Blo 932582 2098313 := bstep (se 2 (by rfl) ⟨786867, by rfl⟩ : syracuseStep 2098313 = 1573735) B1573735
theorem B1579007 : Blo 932582 1579007 := bstep (se 1 (by rfl) ⟨1184255, by rfl⟩ : syracuseStep 1579007 = 2368511) B2368511
theorem B2104991 : Blo 932582 2104991 := bstep (se 1 (by rfl) ⟨1578743, by rfl⟩ : syracuseStep 2104991 = 3157487) B3157487
theorem B2367913 : Blo 932582 2367913 := bstep (se 2 (by rfl) ⟨887967, by rfl⟩ : syracuseStep 2367913 = 1775935) B1775935
theorem B2272063 : Blo 932582 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B8105399 : Blo 932582 8105399 := bstep (se 1 (by rfl) ⟨6079049, by rfl⟩ : syracuseStep 8105399 = 12158099) B12158099
theorem B7091711 : Blo 932582 7091711 := bstep (se 1 (by rfl) ⟨5318783, by rfl⟩ : syracuseStep 7091711 = 10637567) B10637567
theorem B932891 : Blo 932582 932891 := bstep (se 1 (by rfl) ⟨699668, by rfl⟩ : syracuseStep 932891 = 1399337) B1399337
theorem B935391 : Blo 932582 935391 := bstep (se 1 (by rfl) ⟨701543, by rfl⟩ : syracuseStep 935391 = 1403087) B1403087
theorem B4738175 : Blo 932582 4738175 := bstep (se 1 (by rfl) ⟨3553631, by rfl⟩ : syracuseStep 4738175 = 7107263) B7107263
theorem B7983643 : Blo 932582 7983643 := bstep (se 1 (by rfl) ⟨5987732, by rfl⟩ : syracuseStep 7983643 = 11975465) B11975465
theorem B1398953 : Blo 932582 1398953 := bstep (se 2 (by rfl) ⟨524607, by rfl⟩ : syracuseStep 1398953 = 1049215) B1049215
theorem B1402415 : Blo 932582 1402415 := bstep (se 1 (by rfl) ⟨1051811, by rfl⟩ : syracuseStep 1402415 = 2103623) B2103623
theorem B1403711 : Blo 932582 1403711 := bstep (se 1 (by rfl) ⟨1052783, by rfl⟩ : syracuseStep 1403711 = 2105567) B2105567
theorem B1403999 : Blo 932582 1403999 := bstep (se 1 (by rfl) ⟨1052999, by rfl⟩ : syracuseStep 1403999 = 2105999) B2105999
theorem B30734903 : Blo 932582 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B1052671 : Blo 932582 1052671 := bstep (se 1 (by rfl) ⟨789503, by rfl⟩ : syracuseStep 1052671 = 1579007) B1579007
theorem B4727807 : Blo 932582 4727807 := bstep (se 1 (by rfl) ⟨3545855, by rfl⟩ : syracuseStep 4727807 = 7091711) B7091711
theorem B20489935 : Blo 932582 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B3157217 : Blo 932582 3157217 := bstep (se 2 (by rfl) ⟨1183956, by rfl⟩ : syracuseStep 3157217 = 2367913) B2367913
theorem B3158783 : Blo 932582 3158783 := bstep (se 1 (by rfl) ⟨2369087, by rfl⟩ : syracuseStep 3158783 = 4738175) B4738175
theorem B3029417 : Blo 932582 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B932635 : Blo 932582 932635 := bstep (se 1 (by rfl) ⟨699476, by rfl⟩ : syracuseStep 932635 = 1398953) B1398953
theorem B934943 : Blo 932582 934943 := bstep (se 1 (by rfl) ⟨701207, by rfl⟩ : syracuseStep 934943 = 1402415) B1402415
theorem B935807 : Blo 932582 935807 := bstep (se 1 (by rfl) ⟨701855, by rfl⟩ : syracuseStep 935807 = 1403711) B1403711
theorem B935999 : Blo 932582 935999 := bstep (se 1 (by rfl) ⟨701999, by rfl⟩ : syracuseStep 935999 = 1403999) B1403999
theorem B1398875 : Blo 932582 1398875 := bstep (se 1 (by rfl) ⟨1049156, by rfl⟩ : syracuseStep 1398875 = 2098313) B2098313
theorem B1403327 : Blo 932582 1403327 := bstep (se 1 (by rfl) ⟨1052495, by rfl⟩ : syracuseStep 1403327 = 2104991) B2104991
theorem B10644857 : Blo 932582 10644857 := bstep (se 2 (by rfl) ⟨3991821, by rfl⟩ : syracuseStep 10644857 = 7983643) B7983643
theorem B5403599 : Blo 932582 5403599 := bstep (se 1 (by rfl) ⟨4052699, by rfl⟩ : syracuseStep 5403599 = 8105399) B8105399
theorem B3151871 : Blo 932582 3151871 := bstep (se 1 (by rfl) ⟨2363903, by rfl⟩ : syracuseStep 3151871 = 4727807) B4727807
theorem B2104811 : Blo 932582 2104811 := bstep (se 1 (by rfl) ⟨1578608, by rfl⟩ : syracuseStep 2104811 = 3157217) B3157217
theorem B2105855 : Blo 932582 2105855 := bstep (se 1 (by rfl) ⟨1579391, by rfl⟩ : syracuseStep 2105855 = 3158783) B3158783
theorem B932583 : Blo 932582 932583 := bstep (se 1 (by rfl) ⟨699437, by rfl⟩ : syracuseStep 932583 = 1398875) B1398875
theorem B935551 : Blo 932582 935551 := bstep (se 1 (by rfl) ⟨701663, by rfl⟩ : syracuseStep 935551 = 1403327) B1403327
theorem B7096571 : Blo 932582 7096571 := bstep (se 1 (by rfl) ⟨5322428, by rfl⟩ : syracuseStep 7096571 = 10644857) B10644857
theorem B2019611 : Blo 932582 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B27319913 : Blo 932582 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B1403561 : Blo 932582 1403561 := bstep (se 2 (by rfl) ⟨526335, by rfl⟩ : syracuseStep 1403561 = 1052671) B1052671
theorem B3602399 : Blo 932582 3602399 := bstep (se 1 (by rfl) ⟨2701799, by rfl⟩ : syracuseStep 3602399 = 5403599) B5403599
theorem B2101247 : Blo 932582 2101247 := bstep (se 1 (by rfl) ⟨1575935, by rfl⟩ : syracuseStep 2101247 = 3151871) B3151871
theorem B9606397 : Blo 932582 9606397 := bstep (se 3 (by rfl) ⟨1801199, by rfl⟩ : syracuseStep 9606397 = 3602399) B3602399
theorem B5385629 : Blo 932582 5385629 := bstep (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) B2019611
theorem B4731047 : Blo 932582 4731047 := bstep (se 1 (by rfl) ⟨3548285, by rfl⟩ : syracuseStep 4731047 = 7096571) B7096571
theorem B935707 : Blo 932582 935707 := bstep (se 1 (by rfl) ⟨701780, by rfl⟩ : syracuseStep 935707 = 1403561) B1403561
theorem B1403207 : Blo 932582 1403207 := bstep (se 1 (by rfl) ⟨1052405, by rfl⟩ : syracuseStep 1403207 = 2104811) B2104811
theorem B18213275 : Blo 932582 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B1403903 : Blo 932582 1403903 := bstep (se 1 (by rfl) ⟨1052927, by rfl⟩ : syracuseStep 1403903 = 2105855) B2105855
theorem B3154031 : Blo 932582 3154031 := bstep (se 1 (by rfl) ⟨2365523, by rfl⟩ : syracuseStep 3154031 = 4731047) B4731047
theorem B935471 : Blo 932582 935471 := bstep (se 1 (by rfl) ⟨701603, by rfl⟩ : syracuseStep 935471 = 1403207) B1403207
theorem B12142183 : Blo 932582 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B935935 : Blo 932582 935935 := bstep (se 1 (by rfl) ⟨701951, by rfl⟩ : syracuseStep 935935 = 1403903) B1403903
theorem B3590419 : Blo 932582 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B1400831 : Blo 932582 1400831 := bstep (se 1 (by rfl) ⟨1050623, by rfl⟩ : syracuseStep 1400831 = 2101247) B2101247
theorem B12808529 : Blo 932582 12808529 := bstep (se 2 (by rfl) ⟨4803198, by rfl⟩ : syracuseStep 12808529 = 9606397) B9606397
theorem B16189577 : Blo 932582 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B4787225 : Blo 932582 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B2102687 : Blo 932582 2102687 := bstep (se 1 (by rfl) ⟨1577015, by rfl⟩ : syracuseStep 2102687 = 3154031) B3154031
theorem B933887 : Blo 932582 933887 := bstep (se 1 (by rfl) ⟨700415, by rfl⟩ : syracuseStep 933887 = 1400831) B1400831
theorem B8539019 : Blo 932582 8539019 := bstep (se 1 (by rfl) ⟨6404264, by rfl⟩ : syracuseStep 8539019 = 12808529) B12808529
theorem B10793051 : Blo 932582 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B3191483 : Blo 932582 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B5692679 : Blo 932582 5692679 := bstep (se 1 (by rfl) ⟨4269509, by rfl⟩ : syracuseStep 5692679 = 8539019) B8539019
theorem B1401791 : Blo 932582 1401791 := bstep (se 1 (by rfl) ⟨1051343, by rfl⟩ : syracuseStep 1401791 = 2102687) B2102687
theorem B934527 : Blo 932582 934527 := bstep (se 1 (by rfl) ⟨700895, by rfl⟩ : syracuseStep 934527 = 1401791) B1401791
theorem B7195367 : Blo 932582 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B3795119 : Blo 932582 3795119 := bstep (se 1 (by rfl) ⟨2846339, by rfl⟩ : syracuseStep 3795119 = 5692679) B5692679
theorem B2127655 : Blo 932582 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B2530079 : Blo 932582 2530079 := bstep (se 1 (by rfl) ⟨1897559, by rfl⟩ : syracuseStep 2530079 = 3795119) B3795119
theorem B4796911 : Blo 932582 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B2836873 : Blo 932582 2836873 := bstep (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) B2127655
theorem B3782497 : Blo 932582 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B1686719 : Blo 932582 1686719 := bstep (se 1 (by rfl) ⟨1265039, by rfl⟩ : syracuseStep 1686719 = 2530079) B2530079
theorem B25583525 : Blo 932582 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B1124479 : Blo 932582 1124479 := bstep (se 1 (by rfl) ⟨843359, by rfl⟩ : syracuseStep 1124479 = 1686719) B1686719
theorem B17055683 : Blo 932582 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B5043329 : Blo 932582 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B3362219 : Blo 932582 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B1499305 : Blo 932582 1499305 := bstep (se 2 (by rfl) ⟨562239, by rfl⟩ : syracuseStep 1499305 = 1124479) B1124479
theorem B11370455 : Blo 932582 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B1999073 : Blo 932582 1999073 := bstep (se 2 (by rfl) ⟨749652, by rfl⟩ : syracuseStep 1999073 = 1499305) B1499305
theorem B7580303 : Blo 932582 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B2241479 : Blo 932582 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B5053535 : Blo 932582 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B5977277 : Blo 932582 5977277 := bstep (se 3 (by rfl) ⟨1120739, by rfl⟩ : syracuseStep 5977277 = 2241479) B2241479
theorem B1332715 : Blo 932582 1332715 := bstep (se 1 (by rfl) ⟨999536, by rfl⟩ : syracuseStep 1332715 = 1999073) B1999073
theorem B1776953 : Blo 932582 1776953 := bstep (se 2 (by rfl) ⟨666357, by rfl⟩ : syracuseStep 1776953 = 1332715) B1332715
theorem B3984851 : Blo 932582 3984851 := bstep (se 1 (by rfl) ⟨2988638, by rfl⟩ : syracuseStep 3984851 = 5977277) B5977277
theorem B3369023 : Blo 932582 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B2656567 : Blo 932582 2656567 := bstep (se 1 (by rfl) ⟨1992425, by rfl⟩ : syracuseStep 2656567 = 3984851) B3984851
theorem B1184635 : Blo 932582 1184635 := bstep (se 1 (by rfl) ⟨888476, by rfl⟩ : syracuseStep 1184635 = 1776953) B1776953
theorem B2246015 : Blo 932582 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B3542089 : Blo 932582 3542089 := bstep (se 2 (by rfl) ⟨1328283, by rfl⟩ : syracuseStep 3542089 = 2656567) B2656567
theorem B1579513 : Blo 932582 1579513 := bstep (se 2 (by rfl) ⟨592317, by rfl⟩ : syracuseStep 1579513 = 1184635) B1184635
theorem B5989373 : Blo 932582 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B4722785 : Blo 932582 4722785 := bstep (se 2 (by rfl) ⟨1771044, by rfl⟩ : syracuseStep 4722785 = 3542089) B3542089
theorem B2106017 : Blo 932582 2106017 := bstep (se 2 (by rfl) ⟨789756, by rfl⟩ : syracuseStep 2106017 = 1579513) B1579513
theorem B3992915 : Blo 932582 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B3148523 : Blo 932582 3148523 := bstep (se 1 (by rfl) ⟨2361392, by rfl⟩ : syracuseStep 3148523 = 4722785) B4722785
theorem B1404011 : Blo 932582 1404011 := bstep (se 1 (by rfl) ⟨1053008, by rfl⟩ : syracuseStep 1404011 = 2106017) B2106017
theorem B10647773 : Blo 932582 10647773 := bstep (se 3 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 10647773 = 3992915) B3992915
theorem B2099015 : Blo 932582 2099015 := bstep (se 1 (by rfl) ⟨1574261, by rfl⟩ : syracuseStep 2099015 = 3148523) B3148523
theorem B936007 : Blo 932582 936007 := bstep (se 1 (by rfl) ⟨702005, by rfl⟩ : syracuseStep 936007 = 1404011) B1404011
theorem B7098515 : Blo 932582 7098515 := bstep (se 1 (by rfl) ⟨5323886, by rfl⟩ : syracuseStep 7098515 = 10647773) B10647773
theorem B4732343 : Blo 932582 4732343 := bstep (se 1 (by rfl) ⟨3549257, by rfl⟩ : syracuseStep 4732343 = 7098515) B7098515
theorem B1399343 : Blo 932582 1399343 := bstep (se 1 (by rfl) ⟨1049507, by rfl⟩ : syracuseStep 1399343 = 2099015) B2099015
theorem B3154895 : Blo 932582 3154895 := bstep (se 1 (by rfl) ⟨2366171, by rfl⟩ : syracuseStep 3154895 = 4732343) B4732343
theorem B932895 : Blo 932582 932895 := bstep (se 1 (by rfl) ⟨699671, by rfl⟩ : syracuseStep 932895 = 1399343) B1399343
theorem B2103263 : Blo 932582 2103263 := bstep (se 1 (by rfl) ⟨1577447, by rfl⟩ : syracuseStep 2103263 = 3154895) B3154895
theorem B1402175 : Blo 932582 1402175 := bstep (se 1 (by rfl) ⟨1051631, by rfl⟩ : syracuseStep 1402175 = 2103263) B2103263
theorem B934783 : Blo 932582 934783 := bstep (se 1 (by rfl) ⟨701087, by rfl⟩ : syracuseStep 934783 = 1402175) B1402175

theorem C0 (j : ℕ) (h1 : 233145 ≤ j) (h2 : j ≤ 233844) : Blo 932582 (4 * j + 3) := by
  interval_cases j
  · exact B932583
  · exact B932587
  · exact B932591
  · exact B932595
  · exact B932599
  · exact B932603
  · exact B932607
  · exact B932611
  · exact B932615
  · exact B932619
  · exact B932623
  · exact B932627
  · exact B932631
  · exact B932635
  · exact B932639
  · exact B932643
  · exact B932647
  · exact B932651
  · exact B932655
  · exact B932659
  · exact B932663
  · exact B932667
  · exact B932671
  · exact B932675
  · exact B932679
  · exact B932683
  · exact B932687
  · exact B932691
  · exact B932695
  · exact B932699
  · exact B932703
  · exact B932707
  · exact B932711
  · exact B932715
  · exact B932719
  · exact B932723
  · exact B932727
  · exact B932731
  · exact B932735
  · exact B932739
  · exact B932743
  · exact B932747
  · exact B932751
  · exact B932755
  · exact B932759
  · exact B932763
  · exact B932767
  · exact B932771
  · exact B932775
  · exact B932779
  · exact B932783
  · exact B932787
  · exact B932791
  · exact B932795
  · exact B932799
  · exact B932803
  · exact B932807
  · exact B932811
  · exact B932815
  · exact B932819
  · exact B932823
  · exact B932827
  · exact B932831
  · exact B932835
  · exact B932839
  · exact B932843
  · exact B932847
  · exact B932851
  · exact B932855
  · exact B932859
  · exact B932863
  · exact B932867
  · exact B932871
  · exact B932875
  · exact B932879
  · exact B932883
  · exact B932887
  · exact B932891
  · exact B932895
  · exact B932899
  · exact B932903
  · exact B932907
  · exact B932911
  · exact B932915
  · exact B932919
  · exact B932923
  · exact B932927
  · exact B932931
  · exact B932935
  · exact B932939
  · exact B932943
  · exact B932947
  · exact B932951
  · exact B932955
  · exact B932959
  · exact B932963
  · exact B932967
  · exact B932971
  · exact B932975
  · exact B932979
  · exact B932983
  · exact B932987
  · exact B932991
  · exact B932995
  · exact B932999
  · exact B933003
  · exact B933007
  · exact B933011
  · exact B933015
  · exact B933019
  · exact B933023
  · exact B933027
  · exact B933031
  · exact B933035
  · exact B933039
  · exact B933043
  · exact B933047
  · exact B933051
  · exact B933055
  · exact B933059
  · exact B933063
  · exact B933067
  · exact B933071
  · exact B933075
  · exact B933079
  · exact B933083
  · exact B933087
  · exact B933091
  · exact B933095
  · exact B933099
  · exact B933103
  · exact B933107
  · exact B933111
  · exact B933115
  · exact B933119
  · exact B933123
  · exact B933127
  · exact B933131
  · exact B933135
  · exact B933139
  · exact B933143
  · exact B933147
  · exact B933151
  · exact B933155
  · exact B933159
  · exact B933163
  · exact B933167
  · exact B933171
  · exact B933175
  · exact B933179
  · exact B933183
  · exact B933187
  · exact B933191
  · exact B933195
  · exact B933199
  · exact B933203
  · exact B933207
  · exact B933211
  · exact B933215
  · exact B933219
  · exact B933223
  · exact B933227
  · exact B933231
  · exact B933235
  · exact B933239
  · exact B933243
  · exact B933247
  · exact B933251
  · exact B933255
  · exact B933259
  · exact B933263
  · exact B933267
  · exact B933271
  · exact B933275
  · exact B933279
  · exact B933283
  · exact B933287
  · exact B933291
  · exact B933295
  · exact B933299
  · exact B933303
  · exact B933307
  · exact B933311
  · exact B933315
  · exact B933319
  · exact B933323
  · exact B933327
  · exact B933331
  · exact B933335
  · exact B933339
  · exact B933343
  · exact B933347
  · exact B933351
  · exact B933355
  · exact B933359
  · exact B933363
  · exact B933367
  · exact B933371
  · exact B933375
  · exact B933379
  · exact B933383
  · exact B933387
  · exact B933391
  · exact B933395
  · exact B933399
  · exact B933403
  · exact B933407
  · exact B933411
  · exact B933415
  · exact B933419
  · exact B933423
  · exact B933427
  · exact B933431
  · exact B933435
  · exact B933439
  · exact B933443
  · exact B933447
  · exact B933451
  · exact B933455
  · exact B933459
  · exact B933463
  · exact B933467
  · exact B933471
  · exact B933475
  · exact B933479
  · exact B933483
  · exact B933487
  · exact B933491
  · exact B933495
  · exact B933499
  · exact B933503
  · exact B933507
  · exact B933511
  · exact B933515
  · exact B933519
  · exact B933523
  · exact B933527
  · exact B933531
  · exact B933535
  · exact B933539
  · exact B933543
  · exact B933547
  · exact B933551
  · exact B933555
  · exact B933559
  · exact B933563
  · exact B933567
  · exact B933571
  · exact B933575
  · exact B933579
  · exact B933583
  · exact B933587
  · exact B933591
  · exact B933595
  · exact B933599
  · exact B933603
  · exact B933607
  · exact B933611
  · exact B933615
  · exact B933619
  · exact B933623
  · exact B933627
  · exact B933631
  · exact B933635
  · exact B933639
  · exact B933643
  · exact B933647
  · exact B933651
  · exact B933655
  · exact B933659
  · exact B933663
  · exact B933667
  · exact B933671
  · exact B933675
  · exact B933679
  · exact B933683
  · exact B933687
  · exact B933691
  · exact B933695
  · exact B933699
  · exact B933703
  · exact B933707
  · exact B933711
  · exact B933715
  · exact B933719
  · exact B933723
  · exact B933727
  · exact B933731
  · exact B933735
  · exact B933739
  · exact B933743
  · exact B933747
  · exact B933751
  · exact B933755
  · exact B933759
  · exact B933763
  · exact B933767
  · exact B933771
  · exact B933775
  · exact B933779
  · exact B933783
  · exact B933787
  · exact B933791
  · exact B933795
  · exact B933799
  · exact B933803
  · exact B933807
  · exact B933811
  · exact B933815
  · exact B933819
  · exact B933823
  · exact B933827
  · exact B933831
  · exact B933835
  · exact B933839
  · exact B933843
  · exact B933847
  · exact B933851
  · exact B933855
  · exact B933859
  · exact B933863
  · exact B933867
  · exact B933871
  · exact B933875
  · exact B933879
  · exact B933883
  · exact B933887
  · exact B933891
  · exact B933895
  · exact B933899
  · exact B933903
  · exact B933907
  · exact B933911
  · exact B933915
  · exact B933919
  · exact B933923
  · exact B933927
  · exact B933931
  · exact B933935
  · exact B933939
  · exact B933943
  · exact B933947
  · exact B933951
  · exact B933955
  · exact B933959
  · exact B933963
  · exact B933967
  · exact B933971
  · exact B933975
  · exact B933979
  · exact B933983
  · exact B933987
  · exact B933991
  · exact B933995
  · exact B933999
  · exact B934003
  · exact B934007
  · exact B934011
  · exact B934015
  · exact B934019
  · exact B934023
  · exact B934027
  · exact B934031
  · exact B934035
  · exact B934039
  · exact B934043
  · exact B934047
  · exact B934051
  · exact B934055
  · exact B934059
  · exact B934063
  · exact B934067
  · exact B934071
  · exact B934075
  · exact B934079
  · exact B934083
  · exact B934087
  · exact B934091
  · exact B934095
  · exact B934099
  · exact B934103
  · exact B934107
  · exact B934111
  · exact B934115
  · exact B934119
  · exact B934123
  · exact B934127
  · exact B934131
  · exact B934135
  · exact B934139
  · exact B934143
  · exact B934147
  · exact B934151
  · exact B934155
  · exact B934159
  · exact B934163
  · exact B934167
  · exact B934171
  · exact B934175
  · exact B934179
  · exact B934183
  · exact B934187
  · exact B934191
  · exact B934195
  · exact B934199
  · exact B934203
  · exact B934207
  · exact B934211
  · exact B934215
  · exact B934219
  · exact B934223
  · exact B934227
  · exact B934231
  · exact B934235
  · exact B934239
  · exact B934243
  · exact B934247
  · exact B934251
  · exact B934255
  · exact B934259
  · exact B934263
  · exact B934267
  · exact B934271
  · exact B934275
  · exact B934279
  · exact B934283
  · exact B934287
  · exact B934291
  · exact B934295
  · exact B934299
  · exact B934303
  · exact B934307
  · exact B934311
  · exact B934315
  · exact B934319
  · exact B934323
  · exact B934327
  · exact B934331
  · exact B934335
  · exact B934339
  · exact B934343
  · exact B934347
  · exact B934351
  · exact B934355
  · exact B934359
  · exact B934363
  · exact B934367
  · exact B934371
  · exact B934375
  · exact B934379
  · exact B934383
  · exact B934387
  · exact B934391
  · exact B934395
  · exact B934399
  · exact B934403
  · exact B934407
  · exact B934411
  · exact B934415
  · exact B934419
  · exact B934423
  · exact B934427
  · exact B934431
  · exact B934435
  · exact B934439
  · exact B934443
  · exact B934447
  · exact B934451
  · exact B934455
  · exact B934459
  · exact B934463
  · exact B934467
  · exact B934471
  · exact B934475
  · exact B934479
  · exact B934483
  · exact B934487
  · exact B934491
  · exact B934495
  · exact B934499
  · exact B934503
  · exact B934507
  · exact B934511
  · exact B934515
  · exact B934519
  · exact B934523
  · exact B934527
  · exact B934531
  · exact B934535
  · exact B934539
  · exact B934543
  · exact B934547
  · exact B934551
  · exact B934555
  · exact B934559
  · exact B934563
  · exact B934567
  · exact B934571
  · exact B934575
  · exact B934579
  · exact B934583
  · exact B934587
  · exact B934591
  · exact B934595
  · exact B934599
  · exact B934603
  · exact B934607
  · exact B934611
  · exact B934615
  · exact B934619
  · exact B934623
  · exact B934627
  · exact B934631
  · exact B934635
  · exact B934639
  · exact B934643
  · exact B934647
  · exact B934651
  · exact B934655
  · exact B934659
  · exact B934663
  · exact B934667
  · exact B934671
  · exact B934675
  · exact B934679
  · exact B934683
  · exact B934687
  · exact B934691
  · exact B934695
  · exact B934699
  · exact B934703
  · exact B934707
  · exact B934711
  · exact B934715
  · exact B934719
  · exact B934723
  · exact B934727
  · exact B934731
  · exact B934735
  · exact B934739
  · exact B934743
  · exact B934747
  · exact B934751
  · exact B934755
  · exact B934759
  · exact B934763
  · exact B934767
  · exact B934771
  · exact B934775
  · exact B934779
  · exact B934783
  · exact B934787
  · exact B934791
  · exact B934795
  · exact B934799
  · exact B934803
  · exact B934807
  · exact B934811
  · exact B934815
  · exact B934819
  · exact B934823
  · exact B934827
  · exact B934831
  · exact B934835
  · exact B934839
  · exact B934843
  · exact B934847
  · exact B934851
  · exact B934855
  · exact B934859
  · exact B934863
  · exact B934867
  · exact B934871
  · exact B934875
  · exact B934879
  · exact B934883
  · exact B934887
  · exact B934891
  · exact B934895
  · exact B934899
  · exact B934903
  · exact B934907
  · exact B934911
  · exact B934915
  · exact B934919
  · exact B934923
  · exact B934927
  · exact B934931
  · exact B934935
  · exact B934939
  · exact B934943
  · exact B934947
  · exact B934951
  · exact B934955
  · exact B934959
  · exact B934963
  · exact B934967
  · exact B934971
  · exact B934975
  · exact B934979
  · exact B934983
  · exact B934987
  · exact B934991
  · exact B934995
  · exact B934999
  · exact B935003
  · exact B935007
  · exact B935011
  · exact B935015
  · exact B935019
  · exact B935023
  · exact B935027
  · exact B935031
  · exact B935035
  · exact B935039
  · exact B935043
  · exact B935047
  · exact B935051
  · exact B935055
  · exact B935059
  · exact B935063
  · exact B935067
  · exact B935071
  · exact B935075
  · exact B935079
  · exact B935083
  · exact B935087
  · exact B935091
  · exact B935095
  · exact B935099
  · exact B935103
  · exact B935107
  · exact B935111
  · exact B935115
  · exact B935119
  · exact B935123
  · exact B935127
  · exact B935131
  · exact B935135
  · exact B935139
  · exact B935143
  · exact B935147
  · exact B935151
  · exact B935155
  · exact B935159
  · exact B935163
  · exact B935167
  · exact B935171
  · exact B935175
  · exact B935179
  · exact B935183
  · exact B935187
  · exact B935191
  · exact B935195
  · exact B935199
  · exact B935203
  · exact B935207
  · exact B935211
  · exact B935215
  · exact B935219
  · exact B935223
  · exact B935227
  · exact B935231
  · exact B935235
  · exact B935239
  · exact B935243
  · exact B935247
  · exact B935251
  · exact B935255
  · exact B935259
  · exact B935263
  · exact B935267
  · exact B935271
  · exact B935275
  · exact B935279
  · exact B935283
  · exact B935287
  · exact B935291
  · exact B935295
  · exact B935299
  · exact B935303
  · exact B935307
  · exact B935311
  · exact B935315
  · exact B935319
  · exact B935323
  · exact B935327
  · exact B935331
  · exact B935335
  · exact B935339
  · exact B935343
  · exact B935347
  · exact B935351
  · exact B935355
  · exact B935359
  · exact B935363
  · exact B935367
  · exact B935371
  · exact B935375
  · exact B935379

theorem C1 (j : ℕ) (h1 : 233845 ≤ j) (h2 : j ≤ 234144) : Blo 932582 (4 * j + 3) := by
  interval_cases j
  · exact B935383
  · exact B935387
  · exact B935391
  · exact B935395
  · exact B935399
  · exact B935403
  · exact B935407
  · exact B935411
  · exact B935415
  · exact B935419
  · exact B935423
  · exact B935427
  · exact B935431
  · exact B935435
  · exact B935439
  · exact B935443
  · exact B935447
  · exact B935451
  · exact B935455
  · exact B935459
  · exact B935463
  · exact B935467
  · exact B935471
  · exact B935475
  · exact B935479
  · exact B935483
  · exact B935487
  · exact B935491
  · exact B935495
  · exact B935499
  · exact B935503
  · exact B935507
  · exact B935511
  · exact B935515
  · exact B935519
  · exact B935523
  · exact B935527
  · exact B935531
  · exact B935535
  · exact B935539
  · exact B935543
  · exact B935547
  · exact B935551
  · exact B935555
  · exact B935559
  · exact B935563
  · exact B935567
  · exact B935571
  · exact B935575
  · exact B935579
  · exact B935583
  · exact B935587
  · exact B935591
  · exact B935595
  · exact B935599
  · exact B935603
  · exact B935607
  · exact B935611
  · exact B935615
  · exact B935619
  · exact B935623
  · exact B935627
  · exact B935631
  · exact B935635
  · exact B935639
  · exact B935643
  · exact B935647
  · exact B935651
  · exact B935655
  · exact B935659
  · exact B935663
  · exact B935667
  · exact B935671
  · exact B935675
  · exact B935679
  · exact B935683
  · exact B935687
  · exact B935691
  · exact B935695
  · exact B935699
  · exact B935703
  · exact B935707
  · exact B935711
  · exact B935715
  · exact B935719
  · exact B935723
  · exact B935727
  · exact B935731
  · exact B935735
  · exact B935739
  · exact B935743
  · exact B935747
  · exact B935751
  · exact B935755
  · exact B935759
  · exact B935763
  · exact B935767
  · exact B935771
  · exact B935775
  · exact B935779
  · exact B935783
  · exact B935787
  · exact B935791
  · exact B935795
  · exact B935799
  · exact B935803
  · exact B935807
  · exact B935811
  · exact B935815
  · exact B935819
  · exact B935823
  · exact B935827
  · exact B935831
  · exact B935835
  · exact B935839
  · exact B935843
  · exact B935847
  · exact B935851
  · exact B935855
  · exact B935859
  · exact B935863
  · exact B935867
  · exact B935871
  · exact B935875
  · exact B935879
  · exact B935883
  · exact B935887
  · exact B935891
  · exact B935895
  · exact B935899
  · exact B935903
  · exact B935907
  · exact B935911
  · exact B935915
  · exact B935919
  · exact B935923
  · exact B935927
  · exact B935931
  · exact B935935
  · exact B935939
  · exact B935943
  · exact B935947
  · exact B935951
  · exact B935955
  · exact B935959
  · exact B935963
  · exact B935967
  · exact B935971
  · exact B935975
  · exact B935979
  · exact B935983
  · exact B935987
  · exact B935991
  · exact B935995
  · exact B935999
  · exact B936003
  · exact B936007
  · exact B936011
  · exact B936015
  · exact B936019
  · exact B936023
  · exact B936027
  · exact B936031
  · exact B936035
  · exact B936039
  · exact B936043
  · exact B936047
  · exact B936051
  · exact B936055
  · exact B936059
  · exact B936063
  · exact B936067
  · exact B936071
  · exact B936075
  · exact B936079
  · exact B936083
  · exact B936087
  · exact B936091
  · exact B936095
  · exact B936099
  · exact B936103
  · exact B936107
  · exact B936111
  · exact B936115
  · exact B936119
  · exact B936123
  · exact B936127
  · exact B936131
  · exact B936135
  · exact B936139
  · exact B936143
  · exact B936147
  · exact B936151
  · exact B936155
  · exact B936159
  · exact B936163
  · exact B936167
  · exact B936171
  · exact B936175
  · exact B936179
  · exact B936183
  · exact B936187
  · exact B936191
  · exact B936195
  · exact B936199
  · exact B936203
  · exact B936207
  · exact B936211
  · exact B936215
  · exact B936219
  · exact B936223
  · exact B936227
  · exact B936231
  · exact B936235
  · exact B936239
  · exact B936243
  · exact B936247
  · exact B936251
  · exact B936255
  · exact B936259
  · exact B936263
  · exact B936267
  · exact B936271
  · exact B936275
  · exact B936279
  · exact B936283
  · exact B936287
  · exact B936291
  · exact B936295
  · exact B936299
  · exact B936303
  · exact B936307
  · exact B936311
  · exact B936315
  · exact B936319
  · exact B936323
  · exact B936327
  · exact B936331
  · exact B936335
  · exact B936339
  · exact B936343
  · exact B936347
  · exact B936351
  · exact B936355
  · exact B936359
  · exact B936363
  · exact B936367
  · exact B936371
  · exact B936375
  · exact B936379
  · exact B936383
  · exact B936387
  · exact B936391
  · exact B936395
  · exact B936399
  · exact B936403
  · exact B936407
  · exact B936411
  · exact B936415
  · exact B936419
  · exact B936423
  · exact B936427
  · exact B936431
  · exact B936435
  · exact B936439
  · exact B936443
  · exact B936447
  · exact B936451
  · exact B936455
  · exact B936459
  · exact B936463
  · exact B936467
  · exact B936471
  · exact B936475
  · exact B936479
  · exact B936483
  · exact B936487
  · exact B936491
  · exact B936495
  · exact B936499
  · exact B936503
  · exact B936507
  · exact B936511
  · exact B936515
  · exact B936519
  · exact B936523
  · exact B936527
  · exact B936531
  · exact B936535
  · exact B936539
  · exact B936543
  · exact B936547
  · exact B936551
  · exact B936555
  · exact B936559
  · exact B936563
  · exact B936567
  · exact B936571
  · exact B936575
  · exact B936579

theorem solution (m : ℕ) (hlo : 932582 ≤ m) (hhi : m ≤ 936582) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 233145 ≤ j := by omega
    have hj2 : j ≤ 234144 := by omega
    have hb : Blo 932582 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 233845 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
