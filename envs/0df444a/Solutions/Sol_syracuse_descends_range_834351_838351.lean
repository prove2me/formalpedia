-- Prove2me | solution 1 for syracuse_descends_range_834351_838351
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:49.909709+00:00
-- url     : https://prove2.me/submissions/1bab7cf8-7ff5-4447-9def-dfee563f395e

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


theorem B16482325 : Blo 834351 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B1409069 : Blo 834351 1409069 := bbase (se 3 (by rfl) ⟨264200, by rfl⟩ : syracuseStep 1409069 = 528401) (by norm_num)
theorem B1409197 : Blo 834351 1409197 := bbase (se 3 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 1409197 = 528449) (by norm_num)
theorem B1409285 : Blo 834351 1409285 := bbase (se 4 (by rfl) ⟨132120, by rfl⟩ : syracuseStep 1409285 = 264241) (by norm_num)
theorem B2818421 : Blo 834351 2818421 := bbase (se 5 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 2818421 = 264227) (by norm_num)
theorem B6357365 : Blo 834351 6357365 := bbase (se 5 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 6357365 = 596003) (by norm_num)
theorem B1409413 : Blo 834351 1409413 := bbase (se 4 (by rfl) ⟨132132, by rfl⟩ : syracuseStep 1409413 = 264265) (by norm_num)
theorem B1409501 : Blo 834351 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B3572261 : Blo 834351 3572261 := bbase (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) (by norm_num)
theorem B1409629 : Blo 834351 1409629 := bbase (se 3 (by rfl) ⟨264305, by rfl⟩ : syracuseStep 1409629 = 528611) (by norm_num)
theorem B1409717 : Blo 834351 1409717 := bbase (se 5 (by rfl) ⟨66080, by rfl⟩ : syracuseStep 1409717 = 132161) (by norm_num)
theorem B2818853 : Blo 834351 2818853 := bbase (se 4 (by rfl) ⟨264267, by rfl⟩ : syracuseStep 2818853 = 528535) (by norm_num)
theorem B1409845 : Blo 834351 1409845 := bbase (se 5 (by rfl) ⟨66086, by rfl⟩ : syracuseStep 1409845 = 132173) (by norm_num)
theorem B1409933 : Blo 834351 1409933 := bbase (se 3 (by rfl) ⟨264362, by rfl⟩ : syracuseStep 1409933 = 528725) (by norm_num)
theorem B4228037 : Blo 834351 4228037 := bbase (se 4 (by rfl) ⟨396378, by rfl⟩ : syracuseStep 4228037 = 792757) (by norm_num)
theorem B1410061 : Blo 834351 1410061 := bbase (se 3 (by rfl) ⟨264386, by rfl⟩ : syracuseStep 1410061 = 528773) (by norm_num)
theorem B1410149 : Blo 834351 1410149 := bbase (se 4 (by rfl) ⟨132201, by rfl⟩ : syracuseStep 1410149 = 264403) (by norm_num)
theorem B4752533 : Blo 834351 4752533 := bbase (se 6 (by rfl) ⟨111387, by rfl⟩ : syracuseStep 4752533 = 222775) (by norm_num)
theorem B2819285 : Blo 834351 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B951517 : Blo 834351 951517 := bbase (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) (by norm_num)
theorem B1410277 : Blo 834351 1410277 := bbase (se 4 (by rfl) ⟨132213, by rfl⟩ : syracuseStep 1410277 = 264427) (by norm_num)
theorem B1410365 : Blo 834351 1410365 := bbase (se 3 (by rfl) ⟨264443, by rfl⟩ : syracuseStep 1410365 = 528887) (by norm_num)
theorem B1410493 : Blo 834351 1410493 := bbase (se 3 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 1410493 = 528935) (by norm_num)
theorem B3180005 : Blo 834351 3180005 := bbase (se 4 (by rfl) ⟨298125, by rfl⟩ : syracuseStep 3180005 = 596251) (by norm_num)
theorem B1410581 : Blo 834351 1410581 := bbase (se 6 (by rfl) ⟨33060, by rfl⟩ : syracuseStep 1410581 = 66121) (by norm_num)
theorem B2033189 : Blo 834351 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B951869 : Blo 834351 951869 := bbase (se 3 (by rfl) ⟨178475, by rfl⟩ : syracuseStep 951869 = 356951) (by norm_num)
theorem B2819717 : Blo 834351 2819717 := bbase (se 4 (by rfl) ⟨264348, by rfl⟩ : syracuseStep 2819717 = 528697) (by norm_num)
theorem B1410709 : Blo 834351 1410709 := bbase (se 6 (by rfl) ⟨33063, by rfl⟩ : syracuseStep 1410709 = 66127) (by norm_num)
theorem B1410797 : Blo 834351 1410797 := bbase (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) (by norm_num)
theorem B3180293 : Blo 834351 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B1607509 : Blo 834351 1607509 := bbase (se 9 (by rfl) ⟨4709, by rfl⟩ : syracuseStep 1607509 = 9419) (by norm_num)
theorem B1410925 : Blo 834351 1410925 := bbase (se 3 (by rfl) ⟨264548, by rfl⟩ : syracuseStep 1410925 = 529097) (by norm_num)
theorem B6096757 : Blo 834351 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B1411013 : Blo 834351 1411013 := bbase (se 4 (by rfl) ⟨132282, by rfl⟩ : syracuseStep 1411013 = 264565) (by norm_num)
theorem B2820149 : Blo 834351 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B1411141 : Blo 834351 1411141 := bbase (se 4 (by rfl) ⟨132294, by rfl⟩ : syracuseStep 1411141 = 264589) (by norm_num)
theorem B1411229 : Blo 834351 1411229 := bbase (se 3 (by rfl) ⟨264605, by rfl⟩ : syracuseStep 1411229 = 529211) (by norm_num)
theorem B4229333 : Blo 834351 4229333 := bbase (se 7 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 4229333 = 99125) (by norm_num)
theorem B3574037 : Blo 834351 3574037 := bbase (se 6 (by rfl) ⟨83766, by rfl⟩ : syracuseStep 3574037 = 167533) (by norm_num)
theorem B1411357 : Blo 834351 1411357 := bbase (se 3 (by rfl) ⟨264629, by rfl⟩ : syracuseStep 1411357 = 529259) (by norm_num)
theorem B1411445 : Blo 834351 1411445 := bbase (se 5 (by rfl) ⟨66161, by rfl⟩ : syracuseStep 1411445 = 132323) (by norm_num)
theorem B2820581 : Blo 834351 2820581 := bbase (se 4 (by rfl) ⟨264429, by rfl⟩ : syracuseStep 2820581 = 528859) (by norm_num)
theorem B1411573 : Blo 834351 1411573 := bbase (se 5 (by rfl) ⟨66167, by rfl⟩ : syracuseStep 1411573 = 132335) (by norm_num)
theorem B3574277 : Blo 834351 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B1411661 : Blo 834351 1411661 := bbase (se 3 (by rfl) ⟨264686, by rfl⟩ : syracuseStep 1411661 = 529373) (by norm_num)
theorem B2722405 : Blo 834351 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B1411789 : Blo 834351 1411789 := bbase (se 3 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 1411789 = 529421) (by norm_num)
theorem B1018621 : Blo 834351 1018621 := bbase (se 3 (by rfl) ⟨190991, by rfl⟩ : syracuseStep 1018621 = 381983) (by norm_num)
theorem B1018661 : Blo 834351 1018661 := bbase (se 4 (by rfl) ⟨95499, by rfl⟩ : syracuseStep 1018661 = 190999) (by norm_num)
theorem B1411877 : Blo 834351 1411877 := bbase (se 4 (by rfl) ⟨132363, by rfl⟩ : syracuseStep 1411877 = 264727) (by norm_num)
theorem B2263925 : Blo 834351 2263925 := bbase (se 5 (by rfl) ⟨106121, by rfl⟩ : syracuseStep 2263925 = 212243) (by norm_num)
theorem B2821013 : Blo 834351 2821013 := bbase (se 6 (by rfl) ⟨66117, by rfl⟩ : syracuseStep 2821013 = 132235) (by norm_num)
theorem B1412005 : Blo 834351 1412005 := bbase (se 4 (by rfl) ⟨132375, by rfl⟩ : syracuseStep 1412005 = 264751) (by norm_num)
theorem B3181477 : Blo 834351 3181477 := bbase (se 4 (by rfl) ⟨298263, by rfl⟩ : syracuseStep 3181477 = 596527) (by norm_num)
theorem B1412093 : Blo 834351 1412093 := bbase (se 3 (by rfl) ⟨264767, by rfl⟩ : syracuseStep 1412093 = 529535) (by norm_num)
theorem B1412221 : Blo 834351 1412221 := bbase (se 3 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 1412221 = 529583) (by norm_num)
theorem B1412309 : Blo 834351 1412309 := bbase (se 7 (by rfl) ⟨16550, by rfl⟩ : syracuseStep 1412309 = 33101) (by norm_num)
theorem B3181781 : Blo 834351 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B1510645 : Blo 834351 1510645 := bbase (se 5 (by rfl) ⟨70811, by rfl⟩ : syracuseStep 1510645 = 141623) (by norm_num)
theorem B1510709 : Blo 834351 1510709 := bbase (se 5 (by rfl) ⟨70814, by rfl⟩ : syracuseStep 1510709 = 141629) (by norm_num)
theorem B2821445 : Blo 834351 2821445 := bbase (se 4 (by rfl) ⟨264510, by rfl⟩ : syracuseStep 2821445 = 529021) (by norm_num)
theorem B1412437 : Blo 834351 1412437 := bbase (se 11 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 1412437 = 2069) (by norm_num)
theorem B1412525 : Blo 834351 1412525 := bbase (se 3 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 1412525 = 529697) (by norm_num)
theorem B4230629 : Blo 834351 4230629 := bbase (se 4 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 4230629 = 793243) (by norm_num)
theorem B1412653 : Blo 834351 1412653 := bbase (se 3 (by rfl) ⟨264872, by rfl⟩ : syracuseStep 1412653 = 529745) (by norm_num)
theorem B3018293 : Blo 834351 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B1412741 : Blo 834351 1412741 := bbase (se 4 (by rfl) ⟨132444, by rfl⟩ : syracuseStep 1412741 = 264889) (by norm_num)
theorem B954025 : Blo 834351 954025 := bbase (se 2 (by rfl) ⟨357759, by rfl⟩ : syracuseStep 954025 = 715519) (by norm_num)
theorem B32640725 : Blo 834351 32640725 := bbase (se 7 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 32640725 = 765017) (by norm_num)
theorem B2821877 : Blo 834351 2821877 := bbase (se 5 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 2821877 = 264551) (by norm_num)
theorem B954109 : Blo 834351 954109 := bbase (se 3 (by rfl) ⟨178895, by rfl⟩ : syracuseStep 954109 = 357791) (by norm_num)
theorem B1412869 : Blo 834351 1412869 := bbase (se 4 (by rfl) ⟨132456, by rfl⟩ : syracuseStep 1412869 = 264913) (by norm_num)
theorem B1412957 : Blo 834351 1412957 := bbase (se 3 (by rfl) ⟨264929, by rfl⟩ : syracuseStep 1412957 = 529859) (by norm_num)
theorem B4820885 : Blo 834351 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B1413085 : Blo 834351 1413085 := bbase (se 3 (by rfl) ⟨264953, by rfl⟩ : syracuseStep 1413085 = 529907) (by norm_num)
theorem B1413173 : Blo 834351 1413173 := bbase (se 5 (by rfl) ⟨66242, by rfl⟩ : syracuseStep 1413173 = 132485) (by norm_num)
theorem B1085509 : Blo 834351 1085509 := bbase (se 4 (by rfl) ⟨101766, by rfl⟩ : syracuseStep 1085509 = 203533) (by norm_num)
theorem B2822309 : Blo 834351 2822309 := bbase (se 4 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 2822309 = 529183) (by norm_num)
theorem B1413301 : Blo 834351 1413301 := bbase (se 5 (by rfl) ⟨66248, by rfl⟩ : syracuseStep 1413301 = 132497) (by norm_num)
theorem B1413389 : Blo 834351 1413389 := bbase (se 3 (by rfl) ⟨265010, by rfl⟩ : syracuseStep 1413389 = 530021) (by norm_num)
theorem B1806725 : Blo 834351 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B1413517 : Blo 834351 1413517 := bbase (se 3 (by rfl) ⟨265034, by rfl⟩ : syracuseStep 1413517 = 530069) (by norm_num)
theorem B1085905 : Blo 834351 1085905 := bbase (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) (by norm_num)
theorem B1413605 : Blo 834351 1413605 := bbase (se 4 (by rfl) ⟨132525, by rfl⟩ : syracuseStep 1413605 = 265051) (by norm_num)
theorem B3215893 : Blo 834351 3215893 := bbase (se 6 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 3215893 = 150745) (by norm_num)
theorem B954901 : Blo 834351 954901 := bbase (se 6 (by rfl) ⟨22380, by rfl⟩ : syracuseStep 954901 = 44761) (by norm_num)
theorem B3019285 : Blo 834351 3019285 := bbase (se 6 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 3019285 = 141529) (by norm_num)
theorem B2822741 : Blo 834351 2822741 := bbase (se 8 (by rfl) ⟨16539, by rfl⟩ : syracuseStep 2822741 = 33079) (by norm_num)
theorem B1413733 : Blo 834351 1413733 := bbase (se 4 (by rfl) ⟨132537, by rfl⟩ : syracuseStep 1413733 = 265075) (by norm_num)
theorem B954985 : Blo 834351 954985 := bbase (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) (by norm_num)
theorem B1413821 : Blo 834351 1413821 := bbase (se 3 (by rfl) ⟨265091, by rfl⟩ : syracuseStep 1413821 = 530183) (by norm_num)
theorem B4231925 : Blo 834351 4231925 := bbase (se 5 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 4231925 = 396743) (by norm_num)
theorem B3576565 : Blo 834351 3576565 := bbase (se 5 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 3576565 = 335303) (by norm_num)
theorem B1413949 : Blo 834351 1413949 := bbase (se 3 (by rfl) ⟨265115, by rfl⟩ : syracuseStep 1413949 = 530231) (by norm_num)
theorem B7246709 : Blo 834351 7246709 := bbase (se 5 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 7246709 = 679379) (by norm_num)
theorem B1414037 : Blo 834351 1414037 := bbase (se 6 (by rfl) ⟨33141, by rfl⟩ : syracuseStep 1414037 = 66283) (by norm_num)
theorem B2823173 : Blo 834351 2823173 := bbase (se 4 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 2823173 = 529345) (by norm_num)
theorem B1414165 : Blo 834351 1414165 := bbase (se 6 (by rfl) ⟨33144, by rfl⟩ : syracuseStep 1414165 = 66289) (by norm_num)
theorem B2036773 : Blo 834351 2036773 := bbase (se 4 (by rfl) ⟨190947, by rfl⟩ : syracuseStep 2036773 = 381895) (by norm_num)
theorem B1905709 : Blo 834351 1905709 := bbase (se 3 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 1905709 = 714641) (by norm_num)
theorem B1610813 : Blo 834351 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B1414253 : Blo 834351 1414253 := bbase (se 3 (by rfl) ⟨265172, by rfl⟩ : syracuseStep 1414253 = 530345) (by norm_num)
theorem B1905781 : Blo 834351 1905781 := bbase (se 5 (by rfl) ⟨89333, by rfl⟩ : syracuseStep 1905781 = 178667) (by norm_num)
theorem B1414381 : Blo 834351 1414381 := bbase (se 3 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 1414381 = 530393) (by norm_num)
theorem B1414469 : Blo 834351 1414469 := bbase (se 4 (by rfl) ⟨132606, by rfl⟩ : syracuseStep 1414469 = 265213) (by norm_num)
theorem B955741 : Blo 834351 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B1611149 : Blo 834351 1611149 := bbase (se 3 (by rfl) ⟨302090, by rfl⟩ : syracuseStep 1611149 = 604181) (by norm_num)
theorem B2823605 : Blo 834351 2823605 := bbase (se 5 (by rfl) ⟨132356, by rfl⟩ : syracuseStep 2823605 = 264713) (by norm_num)
theorem B1414597 : Blo 834351 1414597 := bbase (se 4 (by rfl) ⟨132618, by rfl⟩ : syracuseStep 1414597 = 265237) (by norm_num)
theorem B5346805 : Blo 834351 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B1414685 : Blo 834351 1414685 := bbase (se 3 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 1414685 = 530507) (by norm_num)
theorem B2856485 : Blo 834351 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B2824037 : Blo 834351 2824037 := bbase (se 4 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 2824037 = 529507) (by norm_num)
theorem B9050069 : Blo 834351 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B4233221 : Blo 834351 4233221 := bbase (se 4 (by rfl) ⟨396864, by rfl⟩ : syracuseStep 4233221 = 793729) (by norm_num)
theorem B6035573 : Blo 834351 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B891049 : Blo 834351 891049 := bbase (se 2 (by rfl) ⟨334143, by rfl⟩ : syracuseStep 891049 = 668287) (by norm_num)
theorem B3578053 : Blo 834351 3578053 := bbase (se 4 (by rfl) ⟨335442, by rfl⟩ : syracuseStep 3578053 = 670885) (by norm_num)
theorem B1251533 : Blo 834351 1251533 := bbase (se 3 (by rfl) ⟨234662, by rfl⟩ : syracuseStep 1251533 = 469325) (by norm_num)
theorem B3578069 : Blo 834351 3578069 := bbase (se 7 (by rfl) ⟨41930, by rfl⟩ : syracuseStep 3578069 = 83861) (by norm_num)
theorem B1251557 : Blo 834351 1251557 := bbase (se 4 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 1251557 = 234667) (by norm_num)
theorem B891109 : Blo 834351 891109 := bbase (se 4 (by rfl) ⟨83541, by rfl⟩ : syracuseStep 891109 = 167083) (by norm_num)
theorem B1251581 : Blo 834351 1251581 := bbase (se 3 (by rfl) ⟨234671, by rfl⟩ : syracuseStep 1251581 = 469343) (by norm_num)
theorem B1251605 : Blo 834351 1251605 := bbase (se 6 (by rfl) ⟨29334, by rfl⟩ : syracuseStep 1251605 = 58669) (by norm_num)
theorem B2824469 : Blo 834351 2824469 := bbase (se 6 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 2824469 = 132397) (by norm_num)
theorem B1251629 : Blo 834351 1251629 := bbase (se 3 (by rfl) ⟨234680, by rfl⟩ : syracuseStep 1251629 = 469361) (by norm_num)
theorem B1251653 : Blo 834351 1251653 := bbase (se 4 (by rfl) ⟨117342, by rfl⟩ : syracuseStep 1251653 = 234685) (by norm_num)
theorem B1251677 : Blo 834351 1251677 := bbase (se 3 (by rfl) ⟨234689, by rfl⟩ : syracuseStep 1251677 = 469379) (by norm_num)
theorem B1251701 : Blo 834351 1251701 := bbase (se 5 (by rfl) ⟨58673, by rfl⟩ : syracuseStep 1251701 = 117347) (by norm_num)
theorem B1251725 : Blo 834351 1251725 := bbase (se 3 (by rfl) ⟨234698, by rfl⟩ : syracuseStep 1251725 = 469397) (by norm_num)
theorem B1251749 : Blo 834351 1251749 := bbase (se 4 (by rfl) ⟨117351, by rfl⟩ : syracuseStep 1251749 = 234703) (by norm_num)
theorem B1251773 : Blo 834351 1251773 := bbase (se 3 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 1251773 = 469415) (by norm_num)
theorem B1251797 : Blo 834351 1251797 := bbase (se 7 (by rfl) ⟨14669, by rfl⟩ : syracuseStep 1251797 = 29339) (by norm_num)
theorem B1251821 : Blo 834351 1251821 := bbase (se 3 (by rfl) ⟨234716, by rfl⟩ : syracuseStep 1251821 = 469433) (by norm_num)
theorem B1251845 : Blo 834351 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B1251869 : Blo 834351 1251869 := bbase (se 3 (by rfl) ⟨234725, by rfl⟩ : syracuseStep 1251869 = 469451) (by norm_num)
theorem B891425 : Blo 834351 891425 := bbase (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) (by norm_num)
theorem B1251893 : Blo 834351 1251893 := bbase (se 5 (by rfl) ⟨58682, by rfl⟩ : syracuseStep 1251893 = 117365) (by norm_num)
theorem B1251917 : Blo 834351 1251917 := bbase (se 3 (by rfl) ⟨234734, by rfl⟩ : syracuseStep 1251917 = 469469) (by norm_num)
theorem B1251941 : Blo 834351 1251941 := bbase (se 4 (by rfl) ⟨117369, by rfl⟩ : syracuseStep 1251941 = 234739) (by norm_num)
theorem B1251965 : Blo 834351 1251965 := bbase (se 3 (by rfl) ⟨234743, by rfl⟩ : syracuseStep 1251965 = 469487) (by norm_num)
theorem B1251989 : Blo 834351 1251989 := bbase (se 6 (by rfl) ⟨29343, by rfl⟩ : syracuseStep 1251989 = 58687) (by norm_num)
theorem B1252013 : Blo 834351 1252013 := bbase (se 3 (by rfl) ⟨234752, by rfl⟩ : syracuseStep 1252013 = 469505) (by norm_num)
theorem B1252037 : Blo 834351 1252037 := bbase (se 4 (by rfl) ⟨117378, by rfl⟩ : syracuseStep 1252037 = 234757) (by norm_num)
theorem B2824901 : Blo 834351 2824901 := bbase (se 4 (by rfl) ⟨264834, by rfl⟩ : syracuseStep 2824901 = 529669) (by norm_num)
theorem B1252061 : Blo 834351 1252061 := bbase (se 3 (by rfl) ⟨234761, by rfl⟩ : syracuseStep 1252061 = 469523) (by norm_num)
theorem B1252085 : Blo 834351 1252085 := bbase (se 5 (by rfl) ⟨58691, by rfl⟩ : syracuseStep 1252085 = 117383) (by norm_num)
theorem B4528885 : Blo 834351 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B1252109 : Blo 834351 1252109 := bbase (se 3 (by rfl) ⟨234770, by rfl⟩ : syracuseStep 1252109 = 469541) (by norm_num)
theorem B1252133 : Blo 834351 1252133 := bbase (se 4 (by rfl) ⟨117387, by rfl⟩ : syracuseStep 1252133 = 234775) (by norm_num)
theorem B2005813 : Blo 834351 2005813 := bbase (se 5 (by rfl) ⟨94022, by rfl⟩ : syracuseStep 2005813 = 188045) (by norm_num)
theorem B1252157 : Blo 834351 1252157 := bbase (se 3 (by rfl) ⟨234779, by rfl⟩ : syracuseStep 1252157 = 469559) (by norm_num)
theorem B1252181 : Blo 834351 1252181 := bbase (se 9 (by rfl) ⟨3668, by rfl⟩ : syracuseStep 1252181 = 7337) (by norm_num)
theorem B1252205 : Blo 834351 1252205 := bbase (se 3 (by rfl) ⟨234788, by rfl⟩ : syracuseStep 1252205 = 469577) (by norm_num)
theorem B1252229 : Blo 834351 1252229 := bbase (se 4 (by rfl) ⟨117396, by rfl⟩ : syracuseStep 1252229 = 234793) (by norm_num)
theorem B1252253 : Blo 834351 1252253 := bbase (se 3 (by rfl) ⟨234797, by rfl⟩ : syracuseStep 1252253 = 469595) (by norm_num)
theorem B1252277 : Blo 834351 1252277 := bbase (se 5 (by rfl) ⟨58700, by rfl⟩ : syracuseStep 1252277 = 117401) (by norm_num)
theorem B3218357 : Blo 834351 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1252301 : Blo 834351 1252301 := bbase (se 3 (by rfl) ⟨234806, by rfl⟩ : syracuseStep 1252301 = 469613) (by norm_num)
theorem B891869 : Blo 834351 891869 := bbase (se 3 (by rfl) ⟨167225, by rfl⟩ : syracuseStep 891869 = 334451) (by norm_num)
theorem B1252325 : Blo 834351 1252325 := bbase (se 4 (by rfl) ⟨117405, by rfl⟩ : syracuseStep 1252325 = 234811) (by norm_num)
theorem B1252349 : Blo 834351 1252349 := bbase (se 3 (by rfl) ⟨234815, by rfl⟩ : syracuseStep 1252349 = 469631) (by norm_num)
theorem B1252373 : Blo 834351 1252373 := bbase (se 6 (by rfl) ⟨29352, by rfl⟩ : syracuseStep 1252373 = 58705) (by norm_num)
theorem B891929 : Blo 834351 891929 := bbase (se 2 (by rfl) ⟨334473, by rfl⟩ : syracuseStep 891929 = 668947) (by norm_num)
theorem B1252397 : Blo 834351 1252397 := bbase (se 3 (by rfl) ⟨234824, by rfl⟩ : syracuseStep 1252397 = 469649) (by norm_num)
theorem B1252421 : Blo 834351 1252421 := bbase (se 4 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 1252421 = 234829) (by norm_num)
theorem B2858053 : Blo 834351 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B1252445 : Blo 834351 1252445 := bbase (se 3 (by rfl) ⟨234833, by rfl⟩ : syracuseStep 1252445 = 469667) (by norm_num)
theorem B2825333 : Blo 834351 2825333 := bbase (se 5 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 2825333 = 264875) (by norm_num)
theorem B1252469 : Blo 834351 1252469 := bbase (se 5 (by rfl) ⟨58709, by rfl⟩ : syracuseStep 1252469 = 117419) (by norm_num)
theorem B1252493 : Blo 834351 1252493 := bbase (se 3 (by rfl) ⟨234842, by rfl⟩ : syracuseStep 1252493 = 469685) (by norm_num)
theorem B892057 : Blo 834351 892057 := bbase (se 2 (by rfl) ⟨334521, by rfl⟩ : syracuseStep 892057 = 669043) (by norm_num)
theorem B1252517 : Blo 834351 1252517 := bbase (se 4 (by rfl) ⟨117423, by rfl⟩ : syracuseStep 1252517 = 234847) (by norm_num)
theorem B1252541 : Blo 834351 1252541 := bbase (se 3 (by rfl) ⟨234851, by rfl⟩ : syracuseStep 1252541 = 469703) (by norm_num)
theorem B1252565 : Blo 834351 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1252589 : Blo 834351 1252589 := bbase (se 3 (by rfl) ⟨234860, by rfl⟩ : syracuseStep 1252589 = 469721) (by norm_num)
theorem B1252613 : Blo 834351 1252613 := bbase (se 4 (by rfl) ⟨117432, by rfl⟩ : syracuseStep 1252613 = 234865) (by norm_num)
theorem B1056017 : Blo 834351 1056017 := bbase (se 2 (by rfl) ⟨396006, by rfl⟩ : syracuseStep 1056017 = 792013) (by norm_num)
theorem B4234517 : Blo 834351 4234517 := bbase (se 6 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 4234517 = 198493) (by norm_num)
theorem B1252637 : Blo 834351 1252637 := bbase (se 3 (by rfl) ⟨234869, by rfl⟩ : syracuseStep 1252637 = 469739) (by norm_num)
theorem B1252661 : Blo 834351 1252661 := bbase (se 5 (by rfl) ⟨58718, by rfl⟩ : syracuseStep 1252661 = 117437) (by norm_num)
theorem B1056073 : Blo 834351 1056073 := bbase (se 2 (by rfl) ⟨396027, by rfl⟩ : syracuseStep 1056073 = 792055) (by norm_num)
theorem B1252685 : Blo 834351 1252685 := bbase (se 3 (by rfl) ⟨234878, by rfl⟩ : syracuseStep 1252685 = 469757) (by norm_num)
theorem B1252709 : Blo 834351 1252709 := bbase (se 4 (by rfl) ⟨117441, by rfl⟩ : syracuseStep 1252709 = 234883) (by norm_num)
theorem B1252733 : Blo 834351 1252733 := bbase (se 3 (by rfl) ⟨234887, by rfl⟩ : syracuseStep 1252733 = 469775) (by norm_num)
theorem B1252757 : Blo 834351 1252757 := bbase (se 6 (by rfl) ⟨29361, by rfl⟩ : syracuseStep 1252757 = 58723) (by norm_num)
theorem B1056169 : Blo 834351 1056169 := bbase (se 2 (by rfl) ⟨396063, by rfl⟩ : syracuseStep 1056169 = 792127) (by norm_num)
theorem B1252781 : Blo 834351 1252781 := bbase (se 3 (by rfl) ⟨234896, by rfl⟩ : syracuseStep 1252781 = 469793) (by norm_num)
theorem B859577 : Blo 834351 859577 := bbase (se 2 (by rfl) ⟨322341, by rfl⟩ : syracuseStep 859577 = 644683) (by norm_num)
theorem B1252805 : Blo 834351 1252805 := bbase (se 4 (by rfl) ⟨117450, by rfl⟩ : syracuseStep 1252805 = 234901) (by norm_num)
theorem B1252829 : Blo 834351 1252829 := bbase (se 3 (by rfl) ⟨234905, by rfl⟩ : syracuseStep 1252829 = 469811) (by norm_num)
theorem B1252853 : Blo 834351 1252853 := bbase (se 5 (by rfl) ⟨58727, by rfl⟩ : syracuseStep 1252853 = 117455) (by norm_num)
theorem B1252877 : Blo 834351 1252877 := bbase (se 3 (by rfl) ⟨234914, by rfl⟩ : syracuseStep 1252877 = 469829) (by norm_num)
theorem B1252901 : Blo 834351 1252901 := bbase (se 4 (by rfl) ⟨117459, by rfl⟩ : syracuseStep 1252901 = 234919) (by norm_num)
theorem B2825765 : Blo 834351 2825765 := bbase (se 4 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 2825765 = 529831) (by norm_num)
theorem B1252925 : Blo 834351 1252925 := bbase (se 3 (by rfl) ⟨234923, by rfl⟩ : syracuseStep 1252925 = 469847) (by norm_num)
theorem B1056341 : Blo 834351 1056341 := bbase (se 8 (by rfl) ⟨6189, by rfl⟩ : syracuseStep 1056341 = 12379) (by norm_num)
theorem B1252949 : Blo 834351 1252949 := bbase (se 8 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 1252949 = 14683) (by norm_num)
theorem B892501 : Blo 834351 892501 := bbase (se 8 (by rfl) ⟨5229, by rfl⟩ : syracuseStep 892501 = 10459) (by norm_num)
theorem B1252973 : Blo 834351 1252973 := bbase (se 3 (by rfl) ⟨234932, by rfl⟩ : syracuseStep 1252973 = 469865) (by norm_num)
theorem B1252997 : Blo 834351 1252997 := bbase (se 4 (by rfl) ⟨117468, by rfl⟩ : syracuseStep 1252997 = 234937) (by norm_num)
theorem B1056397 : Blo 834351 1056397 := bbase (se 3 (by rfl) ⟨198074, by rfl⟩ : syracuseStep 1056397 = 396149) (by norm_num)
theorem B1253021 : Blo 834351 1253021 := bbase (se 3 (by rfl) ⟨234941, by rfl⟩ : syracuseStep 1253021 = 469883) (by norm_num)
theorem B1253045 : Blo 834351 1253045 := bbase (se 5 (by rfl) ⟨58736, by rfl⟩ : syracuseStep 1253045 = 117473) (by norm_num)
theorem B1253069 : Blo 834351 1253069 := bbase (se 3 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 1253069 = 469901) (by norm_num)
theorem B892621 : Blo 834351 892621 := bbase (se 3 (by rfl) ⟨167366, by rfl⟩ : syracuseStep 892621 = 334733) (by norm_num)
theorem B1253093 : Blo 834351 1253093 := bbase (se 4 (by rfl) ⟨117477, by rfl⟩ : syracuseStep 1253093 = 234955) (by norm_num)
theorem B1056493 : Blo 834351 1056493 := bbase (se 3 (by rfl) ⟨198092, by rfl⟩ : syracuseStep 1056493 = 396185) (by norm_num)
theorem B1253117 : Blo 834351 1253117 := bbase (se 3 (by rfl) ⟨234959, by rfl⟩ : syracuseStep 1253117 = 469919) (by norm_num)
theorem B1253141 : Blo 834351 1253141 := bbase (se 6 (by rfl) ⟨29370, by rfl⟩ : syracuseStep 1253141 = 58741) (by norm_num)
theorem B1253165 : Blo 834351 1253165 := bbase (se 3 (by rfl) ⟨234968, by rfl⟩ : syracuseStep 1253165 = 469937) (by norm_num)
theorem B1253189 : Blo 834351 1253189 := bbase (se 4 (by rfl) ⟨117486, by rfl⟩ : syracuseStep 1253189 = 234973) (by norm_num)
theorem B1253213 : Blo 834351 1253213 := bbase (se 3 (by rfl) ⟨234977, by rfl⟩ : syracuseStep 1253213 = 469955) (by norm_num)
theorem B1253237 : Blo 834351 1253237 := bbase (se 5 (by rfl) ⟨58745, by rfl⟩ : syracuseStep 1253237 = 117491) (by norm_num)
theorem B1253261 : Blo 834351 1253261 := bbase (se 3 (by rfl) ⟨234986, by rfl⟩ : syracuseStep 1253261 = 469973) (by norm_num)
theorem B16064405 : Blo 834351 16064405 := bbase (se 6 (by rfl) ⟨376509, by rfl⟩ : syracuseStep 16064405 = 753019) (by norm_num)
theorem B1908629 : Blo 834351 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B1056665 : Blo 834351 1056665 := bbase (se 2 (by rfl) ⟨396249, by rfl⟩ : syracuseStep 1056665 = 792499) (by norm_num)
theorem B1253285 : Blo 834351 1253285 := bbase (se 4 (by rfl) ⟨117495, by rfl⟩ : syracuseStep 1253285 = 234991) (by norm_num)
theorem B1253309 : Blo 834351 1253309 := bbase (se 3 (by rfl) ⟨234995, by rfl⟩ : syracuseStep 1253309 = 469991) (by norm_num)
theorem B892873 : Blo 834351 892873 := bbase (se 2 (by rfl) ⟨334827, by rfl⟩ : syracuseStep 892873 = 669655) (by norm_num)
theorem B892877 : Blo 834351 892877 := bbase (se 3 (by rfl) ⟨167414, by rfl⟩ : syracuseStep 892877 = 334829) (by norm_num)
theorem B1056721 : Blo 834351 1056721 := bbase (se 2 (by rfl) ⟨396270, by rfl⟩ : syracuseStep 1056721 = 792541) (by norm_num)
theorem B1253333 : Blo 834351 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B2826197 : Blo 834351 2826197 := bbase (se 7 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 2826197 = 66239) (by norm_num)
theorem B6365141 : Blo 834351 6365141 := bbase (se 7 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 6365141 = 149183) (by norm_num)
theorem B2007013 : Blo 834351 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B1253357 : Blo 834351 1253357 := bbase (se 3 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 1253357 = 470009) (by norm_num)
theorem B1253381 : Blo 834351 1253381 := bbase (se 4 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 1253381 = 235009) (by norm_num)
theorem B1253405 : Blo 834351 1253405 := bbase (se 3 (by rfl) ⟨235013, by rfl⟩ : syracuseStep 1253405 = 470027) (by norm_num)
theorem B1056817 : Blo 834351 1056817 := bbase (se 2 (by rfl) ⟨396306, by rfl⟩ : syracuseStep 1056817 = 792613) (by norm_num)
theorem B1253429 : Blo 834351 1253429 := bbase (se 5 (by rfl) ⟨58754, by rfl⟩ : syracuseStep 1253429 = 117509) (by norm_num)
theorem B1253453 : Blo 834351 1253453 := bbase (se 3 (by rfl) ⟨235022, by rfl⟩ : syracuseStep 1253453 = 470045) (by norm_num)
theorem B1253477 : Blo 834351 1253477 := bbase (se 4 (by rfl) ⟨117513, by rfl⟩ : syracuseStep 1253477 = 235027) (by norm_num)
theorem B1253501 : Blo 834351 1253501 := bbase (se 3 (by rfl) ⟨235031, by rfl⟩ : syracuseStep 1253501 = 470063) (by norm_num)
theorem B3219589 : Blo 834351 3219589 := bbase (se 4 (by rfl) ⟨301836, by rfl⟩ : syracuseStep 3219589 = 603673) (by norm_num)
theorem B1253525 : Blo 834351 1253525 := bbase (se 6 (by rfl) ⟨29379, by rfl⟩ : syracuseStep 1253525 = 58759) (by norm_num)
theorem B1253549 : Blo 834351 1253549 := bbase (se 3 (by rfl) ⟨235040, by rfl⟩ : syracuseStep 1253549 = 470081) (by norm_num)
theorem B1188037 : Blo 834351 1188037 := bbase (se 4 (by rfl) ⟨111378, by rfl⟩ : syracuseStep 1188037 = 222757) (by norm_num)
theorem B1253573 : Blo 834351 1253573 := bbase (se 4 (by rfl) ⟨117522, by rfl⟩ : syracuseStep 1253573 = 235045) (by norm_num)
theorem B1056989 : Blo 834351 1056989 := bbase (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) (by norm_num)
theorem B1253597 : Blo 834351 1253597 := bbase (se 3 (by rfl) ⟨235049, by rfl⟩ : syracuseStep 1253597 = 470099) (by norm_num)
theorem B1253621 : Blo 834351 1253621 := bbase (se 5 (by rfl) ⟨58763, by rfl⟩ : syracuseStep 1253621 = 117527) (by norm_num)
theorem B1253645 : Blo 834351 1253645 := bbase (se 3 (by rfl) ⟨235058, by rfl⟩ : syracuseStep 1253645 = 470117) (by norm_num)
theorem B1057045 : Blo 834351 1057045 := bbase (se 6 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 1057045 = 49549) (by norm_num)
theorem B1253669 : Blo 834351 1253669 := bbase (se 4 (by rfl) ⟨117531, by rfl⟩ : syracuseStep 1253669 = 235063) (by norm_num)
theorem B1253693 : Blo 834351 1253693 := bbase (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) (by norm_num)
theorem B1253717 : Blo 834351 1253717 := bbase (se 10 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 1253717 = 3673) (by norm_num)
theorem B860513 : Blo 834351 860513 := bbase (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) (by norm_num)
theorem B1253741 : Blo 834351 1253741 := bbase (se 3 (by rfl) ⟨235076, by rfl⟩ : syracuseStep 1253741 = 470153) (by norm_num)
theorem B1057141 : Blo 834351 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B1253765 : Blo 834351 1253765 := bbase (se 4 (by rfl) ⟨117540, by rfl⟩ : syracuseStep 1253765 = 235081) (by norm_num)
theorem B2826629 : Blo 834351 2826629 := bbase (se 4 (by rfl) ⟨264996, by rfl⟩ : syracuseStep 2826629 = 529993) (by norm_num)
theorem B1253789 : Blo 834351 1253789 := bbase (se 3 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 1253789 = 470171) (by norm_num)
theorem B3580325 : Blo 834351 3580325 := bbase (se 4 (by rfl) ⟨335655, by rfl⟩ : syracuseStep 3580325 = 671311) (by norm_num)
theorem B1253813 : Blo 834351 1253813 := bbase (se 5 (by rfl) ⟨58772, by rfl⟩ : syracuseStep 1253813 = 117545) (by norm_num)
theorem B1253837 : Blo 834351 1253837 := bbase (se 3 (by rfl) ⟨235094, by rfl⟩ : syracuseStep 1253837 = 470189) (by norm_num)
theorem B1253861 : Blo 834351 1253861 := bbase (se 4 (by rfl) ⟨117549, by rfl⟩ : syracuseStep 1253861 = 235099) (by norm_num)
theorem B1253885 : Blo 834351 1253885 := bbase (se 3 (by rfl) ⟨235103, by rfl⟩ : syracuseStep 1253885 = 470207) (by norm_num)
theorem B893441 : Blo 834351 893441 := bbase (se 2 (by rfl) ⟨335040, by rfl⟩ : syracuseStep 893441 = 670081) (by norm_num)
theorem B1188373 : Blo 834351 1188373 := bbase (se 6 (by rfl) ⟨27852, by rfl⟩ : syracuseStep 1188373 = 55705) (by norm_num)
theorem B1253909 : Blo 834351 1253909 := bbase (se 6 (by rfl) ⟨29388, by rfl⟩ : syracuseStep 1253909 = 58777) (by norm_num)
theorem B1057313 : Blo 834351 1057313 := bbase (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) (by norm_num)
theorem B4235813 : Blo 834351 4235813 := bbase (se 4 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 4235813 = 794215) (by norm_num)
theorem B1253933 : Blo 834351 1253933 := bbase (se 3 (by rfl) ⟨235112, by rfl⟩ : syracuseStep 1253933 = 470225) (by norm_num)
theorem B1253957 : Blo 834351 1253957 := bbase (se 4 (by rfl) ⟨117558, by rfl⟩ : syracuseStep 1253957 = 235117) (by norm_num)
theorem B2007629 : Blo 834351 2007629 := bbase (se 3 (by rfl) ⟨376430, by rfl⟩ : syracuseStep 2007629 = 752861) (by norm_num)
theorem B1057369 : Blo 834351 1057369 := bbase (se 2 (by rfl) ⟨396513, by rfl⟩ : syracuseStep 1057369 = 793027) (by norm_num)
theorem B1253981 : Blo 834351 1253981 := bbase (se 3 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 1253981 = 470243) (by norm_num)
theorem B1254005 : Blo 834351 1254005 := bbase (se 5 (by rfl) ⟨58781, by rfl⟩ : syracuseStep 1254005 = 117563) (by norm_num)
theorem B1254029 : Blo 834351 1254029 := bbase (se 3 (by rfl) ⟨235130, by rfl⟩ : syracuseStep 1254029 = 470261) (by norm_num)
theorem B1254053 : Blo 834351 1254053 := bbase (se 4 (by rfl) ⟨117567, by rfl⟩ : syracuseStep 1254053 = 235135) (by norm_num)
theorem B1057465 : Blo 834351 1057465 := bbase (se 2 (by rfl) ⟨396549, by rfl⟩ : syracuseStep 1057465 = 793099) (by norm_num)
theorem B1254077 : Blo 834351 1254077 := bbase (se 3 (by rfl) ⟨235139, by rfl⟩ : syracuseStep 1254077 = 470279) (by norm_num)
theorem B893629 : Blo 834351 893629 := bbase (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) (by norm_num)
theorem B1254101 : Blo 834351 1254101 := bbase (se 7 (by rfl) ⟨14696, by rfl⟩ : syracuseStep 1254101 = 29393) (by norm_num)
theorem B1188589 : Blo 834351 1188589 := bbase (se 3 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 1188589 = 445721) (by norm_num)
theorem B1254125 : Blo 834351 1254125 := bbase (se 3 (by rfl) ⟨235148, by rfl⟩ : syracuseStep 1254125 = 470297) (by norm_num)
theorem B1254149 : Blo 834351 1254149 := bbase (se 4 (by rfl) ⟨117576, by rfl⟩ : syracuseStep 1254149 = 235153) (by norm_num)
theorem B2007821 : Blo 834351 2007821 := bbase (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) (by norm_num)
theorem B1254173 : Blo 834351 1254173 := bbase (se 3 (by rfl) ⟨235157, by rfl⟩ : syracuseStep 1254173 = 470315) (by norm_num)
theorem B1254197 : Blo 834351 1254197 := bbase (se 5 (by rfl) ⟨58790, by rfl⟩ : syracuseStep 1254197 = 117581) (by norm_num)
theorem B2827061 : Blo 834351 2827061 := bbase (se 5 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 2827061 = 265037) (by norm_num)
theorem B1254221 : Blo 834351 1254221 := bbase (se 3 (by rfl) ⟨235166, by rfl⟩ : syracuseStep 1254221 = 470333) (by norm_num)
theorem B1057637 : Blo 834351 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B1254245 : Blo 834351 1254245 := bbase (se 4 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 1254245 = 235171) (by norm_num)
theorem B2007917 : Blo 834351 2007917 := bbase (se 3 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 2007917 = 752969) (by norm_num)
theorem B1254269 : Blo 834351 1254269 := bbase (se 3 (by rfl) ⟨235175, by rfl⟩ : syracuseStep 1254269 = 470351) (by norm_num)
theorem B1254293 : Blo 834351 1254293 := bbase (se 6 (by rfl) ⟨29397, by rfl⟩ : syracuseStep 1254293 = 58795) (by norm_num)
theorem B1057693 : Blo 834351 1057693 := bbase (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) (by norm_num)
theorem B1254317 : Blo 834351 1254317 := bbase (se 3 (by rfl) ⟨235184, by rfl⟩ : syracuseStep 1254317 = 470369) (by norm_num)
theorem B1254341 : Blo 834351 1254341 := bbase (se 4 (by rfl) ⟨117594, by rfl⟩ : syracuseStep 1254341 = 235189) (by norm_num)
theorem B1254365 : Blo 834351 1254365 := bbase (se 3 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 1254365 = 470387) (by norm_num)
theorem B1254389 : Blo 834351 1254389 := bbase (se 5 (by rfl) ⟨58799, by rfl⟩ : syracuseStep 1254389 = 117599) (by norm_num)
theorem B1057789 : Blo 834351 1057789 := bbase (se 3 (by rfl) ⟨198335, by rfl⟩ : syracuseStep 1057789 = 396671) (by norm_num)
theorem B1254413 : Blo 834351 1254413 := bbase (se 3 (by rfl) ⟨235202, by rfl⟩ : syracuseStep 1254413 = 470405) (by norm_num)
theorem B1254437 : Blo 834351 1254437 := bbase (se 4 (by rfl) ⟨117603, by rfl⟩ : syracuseStep 1254437 = 235207) (by norm_num)
theorem B1254461 : Blo 834351 1254461 := bbase (se 3 (by rfl) ⟨235211, by rfl⟩ : syracuseStep 1254461 = 470423) (by norm_num)
theorem B1254485 : Blo 834351 1254485 := bbase (se 8 (by rfl) ⟨7350, by rfl⟩ : syracuseStep 1254485 = 14701) (by norm_num)
theorem B1188965 : Blo 834351 1188965 := bbase (se 4 (by rfl) ⟨111465, by rfl⟩ : syracuseStep 1188965 = 222931) (by norm_num)
theorem B1254509 : Blo 834351 1254509 := bbase (se 3 (by rfl) ⟨235220, by rfl⟩ : syracuseStep 1254509 = 470441) (by norm_num)
theorem B1254533 : Blo 834351 1254533 := bbase (se 4 (by rfl) ⟨117612, by rfl⟩ : syracuseStep 1254533 = 235225) (by norm_num)
theorem B1254557 : Blo 834351 1254557 := bbase (se 3 (by rfl) ⟨235229, by rfl⟩ : syracuseStep 1254557 = 470459) (by norm_num)
theorem B1057961 : Blo 834351 1057961 := bbase (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) (by norm_num)
theorem B1254581 : Blo 834351 1254581 := bbase (se 5 (by rfl) ⟨58808, by rfl⟩ : syracuseStep 1254581 = 117617) (by norm_num)
theorem B1254605 : Blo 834351 1254605 := bbase (se 3 (by rfl) ⟨235238, by rfl⟩ : syracuseStep 1254605 = 470477) (by norm_num)
theorem B1058017 : Blo 834351 1058017 := bbase (se 2 (by rfl) ⟨396756, by rfl⟩ : syracuseStep 1058017 = 793513) (by norm_num)
theorem B1254629 : Blo 834351 1254629 := bbase (se 4 (by rfl) ⟨117621, by rfl⟩ : syracuseStep 1254629 = 235243) (by norm_num)
theorem B2827493 : Blo 834351 2827493 := bbase (se 4 (by rfl) ⟨265077, by rfl⟩ : syracuseStep 2827493 = 530155) (by norm_num)
theorem B1254653 : Blo 834351 1254653 := bbase (se 3 (by rfl) ⟨235247, by rfl⟩ : syracuseStep 1254653 = 470495) (by norm_num)
theorem B1254677 : Blo 834351 1254677 := bbase (se 6 (by rfl) ⟨29406, by rfl⟩ : syracuseStep 1254677 = 58813) (by norm_num)
theorem B1254701 : Blo 834351 1254701 := bbase (se 3 (by rfl) ⟨235256, by rfl⟩ : syracuseStep 1254701 = 470513) (by norm_num)
theorem B1877309 : Blo 834351 1877309 := bbase (se 3 (by rfl) ⟨351995, by rfl⟩ : syracuseStep 1877309 = 703991) (by norm_num)
theorem B1058113 : Blo 834351 1058113 := bbase (se 2 (by rfl) ⟨396792, by rfl⟩ : syracuseStep 1058113 = 793585) (by norm_num)
theorem B1254725 : Blo 834351 1254725 := bbase (se 4 (by rfl) ⟨117630, by rfl⟩ : syracuseStep 1254725 = 235261) (by norm_num)
theorem B1254749 : Blo 834351 1254749 := bbase (se 3 (by rfl) ⟨235265, by rfl⟩ : syracuseStep 1254749 = 470531) (by norm_num)
theorem B1254773 : Blo 834351 1254773 := bbase (se 5 (by rfl) ⟨58817, by rfl⟩ : syracuseStep 1254773 = 117635) (by norm_num)
theorem B1877381 : Blo 834351 1877381 := bbase (se 4 (by rfl) ⟨176004, by rfl⟩ : syracuseStep 1877381 = 352009) (by norm_num)
theorem B1254797 : Blo 834351 1254797 := bbase (se 3 (by rfl) ⟨235274, by rfl⟩ : syracuseStep 1254797 = 470549) (by norm_num)
theorem B5350805 : Blo 834351 5350805 := bbase (se 6 (by rfl) ⟨125409, by rfl⟩ : syracuseStep 5350805 = 250819) (by norm_num)
theorem B10855829 : Blo 834351 10855829 := bbase (se 6 (by rfl) ⟨254433, by rfl⟩ : syracuseStep 10855829 = 508867) (by norm_num)
theorem B1254821 : Blo 834351 1254821 := bbase (se 4 (by rfl) ⟨117639, by rfl⟩ : syracuseStep 1254821 = 235279) (by norm_num)
theorem B1254845 : Blo 834351 1254845 := bbase (se 3 (by rfl) ⟨235283, by rfl⟩ : syracuseStep 1254845 = 470567) (by norm_num)
theorem B1877453 : Blo 834351 1877453 := bbase (se 3 (by rfl) ⟨352022, by rfl⟩ : syracuseStep 1877453 = 704045) (by norm_num)
theorem B1254869 : Blo 834351 1254869 := bbase (se 7 (by rfl) ⟨14705, by rfl⟩ : syracuseStep 1254869 = 29411) (by norm_num)
theorem B1058285 : Blo 834351 1058285 := bbase (se 3 (by rfl) ⟨198428, by rfl⟩ : syracuseStep 1058285 = 396857) (by norm_num)
theorem B1254893 : Blo 834351 1254893 := bbase (se 3 (by rfl) ⟨235292, by rfl⟩ : syracuseStep 1254893 = 470585) (by norm_num)
theorem B894449 : Blo 834351 894449 := bbase (se 2 (by rfl) ⟨335418, by rfl⟩ : syracuseStep 894449 = 670837) (by norm_num)
theorem B1254917 : Blo 834351 1254917 := bbase (se 4 (by rfl) ⟨117648, by rfl⟩ : syracuseStep 1254917 = 235297) (by norm_num)
theorem B1877525 : Blo 834351 1877525 := bbase (se 6 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 1877525 = 88009) (by norm_num)
theorem B1254941 : Blo 834351 1254941 := bbase (se 3 (by rfl) ⟨235301, by rfl⟩ : syracuseStep 1254941 = 470603) (by norm_num)
theorem B1058341 : Blo 834351 1058341 := bbase (se 4 (by rfl) ⟨99219, by rfl⟩ : syracuseStep 1058341 = 198439) (by norm_num)
theorem B1254965 : Blo 834351 1254965 := bbase (se 5 (by rfl) ⟨58826, by rfl⟩ : syracuseStep 1254965 = 117653) (by norm_num)
theorem B1254989 : Blo 834351 1254989 := bbase (se 3 (by rfl) ⟨235310, by rfl⟩ : syracuseStep 1254989 = 470621) (by norm_num)
theorem B1877597 : Blo 834351 1877597 := bbase (se 3 (by rfl) ⟨352049, by rfl⟩ : syracuseStep 1877597 = 704099) (by norm_num)
theorem B1255013 : Blo 834351 1255013 := bbase (se 4 (by rfl) ⟨117657, by rfl⟩ : syracuseStep 1255013 = 235315) (by norm_num)
theorem B1255037 : Blo 834351 1255037 := bbase (se 3 (by rfl) ⟨235319, by rfl⟩ : syracuseStep 1255037 = 470639) (by norm_num)
theorem B1058437 : Blo 834351 1058437 := bbase (se 4 (by rfl) ⟨99228, by rfl⟩ : syracuseStep 1058437 = 198457) (by norm_num)
theorem B1255061 : Blo 834351 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B2827925 : Blo 834351 2827925 := bbase (se 6 (by rfl) ⟨66279, by rfl⟩ : syracuseStep 2827925 = 132559) (by norm_num)
theorem B1877669 : Blo 834351 1877669 := bbase (se 4 (by rfl) ⟨176031, by rfl⟩ : syracuseStep 1877669 = 352063) (by norm_num)
theorem B1255085 : Blo 834351 1255085 := bbase (se 3 (by rfl) ⟨235328, by rfl⟩ : syracuseStep 1255085 = 470657) (by norm_num)
theorem B1255109 : Blo 834351 1255109 := bbase (se 4 (by rfl) ⟨117666, by rfl⟩ : syracuseStep 1255109 = 235333) (by norm_num)
theorem B1255133 : Blo 834351 1255133 := bbase (se 3 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 1255133 = 470675) (by norm_num)
theorem B1877741 : Blo 834351 1877741 := bbase (se 3 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 1877741 = 704153) (by norm_num)
theorem B1255157 : Blo 834351 1255157 := bbase (se 5 (by rfl) ⟨58835, by rfl⟩ : syracuseStep 1255157 = 117671) (by norm_num)
theorem B1910533 : Blo 834351 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B1255181 : Blo 834351 1255181 := bbase (se 3 (by rfl) ⟨235346, by rfl⟩ : syracuseStep 1255181 = 470693) (by norm_num)
theorem B1255205 : Blo 834351 1255205 := bbase (se 4 (by rfl) ⟨117675, by rfl⟩ : syracuseStep 1255205 = 235351) (by norm_num)
theorem B1058609 : Blo 834351 1058609 := bbase (se 2 (by rfl) ⟨396978, by rfl⟩ : syracuseStep 1058609 = 793957) (by norm_num)
theorem B1877813 : Blo 834351 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B4237109 : Blo 834351 4237109 := bbase (se 5 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 4237109 = 397229) (by norm_num)
theorem B1255229 : Blo 834351 1255229 := bbase (se 3 (by rfl) ⟨235355, by rfl⟩ : syracuseStep 1255229 = 470711) (by norm_num)
theorem B1255253 : Blo 834351 1255253 := bbase (se 9 (by rfl) ⟨3677, by rfl⟩ : syracuseStep 1255253 = 7355) (by norm_num)
theorem B1058665 : Blo 834351 1058665 := bbase (se 2 (by rfl) ⟨396999, by rfl⟩ : syracuseStep 1058665 = 793999) (by norm_num)
theorem B1255277 : Blo 834351 1255277 := bbase (se 3 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 1255277 = 470729) (by norm_num)
theorem B1877885 : Blo 834351 1877885 := bbase (se 3 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 1877885 = 704207) (by norm_num)
theorem B1255301 : Blo 834351 1255301 := bbase (se 4 (by rfl) ⟨117684, by rfl⟩ : syracuseStep 1255301 = 235369) (by norm_num)
theorem B1255325 : Blo 834351 1255325 := bbase (se 3 (by rfl) ⟨235373, by rfl⟩ : syracuseStep 1255325 = 470747) (by norm_num)
theorem B894893 : Blo 834351 894893 := bbase (se 3 (by rfl) ⟨167792, by rfl⟩ : syracuseStep 894893 = 335585) (by norm_num)
theorem B1255349 : Blo 834351 1255349 := bbase (se 5 (by rfl) ⟨58844, by rfl⟩ : syracuseStep 1255349 = 117689) (by norm_num)
theorem B1877957 : Blo 834351 1877957 := bbase (se 4 (by rfl) ⟨176058, by rfl⟩ : syracuseStep 1877957 = 352117) (by norm_num)
theorem B1058761 : Blo 834351 1058761 := bbase (se 2 (by rfl) ⟨397035, by rfl⟩ : syracuseStep 1058761 = 794071) (by norm_num)
theorem B1255373 : Blo 834351 1255373 := bbase (se 3 (by rfl) ⟨235382, by rfl⟩ : syracuseStep 1255373 = 470765) (by norm_num)
theorem B1255397 : Blo 834351 1255397 := bbase (se 4 (by rfl) ⟨117693, by rfl⟩ : syracuseStep 1255397 = 235387) (by norm_num)
theorem B1255421 : Blo 834351 1255421 := bbase (se 3 (by rfl) ⟨235391, by rfl⟩ : syracuseStep 1255421 = 470783) (by norm_num)
theorem B1878029 : Blo 834351 1878029 := bbase (se 3 (by rfl) ⟨352130, by rfl⟩ : syracuseStep 1878029 = 704261) (by norm_num)
theorem B1255445 : Blo 834351 1255445 := bbase (se 6 (by rfl) ⟨29424, by rfl⟩ : syracuseStep 1255445 = 58849) (by norm_num)
theorem B1255469 : Blo 834351 1255469 := bbase (se 3 (by rfl) ⟨235400, by rfl⟩ : syracuseStep 1255469 = 470801) (by norm_num)
theorem B1255493 : Blo 834351 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B2828357 : Blo 834351 2828357 := bbase (se 4 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 2828357 = 530317) (by norm_num)
theorem B1878101 : Blo 834351 1878101 := bbase (se 8 (by rfl) ⟨11004, by rfl⟩ : syracuseStep 1878101 = 22009) (by norm_num)
theorem B1255517 : Blo 834351 1255517 := bbase (se 3 (by rfl) ⟨235409, by rfl⟩ : syracuseStep 1255517 = 470819) (by norm_num)
theorem B7940213 : Blo 834351 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B1058933 : Blo 834351 1058933 := bbase (se 5 (by rfl) ⟨49637, by rfl⟩ : syracuseStep 1058933 = 99275) (by norm_num)
theorem B1255541 : Blo 834351 1255541 := bbase (se 5 (by rfl) ⟨58853, by rfl⟩ : syracuseStep 1255541 = 117707) (by norm_num)
theorem B1255565 : Blo 834351 1255565 := bbase (se 3 (by rfl) ⟨235418, by rfl⟩ : syracuseStep 1255565 = 470837) (by norm_num)
theorem B1910933 : Blo 834351 1910933 := bbase (se 6 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 1910933 = 89575) (by norm_num)
theorem B1878173 : Blo 834351 1878173 := bbase (se 3 (by rfl) ⟨352157, by rfl⟩ : syracuseStep 1878173 = 704315) (by norm_num)
theorem B1255589 : Blo 834351 1255589 := bbase (se 4 (by rfl) ⟨117711, by rfl⟩ : syracuseStep 1255589 = 235423) (by norm_num)
theorem B895141 : Blo 834351 895141 := bbase (se 4 (by rfl) ⟨83919, by rfl⟩ : syracuseStep 895141 = 167839) (by norm_num)
theorem B1058989 : Blo 834351 1058989 := bbase (se 3 (by rfl) ⟨198560, by rfl⟩ : syracuseStep 1058989 = 397121) (by norm_num)
theorem B1255613 : Blo 834351 1255613 := bbase (se 3 (by rfl) ⟨235427, by rfl⟩ : syracuseStep 1255613 = 470855) (by norm_num)
theorem B1255637 : Blo 834351 1255637 := bbase (se 7 (by rfl) ⟨14714, by rfl⟩ : syracuseStep 1255637 = 29429) (by norm_num)
theorem B1878245 : Blo 834351 1878245 := bbase (se 4 (by rfl) ⟨176085, by rfl⟩ : syracuseStep 1878245 = 352171) (by norm_num)
theorem B1255661 : Blo 834351 1255661 := bbase (se 3 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 1255661 = 470873) (by norm_num)
theorem B1255685 : Blo 834351 1255685 := bbase (se 4 (by rfl) ⟨117720, by rfl⟩ : syracuseStep 1255685 = 235441) (by norm_num)
theorem B1059085 : Blo 834351 1059085 := bbase (se 3 (by rfl) ⟨198578, by rfl⟩ : syracuseStep 1059085 = 397157) (by norm_num)
theorem B1255709 : Blo 834351 1255709 := bbase (se 3 (by rfl) ⟨235445, by rfl⟩ : syracuseStep 1255709 = 470891) (by norm_num)
theorem B1878317 : Blo 834351 1878317 := bbase (se 3 (by rfl) ⟨352184, by rfl⟩ : syracuseStep 1878317 = 704369) (by norm_num)
theorem B1255733 : Blo 834351 1255733 := bbase (se 5 (by rfl) ⟨58862, by rfl⟩ : syracuseStep 1255733 = 117725) (by norm_num)
theorem B1255757 : Blo 834351 1255757 := bbase (se 3 (by rfl) ⟨235454, by rfl⟩ : syracuseStep 1255757 = 470909) (by norm_num)
theorem B1255781 : Blo 834351 1255781 := bbase (se 4 (by rfl) ⟨117729, by rfl⟩ : syracuseStep 1255781 = 235459) (by norm_num)
theorem B1878389 : Blo 834351 1878389 := bbase (se 5 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 1878389 = 176099) (by norm_num)
theorem B1255805 : Blo 834351 1255805 := bbase (se 3 (by rfl) ⟨235463, by rfl⟩ : syracuseStep 1255805 = 470927) (by norm_num)
theorem B1255829 : Blo 834351 1255829 := bbase (se 6 (by rfl) ⟨29433, by rfl⟩ : syracuseStep 1255829 = 58867) (by norm_num)
theorem B1255853 : Blo 834351 1255853 := bbase (se 3 (by rfl) ⟨235472, by rfl⟩ : syracuseStep 1255853 = 470945) (by norm_num)
theorem B1059257 : Blo 834351 1059257 := bbase (se 2 (by rfl) ⟨397221, by rfl⟩ : syracuseStep 1059257 = 794443) (by norm_num)
theorem B1878461 : Blo 834351 1878461 := bbase (se 3 (by rfl) ⟨352211, by rfl⟩ : syracuseStep 1878461 = 704423) (by norm_num)
theorem B1255877 : Blo 834351 1255877 := bbase (se 4 (by rfl) ⟨117738, by rfl⟩ : syracuseStep 1255877 = 235477) (by norm_num)
theorem B1255901 : Blo 834351 1255901 := bbase (se 3 (by rfl) ⟨235481, by rfl⟩ : syracuseStep 1255901 = 470963) (by norm_num)
theorem B1059313 : Blo 834351 1059313 := bbase (se 2 (by rfl) ⟨397242, by rfl⟩ : syracuseStep 1059313 = 794485) (by norm_num)
theorem B1190389 : Blo 834351 1190389 := bbase (se 5 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 1190389 = 111599) (by norm_num)
theorem B1255925 : Blo 834351 1255925 := bbase (se 5 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 1255925 = 117743) (by norm_num)
theorem B2828789 : Blo 834351 2828789 := bbase (se 5 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 2828789 = 265199) (by norm_num)
theorem B2206205 : Blo 834351 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B1878533 : Blo 834351 1878533 := bbase (se 4 (by rfl) ⟨176112, by rfl⟩ : syracuseStep 1878533 = 352225) (by norm_num)
theorem B1255949 : Blo 834351 1255949 := bbase (se 3 (by rfl) ⟨235490, by rfl⟩ : syracuseStep 1255949 = 470981) (by norm_num)
theorem B1255973 : Blo 834351 1255973 := bbase (se 4 (by rfl) ⟨117747, by rfl⟩ : syracuseStep 1255973 = 235495) (by norm_num)
theorem B1255997 : Blo 834351 1255997 := bbase (se 3 (by rfl) ⟨235499, by rfl⟩ : syracuseStep 1255997 = 470999) (by norm_num)
theorem B1878605 : Blo 834351 1878605 := bbase (se 3 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 1878605 = 704477) (by norm_num)
theorem B1059409 : Blo 834351 1059409 := bbase (se 2 (by rfl) ⟨397278, by rfl⟩ : syracuseStep 1059409 = 794557) (by norm_num)
theorem B1256021 : Blo 834351 1256021 := bbase (se 8 (by rfl) ⟨7359, by rfl⟩ : syracuseStep 1256021 = 14719) (by norm_num)
theorem B1256045 : Blo 834351 1256045 := bbase (se 3 (by rfl) ⟨235508, by rfl⟩ : syracuseStep 1256045 = 471017) (by norm_num)
theorem B1256069 : Blo 834351 1256069 := bbase (se 4 (by rfl) ⟨117756, by rfl⟩ : syracuseStep 1256069 = 235513) (by norm_num)
theorem B1878677 : Blo 834351 1878677 := bbase (se 6 (by rfl) ⟨44031, by rfl⟩ : syracuseStep 1878677 = 88063) (by norm_num)
theorem B1256093 : Blo 834351 1256093 := bbase (se 3 (by rfl) ⟨235517, by rfl⟩ : syracuseStep 1256093 = 471035) (by norm_num)
theorem B1256117 : Blo 834351 1256117 := bbase (se 5 (by rfl) ⟨58880, by rfl⟩ : syracuseStep 1256117 = 117761) (by norm_num)
theorem B1256141 : Blo 834351 1256141 := bbase (se 3 (by rfl) ⟨235526, by rfl⟩ : syracuseStep 1256141 = 471053) (by norm_num)
theorem B1878749 : Blo 834351 1878749 := bbase (se 3 (by rfl) ⟨352265, by rfl⟩ : syracuseStep 1878749 = 704531) (by norm_num)
theorem B1256165 : Blo 834351 1256165 := bbase (se 4 (by rfl) ⟨117765, by rfl⟩ : syracuseStep 1256165 = 235531) (by norm_num)
theorem B1059581 : Blo 834351 1059581 := bbase (se 3 (by rfl) ⟨198671, by rfl⟩ : syracuseStep 1059581 = 397343) (by norm_num)
theorem B1256189 : Blo 834351 1256189 := bbase (se 3 (by rfl) ⟨235535, by rfl⟩ : syracuseStep 1256189 = 471071) (by norm_num)
theorem B1256213 : Blo 834351 1256213 := bbase (se 6 (by rfl) ⟨29442, by rfl⟩ : syracuseStep 1256213 = 58885) (by norm_num)
theorem B1878821 : Blo 834351 1878821 := bbase (se 4 (by rfl) ⟨176139, by rfl⟩ : syracuseStep 1878821 = 352279) (by norm_num)
theorem B1256237 : Blo 834351 1256237 := bbase (se 3 (by rfl) ⟨235544, by rfl⟩ : syracuseStep 1256237 = 471089) (by norm_num)
theorem B4762421 : Blo 834351 4762421 := bbase (se 5 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 4762421 = 446477) (by norm_num)
theorem B1059637 : Blo 834351 1059637 := bbase (se 5 (by rfl) ⟨49670, by rfl⟩ : syracuseStep 1059637 = 99341) (by norm_num)
theorem B1256261 : Blo 834351 1256261 := bbase (se 4 (by rfl) ⟨117774, by rfl⟩ : syracuseStep 1256261 = 235549) (by norm_num)
theorem B1583965 : Blo 834351 1583965 := bbase (se 3 (by rfl) ⟨296993, by rfl⟩ : syracuseStep 1583965 = 593987) (by norm_num)
theorem B1256285 : Blo 834351 1256285 := bbase (se 3 (by rfl) ⟨235553, by rfl⟩ : syracuseStep 1256285 = 471107) (by norm_num)
theorem B1878893 : Blo 834351 1878893 := bbase (se 3 (by rfl) ⟨352292, by rfl⟩ : syracuseStep 1878893 = 704585) (by norm_num)
theorem B1256309 : Blo 834351 1256309 := bbase (se 5 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 1256309 = 117779) (by norm_num)
theorem B1256333 : Blo 834351 1256333 := bbase (se 3 (by rfl) ⟨235562, by rfl⟩ : syracuseStep 1256333 = 471125) (by norm_num)
theorem B1059733 : Blo 834351 1059733 := bbase (se 6 (by rfl) ⟨24837, by rfl⟩ : syracuseStep 1059733 = 49675) (by norm_num)
theorem B1256357 : Blo 834351 1256357 := bbase (se 4 (by rfl) ⟨117783, by rfl⟩ : syracuseStep 1256357 = 235567) (by norm_num)
theorem B2829221 : Blo 834351 2829221 := bbase (se 4 (by rfl) ⟨265239, by rfl⟩ : syracuseStep 2829221 = 530479) (by norm_num)
theorem B1878965 : Blo 834351 1878965 := bbase (se 5 (by rfl) ⟨88076, by rfl⟩ : syracuseStep 1878965 = 176153) (by norm_num)
theorem B1256381 : Blo 834351 1256381 := bbase (se 3 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 1256381 = 471143) (by norm_num)
theorem B1256405 : Blo 834351 1256405 := bbase (se 7 (by rfl) ⟨14723, by rfl⟩ : syracuseStep 1256405 = 29447) (by norm_num)
theorem B1354733 : Blo 834351 1354733 := bbase (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) (by norm_num)
theorem B1256429 : Blo 834351 1256429 := bbase (se 3 (by rfl) ⟨235580, by rfl⟩ : syracuseStep 1256429 = 471161) (by norm_num)
theorem B1879037 : Blo 834351 1879037 := bbase (se 3 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 1879037 = 704639) (by norm_num)
theorem B1256453 : Blo 834351 1256453 := bbase (se 4 (by rfl) ⟨117792, by rfl⟩ : syracuseStep 1256453 = 235585) (by norm_num)
theorem B1256477 : Blo 834351 1256477 := bbase (se 3 (by rfl) ⟨235589, by rfl⟩ : syracuseStep 1256477 = 471179) (by norm_num)
theorem B1256501 : Blo 834351 1256501 := bbase (se 5 (by rfl) ⟨58898, by rfl⟩ : syracuseStep 1256501 = 117797) (by norm_num)
theorem B1059905 : Blo 834351 1059905 := bbase (se 2 (by rfl) ⟨397464, by rfl⟩ : syracuseStep 1059905 = 794929) (by norm_num)
theorem B1879109 : Blo 834351 1879109 := bbase (se 4 (by rfl) ⟨176166, by rfl⟩ : syracuseStep 1879109 = 352333) (by norm_num)
theorem B1190981 : Blo 834351 1190981 := bbase (se 4 (by rfl) ⟨111654, by rfl⟩ : syracuseStep 1190981 = 223309) (by norm_num)
theorem B4238405 : Blo 834351 4238405 := bbase (se 4 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 4238405 = 794701) (by norm_num)
theorem B1256525 : Blo 834351 1256525 := bbase (se 3 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 1256525 = 471197) (by norm_num)
theorem B1256549 : Blo 834351 1256549 := bbase (se 4 (by rfl) ⟨117801, by rfl⟩ : syracuseStep 1256549 = 235603) (by norm_num)
theorem B1059961 : Blo 834351 1059961 := bbase (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) (by norm_num)
theorem B1256573 : Blo 834351 1256573 := bbase (se 3 (by rfl) ⟨235607, by rfl⟩ : syracuseStep 1256573 = 471215) (by norm_num)
theorem B1584269 : Blo 834351 1584269 := bbase (se 3 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 1584269 = 594101) (by norm_num)
theorem B1879181 : Blo 834351 1879181 := bbase (se 3 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 1879181 = 704693) (by norm_num)
theorem B1191061 : Blo 834351 1191061 := bbase (se 6 (by rfl) ⟨27915, by rfl⟩ : syracuseStep 1191061 = 55831) (by norm_num)
theorem B1256597 : Blo 834351 1256597 := bbase (se 6 (by rfl) ⟨29451, by rfl⟩ : syracuseStep 1256597 = 58903) (by norm_num)
theorem B1256621 : Blo 834351 1256621 := bbase (se 3 (by rfl) ⟨235616, by rfl⟩ : syracuseStep 1256621 = 471233) (by norm_num)
theorem B1256645 : Blo 834351 1256645 := bbase (se 4 (by rfl) ⟨117810, by rfl⟩ : syracuseStep 1256645 = 235621) (by norm_num)
theorem B1879253 : Blo 834351 1879253 := bbase (se 7 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 1879253 = 44045) (by norm_num)
theorem B1060057 : Blo 834351 1060057 := bbase (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) (by norm_num)
theorem B1256669 : Blo 834351 1256669 := bbase (se 3 (by rfl) ⟨235625, by rfl⟩ : syracuseStep 1256669 = 471251) (by norm_num)
theorem B2010349 : Blo 834351 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B1256693 : Blo 834351 1256693 := bbase (se 5 (by rfl) ⟨58907, by rfl⟩ : syracuseStep 1256693 = 117815) (by norm_num)
theorem B1191181 : Blo 834351 1191181 := bbase (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) (by norm_num)
theorem B1256717 : Blo 834351 1256717 := bbase (se 3 (by rfl) ⟨235634, by rfl⟩ : syracuseStep 1256717 = 471269) (by norm_num)
theorem B1879325 : Blo 834351 1879325 := bbase (se 3 (by rfl) ⟨352373, by rfl⟩ : syracuseStep 1879325 = 704747) (by norm_num)
theorem B1256741 : Blo 834351 1256741 := bbase (se 4 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 1256741 = 235639) (by norm_num)
theorem B1256765 : Blo 834351 1256765 := bbase (se 3 (by rfl) ⟨235643, by rfl⟩ : syracuseStep 1256765 = 471287) (by norm_num)
theorem B1256789 : Blo 834351 1256789 := bbase (se 11 (by rfl) ⟨920, by rfl⟩ : syracuseStep 1256789 = 1841) (by norm_num)
theorem B1879397 : Blo 834351 1879397 := bbase (se 4 (by rfl) ⟨176193, by rfl⟩ : syracuseStep 1879397 = 352387) (by norm_num)
theorem B1191277 : Blo 834351 1191277 := bbase (se 3 (by rfl) ⟨223364, by rfl⟩ : syracuseStep 1191277 = 446729) (by norm_num)
theorem B1256813 : Blo 834351 1256813 := bbase (se 3 (by rfl) ⟨235652, by rfl⟩ : syracuseStep 1256813 = 471305) (by norm_num)
theorem B1060229 : Blo 834351 1060229 := bbase (se 4 (by rfl) ⟨99396, by rfl⟩ : syracuseStep 1060229 = 198793) (by norm_num)
theorem B1256837 : Blo 834351 1256837 := bbase (se 4 (by rfl) ⟨117828, by rfl⟩ : syracuseStep 1256837 = 235657) (by norm_num)
theorem B1256861 : Blo 834351 1256861 := bbase (se 3 (by rfl) ⟨235661, by rfl⟩ : syracuseStep 1256861 = 471323) (by norm_num)
theorem B1879469 : Blo 834351 1879469 := bbase (se 3 (by rfl) ⟨352400, by rfl⟩ : syracuseStep 1879469 = 704801) (by norm_num)
theorem B1256885 : Blo 834351 1256885 := bbase (se 5 (by rfl) ⟨58916, by rfl⟩ : syracuseStep 1256885 = 117833) (by norm_num)
theorem B1060285 : Blo 834351 1060285 := bbase (se 3 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 1060285 = 397607) (by norm_num)
theorem B1256909 : Blo 834351 1256909 := bbase (se 3 (by rfl) ⟨235670, by rfl⟩ : syracuseStep 1256909 = 471341) (by norm_num)
theorem B1256933 : Blo 834351 1256933 := bbase (se 4 (by rfl) ⟨117837, by rfl⟩ : syracuseStep 1256933 = 235675) (by norm_num)
theorem B1879541 : Blo 834351 1879541 := bbase (se 5 (by rfl) ⟨88103, by rfl⟩ : syracuseStep 1879541 = 176207) (by norm_num)
theorem B1256957 : Blo 834351 1256957 := bbase (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) (by norm_num)
theorem B1256981 : Blo 834351 1256981 := bbase (se 6 (by rfl) ⟨29460, by rfl⟩ : syracuseStep 1256981 = 58921) (by norm_num)
theorem B1060381 : Blo 834351 1060381 := bbase (se 3 (by rfl) ⟨198821, by rfl⟩ : syracuseStep 1060381 = 397643) (by norm_num)
theorem B3059237 : Blo 834351 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B1257005 : Blo 834351 1257005 := bbase (se 3 (by rfl) ⟨235688, by rfl⟩ : syracuseStep 1257005 = 471377) (by norm_num)
theorem B1879613 : Blo 834351 1879613 := bbase (se 3 (by rfl) ⟨352427, by rfl⟩ : syracuseStep 1879613 = 704855) (by norm_num)
theorem B2010685 : Blo 834351 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B1257029 : Blo 834351 1257029 := bbase (se 4 (by rfl) ⟨117846, by rfl⟩ : syracuseStep 1257029 = 235693) (by norm_num)
theorem B1257053 : Blo 834351 1257053 := bbase (se 3 (by rfl) ⟨235697, by rfl⟩ : syracuseStep 1257053 = 471395) (by norm_num)
theorem B7155317 : Blo 834351 7155317 := bbase (se 5 (by rfl) ⟨335405, by rfl⟩ : syracuseStep 7155317 = 670811) (by norm_num)
theorem B1257077 : Blo 834351 1257077 := bbase (se 5 (by rfl) ⟨58925, by rfl⟩ : syracuseStep 1257077 = 117851) (by norm_num)
theorem B1879685 : Blo 834351 1879685 := bbase (se 4 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 1879685 = 352441) (by norm_num)
theorem B1257101 : Blo 834351 1257101 := bbase (se 3 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 1257101 = 471413) (by norm_num)
theorem B1257125 : Blo 834351 1257125 := bbase (se 4 (by rfl) ⟨117855, by rfl⟩ : syracuseStep 1257125 = 235711) (by norm_num)
theorem B1257149 : Blo 834351 1257149 := bbase (se 3 (by rfl) ⟨235715, by rfl⟩ : syracuseStep 1257149 = 471431) (by norm_num)
theorem B1060553 : Blo 834351 1060553 := bbase (se 2 (by rfl) ⟨397707, by rfl⟩ : syracuseStep 1060553 = 795415) (by norm_num)
theorem B1879757 : Blo 834351 1879757 := bbase (se 3 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 1879757 = 704909) (by norm_num)
theorem B1257173 : Blo 834351 1257173 := bbase (se 7 (by rfl) ⟨14732, by rfl⟩ : syracuseStep 1257173 = 29465) (by norm_num)
theorem B1257197 : Blo 834351 1257197 := bbase (se 3 (by rfl) ⟨235724, by rfl⟩ : syracuseStep 1257197 = 471449) (by norm_num)
theorem B1289981 : Blo 834351 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B1060609 : Blo 834351 1060609 := bbase (se 2 (by rfl) ⟨397728, by rfl⟩ : syracuseStep 1060609 = 795457) (by norm_num)
theorem B1257221 : Blo 834351 1257221 := bbase (se 4 (by rfl) ⟨117864, by rfl⟩ : syracuseStep 1257221 = 235729) (by norm_num)
theorem B1879829 : Blo 834351 1879829 := bbase (se 6 (by rfl) ⟨44058, by rfl⟩ : syracuseStep 1879829 = 88117) (by norm_num)
theorem B1257245 : Blo 834351 1257245 := bbase (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) (by norm_num)
theorem B1257269 : Blo 834351 1257269 := bbase (se 5 (by rfl) ⟨58934, by rfl⟩ : syracuseStep 1257269 = 117869) (by norm_num)
theorem B1257293 : Blo 834351 1257293 := bbase (se 3 (by rfl) ⟨235742, by rfl⟩ : syracuseStep 1257293 = 471485) (by norm_num)
theorem B1879901 : Blo 834351 1879901 := bbase (se 3 (by rfl) ⟨352481, by rfl⟩ : syracuseStep 1879901 = 704963) (by norm_num)
theorem B1191773 : Blo 834351 1191773 := bbase (se 3 (by rfl) ⟨223457, by rfl⟩ : syracuseStep 1191773 = 446915) (by norm_num)
theorem B1060705 : Blo 834351 1060705 := bbase (se 2 (by rfl) ⟨397764, by rfl⟩ : syracuseStep 1060705 = 795529) (by norm_num)
theorem B1257317 : Blo 834351 1257317 := bbase (se 4 (by rfl) ⟨117873, by rfl⟩ : syracuseStep 1257317 = 235747) (by norm_num)
theorem B1355629 : Blo 834351 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B1585021 : Blo 834351 1585021 := bbase (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) (by norm_num)
theorem B1257341 : Blo 834351 1257341 := bbase (se 3 (by rfl) ⟨235751, by rfl⟩ : syracuseStep 1257341 = 471503) (by norm_num)
theorem B1257365 : Blo 834351 1257365 := bbase (se 6 (by rfl) ⟨29469, by rfl⟩ : syracuseStep 1257365 = 58939) (by norm_num)
theorem B1879973 : Blo 834351 1879973 := bbase (se 4 (by rfl) ⟨176247, by rfl⟩ : syracuseStep 1879973 = 352495) (by norm_num)
theorem B1257389 : Blo 834351 1257389 := bbase (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) (by norm_num)
theorem B1257413 : Blo 834351 1257413 := bbase (se 4 (by rfl) ⟨117882, by rfl⟩ : syracuseStep 1257413 = 235765) (by norm_num)
theorem B1257437 : Blo 834351 1257437 := bbase (se 3 (by rfl) ⟨235769, by rfl⟩ : syracuseStep 1257437 = 471539) (by norm_num)
theorem B1880045 : Blo 834351 1880045 := bbase (se 3 (by rfl) ⟨352508, by rfl⟩ : syracuseStep 1880045 = 705017) (by norm_num)
theorem B1257461 : Blo 834351 1257461 := bbase (se 5 (by rfl) ⟨58943, by rfl⟩ : syracuseStep 1257461 = 117887) (by norm_num)
theorem B1585165 : Blo 834351 1585165 := bbase (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) (by norm_num)
theorem B1060877 : Blo 834351 1060877 := bbase (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) (by norm_num)
theorem B1257485 : Blo 834351 1257485 := bbase (se 3 (by rfl) ⟨235778, by rfl⟩ : syracuseStep 1257485 = 471557) (by norm_num)
theorem B1257509 : Blo 834351 1257509 := bbase (se 4 (by rfl) ⟨117891, by rfl⟩ : syracuseStep 1257509 = 235783) (by norm_num)
theorem B1880117 : Blo 834351 1880117 := bbase (se 5 (by rfl) ⟨88130, by rfl⟩ : syracuseStep 1880117 = 176261) (by norm_num)
theorem B1060933 : Blo 834351 1060933 := bbase (se 4 (by rfl) ⟨99462, by rfl⟩ : syracuseStep 1060933 = 198925) (by norm_num)
theorem B1880189 : Blo 834351 1880189 := bbase (se 3 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 1880189 = 705071) (by norm_num)
theorem B2011301 : Blo 834351 2011301 := bbase (se 4 (by rfl) ⟨188559, by rfl⟩ : syracuseStep 2011301 = 377119) (by norm_num)
theorem B1061029 : Blo 834351 1061029 := bbase (se 4 (by rfl) ⟨99471, by rfl⟩ : syracuseStep 1061029 = 198943) (by norm_num)
theorem B1585325 : Blo 834351 1585325 := bbase (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) (by norm_num)
theorem B1880261 : Blo 834351 1880261 := bbase (se 4 (by rfl) ⟨176274, by rfl⟩ : syracuseStep 1880261 = 352549) (by norm_num)
theorem B1782013 : Blo 834351 1782013 := bbase (se 3 (by rfl) ⟨334127, by rfl⟩ : syracuseStep 1782013 = 668255) (by norm_num)
theorem B1880333 : Blo 834351 1880333 := bbase (se 3 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 1880333 = 705125) (by norm_num)
theorem B1585469 : Blo 834351 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1880405 : Blo 834351 1880405 := bbase (se 10 (by rfl) ⟨2754, by rfl⟩ : syracuseStep 1880405 = 5509) (by norm_num)
theorem B4239701 : Blo 834351 4239701 := bbase (se 10 (by rfl) ⟨6210, by rfl⟩ : syracuseStep 4239701 = 12421) (by norm_num)
theorem B1192325 : Blo 834351 1192325 := bbase (se 4 (by rfl) ⟨111780, by rfl⟩ : syracuseStep 1192325 = 223561) (by norm_num)
theorem B1880477 : Blo 834351 1880477 := bbase (se 3 (by rfl) ⟨352589, by rfl⟩ : syracuseStep 1880477 = 705179) (by norm_num)
theorem B1880549 : Blo 834351 1880549 := bbase (se 4 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 1880549 = 352603) (by norm_num)
theorem B1880621 : Blo 834351 1880621 := bbase (se 3 (by rfl) ⟨352616, by rfl⟩ : syracuseStep 1880621 = 705233) (by norm_num)
theorem B2011733 : Blo 834351 2011733 := bbase (se 8 (by rfl) ⟨11787, by rfl⟩ : syracuseStep 2011733 = 23575) (by norm_num)
theorem B1585757 : Blo 834351 1585757 := bbase (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) (by norm_num)
theorem B1880693 : Blo 834351 1880693 := bbase (se 5 (by rfl) ⟨88157, by rfl⟩ : syracuseStep 1880693 = 176315) (by norm_num)
theorem B1880765 : Blo 834351 1880765 := bbase (se 3 (by rfl) ⟨352643, by rfl⟩ : syracuseStep 1880765 = 705287) (by norm_num)
theorem B1585909 : Blo 834351 1585909 := bbase (se 5 (by rfl) ⟨74339, by rfl⟩ : syracuseStep 1585909 = 148679) (by norm_num)
theorem B1880837 : Blo 834351 1880837 := bbase (se 4 (by rfl) ⟨176328, by rfl⟩ : syracuseStep 1880837 = 352657) (by norm_num)
theorem B1880909 : Blo 834351 1880909 := bbase (se 3 (by rfl) ⟨352670, by rfl⟩ : syracuseStep 1880909 = 705341) (by norm_num)
theorem B2208653 : Blo 834351 2208653 := bbase (se 3 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 2208653 = 828245) (by norm_num)
theorem B1880981 : Blo 834351 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B1881053 : Blo 834351 1881053 := bbase (se 3 (by rfl) ⟨352697, by rfl⟩ : syracuseStep 1881053 = 705395) (by norm_num)
theorem B1586213 : Blo 834351 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B1881125 : Blo 834351 1881125 := bbase (se 4 (by rfl) ⟨176355, by rfl⟩ : syracuseStep 1881125 = 352711) (by norm_num)
theorem B1881197 : Blo 834351 1881197 := bbase (se 3 (by rfl) ⟨352724, by rfl⟩ : syracuseStep 1881197 = 705449) (by norm_num)
theorem B1782901 : Blo 834351 1782901 := bbase (se 5 (by rfl) ⟨83573, by rfl⟩ : syracuseStep 1782901 = 167147) (by norm_num)
theorem B1193077 : Blo 834351 1193077 := bbase (se 5 (by rfl) ⟨55925, by rfl⟩ : syracuseStep 1193077 = 111851) (by norm_num)
theorem B1881269 : Blo 834351 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B2012357 : Blo 834351 2012357 := bbase (se 4 (by rfl) ⟨188658, by rfl⟩ : syracuseStep 2012357 = 377317) (by norm_num)
theorem B4011221 : Blo 834351 4011221 := bbase (se 7 (by rfl) ⟨47006, by rfl⟩ : syracuseStep 4011221 = 94013) (by norm_num)
theorem B1881341 : Blo 834351 1881341 := bbase (se 3 (by rfl) ⟨352751, by rfl⟩ : syracuseStep 1881341 = 705503) (by norm_num)
theorem B1881413 : Blo 834351 1881413 := bbase (se 4 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 1881413 = 352765) (by norm_num)
theorem B1881485 : Blo 834351 1881485 := bbase (se 3 (by rfl) ⟨352778, by rfl⟩ : syracuseStep 1881485 = 705557) (by norm_num)
theorem B14464469 : Blo 834351 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B1881557 : Blo 834351 1881557 := bbase (se 7 (by rfl) ⟨22049, by rfl⟩ : syracuseStep 1881557 = 44099) (by norm_num)
theorem B3814933 : Blo 834351 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B1881629 : Blo 834351 1881629 := bbase (se 3 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 1881629 = 705611) (by norm_num)
theorem B1783397 : Blo 834351 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B1881701 : Blo 834351 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B4240997 : Blo 834351 4240997 := bbase (se 4 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 4240997 = 795187) (by norm_num)
theorem B1881773 : Blo 834351 1881773 := bbase (se 3 (by rfl) ⟨352832, by rfl⟩ : syracuseStep 1881773 = 705665) (by norm_num)
theorem B1881845 : Blo 834351 1881845 := bbase (se 5 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 1881845 = 176423) (by norm_num)
theorem B1586965 : Blo 834351 1586965 := bbase (se 6 (by rfl) ⟨37194, by rfl⟩ : syracuseStep 1586965 = 74389) (by norm_num)
theorem B1128253 : Blo 834351 1128253 := bbase (se 3 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 1128253 = 423095) (by norm_num)
theorem B1881917 : Blo 834351 1881917 := bbase (se 3 (by rfl) ⟨352859, by rfl⟩ : syracuseStep 1881917 = 705719) (by norm_num)
theorem B1718101 : Blo 834351 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B1881989 : Blo 834351 1881989 := bbase (se 4 (by rfl) ⟨176436, by rfl⟩ : syracuseStep 1881989 = 352873) (by norm_num)
theorem B1587109 : Blo 834351 1587109 := bbase (se 4 (by rfl) ⟨148791, by rfl⟩ : syracuseStep 1587109 = 297583) (by norm_num)
theorem B1882061 : Blo 834351 1882061 := bbase (se 3 (by rfl) ⟨352886, by rfl⟩ : syracuseStep 1882061 = 705773) (by norm_num)
theorem B1882133 : Blo 834351 1882133 := bbase (se 6 (by rfl) ⟨44112, by rfl⟩ : syracuseStep 1882133 = 88225) (by norm_num)
theorem B1587269 : Blo 834351 1587269 := bbase (se 4 (by rfl) ⟨148806, by rfl⟩ : syracuseStep 1587269 = 297613) (by norm_num)
theorem B2144333 : Blo 834351 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B1882205 : Blo 834351 1882205 := bbase (se 3 (by rfl) ⟨352913, by rfl⟩ : syracuseStep 1882205 = 705827) (by norm_num)
theorem B1882277 : Blo 834351 1882277 := bbase (se 4 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 1882277 = 352927) (by norm_num)
theorem B1587413 : Blo 834351 1587413 := bbase (se 7 (by rfl) ⟨18602, by rfl⟩ : syracuseStep 1587413 = 37205) (by norm_num)
theorem B1882349 : Blo 834351 1882349 := bbase (se 3 (by rfl) ⟨352940, by rfl⟩ : syracuseStep 1882349 = 705881) (by norm_num)
theorem B1882421 : Blo 834351 1882421 := bbase (se 5 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 1882421 = 176477) (by norm_num)
theorem B1882493 : Blo 834351 1882493 := bbase (se 3 (by rfl) ⟨352967, by rfl⟩ : syracuseStep 1882493 = 705935) (by norm_num)
theorem B1882565 : Blo 834351 1882565 := bbase (se 4 (by rfl) ⟨176490, by rfl⟩ : syracuseStep 1882565 = 352981) (by norm_num)
theorem B1784285 : Blo 834351 1784285 := bbase (se 3 (by rfl) ⟨334553, by rfl⟩ : syracuseStep 1784285 = 669107) (by norm_num)
theorem B1587701 : Blo 834351 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B1882637 : Blo 834351 1882637 := bbase (se 3 (by rfl) ⟨352994, by rfl⟩ : syracuseStep 1882637 = 705989) (by norm_num)
theorem B7158293 : Blo 834351 7158293 := bbase (se 6 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 7158293 = 335545) (by norm_num)
theorem B1784405 : Blo 834351 1784405 := bbase (se 8 (by rfl) ⟨10455, by rfl⟩ : syracuseStep 1784405 = 20911) (by norm_num)
theorem B1882709 : Blo 834351 1882709 := bbase (se 8 (by rfl) ⟨11031, by rfl⟩ : syracuseStep 1882709 = 22063) (by norm_num)
theorem B1587853 : Blo 834351 1587853 := bbase (se 3 (by rfl) ⟨297722, by rfl⟩ : syracuseStep 1587853 = 595445) (by norm_num)
theorem B1882781 : Blo 834351 1882781 := bbase (se 3 (by rfl) ⟨353021, by rfl⟩ : syracuseStep 1882781 = 706043) (by norm_num)
theorem B1882853 : Blo 834351 1882853 := bbase (se 4 (by rfl) ⟨176517, by rfl⟩ : syracuseStep 1882853 = 353035) (by norm_num)
theorem B2538229 : Blo 834351 2538229 := bbase (se 5 (by rfl) ⟨118979, by rfl⟩ : syracuseStep 2538229 = 237959) (by norm_num)
theorem B2112277 : Blo 834351 2112277 := bbase (se 6 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 2112277 = 99013) (by norm_num)
theorem B1882925 : Blo 834351 1882925 := bbase (se 3 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 1882925 = 706097) (by norm_num)
theorem B1882997 : Blo 834351 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B4242293 : Blo 834351 4242293 := bbase (se 5 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 4242293 = 397715) (by norm_num)
theorem B2112389 : Blo 834351 2112389 := bbase (se 4 (by rfl) ⟨198036, by rfl⟩ : syracuseStep 2112389 = 396073) (by norm_num)
theorem B1588157 : Blo 834351 1588157 := bbase (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) (by norm_num)
theorem B1883069 : Blo 834351 1883069 := bbase (se 3 (by rfl) ⟨353075, by rfl⟩ : syracuseStep 1883069 = 706151) (by norm_num)
theorem B1883141 : Blo 834351 1883141 := bbase (se 4 (by rfl) ⟨176544, by rfl⟩ : syracuseStep 1883141 = 353089) (by norm_num)
theorem B2112581 : Blo 834351 2112581 := bbase (se 4 (by rfl) ⟨198054, by rfl⟩ : syracuseStep 2112581 = 396109) (by norm_num)
theorem B1883213 : Blo 834351 1883213 := bbase (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) (by norm_num)
theorem B1883285 : Blo 834351 1883285 := bbase (se 6 (by rfl) ⟨44139, by rfl⟩ : syracuseStep 1883285 = 88279) (by norm_num)
theorem B1129637 : Blo 834351 1129637 := bbase (se 4 (by rfl) ⟨105903, by rfl⟩ : syracuseStep 1129637 = 211807) (by norm_num)
theorem B1785037 : Blo 834351 1785037 := bbase (se 3 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 1785037 = 669389) (by norm_num)
theorem B1883357 : Blo 834351 1883357 := bbase (se 3 (by rfl) ⟨353129, by rfl⟩ : syracuseStep 1883357 = 706259) (by norm_num)
theorem B1883429 : Blo 834351 1883429 := bbase (se 4 (by rfl) ⟨176571, by rfl⟩ : syracuseStep 1883429 = 353143) (by norm_num)
theorem B5356853 : Blo 834351 5356853 := bbase (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) (by norm_num)
theorem B1883501 : Blo 834351 1883501 := bbase (se 3 (by rfl) ⟨353156, by rfl⟩ : syracuseStep 1883501 = 706313) (by norm_num)
theorem B12041621 : Blo 834351 12041621 := bbase (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) (by norm_num)
theorem B2112925 : Blo 834351 2112925 := bbase (se 3 (by rfl) ⟨396173, by rfl⟩ : syracuseStep 2112925 = 792347) (by norm_num)
theorem B1883573 : Blo 834351 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B1883645 : Blo 834351 1883645 := bbase (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) (by norm_num)
theorem B2113037 : Blo 834351 2113037 := bbase (se 3 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 2113037 = 792389) (by norm_num)
theorem B1883717 : Blo 834351 1883717 := bbase (se 4 (by rfl) ⟨176598, by rfl⟩ : syracuseStep 1883717 = 353197) (by norm_num)
theorem B1883789 : Blo 834351 1883789 := bbase (se 3 (by rfl) ⟨353210, by rfl⟩ : syracuseStep 1883789 = 706421) (by norm_num)
theorem B3620501 : Blo 834351 3620501 := bbase (se 6 (by rfl) ⟨84855, by rfl⟩ : syracuseStep 3620501 = 169711) (by norm_num)
theorem B1588909 : Blo 834351 1588909 := bbase (se 3 (by rfl) ⟨297920, by rfl⟩ : syracuseStep 1588909 = 595841) (by norm_num)
theorem B2113229 : Blo 834351 2113229 := bbase (se 3 (by rfl) ⟨396230, by rfl⟩ : syracuseStep 2113229 = 792461) (by norm_num)
theorem B1883861 : Blo 834351 1883861 := bbase (se 7 (by rfl) ⟨22076, by rfl⟩ : syracuseStep 1883861 = 44153) (by norm_num)
theorem B1130221 : Blo 834351 1130221 := bbase (se 3 (by rfl) ⟨211916, by rfl⟩ : syracuseStep 1130221 = 423833) (by norm_num)
theorem B1883933 : Blo 834351 1883933 := bbase (se 3 (by rfl) ⟨353237, by rfl⟩ : syracuseStep 1883933 = 706475) (by norm_num)
theorem B1589053 : Blo 834351 1589053 := bbase (se 3 (by rfl) ⟨297947, by rfl⟩ : syracuseStep 1589053 = 595895) (by norm_num)
theorem B1884005 : Blo 834351 1884005 := bbase (se 4 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 1884005 = 353251) (by norm_num)
theorem B1884077 : Blo 834351 1884077 := bbase (se 3 (by rfl) ⟨353264, by rfl⟩ : syracuseStep 1884077 = 706529) (by norm_num)
theorem B3391429 : Blo 834351 3391429 := bbase (se 4 (by rfl) ⟨317946, by rfl⟩ : syracuseStep 3391429 = 635893) (by norm_num)
theorem B1589213 : Blo 834351 1589213 := bbase (se 3 (by rfl) ⟨297977, by rfl⟩ : syracuseStep 1589213 = 595955) (by norm_num)
theorem B1884149 : Blo 834351 1884149 := bbase (se 5 (by rfl) ⟨88319, by rfl⟩ : syracuseStep 1884149 = 176639) (by norm_num)
theorem B2113573 : Blo 834351 2113573 := bbase (se 4 (by rfl) ⟨198147, by rfl⟩ : syracuseStep 2113573 = 396295) (by norm_num)
theorem B5161013 : Blo 834351 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B1884221 : Blo 834351 1884221 := bbase (se 3 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 1884221 = 706583) (by norm_num)
theorem B1785925 : Blo 834351 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B1589357 : Blo 834351 1589357 := bbase (se 3 (by rfl) ⟨298004, by rfl⟩ : syracuseStep 1589357 = 596009) (by norm_num)
theorem B1884293 : Blo 834351 1884293 := bbase (se 4 (by rfl) ⟨176652, by rfl⟩ : syracuseStep 1884293 = 353305) (by norm_num)
theorem B4243589 : Blo 834351 4243589 := bbase (se 4 (by rfl) ⟨397836, by rfl⟩ : syracuseStep 4243589 = 795673) (by norm_num)
theorem B2113685 : Blo 834351 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B1786045 : Blo 834351 1786045 := bbase (se 3 (by rfl) ⟨334883, by rfl⟩ : syracuseStep 1786045 = 669767) (by norm_num)
theorem B1884365 : Blo 834351 1884365 := bbase (se 3 (by rfl) ⟨353318, by rfl⟩ : syracuseStep 1884365 = 706637) (by norm_num)
theorem B1884437 : Blo 834351 1884437 := bbase (se 6 (by rfl) ⟨44166, by rfl⟩ : syracuseStep 1884437 = 88333) (by norm_num)
theorem B2113877 : Blo 834351 2113877 := bbase (se 10 (by rfl) ⟨3096, by rfl⟩ : syracuseStep 2113877 = 6193) (by norm_num)
theorem B1884509 : Blo 834351 1884509 := bbase (se 3 (by rfl) ⟨353345, by rfl⟩ : syracuseStep 1884509 = 706691) (by norm_num)
theorem B1589645 : Blo 834351 1589645 := bbase (se 3 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 1589645 = 596117) (by norm_num)
theorem B1884581 : Blo 834351 1884581 := bbase (se 4 (by rfl) ⟨176679, by rfl⟩ : syracuseStep 1884581 = 353359) (by norm_num)
theorem B1786301 : Blo 834351 1786301 := bbase (se 3 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 1786301 = 669863) (by norm_num)
theorem B1884653 : Blo 834351 1884653 := bbase (se 3 (by rfl) ⟨353372, by rfl⟩ : syracuseStep 1884653 = 706745) (by norm_num)
theorem B1589797 : Blo 834351 1589797 := bbase (se 4 (by rfl) ⟨149043, by rfl⟩ : syracuseStep 1589797 = 298087) (by norm_num)
theorem B1884725 : Blo 834351 1884725 := bbase (se 5 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 1884725 = 176693) (by norm_num)
theorem B1884797 : Blo 834351 1884797 := bbase (se 3 (by rfl) ⟨353399, by rfl⟩ : syracuseStep 1884797 = 706799) (by norm_num)
theorem B2114221 : Blo 834351 2114221 := bbase (se 3 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 2114221 = 792833) (by norm_num)
theorem B1884869 : Blo 834351 1884869 := bbase (se 4 (by rfl) ⟨176706, by rfl⟩ : syracuseStep 1884869 = 353413) (by norm_num)
theorem B1884941 : Blo 834351 1884941 := bbase (se 3 (by rfl) ⟨353426, by rfl⟩ : syracuseStep 1884941 = 706853) (by norm_num)
theorem B2114333 : Blo 834351 2114333 := bbase (se 3 (by rfl) ⟨396437, by rfl⟩ : syracuseStep 2114333 = 792875) (by norm_num)
theorem B1590101 : Blo 834351 1590101 := bbase (se 9 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 1590101 = 9317) (by norm_num)
theorem B1885013 : Blo 834351 1885013 := bbase (se 9 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 1885013 = 11045) (by norm_num)
theorem B1524629 : Blo 834351 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B1885085 : Blo 834351 1885085 := bbase (se 3 (by rfl) ⟨353453, by rfl⟩ : syracuseStep 1885085 = 706907) (by norm_num)
theorem B2114525 : Blo 834351 2114525 := bbase (se 3 (by rfl) ⟨396473, by rfl⟩ : syracuseStep 2114525 = 792947) (by norm_num)
theorem B2376677 : Blo 834351 2376677 := bbase (se 4 (by rfl) ⟨222813, by rfl⟩ : syracuseStep 2376677 = 445627) (by norm_num)
theorem B1885157 : Blo 834351 1885157 := bbase (se 4 (by rfl) ⟨176733, by rfl⟩ : syracuseStep 1885157 = 353467) (by norm_num)
theorem B1885229 : Blo 834351 1885229 := bbase (se 3 (by rfl) ⟨353480, by rfl⟩ : syracuseStep 1885229 = 706961) (by norm_num)
theorem B1885301 : Blo 834351 1885301 := bbase (se 5 (by rfl) ⟨88373, by rfl⟩ : syracuseStep 1885301 = 176747) (by norm_num)
theorem B6341813 : Blo 834351 6341813 := bbase (se 5 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 6341813 = 594545) (by norm_num)
theorem B1885373 : Blo 834351 1885373 := bbase (se 3 (by rfl) ⟨353507, by rfl⟩ : syracuseStep 1885373 = 707015) (by norm_num)
theorem B3392725 : Blo 834351 3392725 := bbase (se 7 (by rfl) ⟨39758, by rfl⟩ : syracuseStep 3392725 = 79517) (by norm_num)
theorem B1885445 : Blo 834351 1885445 := bbase (se 4 (by rfl) ⟨176760, by rfl⟩ : syracuseStep 1885445 = 353521) (by norm_num)
theorem B2114869 : Blo 834351 2114869 := bbase (se 5 (by rfl) ⟨99134, by rfl⟩ : syracuseStep 2114869 = 198269) (by norm_num)
theorem B1787189 : Blo 834351 1787189 := bbase (se 5 (by rfl) ⟨83774, by rfl⟩ : syracuseStep 1787189 = 167549) (by norm_num)
theorem B1885517 : Blo 834351 1885517 := bbase (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) (by norm_num)
theorem B1885589 : Blo 834351 1885589 := bbase (se 6 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 1885589 = 88387) (by norm_num)
theorem B2114981 : Blo 834351 2114981 := bbase (se 4 (by rfl) ⟨198279, by rfl⟩ : syracuseStep 2114981 = 396559) (by norm_num)
theorem B1885661 : Blo 834351 1885661 := bbase (se 3 (by rfl) ⟨353561, by rfl⟩ : syracuseStep 1885661 = 707123) (by norm_num)
theorem B1787429 : Blo 834351 1787429 := bbase (se 4 (by rfl) ⟨167571, by rfl⟩ : syracuseStep 1787429 = 335143) (by norm_num)
theorem B1885733 : Blo 834351 1885733 := bbase (se 4 (by rfl) ⟨176787, by rfl⟩ : syracuseStep 1885733 = 353575) (by norm_num)
theorem B1590853 : Blo 834351 1590853 := bbase (se 4 (by rfl) ⟨149142, by rfl⟩ : syracuseStep 1590853 = 298285) (by norm_num)
theorem B2115173 : Blo 834351 2115173 := bbase (se 4 (by rfl) ⟨198297, by rfl⟩ : syracuseStep 2115173 = 396595) (by norm_num)
theorem B1885805 : Blo 834351 1885805 := bbase (se 3 (by rfl) ⟨353588, by rfl⟩ : syracuseStep 1885805 = 707177) (by norm_num)
theorem B1885877 : Blo 834351 1885877 := bbase (se 5 (by rfl) ⟨88400, by rfl⟩ : syracuseStep 1885877 = 176801) (by norm_num)
theorem B1590997 : Blo 834351 1590997 := bbase (se 7 (by rfl) ⟨18644, by rfl⟩ : syracuseStep 1590997 = 37289) (by norm_num)
theorem B1885949 : Blo 834351 1885949 := bbase (se 3 (by rfl) ⟨353615, by rfl⟩ : syracuseStep 1885949 = 707231) (by norm_num)
theorem B1886021 : Blo 834351 1886021 := bbase (se 4 (by rfl) ⟨176814, by rfl⟩ : syracuseStep 1886021 = 353629) (by norm_num)
theorem B1591157 : Blo 834351 1591157 := bbase (se 5 (by rfl) ⟨74585, by rfl⟩ : syracuseStep 1591157 = 149171) (by norm_num)
theorem B1886093 : Blo 834351 1886093 := bbase (se 3 (by rfl) ⟨353642, by rfl⟩ : syracuseStep 1886093 = 707285) (by norm_num)
theorem B2115517 : Blo 834351 2115517 := bbase (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) (by norm_num)
theorem B1886165 : Blo 834351 1886165 := bbase (se 7 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 1886165 = 44207) (by norm_num)
theorem B1591301 : Blo 834351 1591301 := bbase (se 4 (by rfl) ⟨149184, by rfl⟩ : syracuseStep 1591301 = 298369) (by norm_num)
theorem B1787933 : Blo 834351 1787933 := bbase (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) (by norm_num)
theorem B1886237 : Blo 834351 1886237 := bbase (se 3 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 1886237 = 707339) (by norm_num)
theorem B1787941 : Blo 834351 1787941 := bbase (se 4 (by rfl) ⟨167619, by rfl⟩ : syracuseStep 1787941 = 335239) (by norm_num)
theorem B2115629 : Blo 834351 2115629 := bbase (se 3 (by rfl) ⟨396680, by rfl⟩ : syracuseStep 2115629 = 793361) (by norm_num)
theorem B1132741 : Blo 834351 1132741 := bbase (se 4 (by rfl) ⟨106194, by rfl⟩ : syracuseStep 1132741 = 212389) (by norm_num)
theorem B2115821 : Blo 834351 2115821 := bbase (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) (by norm_num)
theorem B8046965 : Blo 834351 8046965 := bbase (se 5 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 8046965 = 754403) (by norm_num)
theorem B3394037 : Blo 834351 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B2378261 : Blo 834351 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B2116165 : Blo 834351 2116165 := bbase (se 4 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 2116165 = 396781) (by norm_num)
theorem B3394165 : Blo 834351 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B2116277 : Blo 834351 2116277 := bbase (se 5 (by rfl) ⟨99200, by rfl⟩ : syracuseStep 2116277 = 198401) (by norm_num)
theorem B4770485 : Blo 834351 4770485 := bbase (se 5 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 4770485 = 447233) (by norm_num)
theorem B1428301 : Blo 834351 1428301 := bbase (se 3 (by rfl) ⟨267806, by rfl⟩ : syracuseStep 1428301 = 535613) (by norm_num)
theorem B2116469 : Blo 834351 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B2673557 : Blo 834351 2673557 := bbase (se 6 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 2673557 = 125323) (by norm_num)
theorem B9522197 : Blo 834351 9522197 := bbase (se 6 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 9522197 = 446353) (by norm_num)
theorem B1002565 : Blo 834351 1002565 := bbase (se 4 (by rfl) ⟨93990, by rfl⟩ : syracuseStep 1002565 = 187981) (by norm_num)
theorem B1002637 : Blo 834351 1002637 := bbase (se 3 (by rfl) ⟨187994, by rfl⟩ : syracuseStep 1002637 = 375989) (by norm_num)
theorem B1789069 : Blo 834351 1789069 := bbase (se 3 (by rfl) ⟨335450, by rfl⟩ : syracuseStep 1789069 = 670901) (by norm_num)
theorem B1428629 : Blo 834351 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B2378933 : Blo 834351 2378933 := bbase (se 5 (by rfl) ⟨111512, by rfl⟩ : syracuseStep 2378933 = 223025) (by norm_num)
theorem B2116813 : Blo 834351 2116813 := bbase (se 3 (by rfl) ⟨396902, by rfl⟩ : syracuseStep 2116813 = 793805) (by norm_num)
theorem B2116925 : Blo 834351 2116925 := bbase (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) (by norm_num)
theorem B1527229 : Blo 834351 1527229 := bbase (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) (by norm_num)
theorem B2117117 : Blo 834351 2117117 := bbase (se 3 (by rfl) ⟨396959, by rfl⟩ : syracuseStep 2117117 = 793919) (by norm_num)
theorem B1789445 : Blo 834351 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B3395141 : Blo 834351 3395141 := bbase (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) (by norm_num)
theorem B2379365 : Blo 834351 2379365 := bbase (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) (by norm_num)
theorem B2117461 : Blo 834351 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B4771669 : Blo 834351 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B1429445 : Blo 834351 1429445 := bbase (se 4 (by rfl) ⟨134010, by rfl⟩ : syracuseStep 1429445 = 268021) (by norm_num)
theorem B2117573 : Blo 834351 2117573 := bbase (se 4 (by rfl) ⟨198522, by rfl⟩ : syracuseStep 2117573 = 397045) (by norm_num)
theorem B2543605 : Blo 834351 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B1003637 : Blo 834351 1003637 := bbase (se 5 (by rfl) ⟨47045, by rfl⟩ : syracuseStep 1003637 = 94091) (by norm_num)
theorem B2117765 : Blo 834351 2117765 := bbase (se 4 (by rfl) ⟨198540, by rfl⟩ : syracuseStep 2117765 = 397081) (by norm_num)
theorem B2380117 : Blo 834351 2380117 := bbase (se 10 (by rfl) ⟨3486, by rfl⟩ : syracuseStep 2380117 = 6973) (by norm_num)
theorem B2118109 : Blo 834351 2118109 := bbase (se 3 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 2118109 = 794291) (by norm_num)
theorem B2118221 : Blo 834351 2118221 := bbase (se 3 (by rfl) ⟨397166, by rfl⟩ : syracuseStep 2118221 = 794333) (by norm_num)
theorem B938677 : Blo 834351 938677 := bbase (se 5 (by rfl) ⟨44000, by rfl⟩ : syracuseStep 938677 = 88001) (by norm_num)
theorem B938713 : Blo 834351 938713 := bbase (se 2 (by rfl) ⟨352017, by rfl⟩ : syracuseStep 938713 = 704035) (by norm_num)
theorem B1430245 : Blo 834351 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B938749 : Blo 834351 938749 := bbase (se 3 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 938749 = 352031) (by norm_num)
theorem B2118413 : Blo 834351 2118413 := bbase (se 3 (by rfl) ⟨397202, by rfl⟩ : syracuseStep 2118413 = 794405) (by norm_num)
theorem B6017813 : Blo 834351 6017813 := bbase (se 6 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 6017813 = 282085) (by norm_num)
theorem B938785 : Blo 834351 938785 := bbase (se 2 (by rfl) ⟨352044, by rfl⟩ : syracuseStep 938785 = 704089) (by norm_num)
theorem B1004329 : Blo 834351 1004329 := bbase (se 2 (by rfl) ⟨376623, by rfl⟩ : syracuseStep 1004329 = 753247) (by norm_num)
theorem B1004333 : Blo 834351 1004333 := bbase (se 3 (by rfl) ⟨188312, by rfl⟩ : syracuseStep 1004333 = 376625) (by norm_num)
theorem B938821 : Blo 834351 938821 := bbase (se 4 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 938821 = 176029) (by norm_num)
theorem B938857 : Blo 834351 938857 := bbase (se 2 (by rfl) ⟨352071, by rfl⟩ : syracuseStep 938857 = 704143) (by norm_num)
theorem B938893 : Blo 834351 938893 := bbase (se 3 (by rfl) ⟨176042, by rfl⟩ : syracuseStep 938893 = 352085) (by norm_num)
theorem B938929 : Blo 834351 938929 := bbase (se 2 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 938929 = 704197) (by norm_num)
theorem B938965 : Blo 834351 938965 := bbase (se 7 (by rfl) ⟨11003, by rfl⟩ : syracuseStep 938965 = 22007) (by norm_num)
theorem B5362645 : Blo 834351 5362645 := bbase (se 7 (by rfl) ⟨62843, by rfl⟩ : syracuseStep 5362645 = 125687) (by norm_num)
theorem B939001 : Blo 834351 939001 := bbase (se 2 (by rfl) ⟨352125, by rfl⟩ : syracuseStep 939001 = 704251) (by norm_num)
theorem B939037 : Blo 834351 939037 := bbase (se 3 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 939037 = 352139) (by norm_num)
theorem B2675749 : Blo 834351 2675749 := bbase (se 4 (by rfl) ⟨250851, by rfl⟩ : syracuseStep 2675749 = 501703) (by norm_num)
theorem B939073 : Blo 834351 939073 := bbase (se 2 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 939073 = 704305) (by norm_num)
theorem B939109 : Blo 834351 939109 := bbase (se 4 (by rfl) ⟨88041, by rfl⟩ : syracuseStep 939109 = 176083) (by norm_num)
theorem B2118757 : Blo 834351 2118757 := bbase (se 4 (by rfl) ⟨198633, by rfl⟩ : syracuseStep 2118757 = 397267) (by norm_num)
theorem B939145 : Blo 834351 939145 := bbase (se 2 (by rfl) ⟨352179, by rfl⟩ : syracuseStep 939145 = 704359) (by norm_num)
theorem B939181 : Blo 834351 939181 := bbase (se 3 (by rfl) ⟨176096, by rfl⟩ : syracuseStep 939181 = 352193) (by norm_num)
theorem B939217 : Blo 834351 939217 := bbase (se 2 (by rfl) ⟨352206, by rfl⟩ : syracuseStep 939217 = 704413) (by norm_num)
theorem B2118869 : Blo 834351 2118869 := bbase (se 7 (by rfl) ⟨24830, by rfl⟩ : syracuseStep 2118869 = 49661) (by norm_num)
theorem B939253 : Blo 834351 939253 := bbase (se 5 (by rfl) ⟨44027, by rfl⟩ : syracuseStep 939253 = 88055) (by norm_num)
theorem B939289 : Blo 834351 939289 := bbase (se 2 (by rfl) ⟨352233, by rfl⟩ : syracuseStep 939289 = 704467) (by norm_num)
theorem B1004833 : Blo 834351 1004833 := bbase (se 2 (by rfl) ⟨376812, by rfl⟩ : syracuseStep 1004833 = 753625) (by norm_num)
theorem B939325 : Blo 834351 939325 := bbase (se 3 (by rfl) ⟨176123, by rfl⟩ : syracuseStep 939325 = 352247) (by norm_num)
theorem B1692989 : Blo 834351 1692989 := bbase (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) (by norm_num)
theorem B939361 : Blo 834351 939361 := bbase (se 2 (by rfl) ⟨352260, by rfl⟩ : syracuseStep 939361 = 704521) (by norm_num)
theorem B939397 : Blo 834351 939397 := bbase (se 4 (by rfl) ⟨88068, by rfl⟩ : syracuseStep 939397 = 176137) (by norm_num)
theorem B2119061 : Blo 834351 2119061 := bbase (se 6 (by rfl) ⟨49665, by rfl⟩ : syracuseStep 2119061 = 99331) (by norm_num)
theorem B939433 : Blo 834351 939433 := bbase (se 2 (by rfl) ⟨352287, by rfl⟩ : syracuseStep 939433 = 704575) (by norm_num)
theorem B939469 : Blo 834351 939469 := bbase (se 3 (by rfl) ⟨176150, by rfl⟩ : syracuseStep 939469 = 352301) (by norm_num)
theorem B939505 : Blo 834351 939505 := bbase (se 2 (by rfl) ⟨352314, by rfl⟩ : syracuseStep 939505 = 704629) (by norm_num)
theorem B939541 : Blo 834351 939541 := bbase (se 6 (by rfl) ⟨22020, by rfl⟩ : syracuseStep 939541 = 44041) (by norm_num)
theorem B939577 : Blo 834351 939577 := bbase (se 2 (by rfl) ⟨352341, by rfl⟩ : syracuseStep 939577 = 704683) (by norm_num)
theorem B939613 : Blo 834351 939613 := bbase (se 3 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 939613 = 352355) (by norm_num)
theorem B939649 : Blo 834351 939649 := bbase (se 2 (by rfl) ⟨352368, by rfl⟩ : syracuseStep 939649 = 704737) (by norm_num)
theorem B1005217 : Blo 834351 1005217 := bbase (se 2 (by rfl) ⟨376956, by rfl⟩ : syracuseStep 1005217 = 753913) (by norm_num)
theorem B939685 : Blo 834351 939685 := bbase (se 4 (by rfl) ⟨88095, by rfl⟩ : syracuseStep 939685 = 176191) (by norm_num)
theorem B939721 : Blo 834351 939721 := bbase (se 2 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 939721 = 704791) (by norm_num)
theorem B939757 : Blo 834351 939757 := bbase (se 3 (by rfl) ⟨176204, by rfl⟩ : syracuseStep 939757 = 352409) (by norm_num)
theorem B2119405 : Blo 834351 2119405 := bbase (se 3 (by rfl) ⟨397388, by rfl⟩ : syracuseStep 2119405 = 794777) (by norm_num)
theorem B1070857 : Blo 834351 1070857 := bbase (se 2 (by rfl) ⟨401571, by rfl⟩ : syracuseStep 1070857 = 803143) (by norm_num)
theorem B939793 : Blo 834351 939793 := bbase (se 2 (by rfl) ⟨352422, by rfl⟩ : syracuseStep 939793 = 704845) (by norm_num)
theorem B2545429 : Blo 834351 2545429 := bbase (se 6 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 2545429 = 119317) (by norm_num)
theorem B4773653 : Blo 834351 4773653 := bbase (se 6 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 4773653 = 223765) (by norm_num)
theorem B939829 : Blo 834351 939829 := bbase (se 5 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 939829 = 88109) (by norm_num)
theorem B939865 : Blo 834351 939865 := bbase (se 2 (by rfl) ⟨352449, by rfl⟩ : syracuseStep 939865 = 704899) (by norm_num)
theorem B2119517 : Blo 834351 2119517 := bbase (se 3 (by rfl) ⟨397409, by rfl⟩ : syracuseStep 2119517 = 794819) (by norm_num)
theorem B2676581 : Blo 834351 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B939901 : Blo 834351 939901 := bbase (se 3 (by rfl) ⟨176231, by rfl⟩ : syracuseStep 939901 = 352463) (by norm_num)
theorem B4020101 : Blo 834351 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B939937 : Blo 834351 939937 := bbase (se 2 (by rfl) ⟨352476, by rfl⟩ : syracuseStep 939937 = 704953) (by norm_num)
theorem B939973 : Blo 834351 939973 := bbase (se 4 (by rfl) ⟨88122, by rfl⟩ : syracuseStep 939973 = 176245) (by norm_num)
theorem B3397573 : Blo 834351 3397573 := bbase (se 4 (by rfl) ⟨318522, by rfl⟩ : syracuseStep 3397573 = 637045) (by norm_num)
theorem B940009 : Blo 834351 940009 := bbase (se 2 (by rfl) ⟨352503, by rfl⟩ : syracuseStep 940009 = 705007) (by norm_num)
theorem B907241 : Blo 834351 907241 := bbase (se 2 (by rfl) ⟨340215, by rfl⟩ : syracuseStep 907241 = 680431) (by norm_num)
theorem B940045 : Blo 834351 940045 := bbase (se 3 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 940045 = 352517) (by norm_num)
theorem B2119709 : Blo 834351 2119709 := bbase (se 3 (by rfl) ⟨397445, by rfl⟩ : syracuseStep 2119709 = 794891) (by norm_num)
theorem B940081 : Blo 834351 940081 := bbase (se 2 (by rfl) ⟨352530, by rfl⟩ : syracuseStep 940081 = 705061) (by norm_num)
theorem B1071185 : Blo 834351 1071185 := bbase (se 2 (by rfl) ⟨401694, by rfl⟩ : syracuseStep 1071185 = 803389) (by norm_num)
theorem B3168341 : Blo 834351 3168341 := bbase (se 8 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 3168341 = 37129) (by norm_num)
theorem B940117 : Blo 834351 940117 := bbase (se 8 (by rfl) ⟨5508, by rfl⟩ : syracuseStep 940117 = 11017) (by norm_num)
theorem B940153 : Blo 834351 940153 := bbase (se 2 (by rfl) ⟨352557, by rfl⟩ : syracuseStep 940153 = 705115) (by norm_num)
theorem B940189 : Blo 834351 940189 := bbase (se 3 (by rfl) ⟨176285, by rfl⟩ : syracuseStep 940189 = 352571) (by norm_num)
theorem B940225 : Blo 834351 940225 := bbase (se 2 (by rfl) ⟨352584, by rfl⟩ : syracuseStep 940225 = 705169) (by norm_num)
theorem B940261 : Blo 834351 940261 := bbase (se 4 (by rfl) ⟨88149, by rfl⟩ : syracuseStep 940261 = 176299) (by norm_num)
theorem B940297 : Blo 834351 940297 := bbase (se 2 (by rfl) ⟨352611, by rfl⟩ : syracuseStep 940297 = 705223) (by norm_num)
theorem B940333 : Blo 834351 940333 := bbase (se 3 (by rfl) ⟨176312, by rfl⟩ : syracuseStep 940333 = 352625) (by norm_num)
theorem B940369 : Blo 834351 940369 := bbase (se 2 (by rfl) ⟨352638, by rfl⟩ : syracuseStep 940369 = 705277) (by norm_num)
theorem B3168629 : Blo 834351 3168629 := bbase (se 5 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 3168629 = 297059) (by norm_num)
theorem B940405 : Blo 834351 940405 := bbase (se 5 (by rfl) ⟨44081, by rfl⟩ : syracuseStep 940405 = 88163) (by norm_num)
theorem B2120053 : Blo 834351 2120053 := bbase (se 5 (by rfl) ⟨99377, by rfl⟩ : syracuseStep 2120053 = 198755) (by norm_num)
theorem B940441 : Blo 834351 940441 := bbase (se 2 (by rfl) ⟨352665, by rfl⟩ : syracuseStep 940441 = 705331) (by norm_num)
theorem B1694117 : Blo 834351 1694117 := bbase (se 4 (by rfl) ⟨158823, by rfl⟩ : syracuseStep 1694117 = 317647) (by norm_num)
theorem B940477 : Blo 834351 940477 := bbase (se 3 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 940477 = 352679) (by norm_num)
theorem B6019541 : Blo 834351 6019541 := bbase (se 7 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 6019541 = 141083) (by norm_num)
theorem B940513 : Blo 834351 940513 := bbase (se 2 (by rfl) ⟨352692, by rfl⟩ : syracuseStep 940513 = 705385) (by norm_num)
theorem B2120165 : Blo 834351 2120165 := bbase (se 4 (by rfl) ⟨198765, by rfl⟩ : syracuseStep 2120165 = 397531) (by norm_num)
theorem B940549 : Blo 834351 940549 := bbase (se 4 (by rfl) ⟨88176, by rfl⟩ : syracuseStep 940549 = 176353) (by norm_num)
theorem B4512277 : Blo 834351 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B940585 : Blo 834351 940585 := bbase (se 2 (by rfl) ⟨352719, by rfl⟩ : syracuseStep 940585 = 705439) (by norm_num)
theorem B1006121 : Blo 834351 1006121 := bbase (se 2 (by rfl) ⟨377295, by rfl⟩ : syracuseStep 1006121 = 754591) (by norm_num)
theorem B940621 : Blo 834351 940621 := bbase (se 3 (by rfl) ⟨176366, by rfl⟩ : syracuseStep 940621 = 352733) (by norm_num)
theorem B940657 : Blo 834351 940657 := bbase (se 2 (by rfl) ⟨352746, by rfl⟩ : syracuseStep 940657 = 705493) (by norm_num)
theorem B940693 : Blo 834351 940693 := bbase (se 6 (by rfl) ⟨22047, by rfl⟩ : syracuseStep 940693 = 44095) (by norm_num)
theorem B2120357 : Blo 834351 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B940729 : Blo 834351 940729 := bbase (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) (by norm_num)
theorem B940765 : Blo 834351 940765 := bbase (se 3 (by rfl) ⟨176393, by rfl⟩ : syracuseStep 940765 = 352787) (by norm_num)
theorem B940801 : Blo 834351 940801 := bbase (se 2 (by rfl) ⟨352800, by rfl⟩ : syracuseStep 940801 = 705601) (by norm_num)
theorem B940837 : Blo 834351 940837 := bbase (se 4 (by rfl) ⟨88203, by rfl⟩ : syracuseStep 940837 = 176407) (by norm_num)
theorem B1006381 : Blo 834351 1006381 := bbase (se 3 (by rfl) ⟨188696, by rfl⟩ : syracuseStep 1006381 = 377393) (by norm_num)
theorem B940873 : Blo 834351 940873 := bbase (se 2 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 940873 = 705655) (by norm_num)
theorem B940909 : Blo 834351 940909 := bbase (se 3 (by rfl) ⟨176420, by rfl⟩ : syracuseStep 940909 = 352841) (by norm_num)
theorem B940945 : Blo 834351 940945 := bbase (se 2 (by rfl) ⟨352854, by rfl⟩ : syracuseStep 940945 = 705709) (by norm_num)
theorem B940981 : Blo 834351 940981 := bbase (se 5 (by rfl) ⟨44108, by rfl⟩ : syracuseStep 940981 = 88217) (by norm_num)
theorem B941017 : Blo 834351 941017 := bbase (se 2 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 941017 = 705763) (by norm_num)
theorem B1006573 : Blo 834351 1006573 := bbase (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) (by norm_num)
theorem B941053 : Blo 834351 941053 := bbase (se 3 (by rfl) ⟨176447, by rfl⟩ : syracuseStep 941053 = 352895) (by norm_num)
theorem B2120701 : Blo 834351 2120701 := bbase (se 3 (by rfl) ⟨397631, by rfl⟩ : syracuseStep 2120701 = 795263) (by norm_num)
theorem B1006597 : Blo 834351 1006597 := bbase (se 4 (by rfl) ⟨94368, by rfl⟩ : syracuseStep 1006597 = 188737) (by norm_num)
theorem B1006601 : Blo 834351 1006601 := bbase (se 2 (by rfl) ⟨377475, by rfl⟩ : syracuseStep 1006601 = 754951) (by norm_num)
theorem B941089 : Blo 834351 941089 := bbase (se 2 (by rfl) ⟨352908, by rfl⟩ : syracuseStep 941089 = 705817) (by norm_num)
theorem B941125 : Blo 834351 941125 := bbase (se 4 (by rfl) ⟨88230, by rfl⟩ : syracuseStep 941125 = 176461) (by norm_num)
theorem B941161 : Blo 834351 941161 := bbase (se 2 (by rfl) ⟨352935, by rfl⟩ : syracuseStep 941161 = 705871) (by norm_num)
theorem B2120813 : Blo 834351 2120813 := bbase (se 3 (by rfl) ⟨397652, by rfl⟩ : syracuseStep 2120813 = 795305) (by norm_num)
theorem B2382965 : Blo 834351 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B3398773 : Blo 834351 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B941197 : Blo 834351 941197 := bbase (se 3 (by rfl) ⟨176474, by rfl⟩ : syracuseStep 941197 = 352949) (by norm_num)
theorem B3267749 : Blo 834351 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B941233 : Blo 834351 941233 := bbase (se 2 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 941233 = 705925) (by norm_num)
theorem B2579653 : Blo 834351 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B941269 : Blo 834351 941269 := bbase (se 7 (by rfl) ⟨11030, by rfl⟩ : syracuseStep 941269 = 22061) (by norm_num)
theorem B941305 : Blo 834351 941305 := bbase (se 2 (by rfl) ⟨352989, by rfl⟩ : syracuseStep 941305 = 705979) (by norm_num)
theorem B941341 : Blo 834351 941341 := bbase (se 3 (by rfl) ⟨176501, by rfl⟩ : syracuseStep 941341 = 353003) (by norm_num)
theorem B2121005 : Blo 834351 2121005 := bbase (se 3 (by rfl) ⟨397688, by rfl⟩ : syracuseStep 2121005 = 795377) (by norm_num)
theorem B941377 : Blo 834351 941377 := bbase (se 2 (by rfl) ⟨353016, by rfl⟩ : syracuseStep 941377 = 706033) (by norm_num)
theorem B13557077 : Blo 834351 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B941413 : Blo 834351 941413 := bbase (se 4 (by rfl) ⟨88257, by rfl⟩ : syracuseStep 941413 = 176515) (by norm_num)
theorem B941449 : Blo 834351 941449 := bbase (se 2 (by rfl) ⟨353043, by rfl⟩ : syracuseStep 941449 = 706087) (by norm_num)
theorem B941485 : Blo 834351 941485 := bbase (se 3 (by rfl) ⟨176528, by rfl⟩ : syracuseStep 941485 = 353057) (by norm_num)
theorem B941521 : Blo 834351 941521 := bbase (se 2 (by rfl) ⟨353070, by rfl⟩ : syracuseStep 941521 = 706141) (by norm_num)
theorem B941557 : Blo 834351 941557 := bbase (se 5 (by rfl) ⟨44135, by rfl⟩ : syracuseStep 941557 = 88271) (by norm_num)
theorem B1007101 : Blo 834351 1007101 := bbase (se 3 (by rfl) ⟨188831, by rfl⟩ : syracuseStep 1007101 = 377663) (by norm_num)
theorem B3169813 : Blo 834351 3169813 := bbase (se 6 (by rfl) ⟨74292, by rfl⟩ : syracuseStep 3169813 = 148585) (by norm_num)
theorem B941593 : Blo 834351 941593 := bbase (se 2 (by rfl) ⟨353097, by rfl⟩ : syracuseStep 941593 = 706195) (by norm_num)
theorem B941629 : Blo 834351 941629 := bbase (se 3 (by rfl) ⟨176555, by rfl⟩ : syracuseStep 941629 = 353111) (by norm_num)
theorem B6020693 : Blo 834351 6020693 := bbase (se 8 (by rfl) ⟨35277, by rfl⟩ : syracuseStep 6020693 = 70555) (by norm_num)
theorem B941665 : Blo 834351 941665 := bbase (se 2 (by rfl) ⟨353124, by rfl⟩ : syracuseStep 941665 = 706249) (by norm_num)
theorem B941701 : Blo 834351 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B2121349 : Blo 834351 2121349 := bbase (se 4 (by rfl) ⟨198876, by rfl⟩ : syracuseStep 2121349 = 397753) (by norm_num)
theorem B941737 : Blo 834351 941737 := bbase (se 2 (by rfl) ⟨353151, by rfl⟩ : syracuseStep 941737 = 706303) (by norm_num)
theorem B2678453 : Blo 834351 2678453 := bbase (se 5 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 2678453 = 251105) (by norm_num)
theorem B941773 : Blo 834351 941773 := bbase (se 3 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 941773 = 353165) (by norm_num)
theorem B941809 : Blo 834351 941809 := bbase (se 2 (by rfl) ⟨353178, by rfl⟩ : syracuseStep 941809 = 706357) (by norm_num)
theorem B2121461 : Blo 834351 2121461 := bbase (se 5 (by rfl) ⟨99443, by rfl⟩ : syracuseStep 2121461 = 198887) (by norm_num)
theorem B941845 : Blo 834351 941845 := bbase (se 6 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 941845 = 44149) (by norm_num)
theorem B1072921 : Blo 834351 1072921 := bbase (se 2 (by rfl) ⟨402345, by rfl⟩ : syracuseStep 1072921 = 804691) (by norm_num)
theorem B941881 : Blo 834351 941881 := bbase (se 2 (by rfl) ⟨353205, by rfl⟩ : syracuseStep 941881 = 706411) (by norm_num)
theorem B3170117 : Blo 834351 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B941917 : Blo 834351 941917 := bbase (se 3 (by rfl) ⟨176609, by rfl⟩ : syracuseStep 941917 = 353219) (by norm_num)
theorem B3628901 : Blo 834351 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B941953 : Blo 834351 941953 := bbase (se 2 (by rfl) ⟨353232, by rfl⟩ : syracuseStep 941953 = 706465) (by norm_num)
theorem B941989 : Blo 834351 941989 := bbase (se 4 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 941989 = 176623) (by norm_num)
theorem B2121653 : Blo 834351 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B942025 : Blo 834351 942025 := bbase (se 2 (by rfl) ⟨353259, by rfl⟩ : syracuseStep 942025 = 706519) (by norm_num)
theorem B942061 : Blo 834351 942061 := bbase (se 3 (by rfl) ⟨176636, by rfl⟩ : syracuseStep 942061 = 353273) (by norm_num)
theorem B942097 : Blo 834351 942097 := bbase (se 2 (by rfl) ⟨353286, by rfl⟩ : syracuseStep 942097 = 706573) (by norm_num)
theorem B942133 : Blo 834351 942133 := bbase (se 5 (by rfl) ⟨44162, by rfl⟩ : syracuseStep 942133 = 88325) (by norm_num)
theorem B942169 : Blo 834351 942169 := bbase (se 2 (by rfl) ⟨353313, by rfl⟩ : syracuseStep 942169 = 706627) (by norm_num)
theorem B942205 : Blo 834351 942205 := bbase (se 3 (by rfl) ⟨176663, by rfl⟩ : syracuseStep 942205 = 353327) (by norm_num)
theorem B942241 : Blo 834351 942241 := bbase (se 2 (by rfl) ⟨353340, by rfl⟩ : syracuseStep 942241 = 706681) (by norm_num)
theorem B942277 : Blo 834351 942277 := bbase (se 4 (by rfl) ⟨88338, by rfl⟩ : syracuseStep 942277 = 176677) (by norm_num)
theorem B942313 : Blo 834351 942313 := bbase (se 2 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 942313 = 706735) (by norm_num)
theorem B1073413 : Blo 834351 1073413 := bbase (se 4 (by rfl) ⟨100632, by rfl⟩ : syracuseStep 1073413 = 201265) (by norm_num)
theorem B942349 : Blo 834351 942349 := bbase (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) (by norm_num)
theorem B2121997 : Blo 834351 2121997 := bbase (se 3 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 2121997 = 795749) (by norm_num)
theorem B2384149 : Blo 834351 2384149 := bbase (se 6 (by rfl) ⟨55878, by rfl⟩ : syracuseStep 2384149 = 111757) (by norm_num)
theorem B942385 : Blo 834351 942385 := bbase (se 2 (by rfl) ⟨353394, by rfl⟩ : syracuseStep 942385 = 706789) (by norm_num)
theorem B942421 : Blo 834351 942421 := bbase (se 10 (by rfl) ⟨1380, by rfl⟩ : syracuseStep 942421 = 2761) (by norm_num)
theorem B942457 : Blo 834351 942457 := bbase (se 2 (by rfl) ⟨353421, by rfl⟩ : syracuseStep 942457 = 706843) (by norm_num)
theorem B2318725 : Blo 834351 2318725 := bbase (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) (by norm_num)
theorem B942493 : Blo 834351 942493 := bbase (se 3 (by rfl) ⟨176717, by rfl⟩ : syracuseStep 942493 = 353435) (by norm_num)
theorem B2384309 : Blo 834351 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B942529 : Blo 834351 942529 := bbase (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) (by norm_num)
theorem B942565 : Blo 834351 942565 := bbase (se 4 (by rfl) ⟨88365, by rfl⟩ : syracuseStep 942565 = 176731) (by norm_num)
theorem B942601 : Blo 834351 942601 := bbase (se 2 (by rfl) ⟨353475, by rfl⟩ : syracuseStep 942601 = 706951) (by norm_num)
theorem B942637 : Blo 834351 942637 := bbase (se 3 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 942637 = 353489) (by norm_num)
theorem B2548277 : Blo 834351 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B942673 : Blo 834351 942673 := bbase (se 2 (by rfl) ⟨353502, by rfl⟩ : syracuseStep 942673 = 707005) (by norm_num)
theorem B942709 : Blo 834351 942709 := bbase (se 5 (by rfl) ⟨44189, by rfl⟩ : syracuseStep 942709 = 88379) (by norm_num)
theorem B942745 : Blo 834351 942745 := bbase (se 2 (by rfl) ⟨353529, by rfl⟩ : syracuseStep 942745 = 707059) (by norm_num)
theorem B2384549 : Blo 834351 2384549 := bbase (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) (by norm_num)
theorem B942781 : Blo 834351 942781 := bbase (se 3 (by rfl) ⟨176771, by rfl⟩ : syracuseStep 942781 = 353543) (by norm_num)
theorem B942817 : Blo 834351 942817 := bbase (se 2 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 942817 = 707113) (by norm_num)
theorem B942853 : Blo 834351 942853 := bbase (se 4 (by rfl) ⟨88392, by rfl⟩ : syracuseStep 942853 = 176785) (by norm_num)
theorem B6349589 : Blo 834351 6349589 := bbase (se 6 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 6349589 = 297637) (by norm_num)
theorem B942889 : Blo 834351 942889 := bbase (se 2 (by rfl) ⟨353583, by rfl⟩ : syracuseStep 942889 = 707167) (by norm_num)
theorem B942925 : Blo 834351 942925 := bbase (se 3 (by rfl) ⟨176798, by rfl⟩ : syracuseStep 942925 = 353597) (by norm_num)
theorem B2384741 : Blo 834351 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B942961 : Blo 834351 942961 := bbase (se 2 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 942961 = 707221) (by norm_num)
theorem B942997 : Blo 834351 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B943033 : Blo 834351 943033 := bbase (se 2 (by rfl) ⟨353637, by rfl⟩ : syracuseStep 943033 = 707275) (by norm_num)
theorem B943069 : Blo 834351 943069 := bbase (se 3 (by rfl) ⟨176825, by rfl⟩ : syracuseStep 943069 = 353651) (by norm_num)
theorem B943105 : Blo 834351 943105 := bbase (se 2 (by rfl) ⟨353664, by rfl⟩ : syracuseStep 943105 = 707329) (by norm_num)
theorem B943141 : Blo 834351 943141 := bbase (se 4 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 943141 = 176839) (by norm_num)
theorem B10183765 : Blo 834351 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B1270909 : Blo 834351 1270909 := bbase (se 3 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 1270909 = 476591) (by norm_num)
theorem B3433637 : Blo 834351 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B1205453 : Blo 834351 1205453 := bbase (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) (by norm_num)
theorem B1860989 : Blo 834351 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B3007925 : Blo 834351 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B2418101 : Blo 834351 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B2942453 : Blo 834351 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B3860021 : Blo 834351 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B1074757 : Blo 834351 1074757 := bbase (se 4 (by rfl) ⟨100758, by rfl⟩ : syracuseStep 1074757 = 201517) (by norm_num)
theorem B3565205 : Blo 834351 3565205 := bbase (se 6 (by rfl) ⟨83559, by rfl⟩ : syracuseStep 3565205 = 167119) (by norm_num)
theorem B3434293 : Blo 834351 3434293 := bbase (se 5 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 3434293 = 321965) (by norm_num)
theorem B1271621 : Blo 834351 1271621 := bbase (se 4 (by rfl) ⟨119214, by rfl⟩ : syracuseStep 1271621 = 238429) (by norm_num)
theorem B2385733 : Blo 834351 2385733 := bbase (se 4 (by rfl) ⟨223662, by rfl⟩ : syracuseStep 2385733 = 447325) (by norm_num)
theorem B3172229 : Blo 834351 3172229 := bbase (se 4 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 3172229 = 594793) (by norm_num)
theorem B1697813 : Blo 834351 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B3172517 : Blo 834351 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B1337573 : Blo 834351 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1272077 : Blo 834351 1272077 := bbase (se 3 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 1272077 = 477029) (by norm_num)
theorem B2681221 : Blo 834351 2681221 := bbase (se 4 (by rfl) ⟨251364, by rfl⟩ : syracuseStep 2681221 = 502729) (by norm_num)
theorem B14281109 : Blo 834351 14281109 := bbase (se 6 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 14281109 = 669427) (by norm_num)
theorem B1272277 : Blo 834351 1272277 := bbase (se 7 (by rfl) ⟨14909, by rfl⟩ : syracuseStep 1272277 = 29819) (by norm_num)
theorem B3566213 : Blo 834351 3566213 := bbase (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) (by norm_num)
theorem B1206925 : Blo 834351 1206925 := bbase (se 3 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 1206925 = 452597) (by norm_num)
theorem B1338029 : Blo 834351 1338029 := bbase (se 3 (by rfl) ⟨250880, by rfl⟩ : syracuseStep 1338029 = 501761) (by norm_num)
theorem B2386837 : Blo 834351 2386837 := bbase (se 6 (by rfl) ⟨55941, by rfl⟩ : syracuseStep 2386837 = 111883) (by norm_num)
theorem B2288741 : Blo 834351 2288741 := bbase (se 4 (by rfl) ⟨214569, by rfl⟩ : syracuseStep 2288741 = 429139) (by norm_num)
theorem B5368949 : Blo 834351 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B1698965 : Blo 834351 1698965 := bbase (se 6 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 1698965 = 79639) (by norm_num)
theorem B3173701 : Blo 834351 3173701 := bbase (se 4 (by rfl) ⟨297534, by rfl⟩ : syracuseStep 3173701 = 595069) (by norm_num)
theorem B847309 : Blo 834351 847309 := bbase (se 3 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 847309 = 317741) (by norm_num)
theorem B3174005 : Blo 834351 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B1339021 : Blo 834351 1339021 := bbase (se 3 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 1339021 = 502133) (by norm_num)
theorem B1699501 : Blo 834351 1699501 := bbase (se 3 (by rfl) ⟨318656, by rfl⟩ : syracuseStep 1699501 = 637313) (by norm_num)
theorem B6123413 : Blo 834351 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B847837 : Blo 834351 847837 := bbase (se 3 (by rfl) ⟨158969, by rfl⟩ : syracuseStep 847837 = 317939) (by norm_num)
theorem B1339669 : Blo 834351 1339669 := bbase (se 6 (by rfl) ⟨31398, by rfl⟩ : syracuseStep 1339669 = 62797) (by norm_num)
theorem B3567989 : Blo 834351 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B3011269 : Blo 834351 3011269 := bbase (se 4 (by rfl) ⟨282306, by rfl⟩ : syracuseStep 3011269 = 564613) (by norm_num)
theorem B1504021 : Blo 834351 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B4027157 : Blo 834351 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B848777 : Blo 834351 848777 := bbase (se 2 (by rfl) ⟨318291, by rfl⟩ : syracuseStep 848777 = 636583) (by norm_num)
theorem B4224149 : Blo 834351 4224149 := bbase (se 6 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 4224149 = 198007) (by norm_num)
theorem B1340597 : Blo 834351 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B2684117 : Blo 834351 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B1504597 : Blo 834351 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B1341053 : Blo 834351 1341053 := bbase (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) (by norm_num)
theorem B3176117 : Blo 834351 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B849709 : Blo 834351 849709 := bbase (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) (by norm_num)
theorem B3176405 : Blo 834351 3176405 := bbase (se 7 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 3176405 = 74447) (by norm_num)
theorem B1505405 : Blo 834351 1505405 := bbase (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) (by norm_num)
theorem B1702013 : Blo 834351 1702013 := bbase (se 3 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 1702013 = 638255) (by norm_num)
theorem B1145029 : Blo 834351 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B2816261 : Blo 834351 2816261 := bbase (se 4 (by rfl) ⟨264024, by rfl⟩ : syracuseStep 2816261 = 528049) (by norm_num)
theorem B4225445 : Blo 834351 4225445 := bbase (se 4 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 4225445 = 792271) (by norm_num)
theorem B1505837 : Blo 834351 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B2816693 : Blo 834351 2816693 := bbase (se 5 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 2816693 = 264065) (by norm_num)
theorem B1505981 : Blo 834351 1505981 := bbase (se 3 (by rfl) ⟨282371, by rfl⟩ : syracuseStep 1505981 = 564743) (by norm_num)
theorem B8583893 : Blo 834351 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B1506205 : Blo 834351 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B1407989 : Blo 834351 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B1342469 : Blo 834351 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B2817125 : Blo 834351 2817125 := bbase (se 4 (by rfl) ⟨264105, by rfl⟩ : syracuseStep 2817125 = 528211) (by norm_num)
theorem B1408117 : Blo 834351 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B3177589 : Blo 834351 3177589 := bbase (se 5 (by rfl) ⟨148949, by rfl⟩ : syracuseStep 3177589 = 297899) (by norm_num)
theorem B1408205 : Blo 834351 1408205 := bbase (se 3 (by rfl) ⟨264038, by rfl⟩ : syracuseStep 1408205 = 528077) (by norm_num)
theorem B1342693 : Blo 834351 1342693 := bbase (se 4 (by rfl) ⟨125877, by rfl⟩ : syracuseStep 1342693 = 251755) (by norm_num)
theorem B1506557 : Blo 834351 1506557 := bbase (se 3 (by rfl) ⟨282479, by rfl⟩ : syracuseStep 1506557 = 564959) (by norm_num)
theorem B1408333 : Blo 834351 1408333 := bbase (se 3 (by rfl) ⟨264062, by rfl⟩ : syracuseStep 1408333 = 528125) (by norm_num)
theorem B3177893 : Blo 834351 3177893 := bbase (se 4 (by rfl) ⟨297927, by rfl⟩ : syracuseStep 3177893 = 595855) (by norm_num)
theorem B1408421 : Blo 834351 1408421 := bbase (se 4 (by rfl) ⟨132039, by rfl⟩ : syracuseStep 1408421 = 264079) (by norm_num)
theorem B2817557 : Blo 834351 2817557 := bbase (se 6 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 2817557 = 132073) (by norm_num)
theorem B1408549 : Blo 834351 1408549 := bbase (se 4 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 1408549 = 264103) (by norm_num)
theorem B1408637 : Blo 834351 1408637 := bbase (se 3 (by rfl) ⟨264119, by rfl⟩ : syracuseStep 1408637 = 528239) (by norm_num)
theorem B4226741 : Blo 834351 4226741 := bbase (se 5 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 4226741 = 396257) (by norm_num)
theorem B1408765 : Blo 834351 1408765 := bbase (se 3 (by rfl) ⟨264143, by rfl⟩ : syracuseStep 1408765 = 528287) (by norm_num)
theorem B1408853 : Blo 834351 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B2817989 : Blo 834351 2817989 := bbase (se 4 (by rfl) ⟨264186, by rfl⟩ : syracuseStep 2817989 = 528373) (by norm_num)
theorem B1408981 : Blo 834351 1408981 := bbase (se 7 (by rfl) ⟨16511, by rfl⟩ : syracuseStep 1408981 = 33023) (by norm_num)
theorem B3440675 : Blo 834351 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B2818097 : Blo 834351 2818097 := bstep (se 2 (by rfl) ⟨1056786, by rfl⟩ : syracuseStep 2818097 = 2113573) B2113573
theorem B1409089 : Blo 834351 1409089 := bstep (se 2 (by rfl) ⟨528408, by rfl⟩ : syracuseStep 1409089 = 1056817) B1056817
theorem B1409123 : Blo 834351 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B4292785 : Blo 834351 4292785 := bstep (se 2 (by rfl) ⟨1609794, by rfl⟩ : syracuseStep 4292785 = 3219589) B3219589
theorem B1409251 : Blo 834351 1409251 := bstep (se 1 (by rfl) ⟨1056938, by rfl⟩ : syracuseStep 1409251 = 2113877) B2113877
theorem B1409393 : Blo 834351 1409393 := bstep (se 2 (by rfl) ⟨528522, by rfl⟩ : syracuseStep 1409393 = 1057045) B1057045
theorem B3178865 : Blo 834351 3178865 := bstep (se 2 (by rfl) ⟨1192074, by rfl⟩ : syracuseStep 3178865 = 2384149) B2384149
theorem B1409521 : Blo 834351 1409521 := bstep (se 2 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 1409521 = 1057141) B1057141
theorem B1409555 : Blo 834351 1409555 := bstep (se 1 (by rfl) ⟨1057166, by rfl⟩ : syracuseStep 1409555 = 2114333) B2114333
theorem B2818637 : Blo 834351 2818637 := bstep (se 3 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 2818637 = 1056989) B1056989
theorem B2818691 : Blo 834351 2818691 := bstep (se 1 (by rfl) ⟨2114018, by rfl⟩ : syracuseStep 2818691 = 4228037) B4228037
theorem B1409683 : Blo 834351 1409683 := bstep (se 1 (by rfl) ⟨1057262, by rfl⟩ : syracuseStep 1409683 = 2114525) B2114525
theorem B1409825 : Blo 834351 1409825 := bstep (se 2 (by rfl) ⟨528684, by rfl⟩ : syracuseStep 1409825 = 1057369) B1057369
theorem B4227875 : Blo 834351 4227875 := bstep (se 1 (by rfl) ⟨3170906, by rfl⟩ : syracuseStep 4227875 = 6341813) B6341813
theorem B2818961 : Blo 834351 2818961 := bstep (se 2 (by rfl) ⟨1057110, by rfl⟩ : syracuseStep 2818961 = 2114221) B2114221
theorem B1409953 : Blo 834351 1409953 := bstep (se 2 (by rfl) ⟨528732, by rfl⟩ : syracuseStep 1409953 = 1057465) B1057465
theorem B2294701 : Blo 834351 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B1409987 : Blo 834351 1409987 := bstep (se 1 (by rfl) ⟨1057490, by rfl⟩ : syracuseStep 1409987 = 2114981) B2114981
theorem B3179533 : Blo 834351 3179533 := bstep (se 3 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 3179533 = 1192325) B1192325
theorem B1410115 : Blo 834351 1410115 := bstep (se 1 (by rfl) ⟨1057586, by rfl⟩ : syracuseStep 1410115 = 2115173) B2115173
theorem B1410257 : Blo 834351 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B1410385 : Blo 834351 1410385 := bstep (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) B1057789
theorem B1410419 : Blo 834351 1410419 := bstep (se 1 (by rfl) ⟨1057814, by rfl⟩ : syracuseStep 1410419 = 2115629) B2115629
theorem B2819501 : Blo 834351 2819501 := bstep (se 3 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 2819501 = 1057313) B1057313
theorem B2819555 : Blo 834351 2819555 := bstep (se 1 (by rfl) ⟨2114666, by rfl⟩ : syracuseStep 2819555 = 4229333) B4229333
theorem B1410547 : Blo 834351 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B15238709 : Blo 834351 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B20383285 : Blo 834351 20383285 := bstep (se 5 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 20383285 = 1910933) B1910933
theorem B4228685 : Blo 834351 4228685 := bstep (se 3 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 4228685 = 1585757) B1585757
theorem B4523633 : Blo 834351 4523633 := bstep (se 2 (by rfl) ⟨1696362, by rfl⟩ : syracuseStep 4523633 = 3392725) B3392725
theorem B1410689 : Blo 834351 1410689 := bstep (se 2 (by rfl) ⟨529008, by rfl⟩ : syracuseStep 1410689 = 1058017) B1058017
theorem B2262691 : Blo 834351 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B2819825 : Blo 834351 2819825 := bstep (se 2 (by rfl) ⟨1057434, by rfl⟩ : syracuseStep 2819825 = 2114869) B2114869
theorem B1410817 : Blo 834351 1410817 := bstep (se 2 (by rfl) ⟨529056, by rfl⟩ : syracuseStep 1410817 = 1058113) B1058113
theorem B1410851 : Blo 834351 1410851 := bstep (se 1 (by rfl) ⟨1058138, by rfl⟩ : syracuseStep 1410851 = 2116277) B2116277
theorem B3180323 : Blo 834351 3180323 := bstep (se 1 (by rfl) ⟨2385242, by rfl⟩ : syracuseStep 3180323 = 4770485) B4770485
theorem B1410979 : Blo 834351 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B1509283 : Blo 834351 1509283 := bstep (se 1 (by rfl) ⟨1131962, by rfl⟩ : syracuseStep 1509283 = 2263925) B2263925
theorem B1411121 : Blo 834351 1411121 := bstep (se 2 (by rfl) ⟨529170, by rfl⟩ : syracuseStep 1411121 = 1058341) B1058341
theorem B1411249 : Blo 834351 1411249 := bstep (se 2 (by rfl) ⟨529218, by rfl⟩ : syracuseStep 1411249 = 1058437) B1058437
theorem B1411283 : Blo 834351 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B2820365 : Blo 834351 2820365 := bstep (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) B1057637
theorem B6359309 : Blo 834351 6359309 := bstep (se 3 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 6359309 = 2384741) B2384741
theorem B2820419 : Blo 834351 2820419 := bstep (se 1 (by rfl) ⟨2115314, by rfl⟩ : syracuseStep 2820419 = 4230629) B4230629
theorem B1411411 : Blo 834351 1411411 := bstep (se 1 (by rfl) ⟨1058558, by rfl⟩ : syracuseStep 1411411 = 2117117) B2117117
theorem B2263405 : Blo 834351 2263405 := bstep (se 3 (by rfl) ⟨424388, by rfl⟩ : syracuseStep 2263405 = 848777) B848777
theorem B2263427 : Blo 834351 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B4065677 : Blo 834351 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B3180977 : Blo 834351 3180977 := bstep (se 2 (by rfl) ⟨1192866, by rfl⟩ : syracuseStep 3180977 = 2385733) B2385733
theorem B6785477 : Blo 834351 6785477 := bstep (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) B1272277
theorem B1411553 : Blo 834351 1411553 := bstep (se 2 (by rfl) ⟨529332, by rfl⟩ : syracuseStep 1411553 = 1058665) B1058665
theorem B21760483 : Blo 834351 21760483 := bstep (se 1 (by rfl) ⟨16320362, by rfl⟩ : syracuseStep 21760483 = 32640725) B32640725
theorem B8129009 : Blo 834351 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B2820689 : Blo 834351 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B1411681 : Blo 834351 1411681 := bstep (se 2 (by rfl) ⟨529380, by rfl⟩ : syracuseStep 1411681 = 1058761) B1058761
theorem B3213923 : Blo 834351 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B1411715 : Blo 834351 1411715 := bstep (se 1 (by rfl) ⟨1058786, by rfl⟩ : syracuseStep 1411715 = 2117573) B2117573
theorem B1411843 : Blo 834351 1411843 := bstep (se 1 (by rfl) ⟨1058882, by rfl⟩ : syracuseStep 1411843 = 2117765) B2117765
theorem B4295501 : Blo 834351 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B1411985 : Blo 834351 1411985 := bstep (se 2 (by rfl) ⟨529494, by rfl⟩ : syracuseStep 1411985 = 1058989) B1058989
theorem B1510321 : Blo 834351 1510321 := bstep (se 2 (by rfl) ⟨566370, by rfl⟩ : syracuseStep 1510321 = 1132741) B1132741
theorem B1412113 : Blo 834351 1412113 := bstep (se 2 (by rfl) ⟨529542, by rfl⟩ : syracuseStep 1412113 = 1059085) B1059085
theorem B1412147 : Blo 834351 1412147 := bstep (se 1 (by rfl) ⟨1059110, by rfl⟩ : syracuseStep 1412147 = 2118221) B2118221
theorem B2821229 : Blo 834351 2821229 := bstep (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) B1057961
theorem B3574925 : Blo 834351 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B2821283 : Blo 834351 2821283 := bstep (se 1 (by rfl) ⟨2115962, by rfl⟩ : syracuseStep 2821283 = 4231925) B4231925
theorem B3574961 : Blo 834351 3574961 := bstep (se 2 (by rfl) ⟨1340610, by rfl⟩ : syracuseStep 3574961 = 2681221) B2681221
theorem B1412275 : Blo 834351 1412275 := bstep (se 1 (by rfl) ⟨1059206, by rfl⟩ : syracuseStep 1412275 = 2118413) B2118413
theorem B3214541 : Blo 834351 3214541 := bstep (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) B1205453
theorem B1412417 : Blo 834351 1412417 := bstep (se 2 (by rfl) ⟨529656, by rfl⟩ : syracuseStep 1412417 = 1059313) B1059313
theorem B2821553 : Blo 834351 2821553 := bstep (se 2 (by rfl) ⟨1058082, by rfl⟩ : syracuseStep 2821553 = 2116165) B2116165
theorem B1412545 : Blo 834351 1412545 := bstep (se 2 (by rfl) ⟨529704, by rfl⟩ : syracuseStep 1412545 = 1059409) B1059409
theorem B1412579 : Blo 834351 1412579 := bstep (se 1 (by rfl) ⟨1059434, by rfl⟩ : syracuseStep 1412579 = 2118869) B2118869
theorem B4525553 : Blo 834351 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B1412707 : Blo 834351 1412707 := bstep (se 1 (by rfl) ⟨1059530, by rfl⟩ : syracuseStep 1412707 = 2119061) B2119061
theorem B1904323 : Blo 834351 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B4296397 : Blo 834351 4296397 := bstep (se 3 (by rfl) ⟨805574, by rfl⟩ : syracuseStep 4296397 = 1611149) B1611149
theorem B1412849 : Blo 834351 1412849 := bstep (se 2 (by rfl) ⟨529818, by rfl⟩ : syracuseStep 1412849 = 1059637) B1059637
theorem B1904401 : Blo 834351 1904401 := bstep (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) B1428301
theorem B3182435 : Blo 834351 3182435 := bstep (se 1 (by rfl) ⟨2386826, by rfl⟩ : syracuseStep 3182435 = 4773653) B4773653
theorem B1412977 : Blo 834351 1412977 := bstep (se 2 (by rfl) ⟨529866, by rfl⟩ : syracuseStep 1412977 = 1059733) B1059733
theorem B3182449 : Blo 834351 3182449 := bstep (se 2 (by rfl) ⟨1193418, by rfl⟩ : syracuseStep 3182449 = 2386837) B2386837
theorem B1413011 : Blo 834351 1413011 := bstep (se 1 (by rfl) ⟨1059758, by rfl⟩ : syracuseStep 1413011 = 2119517) B2119517
theorem B2822093 : Blo 834351 2822093 := bstep (se 3 (by rfl) ⟨529142, by rfl⟩ : syracuseStep 2822093 = 1058285) B1058285
theorem B6033379 : Blo 834351 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B2822147 : Blo 834351 2822147 := bstep (se 1 (by rfl) ⟨2116610, by rfl⟩ : syracuseStep 2822147 = 4233221) B4233221
theorem B1413139 : Blo 834351 1413139 := bstep (se 1 (by rfl) ⟨1059854, by rfl⟩ : syracuseStep 1413139 = 2119709) B2119709
theorem B10293389 : Blo 834351 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B1413281 : Blo 834351 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B2822417 : Blo 834351 2822417 := bstep (se 2 (by rfl) ⟨1058406, by rfl⟩ : syracuseStep 2822417 = 2116813) B2116813
theorem B1413409 : Blo 834351 1413409 := bstep (se 2 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 1413409 = 1060057) B1060057
theorem B1413443 : Blo 834351 1413443 := bstep (se 1 (by rfl) ⟨1060082, by rfl⟩ : syracuseStep 1413443 = 2120165) B2120165
theorem B4231601 : Blo 834351 4231601 := bstep (se 2 (by rfl) ⟨1586850, by rfl⟩ : syracuseStep 4231601 = 3173701) B3173701
theorem B1413571 : Blo 834351 1413571 := bstep (se 1 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 1413571 = 2120357) B2120357
theorem B2036305 : Blo 834351 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B1413713 : Blo 834351 1413713 := bstep (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) B1060285
theorem B1413841 : Blo 834351 1413841 := bstep (se 2 (by rfl) ⟨530190, by rfl⟩ : syracuseStep 1413841 = 1060381) B1060381
theorem B1413875 : Blo 834351 1413875 := bstep (se 1 (by rfl) ⟨1060406, by rfl⟩ : syracuseStep 1413875 = 2120813) B2120813
theorem B2822957 : Blo 834351 2822957 := bstep (se 3 (by rfl) ⟨529304, by rfl⟩ : syracuseStep 2822957 = 1058609) B1058609
theorem B8033093 : Blo 834351 8033093 := bstep (se 4 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 8033093 = 1506205) B1506205
theorem B2823011 : Blo 834351 2823011 := bstep (se 1 (by rfl) ⟨2117258, by rfl⟩ : syracuseStep 2823011 = 4234517) B4234517
theorem B1414003 : Blo 834351 1414003 := bstep (se 1 (by rfl) ⟨1060502, by rfl⟩ : syracuseStep 1414003 = 2121005) B2121005
theorem B2266001 : Blo 834351 2266001 := bstep (se 2 (by rfl) ⟨849750, by rfl⟩ : syracuseStep 2266001 = 1699501) B1699501
theorem B1414145 : Blo 834351 1414145 := bstep (se 2 (by rfl) ⟨530304, by rfl⟩ : syracuseStep 1414145 = 1060609) B1060609
theorem B2823281 : Blo 834351 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B6362225 : Blo 834351 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B1414273 : Blo 834351 1414273 := bstep (se 2 (by rfl) ⟨530352, by rfl⟩ : syracuseStep 1414273 = 1060705) B1060705
theorem B1807505 : Blo 834351 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B1414307 : Blo 834351 1414307 := bstep (se 1 (by rfl) ⟨1060730, by rfl⟩ : syracuseStep 1414307 = 2121461) B2121461
theorem B1414435 : Blo 834351 1414435 := bstep (se 1 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 1414435 = 2121653) B2121653
theorem B1447345 : Blo 834351 1447345 := bstep (se 2 (by rfl) ⟨542754, by rfl⟩ : syracuseStep 1447345 = 1085509) B1085509
theorem B1414577 : Blo 834351 1414577 := bstep (se 2 (by rfl) ⟨530466, by rfl⟩ : syracuseStep 1414577 = 1060933) B1060933
theorem B2856493 : Blo 834351 2856493 := bstep (se 3 (by rfl) ⟨535592, by rfl⟩ : syracuseStep 2856493 = 1071185) B1071185
theorem B1414705 : Blo 834351 1414705 := bstep (se 2 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 1414705 = 1061029) B1061029
theorem B2823821 : Blo 834351 2823821 := bstep (se 3 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 2823821 = 1058933) B1058933
theorem B2823875 : Blo 834351 2823875 := bstep (se 1 (by rfl) ⟨2117906, by rfl⟩ : syracuseStep 2823875 = 4235813) B4235813
theorem B4233059 : Blo 834351 4233059 := bstep (se 1 (by rfl) ⟨3174794, by rfl⟩ : syracuseStep 4233059 = 6349589) B6349589
theorem B2824145 : Blo 834351 2824145 := bstep (se 2 (by rfl) ⟨1059054, by rfl⟩ : syracuseStep 2824145 = 2118109) B2118109
theorem B5347397 : Blo 834351 5347397 := bstep (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) B1002637
theorem B1251539 : Blo 834351 1251539 := bstep (se 1 (by rfl) ⟨938654, by rfl⟩ : syracuseStep 1251539 = 1877309) B1877309
theorem B1251569 : Blo 834351 1251569 := bstep (se 2 (by rfl) ⟨469338, by rfl⟩ : syracuseStep 1251569 = 938677) B938677
theorem B1251587 : Blo 834351 1251587 := bstep (se 1 (by rfl) ⟨938690, by rfl⟩ : syracuseStep 1251587 = 1877381) B1877381
theorem B1251617 : Blo 834351 1251617 := bstep (se 2 (by rfl) ⟨469356, by rfl⟩ : syracuseStep 1251617 = 938713) B938713
theorem B2005283 : Blo 834351 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B1612067 : Blo 834351 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B1906993 : Blo 834351 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B1251635 : Blo 834351 1251635 := bstep (se 1 (by rfl) ⟨938726, by rfl⟩ : syracuseStep 1251635 = 1877453) B1877453
theorem B1251665 : Blo 834351 1251665 := bstep (se 2 (by rfl) ⟨469374, by rfl⟩ : syracuseStep 1251665 = 938749) B938749
theorem B1251683 : Blo 834351 1251683 := bstep (se 1 (by rfl) ⟨938762, by rfl⟩ : syracuseStep 1251683 = 1877525) B1877525
theorem B2005361 : Blo 834351 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B1251713 : Blo 834351 1251713 := bstep (se 2 (by rfl) ⟨469392, by rfl⟩ : syracuseStep 1251713 = 938785) B938785
theorem B1251731 : Blo 834351 1251731 := bstep (se 1 (by rfl) ⟨938798, by rfl⟩ : syracuseStep 1251731 = 1877597) B1877597
theorem B1251761 : Blo 834351 1251761 := bstep (se 2 (by rfl) ⟨469410, by rfl⟩ : syracuseStep 1251761 = 938821) B938821
theorem B1251779 : Blo 834351 1251779 := bstep (se 1 (by rfl) ⟨938834, by rfl⟩ : syracuseStep 1251779 = 1877669) B1877669
theorem B1251809 : Blo 834351 1251809 := bstep (se 2 (by rfl) ⟨469428, by rfl⟩ : syracuseStep 1251809 = 938857) B938857
theorem B2824685 : Blo 834351 2824685 := bstep (se 3 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 2824685 = 1059257) B1059257
theorem B1251827 : Blo 834351 1251827 := bstep (se 1 (by rfl) ⟨938870, by rfl⟩ : syracuseStep 1251827 = 1877741) B1877741
theorem B1251857 : Blo 834351 1251857 := bstep (se 2 (by rfl) ⟨469446, by rfl⟩ : syracuseStep 1251857 = 938893) B938893
theorem B1251875 : Blo 834351 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B2824739 : Blo 834351 2824739 := bstep (se 1 (by rfl) ⟨2118554, by rfl⟩ : syracuseStep 2824739 = 4237109) B4237109
theorem B1251905 : Blo 834351 1251905 := bstep (se 2 (by rfl) ⟨469464, by rfl⟩ : syracuseStep 1251905 = 938929) B938929
theorem B1251923 : Blo 834351 1251923 := bstep (se 1 (by rfl) ⟨938942, by rfl⟩ : syracuseStep 1251923 = 1877885) B1877885
theorem B1251953 : Blo 834351 1251953 := bstep (se 2 (by rfl) ⟨469482, by rfl⟩ : syracuseStep 1251953 = 938965) B938965
theorem B7150193 : Blo 834351 7150193 := bstep (se 2 (by rfl) ⟨2681322, by rfl⟩ : syracuseStep 7150193 = 5362645) B5362645
theorem B1251971 : Blo 834351 1251971 := bstep (se 1 (by rfl) ⟨938978, by rfl⟩ : syracuseStep 1251971 = 1877957) B1877957
theorem B4233869 : Blo 834351 4233869 := bstep (se 3 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 4233869 = 1587701) B1587701
theorem B1252001 : Blo 834351 1252001 := bstep (se 2 (by rfl) ⟨469500, by rfl⟩ : syracuseStep 1252001 = 939001) B939001
theorem B1252019 : Blo 834351 1252019 := bstep (se 1 (by rfl) ⟨939014, by rfl⟩ : syracuseStep 1252019 = 1878029) B1878029
theorem B1252049 : Blo 834351 1252049 := bstep (se 2 (by rfl) ⟨469518, by rfl⟩ : syracuseStep 1252049 = 939037) B939037
theorem B1252067 : Blo 834351 1252067 := bstep (se 1 (by rfl) ⟨939050, by rfl⟩ : syracuseStep 1252067 = 1878101) B1878101
theorem B1252097 : Blo 834351 1252097 := bstep (se 2 (by rfl) ⟨469536, by rfl⟩ : syracuseStep 1252097 = 939073) B939073
theorem B1252115 : Blo 834351 1252115 := bstep (se 1 (by rfl) ⟨939086, by rfl⟩ : syracuseStep 1252115 = 1878173) B1878173
theorem B1252145 : Blo 834351 1252145 := bstep (se 2 (by rfl) ⟨469554, by rfl⟩ : syracuseStep 1252145 = 939109) B939109
theorem B2825009 : Blo 834351 2825009 := bstep (se 2 (by rfl) ⟨1059378, by rfl⟩ : syracuseStep 2825009 = 2118757) B2118757
theorem B1252163 : Blo 834351 1252163 := bstep (se 1 (by rfl) ⟨939122, by rfl⟩ : syracuseStep 1252163 = 1878245) B1878245
theorem B1252193 : Blo 834351 1252193 := bstep (se 2 (by rfl) ⟨469572, by rfl⟩ : syracuseStep 1252193 = 939145) B939145
theorem B1252211 : Blo 834351 1252211 := bstep (se 1 (by rfl) ⟨939158, by rfl⟩ : syracuseStep 1252211 = 1878317) B1878317
theorem B1252241 : Blo 834351 1252241 := bstep (se 2 (by rfl) ⟨469590, by rfl⟩ : syracuseStep 1252241 = 939181) B939181
theorem B1252259 : Blo 834351 1252259 := bstep (se 1 (by rfl) ⟨939194, by rfl⟩ : syracuseStep 1252259 = 1878389) B1878389
theorem B1252289 : Blo 834351 1252289 := bstep (se 2 (by rfl) ⟨469608, by rfl⟩ : syracuseStep 1252289 = 939217) B939217
theorem B1252307 : Blo 834351 1252307 := bstep (se 1 (by rfl) ⟨939230, by rfl⟩ : syracuseStep 1252307 = 1878461) B1878461
theorem B1252337 : Blo 834351 1252337 := bstep (se 2 (by rfl) ⟨469626, by rfl⟩ : syracuseStep 1252337 = 939253) B939253
theorem B1252355 : Blo 834351 1252355 := bstep (se 1 (by rfl) ⟨939266, by rfl⟩ : syracuseStep 1252355 = 1878533) B1878533
theorem B1252385 : Blo 834351 1252385 := bstep (se 2 (by rfl) ⟨469644, by rfl⟩ : syracuseStep 1252385 = 939289) B939289
theorem B1252403 : Blo 834351 1252403 := bstep (se 1 (by rfl) ⟨939302, by rfl⟩ : syracuseStep 1252403 = 1878605) B1878605
theorem B1252433 : Blo 834351 1252433 := bstep (se 2 (by rfl) ⟨469662, by rfl⟩ : syracuseStep 1252433 = 939325) B939325
theorem B1252451 : Blo 834351 1252451 := bstep (se 1 (by rfl) ⟨939338, by rfl⟩ : syracuseStep 1252451 = 1878677) B1878677
theorem B2006129 : Blo 834351 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B892019 : Blo 834351 892019 := bstep (se 1 (by rfl) ⟨669014, by rfl⟩ : syracuseStep 892019 = 1338029) B1338029
theorem B1252481 : Blo 834351 1252481 := bstep (se 2 (by rfl) ⟨469680, by rfl⟩ : syracuseStep 1252481 = 939361) B939361
theorem B1252499 : Blo 834351 1252499 := bstep (se 1 (by rfl) ⟨939374, by rfl⟩ : syracuseStep 1252499 = 1878749) B1878749
theorem B1252529 : Blo 834351 1252529 := bstep (se 2 (by rfl) ⟨469698, by rfl⟩ : syracuseStep 1252529 = 939397) B939397
theorem B1252547 : Blo 834351 1252547 := bstep (se 1 (by rfl) ⟨939410, by rfl⟩ : syracuseStep 1252547 = 1878821) B1878821
theorem B1252577 : Blo 834351 1252577 := bstep (se 2 (by rfl) ⟨469716, by rfl⟩ : syracuseStep 1252577 = 939433) B939433
theorem B1252595 : Blo 834351 1252595 := bstep (se 1 (by rfl) ⟨939446, by rfl⟩ : syracuseStep 1252595 = 1878893) B1878893
theorem B1252625 : Blo 834351 1252625 := bstep (se 2 (by rfl) ⟨469734, by rfl⟩ : syracuseStep 1252625 = 939469) B939469
theorem B1252643 : Blo 834351 1252643 := bstep (se 1 (by rfl) ⟨939482, by rfl⟩ : syracuseStep 1252643 = 1878965) B1878965
theorem B1252673 : Blo 834351 1252673 := bstep (se 2 (by rfl) ⟨469752, by rfl⟩ : syracuseStep 1252673 = 939505) B939505
theorem B2825549 : Blo 834351 2825549 := bstep (se 3 (by rfl) ⟨529790, by rfl⟩ : syracuseStep 2825549 = 1059581) B1059581
theorem B1252691 : Blo 834351 1252691 := bstep (se 1 (by rfl) ⟨939518, by rfl⟩ : syracuseStep 1252691 = 1879037) B1879037
theorem B1252721 : Blo 834351 1252721 := bstep (se 2 (by rfl) ⟨469770, by rfl⟩ : syracuseStep 1252721 = 939541) B939541
theorem B5086577 : Blo 834351 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B1252739 : Blo 834351 1252739 := bstep (se 1 (by rfl) ⟨939554, by rfl⟩ : syracuseStep 1252739 = 1879109) B1879109
theorem B2825603 : Blo 834351 2825603 := bstep (se 1 (by rfl) ⟨2119202, by rfl⟩ : syracuseStep 2825603 = 4238405) B4238405
theorem B1252769 : Blo 834351 1252769 := bstep (se 2 (by rfl) ⟨469788, by rfl⟩ : syracuseStep 1252769 = 939577) B939577
theorem B3579299 : Blo 834351 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B1056179 : Blo 834351 1056179 := bstep (se 1 (by rfl) ⟨792134, by rfl⟩ : syracuseStep 1056179 = 1584269) B1584269
theorem B1252787 : Blo 834351 1252787 := bstep (se 1 (by rfl) ⟨939590, by rfl⟩ : syracuseStep 1252787 = 1879181) B1879181
theorem B1252817 : Blo 834351 1252817 := bstep (se 2 (by rfl) ⟨469806, by rfl⟩ : syracuseStep 1252817 = 939613) B939613
theorem B1252835 : Blo 834351 1252835 := bstep (se 1 (by rfl) ⟨939626, by rfl⟩ : syracuseStep 1252835 = 1879253) B1879253
theorem B1252865 : Blo 834351 1252865 := bstep (se 2 (by rfl) ⟨469824, by rfl⟩ : syracuseStep 1252865 = 939649) B939649
theorem B1252883 : Blo 834351 1252883 := bstep (se 1 (by rfl) ⟨939662, by rfl⟩ : syracuseStep 1252883 = 1879325) B1879325
theorem B1252913 : Blo 834351 1252913 := bstep (se 2 (by rfl) ⟨469842, by rfl⟩ : syracuseStep 1252913 = 939685) B939685
theorem B1252931 : Blo 834351 1252931 := bstep (se 1 (by rfl) ⟨939698, by rfl⟩ : syracuseStep 1252931 = 1879397) B1879397
theorem B1252961 : Blo 834351 1252961 := bstep (se 2 (by rfl) ⟨469860, by rfl⟩ : syracuseStep 1252961 = 939721) B939721
theorem B1252979 : Blo 834351 1252979 := bstep (se 1 (by rfl) ⟨939734, by rfl⟩ : syracuseStep 1252979 = 1879469) B1879469
theorem B1253009 : Blo 834351 1253009 := bstep (se 2 (by rfl) ⟨469878, by rfl⟩ : syracuseStep 1253009 = 939757) B939757
theorem B2825873 : Blo 834351 2825873 := bstep (se 2 (by rfl) ⟨1059702, by rfl⟩ : syracuseStep 2825873 = 2119405) B2119405
theorem B1253027 : Blo 834351 1253027 := bstep (se 1 (by rfl) ⟨939770, by rfl⟩ : syracuseStep 1253027 = 1879541) B1879541
theorem B1253057 : Blo 834351 1253057 := bstep (se 2 (by rfl) ⟨469896, by rfl⟩ : syracuseStep 1253057 = 939793) B939793
theorem B2039491 : Blo 834351 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B1253075 : Blo 834351 1253075 := bstep (se 1 (by rfl) ⟨939806, by rfl⟩ : syracuseStep 1253075 = 1879613) B1879613
theorem B1253105 : Blo 834351 1253105 := bstep (se 2 (by rfl) ⟨469914, by rfl⟩ : syracuseStep 1253105 = 939829) B939829
theorem B1253123 : Blo 834351 1253123 := bstep (se 1 (by rfl) ⟨939842, by rfl⟩ : syracuseStep 1253123 = 1879685) B1879685
theorem B1253153 : Blo 834351 1253153 := bstep (se 2 (by rfl) ⟨469932, by rfl⟩ : syracuseStep 1253153 = 939865) B939865
theorem B1253171 : Blo 834351 1253171 := bstep (se 1 (by rfl) ⟨939878, by rfl⟩ : syracuseStep 1253171 = 1879757) B1879757
theorem B1253201 : Blo 834351 1253201 := bstep (se 2 (by rfl) ⟨469950, by rfl⟩ : syracuseStep 1253201 = 939901) B939901
theorem B1253219 : Blo 834351 1253219 := bstep (se 1 (by rfl) ⟨939914, by rfl⟩ : syracuseStep 1253219 = 1879829) B1879829
theorem B1253249 : Blo 834351 1253249 := bstep (se 2 (by rfl) ⟨469968, by rfl⟩ : syracuseStep 1253249 = 939937) B939937
theorem B1253267 : Blo 834351 1253267 := bstep (se 1 (by rfl) ⟨939950, by rfl⟩ : syracuseStep 1253267 = 1879901) B1879901
theorem B1253297 : Blo 834351 1253297 := bstep (se 2 (by rfl) ⟨469986, by rfl⟩ : syracuseStep 1253297 = 939973) B939973
theorem B4530097 : Blo 834351 4530097 := bstep (se 2 (by rfl) ⟨1698786, by rfl⟩ : syracuseStep 4530097 = 3397573) B3397573
theorem B1253315 : Blo 834351 1253315 := bstep (se 1 (by rfl) ⟨939986, by rfl⟩ : syracuseStep 1253315 = 1879973) B1879973
theorem B1253345 : Blo 834351 1253345 := bstep (se 2 (by rfl) ⟨470004, by rfl⟩ : syracuseStep 1253345 = 940009) B940009
theorem B1253363 : Blo 834351 1253363 := bstep (se 1 (by rfl) ⟨940022, by rfl⟩ : syracuseStep 1253363 = 1880045) B1880045
theorem B1253393 : Blo 834351 1253393 := bstep (se 2 (by rfl) ⟨470022, by rfl⟩ : syracuseStep 1253393 = 940045) B940045
theorem B1253411 : Blo 834351 1253411 := bstep (se 1 (by rfl) ⟨940058, by rfl⟩ : syracuseStep 1253411 = 1880117) B1880117
theorem B1253441 : Blo 834351 1253441 := bstep (se 2 (by rfl) ⟨470040, by rfl⟩ : syracuseStep 1253441 = 940081) B940081
theorem B1253459 : Blo 834351 1253459 := bstep (se 1 (by rfl) ⟨940094, by rfl⟩ : syracuseStep 1253459 = 1880189) B1880189
theorem B1253489 : Blo 834351 1253489 := bstep (se 2 (by rfl) ⟨470058, by rfl⟩ : syracuseStep 1253489 = 940117) B940117
theorem B1056883 : Blo 834351 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B1253507 : Blo 834351 1253507 := bstep (se 1 (by rfl) ⟨940130, by rfl⟩ : syracuseStep 1253507 = 1880261) B1880261
theorem B1253537 : Blo 834351 1253537 := bstep (se 2 (by rfl) ⟨470076, by rfl⟩ : syracuseStep 1253537 = 940153) B940153
theorem B2826413 : Blo 834351 2826413 := bstep (se 3 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 2826413 = 1059905) B1059905
theorem B1253555 : Blo 834351 1253555 := bstep (se 1 (by rfl) ⟨940166, by rfl⟩ : syracuseStep 1253555 = 1880333) B1880333
theorem B1253585 : Blo 834351 1253585 := bstep (se 2 (by rfl) ⟨470094, by rfl⟩ : syracuseStep 1253585 = 940189) B940189
theorem B1056979 : Blo 834351 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1188065 : Blo 834351 1188065 := bstep (se 2 (by rfl) ⟨445524, by rfl⟩ : syracuseStep 1188065 = 891049) B891049
theorem B1253603 : Blo 834351 1253603 := bstep (se 1 (by rfl) ⟨940202, by rfl⟩ : syracuseStep 1253603 = 1880405) B1880405
theorem B2826467 : Blo 834351 2826467 := bstep (se 1 (by rfl) ⟨2119850, by rfl⟩ : syracuseStep 2826467 = 4239701) B4239701
theorem B1253633 : Blo 834351 1253633 := bstep (se 2 (by rfl) ⟨470112, by rfl⟩ : syracuseStep 1253633 = 940225) B940225
theorem B6103309 : Blo 834351 6103309 := bstep (se 3 (by rfl) ⟨1144370, by rfl⟩ : syracuseStep 6103309 = 2288741) B2288741
theorem B1253651 : Blo 834351 1253651 := bstep (se 1 (by rfl) ⟨940238, by rfl⟩ : syracuseStep 1253651 = 1880477) B1880477
theorem B1188145 : Blo 834351 1188145 := bstep (se 2 (by rfl) ⟨445554, by rfl⟩ : syracuseStep 1188145 = 891109) B891109
theorem B1253681 : Blo 834351 1253681 := bstep (se 2 (by rfl) ⟨470130, by rfl⟩ : syracuseStep 1253681 = 940261) B940261
theorem B1253699 : Blo 834351 1253699 := bstep (se 1 (by rfl) ⟨940274, by rfl⟩ : syracuseStep 1253699 = 1880549) B1880549
theorem B1253729 : Blo 834351 1253729 := bstep (se 2 (by rfl) ⟨470148, by rfl⟩ : syracuseStep 1253729 = 940297) B940297
theorem B1253747 : Blo 834351 1253747 := bstep (se 1 (by rfl) ⟨940310, by rfl⟩ : syracuseStep 1253747 = 1880621) B1880621
theorem B1253777 : Blo 834351 1253777 := bstep (se 2 (by rfl) ⟨470166, by rfl⟩ : syracuseStep 1253777 = 940333) B940333
theorem B1253795 : Blo 834351 1253795 := bstep (se 1 (by rfl) ⟨940346, by rfl⟩ : syracuseStep 1253795 = 1880693) B1880693
theorem B1253825 : Blo 834351 1253825 := bstep (se 2 (by rfl) ⟨470184, by rfl⟩ : syracuseStep 1253825 = 940369) B940369
theorem B4760005 : Blo 834351 4760005 := bstep (se 4 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 4760005 = 892501) B892501
theorem B1253843 : Blo 834351 1253843 := bstep (se 1 (by rfl) ⟨940382, by rfl⟩ : syracuseStep 1253843 = 1880765) B1880765
theorem B1253873 : Blo 834351 1253873 := bstep (se 2 (by rfl) ⟨470202, by rfl⟩ : syracuseStep 1253873 = 940405) B940405
theorem B2826737 : Blo 834351 2826737 := bstep (se 2 (by rfl) ⟨1060026, by rfl⟩ : syracuseStep 2826737 = 2120053) B2120053
theorem B1253891 : Blo 834351 1253891 := bstep (se 1 (by rfl) ⟨940418, by rfl⟩ : syracuseStep 1253891 = 1880837) B1880837
theorem B1253921 : Blo 834351 1253921 := bstep (se 2 (by rfl) ⟨470220, by rfl⟩ : syracuseStep 1253921 = 940441) B940441
theorem B1253939 : Blo 834351 1253939 := bstep (se 1 (by rfl) ⟨940454, by rfl⟩ : syracuseStep 1253939 = 1880909) B1880909
theorem B1253969 : Blo 834351 1253969 := bstep (se 2 (by rfl) ⟨470238, by rfl⟩ : syracuseStep 1253969 = 940477) B940477
theorem B1253987 : Blo 834351 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B1254017 : Blo 834351 1254017 := bstep (se 2 (by rfl) ⟨470256, by rfl⟩ : syracuseStep 1254017 = 940513) B940513
theorem B1254035 : Blo 834351 1254035 := bstep (se 1 (by rfl) ⟨940526, by rfl⟩ : syracuseStep 1254035 = 1881053) B1881053
theorem B1254065 : Blo 834351 1254065 := bstep (se 2 (by rfl) ⟨470274, by rfl⟩ : syracuseStep 1254065 = 940549) B940549
theorem B1057475 : Blo 834351 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1254083 : Blo 834351 1254083 := bstep (se 1 (by rfl) ⟨940562, by rfl⟩ : syracuseStep 1254083 = 1881125) B1881125
theorem B1254113 : Blo 834351 1254113 := bstep (se 2 (by rfl) ⟨470292, by rfl⟩ : syracuseStep 1254113 = 940585) B940585
theorem B1254131 : Blo 834351 1254131 := bstep (se 1 (by rfl) ⟨940598, by rfl⟩ : syracuseStep 1254131 = 1881197) B1881197
theorem B1254161 : Blo 834351 1254161 := bstep (se 2 (by rfl) ⟨470310, by rfl⟩ : syracuseStep 1254161 = 940621) B940621
theorem B1254179 : Blo 834351 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B1254209 : Blo 834351 1254209 := bstep (se 2 (by rfl) ⟨470328, by rfl⟩ : syracuseStep 1254209 = 940657) B940657
theorem B1254227 : Blo 834351 1254227 := bstep (se 1 (by rfl) ⟨940670, by rfl⟩ : syracuseStep 1254227 = 1881341) B1881341
theorem B1254257 : Blo 834351 1254257 := bstep (se 2 (by rfl) ⟨470346, by rfl⟩ : syracuseStep 1254257 = 940693) B940693
theorem B1254275 : Blo 834351 1254275 := bstep (se 1 (by rfl) ⟨940706, by rfl⟩ : syracuseStep 1254275 = 1881413) B1881413
theorem B5088133 : Blo 834351 5088133 := bstep (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) B954025
theorem B1254305 : Blo 834351 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B1254323 : Blo 834351 1254323 := bstep (se 1 (by rfl) ⟨940742, by rfl⟩ : syracuseStep 1254323 = 1881485) B1881485
theorem B1254353 : Blo 834351 1254353 := bstep (se 2 (by rfl) ⟨470382, by rfl⟩ : syracuseStep 1254353 = 940765) B940765
theorem B9642979 : Blo 834351 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B1254371 : Blo 834351 1254371 := bstep (se 1 (by rfl) ⟨940778, by rfl⟩ : syracuseStep 1254371 = 1881557) B1881557
theorem B3384305 : Blo 834351 3384305 := bstep (se 2 (by rfl) ⟨1269114, by rfl⟩ : syracuseStep 3384305 = 2538229) B2538229
theorem B6038513 : Blo 834351 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B1254401 : Blo 834351 1254401 := bstep (se 2 (by rfl) ⟨470400, by rfl⟩ : syracuseStep 1254401 = 940801) B940801
theorem B2827277 : Blo 834351 2827277 := bstep (se 3 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 2827277 = 1060229) B1060229
theorem B1254419 : Blo 834351 1254419 := bstep (se 1 (by rfl) ⟨940814, by rfl⟩ : syracuseStep 1254419 = 1881629) B1881629
theorem B1254449 : Blo 834351 1254449 := bstep (se 2 (by rfl) ⟨470418, by rfl⟩ : syracuseStep 1254449 = 940837) B940837
theorem B1188931 : Blo 834351 1188931 := bstep (se 1 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 1188931 = 1783397) B1783397
theorem B1254467 : Blo 834351 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B2827331 : Blo 834351 2827331 := bstep (se 1 (by rfl) ⟨2120498, by rfl⟩ : syracuseStep 2827331 = 4240997) B4240997
theorem B894035 : Blo 834351 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B1254497 : Blo 834351 1254497 := bstep (se 2 (by rfl) ⟨470436, by rfl⟩ : syracuseStep 1254497 = 940873) B940873
theorem B1254515 : Blo 834351 1254515 := bstep (se 1 (by rfl) ⟨940886, by rfl⟩ : syracuseStep 1254515 = 1881773) B1881773
theorem B1254545 : Blo 834351 1254545 := bstep (se 2 (by rfl) ⟨470454, by rfl⟩ : syracuseStep 1254545 = 940909) B940909
theorem B1254563 : Blo 834351 1254563 := bstep (se 1 (by rfl) ⟨940922, by rfl⟩ : syracuseStep 1254563 = 1881845) B1881845
theorem B1254593 : Blo 834351 1254593 := bstep (se 2 (by rfl) ⟨470472, by rfl⟩ : syracuseStep 1254593 = 940945) B940945
theorem B1254611 : Blo 834351 1254611 := bstep (se 1 (by rfl) ⟨940958, by rfl⟩ : syracuseStep 1254611 = 1881917) B1881917
theorem B1254641 : Blo 834351 1254641 := bstep (se 2 (by rfl) ⟨470490, by rfl⟩ : syracuseStep 1254641 = 940981) B940981
theorem B1254659 : Blo 834351 1254659 := bstep (se 1 (by rfl) ⟨940994, by rfl⟩ : syracuseStep 1254659 = 1881989) B1881989
theorem B1254689 : Blo 834351 1254689 := bstep (se 2 (by rfl) ⟨470508, by rfl⟩ : syracuseStep 1254689 = 941017) B941017
theorem B1254707 : Blo 834351 1254707 := bstep (se 1 (by rfl) ⟨941030, by rfl⟩ : syracuseStep 1254707 = 1882061) B1882061
theorem B5088581 : Blo 834351 5088581 := bstep (se 4 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 5088581 = 954109) B954109
theorem B1254737 : Blo 834351 1254737 := bstep (se 2 (by rfl) ⟨470526, by rfl⟩ : syracuseStep 1254737 = 941053) B941053
theorem B2827601 : Blo 834351 2827601 := bstep (se 2 (by rfl) ⟨1060350, by rfl⟩ : syracuseStep 2827601 = 2120701) B2120701
theorem B1254755 : Blo 834351 1254755 := bstep (se 1 (by rfl) ⟨941066, by rfl⟩ : syracuseStep 1254755 = 1882133) B1882133
theorem B1254785 : Blo 834351 1254785 := bstep (se 2 (by rfl) ⟨470544, by rfl⟩ : syracuseStep 1254785 = 941089) B941089
theorem B1058179 : Blo 834351 1058179 := bstep (se 1 (by rfl) ⟨793634, by rfl⟩ : syracuseStep 1058179 = 1587269) B1587269
theorem B1254803 : Blo 834351 1254803 := bstep (se 1 (by rfl) ⟨941102, by rfl⟩ : syracuseStep 1254803 = 1882205) B1882205
theorem B3810737 : Blo 834351 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B1254833 : Blo 834351 1254833 := bstep (se 2 (by rfl) ⟨470562, by rfl⟩ : syracuseStep 1254833 = 941125) B941125
theorem B1254851 : Blo 834351 1254851 := bstep (se 1 (by rfl) ⟨941138, by rfl⟩ : syracuseStep 1254851 = 1882277) B1882277
theorem B1254881 : Blo 834351 1254881 := bstep (se 2 (by rfl) ⟨470580, by rfl⟩ : syracuseStep 1254881 = 941161) B941161
theorem B1058275 : Blo 834351 1058275 := bstep (se 1 (by rfl) ⟨793706, by rfl⟩ : syracuseStep 1058275 = 1587413) B1587413
theorem B1877489 : Blo 834351 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B4236785 : Blo 834351 4236785 := bstep (se 2 (by rfl) ⟨1588794, by rfl⟩ : syracuseStep 4236785 = 3177589) B3177589
theorem B1254899 : Blo 834351 1254899 := bstep (se 1 (by rfl) ⟨941174, by rfl⟩ : syracuseStep 1254899 = 1882349) B1882349
theorem B4531697 : Blo 834351 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B1877507 : Blo 834351 1877507 := bstep (se 1 (by rfl) ⟨1408130, by rfl⟩ : syracuseStep 1877507 = 2816261) B2816261
theorem B1254929 : Blo 834351 1254929 := bstep (se 2 (by rfl) ⟨470598, by rfl⟩ : syracuseStep 1254929 = 941197) B941197
theorem B1189409 : Blo 834351 1189409 := bstep (se 2 (by rfl) ⟨446028, by rfl⟩ : syracuseStep 1189409 = 892057) B892057
theorem B1254947 : Blo 834351 1254947 := bstep (se 1 (by rfl) ⟨941210, by rfl⟩ : syracuseStep 1254947 = 1882421) B1882421
theorem B1254977 : Blo 834351 1254977 := bstep (se 2 (by rfl) ⟨470616, by rfl⟩ : syracuseStep 1254977 = 941233) B941233
theorem B4531781 : Blo 834351 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B1254995 : Blo 834351 1254995 := bstep (se 1 (by rfl) ⟨941246, by rfl⟩ : syracuseStep 1254995 = 1882493) B1882493
theorem B1255025 : Blo 834351 1255025 := bstep (se 2 (by rfl) ⟨470634, by rfl⟩ : syracuseStep 1255025 = 941269) B941269
theorem B1255043 : Blo 834351 1255043 := bstep (se 1 (by rfl) ⟨941282, by rfl⟩ : syracuseStep 1255043 = 1882565) B1882565
theorem B1189523 : Blo 834351 1189523 := bstep (se 1 (by rfl) ⟨892142, by rfl⟩ : syracuseStep 1189523 = 1784285) B1784285
theorem B1255073 : Blo 834351 1255073 := bstep (se 2 (by rfl) ⟨470652, by rfl⟩ : syracuseStep 1255073 = 941305) B941305
theorem B1255091 : Blo 834351 1255091 := bstep (se 1 (by rfl) ⟨941318, by rfl⟩ : syracuseStep 1255091 = 1882637) B1882637
theorem B1255121 : Blo 834351 1255121 := bstep (se 2 (by rfl) ⟨470670, by rfl⟩ : syracuseStep 1255121 = 941341) B941341
theorem B1189603 : Blo 834351 1189603 := bstep (se 1 (by rfl) ⟨892202, by rfl⟩ : syracuseStep 1189603 = 1784405) B1784405
theorem B1255139 : Blo 834351 1255139 := bstep (se 1 (by rfl) ⟨941354, by rfl⟩ : syracuseStep 1255139 = 1882709) B1882709
theorem B1255169 : Blo 834351 1255169 := bstep (se 2 (by rfl) ⟨470688, by rfl⟩ : syracuseStep 1255169 = 941377) B941377
theorem B1877777 : Blo 834351 1877777 := bstep (se 2 (by rfl) ⟨704166, by rfl⟩ : syracuseStep 1877777 = 1408333) B1408333
theorem B1255187 : Blo 834351 1255187 := bstep (se 1 (by rfl) ⟨941390, by rfl⟩ : syracuseStep 1255187 = 1882781) B1882781
theorem B1877795 : Blo 834351 1877795 := bstep (se 1 (by rfl) ⟨1408346, by rfl⟩ : syracuseStep 1877795 = 2816693) B2816693
theorem B1255217 : Blo 834351 1255217 := bstep (se 2 (by rfl) ⟨470706, by rfl⟩ : syracuseStep 1255217 = 941413) B941413
theorem B9545525 : Blo 834351 9545525 := bstep (se 5 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 9545525 = 894893) B894893
theorem B1255235 : Blo 834351 1255235 := bstep (se 1 (by rfl) ⟨941426, by rfl⟩ : syracuseStep 1255235 = 1882853) B1882853
theorem B1255265 : Blo 834351 1255265 := bstep (se 2 (by rfl) ⟨470724, by rfl⟩ : syracuseStep 1255265 = 941449) B941449
theorem B2828141 : Blo 834351 2828141 := bstep (se 3 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 2828141 = 1060553) B1060553
theorem B1255283 : Blo 834351 1255283 := bstep (se 1 (by rfl) ⟨941462, by rfl⟩ : syracuseStep 1255283 = 1882925) B1882925
theorem B1255313 : Blo 834351 1255313 := bstep (se 2 (by rfl) ⟨470742, by rfl⟩ : syracuseStep 1255313 = 941485) B941485
theorem B1255331 : Blo 834351 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B2828195 : Blo 834351 2828195 := bstep (se 1 (by rfl) ⟨2121146, by rfl⟩ : syracuseStep 2828195 = 4242293) B4242293
theorem B1255361 : Blo 834351 1255361 := bstep (se 2 (by rfl) ⟨470760, by rfl⟩ : syracuseStep 1255361 = 941521) B941521
theorem B1058771 : Blo 834351 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B1255379 : Blo 834351 1255379 := bstep (se 1 (by rfl) ⟨941534, by rfl⟩ : syracuseStep 1255379 = 1883069) B1883069
theorem B1255409 : Blo 834351 1255409 := bstep (se 2 (by rfl) ⟨470778, by rfl⟩ : syracuseStep 1255409 = 941557) B941557
theorem B1255427 : Blo 834351 1255427 := bstep (se 1 (by rfl) ⟨941570, by rfl⟩ : syracuseStep 1255427 = 1883141) B1883141
theorem B894979 : Blo 834351 894979 := bstep (se 1 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 894979 = 1342469) B1342469
theorem B1255457 : Blo 834351 1255457 := bstep (se 2 (by rfl) ⟨470796, by rfl⟩ : syracuseStep 1255457 = 941593) B941593
theorem B1878065 : Blo 834351 1878065 := bstep (se 2 (by rfl) ⟨704274, by rfl⟩ : syracuseStep 1878065 = 1408549) B1408549
theorem B1255475 : Blo 834351 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B1878083 : Blo 834351 1878083 := bstep (se 1 (by rfl) ⟨1408562, by rfl⟩ : syracuseStep 1878083 = 2817125) B2817125
theorem B1255505 : Blo 834351 1255505 := bstep (se 2 (by rfl) ⟨470814, by rfl⟩ : syracuseStep 1255505 = 941629) B941629
theorem B1255523 : Blo 834351 1255523 := bstep (se 1 (by rfl) ⟨941642, by rfl⟩ : syracuseStep 1255523 = 1883285) B1883285
theorem B1255553 : Blo 834351 1255553 := bstep (se 2 (by rfl) ⟨470832, by rfl⟩ : syracuseStep 1255553 = 941665) B941665
theorem B1255571 : Blo 834351 1255571 := bstep (se 1 (by rfl) ⟨941678, by rfl⟩ : syracuseStep 1255571 = 1883357) B1883357
theorem B1255601 : Blo 834351 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B2828465 : Blo 834351 2828465 := bstep (se 2 (by rfl) ⟨1060674, by rfl⟩ : syracuseStep 2828465 = 2121349) B2121349
theorem B1255619 : Blo 834351 1255619 := bstep (se 1 (by rfl) ⟨941714, by rfl⟩ : syracuseStep 1255619 = 1883429) B1883429
theorem B1255649 : Blo 834351 1255649 := bstep (se 2 (by rfl) ⟨470868, by rfl⟩ : syracuseStep 1255649 = 941737) B941737
theorem B1255667 : Blo 834351 1255667 := bstep (se 1 (by rfl) ⟨941750, by rfl⟩ : syracuseStep 1255667 = 1883501) B1883501
theorem B1190161 : Blo 834351 1190161 := bstep (se 2 (by rfl) ⟨446310, by rfl⟩ : syracuseStep 1190161 = 892621) B892621
theorem B1255697 : Blo 834351 1255697 := bstep (se 2 (by rfl) ⟨470886, by rfl⟩ : syracuseStep 1255697 = 941773) B941773
theorem B1255715 : Blo 834351 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B1255745 : Blo 834351 1255745 := bstep (se 2 (by rfl) ⟨470904, by rfl⟩ : syracuseStep 1255745 = 941809) B941809
theorem B1878353 : Blo 834351 1878353 := bstep (se 2 (by rfl) ⟨704382, by rfl⟩ : syracuseStep 1878353 = 1408765) B1408765
theorem B1255763 : Blo 834351 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B1878371 : Blo 834351 1878371 := bstep (se 1 (by rfl) ⟨1408778, by rfl⟩ : syracuseStep 1878371 = 2817557) B2817557
theorem B1255793 : Blo 834351 1255793 := bstep (se 2 (by rfl) ⟨470922, by rfl⟩ : syracuseStep 1255793 = 941845) B941845
theorem B1255811 : Blo 834351 1255811 := bstep (se 1 (by rfl) ⟨941858, by rfl⟩ : syracuseStep 1255811 = 1883717) B1883717
theorem B4761989 : Blo 834351 4761989 := bstep (se 4 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 4761989 = 892873) B892873
theorem B1255841 : Blo 834351 1255841 := bstep (se 2 (by rfl) ⟨470940, by rfl⟩ : syracuseStep 1255841 = 941881) B941881
theorem B1255859 : Blo 834351 1255859 := bstep (se 1 (by rfl) ⟨941894, by rfl⟩ : syracuseStep 1255859 = 1883789) B1883789
theorem B9677237 : Blo 834351 9677237 := bstep (se 5 (by rfl) ⟨453620, by rfl⟩ : syracuseStep 9677237 = 907241) B907241
theorem B1255889 : Blo 834351 1255889 := bstep (se 2 (by rfl) ⟨470958, by rfl⟩ : syracuseStep 1255889 = 941917) B941917
theorem B1255907 : Blo 834351 1255907 := bstep (se 1 (by rfl) ⟨941930, by rfl⟩ : syracuseStep 1255907 = 1883861) B1883861
theorem B1255937 : Blo 834351 1255937 := bstep (se 2 (by rfl) ⟨470976, by rfl⟩ : syracuseStep 1255937 = 941953) B941953
theorem B3811853 : Blo 834351 3811853 := bstep (se 3 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 3811853 = 1429445) B1429445
theorem B1255955 : Blo 834351 1255955 := bstep (se 1 (by rfl) ⟨941966, by rfl⟩ : syracuseStep 1255955 = 1883933) B1883933
theorem B1255985 : Blo 834351 1255985 := bstep (se 2 (by rfl) ⟨470994, by rfl⟩ : syracuseStep 1255985 = 941989) B941989
theorem B1256003 : Blo 834351 1256003 := bstep (se 1 (by rfl) ⟨942002, by rfl⟩ : syracuseStep 1256003 = 1884005) B1884005
theorem B1256033 : Blo 834351 1256033 := bstep (se 2 (by rfl) ⟨471012, by rfl⟩ : syracuseStep 1256033 = 942025) B942025
theorem B1878641 : Blo 834351 1878641 := bstep (se 2 (by rfl) ⟨704490, by rfl⟩ : syracuseStep 1878641 = 1408981) B1408981
theorem B1256051 : Blo 834351 1256051 := bstep (se 1 (by rfl) ⟨942038, by rfl⟩ : syracuseStep 1256051 = 1884077) B1884077
theorem B1878659 : Blo 834351 1878659 := bstep (se 1 (by rfl) ⟨1408994, by rfl⟩ : syracuseStep 1878659 = 2817989) B2817989
theorem B1256081 : Blo 834351 1256081 := bstep (se 2 (by rfl) ⟨471030, by rfl⟩ : syracuseStep 1256081 = 942061) B942061
theorem B1059475 : Blo 834351 1059475 := bstep (se 1 (by rfl) ⟨794606, by rfl⟩ : syracuseStep 1059475 = 1589213) B1589213
theorem B1256099 : Blo 834351 1256099 := bstep (se 1 (by rfl) ⟨942074, by rfl⟩ : syracuseStep 1256099 = 1884149) B1884149
theorem B1256129 : Blo 834351 1256129 := bstep (se 2 (by rfl) ⟨471048, by rfl⟩ : syracuseStep 1256129 = 942097) B942097
theorem B2829005 : Blo 834351 2829005 := bstep (se 3 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 2829005 = 1060877) B1060877
theorem B1256147 : Blo 834351 1256147 := bstep (se 1 (by rfl) ⟨942110, by rfl⟩ : syracuseStep 1256147 = 1884221) B1884221
theorem B1256177 : Blo 834351 1256177 := bstep (se 2 (by rfl) ⟨471066, by rfl⟩ : syracuseStep 1256177 = 942133) B942133
theorem B1059571 : Blo 834351 1059571 := bstep (se 1 (by rfl) ⟨794678, by rfl⟩ : syracuseStep 1059571 = 1589357) B1589357
theorem B1256195 : Blo 834351 1256195 := bstep (se 1 (by rfl) ⟨942146, by rfl⟩ : syracuseStep 1256195 = 1884293) B1884293
theorem B2829059 : Blo 834351 2829059 := bstep (se 1 (by rfl) ⟨2121794, by rfl⟩ : syracuseStep 2829059 = 4243589) B4243589
theorem B1256225 : Blo 834351 1256225 := bstep (se 2 (by rfl) ⟨471084, by rfl⟩ : syracuseStep 1256225 = 942169) B942169
theorem B1256243 : Blo 834351 1256243 := bstep (se 1 (by rfl) ⟨942182, by rfl⟩ : syracuseStep 1256243 = 1884365) B1884365
theorem B1256273 : Blo 834351 1256273 := bstep (se 2 (by rfl) ⟨471102, by rfl⟩ : syracuseStep 1256273 = 942205) B942205
theorem B1256291 : Blo 834351 1256291 := bstep (se 1 (by rfl) ⟨942218, by rfl⟩ : syracuseStep 1256291 = 1884437) B1884437
theorem B1256321 : Blo 834351 1256321 := bstep (se 2 (by rfl) ⟨471120, by rfl⟩ : syracuseStep 1256321 = 942241) B942241
theorem B1878929 : Blo 834351 1878929 := bstep (se 2 (by rfl) ⟨704598, by rfl⟩ : syracuseStep 1878929 = 1409197) B1409197
theorem B1256339 : Blo 834351 1256339 := bstep (se 1 (by rfl) ⟨942254, by rfl⟩ : syracuseStep 1256339 = 1884509) B1884509
theorem B1878947 : Blo 834351 1878947 := bstep (se 1 (by rfl) ⟨1409210, by rfl⟩ : syracuseStep 1878947 = 2818421) B2818421
theorem B4238243 : Blo 834351 4238243 := bstep (se 1 (by rfl) ⟨3178682, by rfl⟩ : syracuseStep 4238243 = 6357365) B6357365
theorem B1584049 : Blo 834351 1584049 := bstep (se 2 (by rfl) ⟨594018, by rfl⟩ : syracuseStep 1584049 = 1188037) B1188037
theorem B1256369 : Blo 834351 1256369 := bstep (se 2 (by rfl) ⟨471138, by rfl⟩ : syracuseStep 1256369 = 942277) B942277
theorem B1256387 : Blo 834351 1256387 := bstep (se 1 (by rfl) ⟨942290, by rfl⟩ : syracuseStep 1256387 = 1884581) B1884581
theorem B1190867 : Blo 834351 1190867 := bstep (se 1 (by rfl) ⟨893150, by rfl⟩ : syracuseStep 1190867 = 1786301) B1786301
theorem B1256417 : Blo 834351 1256417 := bstep (se 2 (by rfl) ⟨471156, by rfl⟩ : syracuseStep 1256417 = 942313) B942313
theorem B1256435 : Blo 834351 1256435 := bstep (se 1 (by rfl) ⟨942326, by rfl⟩ : syracuseStep 1256435 = 1884653) B1884653
theorem B1256465 : Blo 834351 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B2829329 : Blo 834351 2829329 := bstep (se 2 (by rfl) ⟨1060998, by rfl⟩ : syracuseStep 2829329 = 2121997) B2121997
theorem B1256483 : Blo 834351 1256483 := bstep (se 1 (by rfl) ⟨942362, by rfl⟩ : syracuseStep 1256483 = 1884725) B1884725
theorem B1256513 : Blo 834351 1256513 := bstep (se 2 (by rfl) ⟨471192, by rfl⟩ : syracuseStep 1256513 = 942385) B942385
theorem B1256531 : Blo 834351 1256531 := bstep (se 1 (by rfl) ⟨942398, by rfl⟩ : syracuseStep 1256531 = 1884797) B1884797
theorem B1256561 : Blo 834351 1256561 := bstep (se 2 (by rfl) ⟨471210, by rfl⟩ : syracuseStep 1256561 = 942421) B942421
theorem B1256579 : Blo 834351 1256579 := bstep (se 1 (by rfl) ⟨942434, by rfl⟩ : syracuseStep 1256579 = 1884869) B1884869
theorem B1256609 : Blo 834351 1256609 := bstep (se 2 (by rfl) ⟨471228, by rfl⟩ : syracuseStep 1256609 = 942457) B942457
theorem B1879217 : Blo 834351 1879217 := bstep (se 2 (by rfl) ⟨704706, by rfl⟩ : syracuseStep 1879217 = 1409413) B1409413
theorem B1256627 : Blo 834351 1256627 := bstep (se 1 (by rfl) ⟨942470, by rfl⟩ : syracuseStep 1256627 = 1884941) B1884941
theorem B1879235 : Blo 834351 1879235 := bstep (se 1 (by rfl) ⟨1409426, by rfl⟩ : syracuseStep 1879235 = 2818853) B2818853
theorem B1256657 : Blo 834351 1256657 := bstep (se 2 (by rfl) ⟨471246, by rfl⟩ : syracuseStep 1256657 = 942493) B942493
theorem B1060067 : Blo 834351 1060067 := bstep (se 1 (by rfl) ⟨795050, by rfl⟩ : syracuseStep 1060067 = 1590101) B1590101
theorem B1256675 : Blo 834351 1256675 := bstep (se 1 (by rfl) ⟨942506, by rfl⟩ : syracuseStep 1256675 = 1885013) B1885013
theorem B1256705 : Blo 834351 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B1256723 : Blo 834351 1256723 := bstep (se 1 (by rfl) ⟨942542, by rfl⟩ : syracuseStep 1256723 = 1885085) B1885085
theorem B1256753 : Blo 834351 1256753 := bstep (se 2 (by rfl) ⟨471282, by rfl⟩ : syracuseStep 1256753 = 942565) B942565
theorem B1584451 : Blo 834351 1584451 := bstep (se 1 (by rfl) ⟨1188338, by rfl⟩ : syracuseStep 1584451 = 2376677) B2376677
theorem B1256771 : Blo 834351 1256771 := bstep (se 1 (by rfl) ⟨942578, by rfl⟩ : syracuseStep 1256771 = 1885157) B1885157
theorem B1256801 : Blo 834351 1256801 := bstep (se 2 (by rfl) ⟨471300, by rfl⟩ : syracuseStep 1256801 = 942601) B942601
theorem B1584497 : Blo 834351 1584497 := bstep (se 2 (by rfl) ⟨594186, by rfl⟩ : syracuseStep 1584497 = 1188373) B1188373
theorem B1256819 : Blo 834351 1256819 := bstep (se 1 (by rfl) ⟨942614, by rfl⟩ : syracuseStep 1256819 = 1885229) B1885229
theorem B1256849 : Blo 834351 1256849 := bstep (se 2 (by rfl) ⟨471318, by rfl⟩ : syracuseStep 1256849 = 942637) B942637
theorem B1256867 : Blo 834351 1256867 := bstep (se 1 (by rfl) ⟨942650, by rfl⟩ : syracuseStep 1256867 = 1885301) B1885301
theorem B1256897 : Blo 834351 1256897 := bstep (se 2 (by rfl) ⟨471336, by rfl⟩ : syracuseStep 1256897 = 942673) B942673
theorem B1879505 : Blo 834351 1879505 := bstep (se 2 (by rfl) ⟨704814, by rfl⟩ : syracuseStep 1879505 = 1409629) B1409629
theorem B1256915 : Blo 834351 1256915 := bstep (se 1 (by rfl) ⟨942686, by rfl⟩ : syracuseStep 1256915 = 1885373) B1885373
theorem B1879523 : Blo 834351 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B1256945 : Blo 834351 1256945 := bstep (se 2 (by rfl) ⟨471354, by rfl⟩ : syracuseStep 1256945 = 942709) B942709
theorem B1256963 : Blo 834351 1256963 := bstep (se 1 (by rfl) ⟨942722, by rfl⟩ : syracuseStep 1256963 = 1885445) B1885445
theorem B1256993 : Blo 834351 1256993 := bstep (se 2 (by rfl) ⟨471372, by rfl⟩ : syracuseStep 1256993 = 942745) B942745
theorem B1257011 : Blo 834351 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B1191505 : Blo 834351 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B1257041 : Blo 834351 1257041 := bstep (se 2 (by rfl) ⟨471390, by rfl⟩ : syracuseStep 1257041 = 942781) B942781
theorem B1257059 : Blo 834351 1257059 := bstep (se 1 (by rfl) ⟨942794, by rfl⟩ : syracuseStep 1257059 = 1885589) B1885589
theorem B1257089 : Blo 834351 1257089 := bstep (se 2 (by rfl) ⟨471408, by rfl⟩ : syracuseStep 1257089 = 942817) B942817
theorem B1584785 : Blo 834351 1584785 := bstep (se 2 (by rfl) ⟨594294, by rfl⟩ : syracuseStep 1584785 = 1188589) B1188589
theorem B1257107 : Blo 834351 1257107 := bstep (se 1 (by rfl) ⟨942830, by rfl⟩ : syracuseStep 1257107 = 1885661) B1885661
theorem B1257137 : Blo 834351 1257137 := bstep (se 2 (by rfl) ⟨471426, by rfl⟩ : syracuseStep 1257137 = 942853) B942853
theorem B1355459 : Blo 834351 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B1191619 : Blo 834351 1191619 := bstep (se 1 (by rfl) ⟨893714, by rfl⟩ : syracuseStep 1191619 = 1787429) B1787429
theorem B1257155 : Blo 834351 1257155 := bstep (se 1 (by rfl) ⟨942866, by rfl⟩ : syracuseStep 1257155 = 1885733) B1885733
theorem B4239053 : Blo 834351 4239053 := bstep (se 3 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 4239053 = 1589645) B1589645
theorem B1257185 : Blo 834351 1257185 := bstep (se 2 (by rfl) ⟨471444, by rfl⟩ : syracuseStep 1257185 = 942889) B942889
theorem B1879793 : Blo 834351 1879793 := bstep (se 2 (by rfl) ⟨704922, by rfl⟩ : syracuseStep 1879793 = 1409845) B1409845
theorem B1257203 : Blo 834351 1257203 := bstep (se 1 (by rfl) ⟨942902, by rfl⟩ : syracuseStep 1257203 = 1885805) B1885805
theorem B1879811 : Blo 834351 1879811 := bstep (se 1 (by rfl) ⟨1409858, by rfl⟩ : syracuseStep 1879811 = 2819717) B2819717
theorem B1257233 : Blo 834351 1257233 := bstep (se 2 (by rfl) ⟨471462, by rfl⟩ : syracuseStep 1257233 = 942925) B942925
theorem B1257251 : Blo 834351 1257251 := bstep (se 1 (by rfl) ⟨942938, by rfl⟩ : syracuseStep 1257251 = 1885877) B1885877
theorem B1257281 : Blo 834351 1257281 := bstep (se 2 (by rfl) ⟨471480, by rfl⟩ : syracuseStep 1257281 = 942961) B942961
theorem B1257299 : Blo 834351 1257299 := bstep (se 1 (by rfl) ⟨942974, by rfl⟩ : syracuseStep 1257299 = 1885949) B1885949
theorem B1257329 : Blo 834351 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B1257347 : Blo 834351 1257347 := bstep (se 1 (by rfl) ⟨943010, by rfl⟩ : syracuseStep 1257347 = 1886021) B1886021
theorem B1257377 : Blo 834351 1257377 := bstep (se 2 (by rfl) ⟨471516, by rfl⟩ : syracuseStep 1257377 = 943033) B943033
theorem B1060771 : Blo 834351 1060771 := bstep (se 1 (by rfl) ⟨795578, by rfl⟩ : syracuseStep 1060771 = 1591157) B1591157
theorem B1257395 : Blo 834351 1257395 := bstep (se 1 (by rfl) ⟨943046, by rfl⟩ : syracuseStep 1257395 = 1886093) B1886093
theorem B1257425 : Blo 834351 1257425 := bstep (se 2 (by rfl) ⟨471534, by rfl⟩ : syracuseStep 1257425 = 943069) B943069
theorem B1257443 : Blo 834351 1257443 := bstep (se 1 (by rfl) ⟨943082, by rfl⟩ : syracuseStep 1257443 = 1886165) B1886165
theorem B1257473 : Blo 834351 1257473 := bstep (se 2 (by rfl) ⟨471552, by rfl⟩ : syracuseStep 1257473 = 943105) B943105
theorem B1060867 : Blo 834351 1060867 := bstep (se 1 (by rfl) ⟨795650, by rfl⟩ : syracuseStep 1060867 = 1591301) B1591301
theorem B1880081 : Blo 834351 1880081 := bstep (se 2 (by rfl) ⟨705030, by rfl⟩ : syracuseStep 1880081 = 1410061) B1410061
theorem B1257491 : Blo 834351 1257491 := bstep (se 1 (by rfl) ⟨943118, by rfl⟩ : syracuseStep 1257491 = 1886237) B1886237
theorem B1880099 : Blo 834351 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B1257521 : Blo 834351 1257521 := bstep (se 2 (by rfl) ⟨471570, by rfl⟩ : syracuseStep 1257521 = 943141) B943141
theorem B13578353 : Blo 834351 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B1880369 : Blo 834351 1880369 := bstep (se 2 (by rfl) ⟨705138, by rfl⟩ : syracuseStep 1880369 = 1410277) B1410277
theorem B1880387 : Blo 834351 1880387 := bstep (se 1 (by rfl) ⟨1410290, by rfl⟩ : syracuseStep 1880387 = 2820581) B2820581
theorem B1585507 : Blo 834351 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B1880657 : Blo 834351 1880657 := bstep (se 2 (by rfl) ⟨705246, by rfl⟩ : syracuseStep 1880657 = 1410493) B1410493
theorem B1782371 : Blo 834351 1782371 := bstep (se 1 (by rfl) ⟨1336778, by rfl⟩ : syracuseStep 1782371 = 2673557) B2673557
theorem B1880675 : Blo 834351 1880675 := bstep (se 1 (by rfl) ⟨1410506, by rfl⟩ : syracuseStep 1880675 = 2821013) B2821013
theorem B12366533 : Blo 834351 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B1585955 : Blo 834351 1585955 := bstep (se 1 (by rfl) ⟨1189466, by rfl⟩ : syracuseStep 1585955 = 2378933) B2378933
theorem B1880945 : Blo 834351 1880945 := bstep (se 2 (by rfl) ⟨705354, by rfl⟩ : syracuseStep 1880945 = 1410709) B1410709
theorem B1880963 : Blo 834351 1880963 := bstep (se 1 (by rfl) ⟨1410722, by rfl⟩ : syracuseStep 1880963 = 2821445) B2821445
theorem B1192963 : Blo 834351 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B2012195 : Blo 834351 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B1586243 : Blo 834351 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B2143345 : Blo 834351 2143345 := bstep (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) B1607509
theorem B1881233 : Blo 834351 1881233 := bstep (se 2 (by rfl) ⟨705462, by rfl⟩ : syracuseStep 1881233 = 1410925) B1410925
theorem B1881251 : Blo 834351 1881251 := bstep (se 1 (by rfl) ⟨1410938, by rfl⟩ : syracuseStep 1881251 = 2821877) B2821877
theorem B1881521 : Blo 834351 1881521 := bstep (se 2 (by rfl) ⟨705570, by rfl⟩ : syracuseStep 1881521 = 1411141) B1411141
theorem B1881539 : Blo 834351 1881539 := bstep (se 1 (by rfl) ⟨1411154, by rfl⟩ : syracuseStep 1881539 = 2822309) B2822309
theorem B1881809 : Blo 834351 1881809 := bstep (se 2 (by rfl) ⟨705678, by rfl⟩ : syracuseStep 1881809 = 1411357) B1411357
theorem B1881827 : Blo 834351 1881827 := bstep (se 1 (by rfl) ⟨1411370, by rfl⟩ : syracuseStep 1881827 = 2822741) B2822741
theorem B4011875 : Blo 834351 4011875 := bstep (se 1 (by rfl) ⟨3008906, by rfl⟩ : syracuseStep 4011875 = 6017813) B6017813
theorem B4831139 : Blo 834351 4831139 := bstep (se 1 (by rfl) ⟨3623354, by rfl⟩ : syracuseStep 4831139 = 7246709) B7246709
theorem B1587185 : Blo 834351 1587185 := bstep (se 2 (by rfl) ⟨595194, by rfl⟩ : syracuseStep 1587185 = 1190389) B1190389
theorem B1882097 : Blo 834351 1882097 := bstep (se 2 (by rfl) ⟨705786, by rfl⟩ : syracuseStep 1882097 = 1411573) B1411573
theorem B1882115 : Blo 834351 1882115 := bstep (se 1 (by rfl) ⟨1411586, by rfl⟩ : syracuseStep 1882115 = 2823173) B2823173
theorem B4765837 : Blo 834351 4765837 := bstep (se 3 (by rfl) ⟨893594, by rfl⟩ : syracuseStep 4765837 = 1787189) B1787189
theorem B1128659 : Blo 834351 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B1882385 : Blo 834351 1882385 := bstep (se 2 (by rfl) ⟨705894, by rfl⟩ : syracuseStep 1882385 = 1411789) B1411789
theorem B1882403 : Blo 834351 1882403 := bstep (se 1 (by rfl) ⟨1411802, by rfl⟩ : syracuseStep 1882403 = 2823605) B2823605
theorem B4962637 : Blo 834351 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B2111953 : Blo 834351 2111953 := bstep (se 2 (by rfl) ⟨791982, by rfl⟩ : syracuseStep 2111953 = 1583965) B1583965
theorem B1882673 : Blo 834351 1882673 := bstep (se 2 (by rfl) ⟨706002, by rfl⟩ : syracuseStep 1882673 = 1412005) B1412005
theorem B4241969 : Blo 834351 4241969 := bstep (se 2 (by rfl) ⟨1590738, by rfl⟩ : syracuseStep 4241969 = 3181477) B3181477
theorem B1784387 : Blo 834351 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B1882691 : Blo 834351 1882691 := bstep (se 1 (by rfl) ⟨1412018, by rfl⟩ : syracuseStep 1882691 = 2824037) B2824037
theorem B2112227 : Blo 834351 2112227 := bstep (se 1 (by rfl) ⟨1584170, by rfl⟩ : syracuseStep 2112227 = 3168341) B3168341
theorem B834355 : Blo 834351 834355 := bstep (se 1 (by rfl) ⟨625766, by rfl⟩ : syracuseStep 834355 = 1251533) B1251533
theorem B834371 : Blo 834351 834371 := bstep (se 1 (by rfl) ⟨625778, by rfl⟩ : syracuseStep 834371 = 1251557) B1251557
theorem B2538317 : Blo 834351 2538317 := bstep (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) B951869
theorem B1882961 : Blo 834351 1882961 := bstep (se 2 (by rfl) ⟨706110, by rfl⟩ : syracuseStep 1882961 = 1412221) B1412221
theorem B834387 : Blo 834351 834387 := bstep (se 1 (by rfl) ⟨625790, by rfl⟩ : syracuseStep 834387 = 1251581) B1251581
theorem B834403 : Blo 834351 834403 := bstep (se 1 (by rfl) ⟨625802, by rfl⟩ : syracuseStep 834403 = 1251605) B1251605
theorem B1882979 : Blo 834351 1882979 := bstep (se 1 (by rfl) ⟨1412234, by rfl⟩ : syracuseStep 1882979 = 2824469) B2824469
theorem B1588081 : Blo 834351 1588081 := bstep (se 2 (by rfl) ⟨595530, by rfl⟩ : syracuseStep 1588081 = 1191061) B1191061
theorem B834419 : Blo 834351 834419 := bstep (se 1 (by rfl) ⟨625814, by rfl⟩ : syracuseStep 834419 = 1251629) B1251629
theorem B834435 : Blo 834351 834435 := bstep (se 1 (by rfl) ⟨625826, by rfl⟩ : syracuseStep 834435 = 1251653) B1251653
theorem B834451 : Blo 834351 834451 := bstep (se 1 (by rfl) ⟨625838, by rfl⟩ : syracuseStep 834451 = 1251677) B1251677
theorem B834467 : Blo 834351 834467 := bstep (se 1 (by rfl) ⟨625850, by rfl⟩ : syracuseStep 834467 = 1251701) B1251701
theorem B2112419 : Blo 834351 2112419 := bstep (se 1 (by rfl) ⟨1584314, by rfl⟩ : syracuseStep 2112419 = 3168629) B3168629
theorem B834483 : Blo 834351 834483 := bstep (se 1 (by rfl) ⟨625862, by rfl⟩ : syracuseStep 834483 = 1251725) B1251725
theorem B834499 : Blo 834351 834499 := bstep (se 1 (by rfl) ⟨625874, by rfl⟩ : syracuseStep 834499 = 1251749) B1251749
theorem B1129411 : Blo 834351 1129411 := bstep (se 1 (by rfl) ⟨847058, by rfl⟩ : syracuseStep 1129411 = 1694117) B1694117
theorem B834515 : Blo 834351 834515 := bstep (se 1 (by rfl) ⟨625886, by rfl⟩ : syracuseStep 834515 = 1251773) B1251773
theorem B834531 : Blo 834351 834531 := bstep (se 1 (by rfl) ⟨625898, by rfl⟩ : syracuseStep 834531 = 1251797) B1251797
theorem B4013027 : Blo 834351 4013027 := bstep (se 1 (by rfl) ⟨3009770, by rfl⟩ : syracuseStep 4013027 = 6019541) B6019541
theorem B2014193 : Blo 834351 2014193 := bstep (se 2 (by rfl) ⟨755322, by rfl⟩ : syracuseStep 2014193 = 1510645) B1510645
theorem B834547 : Blo 834351 834547 := bstep (se 1 (by rfl) ⟨625910, by rfl⟩ : syracuseStep 834547 = 1251821) B1251821
theorem B834563 : Blo 834351 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B1588241 : Blo 834351 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B834579 : Blo 834351 834579 := bstep (se 1 (by rfl) ⟨625934, by rfl⟩ : syracuseStep 834579 = 1251869) B1251869
theorem B834595 : Blo 834351 834595 := bstep (se 1 (by rfl) ⟨625946, by rfl⟩ : syracuseStep 834595 = 1251893) B1251893
theorem B834611 : Blo 834351 834611 := bstep (se 1 (by rfl) ⟨625958, by rfl⟩ : syracuseStep 834611 = 1251917) B1251917
theorem B834627 : Blo 834351 834627 := bstep (se 1 (by rfl) ⟨625970, by rfl⟩ : syracuseStep 834627 = 1251941) B1251941
theorem B834643 : Blo 834351 834643 := bstep (se 1 (by rfl) ⟨625982, by rfl⟩ : syracuseStep 834643 = 1251965) B1251965
theorem B834659 : Blo 834351 834659 := bstep (se 1 (by rfl) ⟨625994, by rfl⟩ : syracuseStep 834659 = 1251989) B1251989
theorem B1883249 : Blo 834351 1883249 := bstep (se 2 (by rfl) ⟨706218, by rfl⟩ : syracuseStep 1883249 = 1412437) B1412437
theorem B834675 : Blo 834351 834675 := bstep (se 1 (by rfl) ⟨626006, by rfl⟩ : syracuseStep 834675 = 1252013) B1252013
theorem B834691 : Blo 834351 834691 := bstep (se 1 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 834691 = 1252037) B1252037
theorem B1883267 : Blo 834351 1883267 := bstep (se 1 (by rfl) ⟨1412450, by rfl⟩ : syracuseStep 1883267 = 2824901) B2824901
theorem B834707 : Blo 834351 834707 := bstep (se 1 (by rfl) ⟨626030, by rfl⟩ : syracuseStep 834707 = 1252061) B1252061
theorem B834723 : Blo 834351 834723 := bstep (se 1 (by rfl) ⟨626042, by rfl⟩ : syracuseStep 834723 = 1252085) B1252085
theorem B834739 : Blo 834351 834739 := bstep (se 1 (by rfl) ⟨626054, by rfl⟩ : syracuseStep 834739 = 1252109) B1252109
theorem B834755 : Blo 834351 834755 := bstep (se 1 (by rfl) ⟨626066, by rfl⟩ : syracuseStep 834755 = 1252133) B1252133
theorem B834771 : Blo 834351 834771 := bstep (se 1 (by rfl) ⟨626078, by rfl⟩ : syracuseStep 834771 = 1252157) B1252157
theorem B834787 : Blo 834351 834787 := bstep (se 1 (by rfl) ⟨626090, by rfl⟩ : syracuseStep 834787 = 1252181) B1252181
theorem B834803 : Blo 834351 834803 := bstep (se 1 (by rfl) ⟨626102, by rfl⟩ : syracuseStep 834803 = 1252205) B1252205
theorem B834819 : Blo 834351 834819 := bstep (se 1 (by rfl) ⟨626114, by rfl⟩ : syracuseStep 834819 = 1252229) B1252229
theorem B1129745 : Blo 834351 1129745 := bstep (se 2 (by rfl) ⟨423654, by rfl⟩ : syracuseStep 1129745 = 847309) B847309
theorem B834835 : Blo 834351 834835 := bstep (se 1 (by rfl) ⟨626126, by rfl⟩ : syracuseStep 834835 = 1252253) B1252253
theorem B834851 : Blo 834351 834851 := bstep (se 1 (by rfl) ⟨626138, by rfl⟩ : syracuseStep 834851 = 1252277) B1252277
theorem B2145571 : Blo 834351 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B834867 : Blo 834351 834867 := bstep (se 1 (by rfl) ⟨626150, by rfl⟩ : syracuseStep 834867 = 1252301) B1252301
theorem B834883 : Blo 834351 834883 := bstep (se 1 (by rfl) ⟨626162, by rfl⟩ : syracuseStep 834883 = 1252325) B1252325
theorem B834899 : Blo 834351 834899 := bstep (se 1 (by rfl) ⟨626174, by rfl⟩ : syracuseStep 834899 = 1252349) B1252349
theorem B834915 : Blo 834351 834915 := bstep (se 1 (by rfl) ⟨626186, by rfl⟩ : syracuseStep 834915 = 1252373) B1252373
theorem B834931 : Blo 834351 834931 := bstep (se 1 (by rfl) ⟨626198, by rfl⟩ : syracuseStep 834931 = 1252397) B1252397
theorem B834947 : Blo 834351 834947 := bstep (se 1 (by rfl) ⟨626210, by rfl⟩ : syracuseStep 834947 = 1252421) B1252421
theorem B1883537 : Blo 834351 1883537 := bstep (se 2 (by rfl) ⟨706326, by rfl⟩ : syracuseStep 1883537 = 1412653) B1412653
theorem B834963 : Blo 834351 834963 := bstep (se 1 (by rfl) ⟨626222, by rfl⟩ : syracuseStep 834963 = 1252445) B1252445
theorem B1883555 : Blo 834351 1883555 := bstep (se 1 (by rfl) ⟨1412666, by rfl⟩ : syracuseStep 1883555 = 2825333) B2825333
theorem B834979 : Blo 834351 834979 := bstep (se 1 (by rfl) ⟨626234, by rfl⟩ : syracuseStep 834979 = 1252469) B1252469
theorem B1588643 : Blo 834351 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B834995 : Blo 834351 834995 := bstep (se 1 (by rfl) ⟨626246, by rfl⟩ : syracuseStep 834995 = 1252493) B1252493
theorem B835011 : Blo 834351 835011 := bstep (se 1 (by rfl) ⟨626258, by rfl⟩ : syracuseStep 835011 = 1252517) B1252517
theorem B2178499 : Blo 834351 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B835027 : Blo 834351 835027 := bstep (se 1 (by rfl) ⟨626270, by rfl⟩ : syracuseStep 835027 = 1252541) B1252541
theorem B835043 : Blo 834351 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B835059 : Blo 834351 835059 := bstep (se 1 (by rfl) ⟨626294, by rfl⟩ : syracuseStep 835059 = 1252589) B1252589
theorem B835075 : Blo 834351 835075 := bstep (se 1 (by rfl) ⟨626306, by rfl⟩ : syracuseStep 835075 = 1252613) B1252613
theorem B835091 : Blo 834351 835091 := bstep (se 1 (by rfl) ⟨626318, by rfl⟩ : syracuseStep 835091 = 1252637) B1252637
theorem B835107 : Blo 834351 835107 := bstep (se 1 (by rfl) ⟨626330, by rfl⟩ : syracuseStep 835107 = 1252661) B1252661
theorem B835123 : Blo 834351 835123 := bstep (se 1 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 835123 = 1252685) B1252685
theorem B835139 : Blo 834351 835139 := bstep (se 1 (by rfl) ⟨626354, by rfl⟩ : syracuseStep 835139 = 1252709) B1252709
theorem B835155 : Blo 834351 835155 := bstep (se 1 (by rfl) ⟨626366, by rfl⟩ : syracuseStep 835155 = 1252733) B1252733
theorem B835171 : Blo 834351 835171 := bstep (se 1 (by rfl) ⟨626378, by rfl⟩ : syracuseStep 835171 = 1252757) B1252757
theorem B835187 : Blo 834351 835187 := bstep (se 1 (by rfl) ⟨626390, by rfl⟩ : syracuseStep 835187 = 1252781) B1252781
theorem B835203 : Blo 834351 835203 := bstep (se 1 (by rfl) ⟨626402, by rfl⟩ : syracuseStep 835203 = 1252805) B1252805
theorem B835219 : Blo 834351 835219 := bstep (se 1 (by rfl) ⟨626414, by rfl⟩ : syracuseStep 835219 = 1252829) B1252829
theorem B835235 : Blo 834351 835235 := bstep (se 1 (by rfl) ⟨626426, by rfl⟩ : syracuseStep 835235 = 1252853) B1252853
theorem B1883825 : Blo 834351 1883825 := bstep (se 2 (by rfl) ⟨706434, by rfl⟩ : syracuseStep 1883825 = 1412869) B1412869
theorem B835251 : Blo 834351 835251 := bstep (se 1 (by rfl) ⟨626438, by rfl⟩ : syracuseStep 835251 = 1252877) B1252877
theorem B835267 : Blo 834351 835267 := bstep (se 1 (by rfl) ⟨626450, by rfl⟩ : syracuseStep 835267 = 1252901) B1252901
theorem B1883843 : Blo 834351 1883843 := bstep (se 1 (by rfl) ⟨1412882, by rfl⟩ : syracuseStep 1883843 = 2825765) B2825765
theorem B835283 : Blo 834351 835283 := bstep (se 1 (by rfl) ⟨626462, by rfl⟩ : syracuseStep 835283 = 1252925) B1252925
theorem B4013795 : Blo 834351 4013795 := bstep (se 1 (by rfl) ⟨3010346, by rfl⟩ : syracuseStep 4013795 = 6020693) B6020693
theorem B835299 : Blo 834351 835299 := bstep (se 1 (by rfl) ⟨626474, by rfl⟩ : syracuseStep 835299 = 1252949) B1252949
theorem B835315 : Blo 834351 835315 := bstep (se 1 (by rfl) ⟨626486, by rfl⟩ : syracuseStep 835315 = 1252973) B1252973
theorem B835331 : Blo 834351 835331 := bstep (se 1 (by rfl) ⟨626498, by rfl⟩ : syracuseStep 835331 = 1252997) B1252997
theorem B835347 : Blo 834351 835347 := bstep (se 1 (by rfl) ⟨626510, by rfl⟩ : syracuseStep 835347 = 1253021) B1253021
theorem B835363 : Blo 834351 835363 := bstep (se 1 (by rfl) ⟨626522, by rfl⟩ : syracuseStep 835363 = 1253045) B1253045
theorem B1785635 : Blo 834351 1785635 := bstep (se 1 (by rfl) ⟨1339226, by rfl⟩ : syracuseStep 1785635 = 2678453) B2678453
theorem B835379 : Blo 834351 835379 := bstep (se 1 (by rfl) ⟨626534, by rfl⟩ : syracuseStep 835379 = 1253069) B1253069
theorem B835395 : Blo 834351 835395 := bstep (se 1 (by rfl) ⟨626546, by rfl⟩ : syracuseStep 835395 = 1253093) B1253093
theorem B2113361 : Blo 834351 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B835411 : Blo 834351 835411 := bstep (se 1 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 835411 = 1253117) B1253117
theorem B835427 : Blo 834351 835427 := bstep (se 1 (by rfl) ⟨626570, by rfl⟩ : syracuseStep 835427 = 1253141) B1253141
theorem B835443 : Blo 834351 835443 := bstep (se 1 (by rfl) ⟨626582, by rfl⟩ : syracuseStep 835443 = 1253165) B1253165
theorem B2113411 : Blo 834351 2113411 := bstep (se 1 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 2113411 = 3170117) B3170117
theorem B835459 : Blo 834351 835459 := bstep (se 1 (by rfl) ⟨626594, by rfl⟩ : syracuseStep 835459 = 1253189) B1253189
theorem B835475 : Blo 834351 835475 := bstep (se 1 (by rfl) ⟨626606, by rfl⟩ : syracuseStep 835475 = 1253213) B1253213
theorem B835491 : Blo 834351 835491 := bstep (se 1 (by rfl) ⟨626618, by rfl⟩ : syracuseStep 835491 = 1253237) B1253237
theorem B835507 : Blo 834351 835507 := bstep (se 1 (by rfl) ⟨626630, by rfl⟩ : syracuseStep 835507 = 1253261) B1253261
theorem B835523 : Blo 834351 835523 := bstep (se 1 (by rfl) ⟨626642, by rfl⟩ : syracuseStep 835523 = 1253285) B1253285
theorem B1130449 : Blo 834351 1130449 := bstep (se 2 (by rfl) ⟨423918, by rfl⟩ : syracuseStep 1130449 = 847837) B847837
theorem B1884113 : Blo 834351 1884113 := bstep (se 2 (by rfl) ⟨706542, by rfl⟩ : syracuseStep 1884113 = 1413085) B1413085
theorem B835539 : Blo 834351 835539 := bstep (se 1 (by rfl) ⟨626654, by rfl⟩ : syracuseStep 835539 = 1253309) B1253309
theorem B835555 : Blo 834351 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B1884131 : Blo 834351 1884131 := bstep (se 1 (by rfl) ⟨1413098, by rfl⟩ : syracuseStep 1884131 = 2826197) B2826197
theorem B4243427 : Blo 834351 4243427 := bstep (se 1 (by rfl) ⟨3182570, by rfl⟩ : syracuseStep 4243427 = 6365141) B6365141
theorem B835571 : Blo 834351 835571 := bstep (se 1 (by rfl) ⟨626678, by rfl⟩ : syracuseStep 835571 = 1253357) B1253357
theorem B835587 : Blo 834351 835587 := bstep (se 1 (by rfl) ⟨626690, by rfl⟩ : syracuseStep 835587 = 1253381) B1253381
theorem B2113553 : Blo 834351 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B835603 : Blo 834351 835603 := bstep (se 1 (by rfl) ⟨626702, by rfl⟩ : syracuseStep 835603 = 1253405) B1253405
theorem B835619 : Blo 834351 835619 := bstep (se 1 (by rfl) ⟨626714, by rfl⟩ : syracuseStep 835619 = 1253429) B1253429
theorem B835635 : Blo 834351 835635 := bstep (se 1 (by rfl) ⟨626726, by rfl⟩ : syracuseStep 835635 = 1253453) B1253453
theorem B835651 : Blo 834351 835651 := bstep (se 1 (by rfl) ⟨626738, by rfl⟩ : syracuseStep 835651 = 1253477) B1253477
theorem B4767821 : Blo 834351 4767821 := bstep (se 3 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 4767821 = 1787933) B1787933
theorem B835667 : Blo 834351 835667 := bstep (se 1 (by rfl) ⟨626750, by rfl⟩ : syracuseStep 835667 = 1253501) B1253501
theorem B835683 : Blo 834351 835683 := bstep (se 1 (by rfl) ⟨626762, by rfl⟩ : syracuseStep 835683 = 1253525) B1253525
theorem B835699 : Blo 834351 835699 := bstep (se 1 (by rfl) ⟨626774, by rfl⟩ : syracuseStep 835699 = 1253549) B1253549
theorem B835715 : Blo 834351 835715 := bstep (se 1 (by rfl) ⟨626786, by rfl⟩ : syracuseStep 835715 = 1253573) B1253573
theorem B835731 : Blo 834351 835731 := bstep (se 1 (by rfl) ⟨626798, by rfl⟩ : syracuseStep 835731 = 1253597) B1253597
theorem B835747 : Blo 834351 835747 := bstep (se 1 (by rfl) ⟨626810, by rfl⟩ : syracuseStep 835747 = 1253621) B1253621
theorem B835763 : Blo 834351 835763 := bstep (se 1 (by rfl) ⟨626822, by rfl⟩ : syracuseStep 835763 = 1253645) B1253645
theorem B835779 : Blo 834351 835779 := bstep (se 1 (by rfl) ⟨626834, by rfl⟩ : syracuseStep 835779 = 1253669) B1253669
theorem B5718221 : Blo 834351 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B835795 : Blo 834351 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B835811 : Blo 834351 835811 := bstep (se 1 (by rfl) ⟨626858, by rfl⟩ : syracuseStep 835811 = 1253717) B1253717
theorem B1884401 : Blo 834351 1884401 := bstep (se 2 (by rfl) ⟨706650, by rfl⟩ : syracuseStep 1884401 = 1413301) B1413301
theorem B835827 : Blo 834351 835827 := bstep (se 1 (by rfl) ⟨626870, by rfl⟩ : syracuseStep 835827 = 1253741) B1253741
theorem B835843 : Blo 834351 835843 := bstep (se 1 (by rfl) ⟨626882, by rfl⟩ : syracuseStep 835843 = 1253765) B1253765
theorem B1884419 : Blo 834351 1884419 := bstep (se 1 (by rfl) ⟨1413314, by rfl⟩ : syracuseStep 1884419 = 2826629) B2826629
theorem B835859 : Blo 834351 835859 := bstep (se 1 (by rfl) ⟨626894, by rfl⟩ : syracuseStep 835859 = 1253789) B1253789
theorem B835875 : Blo 834351 835875 := bstep (se 1 (by rfl) ⟨626906, by rfl⟩ : syracuseStep 835875 = 1253813) B1253813
theorem B1589539 : Blo 834351 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B835891 : Blo 834351 835891 := bstep (se 1 (by rfl) ⟨626918, by rfl⟩ : syracuseStep 835891 = 1253837) B1253837
theorem B835907 : Blo 834351 835907 := bstep (se 1 (by rfl) ⟨626930, by rfl⟩ : syracuseStep 835907 = 1253861) B1253861
theorem B4538701 : Blo 834351 4538701 := bstep (se 3 (by rfl) ⟨851006, by rfl⟩ : syracuseStep 4538701 = 1702013) B1702013
theorem B2376017 : Blo 834351 2376017 := bstep (se 2 (by rfl) ⟨891006, by rfl⟩ : syracuseStep 2376017 = 1782013) B1782013
theorem B835923 : Blo 834351 835923 := bstep (se 1 (by rfl) ⟨626942, by rfl⟩ : syracuseStep 835923 = 1253885) B1253885
theorem B835939 : Blo 834351 835939 := bstep (se 1 (by rfl) ⟨626954, by rfl⟩ : syracuseStep 835939 = 1253909) B1253909
theorem B1786225 : Blo 834351 1786225 := bstep (se 2 (by rfl) ⟨669834, by rfl⟩ : syracuseStep 1786225 = 1339669) B1339669
theorem B835955 : Blo 834351 835955 := bstep (se 1 (by rfl) ⟨626966, by rfl⟩ : syracuseStep 835955 = 1253933) B1253933
theorem B835971 : Blo 834351 835971 := bstep (se 1 (by rfl) ⟨626978, by rfl⟩ : syracuseStep 835971 = 1253957) B1253957
theorem B835987 : Blo 834351 835987 := bstep (se 1 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 835987 = 1253981) B1253981
theorem B836003 : Blo 834351 836003 := bstep (se 1 (by rfl) ⟨627002, by rfl⟩ : syracuseStep 836003 = 1254005) B1254005
theorem B836019 : Blo 834351 836019 := bstep (se 1 (by rfl) ⟨627014, by rfl⟩ : syracuseStep 836019 = 1254029) B1254029
theorem B836035 : Blo 834351 836035 := bstep (se 1 (by rfl) ⟨627026, by rfl⟩ : syracuseStep 836035 = 1254053) B1254053
theorem B1589699 : Blo 834351 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B836051 : Blo 834351 836051 := bstep (se 1 (by rfl) ⟨627038, by rfl⟩ : syracuseStep 836051 = 1254077) B1254077
theorem B836067 : Blo 834351 836067 := bstep (se 1 (by rfl) ⟨627050, by rfl⟩ : syracuseStep 836067 = 1254101) B1254101
theorem B836083 : Blo 834351 836083 := bstep (se 1 (by rfl) ⟨627062, by rfl⟩ : syracuseStep 836083 = 1254125) B1254125
theorem B836099 : Blo 834351 836099 := bstep (se 1 (by rfl) ⟨627074, by rfl⟩ : syracuseStep 836099 = 1254149) B1254149
theorem B1884689 : Blo 834351 1884689 := bstep (se 2 (by rfl) ⟨706758, by rfl⟩ : syracuseStep 1884689 = 1413517) B1413517
theorem B836115 : Blo 834351 836115 := bstep (se 1 (by rfl) ⟨627086, by rfl⟩ : syracuseStep 836115 = 1254173) B1254173
theorem B836131 : Blo 834351 836131 := bstep (se 1 (by rfl) ⟨627098, by rfl⟩ : syracuseStep 836131 = 1254197) B1254197
theorem B1884707 : Blo 834351 1884707 := bstep (se 1 (by rfl) ⟨1413530, by rfl⟩ : syracuseStep 1884707 = 2827061) B2827061
theorem B836147 : Blo 834351 836147 := bstep (se 1 (by rfl) ⟨627110, by rfl⟩ : syracuseStep 836147 = 1254221) B1254221
theorem B836163 : Blo 834351 836163 := bstep (se 1 (by rfl) ⟨627122, by rfl⟩ : syracuseStep 836163 = 1254245) B1254245
theorem B836179 : Blo 834351 836179 := bstep (se 1 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 836179 = 1254269) B1254269
theorem B836195 : Blo 834351 836195 := bstep (se 1 (by rfl) ⟨627146, by rfl⟩ : syracuseStep 836195 = 1254293) B1254293
theorem B836211 : Blo 834351 836211 := bstep (se 1 (by rfl) ⟨627158, by rfl⟩ : syracuseStep 836211 = 1254317) B1254317
theorem B836227 : Blo 834351 836227 := bstep (se 1 (by rfl) ⟨627170, by rfl⟩ : syracuseStep 836227 = 1254341) B1254341
theorem B836243 : Blo 834351 836243 := bstep (se 1 (by rfl) ⟨627182, by rfl⟩ : syracuseStep 836243 = 1254365) B1254365
theorem B836259 : Blo 834351 836259 := bstep (se 1 (by rfl) ⟨627194, by rfl⟩ : syracuseStep 836259 = 1254389) B1254389
theorem B836275 : Blo 834351 836275 := bstep (se 1 (by rfl) ⟨627206, by rfl⟩ : syracuseStep 836275 = 1254413) B1254413
theorem B836291 : Blo 834351 836291 := bstep (se 1 (by rfl) ⟨627218, by rfl⟩ : syracuseStep 836291 = 1254437) B1254437
theorem B836307 : Blo 834351 836307 := bstep (se 1 (by rfl) ⟨627230, by rfl⟩ : syracuseStep 836307 = 1254461) B1254461
theorem B836323 : Blo 834351 836323 := bstep (se 1 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 836323 = 1254485) B1254485
theorem B836339 : Blo 834351 836339 := bstep (se 1 (by rfl) ⟨627254, by rfl⟩ : syracuseStep 836339 = 1254509) B1254509
theorem B836355 : Blo 834351 836355 := bstep (se 1 (by rfl) ⟨627266, by rfl⟩ : syracuseStep 836355 = 1254533) B1254533
theorem B836371 : Blo 834351 836371 := bstep (se 1 (by rfl) ⟨627278, by rfl⟩ : syracuseStep 836371 = 1254557) B1254557
theorem B836387 : Blo 834351 836387 := bstep (se 1 (by rfl) ⟨627290, by rfl⟩ : syracuseStep 836387 = 1254581) B1254581
theorem B1884977 : Blo 834351 1884977 := bstep (se 2 (by rfl) ⟨706866, by rfl⟩ : syracuseStep 1884977 = 1413733) B1413733
theorem B836403 : Blo 834351 836403 := bstep (se 1 (by rfl) ⟨627302, by rfl⟩ : syracuseStep 836403 = 1254605) B1254605
theorem B836419 : Blo 834351 836419 := bstep (se 1 (by rfl) ⟨627314, by rfl⟩ : syracuseStep 836419 = 1254629) B1254629
theorem B1884995 : Blo 834351 1884995 := bstep (se 1 (by rfl) ⟨1413746, by rfl⟩ : syracuseStep 1884995 = 2827493) B2827493
theorem B836435 : Blo 834351 836435 := bstep (se 1 (by rfl) ⟨627326, by rfl⟩ : syracuseStep 836435 = 1254653) B1254653
theorem B836451 : Blo 834351 836451 := bstep (se 1 (by rfl) ⟨627338, by rfl⟩ : syracuseStep 836451 = 1254677) B1254677
theorem B836467 : Blo 834351 836467 := bstep (se 1 (by rfl) ⟨627350, by rfl⟩ : syracuseStep 836467 = 1254701) B1254701
theorem B836483 : Blo 834351 836483 := bstep (se 1 (by rfl) ⟨627362, by rfl⟩ : syracuseStep 836483 = 1254725) B1254725
theorem B836499 : Blo 834351 836499 := bstep (se 1 (by rfl) ⟨627374, by rfl⟩ : syracuseStep 836499 = 1254749) B1254749
theorem B836515 : Blo 834351 836515 := bstep (se 1 (by rfl) ⟨627386, by rfl⟩ : syracuseStep 836515 = 1254773) B1254773
theorem B4015025 : Blo 834351 4015025 := bstep (se 2 (by rfl) ⟨1505634, by rfl⟩ : syracuseStep 4015025 = 3011269) B3011269
theorem B836531 : Blo 834351 836531 := bstep (se 1 (by rfl) ⟨627398, by rfl⟩ : syracuseStep 836531 = 1254797) B1254797
theorem B836547 : Blo 834351 836547 := bstep (se 1 (by rfl) ⟨627410, by rfl⟩ : syracuseStep 836547 = 1254821) B1254821
theorem B836563 : Blo 834351 836563 := bstep (se 1 (by rfl) ⟨627422, by rfl⟩ : syracuseStep 836563 = 1254845) B1254845
theorem B836579 : Blo 834351 836579 := bstep (se 1 (by rfl) ⟨627434, by rfl⟩ : syracuseStep 836579 = 1254869) B1254869
theorem B2114545 : Blo 834351 2114545 := bstep (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) B1585909
theorem B4768753 : Blo 834351 4768753 := bstep (se 2 (by rfl) ⟨1788282, by rfl⟩ : syracuseStep 4768753 = 3576565) B3576565
theorem B836595 : Blo 834351 836595 := bstep (se 1 (by rfl) ⟨627446, by rfl⟩ : syracuseStep 836595 = 1254893) B1254893
theorem B836611 : Blo 834351 836611 := bstep (se 1 (by rfl) ⟨627458, by rfl⟩ : syracuseStep 836611 = 1254917) B1254917
theorem B836627 : Blo 834351 836627 := bstep (se 1 (by rfl) ⟨627470, by rfl⟩ : syracuseStep 836627 = 1254941) B1254941
theorem B836643 : Blo 834351 836643 := bstep (se 1 (by rfl) ⟨627482, by rfl⟩ : syracuseStep 836643 = 1254965) B1254965
theorem B836659 : Blo 834351 836659 := bstep (se 1 (by rfl) ⟨627494, by rfl⟩ : syracuseStep 836659 = 1254989) B1254989
theorem B836675 : Blo 834351 836675 := bstep (se 1 (by rfl) ⟨627506, by rfl⟩ : syracuseStep 836675 = 1255013) B1255013
theorem B1885265 : Blo 834351 1885265 := bstep (se 2 (by rfl) ⟨706974, by rfl⟩ : syracuseStep 1885265 = 1413949) B1413949
theorem B836691 : Blo 834351 836691 := bstep (se 1 (by rfl) ⟨627518, by rfl⟩ : syracuseStep 836691 = 1255037) B1255037
theorem B2376803 : Blo 834351 2376803 := bstep (se 1 (by rfl) ⟨1782602, by rfl⟩ : syracuseStep 2376803 = 3565205) B3565205
theorem B836707 : Blo 834351 836707 := bstep (se 1 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 836707 = 1255061) B1255061
theorem B1885283 : Blo 834351 1885283 := bstep (se 1 (by rfl) ⟨1413962, by rfl⟩ : syracuseStep 1885283 = 2827925) B2827925
theorem B836723 : Blo 834351 836723 := bstep (se 1 (by rfl) ⟨627542, by rfl⟩ : syracuseStep 836723 = 1255085) B1255085
theorem B836739 : Blo 834351 836739 := bstep (se 1 (by rfl) ⟨627554, by rfl⟩ : syracuseStep 836739 = 1255109) B1255109
theorem B836755 : Blo 834351 836755 := bstep (se 1 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 836755 = 1255133) B1255133
theorem B836771 : Blo 834351 836771 := bstep (se 1 (by rfl) ⟨627578, by rfl⟩ : syracuseStep 836771 = 1255157) B1255157
theorem B836787 : Blo 834351 836787 := bstep (se 1 (by rfl) ⟨627590, by rfl⟩ : syracuseStep 836787 = 1255181) B1255181
theorem B836803 : Blo 834351 836803 := bstep (se 1 (by rfl) ⟨627602, by rfl⟩ : syracuseStep 836803 = 1255205) B1255205
theorem B836819 : Blo 834351 836819 := bstep (se 1 (by rfl) ⟨627614, by rfl⟩ : syracuseStep 836819 = 1255229) B1255229
theorem B836835 : Blo 834351 836835 := bstep (se 1 (by rfl) ⟨627626, by rfl⟩ : syracuseStep 836835 = 1255253) B1255253
theorem B836851 : Blo 834351 836851 := bstep (se 1 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 836851 = 1255277) B1255277
theorem B2114819 : Blo 834351 2114819 := bstep (se 1 (by rfl) ⟨1586114, by rfl⟩ : syracuseStep 2114819 = 3172229) B3172229
theorem B836867 : Blo 834351 836867 := bstep (se 1 (by rfl) ⟨627650, by rfl⟩ : syracuseStep 836867 = 1255301) B1255301
theorem B836883 : Blo 834351 836883 := bstep (se 1 (by rfl) ⟨627662, by rfl⟩ : syracuseStep 836883 = 1255325) B1255325
theorem B836899 : Blo 834351 836899 := bstep (se 1 (by rfl) ⟨627674, by rfl⟩ : syracuseStep 836899 = 1255349) B1255349
theorem B836915 : Blo 834351 836915 := bstep (se 1 (by rfl) ⟨627686, by rfl⟩ : syracuseStep 836915 = 1255373) B1255373
theorem B836931 : Blo 834351 836931 := bstep (se 1 (by rfl) ⟨627698, by rfl⟩ : syracuseStep 836931 = 1255397) B1255397
theorem B836947 : Blo 834351 836947 := bstep (se 1 (by rfl) ⟨627710, by rfl⟩ : syracuseStep 836947 = 1255421) B1255421
theorem B836963 : Blo 834351 836963 := bstep (se 1 (by rfl) ⟨627722, by rfl⟩ : syracuseStep 836963 = 1255445) B1255445
theorem B1131875 : Blo 834351 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B1885553 : Blo 834351 1885553 := bstep (se 2 (by rfl) ⟨707082, by rfl⟩ : syracuseStep 1885553 = 1414165) B1414165
theorem B836979 : Blo 834351 836979 := bstep (se 1 (by rfl) ⟨627734, by rfl⟩ : syracuseStep 836979 = 1255469) B1255469
theorem B836995 : Blo 834351 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B1885571 : Blo 834351 1885571 := bstep (se 1 (by rfl) ⟨1414178, by rfl⟩ : syracuseStep 1885571 = 2828357) B2828357
theorem B2540945 : Blo 834351 2540945 := bstep (se 2 (by rfl) ⟨952854, by rfl⟩ : syracuseStep 2540945 = 1905709) B1905709
theorem B837011 : Blo 834351 837011 := bstep (se 1 (by rfl) ⟨627758, by rfl⟩ : syracuseStep 837011 = 1255517) B1255517
theorem B5293475 : Blo 834351 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B837027 : Blo 834351 837027 := bstep (se 1 (by rfl) ⟨627770, by rfl⟩ : syracuseStep 837027 = 1255541) B1255541
theorem B2377133 : Blo 834351 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B837043 : Blo 834351 837043 := bstep (se 1 (by rfl) ⟨627782, by rfl⟩ : syracuseStep 837043 = 1255565) B1255565
theorem B2115011 : Blo 834351 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B837059 : Blo 834351 837059 := bstep (se 1 (by rfl) ⟨627794, by rfl⟩ : syracuseStep 837059 = 1255589) B1255589
theorem B4015565 : Blo 834351 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B837075 : Blo 834351 837075 := bstep (se 1 (by rfl) ⟨627806, by rfl⟩ : syracuseStep 837075 = 1255613) B1255613
theorem B837091 : Blo 834351 837091 := bstep (se 1 (by rfl) ⟨627818, by rfl⟩ : syracuseStep 837091 = 1255637) B1255637
theorem B2377201 : Blo 834351 2377201 := bstep (se 2 (by rfl) ⟨891450, by rfl⟩ : syracuseStep 2377201 = 1782901) B1782901
theorem B2541041 : Blo 834351 2541041 := bstep (se 2 (by rfl) ⟨952890, by rfl⟩ : syracuseStep 2541041 = 1905781) B1905781
theorem B837107 : Blo 834351 837107 := bstep (se 1 (by rfl) ⟨627830, by rfl⟩ : syracuseStep 837107 = 1255661) B1255661
theorem B1590769 : Blo 834351 1590769 := bstep (se 2 (by rfl) ⟨596538, by rfl⟩ : syracuseStep 1590769 = 1193077) B1193077
theorem B837123 : Blo 834351 837123 := bstep (se 1 (by rfl) ⟨627842, by rfl⟩ : syracuseStep 837123 = 1255685) B1255685
theorem B837139 : Blo 834351 837139 := bstep (se 1 (by rfl) ⟨627854, by rfl⟩ : syracuseStep 837139 = 1255709) B1255709
theorem B837155 : Blo 834351 837155 := bstep (se 1 (by rfl) ⟨627866, by rfl⟩ : syracuseStep 837155 = 1255733) B1255733
theorem B837171 : Blo 834351 837171 := bstep (se 1 (by rfl) ⟨627878, by rfl⟩ : syracuseStep 837171 = 1255757) B1255757
theorem B837187 : Blo 834351 837187 := bstep (se 1 (by rfl) ⟨627890, by rfl⟩ : syracuseStep 837187 = 1255781) B1255781
theorem B837203 : Blo 834351 837203 := bstep (se 1 (by rfl) ⟨627902, by rfl⟩ : syracuseStep 837203 = 1255805) B1255805
theorem B9520739 : Blo 834351 9520739 := bstep (se 1 (by rfl) ⟨7140554, by rfl⟩ : syracuseStep 9520739 = 14281109) B14281109
theorem B837219 : Blo 834351 837219 := bstep (se 1 (by rfl) ⟨627914, by rfl⟩ : syracuseStep 837219 = 1255829) B1255829
theorem B837235 : Blo 834351 837235 := bstep (se 1 (by rfl) ⟨627926, by rfl⟩ : syracuseStep 837235 = 1255853) B1255853
theorem B837251 : Blo 834351 837251 := bstep (se 1 (by rfl) ⟨627938, by rfl⟩ : syracuseStep 837251 = 1255877) B1255877
theorem B1885841 : Blo 834351 1885841 := bstep (se 2 (by rfl) ⟨707190, by rfl⟩ : syracuseStep 1885841 = 1414381) B1414381
theorem B837267 : Blo 834351 837267 := bstep (se 1 (by rfl) ⟨627950, by rfl⟩ : syracuseStep 837267 = 1255901) B1255901
theorem B837283 : Blo 834351 837283 := bstep (se 1 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 837283 = 1255925) B1255925
theorem B1885859 : Blo 834351 1885859 := bstep (se 1 (by rfl) ⟨1414394, by rfl⟩ : syracuseStep 1885859 = 2828789) B2828789
theorem B837299 : Blo 834351 837299 := bstep (se 1 (by rfl) ⟨627974, by rfl⟩ : syracuseStep 837299 = 1255949) B1255949
theorem B837315 : Blo 834351 837315 := bstep (se 1 (by rfl) ⟨627986, by rfl⟩ : syracuseStep 837315 = 1255973) B1255973
theorem B837331 : Blo 834351 837331 := bstep (se 1 (by rfl) ⟨627998, by rfl⟩ : syracuseStep 837331 = 1255997) B1255997
theorem B837347 : Blo 834351 837347 := bstep (se 1 (by rfl) ⟨628010, by rfl⟩ : syracuseStep 837347 = 1256021) B1256021
theorem B837363 : Blo 834351 837363 := bstep (se 1 (by rfl) ⟨628022, by rfl⟩ : syracuseStep 837363 = 1256045) B1256045
theorem B2377475 : Blo 834351 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B837379 : Blo 834351 837379 := bstep (se 1 (by rfl) ⟨628034, by rfl⟩ : syracuseStep 837379 = 1256069) B1256069
theorem B837395 : Blo 834351 837395 := bstep (se 1 (by rfl) ⟨628046, by rfl⟩ : syracuseStep 837395 = 1256093) B1256093
theorem B837411 : Blo 834351 837411 := bstep (se 1 (by rfl) ⟨628058, by rfl⟩ : syracuseStep 837411 = 1256117) B1256117
theorem B837427 : Blo 834351 837427 := bstep (se 1 (by rfl) ⟨628070, by rfl⟩ : syracuseStep 837427 = 1256141) B1256141
theorem B837443 : Blo 834351 837443 := bstep (se 1 (by rfl) ⟨628082, by rfl⟩ : syracuseStep 837443 = 1256165) B1256165
theorem B837459 : Blo 834351 837459 := bstep (se 1 (by rfl) ⟨628094, by rfl⟩ : syracuseStep 837459 = 1256189) B1256189
theorem B837475 : Blo 834351 837475 := bstep (se 1 (by rfl) ⟨628106, by rfl⟩ : syracuseStep 837475 = 1256213) B1256213
theorem B837491 : Blo 834351 837491 := bstep (se 1 (by rfl) ⟨628118, by rfl⟩ : syracuseStep 837491 = 1256237) B1256237
theorem B837507 : Blo 834351 837507 := bstep (se 1 (by rfl) ⟨628130, by rfl⟩ : syracuseStep 837507 = 1256261) B1256261
theorem B837523 : Blo 834351 837523 := bstep (se 1 (by rfl) ⟨628142, by rfl⟩ : syracuseStep 837523 = 1256285) B1256285
theorem B837539 : Blo 834351 837539 := bstep (se 1 (by rfl) ⟨628154, by rfl⟩ : syracuseStep 837539 = 1256309) B1256309
theorem B1886129 : Blo 834351 1886129 := bstep (se 2 (by rfl) ⟨707298, by rfl⟩ : syracuseStep 1886129 = 1414597) B1414597
theorem B837555 : Blo 834351 837555 := bstep (se 1 (by rfl) ⟨628166, by rfl⟩ : syracuseStep 837555 = 1256333) B1256333
theorem B837571 : Blo 834351 837571 := bstep (se 1 (by rfl) ⟨628178, by rfl⟩ : syracuseStep 837571 = 1256357) B1256357
theorem B1886147 : Blo 834351 1886147 := bstep (se 1 (by rfl) ⟨1414610, by rfl⟩ : syracuseStep 1886147 = 2829221) B2829221
theorem B837587 : Blo 834351 837587 := bstep (se 1 (by rfl) ⟨628190, by rfl⟩ : syracuseStep 837587 = 1256381) B1256381
theorem B837603 : Blo 834351 837603 := bstep (se 1 (by rfl) ⟨628202, by rfl⟩ : syracuseStep 837603 = 1256405) B1256405
theorem B7129073 : Blo 834351 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B903155 : Blo 834351 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B837619 : Blo 834351 837619 := bstep (se 1 (by rfl) ⟨628214, by rfl⟩ : syracuseStep 837619 = 1256429) B1256429
theorem B837635 : Blo 834351 837635 := bstep (se 1 (by rfl) ⟨628226, by rfl⟩ : syracuseStep 837635 = 1256453) B1256453
theorem B837651 : Blo 834351 837651 := bstep (se 1 (by rfl) ⟨628238, by rfl⟩ : syracuseStep 837651 = 1256477) B1256477
theorem B837667 : Blo 834351 837667 := bstep (se 1 (by rfl) ⟨628250, by rfl⟩ : syracuseStep 837667 = 1256501) B1256501
theorem B837683 : Blo 834351 837683 := bstep (se 1 (by rfl) ⟨628262, by rfl⟩ : syracuseStep 837683 = 1256525) B1256525
theorem B837699 : Blo 834351 837699 := bstep (se 1 (by rfl) ⟨628274, by rfl⟩ : syracuseStep 837699 = 1256549) B1256549
theorem B837715 : Blo 834351 837715 := bstep (se 1 (by rfl) ⟨628286, by rfl⟩ : syracuseStep 837715 = 1256573) B1256573
theorem B837731 : Blo 834351 837731 := bstep (se 1 (by rfl) ⟨628298, by rfl⟩ : syracuseStep 837731 = 1256597) B1256597
theorem B1132643 : Blo 834351 1132643 := bstep (se 1 (by rfl) ⟨849482, by rfl⟩ : syracuseStep 1132643 = 1698965) B1698965
theorem B837747 : Blo 834351 837747 := bstep (se 1 (by rfl) ⟨628310, by rfl⟩ : syracuseStep 837747 = 1256621) B1256621
theorem B837763 : Blo 834351 837763 := bstep (se 1 (by rfl) ⟨628322, by rfl⟩ : syracuseStep 837763 = 1256645) B1256645
theorem B837779 : Blo 834351 837779 := bstep (se 1 (by rfl) ⟨628334, by rfl⟩ : syracuseStep 837779 = 1256669) B1256669
theorem B837795 : Blo 834351 837795 := bstep (se 1 (by rfl) ⟨628346, by rfl⟩ : syracuseStep 837795 = 1256693) B1256693
theorem B837811 : Blo 834351 837811 := bstep (se 1 (by rfl) ⟨628358, by rfl⟩ : syracuseStep 837811 = 1256717) B1256717
theorem B837827 : Blo 834351 837827 := bstep (se 1 (by rfl) ⟨628370, by rfl⟩ : syracuseStep 837827 = 1256741) B1256741
theorem B837843 : Blo 834351 837843 := bstep (se 1 (by rfl) ⟨628382, by rfl⟩ : syracuseStep 837843 = 1256765) B1256765
theorem B837859 : Blo 834351 837859 := bstep (se 1 (by rfl) ⟨628394, by rfl⟩ : syracuseStep 837859 = 1256789) B1256789
theorem B837875 : Blo 834351 837875 := bstep (se 1 (by rfl) ⟨628406, by rfl⟩ : syracuseStep 837875 = 1256813) B1256813
theorem B837891 : Blo 834351 837891 := bstep (se 1 (by rfl) ⟨628418, by rfl⟩ : syracuseStep 837891 = 1256837) B1256837
theorem B837907 : Blo 834351 837907 := bstep (se 1 (by rfl) ⟨628430, by rfl⟩ : syracuseStep 837907 = 1256861) B1256861
theorem B837923 : Blo 834351 837923 := bstep (se 1 (by rfl) ⟨628442, by rfl⟩ : syracuseStep 837923 = 1256885) B1256885
theorem B837939 : Blo 834351 837939 := bstep (se 1 (by rfl) ⟨628454, by rfl⟩ : syracuseStep 837939 = 1256909) B1256909
theorem B837955 : Blo 834351 837955 := bstep (se 1 (by rfl) ⟨628466, by rfl⟩ : syracuseStep 837955 = 1256933) B1256933
theorem B837971 : Blo 834351 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B1427809 : Blo 834351 1427809 := bstep (se 2 (by rfl) ⟨535428, by rfl⟩ : syracuseStep 1427809 = 1070857) B1070857
theorem B837987 : Blo 834351 837987 := bstep (se 1 (by rfl) ⟨628490, by rfl⟩ : syracuseStep 837987 = 1256981) B1256981
theorem B2115953 : Blo 834351 2115953 := bstep (se 2 (by rfl) ⟨793482, by rfl⟩ : syracuseStep 2115953 = 1586965) B1586965
theorem B3393905 : Blo 834351 3393905 := bstep (se 2 (by rfl) ⟨1272714, by rfl⟩ : syracuseStep 3393905 = 2545429) B2545429
theorem B838003 : Blo 834351 838003 := bstep (se 1 (by rfl) ⟨628502, by rfl⟩ : syracuseStep 838003 = 1257005) B1257005
theorem B838019 : Blo 834351 838019 := bstep (se 1 (by rfl) ⟨628514, by rfl⟩ : syracuseStep 838019 = 1257029) B1257029
theorem B838035 : Blo 834351 838035 := bstep (se 1 (by rfl) ⟨628526, by rfl⟩ : syracuseStep 838035 = 1257053) B1257053
theorem B2116003 : Blo 834351 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B4770211 : Blo 834351 4770211 := bstep (se 1 (by rfl) ⟨3577658, by rfl⟩ : syracuseStep 4770211 = 7155317) B7155317
theorem B838051 : Blo 834351 838051 := bstep (se 1 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 838051 = 1257077) B1257077
theorem B838067 : Blo 834351 838067 := bstep (se 1 (by rfl) ⟨628550, by rfl⟩ : syracuseStep 838067 = 1257101) B1257101
theorem B838083 : Blo 834351 838083 := bstep (se 1 (by rfl) ⟨628562, by rfl⟩ : syracuseStep 838083 = 1257125) B1257125
theorem B838099 : Blo 834351 838099 := bstep (se 1 (by rfl) ⟨628574, by rfl⟩ : syracuseStep 838099 = 1257149) B1257149
theorem B838115 : Blo 834351 838115 := bstep (se 1 (by rfl) ⟨628586, by rfl⟩ : syracuseStep 838115 = 1257173) B1257173
theorem B838131 : Blo 834351 838131 := bstep (se 1 (by rfl) ⟨628598, by rfl⟩ : syracuseStep 838131 = 1257197) B1257197
theorem B838147 : Blo 834351 838147 := bstep (se 1 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 838147 = 1257221) B1257221
theorem B838163 : Blo 834351 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B838179 : Blo 834351 838179 := bstep (se 1 (by rfl) ⟨628634, by rfl⟩ : syracuseStep 838179 = 1257269) B1257269
theorem B2116145 : Blo 834351 2116145 := bstep (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) B1587109
theorem B838195 : Blo 834351 838195 := bstep (se 1 (by rfl) ⟨628646, by rfl⟩ : syracuseStep 838195 = 1257293) B1257293
theorem B838211 : Blo 834351 838211 := bstep (se 1 (by rfl) ⟨628658, by rfl⟩ : syracuseStep 838211 = 1257317) B1257317
theorem B2378317 : Blo 834351 2378317 := bstep (se 3 (by rfl) ⟨445934, by rfl⟩ : syracuseStep 2378317 = 891869) B891869
theorem B838227 : Blo 834351 838227 := bstep (se 1 (by rfl) ⟨628670, by rfl⟩ : syracuseStep 838227 = 1257341) B1257341
theorem B4082275 : Blo 834351 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B838243 : Blo 834351 838243 := bstep (se 1 (by rfl) ⟨628682, by rfl⟩ : syracuseStep 838243 = 1257365) B1257365
theorem B838259 : Blo 834351 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B838275 : Blo 834351 838275 := bstep (se 1 (by rfl) ⟨628706, by rfl⟩ : syracuseStep 838275 = 1257413) B1257413
theorem B838291 : Blo 834351 838291 := bstep (se 1 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 838291 = 1257437) B1257437
theorem B838307 : Blo 834351 838307 := bstep (se 1 (by rfl) ⟨628730, by rfl⟩ : syracuseStep 838307 = 1257461) B1257461
theorem B838323 : Blo 834351 838323 := bstep (se 1 (by rfl) ⟨628742, by rfl⟩ : syracuseStep 838323 = 1257485) B1257485
theorem B838339 : Blo 834351 838339 := bstep (se 1 (by rfl) ⟨628754, by rfl⟩ : syracuseStep 838339 = 1257509) B1257509
theorem B2378477 : Blo 834351 2378477 := bstep (se 3 (by rfl) ⟨445964, by rfl⟩ : syracuseStep 2378477 = 891929) B891929
theorem B2378659 : Blo 834351 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B1526705 : Blo 834351 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B4770737 : Blo 834351 4770737 := bstep (se 2 (by rfl) ⟨1789026, by rfl⟩ : syracuseStep 4770737 = 3578053) B3578053
theorem B4017485 : Blo 834351 4017485 := bstep (se 3 (by rfl) ⟨753278, by rfl⟩ : syracuseStep 4017485 = 1506557) B1506557
theorem B6016369 : Blo 834351 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B2674147 : Blo 834351 2674147 := bstep (se 1 (by rfl) ⟨2005610, by rfl⟩ : syracuseStep 2674147 = 4011221) B4011221
theorem B1789411 : Blo 834351 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B5361157 : Blo 834351 5361157 := bstep (se 4 (by rfl) ⟨502608, by rfl⟩ : syracuseStep 5361157 = 1005217) B1005217
theorem B2117137 : Blo 834351 2117137 := bstep (se 2 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 2117137 = 1587853) B1587853
theorem B2674417 : Blo 834351 2674417 := bstep (se 2 (by rfl) ⟨1002906, by rfl⟩ : syracuseStep 2674417 = 2005813) B2005813
theorem B2117411 : Blo 834351 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B2117603 : Blo 834351 2117603 := bstep (se 1 (by rfl) ⟨1588202, by rfl⟩ : syracuseStep 2117603 = 3176405) B3176405
theorem B1003603 : Blo 834351 1003603 := bstep (se 1 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 1003603 = 1505405) B1505405
theorem B2380049 : Blo 834351 2380049 := bstep (se 2 (by rfl) ⟨892518, by rfl⟩ : syracuseStep 2380049 = 1785037) B1785037
theorem B1790257 : Blo 834351 1790257 := bstep (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) B1342693
theorem B4772195 : Blo 834351 4772195 := bstep (se 1 (by rfl) ⟨3579146, by rfl⟩ : syracuseStep 4772195 = 7158293) B7158293
theorem B1003987 : Blo 834351 1003987 := bstep (se 1 (by rfl) ⟨752990, by rfl⟩ : syracuseStep 1003987 = 1505981) B1505981
theorem B5722595 : Blo 834351 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B938659 : Blo 834351 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B938803 : Blo 834351 938803 := bstep (se 1 (by rfl) ⟨704102, by rfl⟩ : syracuseStep 938803 = 1408205) B1408205
theorem B2118545 : Blo 834351 2118545 := bstep (se 2 (by rfl) ⟨794454, by rfl⟩ : syracuseStep 2118545 = 1588909) B1588909
theorem B938947 : Blo 834351 938947 := bstep (se 1 (by rfl) ⟨704210, by rfl⟩ : syracuseStep 938947 = 1408421) B1408421
theorem B2118595 : Blo 834351 2118595 := bstep (se 1 (by rfl) ⟨1588946, by rfl⟩ : syracuseStep 2118595 = 3177893) B3177893
theorem B1430561 : Blo 834351 1430561 := bstep (se 2 (by rfl) ⟨536460, by rfl⟩ : syracuseStep 1430561 = 1072921) B1072921
theorem B2118737 : Blo 834351 2118737 := bstep (se 2 (by rfl) ⟨794526, by rfl⟩ : syracuseStep 2118737 = 1589053) B1589053
theorem B939091 : Blo 834351 939091 := bstep (se 1 (by rfl) ⟨704318, by rfl⟩ : syracuseStep 939091 = 1408637) B1408637
theorem B2413667 : Blo 834351 2413667 := bstep (se 1 (by rfl) ⟨1810250, by rfl⟩ : syracuseStep 2413667 = 3620501) B3620501
theorem B2381005 : Blo 834351 2381005 := bstep (se 3 (by rfl) ⟨446438, by rfl⟩ : syracuseStep 2381005 = 892877) B892877
theorem B939235 : Blo 834351 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B2676017 : Blo 834351 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B21976433 : Blo 834351 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B939379 : Blo 834351 939379 := bstep (se 1 (by rfl) ⟨704534, by rfl⟩ : syracuseStep 939379 = 1409069) B1409069
theorem B2381233 : Blo 834351 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B939523 : Blo 834351 939523 := bstep (se 1 (by rfl) ⟨704642, by rfl⟩ : syracuseStep 939523 = 1409285) B1409285
theorem B2381393 : Blo 834351 2381393 := bstep (se 2 (by rfl) ⟨893022, by rfl⟩ : syracuseStep 2381393 = 1786045) B1786045
theorem B2676365 : Blo 834351 2676365 := bstep (se 3 (by rfl) ⟨501818, by rfl⟩ : syracuseStep 2676365 = 1003637) B1003637
theorem B939667 : Blo 834351 939667 := bstep (se 1 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 939667 = 1409501) B1409501
theorem B1431217 : Blo 834351 1431217 := bstep (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) B1073413
theorem B2381507 : Blo 834351 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B939811 : Blo 834351 939811 := bstep (se 1 (by rfl) ⟨704858, by rfl⟩ : syracuseStep 939811 = 1409717) B1409717
theorem B939955 : Blo 834351 939955 := bstep (se 1 (by rfl) ⟨704966, by rfl⟩ : syracuseStep 939955 = 1409933) B1409933
theorem B2119729 : Blo 834351 2119729 := bstep (se 2 (by rfl) ⟨794898, by rfl⟩ : syracuseStep 2119729 = 1589797) B1589797
theorem B940099 : Blo 834351 940099 := bstep (se 1 (by rfl) ⟨705074, by rfl⟩ : syracuseStep 940099 = 1410149) B1410149
theorem B3168355 : Blo 834351 3168355 := bstep (se 1 (by rfl) ⟨2376266, by rfl⟩ : syracuseStep 3168355 = 4752533) B4752533
theorem B4774085 : Blo 834351 4774085 := bstep (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) B895141
theorem B940243 : Blo 834351 940243 := bstep (se 1 (by rfl) ⟨705182, by rfl⟩ : syracuseStep 940243 = 1410365) B1410365
theorem B2120003 : Blo 834351 2120003 := bstep (se 1 (by rfl) ⟨1590002, by rfl⟩ : syracuseStep 2120003 = 3180005) B3180005
theorem B940387 : Blo 834351 940387 := bstep (se 1 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 940387 = 1410581) B1410581
theorem B940531 : Blo 834351 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B2120195 : Blo 834351 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B940675 : Blo 834351 940675 := bstep (se 1 (by rfl) ⟨705506, by rfl⟩ : syracuseStep 940675 = 1411013) B1411013
theorem B2382509 : Blo 834351 2382509 := bstep (se 3 (by rfl) ⟨446720, by rfl⟩ : syracuseStep 2382509 = 893441) B893441
theorem B940819 : Blo 834351 940819 := bstep (se 1 (by rfl) ⟨705614, by rfl⟩ : syracuseStep 940819 = 1411229) B1411229
theorem B2382691 : Blo 834351 2382691 := bstep (se 1 (by rfl) ⟨1787018, by rfl⟩ : syracuseStep 2382691 = 3574037) B3574037
theorem B940963 : Blo 834351 940963 := bstep (se 1 (by rfl) ⟨705722, by rfl⟩ : syracuseStep 940963 = 1411445) B1411445
theorem B5364643 : Blo 834351 5364643 := bstep (se 1 (by rfl) ⟨4023482, by rfl⟩ : syracuseStep 5364643 = 8046965) B8046965
theorem B2382851 : Blo 834351 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B941107 : Blo 834351 941107 := bstep (se 1 (by rfl) ⟨705830, by rfl⟩ : syracuseStep 941107 = 1411661) B1411661
theorem B941251 : Blo 834351 941251 := bstep (se 1 (by rfl) ⟨705938, by rfl⟩ : syracuseStep 941251 = 1411877) B1411877
theorem B941395 : Blo 834351 941395 := bstep (se 1 (by rfl) ⟨706046, by rfl⟩ : syracuseStep 941395 = 1412093) B1412093
theorem B6348131 : Blo 834351 6348131 := bstep (se 1 (by rfl) ⟨4761098, by rfl⟩ : syracuseStep 6348131 = 9522197) B9522197
theorem B1433009 : Blo 834351 1433009 := bstep (se 2 (by rfl) ⟨537378, by rfl⟩ : syracuseStep 1433009 = 1074757) B1074757
theorem B2121137 : Blo 834351 2121137 := bstep (se 2 (by rfl) ⟨795426, by rfl⟩ : syracuseStep 2121137 = 1590853) B1590853
theorem B2678221 : Blo 834351 2678221 := bstep (se 3 (by rfl) ⟨502166, by rfl⟩ : syracuseStep 2678221 = 1004333) B1004333
theorem B941539 : Blo 834351 941539 := bstep (se 1 (by rfl) ⟨706154, by rfl⟩ : syracuseStep 941539 = 1412309) B1412309
theorem B2121187 : Blo 834351 2121187 := bstep (se 1 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 2121187 = 3181781) B3181781
theorem B2121329 : Blo 834351 2121329 := bstep (se 2 (by rfl) ⟨795498, by rfl⟩ : syracuseStep 2121329 = 1590997) B1590997
theorem B941683 : Blo 834351 941683 := bstep (se 1 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 941683 = 1412525) B1412525
theorem B2547377 : Blo 834351 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B4579057 : Blo 834351 4579057 := bstep (se 2 (by rfl) ⟨1717146, by rfl⟩ : syracuseStep 4579057 = 3434293) B3434293
theorem B941827 : Blo 834351 941827 := bstep (se 1 (by rfl) ⟨706370, by rfl⟩ : syracuseStep 941827 = 1412741) B1412741
theorem B5791493 : Blo 834351 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B941971 : Blo 834351 941971 := bstep (se 1 (by rfl) ⟨706478, by rfl⟩ : syracuseStep 941971 = 1412957) B1412957
theorem B942115 : Blo 834351 942115 := bstep (se 1 (by rfl) ⟨706586, by rfl⟩ : syracuseStep 942115 = 1413173) B1413173
theorem B2383921 : Blo 834351 2383921 := bstep (se 2 (by rfl) ⟨893970, by rfl⟩ : syracuseStep 2383921 = 1787941) B1787941
theorem B942259 : Blo 834351 942259 := bstep (se 1 (by rfl) ⟨706694, by rfl⟩ : syracuseStep 942259 = 1413389) B1413389
theorem B1204483 : Blo 834351 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B3170573 : Blo 834351 3170573 := bstep (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) B1188965
theorem B25747733 : Blo 834351 25747733 := bstep (se 6 (by rfl) ⟨603462, by rfl⟩ : syracuseStep 25747733 = 1206925) B1206925
theorem B942403 : Blo 834351 942403 := bstep (se 1 (by rfl) ⟨706802, by rfl⟩ : syracuseStep 942403 = 1413605) B1413605
theorem B942547 : Blo 834351 942547 := bstep (se 1 (by rfl) ⟨706910, by rfl⟩ : syracuseStep 942547 = 1413821) B1413821
theorem B942691 : Blo 834351 942691 := bstep (se 1 (by rfl) ⟨707018, by rfl⟩ : syracuseStep 942691 = 1414037) B1414037
theorem B942835 : Blo 834351 942835 := bstep (se 1 (by rfl) ⟨707126, by rfl⟩ : syracuseStep 942835 = 1414253) B1414253
theorem B3629873 : Blo 834351 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B942979 : Blo 834351 942979 := bstep (se 1 (by rfl) ⟨707234, by rfl⟩ : syracuseStep 942979 = 1414469) B1414469
theorem B943123 : Blo 834351 943123 := bstep (se 1 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 943123 = 1414685) B1414685
theorem B2680067 : Blo 834351 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B2385197 : Blo 834351 2385197 := bstep (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) B894449
theorem B5432645 : Blo 834351 5432645 := bstep (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) B1018621
theorem B4023715 : Blo 834351 4023715 := bstep (se 1 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 4023715 = 6035573) B6035573
theorem B1336753 : Blo 834351 1336753 := bstep (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) B1002565
theorem B2385379 : Blo 834351 2385379 := bstep (se 1 (by rfl) ⟨1789034, by rfl⟩ : syracuseStep 2385379 = 3578069) B3578069
theorem B2385425 : Blo 834351 2385425 := bstep (se 2 (by rfl) ⟨894534, by rfl⟩ : syracuseStep 2385425 = 1789069) B1789069
theorem B2680465 : Blo 834351 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B9168821 : Blo 834351 9168821 := bstep (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) B859577
theorem B2680913 : Blo 834351 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B9038051 : Blo 834351 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B2419267 : Blo 834351 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B10709603 : Blo 834351 10709603 := bstep (se 1 (by rfl) ⟨8032202, by rfl⟩ : syracuseStep 10709603 = 16064405) B16064405
theorem B1272419 : Blo 834351 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B5368517 : Blo 834351 5368517 := bstep (se 4 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 5368517 = 1006597) B1006597
theorem B2386883 : Blo 834351 2386883 := bstep (se 1 (by rfl) ⟨1790162, by rfl⟩ : syracuseStep 2386883 = 3580325) B3580325
theorem B1698851 : Blo 834351 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B1338419 : Blo 834351 1338419 := bstep (se 1 (by rfl) ⟨1003814, by rfl⟩ : syracuseStep 1338419 = 2007629) B2007629
theorem B3173489 : Blo 834351 3173489 := bstep (se 2 (by rfl) ⟨1190058, by rfl⟩ : syracuseStep 3173489 = 2380117) B2380117
theorem B1338547 : Blo 834351 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B1338611 : Blo 834351 1338611 := bstep (se 1 (by rfl) ⟨1003958, by rfl⟩ : syracuseStep 1338611 = 2007917) B2007917
theorem B3566861 : Blo 834351 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B6778181 : Blo 834351 6778181 := bstep (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) B1270909
theorem B4287857 : Blo 834351 4287857 := bstep (se 2 (by rfl) ⟨1607946, by rfl⟩ : syracuseStep 4287857 = 3215893) B3215893
theorem B1273201 : Blo 834351 1273201 := bstep (se 2 (by rfl) ⟨477450, by rfl⟩ : syracuseStep 1273201 = 954901) B954901
theorem B4025713 : Blo 834351 4025713 := bstep (se 2 (by rfl) ⟨1509642, by rfl⟩ : syracuseStep 4025713 = 3019285) B3019285
theorem B2289091 : Blo 834351 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B1273313 : Blo 834351 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B3567203 : Blo 834351 3567203 := bstep (se 1 (by rfl) ⟨2675402, by rfl⟩ : syracuseStep 3567203 = 5350805) B5350805
theorem B7237219 : Blo 834351 7237219 := bstep (se 1 (by rfl) ⟨5427914, by rfl⟩ : syracuseStep 7237219 = 10855829) B10855829
theorem B1961635 : Blo 834351 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B13758149 : Blo 834351 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B1339105 : Blo 834351 1339105 := bstep (se 2 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 1339105 = 1004329) B1004329
theorem B5074757 : Blo 834351 5074757 := bstep (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) B951517
theorem B847747 : Blo 834351 847747 := bstep (se 1 (by rfl) ⟨635810, by rfl⟩ : syracuseStep 847747 = 1271621) B1271621
theorem B3567665 : Blo 834351 3567665 := bstep (se 2 (by rfl) ⟨1337874, by rfl⟩ : syracuseStep 3567665 = 2675749) B2675749
theorem B2715697 : Blo 834351 2715697 := bstep (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) B2036773
theorem B2682989 : Blo 834351 2682989 := bstep (se 3 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 2682989 = 1006121) B1006121
theorem B848051 : Blo 834351 848051 := bstep (se 1 (by rfl) ⟨636038, by rfl⟩ : syracuseStep 848051 = 1272077) B1272077
theorem B1470803 : Blo 834351 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B1339777 : Blo 834351 1339777 := bstep (se 2 (by rfl) ⟨502416, by rfl⟩ : syracuseStep 1339777 = 1004833) B1004833
theorem B1274321 : Blo 834351 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B3174947 : Blo 834351 3174947 := bstep (se 1 (by rfl) ⟨2381210, by rfl⟩ : syracuseStep 3174947 = 4762421) B4762421
theorem B6353477 : Blo 834351 6353477 := bstep (se 4 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 6353477 = 1191277) B1191277
theorem B2716429 : Blo 834351 2716429 := bstep (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) B1018661
theorem B1504337 : Blo 834351 1504337 := bstep (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) B1128253
theorem B2290801 : Blo 834351 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B2684269 : Blo 834351 2684269 := bstep (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) B1006601
theorem B1340867 : Blo 834351 1340867 := bstep (se 1 (by rfl) ⟨1005650, by rfl⟩ : syracuseStep 1340867 = 2011301) B2011301
theorem B3175949 : Blo 834351 3175949 := bstep (se 3 (by rfl) ⟨595490, by rfl⟩ : syracuseStep 3175949 = 1190981) B1190981
theorem B1341155 : Blo 834351 1341155 := bstep (se 1 (by rfl) ⟨1005866, by rfl⟩ : syracuseStep 1341155 = 2011733) B2011733
theorem B3012365 : Blo 834351 3012365 := bstep (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) B1129637
theorem B2684771 : Blo 834351 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B1472435 : Blo 834351 1472435 := bstep (se 1 (by rfl) ⟨1104326, by rfl⟩ : syracuseStep 1472435 = 2208653) B2208653
theorem B2816045 : Blo 834351 2816045 := bstep (se 3 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 2816045 = 1056017) B1056017
theorem B7141445 : Blo 834351 7141445 := bstep (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) B1339021
theorem B2816099 : Blo 834351 2816099 := bstep (se 1 (by rfl) ⟨2112074, by rfl⟩ : syracuseStep 2816099 = 4224149) B4224149
theorem B1341571 : Blo 834351 1341571 := bstep (se 1 (by rfl) ⟨1006178, by rfl⟩ : syracuseStep 1341571 = 2012357) B2012357
theorem B4028557 : Blo 834351 4028557 := bstep (se 3 (by rfl) ⟨755354, by rfl⟩ : syracuseStep 4028557 = 1510709) B1510709
theorem B2816369 : Blo 834351 2816369 := bstep (se 2 (by rfl) ⟨1056138, by rfl⟩ : syracuseStep 2816369 = 2112277) B2112277
theorem B1341841 : Blo 834351 1341841 := bstep (se 2 (by rfl) ⟨503190, by rfl⟩ : syracuseStep 1341841 = 1006381) B1006381
theorem B1342097 : Blo 834351 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B2816909 : Blo 834351 2816909 := bstep (se 3 (by rfl) ⟨528170, by rfl⟩ : syracuseStep 2816909 = 1056341) B1056341
theorem B2816963 : Blo 834351 2816963 := bstep (se 1 (by rfl) ⟨2112722, by rfl⟩ : syracuseStep 2816963 = 4225445) B4225445
theorem B1408097 : Blo 834351 1408097 := bstep (se 2 (by rfl) ⟨528036, by rfl⟩ : syracuseStep 1408097 = 1056073) B1056073
theorem B2817233 : Blo 834351 2817233 := bstep (se 2 (by rfl) ⟨1056462, by rfl⟩ : syracuseStep 2817233 = 2112925) B2112925
theorem B1408225 : Blo 834351 1408225 := bstep (se 2 (by rfl) ⟨528084, by rfl⟩ : syracuseStep 1408225 = 1056169) B1056169
theorem B1408259 : Blo 834351 1408259 := bstep (se 1 (by rfl) ⟨1056194, by rfl⟩ : syracuseStep 1408259 = 2112389) B2112389
theorem B3439949 : Blo 834351 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B1342801 : Blo 834351 1342801 := bstep (se 2 (by rfl) ⟨503550, by rfl⟩ : syracuseStep 1342801 = 1007101) B1007101
theorem B4226417 : Blo 834351 4226417 := bstep (se 2 (by rfl) ⟨1584906, by rfl⟩ : syracuseStep 4226417 = 3169813) B3169813
theorem B1408387 : Blo 834351 1408387 := bstep (se 1 (by rfl) ⟨1056290, by rfl⟩ : syracuseStep 1408387 = 2112581) B2112581
theorem B1408529 : Blo 834351 1408529 := bstep (se 2 (by rfl) ⟨528198, by rfl⟩ : syracuseStep 1408529 = 1056397) B1056397
theorem B3571235 : Blo 834351 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B3178061 : Blo 834351 3178061 := bstep (se 3 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 3178061 = 1191773) B1191773
theorem B8027747 : Blo 834351 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B1408657 : Blo 834351 1408657 := bstep (se 2 (by rfl) ⟨528246, by rfl⟩ : syracuseStep 1408657 = 1056493) B1056493
theorem B1506961 : Blo 834351 1506961 := bstep (se 2 (by rfl) ⟨565110, by rfl⟩ : syracuseStep 1506961 = 1130221) B1130221
theorem B1408691 : Blo 834351 1408691 := bstep (se 1 (by rfl) ⟨1056518, by rfl⟩ : syracuseStep 1408691 = 2113037) B2113037
theorem B2817773 : Blo 834351 2817773 := bstep (se 3 (by rfl) ⟨528332, by rfl⟩ : syracuseStep 2817773 = 1056665) B1056665
theorem B2817827 : Blo 834351 2817827 := bstep (se 1 (by rfl) ⟨2113370, by rfl⟩ : syracuseStep 2817827 = 4226741) B4226741
theorem B1408819 : Blo 834351 1408819 := bstep (se 1 (by rfl) ⟨1056614, by rfl⟩ : syracuseStep 1408819 = 2113229) B2113229
theorem B4521905 : Blo 834351 4521905 := bstep (se 2 (by rfl) ⟨1695714, by rfl⟩ : syracuseStep 4521905 = 3391429) B3391429
theorem B1408961 : Blo 834351 1408961 := bstep (se 2 (by rfl) ⟨528360, by rfl⟩ : syracuseStep 1408961 = 1056721) B1056721
theorem B13565893 : Blo 834351 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B1409035 : Blo 834351 1409035 := bstep (se 1 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 1409035 = 2113553) B2113553
theorem B3178547 : Blo 834351 3178547 := bstep (se 1 (by rfl) ⟨2383910, by rfl⟩ : syracuseStep 3178547 = 4767821) B4767821
theorem B3178561 : Blo 834351 3178561 := bstep (se 2 (by rfl) ⟨1191960, by rfl⟩ : syracuseStep 3178561 = 2383921) B2383921
theorem B9175133 : Blo 834351 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B1409177 : Blo 834351 1409177 := bstep (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) B1056883
theorem B14483717 : Blo 834351 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B1409305 : Blo 834351 1409305 := bstep (se 2 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 1409305 = 1056979) B1056979
theorem B1605977 : Blo 834351 1605977 := bstep (se 2 (by rfl) ⟨602241, by rfl⟩ : syracuseStep 1605977 = 1204483) B1204483
theorem B2818583 : Blo 834351 2818583 := bstep (se 1 (by rfl) ⟨2113937, by rfl⟩ : syracuseStep 2818583 = 4227875) B4227875
theorem B1409879 : Blo 834351 1409879 := bstep (se 1 (by rfl) ⟨1057409, by rfl⟩ : syracuseStep 1409879 = 2114819) B2114819
theorem B1410007 : Blo 834351 1410007 := bstep (se 1 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 1410007 = 2115011) B2115011
theorem B10159139 : Blo 834351 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B2819123 : Blo 834351 2819123 := bstep (se 1 (by rfl) ⟨2114342, by rfl⟩ : syracuseStep 2819123 = 4228685) B4228685
theorem B3015755 : Blo 834351 3015755 := bstep (se 1 (by rfl) ⟨2261816, by rfl⟩ : syracuseStep 3015755 = 4523633) B4523633
theorem B6784177 : Blo 834351 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B2819393 : Blo 834351 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B6358337 : Blo 834351 6358337 := bstep (se 2 (by rfl) ⟨2384376, by rfl⟩ : syracuseStep 6358337 = 4768753) B4768753
theorem B4752715 : Blo 834351 4752715 := bstep (se 1 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 4752715 = 7129073) B7129073
theorem B1410635 : Blo 834351 1410635 := bstep (se 1 (by rfl) ⟨1057976, by rfl⟩ : syracuseStep 1410635 = 2115953) B2115953
theorem B1508951 : Blo 834351 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B4752989 : Blo 834351 4752989 := bstep (se 3 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 4752989 = 1782371) B1782371
theorem B4523651 : Blo 834351 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B1410763 : Blo 834351 1410763 := bstep (se 1 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 1410763 = 2116145) B2116145
theorem B1410905 : Blo 834351 1410905 := bstep (se 2 (by rfl) ⟨529089, by rfl⟩ : syracuseStep 1410905 = 1058179) B1058179
theorem B2819933 : Blo 834351 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B9045877 : Blo 834351 9045877 := bstep (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) B848051
theorem B1017803 : Blo 834351 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B3180491 : Blo 834351 3180491 := bstep (se 1 (by rfl) ⟨2385368, by rfl⟩ : syracuseStep 3180491 = 4770737) B4770737
theorem B1411033 : Blo 834351 1411033 := bstep (se 2 (by rfl) ⟨529137, by rfl⟩ : syracuseStep 1411033 = 1058275) B1058275
theorem B3180505 : Blo 834351 3180505 := bstep (se 2 (by rfl) ⟨1192689, by rfl⟩ : syracuseStep 3180505 = 2385379) B2385379
theorem B3573953 : Blo 834351 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B3016921 : Blo 834351 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B3017035 : Blo 834351 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B1411607 : Blo 834351 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B1411735 : Blo 834351 1411735 := bstep (se 1 (by rfl) ⟨1058801, by rfl⟩ : syracuseStep 1411735 = 2117603) B2117603
theorem B4229981 : Blo 834351 4229981 := bstep (se 3 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 4229981 = 1586243) B1586243
theorem B3181463 : Blo 834351 3181463 := bstep (se 1 (by rfl) ⟨2386097, by rfl⟩ : syracuseStep 3181463 = 4772195) B4772195
theorem B2821067 : Blo 834351 2821067 := bstep (se 1 (by rfl) ⟨2115800, by rfl⟩ : syracuseStep 2821067 = 4231601) B4231601
theorem B1903745 : Blo 834351 1903745 := bstep (se 2 (by rfl) ⟨713904, by rfl⟩ : syracuseStep 1903745 = 1427809) B1427809
theorem B3017873 : Blo 834351 3017873 := bstep (se 2 (by rfl) ⟨1131702, by rfl⟩ : syracuseStep 3017873 = 2263405) B2263405
theorem B2821337 : Blo 834351 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B6360281 : Blo 834351 6360281 := bstep (se 2 (by rfl) ⟨2385105, by rfl⟩ : syracuseStep 6360281 = 4770211) B4770211
theorem B1412363 : Blo 834351 1412363 := bstep (se 1 (by rfl) ⟨1059272, by rfl⟩ : syracuseStep 1412363 = 2118545) B2118545
theorem B1510667 : Blo 834351 1510667 := bstep (se 1 (by rfl) ⟨1133000, by rfl⟩ : syracuseStep 1510667 = 2266001) B2266001
theorem B953707 : Blo 834351 953707 := bstep (se 1 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 953707 = 1430561) B1430561
theorem B1412491 : Blo 834351 1412491 := bstep (se 1 (by rfl) ⟨1059368, by rfl⟩ : syracuseStep 1412491 = 2118737) B2118737
theorem B1609111 : Blo 834351 1609111 := bstep (se 1 (by rfl) ⟨1206833, by rfl⟩ : syracuseStep 1609111 = 2413667) B2413667
theorem B5443033 : Blo 834351 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B1412633 : Blo 834351 1412633 := bstep (se 2 (by rfl) ⟨529737, by rfl⟩ : syracuseStep 1412633 = 1059475) B1059475
theorem B14650955 : Blo 834351 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B1412761 : Blo 834351 1412761 := bstep (se 2 (by rfl) ⟨529785, by rfl⟩ : syracuseStep 1412761 = 1059571) B1059571
theorem B2822039 : Blo 834351 2822039 := bstep (se 1 (by rfl) ⟨2116529, by rfl⟩ : syracuseStep 2822039 = 4233059) B4233059
theorem B3182723 : Blo 834351 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B1413335 : Blo 834351 1413335 := bstep (se 1 (by rfl) ⟨1060001, by rfl⟩ : syracuseStep 1413335 = 2120003) B2120003
theorem B1413463 : Blo 834351 1413463 := bstep (se 1 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 1413463 = 2120195) B2120195
theorem B2822579 : Blo 834351 2822579 := bstep (se 1 (by rfl) ⟨2116934, by rfl⟩ : syracuseStep 2822579 = 4233869) B4233869
theorem B3052121 : Blo 834351 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B3576413 : Blo 834351 3576413 := bstep (se 3 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 3576413 = 1341155) B1341155
theorem B7148209 : Blo 834351 7148209 := bstep (se 2 (by rfl) ⟨2680578, by rfl⟩ : syracuseStep 7148209 = 5361157) B5361157
theorem B2822849 : Blo 834351 2822849 := bstep (se 2 (by rfl) ⟨1058568, by rfl⟩ : syracuseStep 2822849 = 2117137) B2117137
theorem B4232087 : Blo 834351 4232087 := bstep (se 1 (by rfl) ⟨3174065, by rfl⟩ : syracuseStep 4232087 = 6348131) B6348131
theorem B1414091 : Blo 834351 1414091 := bstep (se 1 (by rfl) ⟨1060568, by rfl⟩ : syracuseStep 1414091 = 2121137) B2121137
theorem B1414219 : Blo 834351 1414219 := bstep (se 1 (by rfl) ⟨1060664, by rfl⟩ : syracuseStep 1414219 = 2121329) B2121329
theorem B1414361 : Blo 834351 1414361 := bstep (se 2 (by rfl) ⟨530385, by rfl⟩ : syracuseStep 1414361 = 1060771) B1060771
theorem B2823389 : Blo 834351 2823389 := bstep (se 3 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 2823389 = 1058771) B1058771
theorem B1414489 : Blo 834351 1414489 := bstep (se 2 (by rfl) ⟨530433, by rfl⟩ : syracuseStep 1414489 = 1060867) B1060867
theorem B3020381 : Blo 834351 3020381 := bstep (se 3 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 3020381 = 1132643) B1132643
theorem B5347421 : Blo 834351 5347421 := bstep (se 3 (by rfl) ⟨1002641, by rfl⟩ : syracuseStep 5347421 = 2005283) B2005283
theorem B4298845 : Blo 834351 4298845 := bstep (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) B1612067
theorem B1251545 : Blo 834351 1251545 := bstep (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) B938659
theorem B1251659 : Blo 834351 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B2824523 : Blo 834351 2824523 := bstep (se 1 (by rfl) ⟨2118392, by rfl⟩ : syracuseStep 2824523 = 4236785) B4236785
theorem B3021131 : Blo 834351 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B1251671 : Blo 834351 1251671 := bstep (se 1 (by rfl) ⟨938753, by rfl⟩ : syracuseStep 1251671 = 1877507) B1877507
theorem B3021187 : Blo 834351 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B1251737 : Blo 834351 1251737 := bstep (se 2 (by rfl) ⟨469401, by rfl⟩ : syracuseStep 1251737 = 938803) B938803
theorem B1251851 : Blo 834351 1251851 := bstep (se 1 (by rfl) ⟨938888, by rfl⟩ : syracuseStep 1251851 = 1877777) B1877777
theorem B1251863 : Blo 834351 1251863 := bstep (se 1 (by rfl) ⟨938897, by rfl⟩ : syracuseStep 1251863 = 1877795) B1877795
theorem B6363683 : Blo 834351 6363683 := bstep (se 1 (by rfl) ⟨4772762, by rfl⟩ : syracuseStep 6363683 = 9545525) B9545525
theorem B1251929 : Blo 834351 1251929 := bstep (se 2 (by rfl) ⟨469473, by rfl⟩ : syracuseStep 1251929 = 938947) B938947
theorem B2824793 : Blo 834351 2824793 := bstep (se 2 (by rfl) ⟨1059297, by rfl⟩ : syracuseStep 2824793 = 2118595) B2118595
theorem B1252043 : Blo 834351 1252043 := bstep (se 1 (by rfl) ⟨939032, by rfl⟩ : syracuseStep 1252043 = 1878065) B1878065
theorem B1252055 : Blo 834351 1252055 := bstep (se 1 (by rfl) ⟨939041, by rfl⟩ : syracuseStep 1252055 = 1878083) B1878083
theorem B1252121 : Blo 834351 1252121 := bstep (se 2 (by rfl) ⟨469545, by rfl⟩ : syracuseStep 1252121 = 939091) B939091
theorem B2857793 : Blo 834351 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B3054401 : Blo 834351 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B4758365 : Blo 834351 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B11443045 : Blo 834351 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B1252235 : Blo 834351 1252235 := bstep (se 1 (by rfl) ⟨939176, by rfl⟩ : syracuseStep 1252235 = 1878353) B1878353
theorem B1252247 : Blo 834351 1252247 := bstep (se 1 (by rfl) ⟨939185, by rfl⟩ : syracuseStep 1252247 = 1878371) B1878371
theorem B1252313 : Blo 834351 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B1252427 : Blo 834351 1252427 := bstep (se 1 (by rfl) ⟨939320, by rfl⟩ : syracuseStep 1252427 = 1878641) B1878641
theorem B1252439 : Blo 834351 1252439 := bstep (se 1 (by rfl) ⟨939329, by rfl⟩ : syracuseStep 1252439 = 1878659) B1878659
theorem B3579011 : Blo 834351 3579011 := bstep (se 1 (by rfl) ⟨2684258, by rfl⟩ : syracuseStep 3579011 = 5368517) B5368517
theorem B1252505 : Blo 834351 1252505 := bstep (se 2 (by rfl) ⟨469689, by rfl⟩ : syracuseStep 1252505 = 939379) B939379
theorem B6790405 : Blo 834351 6790405 := bstep (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) B1273201
theorem B1252619 : Blo 834351 1252619 := bstep (se 1 (by rfl) ⟨939464, by rfl⟩ : syracuseStep 1252619 = 1878929) B1878929
theorem B1252631 : Blo 834351 1252631 := bstep (se 1 (by rfl) ⟨939473, by rfl⟩ : syracuseStep 1252631 = 1878947) B1878947
theorem B2825495 : Blo 834351 2825495 := bstep (se 1 (by rfl) ⟨2119121, by rfl⟩ : syracuseStep 2825495 = 4238243) B4238243
theorem B1252697 : Blo 834351 1252697 := bstep (se 2 (by rfl) ⟨469761, by rfl⟩ : syracuseStep 1252697 = 939523) B939523
theorem B892279 : Blo 834351 892279 := bstep (se 1 (by rfl) ⟨669209, by rfl⟩ : syracuseStep 892279 = 1338419) B1338419
theorem B3808657 : Blo 834351 3808657 := bstep (se 2 (by rfl) ⟨1428246, by rfl⟩ : syracuseStep 3808657 = 2856493) B2856493
theorem B1252811 : Blo 834351 1252811 := bstep (se 1 (by rfl) ⟨939608, by rfl⟩ : syracuseStep 1252811 = 1879217) B1879217
theorem B1252823 : Blo 834351 1252823 := bstep (se 1 (by rfl) ⟨939617, by rfl⟩ : syracuseStep 1252823 = 1879235) B1879235
theorem B1252889 : Blo 834351 1252889 := bstep (se 2 (by rfl) ⟨469833, by rfl⟩ : syracuseStep 1252889 = 939667) B939667
theorem B1908289 : Blo 834351 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B1056331 : Blo 834351 1056331 := bstep (se 1 (by rfl) ⟨792248, by rfl⟩ : syracuseStep 1056331 = 1584497) B1584497
theorem B1253003 : Blo 834351 1253003 := bstep (se 1 (by rfl) ⟨939752, by rfl⟩ : syracuseStep 1253003 = 1879505) B1879505
theorem B1253015 : Blo 834351 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B1253081 : Blo 834351 1253081 := bstep (se 2 (by rfl) ⟨469905, by rfl⟩ : syracuseStep 1253081 = 939811) B939811
theorem B2826035 : Blo 834351 2826035 := bstep (se 1 (by rfl) ⟨2119526, by rfl⟩ : syracuseStep 2826035 = 4239053) B4239053
theorem B1253195 : Blo 834351 1253195 := bstep (se 1 (by rfl) ⟨939896, by rfl⟩ : syracuseStep 1253195 = 1879793) B1879793
theorem B1253207 : Blo 834351 1253207 := bstep (se 1 (by rfl) ⟨939905, by rfl⟩ : syracuseStep 1253207 = 1879811) B1879811
theorem B3383171 : Blo 834351 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B1253273 : Blo 834351 1253273 := bstep (se 2 (by rfl) ⟨469977, by rfl⟩ : syracuseStep 1253273 = 939955) B939955
theorem B1253387 : Blo 834351 1253387 := bstep (se 1 (by rfl) ⟨940040, by rfl⟩ : syracuseStep 1253387 = 1880081) B1880081
theorem B1253399 : Blo 834351 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B2826305 : Blo 834351 2826305 := bstep (se 2 (by rfl) ⟨1059864, by rfl⟩ : syracuseStep 2826305 = 2119729) B2119729
theorem B9052235 : Blo 834351 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B1253465 : Blo 834351 1253465 := bstep (se 2 (by rfl) ⟨470049, by rfl⟩ : syracuseStep 1253465 = 940099) B940099
theorem B4530269 : Blo 834351 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B1253579 : Blo 834351 1253579 := bstep (se 1 (by rfl) ⟨940184, by rfl⟩ : syracuseStep 1253579 = 1880369) B1880369
theorem B1253591 : Blo 834351 1253591 := bstep (se 1 (by rfl) ⟨940193, by rfl⟩ : syracuseStep 1253591 = 1880387) B1880387
theorem B1253657 : Blo 834351 1253657 := bstep (se 2 (by rfl) ⟨470121, by rfl⟩ : syracuseStep 1253657 = 940243) B940243
theorem B4235651 : Blo 834351 4235651 := bstep (se 1 (by rfl) ⟨3176738, by rfl⟩ : syracuseStep 4235651 = 6353477) B6353477
theorem B1253771 : Blo 834351 1253771 := bstep (se 1 (by rfl) ⟨940328, by rfl⟩ : syracuseStep 1253771 = 1880657) B1880657
theorem B1253783 : Blo 834351 1253783 := bstep (se 1 (by rfl) ⟨940337, by rfl⟩ : syracuseStep 1253783 = 1880675) B1880675
theorem B1253849 : Blo 834351 1253849 := bstep (se 2 (by rfl) ⟨470193, by rfl⟩ : syracuseStep 1253849 = 940387) B940387
theorem B1057303 : Blo 834351 1057303 := bstep (se 1 (by rfl) ⟨792977, by rfl⟩ : syracuseStep 1057303 = 1585955) B1585955
theorem B1253963 : Blo 834351 1253963 := bstep (se 1 (by rfl) ⟨940472, by rfl⟩ : syracuseStep 1253963 = 1880945) B1880945
theorem B1253975 : Blo 834351 1253975 := bstep (se 1 (by rfl) ⟨940481, by rfl⟩ : syracuseStep 1253975 = 1880963) B1880963
theorem B2826845 : Blo 834351 2826845 := bstep (se 3 (by rfl) ⟨530033, by rfl⟩ : syracuseStep 2826845 = 1060067) B1060067
theorem B1254041 : Blo 834351 1254041 := bstep (se 2 (by rfl) ⟨470265, by rfl⟩ : syracuseStep 1254041 = 940531) B940531
theorem B1254155 : Blo 834351 1254155 := bstep (se 1 (by rfl) ⟨940616, by rfl⟩ : syracuseStep 1254155 = 1881233) B1881233
theorem B1254167 : Blo 834351 1254167 := bstep (se 1 (by rfl) ⟨940625, by rfl⟩ : syracuseStep 1254167 = 1881251) B1881251
theorem B1254233 : Blo 834351 1254233 := bstep (se 2 (by rfl) ⟨470337, by rfl⟩ : syracuseStep 1254233 = 940675) B940675
theorem B1254347 : Blo 834351 1254347 := bstep (se 1 (by rfl) ⟨940760, by rfl⟩ : syracuseStep 1254347 = 1881521) B1881521
theorem B1254359 : Blo 834351 1254359 := bstep (se 1 (by rfl) ⟨940769, by rfl⟩ : syracuseStep 1254359 = 1881539) B1881539
theorem B893911 : Blo 834351 893911 := bstep (se 1 (by rfl) ⟨670433, by rfl⟩ : syracuseStep 893911 = 1340867) B1340867
theorem B1254425 : Blo 834351 1254425 := bstep (se 2 (by rfl) ⟨470409, by rfl⟩ : syracuseStep 1254425 = 940819) B940819
theorem B1254539 : Blo 834351 1254539 := bstep (se 1 (by rfl) ⟨940904, by rfl⟩ : syracuseStep 1254539 = 1881809) B1881809
theorem B1254551 : Blo 834351 1254551 := bstep (se 1 (by rfl) ⟨940913, by rfl⟩ : syracuseStep 1254551 = 1881827) B1881827
theorem B2008243 : Blo 834351 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B1254617 : Blo 834351 1254617 := bstep (se 2 (by rfl) ⟨470481, by rfl⟩ : syracuseStep 1254617 = 940963) B940963
theorem B7152857 : Blo 834351 7152857 := bstep (se 2 (by rfl) ⟨2682321, by rfl⟩ : syracuseStep 7152857 = 5364643) B5364643
theorem B24421637 : Blo 834351 24421637 := bstep (se 4 (by rfl) ⟨2289528, by rfl⟩ : syracuseStep 24421637 = 4579057) B4579057
theorem B3220759 : Blo 834351 3220759 := bstep (se 1 (by rfl) ⟨2415569, by rfl⟩ : syracuseStep 3220759 = 4831139) B4831139
theorem B1058123 : Blo 834351 1058123 := bstep (se 1 (by rfl) ⟨793592, by rfl⟩ : syracuseStep 1058123 = 1587185) B1587185
theorem B1254731 : Blo 834351 1254731 := bstep (se 1 (by rfl) ⟨941048, by rfl⟩ : syracuseStep 1254731 = 1882097) B1882097
theorem B1254743 : Blo 834351 1254743 := bstep (se 1 (by rfl) ⟨941057, by rfl⟩ : syracuseStep 1254743 = 1882115) B1882115
theorem B1877363 : Blo 834351 1877363 := bstep (se 1 (by rfl) ⟨1408022, by rfl⟩ : syracuseStep 1877363 = 2816045) B2816045
theorem B4760963 : Blo 834351 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B1877399 : Blo 834351 1877399 := bstep (se 1 (by rfl) ⟨1408049, by rfl⟩ : syracuseStep 1877399 = 2816099) B2816099
theorem B1254809 : Blo 834351 1254809 := bstep (se 2 (by rfl) ⟨470553, by rfl⟩ : syracuseStep 1254809 = 941107) B941107
theorem B1254923 : Blo 834351 1254923 := bstep (se 1 (by rfl) ⟨941192, by rfl⟩ : syracuseStep 1254923 = 1882385) B1882385
theorem B1254935 : Blo 834351 1254935 := bstep (se 1 (by rfl) ⟨941201, by rfl⟩ : syracuseStep 1254935 = 1882403) B1882403
theorem B1877579 : Blo 834351 1877579 := bstep (se 1 (by rfl) ⟨1408184, by rfl⟩ : syracuseStep 1877579 = 2816369) B2816369
theorem B1255001 : Blo 834351 1255001 := bstep (se 2 (by rfl) ⟨470625, by rfl⟩ : syracuseStep 1255001 = 941251) B941251
theorem B1877633 : Blo 834351 1877633 := bstep (se 2 (by rfl) ⟨704112, by rfl⟩ : syracuseStep 1877633 = 1408225) B1408225
theorem B1255115 : Blo 834351 1255115 := bstep (se 1 (by rfl) ⟨941336, by rfl⟩ : syracuseStep 1255115 = 1882673) B1882673
theorem B2827979 : Blo 834351 2827979 := bstep (se 1 (by rfl) ⟨2120984, by rfl⟩ : syracuseStep 2827979 = 4241969) B4241969
theorem B1255127 : Blo 834351 1255127 := bstep (se 1 (by rfl) ⟨941345, by rfl⟩ : syracuseStep 1255127 = 1882691) B1882691
theorem B894731 : Blo 834351 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1255193 : Blo 834351 1255193 := bstep (se 2 (by rfl) ⟨470697, by rfl⟩ : syracuseStep 1255193 = 941395) B941395
theorem B1877849 : Blo 834351 1877849 := bstep (se 2 (by rfl) ⟨704193, by rfl⟩ : syracuseStep 1877849 = 1408387) B1408387
theorem B3614557 : Blo 834351 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B1255307 : Blo 834351 1255307 := bstep (se 1 (by rfl) ⟨941480, by rfl⟩ : syracuseStep 1255307 = 1882961) B1882961
theorem B1255319 : Blo 834351 1255319 := bstep (se 1 (by rfl) ⟨941489, by rfl⟩ : syracuseStep 1255319 = 1882979) B1882979
theorem B1877939 : Blo 834351 1877939 := bstep (se 1 (by rfl) ⟨1408454, by rfl⟩ : syracuseStep 1877939 = 2816909) B2816909
theorem B1877975 : Blo 834351 1877975 := bstep (se 1 (by rfl) ⟨1408481, by rfl⟩ : syracuseStep 1877975 = 2816963) B2816963
theorem B1255385 : Blo 834351 1255385 := bstep (se 2 (by rfl) ⟨470769, by rfl⟩ : syracuseStep 1255385 = 941539) B941539
theorem B2828249 : Blo 834351 2828249 := bstep (se 2 (by rfl) ⟨1060593, by rfl⟩ : syracuseStep 2828249 = 2121187) B2121187
theorem B1058827 : Blo 834351 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B1255499 : Blo 834351 1255499 := bstep (se 1 (by rfl) ⟨941624, by rfl⟩ : syracuseStep 1255499 = 1883249) B1883249
theorem B1255511 : Blo 834351 1255511 := bstep (se 1 (by rfl) ⟨941633, by rfl⟩ : syracuseStep 1255511 = 1883267) B1883267
theorem B1878155 : Blo 834351 1878155 := bstep (se 1 (by rfl) ⟨1408616, by rfl⟩ : syracuseStep 1878155 = 2817233) B2817233
theorem B1255577 : Blo 834351 1255577 := bstep (se 2 (by rfl) ⟨470841, by rfl⟩ : syracuseStep 1255577 = 941683) B941683
theorem B1878209 : Blo 834351 1878209 := bstep (se 2 (by rfl) ⟨704328, by rfl⟩ : syracuseStep 1878209 = 1408657) B1408657
theorem B2009281 : Blo 834351 2009281 := bstep (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) B1506961
theorem B1255691 : Blo 834351 1255691 := bstep (se 1 (by rfl) ⟨941768, by rfl⟩ : syracuseStep 1255691 = 1883537) B1883537
theorem B1059095 : Blo 834351 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B1255703 : Blo 834351 1255703 := bstep (se 1 (by rfl) ⟨941777, by rfl⟩ : syracuseStep 1255703 = 1883555) B1883555
theorem B1255769 : Blo 834351 1255769 := bstep (se 2 (by rfl) ⟨470913, by rfl⟩ : syracuseStep 1255769 = 941827) B941827
theorem B5351831 : Blo 834351 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B1878425 : Blo 834351 1878425 := bstep (se 2 (by rfl) ⟨704409, by rfl⟩ : syracuseStep 1878425 = 1408819) B1408819
theorem B1255883 : Blo 834351 1255883 := bstep (se 1 (by rfl) ⟨941912, by rfl⟩ : syracuseStep 1255883 = 1883825) B1883825
theorem B1255895 : Blo 834351 1255895 := bstep (se 1 (by rfl) ⟨941921, by rfl⟩ : syracuseStep 1255895 = 1883843) B1883843
theorem B1878515 : Blo 834351 1878515 := bstep (se 1 (by rfl) ⟨1408886, by rfl⟩ : syracuseStep 1878515 = 2817773) B2817773
theorem B1878551 : Blo 834351 1878551 := bstep (se 1 (by rfl) ⟨1408913, by rfl⟩ : syracuseStep 1878551 = 2817827) B2817827
theorem B1190423 : Blo 834351 1190423 := bstep (se 1 (by rfl) ⟨892817, by rfl⟩ : syracuseStep 1190423 = 1785635) B1785635
theorem B1255961 : Blo 834351 1255961 := bstep (se 2 (by rfl) ⟨470985, by rfl⟩ : syracuseStep 1255961 = 941971) B941971
theorem B6040129 : Blo 834351 6040129 := bstep (se 2 (by rfl) ⟨2265048, by rfl⟩ : syracuseStep 6040129 = 4530097) B4530097
theorem B1256075 : Blo 834351 1256075 := bstep (se 1 (by rfl) ⟨942056, by rfl⟩ : syracuseStep 1256075 = 1884113) B1884113
theorem B1256087 : Blo 834351 1256087 := bstep (se 1 (by rfl) ⟨942065, by rfl⟩ : syracuseStep 1256087 = 1884131) B1884131
theorem B2828951 : Blo 834351 2828951 := bstep (se 1 (by rfl) ⟨2121713, by rfl⟩ : syracuseStep 2828951 = 4243427) B4243427
theorem B1878731 : Blo 834351 1878731 := bstep (se 1 (by rfl) ⟨1409048, by rfl⟩ : syracuseStep 1878731 = 2818097) B2818097
theorem B1256153 : Blo 834351 1256153 := bstep (se 2 (by rfl) ⟨471057, by rfl⟩ : syracuseStep 1256153 = 942115) B942115
theorem B1878785 : Blo 834351 1878785 := bstep (se 2 (by rfl) ⟨704544, by rfl⟩ : syracuseStep 1878785 = 1409089) B1409089
theorem B3812147 : Blo 834351 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B1256267 : Blo 834351 1256267 := bstep (se 1 (by rfl) ⟨942200, by rfl⟩ : syracuseStep 1256267 = 1884401) B1884401
theorem B1256279 : Blo 834351 1256279 := bstep (se 1 (by rfl) ⟨942209, by rfl⟩ : syracuseStep 1256279 = 1884419) B1884419
theorem B1584011 : Blo 834351 1584011 := bstep (se 1 (by rfl) ⟨1188008, by rfl⟩ : syracuseStep 1584011 = 2376017) B2376017
theorem B1256345 : Blo 834351 1256345 := bstep (se 2 (by rfl) ⟨471129, by rfl⟩ : syracuseStep 1256345 = 942259) B942259
theorem B1059799 : Blo 834351 1059799 := bstep (se 1 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 1059799 = 1589699) B1589699
theorem B1879001 : Blo 834351 1879001 := bstep (se 2 (by rfl) ⟨704625, by rfl⟩ : syracuseStep 1879001 = 1409251) B1409251
theorem B1256459 : Blo 834351 1256459 := bstep (se 1 (by rfl) ⟨942344, by rfl⟩ : syracuseStep 1256459 = 1884689) B1884689
theorem B8137745 : Blo 834351 8137745 := bstep (se 2 (by rfl) ⟨3051654, by rfl⟩ : syracuseStep 8137745 = 6103309) B6103309
theorem B1256471 : Blo 834351 1256471 := bstep (se 1 (by rfl) ⟨942353, by rfl⟩ : syracuseStep 1256471 = 1884707) B1884707
theorem B1879091 : Blo 834351 1879091 := bstep (se 1 (by rfl) ⟨1409318, by rfl⟩ : syracuseStep 1879091 = 2818637) B2818637
theorem B1584193 : Blo 834351 1584193 := bstep (se 2 (by rfl) ⟨594072, by rfl⟩ : syracuseStep 1584193 = 1188145) B1188145
theorem B1879127 : Blo 834351 1879127 := bstep (se 1 (by rfl) ⟨1409345, by rfl⟩ : syracuseStep 1879127 = 2818691) B2818691
theorem B1256537 : Blo 834351 1256537 := bstep (se 2 (by rfl) ⟨471201, by rfl⟩ : syracuseStep 1256537 = 942403) B942403
theorem B1256651 : Blo 834351 1256651 := bstep (se 1 (by rfl) ⟨942488, by rfl⟩ : syracuseStep 1256651 = 1884977) B1884977
theorem B1256663 : Blo 834351 1256663 := bstep (se 1 (by rfl) ⟨942497, by rfl⟩ : syracuseStep 1256663 = 1884995) B1884995
theorem B1879307 : Blo 834351 1879307 := bstep (se 1 (by rfl) ⟨1409480, by rfl⟩ : syracuseStep 1879307 = 2818961) B2818961
theorem B1256729 : Blo 834351 1256729 := bstep (se 2 (by rfl) ⟨471273, by rfl⟩ : syracuseStep 1256729 = 942547) B942547
theorem B1879361 : Blo 834351 1879361 := bstep (se 2 (by rfl) ⟨704760, by rfl⟩ : syracuseStep 1879361 = 1409521) B1409521
theorem B1256843 : Blo 834351 1256843 := bstep (se 1 (by rfl) ⟨942632, by rfl⟩ : syracuseStep 1256843 = 1885265) B1885265
theorem B1584535 : Blo 834351 1584535 := bstep (se 1 (by rfl) ⟨1188401, by rfl⟩ : syracuseStep 1584535 = 2376803) B2376803
theorem B1256855 : Blo 834351 1256855 := bstep (se 1 (by rfl) ⟨942641, by rfl⟩ : syracuseStep 1256855 = 1885283) B1885283
theorem B1256921 : Blo 834351 1256921 := bstep (se 2 (by rfl) ⟨471345, by rfl⟩ : syracuseStep 1256921 = 942691) B942691
theorem B1879577 : Blo 834351 1879577 := bstep (se 2 (by rfl) ⟨704841, by rfl⟩ : syracuseStep 1879577 = 1409683) B1409683
theorem B1257035 : Blo 834351 1257035 := bstep (se 1 (by rfl) ⟨942776, by rfl⟩ : syracuseStep 1257035 = 1885553) B1885553
theorem B1257047 : Blo 834351 1257047 := bstep (se 1 (by rfl) ⟨942785, by rfl⟩ : syracuseStep 1257047 = 1885571) B1885571
theorem B1584755 : Blo 834351 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B1879667 : Blo 834351 1879667 := bstep (se 1 (by rfl) ⟨1409750, by rfl⟩ : syracuseStep 1879667 = 2819501) B2819501
theorem B1879703 : Blo 834351 1879703 := bstep (se 1 (by rfl) ⟨1409777, by rfl⟩ : syracuseStep 1879703 = 2819555) B2819555
theorem B1257113 : Blo 834351 1257113 := bstep (se 2 (by rfl) ⟨471417, by rfl⟩ : syracuseStep 1257113 = 942835) B942835
theorem B1257227 : Blo 834351 1257227 := bstep (se 1 (by rfl) ⟨942920, by rfl⟩ : syracuseStep 1257227 = 1885841) B1885841
theorem B1257239 : Blo 834351 1257239 := bstep (se 1 (by rfl) ⟨942929, by rfl⟩ : syracuseStep 1257239 = 1885859) B1885859
theorem B1879883 : Blo 834351 1879883 := bstep (se 1 (by rfl) ⟨1409912, by rfl⟩ : syracuseStep 1879883 = 2819825) B2819825
theorem B1584983 : Blo 834351 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B1257305 : Blo 834351 1257305 := bstep (se 2 (by rfl) ⟨471489, by rfl⟩ : syracuseStep 1257305 = 942979) B942979
theorem B1879937 : Blo 834351 1879937 := bstep (se 2 (by rfl) ⟨704976, by rfl⟩ : syracuseStep 1879937 = 1409953) B1409953
theorem B1257419 : Blo 834351 1257419 := bstep (se 1 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 1257419 = 1886129) B1886129
theorem B1257431 : Blo 834351 1257431 := bstep (se 1 (by rfl) ⟨943073, by rfl⟩ : syracuseStep 1257431 = 1886147) B1886147
theorem B12857305 : Blo 834351 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B4239377 : Blo 834351 4239377 := bstep (se 2 (by rfl) ⟨1589766, by rfl⟩ : syracuseStep 4239377 = 3179533) B3179533
theorem B1257497 : Blo 834351 1257497 := bstep (se 2 (by rfl) ⟨471561, by rfl⟩ : syracuseStep 1257497 = 943123) B943123
theorem B1585241 : Blo 834351 1585241 := bstep (se 2 (by rfl) ⟨594465, by rfl⟩ : syracuseStep 1585241 = 1188931) B1188931
theorem B1880153 : Blo 834351 1880153 := bstep (se 2 (by rfl) ⟨705057, by rfl⟩ : syracuseStep 1880153 = 1410115) B1410115
theorem B1880243 : Blo 834351 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B4239539 : Blo 834351 4239539 := bstep (se 1 (by rfl) ⟨3179654, by rfl⟩ : syracuseStep 4239539 = 6359309) B6359309
theorem B1880279 : Blo 834351 1880279 := bstep (se 1 (by rfl) ⟨1410209, by rfl⟩ : syracuseStep 1880279 = 2820419) B2820419
theorem B10170629 : Blo 834351 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B1880459 : Blo 834351 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B1880513 : Blo 834351 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B1585651 : Blo 834351 1585651 := bstep (se 1 (by rfl) ⟨1189238, by rfl⟩ : syracuseStep 1585651 = 2378477) B2378477
theorem B2863667 : Blo 834351 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B1782337 : Blo 834351 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B1880729 : Blo 834351 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B27177713 : Blo 834351 27177713 := bstep (se 2 (by rfl) ⟨10191642, by rfl⟩ : syracuseStep 27177713 = 20383285) B20383285
theorem B1880819 : Blo 834351 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B1880855 : Blo 834351 1880855 := bstep (se 1 (by rfl) ⟨1410641, by rfl⟩ : syracuseStep 1880855 = 2821283) B2821283
theorem B9679661 : Blo 834351 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B2143027 : Blo 834351 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1881035 : Blo 834351 1881035 := bstep (se 1 (by rfl) ⟨1410776, by rfl⟩ : syracuseStep 1881035 = 2821553) B2821553
theorem B1586137 : Blo 834351 1586137 := bstep (se 2 (by rfl) ⟨594801, by rfl⟩ : syracuseStep 1586137 = 1189603) B1189603
theorem B1881089 : Blo 834351 1881089 := bstep (se 2 (by rfl) ⟨705408, by rfl⟩ : syracuseStep 1881089 = 1410817) B1410817
theorem B1881305 : Blo 834351 1881305 := bstep (se 2 (by rfl) ⟨705489, by rfl⟩ : syracuseStep 1881305 = 1410979) B1410979
theorem B2012377 : Blo 834351 2012377 := bstep (se 2 (by rfl) ⟨754641, by rfl⟩ : syracuseStep 2012377 = 1509283) B1509283
theorem B1881395 : Blo 834351 1881395 := bstep (se 1 (by rfl) ⟨1411046, by rfl⟩ : syracuseStep 1881395 = 2822093) B2822093
theorem B1881431 : Blo 834351 1881431 := bstep (se 1 (by rfl) ⟨1411073, by rfl⟩ : syracuseStep 1881431 = 2822147) B2822147
theorem B1193305 : Blo 834351 1193305 := bstep (se 2 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 1193305 = 894979) B894979
theorem B6862259 : Blo 834351 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B1586699 : Blo 834351 1586699 := bstep (se 1 (by rfl) ⟨1190024, by rfl⟩ : syracuseStep 1586699 = 2380049) B2380049
theorem B1881611 : Blo 834351 1881611 := bstep (se 1 (by rfl) ⟨1411208, by rfl⟩ : syracuseStep 1881611 = 2822417) B2822417
theorem B1881665 : Blo 834351 1881665 := bstep (se 2 (by rfl) ⟨705624, by rfl⟩ : syracuseStep 1881665 = 1411249) B1411249
theorem B3815063 : Blo 834351 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B1586881 : Blo 834351 1586881 := bstep (se 2 (by rfl) ⟨595080, by rfl⟩ : syracuseStep 1586881 = 1190161) B1190161
theorem B10860293 : Blo 834351 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B1881881 : Blo 834351 1881881 := bstep (se 2 (by rfl) ⟨705705, by rfl⟩ : syracuseStep 1881881 = 1411411) B1411411
theorem B1881971 : Blo 834351 1881971 := bstep (se 1 (by rfl) ⟨1411478, by rfl⟩ : syracuseStep 1881971 = 2822957) B2822957
theorem B5355395 : Blo 834351 5355395 := bstep (se 1 (by rfl) ⟨4016546, by rfl⟩ : syracuseStep 5355395 = 8033093) B8033093
theorem B1882007 : Blo 834351 1882007 := bstep (se 1 (by rfl) ⟨1411505, by rfl⟩ : syracuseStep 1882007 = 2823011) B2823011
theorem B29013977 : Blo 834351 29013977 := bstep (se 2 (by rfl) ⟨10880241, by rfl⟩ : syracuseStep 29013977 = 21760483) B21760483
theorem B1882187 : Blo 834351 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B4241483 : Blo 834351 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B3225689 : Blo 834351 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B1882241 : Blo 834351 1882241 := bstep (se 2 (by rfl) ⟨705840, by rfl⟩ : syracuseStep 1882241 = 1411681) B1411681
theorem B1882457 : Blo 834351 1882457 := bstep (se 2 (by rfl) ⟨705921, by rfl⟩ : syracuseStep 1882457 = 1411843) B1411843
theorem B12073333 : Blo 834351 12073333 := bstep (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) B1131875
theorem B1587595 : Blo 834351 1587595 := bstep (se 1 (by rfl) ⟨1190696, by rfl⟩ : syracuseStep 1587595 = 2381393) B2381393
theorem B1784243 : Blo 834351 1784243 := bstep (se 1 (by rfl) ⟨1338182, by rfl⟩ : syracuseStep 1784243 = 2676365) B2676365
theorem B1882547 : Blo 834351 1882547 := bstep (se 1 (by rfl) ⟨1411910, by rfl⟩ : syracuseStep 1882547 = 2823821) B2823821
theorem B1587671 : Blo 834351 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B1882583 : Blo 834351 1882583 := bstep (se 1 (by rfl) ⟨1411937, by rfl⟩ : syracuseStep 1882583 = 2823875) B2823875
theorem B2112065 : Blo 834351 2112065 := bstep (se 2 (by rfl) ⟨792024, by rfl⟩ : syracuseStep 2112065 = 1584049) B1584049
theorem B2013761 : Blo 834351 2013761 := bstep (se 2 (by rfl) ⟨755160, by rfl⟩ : syracuseStep 2013761 = 1510321) B1510321
theorem B1882763 : Blo 834351 1882763 := bstep (se 1 (by rfl) ⟨1412072, by rfl⟩ : syracuseStep 1882763 = 2824145) B2824145
theorem B1882817 : Blo 834351 1882817 := bstep (se 2 (by rfl) ⟨706056, by rfl⟩ : syracuseStep 1882817 = 1412113) B1412113
theorem B834359 : Blo 834351 834359 := bstep (se 1 (by rfl) ⟨625769, by rfl⟩ : syracuseStep 834359 = 1251539) B1251539
theorem B834379 : Blo 834351 834379 := bstep (se 1 (by rfl) ⟨625784, by rfl⟩ : syracuseStep 834379 = 1251569) B1251569
theorem B834391 : Blo 834351 834391 := bstep (se 1 (by rfl) ⟨625793, by rfl⟩ : syracuseStep 834391 = 1251587) B1251587
theorem B834411 : Blo 834351 834411 := bstep (se 1 (by rfl) ⟨625808, by rfl⟩ : syracuseStep 834411 = 1251617) B1251617
theorem B834423 : Blo 834351 834423 := bstep (se 1 (by rfl) ⟨625817, by rfl⟩ : syracuseStep 834423 = 1251635) B1251635
theorem B834443 : Blo 834351 834443 := bstep (se 1 (by rfl) ⟨625832, by rfl⟩ : syracuseStep 834443 = 1251665) B1251665
theorem B834455 : Blo 834351 834455 := bstep (se 1 (by rfl) ⟨625841, by rfl⟩ : syracuseStep 834455 = 1251683) B1251683
theorem B1784729 : Blo 834351 1784729 := bstep (se 2 (by rfl) ⟨669273, by rfl⟩ : syracuseStep 1784729 = 1338547) B1338547
theorem B1883033 : Blo 834351 1883033 := bstep (se 2 (by rfl) ⟨706137, by rfl⟩ : syracuseStep 1883033 = 1412275) B1412275
theorem B834475 : Blo 834351 834475 := bstep (se 1 (by rfl) ⟨625856, by rfl⟩ : syracuseStep 834475 = 1251713) B1251713
theorem B834487 : Blo 834351 834487 := bstep (se 1 (by rfl) ⟨625865, by rfl⟩ : syracuseStep 834487 = 1251731) B1251731
theorem B834507 : Blo 834351 834507 := bstep (se 1 (by rfl) ⟨625880, by rfl⟩ : syracuseStep 834507 = 1251761) B1251761
theorem B834519 : Blo 834351 834519 := bstep (se 1 (by rfl) ⟨625889, by rfl⟩ : syracuseStep 834519 = 1251779) B1251779
theorem B834539 : Blo 834351 834539 := bstep (se 1 (by rfl) ⟨625904, by rfl⟩ : syracuseStep 834539 = 1251809) B1251809
theorem B1883123 : Blo 834351 1883123 := bstep (se 1 (by rfl) ⟨1412342, by rfl⟩ : syracuseStep 1883123 = 2824685) B2824685
theorem B834551 : Blo 834351 834551 := bstep (se 1 (by rfl) ⟨625913, by rfl⟩ : syracuseStep 834551 = 1251827) B1251827
theorem B834571 : Blo 834351 834571 := bstep (se 1 (by rfl) ⟨625928, by rfl⟩ : syracuseStep 834571 = 1251857) B1251857
theorem B834583 : Blo 834351 834583 := bstep (se 1 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 834583 = 1251875) B1251875
theorem B1883159 : Blo 834351 1883159 := bstep (se 1 (by rfl) ⟨1412369, by rfl⟩ : syracuseStep 1883159 = 2824739) B2824739
theorem B834603 : Blo 834351 834603 := bstep (se 1 (by rfl) ⟨625952, by rfl⟩ : syracuseStep 834603 = 1251905) B1251905
theorem B834615 : Blo 834351 834615 := bstep (se 1 (by rfl) ⟨625961, by rfl⟩ : syracuseStep 834615 = 1251923) B1251923
theorem B834635 : Blo 834351 834635 := bstep (se 1 (by rfl) ⟨625976, by rfl⟩ : syracuseStep 834635 = 1251953) B1251953
theorem B4766795 : Blo 834351 4766795 := bstep (se 1 (by rfl) ⟨3575096, by rfl⟩ : syracuseStep 4766795 = 7150193) B7150193
theorem B834647 : Blo 834351 834647 := bstep (se 1 (by rfl) ⟨625985, by rfl⟩ : syracuseStep 834647 = 1251971) B1251971
theorem B2112601 : Blo 834351 2112601 := bstep (se 2 (by rfl) ⟨792225, by rfl⟩ : syracuseStep 2112601 = 1584451) B1584451
theorem B834667 : Blo 834351 834667 := bstep (se 1 (by rfl) ⟨626000, by rfl⟩ : syracuseStep 834667 = 1252001) B1252001
theorem B1588339 : Blo 834351 1588339 := bstep (se 1 (by rfl) ⟨1191254, by rfl⟩ : syracuseStep 1588339 = 2382509) B2382509
theorem B834679 : Blo 834351 834679 := bstep (se 1 (by rfl) ⟨626009, by rfl⟩ : syracuseStep 834679 = 1252019) B1252019
theorem B834699 : Blo 834351 834699 := bstep (se 1 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 834699 = 1252049) B1252049
theorem B834711 : Blo 834351 834711 := bstep (se 1 (by rfl) ⟨626033, by rfl⟩ : syracuseStep 834711 = 1252067) B1252067
theorem B834731 : Blo 834351 834731 := bstep (se 1 (by rfl) ⟨626048, by rfl⟩ : syracuseStep 834731 = 1252097) B1252097
theorem B834743 : Blo 834351 834743 := bstep (se 1 (by rfl) ⟨626057, by rfl⟩ : syracuseStep 834743 = 1252115) B1252115
theorem B834763 : Blo 834351 834763 := bstep (se 1 (by rfl) ⟨626072, by rfl⟩ : syracuseStep 834763 = 1252145) B1252145
theorem B1883339 : Blo 834351 1883339 := bstep (se 1 (by rfl) ⟨1412504, by rfl⟩ : syracuseStep 1883339 = 2825009) B2825009
theorem B834775 : Blo 834351 834775 := bstep (se 1 (by rfl) ⟨626081, by rfl⟩ : syracuseStep 834775 = 1252163) B1252163
theorem B834795 : Blo 834351 834795 := bstep (se 1 (by rfl) ⟨626096, by rfl⟩ : syracuseStep 834795 = 1252193) B1252193
theorem B834807 : Blo 834351 834807 := bstep (se 1 (by rfl) ⟨626105, by rfl⟩ : syracuseStep 834807 = 1252211) B1252211
theorem B1883393 : Blo 834351 1883393 := bstep (se 2 (by rfl) ⟨706272, by rfl⟩ : syracuseStep 1883393 = 1412545) B1412545
theorem B834827 : Blo 834351 834827 := bstep (se 1 (by rfl) ⟨626120, by rfl⟩ : syracuseStep 834827 = 1252241) B1252241
theorem B834839 : Blo 834351 834839 := bstep (se 1 (by rfl) ⟨626129, by rfl⟩ : syracuseStep 834839 = 1252259) B1252259
theorem B834859 : Blo 834351 834859 := bstep (se 1 (by rfl) ⟨626144, by rfl⟩ : syracuseStep 834859 = 1252289) B1252289
theorem B834871 : Blo 834351 834871 := bstep (se 1 (by rfl) ⟨626153, by rfl⟩ : syracuseStep 834871 = 1252307) B1252307
theorem B834891 : Blo 834351 834891 := bstep (se 1 (by rfl) ⟨626168, by rfl⟩ : syracuseStep 834891 = 1252337) B1252337
theorem B834903 : Blo 834351 834903 := bstep (se 1 (by rfl) ⟨626177, by rfl⟩ : syracuseStep 834903 = 1252355) B1252355
theorem B1588567 : Blo 834351 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B834923 : Blo 834351 834923 := bstep (se 1 (by rfl) ⟨626192, by rfl⟩ : syracuseStep 834923 = 1252385) B1252385
theorem B834935 : Blo 834351 834935 := bstep (se 1 (by rfl) ⟨626201, by rfl⟩ : syracuseStep 834935 = 1252403) B1252403
theorem B834955 : Blo 834351 834955 := bstep (se 1 (by rfl) ⟨626216, by rfl⟩ : syracuseStep 834955 = 1252433) B1252433
theorem B834967 : Blo 834351 834967 := bstep (se 1 (by rfl) ⟨626225, by rfl⟩ : syracuseStep 834967 = 1252451) B1252451
theorem B834987 : Blo 834351 834987 := bstep (se 1 (by rfl) ⟨626240, by rfl⟩ : syracuseStep 834987 = 1252481) B1252481
theorem B834999 : Blo 834351 834999 := bstep (se 1 (by rfl) ⟨626249, by rfl⟩ : syracuseStep 834999 = 1252499) B1252499
theorem B1588673 : Blo 834351 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B835019 : Blo 834351 835019 := bstep (se 1 (by rfl) ⟨626264, by rfl⟩ : syracuseStep 835019 = 1252529) B1252529
theorem B835031 : Blo 834351 835031 := bstep (se 1 (by rfl) ⟨626273, by rfl⟩ : syracuseStep 835031 = 1252547) B1252547
theorem B9649625 : Blo 834351 9649625 := bstep (se 2 (by rfl) ⟨3618609, by rfl⟩ : syracuseStep 9649625 = 7237219) B7237219
theorem B1883609 : Blo 834351 1883609 := bstep (se 2 (by rfl) ⟨706353, by rfl⟩ : syracuseStep 1883609 = 1412707) B1412707
theorem B835051 : Blo 834351 835051 := bstep (se 1 (by rfl) ⟨626288, by rfl⟩ : syracuseStep 835051 = 1252577) B1252577
theorem B835063 : Blo 834351 835063 := bstep (se 1 (by rfl) ⟨626297, by rfl⟩ : syracuseStep 835063 = 1252595) B1252595
theorem B835083 : Blo 834351 835083 := bstep (se 1 (by rfl) ⟨626312, by rfl⟩ : syracuseStep 835083 = 1252625) B1252625
theorem B835095 : Blo 834351 835095 := bstep (se 1 (by rfl) ⟨626321, by rfl⟩ : syracuseStep 835095 = 1252643) B1252643
theorem B835115 : Blo 834351 835115 := bstep (se 1 (by rfl) ⟨626336, by rfl⟩ : syracuseStep 835115 = 1252673) B1252673
theorem B1883699 : Blo 834351 1883699 := bstep (se 1 (by rfl) ⟨1412774, by rfl⟩ : syracuseStep 1883699 = 2825549) B2825549
theorem B835127 : Blo 834351 835127 := bstep (se 1 (by rfl) ⟨626345, by rfl⟩ : syracuseStep 835127 = 1252691) B1252691
theorem B835147 : Blo 834351 835147 := bstep (se 1 (by rfl) ⟨626360, by rfl⟩ : syracuseStep 835147 = 1252721) B1252721
theorem B3391051 : Blo 834351 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B1883735 : Blo 834351 1883735 := bstep (se 1 (by rfl) ⟨1412801, by rfl⟩ : syracuseStep 1883735 = 2825603) B2825603
theorem B835159 : Blo 834351 835159 := bstep (se 1 (by rfl) ⟨626369, by rfl⟩ : syracuseStep 835159 = 1252739) B1252739
theorem B2539097 : Blo 834351 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B1588825 : Blo 834351 1588825 := bstep (se 2 (by rfl) ⟨595809, by rfl⟩ : syracuseStep 1588825 = 1191619) B1191619
theorem B835179 : Blo 834351 835179 := bstep (se 1 (by rfl) ⟨626384, by rfl⟩ : syracuseStep 835179 = 1252769) B1252769
theorem B835191 : Blo 834351 835191 := bstep (se 1 (by rfl) ⟨626393, by rfl⟩ : syracuseStep 835191 = 1252787) B1252787
theorem B1785473 : Blo 834351 1785473 := bstep (se 2 (by rfl) ⟨669552, by rfl⟩ : syracuseStep 1785473 = 1339105) B1339105
theorem B835211 : Blo 834351 835211 := bstep (se 1 (by rfl) ⟨626408, by rfl⟩ : syracuseStep 835211 = 1252817) B1252817
theorem B835223 : Blo 834351 835223 := bstep (se 1 (by rfl) ⟨626417, by rfl⟩ : syracuseStep 835223 = 1252835) B1252835
theorem B835243 : Blo 834351 835243 := bstep (se 1 (by rfl) ⟨626432, by rfl⟩ : syracuseStep 835243 = 1252865) B1252865
theorem B835255 : Blo 834351 835255 := bstep (se 1 (by rfl) ⟨626441, by rfl⟩ : syracuseStep 835255 = 1252883) B1252883
theorem B835275 : Blo 834351 835275 := bstep (se 1 (by rfl) ⟨626456, by rfl⟩ : syracuseStep 835275 = 1252913) B1252913
theorem B835287 : Blo 834351 835287 := bstep (se 1 (by rfl) ⟨626465, by rfl⟩ : syracuseStep 835287 = 1252931) B1252931
theorem B835307 : Blo 834351 835307 := bstep (se 1 (by rfl) ⟨626480, by rfl⟩ : syracuseStep 835307 = 1252961) B1252961
theorem B835319 : Blo 834351 835319 := bstep (se 1 (by rfl) ⟨626489, by rfl⟩ : syracuseStep 835319 = 1252979) B1252979
theorem B835339 : Blo 834351 835339 := bstep (se 1 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 835339 = 1253009) B1253009
theorem B1883915 : Blo 834351 1883915 := bstep (se 1 (by rfl) ⟨1412936, by rfl⟩ : syracuseStep 1883915 = 2825873) B2825873
theorem B835351 : Blo 834351 835351 := bstep (se 1 (by rfl) ⟨626513, by rfl⟩ : syracuseStep 835351 = 1253027) B1253027
theorem B835371 : Blo 834351 835371 := bstep (se 1 (by rfl) ⟨626528, by rfl⟩ : syracuseStep 835371 = 1253057) B1253057
theorem B835383 : Blo 834351 835383 := bstep (se 1 (by rfl) ⟨626537, by rfl⟩ : syracuseStep 835383 = 1253075) B1253075
theorem B1883969 : Blo 834351 1883969 := bstep (se 2 (by rfl) ⟨706488, by rfl⟩ : syracuseStep 1883969 = 1412977) B1412977
theorem B4243265 : Blo 834351 4243265 := bstep (se 2 (by rfl) ⟨1591224, by rfl⟩ : syracuseStep 4243265 = 3182449) B3182449
theorem B835403 : Blo 834351 835403 := bstep (se 1 (by rfl) ⟨626552, by rfl⟩ : syracuseStep 835403 = 1253105) B1253105
theorem B835415 : Blo 834351 835415 := bstep (se 1 (by rfl) ⟨626561, by rfl⟩ : syracuseStep 835415 = 1253123) B1253123
theorem B1130329 : Blo 834351 1130329 := bstep (se 2 (by rfl) ⟨423873, by rfl⟩ : syracuseStep 1130329 = 847747) B847747
theorem B835435 : Blo 834351 835435 := bstep (se 1 (by rfl) ⟨626576, by rfl⟩ : syracuseStep 835435 = 1253153) B1253153
theorem B835447 : Blo 834351 835447 := bstep (se 1 (by rfl) ⟨626585, by rfl⟩ : syracuseStep 835447 = 1253171) B1253171
theorem B835467 : Blo 834351 835467 := bstep (se 1 (by rfl) ⟨626600, by rfl⟩ : syracuseStep 835467 = 1253201) B1253201
theorem B835479 : Blo 834351 835479 := bstep (se 1 (by rfl) ⟨626609, by rfl⟩ : syracuseStep 835479 = 1253219) B1253219
theorem B835499 : Blo 834351 835499 := bstep (se 1 (by rfl) ⟨626624, by rfl⟩ : syracuseStep 835499 = 1253249) B1253249
theorem B835511 : Blo 834351 835511 := bstep (se 1 (by rfl) ⟨626633, by rfl⟩ : syracuseStep 835511 = 1253267) B1253267
theorem B835531 : Blo 834351 835531 := bstep (se 1 (by rfl) ⟨626648, by rfl⟩ : syracuseStep 835531 = 1253297) B1253297
theorem B835543 : Blo 834351 835543 := bstep (se 1 (by rfl) ⟨626657, by rfl⟩ : syracuseStep 835543 = 1253315) B1253315
theorem B8044505 : Blo 834351 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B835563 : Blo 834351 835563 := bstep (se 1 (by rfl) ⟨626672, by rfl⟩ : syracuseStep 835563 = 1253345) B1253345
theorem B835575 : Blo 834351 835575 := bstep (se 1 (by rfl) ⟨626681, by rfl⟩ : syracuseStep 835575 = 1253363) B1253363
theorem B835595 : Blo 834351 835595 := bstep (se 1 (by rfl) ⟨626696, by rfl⟩ : syracuseStep 835595 = 1253393) B1253393
theorem B835607 : Blo 834351 835607 := bstep (se 1 (by rfl) ⟨626705, by rfl⟩ : syracuseStep 835607 = 1253411) B1253411
theorem B1884185 : Blo 834351 1884185 := bstep (se 2 (by rfl) ⟨706569, by rfl⟩ : syracuseStep 1884185 = 1413139) B1413139
theorem B835627 : Blo 834351 835627 := bstep (se 1 (by rfl) ⟨626720, by rfl⟩ : syracuseStep 835627 = 1253441) B1253441
theorem B835639 : Blo 834351 835639 := bstep (se 1 (by rfl) ⟨626729, by rfl⟩ : syracuseStep 835639 = 1253459) B1253459
theorem B835659 : Blo 834351 835659 := bstep (se 1 (by rfl) ⟨626744, by rfl⟩ : syracuseStep 835659 = 1253489) B1253489
theorem B835671 : Blo 834351 835671 := bstep (se 1 (by rfl) ⟨626753, by rfl⟩ : syracuseStep 835671 = 1253507) B1253507
theorem B835691 : Blo 834351 835691 := bstep (se 1 (by rfl) ⟨626768, by rfl⟩ : syracuseStep 835691 = 1253537) B1253537
theorem B1884275 : Blo 834351 1884275 := bstep (se 1 (by rfl) ⟨1413206, by rfl⟩ : syracuseStep 1884275 = 2826413) B2826413
theorem B835703 : Blo 834351 835703 := bstep (se 1 (by rfl) ⟨626777, by rfl⟩ : syracuseStep 835703 = 1253555) B1253555
theorem B835723 : Blo 834351 835723 := bstep (se 1 (by rfl) ⟨626792, by rfl⟩ : syracuseStep 835723 = 1253585) B1253585
theorem B835735 : Blo 834351 835735 := bstep (se 1 (by rfl) ⟨626801, by rfl⟩ : syracuseStep 835735 = 1253603) B1253603
theorem B1884311 : Blo 834351 1884311 := bstep (se 1 (by rfl) ⟨1413233, by rfl⟩ : syracuseStep 1884311 = 2826467) B2826467
theorem B835755 : Blo 834351 835755 := bstep (se 1 (by rfl) ⟨626816, by rfl⟩ : syracuseStep 835755 = 1253633) B1253633
theorem B2113715 : Blo 834351 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B835767 : Blo 834351 835767 := bstep (se 1 (by rfl) ⟨626825, by rfl⟩ : syracuseStep 835767 = 1253651) B1253651
theorem B835787 : Blo 834351 835787 := bstep (se 1 (by rfl) ⟨626840, by rfl⟩ : syracuseStep 835787 = 1253681) B1253681
theorem B835799 : Blo 834351 835799 := bstep (se 1 (by rfl) ⟨626849, by rfl⟩ : syracuseStep 835799 = 1253699) B1253699
theorem B835819 : Blo 834351 835819 := bstep (se 1 (by rfl) ⟨626864, by rfl⟩ : syracuseStep 835819 = 1253729) B1253729
theorem B835831 : Blo 834351 835831 := bstep (se 1 (by rfl) ⟨626873, by rfl⟩ : syracuseStep 835831 = 1253747) B1253747
theorem B835851 : Blo 834351 835851 := bstep (se 1 (by rfl) ⟨626888, by rfl⟩ : syracuseStep 835851 = 1253777) B1253777
theorem B835863 : Blo 834351 835863 := bstep (se 1 (by rfl) ⟨626897, by rfl⟩ : syracuseStep 835863 = 1253795) B1253795
theorem B835883 : Blo 834351 835883 := bstep (se 1 (by rfl) ⟨626912, by rfl⟩ : syracuseStep 835883 = 1253825) B1253825
theorem B835895 : Blo 834351 835895 := bstep (se 1 (by rfl) ⟨626921, by rfl⟩ : syracuseStep 835895 = 1253843) B1253843
theorem B835915 : Blo 834351 835915 := bstep (se 1 (by rfl) ⟨626936, by rfl⟩ : syracuseStep 835915 = 1253873) B1253873
theorem B1884491 : Blo 834351 1884491 := bstep (se 1 (by rfl) ⟨1413368, by rfl⟩ : syracuseStep 1884491 = 2826737) B2826737
theorem B835927 : Blo 834351 835927 := bstep (se 1 (by rfl) ⟨626945, by rfl⟩ : syracuseStep 835927 = 1253891) B1253891
theorem B835947 : Blo 834351 835947 := bstep (se 1 (by rfl) ⟨626960, by rfl⟩ : syracuseStep 835947 = 1253921) B1253921
theorem B835959 : Blo 834351 835959 := bstep (se 1 (by rfl) ⟨626969, by rfl⟩ : syracuseStep 835959 = 1253939) B1253939
theorem B1884545 : Blo 834351 1884545 := bstep (se 2 (by rfl) ⟨706704, by rfl⟩ : syracuseStep 1884545 = 1413409) B1413409
theorem B835979 : Blo 834351 835979 := bstep (se 1 (by rfl) ⟨626984, by rfl⟩ : syracuseStep 835979 = 1253969) B1253969
theorem B835991 : Blo 834351 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B836011 : Blo 834351 836011 := bstep (se 1 (by rfl) ⟨627008, by rfl⟩ : syracuseStep 836011 = 1254017) B1254017
theorem B836023 : Blo 834351 836023 := bstep (se 1 (by rfl) ⟨627017, by rfl⟩ : syracuseStep 836023 = 1254035) B1254035
theorem B836043 : Blo 834351 836043 := bstep (se 1 (by rfl) ⟨627032, by rfl⟩ : syracuseStep 836043 = 1254065) B1254065
theorem B836055 : Blo 834351 836055 := bstep (se 1 (by rfl) ⟨627041, by rfl⟩ : syracuseStep 836055 = 1254083) B1254083
theorem B2114009 : Blo 834351 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B836075 : Blo 834351 836075 := bstep (se 1 (by rfl) ⟨627056, by rfl⟩ : syracuseStep 836075 = 1254113) B1254113
theorem B836087 : Blo 834351 836087 := bstep (se 1 (by rfl) ⟨627065, by rfl⟩ : syracuseStep 836087 = 1254131) B1254131
theorem B1786369 : Blo 834351 1786369 := bstep (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) B1339777
theorem B836107 : Blo 834351 836107 := bstep (se 1 (by rfl) ⟨627080, by rfl⟩ : syracuseStep 836107 = 1254161) B1254161
theorem B836119 : Blo 834351 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B836139 : Blo 834351 836139 := bstep (se 1 (by rfl) ⟨627104, by rfl⟩ : syracuseStep 836139 = 1254209) B1254209
theorem B836151 : Blo 834351 836151 := bstep (se 1 (by rfl) ⟨627113, by rfl⟩ : syracuseStep 836151 = 1254227) B1254227
theorem B836171 : Blo 834351 836171 := bstep (se 1 (by rfl) ⟨627128, by rfl⟩ : syracuseStep 836171 = 1254257) B1254257
theorem B836183 : Blo 834351 836183 := bstep (se 1 (by rfl) ⟨627137, by rfl⟩ : syracuseStep 836183 = 1254275) B1254275
theorem B1884761 : Blo 834351 1884761 := bstep (se 2 (by rfl) ⟨706785, by rfl⟩ : syracuseStep 1884761 = 1413571) B1413571
theorem B836203 : Blo 834351 836203 := bstep (se 1 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 836203 = 1254305) B1254305
theorem B836215 : Blo 834351 836215 := bstep (se 1 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 836215 = 1254323) B1254323
theorem B836235 : Blo 834351 836235 := bstep (se 1 (by rfl) ⟨627176, by rfl⟩ : syracuseStep 836235 = 1254353) B1254353
theorem B836247 : Blo 834351 836247 := bstep (se 1 (by rfl) ⟨627185, by rfl⟩ : syracuseStep 836247 = 1254371) B1254371
theorem B836267 : Blo 834351 836267 := bstep (se 1 (by rfl) ⟨627200, by rfl⟩ : syracuseStep 836267 = 1254401) B1254401
theorem B1884851 : Blo 834351 1884851 := bstep (se 1 (by rfl) ⟨1413638, by rfl⟩ : syracuseStep 1884851 = 2827277) B2827277
theorem B836279 : Blo 834351 836279 := bstep (se 1 (by rfl) ⟨627209, by rfl⟩ : syracuseStep 836279 = 1254419) B1254419
theorem B836299 : Blo 834351 836299 := bstep (se 1 (by rfl) ⟨627224, by rfl⟩ : syracuseStep 836299 = 1254449) B1254449
theorem B836311 : Blo 834351 836311 := bstep (se 1 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 836311 = 1254467) B1254467
theorem B1884887 : Blo 834351 1884887 := bstep (se 1 (by rfl) ⟨1413665, by rfl⟩ : syracuseStep 1884887 = 2827331) B2827331
theorem B836331 : Blo 834351 836331 := bstep (se 1 (by rfl) ⟨627248, by rfl⟩ : syracuseStep 836331 = 1254497) B1254497
theorem B836343 : Blo 834351 836343 := bstep (se 1 (by rfl) ⟨627257, by rfl⟩ : syracuseStep 836343 = 1254515) B1254515
theorem B836363 : Blo 834351 836363 := bstep (se 1 (by rfl) ⟨627272, by rfl⟩ : syracuseStep 836363 = 1254545) B1254545
theorem B836375 : Blo 834351 836375 := bstep (se 1 (by rfl) ⟨627281, by rfl⟩ : syracuseStep 836375 = 1254563) B1254563
theorem B836395 : Blo 834351 836395 := bstep (se 1 (by rfl) ⟨627296, by rfl⟩ : syracuseStep 836395 = 1254593) B1254593
theorem B836407 : Blo 834351 836407 := bstep (se 1 (by rfl) ⟨627305, by rfl⟩ : syracuseStep 836407 = 1254611) B1254611
theorem B836427 : Blo 834351 836427 := bstep (se 1 (by rfl) ⟨627320, by rfl⟩ : syracuseStep 836427 = 1254641) B1254641
theorem B836439 : Blo 834351 836439 := bstep (se 1 (by rfl) ⟨627329, by rfl⟩ : syracuseStep 836439 = 1254659) B1254659
theorem B1786711 : Blo 834351 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B836459 : Blo 834351 836459 := bstep (se 1 (by rfl) ⟨627344, by rfl⟩ : syracuseStep 836459 = 1254689) B1254689
theorem B1590131 : Blo 834351 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B836471 : Blo 834351 836471 := bstep (se 1 (by rfl) ⟨627353, by rfl⟩ : syracuseStep 836471 = 1254707) B1254707
theorem B3621763 : Blo 834351 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B3392387 : Blo 834351 3392387 := bstep (se 1 (by rfl) ⟨2544290, by rfl⟩ : syracuseStep 3392387 = 5088581) B5088581
theorem B836491 : Blo 834351 836491 := bstep (se 1 (by rfl) ⟨627368, by rfl⟩ : syracuseStep 836491 = 1254737) B1254737
theorem B1885067 : Blo 834351 1885067 := bstep (se 1 (by rfl) ⟨1413800, by rfl⟩ : syracuseStep 1885067 = 2827601) B2827601
theorem B836503 : Blo 834351 836503 := bstep (se 1 (by rfl) ⟨627377, by rfl⟩ : syracuseStep 836503 = 1254755) B1254755
theorem B836523 : Blo 834351 836523 := bstep (se 1 (by rfl) ⟨627392, by rfl⟩ : syracuseStep 836523 = 1254785) B1254785
theorem B836535 : Blo 834351 836535 := bstep (se 1 (by rfl) ⟨627401, by rfl⟩ : syracuseStep 836535 = 1254803) B1254803
theorem B1885121 : Blo 834351 1885121 := bstep (se 2 (by rfl) ⟨706920, by rfl⟩ : syracuseStep 1885121 = 1413841) B1413841
theorem B2540491 : Blo 834351 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B836555 : Blo 834351 836555 := bstep (se 1 (by rfl) ⟨627416, by rfl⟩ : syracuseStep 836555 = 1254833) B1254833
theorem B836567 : Blo 834351 836567 := bstep (se 1 (by rfl) ⟨627425, by rfl⟩ : syracuseStep 836567 = 1254851) B1254851
theorem B836587 : Blo 834351 836587 := bstep (se 1 (by rfl) ⟨627440, by rfl⟩ : syracuseStep 836587 = 1254881) B1254881
theorem B836599 : Blo 834351 836599 := bstep (se 1 (by rfl) ⟨627449, by rfl⟩ : syracuseStep 836599 = 1254899) B1254899
theorem B836619 : Blo 834351 836619 := bstep (se 1 (by rfl) ⟨627464, by rfl⟩ : syracuseStep 836619 = 1254929) B1254929
theorem B1590283 : Blo 834351 1590283 := bstep (se 1 (by rfl) ⟨1192712, by rfl⟩ : syracuseStep 1590283 = 2385425) B2385425
theorem B3621905 : Blo 834351 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B836631 : Blo 834351 836631 := bstep (se 1 (by rfl) ⟨627473, by rfl⟩ : syracuseStep 836631 = 1254947) B1254947
theorem B836651 : Blo 834351 836651 := bstep (se 1 (by rfl) ⟨627488, by rfl⟩ : syracuseStep 836651 = 1254977) B1254977
theorem B836663 : Blo 834351 836663 := bstep (se 1 (by rfl) ⟨627497, by rfl⟩ : syracuseStep 836663 = 1254995) B1254995
theorem B836683 : Blo 834351 836683 := bstep (se 1 (by rfl) ⟨627512, by rfl⟩ : syracuseStep 836683 = 1255025) B1255025
theorem B836695 : Blo 834351 836695 := bstep (se 1 (by rfl) ⟨627521, by rfl⟩ : syracuseStep 836695 = 1255043) B1255043
theorem B836715 : Blo 834351 836715 := bstep (se 1 (by rfl) ⟨627536, by rfl⟩ : syracuseStep 836715 = 1255073) B1255073
theorem B836727 : Blo 834351 836727 := bstep (se 1 (by rfl) ⟨627545, by rfl⟩ : syracuseStep 836727 = 1255091) B1255091
theorem B836747 : Blo 834351 836747 := bstep (se 1 (by rfl) ⟨627560, by rfl⟩ : syracuseStep 836747 = 1255121) B1255121
theorem B25805965 : Blo 834351 25805965 := bstep (se 3 (by rfl) ⟨4838618, by rfl⟩ : syracuseStep 25805965 = 9677237) B9677237
theorem B836759 : Blo 834351 836759 := bstep (se 1 (by rfl) ⟨627569, by rfl⟩ : syracuseStep 836759 = 1255139) B1255139
theorem B1885337 : Blo 834351 1885337 := bstep (se 2 (by rfl) ⟨707001, by rfl⟩ : syracuseStep 1885337 = 1414003) B1414003
theorem B836779 : Blo 834351 836779 := bstep (se 1 (by rfl) ⟨627584, by rfl⟩ : syracuseStep 836779 = 1255169) B1255169
theorem B836791 : Blo 834351 836791 := bstep (se 1 (by rfl) ⟨627593, by rfl⟩ : syracuseStep 836791 = 1255187) B1255187
theorem B836811 : Blo 834351 836811 := bstep (se 1 (by rfl) ⟨627608, by rfl⟩ : syracuseStep 836811 = 1255217) B1255217
theorem B836823 : Blo 834351 836823 := bstep (se 1 (by rfl) ⟨627617, by rfl⟩ : syracuseStep 836823 = 1255235) B1255235
theorem B836843 : Blo 834351 836843 := bstep (se 1 (by rfl) ⟨627632, by rfl⟩ : syracuseStep 836843 = 1255265) B1255265
theorem B1885427 : Blo 834351 1885427 := bstep (se 1 (by rfl) ⟨1414070, by rfl⟩ : syracuseStep 1885427 = 2828141) B2828141
theorem B836855 : Blo 834351 836855 := bstep (se 1 (by rfl) ⟨627641, by rfl⟩ : syracuseStep 836855 = 1255283) B1255283
theorem B836875 : Blo 834351 836875 := bstep (se 1 (by rfl) ⟨627656, by rfl⟩ : syracuseStep 836875 = 1255313) B1255313
theorem B836887 : Blo 834351 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B1885463 : Blo 834351 1885463 := bstep (se 1 (by rfl) ⟨1414097, by rfl⟩ : syracuseStep 1885463 = 2828195) B2828195
theorem B6112547 : Blo 834351 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B836907 : Blo 834351 836907 := bstep (se 1 (by rfl) ⟨627680, by rfl⟩ : syracuseStep 836907 = 1255361) B1255361
theorem B21677357 : Blo 834351 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B836919 : Blo 834351 836919 := bstep (se 1 (by rfl) ⟨627689, by rfl⟩ : syracuseStep 836919 = 1255379) B1255379
theorem B836939 : Blo 834351 836939 := bstep (se 1 (by rfl) ⟨627704, by rfl⟩ : syracuseStep 836939 = 1255409) B1255409
theorem B836951 : Blo 834351 836951 := bstep (se 1 (by rfl) ⟨627713, by rfl⟩ : syracuseStep 836951 = 1255427) B1255427
theorem B1590617 : Blo 834351 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B836971 : Blo 834351 836971 := bstep (se 1 (by rfl) ⟨627728, by rfl⟩ : syracuseStep 836971 = 1255457) B1255457
theorem B836983 : Blo 834351 836983 := bstep (se 1 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 836983 = 1255475) B1255475
theorem B1787275 : Blo 834351 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B837003 : Blo 834351 837003 := bstep (se 1 (by rfl) ⟨627752, by rfl⟩ : syracuseStep 837003 = 1255505) B1255505
theorem B837015 : Blo 834351 837015 := bstep (se 1 (by rfl) ⟨627761, by rfl⟩ : syracuseStep 837015 = 1255523) B1255523
theorem B837035 : Blo 834351 837035 := bstep (se 1 (by rfl) ⟨627776, by rfl⟩ : syracuseStep 837035 = 1255553) B1255553
theorem B837047 : Blo 834351 837047 := bstep (se 1 (by rfl) ⟨627785, by rfl⟩ : syracuseStep 837047 = 1255571) B1255571
theorem B837067 : Blo 834351 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B1885643 : Blo 834351 1885643 := bstep (se 1 (by rfl) ⟨1414232, by rfl⟩ : syracuseStep 1885643 = 2828465) B2828465
theorem B837079 : Blo 834351 837079 := bstep (se 1 (by rfl) ⟨627809, by rfl⟩ : syracuseStep 837079 = 1255619) B1255619
theorem B837099 : Blo 834351 837099 := bstep (se 1 (by rfl) ⟨627824, by rfl⟩ : syracuseStep 837099 = 1255649) B1255649
theorem B837111 : Blo 834351 837111 := bstep (se 1 (by rfl) ⟨627833, by rfl⟩ : syracuseStep 837111 = 1255667) B1255667
theorem B1885697 : Blo 834351 1885697 := bstep (se 2 (by rfl) ⟨707136, by rfl⟩ : syracuseStep 1885697 = 1414273) B1414273
theorem B837131 : Blo 834351 837131 := bstep (se 1 (by rfl) ⟨627848, by rfl⟩ : syracuseStep 837131 = 1255697) B1255697
theorem B837143 : Blo 834351 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B837163 : Blo 834351 837163 := bstep (se 1 (by rfl) ⟨627872, by rfl⟩ : syracuseStep 837163 = 1255745) B1255745
theorem B837175 : Blo 834351 837175 := bstep (se 1 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 837175 = 1255763) B1255763
theorem B837195 : Blo 834351 837195 := bstep (se 1 (by rfl) ⟨627896, by rfl⟩ : syracuseStep 837195 = 1255793) B1255793
theorem B837207 : Blo 834351 837207 := bstep (se 1 (by rfl) ⟨627905, by rfl⟩ : syracuseStep 837207 = 1255811) B1255811
theorem B8570461 : Blo 834351 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B837227 : Blo 834351 837227 := bstep (se 1 (by rfl) ⟨627920, by rfl⟩ : syracuseStep 837227 = 1255841) B1255841
theorem B837239 : Blo 834351 837239 := bstep (se 1 (by rfl) ⟨627929, by rfl⟩ : syracuseStep 837239 = 1255859) B1255859
theorem B837259 : Blo 834351 837259 := bstep (se 1 (by rfl) ⟨627944, by rfl⟩ : syracuseStep 837259 = 1255889) B1255889
theorem B837271 : Blo 834351 837271 := bstep (se 1 (by rfl) ⟨627953, by rfl⟩ : syracuseStep 837271 = 1255907) B1255907
theorem B837291 : Blo 834351 837291 := bstep (se 1 (by rfl) ⟨627968, by rfl⟩ : syracuseStep 837291 = 1255937) B1255937
theorem B2541235 : Blo 834351 2541235 := bstep (se 1 (by rfl) ⟨1905926, by rfl⟩ : syracuseStep 2541235 = 3811853) B3811853
theorem B837303 : Blo 834351 837303 := bstep (se 1 (by rfl) ⟨627977, by rfl⟩ : syracuseStep 837303 = 1255955) B1255955
theorem B837323 : Blo 834351 837323 := bstep (se 1 (by rfl) ⟨627992, by rfl⟩ : syracuseStep 837323 = 1255985) B1255985
theorem B837335 : Blo 834351 837335 := bstep (se 1 (by rfl) ⟨628001, by rfl⟩ : syracuseStep 837335 = 1256003) B1256003
theorem B1885913 : Blo 834351 1885913 := bstep (se 2 (by rfl) ⟨707217, by rfl⟩ : syracuseStep 1885913 = 1414435) B1414435
theorem B837355 : Blo 834351 837355 := bstep (se 1 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 837355 = 1256033) B1256033
theorem B837367 : Blo 834351 837367 := bstep (se 1 (by rfl) ⟨628025, by rfl⟩ : syracuseStep 837367 = 1256051) B1256051
theorem B7161605 : Blo 834351 7161605 := bstep (se 4 (by rfl) ⟨671400, by rfl⟩ : syracuseStep 7161605 = 1342801) B1342801
theorem B837387 : Blo 834351 837387 := bstep (se 1 (by rfl) ⟨628040, by rfl⟩ : syracuseStep 837387 = 1256081) B1256081
theorem B837399 : Blo 834351 837399 := bstep (se 1 (by rfl) ⟨628049, by rfl⟩ : syracuseStep 837399 = 1256099) B1256099
theorem B837419 : Blo 834351 837419 := bstep (se 1 (by rfl) ⟨628064, by rfl⟩ : syracuseStep 837419 = 1256129) B1256129
theorem B1886003 : Blo 834351 1886003 := bstep (se 1 (by rfl) ⟨1414502, by rfl⟩ : syracuseStep 1886003 = 2829005) B2829005
theorem B837431 : Blo 834351 837431 := bstep (se 1 (by rfl) ⟨628073, by rfl⟩ : syracuseStep 837431 = 1256147) B1256147
theorem B837451 : Blo 834351 837451 := bstep (se 1 (by rfl) ⟨628088, by rfl⟩ : syracuseStep 837451 = 1256177) B1256177
theorem B837463 : Blo 834351 837463 := bstep (se 1 (by rfl) ⟨628097, by rfl⟩ : syracuseStep 837463 = 1256195) B1256195
theorem B1886039 : Blo 834351 1886039 := bstep (se 1 (by rfl) ⟨1414529, by rfl⟩ : syracuseStep 1886039 = 2829059) B2829059
theorem B837483 : Blo 834351 837483 := bstep (se 1 (by rfl) ⟨628112, by rfl⟩ : syracuseStep 837483 = 1256225) B1256225
theorem B837495 : Blo 834351 837495 := bstep (se 1 (by rfl) ⟨628121, by rfl⟩ : syracuseStep 837495 = 1256243) B1256243
theorem B837515 : Blo 834351 837515 := bstep (se 1 (by rfl) ⟨628136, by rfl⟩ : syracuseStep 837515 = 1256273) B1256273
theorem B837527 : Blo 834351 837527 := bstep (se 1 (by rfl) ⟨628145, by rfl⟩ : syracuseStep 837527 = 1256291) B1256291
theorem B837547 : Blo 834351 837547 := bstep (se 1 (by rfl) ⟨628160, by rfl⟩ : syracuseStep 837547 = 1256321) B1256321
theorem B837559 : Blo 834351 837559 := bstep (se 1 (by rfl) ⟨628169, by rfl⟩ : syracuseStep 837559 = 1256339) B1256339
theorem B837579 : Blo 834351 837579 := bstep (se 1 (by rfl) ⟨628184, by rfl⟩ : syracuseStep 837579 = 1256369) B1256369
theorem B837591 : Blo 834351 837591 := bstep (se 1 (by rfl) ⟨628193, by rfl⟩ : syracuseStep 837591 = 1256387) B1256387
theorem B1591255 : Blo 834351 1591255 := bstep (se 1 (by rfl) ⟨1193441, by rfl⟩ : syracuseStep 1591255 = 2386883) B2386883
theorem B837611 : Blo 834351 837611 := bstep (se 1 (by rfl) ⟨628208, by rfl⟩ : syracuseStep 837611 = 1256417) B1256417
theorem B837623 : Blo 834351 837623 := bstep (se 1 (by rfl) ⟨628217, by rfl⟩ : syracuseStep 837623 = 1256435) B1256435
theorem B837643 : Blo 834351 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B1886219 : Blo 834351 1886219 := bstep (se 1 (by rfl) ⟨1414664, by rfl⟩ : syracuseStep 1886219 = 2829329) B2829329
theorem B837655 : Blo 834351 837655 := bstep (se 1 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 837655 = 1256483) B1256483
theorem B837675 : Blo 834351 837675 := bstep (se 1 (by rfl) ⟨628256, by rfl⟩ : syracuseStep 837675 = 1256513) B1256513
theorem B837687 : Blo 834351 837687 := bstep (se 1 (by rfl) ⟨628265, by rfl⟩ : syracuseStep 837687 = 1256531) B1256531
theorem B1886273 : Blo 834351 1886273 := bstep (se 2 (by rfl) ⟨707352, by rfl⟩ : syracuseStep 1886273 = 1414705) B1414705
theorem B2115659 : Blo 834351 2115659 := bstep (se 1 (by rfl) ⟨1586744, by rfl⟩ : syracuseStep 2115659 = 3173489) B3173489
theorem B837707 : Blo 834351 837707 := bstep (se 1 (by rfl) ⟨628280, by rfl⟩ : syracuseStep 837707 = 1256561) B1256561
theorem B837719 : Blo 834351 837719 := bstep (se 1 (by rfl) ⟨628289, by rfl⟩ : syracuseStep 837719 = 1256579) B1256579
theorem B837739 : Blo 834351 837739 := bstep (se 1 (by rfl) ⟨628304, by rfl⟩ : syracuseStep 837739 = 1256609) B1256609
theorem B837751 : Blo 834351 837751 := bstep (se 1 (by rfl) ⟨628313, by rfl⟩ : syracuseStep 837751 = 1256627) B1256627
theorem B837771 : Blo 834351 837771 := bstep (se 1 (by rfl) ⟨628328, by rfl⟩ : syracuseStep 837771 = 1256657) B1256657
theorem B837783 : Blo 834351 837783 := bstep (se 1 (by rfl) ⟨628337, by rfl⟩ : syracuseStep 837783 = 1256675) B1256675
theorem B837803 : Blo 834351 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B2377907 : Blo 834351 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B837815 : Blo 834351 837815 := bstep (se 1 (by rfl) ⟨628361, by rfl⟩ : syracuseStep 837815 = 1256723) B1256723
theorem B837835 : Blo 834351 837835 := bstep (se 1 (by rfl) ⟨628376, by rfl⟩ : syracuseStep 837835 = 1256753) B1256753
theorem B837847 : Blo 834351 837847 := bstep (se 1 (by rfl) ⟨628385, by rfl⟩ : syracuseStep 837847 = 1256771) B1256771
theorem B837867 : Blo 834351 837867 := bstep (se 1 (by rfl) ⟨628400, by rfl⟩ : syracuseStep 837867 = 1256801) B1256801
theorem B837879 : Blo 834351 837879 := bstep (se 1 (by rfl) ⟨628409, by rfl⟩ : syracuseStep 837879 = 1256819) B1256819
theorem B837899 : Blo 834351 837899 := bstep (se 1 (by rfl) ⟨628424, by rfl⟩ : syracuseStep 837899 = 1256849) B1256849
theorem B837911 : Blo 834351 837911 := bstep (se 1 (by rfl) ⟨628433, by rfl⟩ : syracuseStep 837911 = 1256867) B1256867
theorem B837931 : Blo 834351 837931 := bstep (se 1 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 837931 = 1256897) B1256897
theorem B837943 : Blo 834351 837943 := bstep (se 1 (by rfl) ⟨628457, by rfl⟩ : syracuseStep 837943 = 1256915) B1256915
theorem B837963 : Blo 834351 837963 := bstep (se 1 (by rfl) ⟨628472, by rfl⟩ : syracuseStep 837963 = 1256945) B1256945
theorem B837975 : Blo 834351 837975 := bstep (se 1 (by rfl) ⟨628481, by rfl⟩ : syracuseStep 837975 = 1256963) B1256963
theorem B837995 : Blo 834351 837995 := bstep (se 1 (by rfl) ⟨628496, by rfl⟩ : syracuseStep 837995 = 1256993) B1256993
theorem B838007 : Blo 834351 838007 := bstep (se 1 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 838007 = 1257011) B1257011
theorem B838027 : Blo 834351 838027 := bstep (se 1 (by rfl) ⟨628520, by rfl⟩ : syracuseStep 838027 = 1257041) B1257041
theorem B2378135 : Blo 834351 2378135 := bstep (se 1 (by rfl) ⟨1783601, by rfl⟩ : syracuseStep 2378135 = 3567203) B3567203
theorem B838039 : Blo 834351 838039 := bstep (se 1 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 838039 = 1257059) B1257059
theorem B838059 : Blo 834351 838059 := bstep (se 1 (by rfl) ⟨628544, by rfl⟩ : syracuseStep 838059 = 1257089) B1257089
theorem B838071 : Blo 834351 838071 := bstep (se 1 (by rfl) ⟨628553, by rfl⟩ : syracuseStep 838071 = 1257107) B1257107
theorem B838091 : Blo 834351 838091 := bstep (se 1 (by rfl) ⟨628568, by rfl⟩ : syracuseStep 838091 = 1257137) B1257137
theorem B838103 : Blo 834351 838103 := bstep (se 1 (by rfl) ⟨628577, by rfl⟩ : syracuseStep 838103 = 1257155) B1257155
theorem B838123 : Blo 834351 838123 := bstep (se 1 (by rfl) ⟨628592, by rfl⟩ : syracuseStep 838123 = 1257185) B1257185
theorem B838135 : Blo 834351 838135 := bstep (se 1 (by rfl) ⟨628601, by rfl⟩ : syracuseStep 838135 = 1257203) B1257203
theorem B838155 : Blo 834351 838155 := bstep (se 1 (by rfl) ⟨628616, by rfl⟩ : syracuseStep 838155 = 1257233) B1257233
theorem B838167 : Blo 834351 838167 := bstep (se 1 (by rfl) ⟨628625, by rfl⟩ : syracuseStep 838167 = 1257251) B1257251
theorem B838187 : Blo 834351 838187 := bstep (se 1 (by rfl) ⟨628640, by rfl⟩ : syracuseStep 838187 = 1257281) B1257281
theorem B838199 : Blo 834351 838199 := bstep (se 1 (by rfl) ⟨628649, by rfl⟩ : syracuseStep 838199 = 1257299) B1257299
theorem B838219 : Blo 834351 838219 := bstep (se 1 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 838219 = 1257329) B1257329
theorem B838231 : Blo 834351 838231 := bstep (se 1 (by rfl) ⟨628673, by rfl⟩ : syracuseStep 838231 = 1257347) B1257347
theorem B838251 : Blo 834351 838251 := bstep (se 1 (by rfl) ⟨628688, by rfl⟩ : syracuseStep 838251 = 1257377) B1257377
theorem B838263 : Blo 834351 838263 := bstep (se 1 (by rfl) ⟨628697, by rfl⟩ : syracuseStep 838263 = 1257395) B1257395
theorem B838283 : Blo 834351 838283 := bstep (se 1 (by rfl) ⟨628712, by rfl⟩ : syracuseStep 838283 = 1257425) B1257425
theorem B838295 : Blo 834351 838295 := bstep (se 1 (by rfl) ⟨628721, by rfl⟩ : syracuseStep 838295 = 1257443) B1257443
theorem B838315 : Blo 834351 838315 := bstep (se 1 (by rfl) ⟨628736, by rfl⟩ : syracuseStep 838315 = 1257473) B1257473
theorem B838327 : Blo 834351 838327 := bstep (se 1 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 838327 = 1257491) B1257491
theorem B2378443 : Blo 834351 2378443 := bstep (se 1 (by rfl) ⟨1783832, by rfl⟩ : syracuseStep 2378443 = 3567665) B3567665
theorem B838347 : Blo 834351 838347 := bstep (se 1 (by rfl) ⟨628760, by rfl⟩ : syracuseStep 838347 = 1257521) B1257521
theorem B1788659 : Blo 834351 1788659 := bstep (se 1 (by rfl) ⟨1341494, by rfl⟩ : syracuseStep 1788659 = 2682989) B2682989
theorem B1788761 : Blo 834351 1788761 := bstep (se 2 (by rfl) ⟨670785, by rfl⟩ : syracuseStep 1788761 = 1341571) B1341571
theorem B2378717 : Blo 834351 2378717 := bstep (se 3 (by rfl) ⟨446009, by rfl⟩ : syracuseStep 2378717 = 892019) B892019
theorem B2116631 : Blo 834351 2116631 := bstep (se 1 (by rfl) ⟨1587473, by rfl⟩ : syracuseStep 2116631 = 3174947) B3174947
theorem B8244355 : Blo 834351 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B1789121 : Blo 834351 1789121 := bstep (se 2 (by rfl) ⟨670920, by rfl⟩ : syracuseStep 1789121 = 1341841) B1341841
theorem B2117299 : Blo 834351 2117299 := bstep (se 1 (by rfl) ⟨1587974, by rfl⟩ : syracuseStep 2117299 = 3175949) B3175949
theorem B3821357 : Blo 834351 3821357 := bstep (se 3 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 3821357 = 1433009) B1433009
theorem B2117441 : Blo 834351 2117441 := bstep (se 2 (by rfl) ⟨794040, by rfl⟩ : syracuseStep 2117441 = 1588081) B1588081
theorem B2674583 : Blo 834351 2674583 := bstep (se 1 (by rfl) ⟨2005937, by rfl⟩ : syracuseStep 2674583 = 4011875) B4011875
theorem B1789847 : Blo 834351 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B1692211 : Blo 834351 1692211 := bstep (se 1 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 1692211 = 2538317) B2538317
theorem B2904665 : Blo 834351 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B2675351 : Blo 834351 2675351 := bstep (se 1 (by rfl) ⟨2006513, by rfl⟩ : syracuseStep 2675351 = 4013027) B4013027
theorem B938731 : Blo 834351 938731 := bstep (se 1 (by rfl) ⟨704048, by rfl⟩ : syracuseStep 938731 = 1408097) B1408097
theorem B938839 : Blo 834351 938839 := bstep (se 1 (by rfl) ⟨704129, by rfl⟩ : syracuseStep 938839 = 1408259) B1408259
theorem B939019 : Blo 834351 939019 := bstep (se 1 (by rfl) ⟨704264, by rfl⟩ : syracuseStep 939019 = 1408529) B1408529
theorem B2380823 : Blo 834351 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B2118707 : Blo 834351 2118707 := bstep (se 1 (by rfl) ⟨1589030, by rfl⟩ : syracuseStep 2118707 = 3178061) B3178061
theorem B939127 : Blo 834351 939127 := bstep (se 1 (by rfl) ⟨704345, by rfl⟩ : syracuseStep 939127 = 1408691) B1408691
theorem B2675863 : Blo 834351 2675863 := bstep (se 1 (by rfl) ⟨2006897, by rfl⟩ : syracuseStep 2675863 = 4013795) B4013795
theorem B939307 : Blo 834351 939307 := bstep (se 1 (by rfl) ⟨704480, by rfl⟩ : syracuseStep 939307 = 1408961) B1408961
theorem B939415 : Blo 834351 939415 := bstep (se 1 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 939415 = 1409123) B1409123
theorem B5723713 : Blo 834351 5723713 := bstep (se 2 (by rfl) ⟨2146392, by rfl⟩ : syracuseStep 5723713 = 4292785) B4292785
theorem B939595 : Blo 834351 939595 := bstep (se 1 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 939595 = 1409393) B1409393
theorem B2119243 : Blo 834351 2119243 := bstep (se 1 (by rfl) ⟨1589432, by rfl⟩ : syracuseStep 2119243 = 3178865) B3178865
theorem B939703 : Blo 834351 939703 := bstep (se 1 (by rfl) ⟨704777, by rfl⟩ : syracuseStep 939703 = 1409555) B1409555
theorem B2119385 : Blo 834351 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B6051601 : Blo 834351 6051601 := bstep (se 2 (by rfl) ⟨2269350, by rfl⟩ : syracuseStep 6051601 = 4538701) B4538701
theorem B2381633 : Blo 834351 2381633 := bstep (se 2 (by rfl) ⟨893112, by rfl⟩ : syracuseStep 2381633 = 1786225) B1786225
theorem B939883 : Blo 834351 939883 := bstep (se 1 (by rfl) ⟨704912, by rfl⟩ : syracuseStep 939883 = 1409825) B1409825
theorem B3168173 : Blo 834351 3168173 := bstep (se 3 (by rfl) ⟨594032, by rfl⟩ : syracuseStep 3168173 = 1188065) B1188065
theorem B6346673 : Blo 834351 6346673 := bstep (se 2 (by rfl) ⟨2380002, by rfl⟩ : syracuseStep 6346673 = 4760005) B4760005
theorem B2676683 : Blo 834351 2676683 := bstep (se 1 (by rfl) ⟨2007512, by rfl⟩ : syracuseStep 2676683 = 4015025) B4015025
theorem B939991 : Blo 834351 939991 := bstep (se 1 (by rfl) ⟨704993, by rfl⟩ : syracuseStep 939991 = 1409987) B1409987
theorem B940171 : Blo 834351 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B16046261 : Blo 834351 16046261 := bstep (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) B1504337
theorem B3922141 : Blo 834351 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B940279 : Blo 834351 940279 := bstep (se 1 (by rfl) ⟨705209, by rfl⟩ : syracuseStep 940279 = 1410419) B1410419
theorem B1693963 : Blo 834351 1693963 := bstep (se 1 (by rfl) ⟨1270472, by rfl⟩ : syracuseStep 1693963 = 2540945) B2540945
theorem B3528983 : Blo 834351 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B2677043 : Blo 834351 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1694027 : Blo 834351 1694027 := bstep (se 1 (by rfl) ⟨1270520, by rfl⟩ : syracuseStep 1694027 = 2541041) B2541041
theorem B6347159 : Blo 834351 6347159 := bstep (se 1 (by rfl) ⟨4760369, by rfl⟩ : syracuseStep 6347159 = 9520739) B9520739
theorem B940459 : Blo 834351 940459 := bstep (se 1 (by rfl) ⟨705344, by rfl⟩ : syracuseStep 940459 = 1410689) B1410689
theorem B940567 : Blo 834351 940567 := bstep (se 1 (by rfl) ⟨705425, by rfl⟩ : syracuseStep 940567 = 1410851) B1410851
theorem B2120215 : Blo 834351 2120215 := bstep (se 1 (by rfl) ⟨1590161, by rfl⟩ : syracuseStep 2120215 = 3180323) B3180323
theorem B940747 : Blo 834351 940747 := bstep (se 1 (by rfl) ⟨705560, by rfl⟩ : syracuseStep 940747 = 1411121) B1411121
theorem B940855 : Blo 834351 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B2710451 : Blo 834351 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B2120651 : Blo 834351 2120651 := bstep (se 1 (by rfl) ⟨1590488, by rfl⟩ : syracuseStep 2120651 = 3180977) B3180977
theorem B941035 : Blo 834351 941035 := bstep (se 1 (by rfl) ⟨705776, by rfl⟩ : syracuseStep 941035 = 1411553) B1411553
theorem B941143 : Blo 834351 941143 := bstep (se 1 (by rfl) ⟨705857, by rfl⟩ : syracuseStep 941143 = 1411715) B1411715
theorem B5364953 : Blo 834351 5364953 := bstep (se 2 (by rfl) ⟨2011857, by rfl⟩ : syracuseStep 5364953 = 4023715) B4023715
theorem B941323 : Blo 834351 941323 := bstep (se 1 (by rfl) ⟨705992, by rfl⟩ : syracuseStep 941323 = 1411985) B1411985
theorem B3169601 : Blo 834351 3169601 := bstep (se 2 (by rfl) ⟨1188600, by rfl⟩ : syracuseStep 3169601 = 2377201) B2377201
theorem B2121025 : Blo 834351 2121025 := bstep (se 2 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 2121025 = 1590769) B1590769
theorem B941431 : Blo 834351 941431 := bstep (se 1 (by rfl) ⟨706073, by rfl⟩ : syracuseStep 941431 = 1412147) B1412147
theorem B2383283 : Blo 834351 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B2383307 : Blo 834351 2383307 := bstep (se 1 (by rfl) ⟨1787480, by rfl⟩ : syracuseStep 2383307 = 3574961) B3574961
theorem B941611 : Blo 834351 941611 := bstep (se 1 (by rfl) ⟨706208, by rfl⟩ : syracuseStep 941611 = 1412417) B1412417
theorem B941719 : Blo 834351 941719 := bstep (se 1 (by rfl) ⟨706289, by rfl⟩ : syracuseStep 941719 = 1412579) B1412579
theorem B941899 : Blo 834351 941899 := bstep (se 1 (by rfl) ⟨706424, by rfl⟩ : syracuseStep 941899 = 1412849) B1412849
theorem B2121623 : Blo 834351 2121623 := bstep (se 1 (by rfl) ⟨1591217, by rfl⟩ : syracuseStep 2121623 = 3182435) B3182435
theorem B942007 : Blo 834351 942007 := bstep (se 1 (by rfl) ⟨706505, by rfl⟩ : syracuseStep 942007 = 1413011) B1413011
theorem B942187 : Blo 834351 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B942295 : Blo 834351 942295 := bstep (se 1 (by rfl) ⟨706721, by rfl⟩ : syracuseStep 942295 = 1413443) B1413443
theorem B2384093 : Blo 834351 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B942475 : Blo 834351 942475 := bstep (se 1 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 942475 = 1413713) B1413713
theorem B942583 : Blo 834351 942583 := bstep (se 1 (by rfl) ⟨706937, by rfl⟩ : syracuseStep 942583 = 1413875) B1413875
theorem B942763 : Blo 834351 942763 := bstep (se 1 (by rfl) ⟨707072, by rfl⟩ : syracuseStep 942763 = 1414145) B1414145
theorem B1205003 : Blo 834351 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B3171089 : Blo 834351 3171089 := bstep (se 2 (by rfl) ⟨1189158, by rfl⟩ : syracuseStep 3171089 = 2378317) B2378317
theorem B942871 : Blo 834351 942871 := bstep (se 1 (by rfl) ⟨707153, by rfl⟩ : syracuseStep 942871 = 1414307) B1414307
theorem B7136045 : Blo 834351 7136045 := bstep (se 3 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 7136045 = 2676017) B2676017
theorem B943051 : Blo 834351 943051 := bstep (se 1 (by rfl) ⟨707288, by rfl⟩ : syracuseStep 943051 = 1414577) B1414577
theorem B45737141 : Blo 834351 45737141 := bstep (se 5 (by rfl) ⟨2143928, by rfl⟩ : syracuseStep 45737141 = 4287857) B4287857
theorem B36201653 : Blo 834351 36201653 := bstep (se 5 (by rfl) ⟨1696952, by rfl⟩ : syracuseStep 36201653 = 3393905) B3393905
theorem B3171545 : Blo 834351 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B3564931 : Blo 834351 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B3171757 : Blo 834351 3171757 := bstep (se 3 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 3171757 = 1189409) B1189409
theorem B1336907 : Blo 834351 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B3172061 : Blo 834351 3172061 := bstep (se 3 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 3172061 = 1189523) B1189523
theorem B8021825 : Blo 834351 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B5367617 : Blo 834351 5367617 := bstep (se 2 (by rfl) ⟨2012856, by rfl⟩ : syracuseStep 5367617 = 4025713) B4025713
theorem B3565529 : Blo 834351 3565529 := bstep (se 2 (by rfl) ⟨1337073, by rfl⟩ : syracuseStep 3565529 = 2674147) B2674147
theorem B2385881 : Blo 834351 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B1337419 : Blo 834351 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B2615513 : Blo 834351 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B5728529 : Blo 834351 5728529 := bstep (se 2 (by rfl) ⟨2148198, by rfl⟩ : syracuseStep 5728529 = 4296397) B4296397
theorem B2386199 : Blo 834351 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B3565889 : Blo 834351 3565889 := bstep (se 2 (by rfl) ⟨1337208, by rfl⟩ : syracuseStep 3565889 = 2674417) B2674417
theorem B1698251 : Blo 834351 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B3860995 : Blo 834351 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B1338137 : Blo 834351 1338137 := bstep (se 2 (by rfl) ⟨501801, by rfl⟩ : syracuseStep 1338137 = 1003603) B1003603
theorem B17165155 : Blo 834351 17165155 := bstep (se 1 (by rfl) ⟨12873866, by rfl⟩ : syracuseStep 17165155 = 25747733) B25747733
theorem B2387009 : Blo 834351 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B3009757 : Blo 834351 3009757 := bstep (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) B1128659
theorem B1338649 : Blo 834351 1338649 := bstep (se 2 (by rfl) ⟨501993, by rfl⟩ : syracuseStep 1338649 = 1003987) B1003987
theorem B2256203 : Blo 834351 2256203 := bstep (se 1 (by rfl) ⟨1692152, by rfl⟩ : syracuseStep 2256203 = 3384305) B3384305
theorem B4025675 : Blo 834351 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B6025367 : Blo 834351 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B3174659 : Blo 834351 3174659 := bstep (se 1 (by rfl) ⟨2380994, by rfl⟩ : syracuseStep 3174659 = 4761989) B4761989
theorem B3174673 : Blo 834351 3174673 := bstep (se 2 (by rfl) ⟨1190502, by rfl⟩ : syracuseStep 3174673 = 2381005) B2381005
theorem B7139735 : Blo 834351 7139735 := bstep (se 1 (by rfl) ⟨5354801, by rfl⟩ : syracuseStep 7139735 = 10709603) B10709603
theorem B848279 : Blo 834351 848279 := bstep (se 1 (by rfl) ⟨636209, by rfl⟩ : syracuseStep 848279 = 1272419) B1272419
theorem B1929793 : Blo 834351 1929793 := bstep (se 2 (by rfl) ⟨723672, by rfl⟩ : syracuseStep 1929793 = 1447345) B1447345
theorem B3174977 : Blo 834351 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B14316101 : Blo 834351 14316101 := bstep (se 4 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 14316101 = 2684269) B2684269
theorem B4518787 : Blo 834351 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B848875 : Blo 834351 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B9172099 : Blo 834351 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B3175645 : Blo 834351 3175645 := bstep (se 3 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 3175645 = 1190867) B1190867
theorem B5371181 : Blo 834351 5371181 := bstep (se 3 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 5371181 = 2014193) B2014193
theorem B4224473 : Blo 834351 4224473 := bstep (se 2 (by rfl) ⟨1584177, by rfl⟩ : syracuseStep 4224473 = 3168355) B3168355
theorem B6354449 : Blo 834351 6354449 := bstep (se 2 (by rfl) ⟨2382918, by rfl⟩ : syracuseStep 6354449 = 4765837) B4765837
theorem B5371409 : Blo 834351 5371409 := bstep (se 2 (by rfl) ⟨2014278, by rfl⟩ : syracuseStep 5371409 = 4028557) B4028557
theorem B849547 : Blo 834351 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B6616849 : Blo 834351 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B2815937 : Blo 834351 2815937 := bstep (se 2 (by rfl) ⟨1055976, by rfl⟩ : syracuseStep 2815937 = 2111953) B2111953
theorem B3569629 : Blo 834351 3569629 := bstep (se 3 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 3569629 = 1338611) B1338611
theorem B1341463 : Blo 834351 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B3012653 : Blo 834351 3012653 := bstep (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) B1129745
theorem B10713293 : Blo 834351 10713293 := bstep (se 3 (by rfl) ⟨2008742, by rfl⟩ : syracuseStep 10713293 = 4017485) B4017485
theorem B9173197 : Blo 834351 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B48953621 : Blo 834351 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B10877285 : Blo 834351 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B3176921 : Blo 834351 3176921 := bstep (se 2 (by rfl) ⟨1191345, by rfl⟩ : syracuseStep 3176921 = 2382691) B2382691
theorem B2816477 : Blo 834351 2816477 := bstep (se 3 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 2816477 = 1056179) B1056179
theorem B1505881 : Blo 834351 1505881 := bstep (se 2 (by rfl) ⟨564705, by rfl⟩ : syracuseStep 1505881 = 1129411) B1129411
theorem B981623 : Blo 834351 981623 := bstep (se 1 (by rfl) ⟨736217, by rfl⟩ : syracuseStep 981623 = 1472435) B1472435
theorem B10156805 : Blo 834351 10156805 := bstep (se 4 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 10156805 = 1904401) B1904401
theorem B4226093 : Blo 834351 4226093 := bstep (se 3 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 4226093 = 1584785) B1584785
theorem B1408151 : Blo 834351 1408151 := bstep (se 1 (by rfl) ⟨1056113, by rfl⟩ : syracuseStep 1408151 = 2112227) B2112227
theorem B3570961 : Blo 834351 3570961 := bstep (se 2 (by rfl) ⟨1339110, by rfl⟩ : syracuseStep 3570961 = 2678221) B2678221
theorem B1408279 : Blo 834351 1408279 := bstep (se 1 (by rfl) ⟨1056209, by rfl⟩ : syracuseStep 1408279 = 2112419) B2112419
theorem B2817611 : Blo 834351 2817611 := bstep (se 1 (by rfl) ⟨2113208, by rfl⟩ : syracuseStep 2817611 = 4226417) B4226417
theorem B2817881 : Blo 834351 2817881 := bstep (se 2 (by rfl) ⟨1056705, by rfl⟩ : syracuseStep 2817881 = 2113411) B2113411
theorem B9633653 : Blo 834351 9633653 := bstep (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) B903155
theorem B1408907 : Blo 834351 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B18087857 : Blo 834351 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B1507265 : Blo 834351 1507265 := bstep (se 2 (by rfl) ⟨565224, by rfl⟩ : syracuseStep 1507265 = 1130449) B1130449
theorem B3014603 : Blo 834351 3014603 := bstep (se 1 (by rfl) ⟨2260952, by rfl⟩ : syracuseStep 3014603 = 4521905) B4521905
theorem B1409143 : Blo 834351 1409143 := bstep (se 1 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 1409143 = 2113715) B2113715
theorem B1409339 : Blo 834351 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B2261591 : Blo 834351 2261591 := bstep (se 1 (by rfl) ⟨1696193, by rfl⟩ : syracuseStep 2261591 = 3392387) B3392387
theorem B1409737 : Blo 834351 1409737 := bstep (se 2 (by rfl) ⟨528651, by rfl⟩ : syracuseStep 1409737 = 1057303) B1057303
theorem B14451571 : Blo 834351 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B2262077 : Blo 834351 2262077 := bstep (se 3 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 2262077 = 848279) B848279
theorem B3015767 : Blo 834351 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B1410439 : Blo 834351 1410439 := bstep (se 1 (by rfl) ⟨1057829, by rfl⟩ : syracuseStep 1410439 = 2115659) B2115659
theorem B34407953 : Blo 834351 34407953 := bstep (se 2 (by rfl) ⟨12902982, by rfl⟩ : syracuseStep 34407953 = 25805965) B25805965
theorem B9045569 : Blo 834351 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B4294345 : Blo 834351 4294345 := bstep (se 2 (by rfl) ⟨1610379, by rfl⟩ : syracuseStep 4294345 = 3220759) B3220759
theorem B4753241 : Blo 834351 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B4229009 : Blo 834351 4229009 := bstep (se 2 (by rfl) ⟨1585878, by rfl⟩ : syracuseStep 4229009 = 3171757) B3171757
theorem B2819987 : Blo 834351 2819987 := bstep (se 1 (by rfl) ⟨2114990, by rfl⟩ : syracuseStep 2819987 = 4229981) B4229981
theorem B1411087 : Blo 834351 1411087 := bstep (se 1 (by rfl) ⟨1058315, by rfl⟩ : syracuseStep 1411087 = 2116631) B2116631
theorem B3213341 : Blo 834351 3213341 := bstep (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) B1205003
theorem B9767303 : Blo 834351 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B4819409 : Blo 834351 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B12061169 : Blo 834351 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B1411627 : Blo 834351 1411627 := bstep (se 1 (by rfl) ⟨1058720, by rfl⟩ : syracuseStep 1411627 = 2117441) B2117441
theorem B1411769 : Blo 834351 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B121965709 : Blo 834351 121965709 := bstep (se 3 (by rfl) ⟨22868570, by rfl⟩ : syracuseStep 121965709 = 45737141) B45737141
theorem B2821391 : Blo 834351 2821391 := bstep (se 1 (by rfl) ⟨2116043, by rfl⟩ : syracuseStep 2821391 = 4232087) B4232087
theorem B5147993 : Blo 834351 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B1412471 : Blo 834351 1412471 := bstep (se 1 (by rfl) ⟨1059353, by rfl⟩ : syracuseStep 1412471 = 2118707) B2118707
theorem B2821661 : Blo 834351 2821661 := bstep (se 3 (by rfl) ⟨529061, by rfl⟩ : syracuseStep 2821661 = 1058123) B1058123
theorem B1412923 : Blo 834351 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B1413065 : Blo 834351 1413065 := bstep (se 2 (by rfl) ⟨529899, by rfl⟩ : syracuseStep 1413065 = 1059799) B1059799
theorem B4231115 : Blo 834351 4231115 := bstep (se 1 (by rfl) ⟨3173336, by rfl⟩ : syracuseStep 4231115 = 6346673) B6346673
theorem B4231439 : Blo 834351 4231439 := bstep (se 1 (by rfl) ⟨3173579, by rfl⟩ : syracuseStep 4231439 = 6347159) B6347159
theorem B2036267 : Blo 834351 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B1806967 : Blo 834351 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B1413767 : Blo 834351 1413767 := bstep (se 1 (by rfl) ⟨1060325, by rfl⟩ : syracuseStep 1413767 = 2120651) B2120651
theorem B3576635 : Blo 834351 3576635 := bstep (se 1 (by rfl) ⟨2682476, by rfl⟩ : syracuseStep 3576635 = 5364953) B5364953
theorem B2823065 : Blo 834351 2823065 := bstep (se 2 (by rfl) ⟨1058649, by rfl⟩ : syracuseStep 2823065 = 2117299) B2117299
theorem B1414415 : Blo 834351 1414415 := bstep (se 1 (by rfl) ⟨1060811, by rfl⟩ : syracuseStep 1414415 = 2121623) B2121623
theorem B17143073 : Blo 834351 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B6034823 : Blo 834351 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B3020179 : Blo 834351 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B8033741 : Blo 834351 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B2823767 : Blo 834351 2823767 := bstep (se 1 (by rfl) ⟨2117825, by rfl⟩ : syracuseStep 2823767 = 4235651) B4235651
theorem B4232897 : Blo 834351 4232897 := bstep (se 2 (by rfl) ⟨1587336, by rfl⟩ : syracuseStep 4232897 = 3174673) B3174673
theorem B4757363 : Blo 834351 4757363 := bstep (se 1 (by rfl) ⟨3568022, by rfl⟩ : syracuseStep 4757363 = 7136045) B7136045
theorem B15276077 : Blo 834351 15276077 := bstep (se 3 (by rfl) ⟨2864264, by rfl⟩ : syracuseStep 15276077 = 5728529) B5728529
theorem B2824253 : Blo 834351 2824253 := bstep (se 3 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 2824253 = 1059095) B1059095
theorem B6363197 : Blo 834351 6363197 := bstep (se 3 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 6363197 = 2386199) B2386199
theorem B1251575 : Blo 834351 1251575 := bstep (se 1 (by rfl) ⟨938681, by rfl⟩ : syracuseStep 1251575 = 1877363) B1877363
theorem B29006093 : Blo 834351 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B1251599 : Blo 834351 1251599 := bstep (se 1 (by rfl) ⟨938699, by rfl⟩ : syracuseStep 1251599 = 1877399) B1877399
theorem B1251641 : Blo 834351 1251641 := bstep (se 2 (by rfl) ⟨469365, by rfl⟩ : syracuseStep 1251641 = 938731) B938731
theorem B1251719 : Blo 834351 1251719 := bstep (se 1 (by rfl) ⟨938789, by rfl⟩ : syracuseStep 1251719 = 1877579) B1877579
theorem B891271 : Blo 834351 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B2857369 : Blo 834351 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B1251755 : Blo 834351 1251755 := bstep (se 1 (by rfl) ⟨938816, by rfl⟩ : syracuseStep 1251755 = 1877633) B1877633
theorem B1251785 : Blo 834351 1251785 := bstep (se 2 (by rfl) ⟨469419, by rfl⟩ : syracuseStep 1251785 = 938839) B938839
theorem B4528669 : Blo 834351 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B5347883 : Blo 834351 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B3578411 : Blo 834351 3578411 := bstep (se 1 (by rfl) ⟨2683808, by rfl⟩ : syracuseStep 3578411 = 5367617) B5367617
theorem B1251899 : Blo 834351 1251899 := bstep (se 1 (by rfl) ⟨938924, by rfl⟩ : syracuseStep 1251899 = 1877849) B1877849
theorem B1251959 : Blo 834351 1251959 := bstep (se 1 (by rfl) ⟨938969, by rfl⟩ : syracuseStep 1251959 = 1877939) B1877939
theorem B1251983 : Blo 834351 1251983 := bstep (se 1 (by rfl) ⟨938987, by rfl⟩ : syracuseStep 1251983 = 1877975) B1877975
theorem B1252025 : Blo 834351 1252025 := bstep (se 2 (by rfl) ⟨469509, by rfl⟩ : syracuseStep 1252025 = 939019) B939019
theorem B1252103 : Blo 834351 1252103 := bstep (se 1 (by rfl) ⟨939077, by rfl⟩ : syracuseStep 1252103 = 1878155) B1878155
theorem B1252139 : Blo 834351 1252139 := bstep (se 1 (by rfl) ⟨939104, by rfl⟩ : syracuseStep 1252139 = 1878209) B1878209
theorem B1252169 : Blo 834351 1252169 := bstep (se 2 (by rfl) ⟨469563, by rfl⟩ : syracuseStep 1252169 = 939127) B939127
theorem B12229465 : Blo 834351 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B1252283 : Blo 834351 1252283 := bstep (se 1 (by rfl) ⟨939212, by rfl⟩ : syracuseStep 1252283 = 1878425) B1878425
theorem B4234193 : Blo 834351 4234193 := bstep (se 2 (by rfl) ⟨1587822, by rfl⟩ : syracuseStep 4234193 = 3175645) B3175645
theorem B1252343 : Blo 834351 1252343 := bstep (se 1 (by rfl) ⟨939257, by rfl⟩ : syracuseStep 1252343 = 1878515) B1878515
theorem B1252367 : Blo 834351 1252367 := bstep (se 1 (by rfl) ⟨939275, by rfl⟩ : syracuseStep 1252367 = 1878551) B1878551
theorem B1252409 : Blo 834351 1252409 := bstep (se 2 (by rfl) ⟨469653, by rfl⟩ : syracuseStep 1252409 = 939307) B939307
theorem B1252487 : Blo 834351 1252487 := bstep (se 1 (by rfl) ⟨939365, by rfl⟩ : syracuseStep 1252487 = 1878731) B1878731
theorem B1252523 : Blo 834351 1252523 := bstep (se 1 (by rfl) ⟨939392, by rfl⟩ : syracuseStep 1252523 = 1878785) B1878785
theorem B892091 : Blo 834351 892091 := bstep (se 1 (by rfl) ⟨669068, by rfl⟩ : syracuseStep 892091 = 1338137) B1338137
theorem B1252553 : Blo 834351 1252553 := bstep (se 2 (by rfl) ⟨469707, by rfl⟩ : syracuseStep 1252553 = 939415) B939415
theorem B1056007 : Blo 834351 1056007 := bstep (se 1 (by rfl) ⟨792005, by rfl⟩ : syracuseStep 1056007 = 1584011) B1584011
theorem B4758821 : Blo 834351 4758821 := bstep (se 4 (by rfl) ⟨446139, by rfl⟩ : syracuseStep 4758821 = 892279) B892279
theorem B1252667 : Blo 834351 1252667 := bstep (se 1 (by rfl) ⟨939500, by rfl⟩ : syracuseStep 1252667 = 1879001) B1879001
theorem B1252727 : Blo 834351 1252727 := bstep (se 1 (by rfl) ⟨939545, by rfl⟩ : syracuseStep 1252727 = 1879091) B1879091
theorem B1252751 : Blo 834351 1252751 := bstep (se 1 (by rfl) ⟨939563, by rfl⟩ : syracuseStep 1252751 = 1879127) B1879127
theorem B2825657 : Blo 834351 2825657 := bstep (se 2 (by rfl) ⟨1059621, by rfl⟩ : syracuseStep 2825657 = 2119243) B2119243
theorem B1252793 : Blo 834351 1252793 := bstep (se 2 (by rfl) ⟨469797, by rfl⟩ : syracuseStep 1252793 = 939595) B939595
theorem B1252871 : Blo 834351 1252871 := bstep (se 1 (by rfl) ⟨939653, by rfl⟩ : syracuseStep 1252871 = 1879307) B1879307
theorem B1252907 : Blo 834351 1252907 := bstep (se 1 (by rfl) ⟨939680, by rfl⟩ : syracuseStep 1252907 = 1879361) B1879361
theorem B1252937 : Blo 834351 1252937 := bstep (se 2 (by rfl) ⟨469851, by rfl⟩ : syracuseStep 1252937 = 939703) B939703
theorem B1253051 : Blo 834351 1253051 := bstep (se 1 (by rfl) ⟨939788, by rfl⟩ : syracuseStep 1253051 = 1879577) B1879577
theorem B8822465 : Blo 834351 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1056503 : Blo 834351 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B1253111 : Blo 834351 1253111 := bstep (se 1 (by rfl) ⟨939833, by rfl⟩ : syracuseStep 1253111 = 1879667) B1879667
theorem B1253135 : Blo 834351 1253135 := bstep (se 1 (by rfl) ⟨939851, by rfl⟩ : syracuseStep 1253135 = 1879703) B1879703
theorem B1253177 : Blo 834351 1253177 := bstep (se 2 (by rfl) ⟨469941, by rfl⟩ : syracuseStep 1253177 = 939883) B939883
theorem B1253255 : Blo 834351 1253255 := bstep (se 1 (by rfl) ⟨939941, by rfl⟩ : syracuseStep 1253255 = 1879883) B1879883
theorem B1056655 : Blo 834351 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B1253291 : Blo 834351 1253291 := bstep (se 1 (by rfl) ⟨939968, by rfl⟩ : syracuseStep 1253291 = 1879937) B1879937
theorem B1253321 : Blo 834351 1253321 := bstep (se 2 (by rfl) ⟨469995, by rfl⟩ : syracuseStep 1253321 = 939991) B939991
theorem B4759505 : Blo 834351 4759505 := bstep (se 2 (by rfl) ⟨1784814, by rfl⟩ : syracuseStep 4759505 = 3569629) B3569629
theorem B2826251 : Blo 834351 2826251 := bstep (se 1 (by rfl) ⟨2119688, by rfl⟩ : syracuseStep 2826251 = 4239377) B4239377
theorem B1056827 : Blo 834351 1056827 := bstep (se 1 (by rfl) ⟨792620, by rfl⟩ : syracuseStep 1056827 = 1585241) B1585241
theorem B1253435 : Blo 834351 1253435 := bstep (se 1 (by rfl) ⟨940076, by rfl⟩ : syracuseStep 1253435 = 1880153) B1880153
theorem B1253495 : Blo 834351 1253495 := bstep (se 1 (by rfl) ⟨940121, by rfl⟩ : syracuseStep 1253495 = 1880243) B1880243
theorem B2826359 : Blo 834351 2826359 := bstep (se 1 (by rfl) ⟨2119769, by rfl⟩ : syracuseStep 2826359 = 4239539) B4239539
theorem B1253519 : Blo 834351 1253519 := bstep (se 1 (by rfl) ⟨940139, by rfl⟩ : syracuseStep 1253519 = 1880279) B1880279
theorem B1253561 : Blo 834351 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B1253639 : Blo 834351 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B4759823 : Blo 834351 4759823 := bstep (se 1 (by rfl) ⟨3569867, by rfl⟩ : syracuseStep 4759823 = 7139735) B7139735
theorem B12230929 : Blo 834351 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1253675 : Blo 834351 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B1253705 : Blo 834351 1253705 := bstep (se 2 (by rfl) ⟨470139, by rfl⟩ : syracuseStep 1253705 = 940279) B940279
theorem B1909111 : Blo 834351 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B9544067 : Blo 834351 9544067 := bstep (se 1 (by rfl) ⟨7158050, by rfl⟩ : syracuseStep 9544067 = 14316101) B14316101
theorem B1253819 : Blo 834351 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B16097777 : Blo 834351 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B1253879 : Blo 834351 1253879 := bstep (se 1 (by rfl) ⟨940409, by rfl⟩ : syracuseStep 1253879 = 1880819) B1880819
theorem B1253903 : Blo 834351 1253903 := bstep (se 1 (by rfl) ⟨940427, by rfl⟩ : syracuseStep 1253903 = 1880855) B1880855
theorem B1253945 : Blo 834351 1253945 := bstep (se 2 (by rfl) ⟨470229, by rfl⟩ : syracuseStep 1253945 = 940459) B940459
theorem B1254023 : Blo 834351 1254023 := bstep (se 1 (by rfl) ⟨940517, by rfl⟩ : syracuseStep 1254023 = 1881035) B1881035
theorem B1254059 : Blo 834351 1254059 := bstep (se 1 (by rfl) ⟨940544, by rfl⟩ : syracuseStep 1254059 = 1881089) B1881089
theorem B30483125 : Blo 834351 30483125 := bstep (se 5 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 30483125 = 2857793) B2857793
theorem B1254089 : Blo 834351 1254089 := bstep (se 2 (by rfl) ⟨470283, by rfl⟩ : syracuseStep 1254089 = 940567) B940567
theorem B2826953 : Blo 834351 2826953 := bstep (se 2 (by rfl) ⟨1060107, by rfl⟩ : syracuseStep 2826953 = 2120215) B2120215
theorem B4530917 : Blo 834351 4530917 := bstep (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) B849547
theorem B2007841 : Blo 834351 2007841 := bstep (se 2 (by rfl) ⟨752940, by rfl⟩ : syracuseStep 2007841 = 1505881) B1505881
theorem B1254203 : Blo 834351 1254203 := bstep (se 1 (by rfl) ⟨940652, by rfl⟩ : syracuseStep 1254203 = 1881305) B1881305
theorem B3580787 : Blo 834351 3580787 := bstep (se 1 (by rfl) ⟨2685590, by rfl⟩ : syracuseStep 3580787 = 5371181) B5371181
theorem B1254263 : Blo 834351 1254263 := bstep (se 1 (by rfl) ⟨940697, by rfl⟩ : syracuseStep 1254263 = 1881395) B1881395
theorem B1254287 : Blo 834351 1254287 := bstep (se 1 (by rfl) ⟨940715, by rfl⟩ : syracuseStep 1254287 = 1881431) B1881431
theorem B1254329 : Blo 834351 1254329 := bstep (se 2 (by rfl) ⟨470373, by rfl⟩ : syracuseStep 1254329 = 940747) B940747
theorem B1057799 : Blo 834351 1057799 := bstep (se 1 (by rfl) ⟨793349, by rfl⟩ : syracuseStep 1057799 = 1586699) B1586699
theorem B1254407 : Blo 834351 1254407 := bstep (se 1 (by rfl) ⟨940805, by rfl⟩ : syracuseStep 1254407 = 1881611) B1881611
theorem B4236299 : Blo 834351 4236299 := bstep (se 1 (by rfl) ⟨3177224, by rfl⟩ : syracuseStep 4236299 = 6354449) B6354449
theorem B3580939 : Blo 834351 3580939 := bstep (se 1 (by rfl) ⟨2685704, by rfl⟩ : syracuseStep 3580939 = 5371409) B5371409
theorem B1254443 : Blo 834351 1254443 := bstep (se 1 (by rfl) ⟨940832, by rfl⟩ : syracuseStep 1254443 = 1881665) B1881665
theorem B1254473 : Blo 834351 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B4236461 : Blo 834351 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B1254587 : Blo 834351 1254587 := bstep (se 1 (by rfl) ⟨940940, by rfl⟩ : syracuseStep 1254587 = 1881881) B1881881
theorem B25732333 : Blo 834351 25732333 := bstep (se 3 (by rfl) ⟨4824812, by rfl⟩ : syracuseStep 25732333 = 9649625) B9649625
theorem B1254647 : Blo 834351 1254647 := bstep (se 1 (by rfl) ⟨940985, by rfl⟩ : syracuseStep 1254647 = 1881971) B1881971
theorem B1254671 : Blo 834351 1254671 := bstep (se 1 (by rfl) ⟨941003, by rfl⟩ : syracuseStep 1254671 = 1882007) B1882007
theorem B1877291 : Blo 834351 1877291 := bstep (se 1 (by rfl) ⟨1407968, by rfl⟩ : syracuseStep 1877291 = 2815937) B2815937
theorem B1254713 : Blo 834351 1254713 := bstep (se 2 (by rfl) ⟨470517, by rfl⟩ : syracuseStep 1254713 = 941035) B941035
theorem B19342651 : Blo 834351 19342651 := bstep (se 1 (by rfl) ⟨14506988, by rfl⟩ : syracuseStep 19342651 = 29013977) B29013977
theorem B1254791 : Blo 834351 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B2827655 : Blo 834351 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B1254827 : Blo 834351 1254827 := bstep (se 1 (by rfl) ⟨941120, by rfl⟩ : syracuseStep 1254827 = 1882241) B1882241
theorem B1254857 : Blo 834351 1254857 := bstep (se 2 (by rfl) ⟨470571, by rfl⟩ : syracuseStep 1254857 = 941143) B941143
theorem B1254971 : Blo 834351 1254971 := bstep (se 1 (by rfl) ⟨941228, by rfl⟩ : syracuseStep 1254971 = 1882457) B1882457
theorem B1189495 : Blo 834351 1189495 := bstep (se 1 (by rfl) ⟨892121, by rfl⟩ : syracuseStep 1189495 = 1784243) B1784243
theorem B1255031 : Blo 834351 1255031 := bstep (se 1 (by rfl) ⟨941273, by rfl⟩ : syracuseStep 1255031 = 1882547) B1882547
theorem B1058447 : Blo 834351 1058447 := bstep (se 1 (by rfl) ⟨793835, by rfl⟩ : syracuseStep 1058447 = 1587671) B1587671
theorem B1255055 : Blo 834351 1255055 := bstep (se 1 (by rfl) ⟨941291, by rfl⟩ : syracuseStep 1255055 = 1882583) B1882583
theorem B1877651 : Blo 834351 1877651 := bstep (se 1 (by rfl) ⟨1408238, by rfl⟩ : syracuseStep 1877651 = 2816477) B2816477
theorem B9053873 : Blo 834351 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B1255097 : Blo 834351 1255097 := bstep (se 2 (by rfl) ⟨470661, by rfl⟩ : syracuseStep 1255097 = 941323) B941323
theorem B4761281 : Blo 834351 4761281 := bstep (se 2 (by rfl) ⟨1785480, by rfl⟩ : syracuseStep 4761281 = 3570961) B3570961
theorem B1877705 : Blo 834351 1877705 := bstep (se 2 (by rfl) ⟨704139, by rfl⟩ : syracuseStep 1877705 = 1408279) B1408279
theorem B2828033 : Blo 834351 2828033 := bstep (se 2 (by rfl) ⟨1060512, by rfl⟩ : syracuseStep 2828033 = 2121025) B2121025
theorem B1255175 : Blo 834351 1255175 := bstep (se 1 (by rfl) ⟨941381, by rfl⟩ : syracuseStep 1255175 = 1882763) B1882763
theorem B1255211 : Blo 834351 1255211 := bstep (se 1 (by rfl) ⟨941408, by rfl⟩ : syracuseStep 1255211 = 1882817) B1882817
theorem B1255241 : Blo 834351 1255241 := bstep (se 2 (by rfl) ⟨470715, by rfl⟩ : syracuseStep 1255241 = 941431) B941431
theorem B1189819 : Blo 834351 1189819 := bstep (se 1 (by rfl) ⟨892364, by rfl⟩ : syracuseStep 1189819 = 1784729) B1784729
theorem B1255355 : Blo 834351 1255355 := bstep (se 1 (by rfl) ⟨941516, by rfl⟩ : syracuseStep 1255355 = 1883033) B1883033
theorem B1255415 : Blo 834351 1255415 := bstep (se 1 (by rfl) ⟨941561, by rfl⟩ : syracuseStep 1255415 = 1883123) B1883123
theorem B1255439 : Blo 834351 1255439 := bstep (se 1 (by rfl) ⟨941579, by rfl⟩ : syracuseStep 1255439 = 1883159) B1883159
theorem B1255481 : Blo 834351 1255481 := bstep (se 2 (by rfl) ⟨470805, by rfl⟩ : syracuseStep 1255481 = 941611) B941611
theorem B1255559 : Blo 834351 1255559 := bstep (se 1 (by rfl) ⟨941669, by rfl⟩ : syracuseStep 1255559 = 1883339) B1883339
theorem B1255595 : Blo 834351 1255595 := bstep (se 1 (by rfl) ⟨941696, by rfl⟩ : syracuseStep 1255595 = 1883393) B1883393
theorem B1255625 : Blo 834351 1255625 := bstep (se 2 (by rfl) ⟨470859, by rfl⟩ : syracuseStep 1255625 = 941719) B941719
theorem B1255739 : Blo 834351 1255739 := bstep (se 1 (by rfl) ⟨941804, by rfl⟩ : syracuseStep 1255739 = 1883609) B1883609
theorem B1255799 : Blo 834351 1255799 := bstep (se 1 (by rfl) ⟨941849, by rfl⟩ : syracuseStep 1255799 = 1883699) B1883699
theorem B1878407 : Blo 834351 1878407 := bstep (se 1 (by rfl) ⟨1408805, by rfl⟩ : syracuseStep 1878407 = 2817611) B2817611
theorem B1255823 : Blo 834351 1255823 := bstep (se 1 (by rfl) ⟨941867, by rfl⟩ : syracuseStep 1255823 = 1883735) B1883735
theorem B1190315 : Blo 834351 1190315 := bstep (se 1 (by rfl) ⟨892736, by rfl⟩ : syracuseStep 1190315 = 1785473) B1785473
theorem B1255865 : Blo 834351 1255865 := bstep (se 2 (by rfl) ⟨470949, by rfl⟩ : syracuseStep 1255865 = 941899) B941899
theorem B1255943 : Blo 834351 1255943 := bstep (se 1 (by rfl) ⟨941957, by rfl⟩ : syracuseStep 1255943 = 1883915) B1883915
theorem B1255979 : Blo 834351 1255979 := bstep (se 1 (by rfl) ⟨941984, by rfl⟩ : syracuseStep 1255979 = 1883969) B1883969
theorem B2828843 : Blo 834351 2828843 := bstep (se 1 (by rfl) ⟨2121632, by rfl⟩ : syracuseStep 2828843 = 4243265) B4243265
theorem B1878587 : Blo 834351 1878587 := bstep (se 1 (by rfl) ⟨1408940, by rfl⟩ : syracuseStep 1878587 = 2817881) B2817881
theorem B1256009 : Blo 834351 1256009 := bstep (se 2 (by rfl) ⟨471003, by rfl⟩ : syracuseStep 1256009 = 942007) B942007
theorem B2009735 : Blo 834351 2009735 := bstep (se 1 (by rfl) ⟨1507301, by rfl⟩ : syracuseStep 2009735 = 3014603) B3014603
theorem B1878713 : Blo 834351 1878713 := bstep (se 2 (by rfl) ⟨704517, by rfl⟩ : syracuseStep 1878713 = 1409035) B1409035
theorem B1256123 : Blo 834351 1256123 := bstep (se 1 (by rfl) ⟨942092, by rfl⟩ : syracuseStep 1256123 = 1884185) B1884185
theorem B1256183 : Blo 834351 1256183 := bstep (se 1 (by rfl) ⟨942137, by rfl⟩ : syracuseStep 1256183 = 1884275) B1884275
theorem B4238081 : Blo 834351 4238081 := bstep (se 2 (by rfl) ⟨1589280, by rfl⟩ : syracuseStep 4238081 = 3178561) B3178561
theorem B1256207 : Blo 834351 1256207 := bstep (se 1 (by rfl) ⟨942155, by rfl⟩ : syracuseStep 1256207 = 1884311) B1884311
theorem B1256249 : Blo 834351 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B1256327 : Blo 834351 1256327 := bstep (se 1 (by rfl) ⟨942245, by rfl⟩ : syracuseStep 1256327 = 1884491) B1884491
theorem B1256363 : Blo 834351 1256363 := bstep (se 1 (by rfl) ⟨942272, by rfl⟩ : syracuseStep 1256363 = 1884545) B1884545
theorem B1256393 : Blo 834351 1256393 := bstep (se 2 (by rfl) ⟨471147, by rfl⟩ : syracuseStep 1256393 = 942295) B942295
theorem B1879055 : Blo 834351 1879055 := bstep (se 1 (by rfl) ⟨1409291, by rfl⟩ : syracuseStep 1879055 = 2818583) B2818583
theorem B1879073 : Blo 834351 1879073 := bstep (se 2 (by rfl) ⟨704652, by rfl⟩ : syracuseStep 1879073 = 1409305) B1409305
theorem B1256507 : Blo 834351 1256507 := bstep (se 1 (by rfl) ⟨942380, by rfl⟩ : syracuseStep 1256507 = 1884761) B1884761
theorem B1256567 : Blo 834351 1256567 := bstep (se 1 (by rfl) ⟨942425, by rfl⟩ : syracuseStep 1256567 = 1884851) B1884851
theorem B1256591 : Blo 834351 1256591 := bstep (se 1 (by rfl) ⟨942443, by rfl⟩ : syracuseStep 1256591 = 1884887) B1884887
theorem B1256633 : Blo 834351 1256633 := bstep (se 2 (by rfl) ⟨471237, by rfl⟩ : syracuseStep 1256633 = 942475) B942475
theorem B1256711 : Blo 834351 1256711 := bstep (se 1 (by rfl) ⟨942533, by rfl⟩ : syracuseStep 1256711 = 1885067) B1885067
theorem B1256747 : Blo 834351 1256747 := bstep (se 1 (by rfl) ⟨942560, by rfl⟩ : syracuseStep 1256747 = 1885121) B1885121
theorem B1256777 : Blo 834351 1256777 := bstep (se 2 (by rfl) ⟨471291, by rfl⟩ : syracuseStep 1256777 = 942583) B942583
theorem B1879415 : Blo 834351 1879415 := bstep (se 1 (by rfl) ⟨1409561, by rfl⟩ : syracuseStep 1879415 = 2819123) B2819123
theorem B2010503 : Blo 834351 2010503 := bstep (se 1 (by rfl) ⟨1507877, by rfl⟩ : syracuseStep 2010503 = 3015755) B3015755
theorem B1256891 : Blo 834351 1256891 := bstep (se 1 (by rfl) ⟨942668, by rfl⟩ : syracuseStep 1256891 = 1885337) B1885337
theorem B1256951 : Blo 834351 1256951 := bstep (se 1 (by rfl) ⟨942713, by rfl⟩ : syracuseStep 1256951 = 1885427) B1885427
theorem B1256975 : Blo 834351 1256975 := bstep (se 1 (by rfl) ⟨942731, by rfl⟩ : syracuseStep 1256975 = 1885463) B1885463
theorem B4075031 : Blo 834351 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B1879595 : Blo 834351 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B4238891 : Blo 834351 4238891 := bstep (se 1 (by rfl) ⟨3179168, by rfl⟩ : syracuseStep 4238891 = 6358337) B6358337
theorem B1257017 : Blo 834351 1257017 := bstep (se 2 (by rfl) ⟨471381, by rfl⟩ : syracuseStep 1257017 = 942763) B942763
theorem B1257095 : Blo 834351 1257095 := bstep (se 1 (by rfl) ⟨942821, by rfl⟩ : syracuseStep 1257095 = 1885643) B1885643
theorem B1257131 : Blo 834351 1257131 := bstep (se 1 (by rfl) ⟨942848, by rfl⟩ : syracuseStep 1257131 = 1885697) B1885697
theorem B1257161 : Blo 834351 1257161 := bstep (se 2 (by rfl) ⟨471435, by rfl⟩ : syracuseStep 1257161 = 942871) B942871
theorem B1257275 : Blo 834351 1257275 := bstep (se 1 (by rfl) ⟨942956, by rfl⟩ : syracuseStep 1257275 = 1885913) B1885913
theorem B4829017 : Blo 834351 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B1257335 : Blo 834351 1257335 := bstep (se 1 (by rfl) ⟨943001, by rfl⟩ : syracuseStep 1257335 = 1886003) B1886003
theorem B1257359 : Blo 834351 1257359 := bstep (se 1 (by rfl) ⟨943019, by rfl⟩ : syracuseStep 1257359 = 1886039) B1886039
theorem B1879955 : Blo 834351 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B1257401 : Blo 834351 1257401 := bstep (se 2 (by rfl) ⟨471525, by rfl⟩ : syracuseStep 1257401 = 943051) B943051
theorem B1880009 : Blo 834351 1880009 := bstep (se 2 (by rfl) ⟨705003, by rfl⟩ : syracuseStep 1880009 = 1410007) B1410007
theorem B1191881 : Blo 834351 1191881 := bstep (se 2 (by rfl) ⟨446955, by rfl⟩ : syracuseStep 1191881 = 893911) B893911
theorem B1257479 : Blo 834351 1257479 := bstep (se 1 (by rfl) ⟨943109, by rfl⟩ : syracuseStep 1257479 = 1886219) B1886219
theorem B1257515 : Blo 834351 1257515 := bstep (se 1 (by rfl) ⟨943136, by rfl⟩ : syracuseStep 1257515 = 1886273) B1886273
theorem B1585271 : Blo 834351 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B8138989 : Blo 834351 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B1585423 : Blo 834351 1585423 := bstep (se 1 (by rfl) ⟨1189067, by rfl⟩ : syracuseStep 1585423 = 2378135) B2378135
theorem B6336953 : Blo 834351 6336953 := bstep (se 2 (by rfl) ⟨2376357, by rfl⟩ : syracuseStep 6336953 = 4752715) B4752715
theorem B1192439 : Blo 834351 1192439 := bstep (se 1 (by rfl) ⟨894329, by rfl⟩ : syracuseStep 1192439 = 1788659) B1788659
theorem B1880711 : Blo 834351 1880711 := bstep (se 1 (by rfl) ⟨1410533, by rfl⟩ : syracuseStep 1880711 = 2821067) B2821067
theorem B1585811 : Blo 834351 1585811 := bstep (se 1 (by rfl) ⟨1189358, by rfl⟩ : syracuseStep 1585811 = 2378717) B2378717
theorem B2011915 : Blo 834351 2011915 := bstep (se 1 (by rfl) ⟨1508936, by rfl⟩ : syracuseStep 2011915 = 3017873) B3017873
theorem B1192747 : Blo 834351 1192747 := bstep (se 1 (by rfl) ⟨894560, by rfl⟩ : syracuseStep 1192747 = 1789121) B1789121
theorem B1880891 : Blo 834351 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B4240187 : Blo 834351 4240187 := bstep (se 1 (by rfl) ⟨3180140, by rfl⟩ : syracuseStep 4240187 = 6360281) B6360281
theorem B3388313 : Blo 834351 3388313 := bstep (se 2 (by rfl) ⟨1270617, by rfl⟩ : syracuseStep 3388313 = 2541235) B2541235
theorem B27898805 : Blo 834351 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B1881017 : Blo 834351 1881017 := bstep (se 2 (by rfl) ⟨705381, by rfl⟩ : syracuseStep 1881017 = 1410763) B1410763
theorem B4240349 : Blo 834351 4240349 := bstep (se 3 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 4240349 = 1590131) B1590131
theorem B1783055 : Blo 834351 1783055 := bstep (se 1 (by rfl) ⟨1337291, by rfl⟩ : syracuseStep 1783055 = 2674583) B2674583
theorem B1881359 : Blo 834351 1881359 := bstep (se 1 (by rfl) ⟨1411019, by rfl⟩ : syracuseStep 1881359 = 2822039) B2822039
theorem B1193231 : Blo 834351 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B1881377 : Blo 834351 1881377 := bstep (se 2 (by rfl) ⟨705516, by rfl⟩ : syracuseStep 1881377 = 1411033) B1411033
theorem B4240673 : Blo 834351 4240673 := bstep (se 2 (by rfl) ⟨1590252, by rfl⟩ : syracuseStep 4240673 = 3180505) B3180505
theorem B1783225 : Blo 834351 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B1881719 : Blo 834351 1881719 := bstep (se 1 (by rfl) ⟨1411289, by rfl⟩ : syracuseStep 1881719 = 2822579) B2822579
theorem B1783567 : Blo 834351 1783567 := bstep (se 1 (by rfl) ⟨1337675, by rfl⟩ : syracuseStep 1783567 = 2675351) B2675351
theorem B1881899 : Blo 834351 1881899 := bstep (se 1 (by rfl) ⟨1411424, by rfl⟩ : syracuseStep 1881899 = 2822849) B2822849
theorem B1587215 : Blo 834351 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B1882259 : Blo 834351 1882259 := bstep (se 1 (by rfl) ⟨1411694, by rfl⟩ : syracuseStep 1882259 = 2823389) B2823389
theorem B1882313 : Blo 834351 1882313 := bstep (se 2 (by rfl) ⟨705867, by rfl⟩ : syracuseStep 1882313 = 1411735) B1411735
theorem B4241645 : Blo 834351 4241645 := bstep (se 3 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 4241645 = 1590617) B1590617
theorem B2013587 : Blo 834351 2013587 := bstep (se 1 (by rfl) ⟨1510190, by rfl⟩ : syracuseStep 2013587 = 3020381) B3020381
theorem B22886873 : Blo 834351 22886873 := bstep (se 2 (by rfl) ⟨8582577, by rfl⟩ : syracuseStep 22886873 = 17165155) B17165155
theorem B1587755 : Blo 834351 1587755 := bstep (se 1 (by rfl) ⟨1190816, by rfl⟩ : syracuseStep 1587755 = 2381633) B2381633
theorem B2112115 : Blo 834351 2112115 := bstep (se 1 (by rfl) ⟨1584086, by rfl⟩ : syracuseStep 2112115 = 3168173) B3168173
theorem B2112257 : Blo 834351 2112257 := bstep (se 2 (by rfl) ⟨792096, by rfl⟩ : syracuseStep 2112257 = 1584193) B1584193
theorem B10697507 : Blo 834351 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B834363 : Blo 834351 834363 := bstep (se 1 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 834363 = 1251545) B1251545
theorem B10992473 : Blo 834351 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B1784695 : Blo 834351 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B834439 : Blo 834351 834439 := bstep (se 1 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 834439 = 1251659) B1251659
theorem B1129351 : Blo 834351 1129351 := bstep (se 1 (by rfl) ⟨847013, by rfl⟩ : syracuseStep 1129351 = 1694027) B1694027
theorem B1883015 : Blo 834351 1883015 := bstep (se 1 (by rfl) ⟨1412261, by rfl⟩ : syracuseStep 1883015 = 2824523) B2824523
theorem B2014087 : Blo 834351 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B834447 : Blo 834351 834447 := bstep (se 1 (by rfl) ⟨625835, by rfl⟩ : syracuseStep 834447 = 1251671) B1251671
theorem B834491 : Blo 834351 834491 := bstep (se 1 (by rfl) ⟨625868, by rfl⟩ : syracuseStep 834491 = 1251737) B1251737
theorem B4013009 : Blo 834351 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B834567 : Blo 834351 834567 := bstep (se 1 (by rfl) ⟨625925, by rfl⟩ : syracuseStep 834567 = 1251851) B1251851
theorem B834575 : Blo 834351 834575 := bstep (se 1 (by rfl) ⟨625931, by rfl⟩ : syracuseStep 834575 = 1251863) B1251863
theorem B4242455 : Blo 834351 4242455 := bstep (se 1 (by rfl) ⟨3181841, by rfl⟩ : syracuseStep 4242455 = 6363683) B6363683
theorem B834619 : Blo 834351 834619 := bstep (se 1 (by rfl) ⟨625964, by rfl⟩ : syracuseStep 834619 = 1251929) B1251929
theorem B1883195 : Blo 834351 1883195 := bstep (se 1 (by rfl) ⟨1412396, by rfl⟩ : syracuseStep 1883195 = 2824793) B2824793
theorem B834695 : Blo 834351 834695 := bstep (se 1 (by rfl) ⟨626021, by rfl⟩ : syracuseStep 834695 = 1252043) B1252043
theorem B834703 : Blo 834351 834703 := bstep (se 1 (by rfl) ⟨626027, by rfl⟩ : syracuseStep 834703 = 1252055) B1252055
theorem B1883321 : Blo 834351 1883321 := bstep (se 2 (by rfl) ⟨706245, by rfl⟩ : syracuseStep 1883321 = 1412491) B1412491
theorem B834747 : Blo 834351 834747 := bstep (se 1 (by rfl) ⟨626060, by rfl⟩ : syracuseStep 834747 = 1252121) B1252121
theorem B2112713 : Blo 834351 2112713 := bstep (se 2 (by rfl) ⟨792267, by rfl⟩ : syracuseStep 2112713 = 1584535) B1584535
theorem B834823 : Blo 834351 834823 := bstep (se 1 (by rfl) ⟨626117, by rfl⟩ : syracuseStep 834823 = 1252235) B1252235
theorem B834831 : Blo 834351 834831 := bstep (se 1 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 834831 = 1252247) B1252247
theorem B7257377 : Blo 834351 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B834875 : Blo 834351 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B834951 : Blo 834351 834951 := bstep (se 1 (by rfl) ⟨626213, by rfl⟩ : syracuseStep 834951 = 1252427) B1252427
theorem B834959 : Blo 834351 834959 := bstep (se 1 (by rfl) ⟨626219, by rfl⟩ : syracuseStep 834959 = 1252439) B1252439
theorem B835003 : Blo 834351 835003 := bstep (se 1 (by rfl) ⟨626252, by rfl⟩ : syracuseStep 835003 = 1252505) B1252505
theorem B835079 : Blo 834351 835079 := bstep (se 1 (by rfl) ⟨626309, by rfl⟩ : syracuseStep 835079 = 1252619) B1252619
theorem B835087 : Blo 834351 835087 := bstep (se 1 (by rfl) ⟨626315, by rfl⟩ : syracuseStep 835087 = 1252631) B1252631
theorem B1883663 : Blo 834351 1883663 := bstep (se 1 (by rfl) ⟨1412747, by rfl⟩ : syracuseStep 1883663 = 2825495) B2825495
theorem B1883681 : Blo 834351 1883681 := bstep (se 2 (by rfl) ⟨706380, by rfl⟩ : syracuseStep 1883681 = 1412761) B1412761
theorem B2113067 : Blo 834351 2113067 := bstep (se 1 (by rfl) ⟨1584800, by rfl⟩ : syracuseStep 2113067 = 3169601) B3169601
theorem B835131 : Blo 834351 835131 := bstep (se 1 (by rfl) ⟨626348, by rfl⟩ : syracuseStep 835131 = 1252697) B1252697
theorem B835207 : Blo 834351 835207 := bstep (se 1 (by rfl) ⟨626405, by rfl⟩ : syracuseStep 835207 = 1252811) B1252811
theorem B1588871 : Blo 834351 1588871 := bstep (se 1 (by rfl) ⟨1191653, by rfl⟩ : syracuseStep 1588871 = 2383307) B2383307
theorem B835215 : Blo 834351 835215 := bstep (se 1 (by rfl) ⟨626411, by rfl⟩ : syracuseStep 835215 = 1252823) B1252823
theorem B835259 : Blo 834351 835259 := bstep (se 1 (by rfl) ⟨626444, by rfl⟩ : syracuseStep 835259 = 1252889) B1252889
theorem B13549285 : Blo 834351 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B835335 : Blo 834351 835335 := bstep (se 1 (by rfl) ⟨626501, by rfl⟩ : syracuseStep 835335 = 1253003) B1253003
theorem B835343 : Blo 834351 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B835387 : Blo 834351 835387 := bstep (se 1 (by rfl) ⟨626540, by rfl⟩ : syracuseStep 835387 = 1253081) B1253081
theorem B1884023 : Blo 834351 1884023 := bstep (se 1 (by rfl) ⟨1413017, by rfl⟩ : syracuseStep 1884023 = 2826035) B2826035
theorem B835463 : Blo 834351 835463 := bstep (se 1 (by rfl) ⟨626597, by rfl⟩ : syracuseStep 835463 = 1253195) B1253195
theorem B835471 : Blo 834351 835471 := bstep (se 1 (by rfl) ⟨626603, by rfl⟩ : syracuseStep 835471 = 1253207) B1253207
theorem B835515 : Blo 834351 835515 := bstep (se 1 (by rfl) ⟨626636, by rfl⟩ : syracuseStep 835515 = 1253273) B1253273
theorem B835591 : Blo 834351 835591 := bstep (se 1 (by rfl) ⟨626693, by rfl⟩ : syracuseStep 835591 = 1253387) B1253387
theorem B835599 : Blo 834351 835599 := bstep (se 1 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 835599 = 1253399) B1253399
theorem B1884203 : Blo 834351 1884203 := bstep (se 1 (by rfl) ⟨1413152, by rfl⟩ : syracuseStep 1884203 = 2826305) B2826305
theorem B835643 : Blo 834351 835643 := bstep (se 1 (by rfl) ⟨626732, by rfl⟩ : syracuseStep 835643 = 1253465) B1253465
theorem B835719 : Blo 834351 835719 := bstep (se 1 (by rfl) ⟨626789, by rfl⟩ : syracuseStep 835719 = 1253579) B1253579
theorem B835727 : Blo 834351 835727 := bstep (se 1 (by rfl) ⟨626795, by rfl⟩ : syracuseStep 835727 = 1253591) B1253591
theorem B1589395 : Blo 834351 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B835771 : Blo 834351 835771 := bstep (se 1 (by rfl) ⟨626828, by rfl⟩ : syracuseStep 835771 = 1253657) B1253657
theorem B835847 : Blo 834351 835847 := bstep (se 1 (by rfl) ⟨626885, by rfl⟩ : syracuseStep 835847 = 1253771) B1253771
theorem B835855 : Blo 834351 835855 := bstep (se 1 (by rfl) ⟨626891, by rfl⟩ : syracuseStep 835855 = 1253783) B1253783
theorem B835899 : Blo 834351 835899 := bstep (se 1 (by rfl) ⟨626924, by rfl⟩ : syracuseStep 835899 = 1253849) B1253849
theorem B835975 : Blo 834351 835975 := bstep (se 1 (by rfl) ⟨626981, by rfl⟩ : syracuseStep 835975 = 1253963) B1253963
theorem B835983 : Blo 834351 835983 := bstep (se 1 (by rfl) ⟨626987, by rfl⟩ : syracuseStep 835983 = 1253975) B1253975
theorem B1884563 : Blo 834351 1884563 := bstep (se 1 (by rfl) ⟨1413422, by rfl⟩ : syracuseStep 1884563 = 2826845) B2826845
theorem B836027 : Blo 834351 836027 := bstep (se 1 (by rfl) ⟨627020, by rfl⟩ : syracuseStep 836027 = 1254041) B1254041
theorem B1884617 : Blo 834351 1884617 := bstep (se 2 (by rfl) ⟨706731, by rfl⟩ : syracuseStep 1884617 = 1413463) B1413463
theorem B836103 : Blo 834351 836103 := bstep (se 1 (by rfl) ⟨627077, by rfl⟩ : syracuseStep 836103 = 1254155) B1254155
theorem B2114059 : Blo 834351 2114059 := bstep (se 1 (by rfl) ⟨1585544, by rfl⟩ : syracuseStep 2114059 = 3171089) B3171089
theorem B836111 : Blo 834351 836111 := bstep (se 1 (by rfl) ⟨627083, by rfl⟩ : syracuseStep 836111 = 1254167) B1254167
theorem B836155 : Blo 834351 836155 := bstep (se 1 (by rfl) ⟨627116, by rfl⟩ : syracuseStep 836155 = 1254233) B1254233
theorem B836231 : Blo 834351 836231 := bstep (se 1 (by rfl) ⟨627173, by rfl⟩ : syracuseStep 836231 = 1254347) B1254347
theorem B836239 : Blo 834351 836239 := bstep (se 1 (by rfl) ⟨627179, by rfl⟩ : syracuseStep 836239 = 1254359) B1254359
theorem B2114201 : Blo 834351 2114201 := bstep (se 2 (by rfl) ⟨792825, by rfl⟩ : syracuseStep 2114201 = 1585651) B1585651
theorem B836283 : Blo 834351 836283 := bstep (se 1 (by rfl) ⟨627212, by rfl⟩ : syracuseStep 836283 = 1254425) B1254425
theorem B2376449 : Blo 834351 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B2573057 : Blo 834351 2573057 := bstep (se 2 (by rfl) ⟨964896, by rfl⟩ : syracuseStep 2573057 = 1929793) B1929793
theorem B836359 : Blo 834351 836359 := bstep (se 1 (by rfl) ⟨627269, by rfl⟩ : syracuseStep 836359 = 1254539) B1254539
theorem B836367 : Blo 834351 836367 := bstep (se 1 (by rfl) ⟨627275, by rfl⟩ : syracuseStep 836367 = 1254551) B1254551
theorem B24134435 : Blo 834351 24134435 := bstep (se 1 (by rfl) ⟨18100826, by rfl⟩ : syracuseStep 24134435 = 36201653) B36201653
theorem B2114363 : Blo 834351 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B836411 : Blo 834351 836411 := bstep (se 1 (by rfl) ⟨627308, by rfl⟩ : syracuseStep 836411 = 1254617) B1254617
theorem B4768571 : Blo 834351 4768571 := bstep (se 1 (by rfl) ⟨3576428, by rfl⟩ : syracuseStep 4768571 = 7152857) B7152857
theorem B836487 : Blo 834351 836487 := bstep (se 1 (by rfl) ⟨627365, by rfl⟩ : syracuseStep 836487 = 1254731) B1254731
theorem B836495 : Blo 834351 836495 := bstep (se 1 (by rfl) ⟨627371, by rfl⟩ : syracuseStep 836495 = 1254743) B1254743
theorem B30983093 : Blo 834351 30983093 := bstep (se 5 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 30983093 = 2904665) B2904665
theorem B836539 : Blo 834351 836539 := bstep (se 1 (by rfl) ⟨627404, by rfl⟩ : syracuseStep 836539 = 1254809) B1254809
theorem B836615 : Blo 834351 836615 := bstep (se 1 (by rfl) ⟨627461, by rfl⟩ : syracuseStep 836615 = 1254923) B1254923
theorem B836623 : Blo 834351 836623 := bstep (se 1 (by rfl) ⟨627467, by rfl⟩ : syracuseStep 836623 = 1254935) B1254935
theorem B836667 : Blo 834351 836667 := bstep (se 1 (by rfl) ⟨627500, by rfl⟩ : syracuseStep 836667 = 1255001) B1255001
theorem B836743 : Blo 834351 836743 := bstep (se 1 (by rfl) ⟨627557, by rfl⟩ : syracuseStep 836743 = 1255115) B1255115
theorem B1885319 : Blo 834351 1885319 := bstep (se 1 (by rfl) ⟨1413989, by rfl⟩ : syracuseStep 1885319 = 2827979) B2827979
theorem B836751 : Blo 834351 836751 := bstep (se 1 (by rfl) ⟨627563, by rfl⟩ : syracuseStep 836751 = 1255127) B1255127
theorem B2114707 : Blo 834351 2114707 := bstep (se 1 (by rfl) ⟨1586030, by rfl⟩ : syracuseStep 2114707 = 3172061) B3172061
theorem B836795 : Blo 834351 836795 := bstep (se 1 (by rfl) ⟨627596, by rfl⟩ : syracuseStep 836795 = 1255193) B1255193
theorem B836871 : Blo 834351 836871 := bstep (se 1 (by rfl) ⟨627653, by rfl⟩ : syracuseStep 836871 = 1255307) B1255307
theorem B836879 : Blo 834351 836879 := bstep (se 1 (by rfl) ⟨627659, by rfl⟩ : syracuseStep 836879 = 1255319) B1255319
theorem B2114849 : Blo 834351 2114849 := bstep (se 2 (by rfl) ⟨793068, by rfl⟩ : syracuseStep 2114849 = 1586137) B1586137
theorem B1131833 : Blo 834351 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B2377019 : Blo 834351 2377019 := bstep (se 1 (by rfl) ⟨1782764, by rfl⟩ : syracuseStep 2377019 = 3565529) B3565529
theorem B836923 : Blo 834351 836923 := bstep (se 1 (by rfl) ⟨627692, by rfl⟩ : syracuseStep 836923 = 1255385) B1255385
theorem B1590587 : Blo 834351 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B1885499 : Blo 834351 1885499 := bstep (se 1 (by rfl) ⟨1414124, by rfl⟩ : syracuseStep 1885499 = 2828249) B2828249
theorem B836999 : Blo 834351 836999 := bstep (se 1 (by rfl) ⟨627749, by rfl⟩ : syracuseStep 836999 = 1255499) B1255499
theorem B837007 : Blo 834351 837007 := bstep (se 1 (by rfl) ⟨627755, by rfl⟩ : syracuseStep 837007 = 1255511) B1255511
theorem B1885625 : Blo 834351 1885625 := bstep (se 2 (by rfl) ⟨707109, by rfl⟩ : syracuseStep 1885625 = 1414219) B1414219
theorem B837051 : Blo 834351 837051 := bstep (se 1 (by rfl) ⟨627788, by rfl⟩ : syracuseStep 837051 = 1255577) B1255577
theorem B837127 : Blo 834351 837127 := bstep (se 1 (by rfl) ⟨627845, by rfl⟩ : syracuseStep 837127 = 1255691) B1255691
theorem B837135 : Blo 834351 837135 := bstep (se 1 (by rfl) ⟨627851, by rfl⟩ : syracuseStep 837135 = 1255703) B1255703
theorem B2377259 : Blo 834351 2377259 := bstep (se 1 (by rfl) ⟨1782944, by rfl⟩ : syracuseStep 2377259 = 3565889) B3565889
theorem B837179 : Blo 834351 837179 := bstep (se 1 (by rfl) ⟨627884, by rfl⟩ : syracuseStep 837179 = 1255769) B1255769
theorem B837255 : Blo 834351 837255 := bstep (se 1 (by rfl) ⟨627941, by rfl⟩ : syracuseStep 837255 = 1255883) B1255883
theorem B837263 : Blo 834351 837263 := bstep (se 1 (by rfl) ⟨627947, by rfl⟩ : syracuseStep 837263 = 1255895) B1255895
theorem B837307 : Blo 834351 837307 := bstep (se 1 (by rfl) ⟨627980, by rfl⟩ : syracuseStep 837307 = 1255961) B1255961
theorem B837383 : Blo 834351 837383 := bstep (se 1 (by rfl) ⟨628037, by rfl⟩ : syracuseStep 837383 = 1256075) B1256075
theorem B837391 : Blo 834351 837391 := bstep (se 1 (by rfl) ⟨628043, by rfl⟩ : syracuseStep 837391 = 1256087) B1256087
theorem B1885967 : Blo 834351 1885967 := bstep (se 1 (by rfl) ⟨1414475, by rfl⟩ : syracuseStep 1885967 = 2828951) B2828951
theorem B1591073 : Blo 834351 1591073 := bstep (se 2 (by rfl) ⟨596652, by rfl⟩ : syracuseStep 1591073 = 1193305) B1193305
theorem B1885985 : Blo 834351 1885985 := bstep (se 2 (by rfl) ⟨707244, by rfl⟩ : syracuseStep 1885985 = 1414489) B1414489
theorem B837435 : Blo 834351 837435 := bstep (se 1 (by rfl) ⟨628076, by rfl⟩ : syracuseStep 837435 = 1256153) B1256153
theorem B2541431 : Blo 834351 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B837511 : Blo 834351 837511 := bstep (se 1 (by rfl) ⟨628133, by rfl⟩ : syracuseStep 837511 = 1256267) B1256267
theorem B837519 : Blo 834351 837519 := bstep (se 1 (by rfl) ⟨628139, by rfl⟩ : syracuseStep 837519 = 1256279) B1256279
theorem B837563 : Blo 834351 837563 := bstep (se 1 (by rfl) ⟨628172, by rfl⟩ : syracuseStep 837563 = 1256345) B1256345
theorem B837639 : Blo 834351 837639 := bstep (se 1 (by rfl) ⟨628229, by rfl⟩ : syracuseStep 837639 = 1256459) B1256459
theorem B5425163 : Blo 834351 5425163 := bstep (se 1 (by rfl) ⟨4068872, by rfl⟩ : syracuseStep 5425163 = 8137745) B8137745
theorem B837647 : Blo 834351 837647 := bstep (se 1 (by rfl) ⟨628235, by rfl⟩ : syracuseStep 837647 = 1256471) B1256471
theorem B1591339 : Blo 834351 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B837691 : Blo 834351 837691 := bstep (se 1 (by rfl) ⟨628268, by rfl⟩ : syracuseStep 837691 = 1256537) B1256537
theorem B837767 : Blo 834351 837767 := bstep (se 1 (by rfl) ⟨628325, by rfl⟩ : syracuseStep 837767 = 1256651) B1256651
theorem B837775 : Blo 834351 837775 := bstep (se 1 (by rfl) ⟨628331, by rfl⟩ : syracuseStep 837775 = 1256663) B1256663
theorem B837819 : Blo 834351 837819 := bstep (se 1 (by rfl) ⟨628364, by rfl⟩ : syracuseStep 837819 = 1256729) B1256729
theorem B4770029 : Blo 834351 4770029 := bstep (se 3 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 4770029 = 1788761) B1788761
theorem B2115841 : Blo 834351 2115841 := bstep (se 2 (by rfl) ⟨793440, by rfl⟩ : syracuseStep 2115841 = 1586881) B1586881
theorem B837895 : Blo 834351 837895 := bstep (se 1 (by rfl) ⟨628421, by rfl⟩ : syracuseStep 837895 = 1256843) B1256843
theorem B837903 : Blo 834351 837903 := bstep (se 1 (by rfl) ⟨628427, by rfl⟩ : syracuseStep 837903 = 1256855) B1256855
theorem B837947 : Blo 834351 837947 := bstep (se 1 (by rfl) ⟨628460, by rfl⟩ : syracuseStep 837947 = 1256921) B1256921
theorem B838023 : Blo 834351 838023 := bstep (se 1 (by rfl) ⟨628517, by rfl⟩ : syracuseStep 838023 = 1257035) B1257035
theorem B838031 : Blo 834351 838031 := bstep (se 1 (by rfl) ⟨628523, by rfl⟩ : syracuseStep 838031 = 1257047) B1257047
theorem B838075 : Blo 834351 838075 := bstep (se 1 (by rfl) ⟨628556, by rfl⟩ : syracuseStep 838075 = 1257113) B1257113
theorem B838151 : Blo 834351 838151 := bstep (se 1 (by rfl) ⟨628613, by rfl⟩ : syracuseStep 838151 = 1257227) B1257227
theorem B838159 : Blo 834351 838159 := bstep (se 1 (by rfl) ⟨628619, by rfl⟩ : syracuseStep 838159 = 1257239) B1257239
theorem B838203 : Blo 834351 838203 := bstep (se 1 (by rfl) ⟨628652, by rfl⟩ : syracuseStep 838203 = 1257305) B1257305
theorem B838279 : Blo 834351 838279 := bstep (se 1 (by rfl) ⟨628709, by rfl⟩ : syracuseStep 838279 = 1257419) B1257419
theorem B838287 : Blo 834351 838287 := bstep (se 1 (by rfl) ⟨628715, by rfl⟩ : syracuseStep 838287 = 1257431) B1257431
theorem B838331 : Blo 834351 838331 := bstep (se 1 (by rfl) ⟨628748, by rfl⟩ : syracuseStep 838331 = 1257497) B1257497
theorem B1788617 : Blo 834351 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B4016911 : Blo 834351 4016911 := bstep (se 1 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 4016911 = 6025367) B6025367
theorem B2116439 : Blo 834351 2116439 := bstep (se 1 (by rfl) ⟨1587329, by rfl⟩ : syracuseStep 2116439 = 3174659) B3174659
theorem B5229521 : Blo 834351 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B2116651 : Blo 834351 2116651 := bstep (se 1 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 2116651 = 3174977) B3174977
theorem B2116793 : Blo 834351 2116793 := bstep (se 2 (by rfl) ⟨793797, by rfl⟩ : syracuseStep 2116793 = 1587595) B1587595
theorem B4574839 : Blo 834351 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B2543375 : Blo 834351 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B15257393 : Blo 834351 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B2150459 : Blo 834351 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B2117785 : Blo 834351 2117785 := bstep (se 2 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 2117785 = 1588339) B1588339
theorem B2117947 : Blo 834351 2117947 := bstep (se 1 (by rfl) ⟨1588460, by rfl⟩ : syracuseStep 2117947 = 3176921) B3176921
theorem B2118089 : Blo 834351 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B6771203 : Blo 834351 6771203 := bstep (se 1 (by rfl) ⟨5078402, by rfl⟩ : syracuseStep 6771203 = 10156805) B10156805
theorem B2544385 : Blo 834351 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B938767 : Blo 834351 938767 := bstep (se 1 (by rfl) ⟨704075, by rfl⟩ : syracuseStep 938767 = 1408151) B1408151
theorem B2118433 : Blo 834351 2118433 := bstep (se 2 (by rfl) ⟨794412, by rfl⟩ : syracuseStep 2118433 = 1588825) B1588825
theorem B1692731 : Blo 834351 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B939271 : Blo 834351 939271 := bstep (se 1 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 939271 = 1408907) B1408907
theorem B1004843 : Blo 834351 1004843 := bstep (se 1 (by rfl) ⟨753632, by rfl⟩ : syracuseStep 1004843 = 1507265) B1507265
theorem B5363003 : Blo 834351 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B2119031 : Blo 834351 2119031 := bstep (se 1 (by rfl) ⟨1589273, by rfl⟩ : syracuseStep 2119031 = 3178547) B3178547
theorem B6116755 : Blo 834351 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B939451 : Blo 834351 939451 := bstep (se 1 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 939451 = 1409177) B1409177
theorem B9655811 : Blo 834351 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B1070651 : Blo 834351 1070651 := bstep (se 1 (by rfl) ⟨802988, by rfl⟩ : syracuseStep 1070651 = 1605977) B1605977
theorem B939919 : Blo 834351 939919 := bstep (se 1 (by rfl) ⟨704939, by rfl⟩ : syracuseStep 939919 = 1409879) B1409879
theorem B2381825 : Blo 834351 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B2414603 : Blo 834351 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B940423 : Blo 834351 940423 := bstep (se 1 (by rfl) ⟨705317, by rfl⟩ : syracuseStep 940423 = 1410635) B1410635
theorem B1005967 : Blo 834351 1005967 := bstep (se 1 (by rfl) ⟨754475, by rfl⟩ : syracuseStep 1005967 = 1508951) B1508951
theorem B3168659 : Blo 834351 3168659 := bstep (se 1 (by rfl) ⟨2376494, by rfl⟩ : syracuseStep 3168659 = 4752989) B4752989
theorem B2382281 : Blo 834351 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B4774403 : Blo 834351 4774403 := bstep (se 1 (by rfl) ⟨3580802, by rfl⟩ : syracuseStep 4774403 = 7161605) B7161605
theorem B940603 : Blo 834351 940603 := bstep (se 1 (by rfl) ⟨705452, by rfl⟩ : syracuseStep 940603 = 1410905) B1410905
theorem B2120327 : Blo 834351 2120327 := bstep (se 1 (by rfl) ⟨1590245, by rfl⟩ : syracuseStep 2120327 = 3180491) B3180491
theorem B2120377 : Blo 834351 2120377 := bstep (se 2 (by rfl) ⟨795141, by rfl⟩ : syracuseStep 2120377 = 1590283) B1590283
theorem B2382635 : Blo 834351 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B941071 : Blo 834351 941071 := bstep (se 1 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 941071 = 1411607) B1411607
theorem B2383033 : Blo 834351 2383033 := bstep (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) B1787275
theorem B2120975 : Blo 834351 2120975 := bstep (se 1 (by rfl) ⟨1590731, by rfl⟩ : syracuseStep 2120975 = 3181463) B3181463
theorem B1269163 : Blo 834351 1269163 := bstep (se 1 (by rfl) ⟨951872, by rfl⟩ : syracuseStep 1269163 = 1903745) B1903745
theorem B11427281 : Blo 834351 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B941575 : Blo 834351 941575 := bstep (se 1 (by rfl) ⟨706181, by rfl⟩ : syracuseStep 941575 = 1412363) B1412363
theorem B1007111 : Blo 834351 1007111 := bstep (se 1 (by rfl) ⟨755333, by rfl⟩ : syracuseStep 1007111 = 1510667) B1510667
theorem B941755 : Blo 834351 941755 := bstep (se 1 (by rfl) ⟨706316, by rfl⟩ : syracuseStep 941755 = 1412633) B1412633
theorem B2547571 : Blo 834351 2547571 := bstep (se 1 (by rfl) ⟨1910678, by rfl⟩ : syracuseStep 2547571 = 3821357) B3821357
theorem B2121673 : Blo 834351 2121673 := bstep (se 2 (by rfl) ⟨795627, by rfl⟩ : syracuseStep 2121673 = 1591255) B1591255
theorem B2121815 : Blo 834351 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B27091037 : Blo 834351 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B942223 : Blo 834351 942223 := bstep (se 1 (by rfl) ⟨706667, by rfl⟩ : syracuseStep 942223 = 1413335) B1413335
theorem B2679041 : Blo 834351 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B4022561 : Blo 834351 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B2384275 : Blo 834351 2384275 := bstep (se 1 (by rfl) ⟨1788206, by rfl⟩ : syracuseStep 2384275 = 3576413) B3576413
theorem B4022713 : Blo 834351 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B942727 : Blo 834351 942727 := bstep (se 1 (by rfl) ⟨707045, by rfl⟩ : syracuseStep 942727 = 1414091) B1414091
theorem B8053505 : Blo 834351 8053505 := bstep (se 2 (by rfl) ⟨3020064, by rfl⟩ : syracuseStep 8053505 = 6040129) B6040129
theorem B942907 : Blo 834351 942907 := bstep (se 1 (by rfl) ⟨707180, by rfl⟩ : syracuseStep 942907 = 1414361) B1414361
theorem B3171257 : Blo 834351 3171257 := bstep (se 2 (by rfl) ⟨1189221, by rfl⟩ : syracuseStep 3171257 = 2378443) B2378443
theorem B3564947 : Blo 834351 3564947 := bstep (se 1 (by rfl) ⟨2673710, by rfl⟩ : syracuseStep 3564947 = 5347421) B5347421
theorem B2352655 : Blo 834351 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B1271609 : Blo 834351 1271609 := bstep (se 2 (by rfl) ⟨476853, by rfl⟩ : syracuseStep 1271609 = 953707) B953707
theorem B3172243 : Blo 834351 3172243 := bstep (se 1 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 3172243 = 4758365) B4758365
theorem B2385949 : Blo 834351 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B2386007 : Blo 834351 2386007 := bstep (se 1 (by rfl) ⟨1789505, by rfl⟩ : syracuseStep 2386007 = 3579011) B3579011
theorem B7137821 : Blo 834351 7137821 := bstep (se 3 (by rfl) ⟨1338341, by rfl⟩ : syracuseStep 7137821 = 2676683) B2676683
theorem B2714141 : Blo 834351 2714141 := bstep (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) B1017803
theorem B2255447 : Blo 834351 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B2256281 : Blo 834351 2256281 := bstep (se 2 (by rfl) ⟨846105, by rfl⟩ : syracuseStep 2256281 = 1692211) B1692211
theorem B16281091 : Blo 834351 16281091 := bstep (se 1 (by rfl) ⟨12210818, by rfl⟩ : syracuseStep 16281091 = 24421637) B24421637
theorem B9530945 : Blo 834351 9530945 := bstep (se 2 (by rfl) ⟨3574104, by rfl⟩ : syracuseStep 9530945 = 7148209) B7148209
theorem B3173975 : Blo 834351 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B10710629 : Blo 834351 10710629 := bstep (se 4 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 10710629 = 2008243) B2008243
theorem B6025049 : Blo 834351 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B3174461 : Blo 834351 3174461 := bstep (se 3 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 3174461 = 1190423) B1190423
theorem B7139461 : Blo 834351 7139461 := bstep (se 4 (by rfl) ⟨669324, by rfl⟩ : syracuseStep 7139461 = 1338649) B1338649
theorem B3567817 : Blo 834351 3567817 := bstep (se 2 (by rfl) ⟨1337931, by rfl⟩ : syracuseStep 3567817 = 2675863) B2675863
theorem B3567887 : Blo 834351 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B2683169 : Blo 834351 2683169 := bstep (se 2 (by rfl) ⟨1006188, by rfl⟩ : syracuseStep 2683169 = 2012377) B2012377
theorem B2617661 : Blo 834351 2617661 := bstep (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) B981623
theorem B7631617 : Blo 834351 7631617 := bstep (se 2 (by rfl) ⟨2861856, by rfl⟩ : syracuseStep 7631617 = 5723713) B5723713
theorem B8581925 : Blo 834351 8581925 := bstep (se 4 (by rfl) ⟨804555, by rfl⟩ : syracuseStep 8581925 = 1609111) B1609111
theorem B1504135 : Blo 834351 1504135 := bstep (se 1 (by rfl) ⟨1128101, by rfl⟩ : syracuseStep 1504135 = 2256203) B2256203
theorem B2683783 : Blo 834351 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B5731793 : Blo 834351 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B6780419 : Blo 834351 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B2258617 : Blo 834351 2258617 := bstep (se 2 (by rfl) ⟨846981, by rfl⟩ : syracuseStep 2258617 = 1693963) B1693963
theorem B18118475 : Blo 834351 18118475 := bstep (se 1 (by rfl) ⟨13588856, by rfl⟩ : syracuseStep 18118475 = 27177713) B27177713
theorem B4028249 : Blo 834351 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B6453107 : Blo 834351 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B2816315 : Blo 834351 2816315 := bstep (se 1 (by rfl) ⟨2112236, by rfl⟩ : syracuseStep 2816315 = 4224473) B4224473
theorem B6355421 : Blo 834351 6355421 := bstep (se 3 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 6355421 = 2383283) B2383283
theorem B7240195 : Blo 834351 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B3570263 : Blo 834351 3570263 := bstep (se 1 (by rfl) ⟨2677697, by rfl⟩ : syracuseStep 3570263 = 5355395) B5355395
theorem B32275205 : Blo 834351 32275205 := bstep (se 4 (by rfl) ⟨3025800, by rfl⟩ : syracuseStep 32275205 = 6051601) B6051601
theorem B2816801 : Blo 834351 2816801 := bstep (se 2 (by rfl) ⟨1056300, by rfl⟩ : syracuseStep 2816801 = 2112601) B2112601
theorem B7142195 : Blo 834351 7142195 := bstep (se 1 (by rfl) ⟨5356646, by rfl⟩ : syracuseStep 7142195 = 10713293) B10713293
theorem B32635747 : Blo 834351 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B1408043 : Blo 834351 1408043 := bstep (se 1 (by rfl) ⟨1056032, by rfl⟩ : syracuseStep 1408043 = 2112065) B2112065
theorem B1342507 : Blo 834351 1342507 := bstep (se 1 (by rfl) ⟨1006880, by rfl⟩ : syracuseStep 1342507 = 2013761) B2013761
theorem B5078209 : Blo 834351 5078209 := bstep (se 2 (by rfl) ⟨1904328, by rfl⟩ : syracuseStep 5078209 = 3808657) B3808657
theorem B2817395 : Blo 834351 2817395 := bstep (se 1 (by rfl) ⟨2113046, by rfl⟩ : syracuseStep 2817395 = 4226093) B4226093
theorem B3177863 : Blo 834351 3177863 := bstep (se 1 (by rfl) ⟨2383397, by rfl⟩ : syracuseStep 3177863 = 4766795) B4766795
theorem B1408441 : Blo 834351 1408441 := bstep (se 2 (by rfl) ⟨528165, by rfl⟩ : syracuseStep 1408441 = 1056331) B1056331
theorem B4521401 : Blo 834351 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B1507105 : Blo 834351 1507105 := bstep (se 2 (by rfl) ⟨565164, by rfl⟩ : syracuseStep 1507105 = 1130329) B1130329
theorem B6422435 : Blo 834351 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B12058571 : Blo 834351 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B2818205 : Blo 834351 2818205 := bstep (se 3 (by rfl) ⟨528413, by rfl⟩ : syracuseStep 2818205 = 1056827) B1056827
theorem B4227389 : Blo 834351 4227389 := bstep (se 3 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 4227389 = 1585271) B1585271
theorem B1507727 : Blo 834351 1507727 := bstep (se 1 (by rfl) ⟨1130795, by rfl⟩ : syracuseStep 1507727 = 2261591) B2261591
theorem B1409467 : Blo 834351 1409467 := bstep (se 1 (by rfl) ⟨1057100, by rfl⟩ : syracuseStep 1409467 = 2114201) B2114201
theorem B16089623 : Blo 834351 16089623 := bstep (se 1 (by rfl) ⟨12067217, by rfl⟩ : syracuseStep 16089623 = 24134435) B24134435
theorem B3179033 : Blo 834351 3179033 := bstep (se 2 (by rfl) ⟨1192137, by rfl⟩ : syracuseStep 3179033 = 2384275) B2384275
theorem B1409575 : Blo 834351 1409575 := bstep (se 1 (by rfl) ⟨1057181, by rfl⟩ : syracuseStep 1409575 = 2114363) B2114363
theorem B3179047 : Blo 834351 3179047 := bstep (se 1 (by rfl) ⟨2384285, by rfl⟩ : syracuseStep 3179047 = 4768571) B4768571
theorem B7144109 : Blo 834351 7144109 := bstep (se 3 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 7144109 = 2679041) B2679041
theorem B2818745 : Blo 834351 2818745 := bstep (se 2 (by rfl) ⟨1057029, by rfl⟩ : syracuseStep 2818745 = 2114059) B2114059
theorem B1508051 : Blo 834351 1508051 := bstep (se 1 (by rfl) ⟨1131038, by rfl⟩ : syracuseStep 1508051 = 2262077) B2262077
theorem B1409899 : Blo 834351 1409899 := bstep (se 1 (by rfl) ⟨1057424, by rfl⟩ : syracuseStep 1409899 = 2114849) B2114849
theorem B22938635 : Blo 834351 22938635 := bstep (se 1 (by rfl) ⟨17203976, by rfl⟩ : syracuseStep 22938635 = 34407953) B34407953
theorem B6030379 : Blo 834351 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B19268761 : Blo 834351 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B2819339 : Blo 834351 2819339 := bstep (se 1 (by rfl) ⟨2114504, by rfl⟩ : syracuseStep 2819339 = 4229009) B4229009
theorem B3179837 : Blo 834351 3179837 := bstep (se 3 (by rfl) ⟨596219, by rfl⟩ : syracuseStep 3179837 = 1192439) B1192439
theorem B3180019 : Blo 834351 3180019 := bstep (se 1 (by rfl) ⟨2385014, by rfl⟩ : syracuseStep 3180019 = 4770029) B4770029
theorem B2819609 : Blo 834351 2819609 := bstep (se 2 (by rfl) ⟨1057353, by rfl⟩ : syracuseStep 2819609 = 2114707) B2114707
theorem B3212939 : Blo 834351 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B34309777 : Blo 834351 34309777 := bstep (se 2 (by rfl) ⟨12866166, by rfl⟩ : syracuseStep 34309777 = 25732333) B25732333
theorem B25790201 : Blo 834351 25790201 := bstep (se 2 (by rfl) ⟨9671325, by rfl⟩ : syracuseStep 25790201 = 19342651) B19342651
theorem B1410959 : Blo 834351 1410959 := bstep (se 1 (by rfl) ⟨1058219, by rfl⟩ : syracuseStep 1410959 = 2116439) B2116439
theorem B1411195 : Blo 834351 1411195 := bstep (se 1 (by rfl) ⟨1058396, by rfl⟩ : syracuseStep 1411195 = 2116793) B2116793
theorem B4229657 : Blo 834351 4229657 := bstep (se 2 (by rfl) ⟨1586121, by rfl⟩ : syracuseStep 4229657 = 3172243) B3172243
theorem B2820743 : Blo 834351 2820743 := bstep (se 1 (by rfl) ⟨2115557, by rfl⟩ : syracuseStep 2820743 = 4231115) B4231115
theorem B2820797 : Blo 834351 2820797 := bstep (se 3 (by rfl) ⟨528899, by rfl⟩ : syracuseStep 2820797 = 1057799) B1057799
theorem B3181265 : Blo 834351 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B2820959 : Blo 834351 2820959 := bstep (se 1 (by rfl) ⟨2115719, by rfl⟩ : syracuseStep 2820959 = 4231439) B4231439
theorem B1412059 : Blo 834351 1412059 := bstep (se 1 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 1412059 = 2118089) B2118089
theorem B2821121 : Blo 834351 2821121 := bstep (se 2 (by rfl) ⟨1057920, by rfl⟩ : syracuseStep 2821121 = 2115841) B2115841
theorem B9637157 : Blo 834351 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B3181949 : Blo 834351 3181949 := bstep (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) B1193231
theorem B3018221 : Blo 834351 3018221 := bstep (se 3 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 3018221 = 1131833) B1131833
theorem B3575335 : Blo 834351 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1412687 : Blo 834351 1412687 := bstep (se 1 (by rfl) ⟨1059515, by rfl⟩ : syracuseStep 1412687 = 2119031) B2119031
theorem B2821931 : Blo 834351 2821931 := bstep (se 1 (by rfl) ⟨2116448, by rfl⟩ : syracuseStep 2821931 = 4232897) B4232897
theorem B1609735 : Blo 834351 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B2822201 : Blo 834351 2822201 := bstep (se 2 (by rfl) ⟨1058325, by rfl⟩ : syracuseStep 2822201 = 2116651) B2116651
theorem B2855069 : Blo 834351 2855069 := bstep (se 3 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 2855069 = 1070651) B1070651
theorem B19337395 : Blo 834351 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B3182935 : Blo 834351 3182935 := bstep (se 1 (by rfl) ⟨2387201, by rfl⟩ : syracuseStep 3182935 = 4774403) B4774403
theorem B2822525 : Blo 834351 2822525 := bstep (se 3 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 2822525 = 1058447) B1058447
theorem B1413551 : Blo 834351 1413551 := bstep (se 1 (by rfl) ⟨1060163, by rfl⟩ : syracuseStep 1413551 = 2120327) B2120327
theorem B2822795 : Blo 834351 2822795 := bstep (se 1 (by rfl) ⟨2117096, by rfl⟩ : syracuseStep 2822795 = 4234193) B4234193
theorem B6099785 : Blo 834351 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B1413983 : Blo 834351 1413983 := bstep (se 1 (by rfl) ⟨1060487, by rfl⟩ : syracuseStep 1413983 = 2120975) B2120975
theorem B4232573 : Blo 834351 4232573 := bstep (se 3 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 4232573 = 1587215) B1587215
theorem B1414543 : Blo 834351 1414543 := bstep (se 1 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 1414543 = 2121815) B2121815
theorem B18060691 : Blo 834351 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B2823713 : Blo 834351 2823713 := bstep (se 2 (by rfl) ⟨1058892, by rfl⟩ : syracuseStep 2823713 = 2117785) B2117785
theorem B6362711 : Blo 834351 6362711 := bstep (se 1 (by rfl) ⟨4772033, by rfl⟩ : syracuseStep 6362711 = 9544067) B9544067
theorem B4757089 : Blo 834351 4757089 := bstep (se 2 (by rfl) ⟨1783908, by rfl⟩ : syracuseStep 4757089 = 3567817) B3567817
theorem B10851985 : Blo 834351 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B2823929 : Blo 834351 2823929 := bstep (se 2 (by rfl) ⟨1058973, by rfl⟩ : syracuseStep 2823929 = 2117947) B2117947
theorem B20322083 : Blo 834351 20322083 := bstep (se 1 (by rfl) ⟨15241562, by rfl⟩ : syracuseStep 20322083 = 30483125) B30483125
theorem B2824199 : Blo 834351 2824199 := bstep (se 1 (by rfl) ⟨2118149, by rfl⟩ : syracuseStep 2824199 = 4236299) B4236299
theorem B2824307 : Blo 834351 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B1251527 : Blo 834351 1251527 := bstep (se 1 (by rfl) ⟨938645, by rfl⟩ : syracuseStep 1251527 = 1877291) B1877291
theorem B1251689 : Blo 834351 1251689 := bstep (se 2 (by rfl) ⟨469383, by rfl⟩ : syracuseStep 1251689 = 938767) B938767
theorem B2824577 : Blo 834351 2824577 := bstep (se 2 (by rfl) ⟨1059216, by rfl⟩ : syracuseStep 2824577 = 2118433) B2118433
theorem B1251767 : Blo 834351 1251767 := bstep (se 1 (by rfl) ⟨938825, by rfl⟩ : syracuseStep 1251767 = 1877651) B1877651
theorem B6035915 : Blo 834351 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B1251803 : Blo 834351 1251803 := bstep (se 1 (by rfl) ⟨938852, by rfl⟩ : syracuseStep 1251803 = 1877705) B1877705
theorem B3578377 : Blo 834351 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B1252271 : Blo 834351 1252271 := bstep (se 1 (by rfl) ⟨939203, by rfl⟩ : syracuseStep 1252271 = 1878407) B1878407
theorem B1252361 : Blo 834351 1252361 := bstep (se 2 (by rfl) ⟨469635, by rfl⟩ : syracuseStep 1252361 = 939271) B939271
theorem B4758547 : Blo 834351 4758547 := bstep (se 1 (by rfl) ⟨3568910, by rfl⟩ : syracuseStep 4758547 = 7137821) B7137821
theorem B1809427 : Blo 834351 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B1252391 : Blo 834351 1252391 := bstep (se 1 (by rfl) ⟨939293, by rfl⟩ : syracuseStep 1252391 = 1878587) B1878587
theorem B1252475 : Blo 834351 1252475 := bstep (se 1 (by rfl) ⟨939356, by rfl⟩ : syracuseStep 1252475 = 1878713) B1878713
theorem B2825387 : Blo 834351 2825387 := bstep (se 1 (by rfl) ⟨2119040, by rfl⟩ : syracuseStep 2825387 = 4238081) B4238081
theorem B1252601 : Blo 834351 1252601 := bstep (se 2 (by rfl) ⟨469725, by rfl⟩ : syracuseStep 1252601 = 939451) B939451
theorem B1252703 : Blo 834351 1252703 := bstep (se 1 (by rfl) ⟨939527, by rfl⟩ : syracuseStep 1252703 = 1879055) B1879055
theorem B1252715 : Blo 834351 1252715 := bstep (se 1 (by rfl) ⟨939536, by rfl⟩ : syracuseStep 1252715 = 1879073) B1879073
theorem B1252943 : Blo 834351 1252943 := bstep (se 1 (by rfl) ⟨939707, by rfl⟩ : syracuseStep 1252943 = 1879415) B1879415
theorem B9510533 : Blo 834351 9510533 := bstep (se 4 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 9510533 = 1783225) B1783225
theorem B1253063 : Blo 834351 1253063 := bstep (se 1 (by rfl) ⟨939797, by rfl⟩ : syracuseStep 1253063 = 1879595) B1879595
theorem B2825927 : Blo 834351 2825927 := bstep (se 1 (by rfl) ⟨2119445, by rfl⟩ : syracuseStep 2825927 = 4238891) B4238891
theorem B1253225 : Blo 834351 1253225 := bstep (se 2 (by rfl) ⟨469959, by rfl⟩ : syracuseStep 1253225 = 939919) B939919
theorem B1253303 : Blo 834351 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B1253339 : Blo 834351 1253339 := bstep (se 1 (by rfl) ⟨940004, by rfl⟩ : syracuseStep 1253339 = 1880009) B1880009
theorem B1745107 : Blo 834351 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B1253807 : Blo 834351 1253807 := bstep (se 1 (by rfl) ⟨940355, by rfl⟩ : syracuseStep 1253807 = 1880711) B1880711
theorem B1057207 : Blo 834351 1057207 := bstep (se 1 (by rfl) ⟨792905, by rfl⟩ : syracuseStep 1057207 = 1585811) B1585811
theorem B1188361 : Blo 834351 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B1253897 : Blo 834351 1253897 := bstep (se 2 (by rfl) ⟨470211, by rfl⟩ : syracuseStep 1253897 = 940423) B940423
theorem B3809825 : Blo 834351 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B1253927 : Blo 834351 1253927 := bstep (se 1 (by rfl) ⟨940445, by rfl⟩ : syracuseStep 1253927 = 1880891) B1880891
theorem B2826791 : Blo 834351 2826791 := bstep (se 1 (by rfl) ⟨2120093, by rfl⟩ : syracuseStep 2826791 = 4240187) B4240187
theorem B1254011 : Blo 834351 1254011 := bstep (se 1 (by rfl) ⟨940508, by rfl⟩ : syracuseStep 1254011 = 1881017) B1881017
theorem B2826899 : Blo 834351 2826899 := bstep (se 1 (by rfl) ⟨2120174, by rfl⟩ : syracuseStep 2826899 = 4240349) B4240349
theorem B6038225 : Blo 834351 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B1254137 : Blo 834351 1254137 := bstep (se 2 (by rfl) ⟨470301, by rfl⟩ : syracuseStep 1254137 = 940603) B940603
theorem B1188703 : Blo 834351 1188703 := bstep (se 1 (by rfl) ⟨891527, by rfl⟩ : syracuseStep 1188703 = 1783055) B1783055
theorem B1254239 : Blo 834351 1254239 := bstep (se 1 (by rfl) ⟨940679, by rfl⟩ : syracuseStep 1254239 = 1881359) B1881359
theorem B1254251 : Blo 834351 1254251 := bstep (se 1 (by rfl) ⟨940688, by rfl⟩ : syracuseStep 1254251 = 1881377) B1881377
theorem B2827115 : Blo 834351 2827115 := bstep (se 1 (by rfl) ⟨2120336, by rfl⟩ : syracuseStep 2827115 = 4240673) B4240673
theorem B2827169 : Blo 834351 2827169 := bstep (se 2 (by rfl) ⟨1060188, by rfl⟩ : syracuseStep 2827169 = 2120377) B2120377
theorem B1254479 : Blo 834351 1254479 := bstep (se 1 (by rfl) ⟨940859, by rfl⟩ : syracuseStep 1254479 = 1881719) B1881719
theorem B1254599 : Blo 834351 1254599 := bstep (se 1 (by rfl) ⟨940949, by rfl⟩ : syracuseStep 1254599 = 1881899) B1881899
theorem B4302071 : Blo 834351 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B1254761 : Blo 834351 1254761 := bstep (se 2 (by rfl) ⟨470535, by rfl⟩ : syracuseStep 1254761 = 941071) B941071
theorem B1254839 : Blo 834351 1254839 := bstep (se 1 (by rfl) ⟨941129, by rfl⟩ : syracuseStep 1254839 = 1882259) B1882259
theorem B1254875 : Blo 834351 1254875 := bstep (se 1 (by rfl) ⟨941156, by rfl⟩ : syracuseStep 1254875 = 1882313) B1882313
theorem B2827763 : Blo 834351 2827763 := bstep (se 1 (by rfl) ⟨2120822, by rfl⟩ : syracuseStep 2827763 = 4241645) B4241645
theorem B8037893 : Blo 834351 8037893 := bstep (se 4 (by rfl) ⟨753552, by rfl⟩ : syracuseStep 8037893 = 1507105) B1507105
theorem B1877543 : Blo 834351 1877543 := bstep (se 1 (by rfl) ⟨1408157, by rfl⟩ : syracuseStep 1877543 = 2816315) B2816315
theorem B4236947 : Blo 834351 4236947 := bstep (se 1 (by rfl) ⟨3177710, by rfl⟩ : syracuseStep 4236947 = 6355421) B6355421
theorem B1058503 : Blo 834351 1058503 := bstep (se 1 (by rfl) ⟨793877, by rfl⟩ : syracuseStep 1058503 = 1587755) B1587755
theorem B1877867 : Blo 834351 1877867 := bstep (se 1 (by rfl) ⟨1408400, by rfl⟩ : syracuseStep 1877867 = 2816801) B2816801
theorem B4761463 : Blo 834351 4761463 := bstep (se 1 (by rfl) ⟨3571097, by rfl⟩ : syracuseStep 4761463 = 7142195) B7142195
theorem B1877921 : Blo 834351 1877921 := bstep (se 2 (by rfl) ⟨704220, by rfl⟩ : syracuseStep 1877921 = 1408441) B1408441
theorem B1255343 : Blo 834351 1255343 := bstep (se 1 (by rfl) ⟨941507, by rfl⟩ : syracuseStep 1255343 = 1883015) B1883015
theorem B1255433 : Blo 834351 1255433 := bstep (se 2 (by rfl) ⟨470787, by rfl⟩ : syracuseStep 1255433 = 941575) B941575
theorem B2828303 : Blo 834351 2828303 := bstep (se 1 (by rfl) ⟨2121227, by rfl⟩ : syracuseStep 2828303 = 4242455) B4242455
theorem B1255463 : Blo 834351 1255463 := bstep (se 1 (by rfl) ⟨941597, by rfl⟩ : syracuseStep 1255463 = 1883195) B1883195
theorem B1255547 : Blo 834351 1255547 := bstep (se 1 (by rfl) ⟨941660, by rfl⟩ : syracuseStep 1255547 = 1883321) B1883321
theorem B1878263 : Blo 834351 1878263 := bstep (se 1 (by rfl) ⟨1408697, by rfl⟩ : syracuseStep 1878263 = 2817395) B2817395
theorem B1255673 : Blo 834351 1255673 := bstep (se 2 (by rfl) ⟨470877, by rfl⟩ : syracuseStep 1255673 = 941755) B941755
theorem B18065713 : Blo 834351 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B1255775 : Blo 834351 1255775 := bstep (se 1 (by rfl) ⟨941831, by rfl⟩ : syracuseStep 1255775 = 1883663) B1883663
theorem B1255787 : Blo 834351 1255787 := bstep (se 1 (by rfl) ⟨941840, by rfl⟩ : syracuseStep 1255787 = 1883681) B1883681
theorem B1059247 : Blo 834351 1059247 := bstep (se 1 (by rfl) ⟨794435, by rfl⟩ : syracuseStep 1059247 = 1588871) B1588871
theorem B1256015 : Blo 834351 1256015 := bstep (se 1 (by rfl) ⟨942011, by rfl⟩ : syracuseStep 1256015 = 1884023) B1884023
theorem B2828897 : Blo 834351 2828897 := bstep (se 2 (by rfl) ⟨1060836, by rfl⟩ : syracuseStep 2828897 = 2121673) B2121673
theorem B8039047 : Blo 834351 8039047 := bstep (se 1 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 8039047 = 12058571) B12058571
theorem B1256135 : Blo 834351 1256135 := bstep (se 1 (by rfl) ⟨942101, by rfl⟩ : syracuseStep 1256135 = 1884203) B1884203
theorem B1878857 : Blo 834351 1878857 := bstep (se 2 (by rfl) ⟨704571, by rfl⟩ : syracuseStep 1878857 = 1409143) B1409143
theorem B1256297 : Blo 834351 1256297 := bstep (se 2 (by rfl) ⟨471111, by rfl⟩ : syracuseStep 1256297 = 942223) B942223
theorem B1256375 : Blo 834351 1256375 := bstep (se 1 (by rfl) ⟨942281, by rfl⟩ : syracuseStep 1256375 = 1884563) B1884563
theorem B1256411 : Blo 834351 1256411 := bstep (se 1 (by rfl) ⟨942308, by rfl⟩ : syracuseStep 1256411 = 1884617) B1884617
theorem B1584299 : Blo 834351 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B20655395 : Blo 834351 20655395 := bstep (se 1 (by rfl) ⟨15491546, by rfl⟩ : syracuseStep 20655395 = 30983093) B30983093
theorem B2010511 : Blo 834351 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B1256879 : Blo 834351 1256879 := bstep (se 1 (by rfl) ⟨942659, by rfl⟩ : syracuseStep 1256879 = 1885319) B1885319
theorem B1256969 : Blo 834351 1256969 := bstep (se 2 (by rfl) ⟨471363, by rfl⟩ : syracuseStep 1256969 = 942727) B942727
theorem B1584679 : Blo 834351 1584679 := bstep (se 1 (by rfl) ⟨1188509, by rfl⟩ : syracuseStep 1584679 = 2377019) B2377019
theorem B1060391 : Blo 834351 1060391 := bstep (se 1 (by rfl) ⟨795293, by rfl⟩ : syracuseStep 1060391 = 1590587) B1590587
theorem B1256999 : Blo 834351 1256999 := bstep (se 1 (by rfl) ⟨942749, by rfl⟩ : syracuseStep 1256999 = 1885499) B1885499
theorem B1879649 : Blo 834351 1879649 := bstep (se 2 (by rfl) ⟨704868, by rfl⟩ : syracuseStep 1879649 = 1409737) B1409737
theorem B1257083 : Blo 834351 1257083 := bstep (se 1 (by rfl) ⟨942812, by rfl⟩ : syracuseStep 1257083 = 1885625) B1885625
theorem B1584839 : Blo 834351 1584839 := bstep (se 1 (by rfl) ⟨1188629, by rfl⟩ : syracuseStep 1584839 = 2377259) B2377259
theorem B1257209 : Blo 834351 1257209 := bstep (se 2 (by rfl) ⟨471453, by rfl⟩ : syracuseStep 1257209 = 942907) B942907
theorem B1257311 : Blo 834351 1257311 := bstep (se 1 (by rfl) ⟨942983, by rfl⟩ : syracuseStep 1257311 = 1885967) B1885967
theorem B1060715 : Blo 834351 1060715 := bstep (se 1 (by rfl) ⟨795536, by rfl⟩ : syracuseStep 1060715 = 1591073) B1591073
theorem B1257323 : Blo 834351 1257323 := bstep (se 1 (by rfl) ⟨942992, by rfl⟩ : syracuseStep 1257323 = 1885985) B1885985
theorem B1879991 : Blo 834351 1879991 := bstep (se 1 (by rfl) ⟨1409993, by rfl⟩ : syracuseStep 1879991 = 2819987) B2819987
theorem B3616775 : Blo 834351 3616775 := bstep (se 1 (by rfl) ⟨2712581, by rfl⟩ : syracuseStep 3616775 = 5425163) B5425163
theorem B2142227 : Blo 834351 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B8040779 : Blo 834351 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B1192411 : Blo 834351 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B1880585 : Blo 834351 1880585 := bstep (se 2 (by rfl) ⟨705219, by rfl⟩ : syracuseStep 1880585 = 1410439) B1410439
theorem B3486347 : Blo 834351 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B6861485 : Blo 834351 6861485 := bstep (se 3 (by rfl) ⟨1286528, by rfl⟩ : syracuseStep 6861485 = 2573057) B2573057
theorem B1585993 : Blo 834351 1585993 := bstep (se 2 (by rfl) ⟨594747, by rfl⟩ : syracuseStep 1585993 = 1189495) B1189495
theorem B1880927 : Blo 834351 1880927 := bstep (se 1 (by rfl) ⟨1410695, by rfl⟩ : syracuseStep 1880927 = 2821391) B2821391
theorem B1881107 : Blo 834351 1881107 := bstep (se 1 (by rfl) ⟨1410830, by rfl⟩ : syracuseStep 1881107 = 2821661) B2821661
theorem B10171595 : Blo 834351 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B1881449 : Blo 834351 1881449 := bstep (se 2 (by rfl) ⟨705543, by rfl⟩ : syracuseStep 1881449 = 1411087) B1411087
theorem B1357511 : Blo 834351 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B1882043 : Blo 834351 1882043 := bstep (se 1 (by rfl) ⟨1411532, by rfl⟩ : syracuseStep 1882043 = 2823065) B2823065
theorem B1128487 : Blo 834351 1128487 := bstep (se 1 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 1128487 = 1692731) B1692731
theorem B1882169 : Blo 834351 1882169 := bstep (se 2 (by rfl) ⟨705813, by rfl⟩ : syracuseStep 1882169 = 1411627) B1411627
theorem B5355827 : Blo 834351 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B6437207 : Blo 834351 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B5355881 : Blo 834351 5355881 := bstep (se 2 (by rfl) ⟨2008455, by rfl⟩ : syracuseStep 5355881 = 4016911) B4016911
theorem B1882511 : Blo 834351 1882511 := bstep (se 1 (by rfl) ⟨1411883, by rfl⟩ : syracuseStep 1882511 = 2823767) B2823767
theorem B1882835 : Blo 834351 1882835 := bstep (se 1 (by rfl) ⟨1412126, by rfl⟩ : syracuseStep 1882835 = 2824253) B2824253
theorem B4242131 : Blo 834351 4242131 := bstep (se 1 (by rfl) ⟨3181598, by rfl⟩ : syracuseStep 4242131 = 6363197) B6363197
theorem B834383 : Blo 834351 834383 := bstep (se 1 (by rfl) ⟨625787, by rfl⟩ : syracuseStep 834383 = 1251575) B1251575
theorem B834399 : Blo 834351 834399 := bstep (se 1 (by rfl) ⟨625799, by rfl⟩ : syracuseStep 834399 = 1251599) B1251599
theorem B834427 : Blo 834351 834427 := bstep (se 1 (by rfl) ⟨625820, by rfl⟩ : syracuseStep 834427 = 1251641) B1251641
theorem B834479 : Blo 834351 834479 := bstep (se 1 (by rfl) ⟨625859, by rfl⟩ : syracuseStep 834479 = 1251719) B1251719
theorem B2112439 : Blo 834351 2112439 := bstep (se 1 (by rfl) ⟨1584329, by rfl⟩ : syracuseStep 2112439 = 3168659) B3168659
theorem B834503 : Blo 834351 834503 := bstep (se 1 (by rfl) ⟨625877, by rfl⟩ : syracuseStep 834503 = 1251755) B1251755
theorem B834523 : Blo 834351 834523 := bstep (se 1 (by rfl) ⟨625892, by rfl⟩ : syracuseStep 834523 = 1251785) B1251785
theorem B1588187 : Blo 834351 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B834599 : Blo 834351 834599 := bstep (se 1 (by rfl) ⟨625949, by rfl⟩ : syracuseStep 834599 = 1251899) B1251899
theorem B834639 : Blo 834351 834639 := bstep (se 1 (by rfl) ⟨625979, by rfl⟩ : syracuseStep 834639 = 1251959) B1251959
theorem B834655 : Blo 834351 834655 := bstep (se 1 (by rfl) ⟨625991, by rfl⟩ : syracuseStep 834655 = 1251983) B1251983
theorem B834683 : Blo 834351 834683 := bstep (se 1 (by rfl) ⟨626012, by rfl⟩ : syracuseStep 834683 = 1252025) B1252025
theorem B834735 : Blo 834351 834735 := bstep (se 1 (by rfl) ⟨626051, by rfl⟩ : syracuseStep 834735 = 1252103) B1252103
theorem B834759 : Blo 834351 834759 := bstep (se 1 (by rfl) ⟨626069, by rfl⟩ : syracuseStep 834759 = 1252139) B1252139
theorem B1588423 : Blo 834351 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B834779 : Blo 834351 834779 := bstep (se 1 (by rfl) ⟨626084, by rfl⟩ : syracuseStep 834779 = 1252169) B1252169
theorem B834855 : Blo 834351 834855 := bstep (se 1 (by rfl) ⟨626141, by rfl⟩ : syracuseStep 834855 = 1252283) B1252283
theorem B834895 : Blo 834351 834895 := bstep (se 1 (by rfl) ⟨626171, by rfl⟩ : syracuseStep 834895 = 1252343) B1252343
theorem B21708121 : Blo 834351 21708121 := bstep (se 2 (by rfl) ⟨8140545, by rfl⟩ : syracuseStep 21708121 = 16281091) B16281091
theorem B834911 : Blo 834351 834911 := bstep (se 1 (by rfl) ⟨626183, by rfl⟩ : syracuseStep 834911 = 1252367) B1252367
theorem B834939 : Blo 834351 834939 := bstep (se 1 (by rfl) ⟨626204, by rfl⟩ : syracuseStep 834939 = 1252409) B1252409
theorem B834991 : Blo 834351 834991 := bstep (se 1 (by rfl) ⟨626243, by rfl⟩ : syracuseStep 834991 = 1252487) B1252487
theorem B835015 : Blo 834351 835015 := bstep (se 1 (by rfl) ⟨626261, by rfl⟩ : syracuseStep 835015 = 1252523) B1252523
theorem B835035 : Blo 834351 835035 := bstep (se 1 (by rfl) ⟨626276, by rfl⟩ : syracuseStep 835035 = 1252553) B1252553
theorem B835111 : Blo 834351 835111 := bstep (se 1 (by rfl) ⟨626333, by rfl⟩ : syracuseStep 835111 = 1252667) B1252667
theorem B835151 : Blo 834351 835151 := bstep (se 1 (by rfl) ⟨626363, by rfl⟩ : syracuseStep 835151 = 1252727) B1252727
theorem B835167 : Blo 834351 835167 := bstep (se 1 (by rfl) ⟨626375, by rfl⟩ : syracuseStep 835167 = 1252751) B1252751
theorem B835195 : Blo 834351 835195 := bstep (se 1 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 835195 = 1252793) B1252793
theorem B1883771 : Blo 834351 1883771 := bstep (se 1 (by rfl) ⟨1412828, by rfl⟩ : syracuseStep 1883771 = 2825657) B2825657
theorem B7618187 : Blo 834351 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B835247 : Blo 834351 835247 := bstep (se 1 (by rfl) ⟨626435, by rfl⟩ : syracuseStep 835247 = 1252871) B1252871
theorem B835271 : Blo 834351 835271 := bstep (se 1 (by rfl) ⟨626453, by rfl⟩ : syracuseStep 835271 = 1252907) B1252907
theorem B835291 : Blo 834351 835291 := bstep (se 1 (by rfl) ⟨626468, by rfl⟩ : syracuseStep 835291 = 1252937) B1252937
theorem B1883897 : Blo 834351 1883897 := bstep (se 2 (by rfl) ⟨706461, by rfl⟩ : syracuseStep 1883897 = 1412923) B1412923
theorem B6438689 : Blo 834351 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B835367 : Blo 834351 835367 := bstep (se 1 (by rfl) ⟨626525, by rfl⟩ : syracuseStep 835367 = 1253051) B1253051
theorem B5881643 : Blo 834351 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B835407 : Blo 834351 835407 := bstep (se 1 (by rfl) ⟨626555, by rfl⟩ : syracuseStep 835407 = 1253111) B1253111
theorem B835423 : Blo 834351 835423 := bstep (se 1 (by rfl) ⟨626567, by rfl⟩ : syracuseStep 835423 = 1253135) B1253135
theorem B835451 : Blo 834351 835451 := bstep (se 1 (by rfl) ⟨626588, by rfl⟩ : syracuseStep 835451 = 1253177) B1253177
theorem B835503 : Blo 834351 835503 := bstep (se 1 (by rfl) ⟨626627, by rfl⟩ : syracuseStep 835503 = 1253255) B1253255
theorem B835527 : Blo 834351 835527 := bstep (se 1 (by rfl) ⟨626645, by rfl⟩ : syracuseStep 835527 = 1253291) B1253291
theorem B835547 : Blo 834351 835547 := bstep (se 1 (by rfl) ⟨626660, by rfl⟩ : syracuseStep 835547 = 1253321) B1253321
theorem B1884167 : Blo 834351 1884167 := bstep (se 1 (by rfl) ⟨1413125, by rfl⟩ : syracuseStep 1884167 = 2826251) B2826251
theorem B835623 : Blo 834351 835623 := bstep (se 1 (by rfl) ⟨626717, by rfl⟩ : syracuseStep 835623 = 1253435) B1253435
theorem B835663 : Blo 834351 835663 := bstep (se 1 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 835663 = 1253495) B1253495
theorem B1884239 : Blo 834351 1884239 := bstep (se 1 (by rfl) ⟨1413179, by rfl⟩ : syracuseStep 1884239 = 2826359) B2826359
theorem B835679 : Blo 834351 835679 := bstep (se 1 (by rfl) ⟨626759, by rfl⟩ : syracuseStep 835679 = 1253519) B1253519
theorem B835707 : Blo 834351 835707 := bstep (se 1 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 835707 = 1253561) B1253561
theorem B835759 : Blo 834351 835759 := bstep (se 1 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 835759 = 1253639) B1253639
theorem B9519281 : Blo 834351 9519281 := bstep (se 2 (by rfl) ⟨3569730, by rfl⟩ : syracuseStep 9519281 = 7139461) B7139461
theorem B835783 : Blo 834351 835783 := bstep (se 1 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 835783 = 1253675) B1253675
theorem B835803 : Blo 834351 835803 := bstep (se 1 (by rfl) ⟨626852, by rfl⟩ : syracuseStep 835803 = 1253705) B1253705
theorem B835879 : Blo 834351 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B10731851 : Blo 834351 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B835919 : Blo 834351 835919 := bstep (se 1 (by rfl) ⟨626939, by rfl⟩ : syracuseStep 835919 = 1253879) B1253879
theorem B835935 : Blo 834351 835935 := bstep (se 1 (by rfl) ⟨626951, by rfl⟩ : syracuseStep 835935 = 1253903) B1253903
theorem B2113897 : Blo 834351 2113897 := bstep (se 2 (by rfl) ⟨792711, by rfl⟩ : syracuseStep 2113897 = 1585423) B1585423
theorem B835963 : Blo 834351 835963 := bstep (se 1 (by rfl) ⟨626972, by rfl⟩ : syracuseStep 835963 = 1253945) B1253945
theorem B836015 : Blo 834351 836015 := bstep (se 1 (by rfl) ⟨627011, by rfl⟩ : syracuseStep 836015 = 1254023) B1254023
theorem B836039 : Blo 834351 836039 := bstep (se 1 (by rfl) ⟨627029, by rfl⟩ : syracuseStep 836039 = 1254059) B1254059
theorem B836059 : Blo 834351 836059 := bstep (se 1 (by rfl) ⟨627044, by rfl⟩ : syracuseStep 836059 = 1254089) B1254089
theorem B1884635 : Blo 834351 1884635 := bstep (se 1 (by rfl) ⟨1413476, by rfl⟩ : syracuseStep 1884635 = 2826953) B2826953
theorem B836135 : Blo 834351 836135 := bstep (se 1 (by rfl) ⟨627101, by rfl⟩ : syracuseStep 836135 = 1254203) B1254203
theorem B836175 : Blo 834351 836175 := bstep (se 1 (by rfl) ⟨627131, by rfl⟩ : syracuseStep 836175 = 1254263) B1254263
theorem B836191 : Blo 834351 836191 := bstep (se 1 (by rfl) ⟨627143, by rfl⟩ : syracuseStep 836191 = 1254287) B1254287
theorem B2114171 : Blo 834351 2114171 := bstep (se 1 (by rfl) ⟨1585628, by rfl⟩ : syracuseStep 2114171 = 3171257) B3171257
theorem B836219 : Blo 834351 836219 := bstep (se 1 (by rfl) ⟨627164, by rfl⟩ : syracuseStep 836219 = 1254329) B1254329
theorem B836271 : Blo 834351 836271 := bstep (se 1 (by rfl) ⟨627203, by rfl⟩ : syracuseStep 836271 = 1254407) B1254407
theorem B836295 : Blo 834351 836295 := bstep (se 1 (by rfl) ⟨627221, by rfl⟩ : syracuseStep 836295 = 1254443) B1254443
theorem B836315 : Blo 834351 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B836391 : Blo 834351 836391 := bstep (se 1 (by rfl) ⟨627293, by rfl⟩ : syracuseStep 836391 = 1254587) B1254587
theorem B836431 : Blo 834351 836431 := bstep (se 1 (by rfl) ⟨627323, by rfl⟩ : syracuseStep 836431 = 1254647) B1254647
theorem B836447 : Blo 834351 836447 := bstep (se 1 (by rfl) ⟨627335, by rfl⟩ : syracuseStep 836447 = 1254671) B1254671
theorem B836475 : Blo 834351 836475 := bstep (se 1 (by rfl) ⟨627356, by rfl⟩ : syracuseStep 836475 = 1254713) B1254713
theorem B836527 : Blo 834351 836527 := bstep (se 1 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 836527 = 1254791) B1254791
theorem B1885103 : Blo 834351 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B2376631 : Blo 834351 2376631 := bstep (se 1 (by rfl) ⟨1782473, by rfl⟩ : syracuseStep 2376631 = 3564947) B3564947
theorem B836551 : Blo 834351 836551 := bstep (se 1 (by rfl) ⟨627413, by rfl⟩ : syracuseStep 836551 = 1254827) B1254827
theorem B836571 : Blo 834351 836571 := bstep (se 1 (by rfl) ⟨627428, by rfl⟩ : syracuseStep 836571 = 1254857) B1254857
theorem B10175489 : Blo 834351 10175489 := bstep (se 2 (by rfl) ⟨3815808, by rfl⟩ : syracuseStep 10175489 = 7631617) B7631617
theorem B3392513 : Blo 834351 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B836647 : Blo 834351 836647 := bstep (se 1 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 836647 = 1254971) B1254971
theorem B1590329 : Blo 834351 1590329 := bstep (se 2 (by rfl) ⟨596373, by rfl⟩ : syracuseStep 1590329 = 1192747) B1192747
theorem B836687 : Blo 834351 836687 := bstep (se 1 (by rfl) ⟨627515, by rfl⟩ : syracuseStep 836687 = 1255031) B1255031
theorem B836703 : Blo 834351 836703 := bstep (se 1 (by rfl) ⟨627527, by rfl⟩ : syracuseStep 836703 = 1255055) B1255055
theorem B836731 : Blo 834351 836731 := bstep (se 1 (by rfl) ⟨627548, by rfl⟩ : syracuseStep 836731 = 1255097) B1255097
theorem B1885355 : Blo 834351 1885355 := bstep (se 1 (by rfl) ⟨1414016, by rfl⟩ : syracuseStep 1885355 = 2828033) B2828033
theorem B836783 : Blo 834351 836783 := bstep (se 1 (by rfl) ⟨627587, by rfl⟩ : syracuseStep 836783 = 1255175) B1255175
theorem B836807 : Blo 834351 836807 := bstep (se 1 (by rfl) ⟨627605, by rfl⟩ : syracuseStep 836807 = 1255211) B1255211
theorem B836827 : Blo 834351 836827 := bstep (se 1 (by rfl) ⟨627620, by rfl⟩ : syracuseStep 836827 = 1255241) B1255241
theorem B836903 : Blo 834351 836903 := bstep (se 1 (by rfl) ⟨627677, by rfl⟩ : syracuseStep 836903 = 1255355) B1255355
theorem B836943 : Blo 834351 836943 := bstep (se 1 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 836943 = 1255415) B1255415
theorem B836959 : Blo 834351 836959 := bstep (se 1 (by rfl) ⟨627719, by rfl⟩ : syracuseStep 836959 = 1255439) B1255439
theorem B836987 : Blo 834351 836987 := bstep (se 1 (by rfl) ⟨627740, by rfl⟩ : syracuseStep 836987 = 1255481) B1255481
theorem B1590671 : Blo 834351 1590671 := bstep (se 1 (by rfl) ⟨1193003, by rfl⟩ : syracuseStep 1590671 = 2386007) B2386007
theorem B837039 : Blo 834351 837039 := bstep (se 1 (by rfl) ⟨627779, by rfl⟩ : syracuseStep 837039 = 1255559) B1255559
theorem B837063 : Blo 834351 837063 := bstep (se 1 (by rfl) ⟨627797, by rfl⟩ : syracuseStep 837063 = 1255595) B1255595
theorem B837083 : Blo 834351 837083 := bstep (se 1 (by rfl) ⟨627812, by rfl⟩ : syracuseStep 837083 = 1255625) B1255625
theorem B837159 : Blo 834351 837159 := bstep (se 1 (by rfl) ⟨627869, by rfl⟩ : syracuseStep 837159 = 1255739) B1255739
theorem B837199 : Blo 834351 837199 := bstep (se 1 (by rfl) ⟨627899, by rfl⟩ : syracuseStep 837199 = 1255799) B1255799
theorem B837215 : Blo 834351 837215 := bstep (se 1 (by rfl) ⟨627911, by rfl⟩ : syracuseStep 837215 = 1255823) B1255823
theorem B837243 : Blo 834351 837243 := bstep (se 1 (by rfl) ⟨627932, by rfl⟩ : syracuseStep 837243 = 1255865) B1255865
theorem B837295 : Blo 834351 837295 := bstep (se 1 (by rfl) ⟨627971, by rfl⟩ : syracuseStep 837295 = 1255943) B1255943
theorem B837319 : Blo 834351 837319 := bstep (se 1 (by rfl) ⟨627989, by rfl⟩ : syracuseStep 837319 = 1255979) B1255979
theorem B1885895 : Blo 834351 1885895 := bstep (se 1 (by rfl) ⟨1414421, by rfl⟩ : syracuseStep 1885895 = 2828843) B2828843
theorem B837339 : Blo 834351 837339 := bstep (se 1 (by rfl) ⟨628004, by rfl⟩ : syracuseStep 837339 = 1256009) B1256009
theorem B837415 : Blo 834351 837415 := bstep (se 1 (by rfl) ⟨628061, by rfl⟩ : syracuseStep 837415 = 1256123) B1256123
theorem B837455 : Blo 834351 837455 := bstep (se 1 (by rfl) ⟨628091, by rfl⟩ : syracuseStep 837455 = 1256183) B1256183
theorem B837471 : Blo 834351 837471 := bstep (se 1 (by rfl) ⟨628103, by rfl⟩ : syracuseStep 837471 = 1256207) B1256207
theorem B837499 : Blo 834351 837499 := bstep (se 1 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 837499 = 1256249) B1256249
theorem B837551 : Blo 834351 837551 := bstep (se 1 (by rfl) ⟨628163, by rfl⟩ : syracuseStep 837551 = 1256327) B1256327
theorem B837575 : Blo 834351 837575 := bstep (se 1 (by rfl) ⟨628181, by rfl⟩ : syracuseStep 837575 = 1256363) B1256363
theorem B837595 : Blo 834351 837595 := bstep (se 1 (by rfl) ⟨628196, by rfl⟩ : syracuseStep 837595 = 1256393) B1256393
theorem B837671 : Blo 834351 837671 := bstep (se 1 (by rfl) ⟨628253, by rfl⟩ : syracuseStep 837671 = 1256507) B1256507
theorem B837711 : Blo 834351 837711 := bstep (se 1 (by rfl) ⟨628283, by rfl⟩ : syracuseStep 837711 = 1256567) B1256567
theorem B837727 : Blo 834351 837727 := bstep (se 1 (by rfl) ⟨628295, by rfl⟩ : syracuseStep 837727 = 1256591) B1256591
theorem B837755 : Blo 834351 837755 := bstep (se 1 (by rfl) ⟨628316, by rfl⟩ : syracuseStep 837755 = 1256633) B1256633
theorem B837807 : Blo 834351 837807 := bstep (se 1 (by rfl) ⟨628355, by rfl⟩ : syracuseStep 837807 = 1256711) B1256711
theorem B837831 : Blo 834351 837831 := bstep (se 1 (by rfl) ⟨628373, by rfl⟩ : syracuseStep 837831 = 1256747) B1256747
theorem B837851 : Blo 834351 837851 := bstep (se 1 (by rfl) ⟨628388, by rfl⟩ : syracuseStep 837851 = 1256777) B1256777
theorem B837927 : Blo 834351 837927 := bstep (se 1 (by rfl) ⟨628445, by rfl⟩ : syracuseStep 837927 = 1256891) B1256891
theorem B837967 : Blo 834351 837967 := bstep (se 1 (by rfl) ⟨628475, by rfl⟩ : syracuseStep 837967 = 1256951) B1256951
theorem B837983 : Blo 834351 837983 := bstep (se 1 (by rfl) ⟨628487, by rfl⟩ : syracuseStep 837983 = 1256975) B1256975
theorem B2378089 : Blo 834351 2378089 := bstep (se 2 (by rfl) ⟨891783, by rfl⟩ : syracuseStep 2378089 = 1783567) B1783567
theorem B838011 : Blo 834351 838011 := bstep (se 1 (by rfl) ⟨628508, by rfl⟩ : syracuseStep 838011 = 1257017) B1257017
theorem B2115983 : Blo 834351 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B838063 : Blo 834351 838063 := bstep (se 1 (by rfl) ⟨628547, by rfl⟩ : syracuseStep 838063 = 1257095) B1257095
theorem B838087 : Blo 834351 838087 := bstep (se 1 (by rfl) ⟨628565, by rfl⟩ : syracuseStep 838087 = 1257131) B1257131
theorem B838107 : Blo 834351 838107 := bstep (se 1 (by rfl) ⟨628580, by rfl⟩ : syracuseStep 838107 = 1257161) B1257161
theorem B838183 : Blo 834351 838183 := bstep (se 1 (by rfl) ⟨628637, by rfl⟩ : syracuseStep 838183 = 1257275) B1257275
theorem B4016699 : Blo 834351 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B838223 : Blo 834351 838223 := bstep (se 1 (by rfl) ⟨628667, by rfl⟩ : syracuseStep 838223 = 1257335) B1257335
theorem B838239 : Blo 834351 838239 := bstep (se 1 (by rfl) ⟨628679, by rfl⟩ : syracuseStep 838239 = 1257359) B1257359
theorem B838267 : Blo 834351 838267 := bstep (se 1 (by rfl) ⟨628700, by rfl⟩ : syracuseStep 838267 = 1257401) B1257401
theorem B838319 : Blo 834351 838319 := bstep (se 1 (by rfl) ⟨628739, by rfl⟩ : syracuseStep 838319 = 1257479) B1257479
theorem B838343 : Blo 834351 838343 := bstep (se 1 (by rfl) ⟨628757, by rfl⟩ : syracuseStep 838343 = 1257515) B1257515
theorem B2116307 : Blo 834351 2116307 := bstep (se 1 (by rfl) ⟨1587230, by rfl⟩ : syracuseStep 2116307 = 3174461) B3174461
theorem B2378591 : Blo 834351 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B1788779 : Blo 834351 1788779 := bstep (se 1 (by rfl) ⟨1341584, by rfl⟩ : syracuseStep 1788779 = 2683169) B2683169
theorem B2378909 : Blo 834351 2378909 := bstep (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) B892091
theorem B5721283 : Blo 834351 5721283 := bstep (se 1 (by rfl) ⟨4290962, by rfl⟩ : syracuseStep 5721283 = 8581925) B8581925
theorem B18599203 : Blo 834351 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B9653593 : Blo 834351 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B19353005 : Blo 834351 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B3821195 : Blo 834351 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B16305953 : Blo 834351 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B2379593 : Blo 834351 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B12078983 : Blo 834351 12078983 := bstep (se 1 (by rfl) ⟨9059237, by rfl⟩ : syracuseStep 12078983 = 18118475) B18118475
theorem B1790009 : Blo 834351 1790009 := bstep (se 2 (by rfl) ⟨671253, by rfl⟩ : syracuseStep 1790009 = 1342507) B1342507
theorem B6770945 : Blo 834351 6770945 := bstep (se 2 (by rfl) ⟨2539104, by rfl⟩ : syracuseStep 6770945 = 5078209) B5078209
theorem B15257915 : Blo 834351 15257915 := bstep (se 1 (by rfl) ⟨11443436, by rfl⟩ : syracuseStep 15257915 = 22886873) B22886873
theorem B2380175 : Blo 834351 2380175 := bstep (se 1 (by rfl) ⟨1785131, by rfl⟩ : syracuseStep 2380175 = 3570263) B3570263
theorem B21516803 : Blo 834351 21516803 := bstep (se 1 (by rfl) ⟨16137602, by rfl⟩ : syracuseStep 21516803 = 32275205) B32275205
theorem B7131671 : Blo 834351 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B1692217 : Blo 834351 1692217 := bstep (se 2 (by rfl) ⟨634581, by rfl⟩ : syracuseStep 1692217 = 1269163) B1269163
theorem B7328315 : Blo 834351 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B2675339 : Blo 834351 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B938695 : Blo 834351 938695 := bstep (se 1 (by rfl) ⟨704021, by rfl⟩ : syracuseStep 938695 = 1408043) B1408043
theorem B2118575 : Blo 834351 2118575 := bstep (se 1 (by rfl) ⟨1588931, by rfl⟩ : syracuseStep 2118575 = 3177863) B3177863
theorem B6345701 : Blo 834351 6345701 := bstep (se 4 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 6345701 = 1189819) B1189819
theorem B3396761 : Blo 834351 3396761 := bstep (se 2 (by rfl) ⟨1273785, by rfl⟩ : syracuseStep 3396761 = 2547571) B2547571
theorem B4281623 : Blo 834351 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B2119193 : Blo 834351 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B939559 : Blo 834351 939559 := bstep (se 1 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 939559 = 1409339) B1409339
theorem B16307905 : Blo 834351 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B2545481 : Blo 834351 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B2677121 : Blo 834351 2677121 := bstep (se 2 (by rfl) ⟨1003920, by rfl⟩ : syracuseStep 2677121 = 2007841) B2007841
theorem B3168827 : Blo 834351 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B1694287 : Blo 834351 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B4774585 : Blo 834351 4774585 := bstep (se 2 (by rfl) ⟨1790469, by rfl⟩ : syracuseStep 4774585 = 3580939) B3580939
theorem B6511535 : Blo 834351 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B941179 : Blo 834351 941179 := bstep (se 1 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 941179 = 1411769) B1411769
theorem B12082445 : Blo 834351 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B941647 : Blo 834351 941647 := bstep (se 1 (by rfl) ⟨706235, by rfl⟩ : syracuseStep 941647 = 1412471) B1412471
theorem B5725793 : Blo 834351 5725793 := bstep (se 2 (by rfl) ⟨2147172, by rfl⟩ : syracuseStep 5725793 = 4294345) B4294345
theorem B21454469 : Blo 834351 21454469 := bstep (se 4 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 21454469 = 4022713) B4022713
theorem B1695583 : Blo 834351 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B942043 : Blo 834351 942043 := bstep (se 1 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 942043 = 1413065) B1413065
theorem B1433639 : Blo 834351 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B2121785 : Blo 834351 2121785 := bstep (se 2 (by rfl) ⟨795669, by rfl⟩ : syracuseStep 2121785 = 1591339) B1591339
theorem B4514135 : Blo 834351 4514135 := bstep (se 1 (by rfl) ⟨3385601, by rfl⟩ : syracuseStep 4514135 = 6771203) B6771203
theorem B942511 : Blo 834351 942511 := bstep (se 1 (by rfl) ⟨706883, by rfl⟩ : syracuseStep 942511 = 1413767) B1413767
theorem B2384423 : Blo 834351 2384423 := bstep (se 1 (by rfl) ⟨1788317, by rfl⟩ : syracuseStep 2384423 = 3576635) B3576635
theorem B2679581 : Blo 834351 2679581 := bstep (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) B1004843
theorem B942943 : Blo 834351 942943 := bstep (se 1 (by rfl) ⟨707207, by rfl⟩ : syracuseStep 942943 = 1414415) B1414415
theorem B11428715 : Blo 834351 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B4023215 : Blo 834351 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B3171575 : Blo 834351 3171575 := bstep (se 1 (by rfl) ⟨2378681, by rfl⟩ : syracuseStep 3171575 = 4757363) B4757363
theorem B10184051 : Blo 834351 10184051 := bstep (se 1 (by rfl) ⟨7638038, by rfl⟩ : syracuseStep 10184051 = 15276077) B15276077
theorem B162620945 : Blo 834351 162620945 := bstep (se 2 (by rfl) ⟨60982854, by rfl⟩ : syracuseStep 162620945 = 121965709) B121965709
theorem B3565255 : Blo 834351 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B2385607 : Blo 834351 2385607 := bstep (se 1 (by rfl) ⟨1789205, by rfl⟩ : syracuseStep 2385607 = 3578411) B3578411
theorem B8022053 : Blo 834351 8022053 := bstep (se 4 (by rfl) ⟨752067, by rfl⟩ : syracuseStep 8022053 = 1504135) B1504135
theorem B3172547 : Blo 834351 3172547 := bstep (se 1 (by rfl) ⟨2379410, by rfl⟩ : syracuseStep 3172547 = 4758821) B4758821
theorem B10741997 : Blo 834351 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B3173003 : Blo 834351 3173003 := bstep (se 1 (by rfl) ⟨2379752, by rfl⟩ : syracuseStep 3173003 = 4759505) B4759505
theorem B6351533 : Blo 834351 6351533 := bstep (se 3 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 6351533 = 2381825) B2381825
theorem B3173215 : Blo 834351 3173215 := bstep (se 1 (by rfl) ⟨2379911, by rfl⟩ : syracuseStep 3173215 = 4759823) B4759823
theorem B2681707 : Blo 834351 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B5369003 : Blo 834351 5369003 := bstep (se 1 (by rfl) ⟨4026752, by rfl⟩ : syracuseStep 5369003 = 8053505) B8053505
theorem B2387191 : Blo 834351 2387191 := bstep (se 1 (by rfl) ⟨1790393, by rfl⟩ : syracuseStep 2387191 = 3580787) B3580787
theorem B2682553 : Blo 834351 2682553 := bstep (se 2 (by rfl) ⟨1005957, by rfl⟩ : syracuseStep 2682553 = 2011915) B2011915
theorem B3174173 : Blo 834351 3174173 := bstep (se 3 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 3174173 = 1190315) B1190315
theorem B3174187 : Blo 834351 3174187 := bstep (se 1 (by rfl) ⟨2380640, by rfl⟩ : syracuseStep 3174187 = 4761281) B4761281
theorem B847739 : Blo 834351 847739 := bstep (se 1 (by rfl) ⟨635804, by rfl⟩ : syracuseStep 847739 = 1271609) B1271609
theorem B1503631 : Blo 834351 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B1339823 : Blo 834351 1339823 := bstep (se 1 (by rfl) ⟨1004867, by rfl⟩ : syracuseStep 1339823 = 2009735) B2009735
theorem B8155673 : Blo 834351 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B4026905 : Blo 834351 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B3011489 : Blo 834351 3011489 := bstep (se 2 (by rfl) ⟨1129308, by rfl⟩ : syracuseStep 3011489 = 2258617) B2258617
theorem B1340335 : Blo 834351 1340335 := bstep (se 1 (by rfl) ⟨1005251, by rfl⟩ : syracuseStep 1340335 = 2010503) B2010503
theorem B1504187 : Blo 834351 1504187 := bstep (se 1 (by rfl) ⟨1128140, by rfl⟩ : syracuseStep 1504187 = 2256281) B2256281
theorem B2716687 : Blo 834351 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B6353963 : Blo 834351 6353963 := bstep (se 1 (by rfl) ⟨4765472, by rfl⟩ : syracuseStep 6353963 = 9530945) B9530945
theorem B7140419 : Blo 834351 7140419 := bstep (se 1 (by rfl) ⟨5355314, by rfl⟩ : syracuseStep 7140419 = 10710629) B10710629
theorem B12547493 : Blo 834351 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B4224635 : Blo 834351 4224635 := bstep (se 1 (by rfl) ⟨3168476, by rfl⟩ : syracuseStep 4224635 = 6336953) B6336953
theorem B1341289 : Blo 834351 1341289 := bstep (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) B1005967
theorem B2258875 : Blo 834351 2258875 := bstep (se 1 (by rfl) ⟨1694156, by rfl⟩ : syracuseStep 2258875 = 3388313) B3388313
theorem B2816153 : Blo 834351 2816153 := bstep (se 2 (by rfl) ⟨1056057, by rfl⟩ : syracuseStep 2816153 = 2112115) B2112115
theorem B13727981 : Blo 834351 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B4520279 : Blo 834351 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B43514329 : Blo 834351 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B1505801 : Blo 834351 1505801 := bstep (se 2 (by rfl) ⟨564675, by rfl⟩ : syracuseStep 1505801 = 1129351) B1129351
theorem B2685449 : Blo 834351 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B2685629 : Blo 834351 2685629 := bstep (se 3 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 2685629 = 1007111) B1007111
theorem B3177377 : Blo 834351 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B1342391 : Blo 834351 1342391 := bstep (se 1 (by rfl) ⟨1006793, by rfl⟩ : syracuseStep 1342391 = 2013587) B2013587
theorem B1408009 : Blo 834351 1408009 := bstep (se 2 (by rfl) ⟨528003, by rfl⟩ : syracuseStep 1408009 = 1056007) B1056007
theorem B1408171 : Blo 834351 1408171 := bstep (se 1 (by rfl) ⟨1056128, by rfl⟩ : syracuseStep 1408171 = 2112257) B2112257
theorem B2817341 : Blo 834351 2817341 := bstep (se 3 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 2817341 = 1056503) B1056503
theorem B1408475 : Blo 834351 1408475 := bstep (se 1 (by rfl) ⟨1056356, by rfl⟩ : syracuseStep 1408475 = 2112713) B2112713
theorem B3014267 : Blo 834351 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B1408711 : Blo 834351 1408711 := bstep (se 1 (by rfl) ⟨1056533, by rfl⟩ : syracuseStep 1408711 = 2113067) B2113067
theorem B1408873 : Blo 834351 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B3178349 : Blo 834351 3178349 := bstep (se 3 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 3178349 = 1191881) B1191881
theorem B2818259 : Blo 834351 2818259 := bstep (se 1 (by rfl) ⟨2113694, by rfl⟩ : syracuseStep 2818259 = 4227389) B4227389
theorem B1409447 : Blo 834351 1409447 := bstep (se 1 (by rfl) ⟨1057085, by rfl⟩ : syracuseStep 1409447 = 2114171) B2114171
theorem B2818529 : Blo 834351 2818529 := bstep (se 2 (by rfl) ⟨1056948, by rfl⟩ : syracuseStep 2818529 = 2113897) B2113897
theorem B1409609 : Blo 834351 1409609 := bstep (se 2 (by rfl) ⟨528603, by rfl⟩ : syracuseStep 1409609 = 1057207) B1057207
theorem B6783659 : Blo 834351 6783659 := bstep (se 1 (by rfl) ⟨5087744, by rfl⟩ : syracuseStep 6783659 = 10175489) B10175489
theorem B2261675 : Blo 834351 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B9307237 : Blo 834351 9307237 := bstep (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) B1745107
theorem B25691681 : Blo 834351 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B1410655 : Blo 834351 1410655 := bstep (se 1 (by rfl) ⟨1057991, by rfl⟩ : syracuseStep 1410655 = 2115983) B2115983
theorem B2819771 : Blo 834351 2819771 := bstep (se 1 (by rfl) ⟨2114828, by rfl⟩ : syracuseStep 2819771 = 4229657) B4229657
theorem B1410871 : Blo 834351 1410871 := bstep (se 1 (by rfl) ⟨1058153, by rfl⟩ : syracuseStep 1410871 = 2116307) B2116307
theorem B45746369 : Blo 834351 45746369 := bstep (se 2 (by rfl) ⟨17154888, by rfl⟩ : syracuseStep 45746369 = 34309777) B34309777
theorem B6424771 : Blo 834351 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B4753673 : Blo 834351 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B1411337 : Blo 834351 1411337 := bstep (se 2 (by rfl) ⟨529251, by rfl⟩ : syracuseStep 1411337 = 1058503) B1058503
theorem B3180809 : Blo 834351 3180809 := bstep (se 2 (by rfl) ⟨1192803, by rfl⟩ : syracuseStep 3180809 = 2385607) B2385607
theorem B1903379 : Blo 834351 1903379 := bstep (se 1 (by rfl) ⟨1427534, by rfl⟩ : syracuseStep 1903379 = 2855069) B2855069
theorem B4754447 : Blo 834351 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B4885543 : Blo 834351 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B24087617 : Blo 834351 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B4066523 : Blo 834351 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B1412329 : Blo 834351 1412329 := bstep (se 2 (by rfl) ⟨529623, by rfl⟩ : syracuseStep 1412329 = 1059247) B1059247
theorem B1412383 : Blo 834351 1412383 := bstep (se 1 (by rfl) ⟨1059287, by rfl⟩ : syracuseStep 1412383 = 2118575) B2118575
theorem B4230467 : Blo 834351 4230467 := bstep (se 1 (by rfl) ⟨3172850, by rfl⟩ : syracuseStep 4230467 = 6345701) B6345701
theorem B2264507 : Blo 834351 2264507 := bstep (se 1 (by rfl) ⟨1698380, by rfl⟩ : syracuseStep 2264507 = 3396761) B3396761
theorem B10718729 : Blo 834351 10718729 := bstep (se 2 (by rfl) ⟨4019523, by rfl⟩ : syracuseStep 10718729 = 8039047) B8039047
theorem B2854415 : Blo 834351 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B2821715 : Blo 834351 2821715 := bstep (se 1 (by rfl) ⟨2116286, by rfl⟩ : syracuseStep 2821715 = 4232573) B4232573
theorem B1412795 : Blo 834351 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B4230953 : Blo 834351 4230953 := bstep (se 2 (by rfl) ⟨1586607, by rfl⟩ : syracuseStep 4230953 = 3173215) B3173215
theorem B3575609 : Blo 834351 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B3182921 : Blo 834351 3182921 := bstep (se 2 (by rfl) ⟨1193595, by rfl⟩ : syracuseStep 3182921 = 2387191) B2387191
theorem B3576737 : Blo 834351 3576737 := bstep (se 2 (by rfl) ⟨1341276, by rfl⟩ : syracuseStep 3576737 = 2682553) B2682553
theorem B4232249 : Blo 834351 4232249 := bstep (se 2 (by rfl) ⟨1587093, by rfl⟩ : syracuseStep 4232249 = 3174187) B3174187
theorem B1414523 : Blo 834351 1414523 := bstep (se 1 (by rfl) ⟨1060892, by rfl⟩ : syracuseStep 1414523 = 2121785) B2121785
theorem B2004841 : Blo 834351 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B6789367 : Blo 834351 6789367 := bstep (se 1 (by rfl) ⟨5092025, by rfl⟩ : syracuseStep 6789367 = 10184051) B10184051
theorem B1251593 : Blo 834351 1251593 := bstep (se 2 (by rfl) ⟨469347, by rfl⟩ : syracuseStep 1251593 = 938695) B938695
theorem B1251695 : Blo 834351 1251695 := bstep (se 1 (by rfl) ⟨938771, by rfl⟩ : syracuseStep 1251695 = 1877543) B1877543
theorem B2824631 : Blo 834351 2824631 := bstep (se 1 (by rfl) ⟨2118473, by rfl⟩ : syracuseStep 2824631 = 4236947) B4236947
theorem B16095773 : Blo 834351 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B1251911 : Blo 834351 1251911 := bstep (se 1 (by rfl) ⟨938933, by rfl⟩ : syracuseStep 1251911 = 1877867) B1877867
theorem B1251947 : Blo 834351 1251947 := bstep (se 1 (by rfl) ⟨938960, by rfl⟩ : syracuseStep 1251947 = 1877921) B1877921
theorem B5348035 : Blo 834351 5348035 := bstep (se 1 (by rfl) ⟨4011026, by rfl⟩ : syracuseStep 5348035 = 8022053) B8022053
theorem B1252175 : Blo 834351 1252175 := bstep (se 1 (by rfl) ⟨939131, by rfl⟩ : syracuseStep 1252175 = 1878263) B1878263
theorem B99195749 : Blo 834351 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B4234355 : Blo 834351 4234355 := bstep (se 1 (by rfl) ⟨3175766, by rfl⟩ : syracuseStep 4234355 = 6351533) B6351533
theorem B1252571 : Blo 834351 1252571 := bstep (se 1 (by rfl) ⟨939428, by rfl⟩ : syracuseStep 1252571 = 1878857) B1878857
theorem B1252745 : Blo 834351 1252745 := bstep (se 2 (by rfl) ⟨469779, by rfl⟩ : syracuseStep 1252745 = 939559) B939559
theorem B10722725 : Blo 834351 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B3579335 : Blo 834351 3579335 := bstep (se 1 (by rfl) ⟨2684501, by rfl⟩ : syracuseStep 3579335 = 5369003) B5369003
theorem B13770263 : Blo 834351 13770263 := bstep (se 1 (by rfl) ⟨10327697, by rfl⟩ : syracuseStep 13770263 = 20655395) B20655395
theorem B1253099 : Blo 834351 1253099 := bstep (se 1 (by rfl) ⟨939824, by rfl⟩ : syracuseStep 1253099 = 1879649) B1879649
theorem B1056559 : Blo 834351 1056559 := bstep (se 1 (by rfl) ⟨792419, by rfl⟩ : syracuseStep 1056559 = 1584839) B1584839
theorem B3579709 : Blo 834351 3579709 := bstep (se 3 (by rfl) ⟨671195, by rfl⟩ : syracuseStep 3579709 = 1342391) B1342391
theorem B4235165 : Blo 834351 4235165 := bstep (se 3 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 4235165 = 1588187) B1588187
theorem B1253327 : Blo 834351 1253327 := bstep (se 1 (by rfl) ⟨939995, by rfl⟩ : syracuseStep 1253327 = 1879991) B1879991
theorem B893215 : Blo 834351 893215 := bstep (se 1 (by rfl) ⟨669911, by rfl⟩ : syracuseStep 893215 = 1339823) B1339823
theorem B1253723 : Blo 834351 1253723 := bstep (se 1 (by rfl) ⟨940292, by rfl⟩ : syracuseStep 1253723 = 1880585) B1880585
theorem B1253951 : Blo 834351 1253951 := bstep (se 1 (by rfl) ⟨940463, by rfl⟩ : syracuseStep 1253951 = 1880927) B1880927
theorem B2007659 : Blo 834351 2007659 := bstep (se 1 (by rfl) ⟨1505744, by rfl⟩ : syracuseStep 2007659 = 3011489) B3011489
theorem B1254071 : Blo 834351 1254071 := bstep (se 1 (by rfl) ⟨940553, by rfl⟩ : syracuseStep 1254071 = 1881107) B1881107
theorem B4235975 : Blo 834351 4235975 := bstep (se 1 (by rfl) ⟨3176981, by rfl⟩ : syracuseStep 4235975 = 6353963) B6353963
theorem B4760279 : Blo 834351 4760279 := bstep (se 1 (by rfl) ⟨3570209, by rfl⟩ : syracuseStep 4760279 = 7140419) B7140419
theorem B1254299 : Blo 834351 1254299 := bstep (se 1 (by rfl) ⟨940724, by rfl⟩ : syracuseStep 1254299 = 1881449) B1881449
theorem B6366113 : Blo 834351 6366113 := bstep (se 2 (by rfl) ⟨2387292, by rfl⟩ : syracuseStep 6366113 = 4774585) B4774585
theorem B8364995 : Blo 834351 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B1254695 : Blo 834351 1254695 := bstep (se 1 (by rfl) ⟨941021, by rfl⟩ : syracuseStep 1254695 = 1882043) B1882043
theorem B1877345 : Blo 834351 1877345 := bstep (se 2 (by rfl) ⟨704004, by rfl⟩ : syracuseStep 1877345 = 1408009) B1408009
theorem B1254779 : Blo 834351 1254779 := bstep (se 1 (by rfl) ⟨941084, by rfl⟩ : syracuseStep 1254779 = 1882169) B1882169
theorem B1877435 : Blo 834351 1877435 := bstep (se 1 (by rfl) ⟨1408076, by rfl⟩ : syracuseStep 1877435 = 2816153) B2816153
theorem B2827709 : Blo 834351 2827709 := bstep (se 3 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 2827709 = 1060391) B1060391
theorem B9151987 : Blo 834351 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B1254905 : Blo 834351 1254905 := bstep (se 2 (by rfl) ⟨470589, by rfl⟩ : syracuseStep 1254905 = 941179) B941179
theorem B1877561 : Blo 834351 1877561 := bstep (se 2 (by rfl) ⟨704085, by rfl⟩ : syracuseStep 1877561 = 1408171) B1408171
theorem B1255007 : Blo 834351 1255007 := bstep (se 1 (by rfl) ⟨941255, by rfl⟩ : syracuseStep 1255007 = 1882511) B1882511
theorem B8038045 : Blo 834351 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B28944161 : Blo 834351 28944161 := bstep (se 2 (by rfl) ⟨10854060, by rfl⟩ : syracuseStep 28944161 = 21708121) B21708121
theorem B1255223 : Blo 834351 1255223 := bstep (se 1 (by rfl) ⟨941417, by rfl⟩ : syracuseStep 1255223 = 1882835) B1882835
theorem B2828087 : Blo 834351 2828087 := bstep (se 1 (by rfl) ⟨2121065, by rfl⟩ : syracuseStep 2828087 = 4242131) B4242131
theorem B7153541 : Blo 834351 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B1255529 : Blo 834351 1255529 := bstep (se 2 (by rfl) ⟨470823, by rfl⟩ : syracuseStep 1255529 = 941647) B941647
theorem B1878227 : Blo 834351 1878227 := bstep (se 1 (by rfl) ⟨1408670, by rfl⟩ : syracuseStep 1878227 = 2817341) B2817341
theorem B1878281 : Blo 834351 1878281 := bstep (se 2 (by rfl) ⟨704355, by rfl⟩ : syracuseStep 1878281 = 1408711) B1408711
theorem B2828573 : Blo 834351 2828573 := bstep (se 3 (by rfl) ⟨530357, by rfl⟩ : syracuseStep 2828573 = 1060715) B1060715
theorem B1255847 : Blo 834351 1255847 := bstep (se 1 (by rfl) ⟨941885, by rfl⟩ : syracuseStep 1255847 = 1883771) B1883771
theorem B1878497 : Blo 834351 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B1255931 : Blo 834351 1255931 := bstep (se 1 (by rfl) ⟨941948, by rfl⟩ : syracuseStep 1255931 = 1883897) B1883897
theorem B1256057 : Blo 834351 1256057 := bstep (se 2 (by rfl) ⟨471021, by rfl⟩ : syracuseStep 1256057 = 942043) B942043
theorem B1256111 : Blo 834351 1256111 := bstep (se 1 (by rfl) ⟨942083, by rfl⟩ : syracuseStep 1256111 = 1884167) B1884167
theorem B5712605 : Blo 834351 5712605 := bstep (se 3 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 5712605 = 2142227) B2142227
theorem B1256159 : Blo 834351 1256159 := bstep (se 1 (by rfl) ⟨942119, by rfl⟩ : syracuseStep 1256159 = 1884239) B1884239
theorem B1878803 : Blo 834351 1878803 := bstep (se 1 (by rfl) ⟨1409102, by rfl⟩ : syracuseStep 1878803 = 2818205) B2818205
theorem B7154567 : Blo 834351 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B1256423 : Blo 834351 1256423 := bstep (se 1 (by rfl) ⟨942317, by rfl⟩ : syracuseStep 1256423 = 1884635) B1884635
theorem B10726415 : Blo 834351 10726415 := bstep (se 1 (by rfl) ⟨8044811, by rfl⟩ : syracuseStep 10726415 = 16089623) B16089623
theorem B4762739 : Blo 834351 4762739 := bstep (se 1 (by rfl) ⟨3572054, by rfl⟩ : syracuseStep 4762739 = 7144109) B7144109
theorem B1879163 : Blo 834351 1879163 := bstep (se 1 (by rfl) ⟨1409372, by rfl⟩ : syracuseStep 1879163 = 2818745) B2818745
theorem B1256681 : Blo 834351 1256681 := bstep (se 2 (by rfl) ⟨471255, by rfl⟩ : syracuseStep 1256681 = 942511) B942511
theorem B1879289 : Blo 834351 1879289 := bstep (se 2 (by rfl) ⟨704733, by rfl⟩ : syracuseStep 1879289 = 1409467) B1409467
theorem B1256735 : Blo 834351 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B1060219 : Blo 834351 1060219 := bstep (se 1 (by rfl) ⟨795164, by rfl⟩ : syracuseStep 1060219 = 1590329) B1590329
theorem B1879433 : Blo 834351 1879433 := bstep (se 2 (by rfl) ⟨704787, by rfl⟩ : syracuseStep 1879433 = 1409575) B1409575
theorem B4238729 : Blo 834351 4238729 := bstep (se 2 (by rfl) ⟨1589523, by rfl⟩ : syracuseStep 4238729 = 3179047) B3179047
theorem B1256903 : Blo 834351 1256903 := bstep (se 1 (by rfl) ⟨942677, by rfl⟩ : syracuseStep 1256903 = 1885355) B1885355
theorem B1879559 : Blo 834351 1879559 := bstep (se 1 (by rfl) ⟨1409669, by rfl⟩ : syracuseStep 1879559 = 2819339) B2819339
theorem B12037693 : Blo 834351 12037693 := bstep (se 3 (by rfl) ⟨2257067, by rfl⟩ : syracuseStep 12037693 = 4514135) B4514135
theorem B1060447 : Blo 834351 1060447 := bstep (se 1 (by rfl) ⟨795335, by rfl⟩ : syracuseStep 1060447 = 1590671) B1590671
theorem B1879739 : Blo 834351 1879739 := bstep (se 1 (by rfl) ⟨1409804, by rfl⟩ : syracuseStep 1879739 = 2819609) B2819609
theorem B2141959 : Blo 834351 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B1584937 : Blo 834351 1584937 := bstep (se 2 (by rfl) ⟨594351, by rfl⟩ : syracuseStep 1584937 = 1188703) B1188703
theorem B1257257 : Blo 834351 1257257 := bstep (se 2 (by rfl) ⟨471471, by rfl⟩ : syracuseStep 1257257 = 942943) B942943
theorem B1257263 : Blo 834351 1257263 := bstep (se 1 (by rfl) ⟨942947, by rfl⟩ : syracuseStep 1257263 = 1885895) B1885895
theorem B1879865 : Blo 834351 1879865 := bstep (se 2 (by rfl) ⟨704949, by rfl⟩ : syracuseStep 1879865 = 1409899) B1409899
theorem B1880495 : Blo 834351 1880495 := bstep (se 1 (by rfl) ⟨1410371, by rfl⟩ : syracuseStep 1880495 = 2820743) B2820743
theorem B1880531 : Blo 834351 1880531 := bstep (se 1 (by rfl) ⟨1410398, by rfl⟩ : syracuseStep 1880531 = 2820797) B2820797
theorem B1585727 : Blo 834351 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B1880639 : Blo 834351 1880639 := bstep (se 1 (by rfl) ⟨1410479, by rfl⟩ : syracuseStep 1880639 = 2820959) B2820959
theorem B1192519 : Blo 834351 1192519 := bstep (se 1 (by rfl) ⟨894389, by rfl⟩ : syracuseStep 1192519 = 1788779) B1788779
theorem B4240025 : Blo 834351 4240025 := bstep (se 2 (by rfl) ⟨1590009, by rfl⟩ : syracuseStep 4240025 = 3180019) B3180019
theorem B1880747 : Blo 834351 1880747 := bstep (se 1 (by rfl) ⟨1410560, by rfl⟩ : syracuseStep 1880747 = 2821121) B2821121
theorem B2012147 : Blo 834351 2012147 := bstep (se 1 (by rfl) ⟨1509110, by rfl⟩ : syracuseStep 2012147 = 3018221) B3018221
theorem B1881287 : Blo 834351 1881287 := bstep (se 1 (by rfl) ⟨1410965, by rfl⟩ : syracuseStep 1881287 = 2821931) B2821931
theorem B1586395 : Blo 834351 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B1881467 : Blo 834351 1881467 := bstep (se 1 (by rfl) ⟨1411100, by rfl⟩ : syracuseStep 1881467 = 2822201) B2822201
theorem B1193339 : Blo 834351 1193339 := bstep (se 1 (by rfl) ⟨895004, by rfl⟩ : syracuseStep 1193339 = 1790009) B1790009
theorem B6337925 : Blo 834351 6337925 := bstep (se 4 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 6337925 = 1188361) B1188361
theorem B1881593 : Blo 834351 1881593 := bstep (se 2 (by rfl) ⟨705597, by rfl⟩ : syracuseStep 1881593 = 1411195) B1411195
theorem B10171943 : Blo 834351 10171943 := bstep (se 1 (by rfl) ⟨7628957, by rfl⟩ : syracuseStep 10171943 = 15257915) B15257915
theorem B1881683 : Blo 834351 1881683 := bstep (se 1 (by rfl) ⟨1411262, by rfl⟩ : syracuseStep 1881683 = 2822525) B2822525
theorem B1586783 : Blo 834351 1586783 := bstep (se 1 (by rfl) ⟨1190087, by rfl⟩ : syracuseStep 1586783 = 2380175) B2380175
theorem B9025157 : Blo 834351 9025157 := bstep (se 4 (by rfl) ⟨846108, by rfl⟩ : syracuseStep 9025157 = 1692217) B1692217
theorem B1783559 : Blo 834351 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B1881863 : Blo 834351 1881863 := bstep (se 1 (by rfl) ⟨1411397, by rfl⟩ : syracuseStep 1881863 = 2822795) B2822795
theorem B1882475 : Blo 834351 1882475 := bstep (se 1 (by rfl) ⟨1411856, by rfl⟩ : syracuseStep 1882475 = 2823713) B2823713
theorem B4241807 : Blo 834351 4241807 := bstep (se 1 (by rfl) ⟨3181355, by rfl⟩ : syracuseStep 4241807 = 6362711) B6362711
theorem B1882619 : Blo 834351 1882619 := bstep (se 1 (by rfl) ⟨1411964, by rfl⟩ : syracuseStep 1882619 = 2823929) B2823929
theorem B13548055 : Blo 834351 13548055 := bstep (se 1 (by rfl) ⟨10161041, by rfl⟩ : syracuseStep 13548055 = 20322083) B20322083
theorem B1882745 : Blo 834351 1882745 := bstep (se 2 (by rfl) ⟨706029, by rfl⟩ : syracuseStep 1882745 = 1412059) B1412059
theorem B1882799 : Blo 834351 1882799 := bstep (se 1 (by rfl) ⟨1412099, by rfl⟩ : syracuseStep 1882799 = 2824199) B2824199
theorem B1882871 : Blo 834351 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B834351 : Blo 834351 834351 := bstep (se 1 (by rfl) ⟨625763, by rfl⟩ : syracuseStep 834351 = 1251527) B1251527
theorem B834459 : Blo 834351 834459 := bstep (se 1 (by rfl) ⟨625844, by rfl⟩ : syracuseStep 834459 = 1251689) B1251689
theorem B1784747 : Blo 834351 1784747 := bstep (se 1 (by rfl) ⟨1338560, by rfl⟩ : syracuseStep 1784747 = 2677121) B2677121
theorem B1883051 : Blo 834351 1883051 := bstep (se 1 (by rfl) ⟨1412288, by rfl⟩ : syracuseStep 1883051 = 2824577) B2824577
theorem B834511 : Blo 834351 834511 := bstep (se 1 (by rfl) ⟨625883, by rfl⟩ : syracuseStep 834511 = 1251767) B1251767
theorem B834535 : Blo 834351 834535 := bstep (se 1 (by rfl) ⟨625901, by rfl⟩ : syracuseStep 834535 = 1251803) B1251803
theorem B2112551 : Blo 834351 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B4341023 : Blo 834351 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B834847 : Blo 834351 834847 := bstep (se 1 (by rfl) ⟨626135, by rfl⟩ : syracuseStep 834847 = 1252271) B1252271
theorem B834907 : Blo 834351 834907 := bstep (se 1 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 834907 = 1252361) B1252361
theorem B834927 : Blo 834351 834927 := bstep (se 1 (by rfl) ⟨626195, by rfl⟩ : syracuseStep 834927 = 1252391) B1252391
theorem B2112905 : Blo 834351 2112905 := bstep (se 2 (by rfl) ⟨792339, by rfl⟩ : syracuseStep 2112905 = 1584679) B1584679
theorem B4767113 : Blo 834351 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B834983 : Blo 834351 834983 := bstep (se 1 (by rfl) ⟨626237, by rfl⟩ : syracuseStep 834983 = 1252475) B1252475
theorem B1883591 : Blo 834351 1883591 := bstep (se 1 (by rfl) ⟨1412693, by rfl⟩ : syracuseStep 1883591 = 2825387) B2825387
theorem B835067 : Blo 834351 835067 := bstep (se 1 (by rfl) ⟨626300, by rfl⟩ : syracuseStep 835067 = 1252601) B1252601
theorem B835135 : Blo 834351 835135 := bstep (se 1 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 835135 = 1252703) B1252703
theorem B835143 : Blo 834351 835143 := bstep (se 1 (by rfl) ⟨626357, by rfl⟩ : syracuseStep 835143 = 1252715) B1252715
theorem B835295 : Blo 834351 835295 := bstep (se 1 (by rfl) ⟨626471, by rfl⟩ : syracuseStep 835295 = 1252943) B1252943
theorem B3817195 : Blo 834351 3817195 := bstep (se 1 (by rfl) ⟨2862896, by rfl⟩ : syracuseStep 3817195 = 5725793) B5725793
theorem B6340355 : Blo 834351 6340355 := bstep (se 1 (by rfl) ⟨4755266, by rfl⟩ : syracuseStep 6340355 = 9510533) B9510533
theorem B14302979 : Blo 834351 14302979 := bstep (se 1 (by rfl) ⟨10727234, by rfl⟩ : syracuseStep 14302979 = 21454469) B21454469
theorem B835375 : Blo 834351 835375 := bstep (se 1 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 835375 = 1253063) B1253063
theorem B1883951 : Blo 834351 1883951 := bstep (se 1 (by rfl) ⟨1412963, by rfl⟩ : syracuseStep 1883951 = 2825927) B2825927
theorem B835483 : Blo 834351 835483 := bstep (se 1 (by rfl) ⟨626612, by rfl⟩ : syracuseStep 835483 = 1253225) B1253225
theorem B835535 : Blo 834351 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B835559 : Blo 834351 835559 := bstep (se 1 (by rfl) ⟨626669, by rfl⟩ : syracuseStep 835559 = 1253339) B1253339
theorem B2146313 : Blo 834351 2146313 := bstep (se 2 (by rfl) ⟨804867, by rfl⟩ : syracuseStep 2146313 = 1609735) B1609735
theorem B32162021 : Blo 834351 32162021 := bstep (se 4 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 32162021 = 6030379) B6030379
theorem B835871 : Blo 834351 835871 := bstep (se 1 (by rfl) ⟨626903, by rfl⟩ : syracuseStep 835871 = 1253807) B1253807
theorem B835931 : Blo 834351 835931 := bstep (se 1 (by rfl) ⟨626948, by rfl⟩ : syracuseStep 835931 = 1253897) B1253897
theorem B2539883 : Blo 834351 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B835951 : Blo 834351 835951 := bstep (se 1 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 835951 = 1253927) B1253927
theorem B1589615 : Blo 834351 1589615 := bstep (se 1 (by rfl) ⟨1192211, by rfl⟩ : syracuseStep 1589615 = 2384423) B2384423
theorem B1884527 : Blo 834351 1884527 := bstep (se 1 (by rfl) ⟨1413395, by rfl⟩ : syracuseStep 1884527 = 2826791) B2826791
theorem B836007 : Blo 834351 836007 := bstep (se 1 (by rfl) ⟨627005, by rfl⟩ : syracuseStep 836007 = 1254011) B1254011
theorem B1884599 : Blo 834351 1884599 := bstep (se 1 (by rfl) ⟨1413449, by rfl⟩ : syracuseStep 1884599 = 2826899) B2826899
theorem B4243913 : Blo 834351 4243913 := bstep (se 2 (by rfl) ⟨1591467, by rfl⟩ : syracuseStep 4243913 = 3182935) B3182935
theorem B148750805 : Blo 834351 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B836091 : Blo 834351 836091 := bstep (se 1 (by rfl) ⟨627068, by rfl⟩ : syracuseStep 836091 = 1254137) B1254137
theorem B1786387 : Blo 834351 1786387 := bstep (se 1 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 1786387 = 2679581) B2679581
theorem B836159 : Blo 834351 836159 := bstep (se 1 (by rfl) ⟨627119, by rfl⟩ : syracuseStep 836159 = 1254239) B1254239
theorem B7619143 : Blo 834351 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B836167 : Blo 834351 836167 := bstep (se 1 (by rfl) ⟨627125, by rfl⟩ : syracuseStep 836167 = 1254251) B1254251
theorem B1884743 : Blo 834351 1884743 := bstep (se 1 (by rfl) ⟨1413557, by rfl⟩ : syracuseStep 1884743 = 2827115) B2827115
theorem B1884779 : Blo 834351 1884779 := bstep (se 1 (by rfl) ⟨1413584, by rfl⟩ : syracuseStep 1884779 = 2827169) B2827169
theorem B1589881 : Blo 834351 1589881 := bstep (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) B1192411
theorem B836319 : Blo 834351 836319 := bstep (se 1 (by rfl) ⟨627239, by rfl⟩ : syracuseStep 836319 = 1254479) B1254479
theorem B836399 : Blo 834351 836399 := bstep (se 1 (by rfl) ⟨627299, by rfl⟩ : syracuseStep 836399 = 1254599) B1254599
theorem B2114383 : Blo 834351 2114383 := bstep (se 1 (by rfl) ⟨1585787, by rfl⟩ : syracuseStep 2114383 = 3171575) B3171575
theorem B2868047 : Blo 834351 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B836507 : Blo 834351 836507 := bstep (se 1 (by rfl) ⟨627380, by rfl⟩ : syracuseStep 836507 = 1254761) B1254761
theorem B836559 : Blo 834351 836559 := bstep (se 1 (by rfl) ⟨627419, by rfl⟩ : syracuseStep 836559 = 1254839) B1254839
theorem B836583 : Blo 834351 836583 := bstep (se 1 (by rfl) ⟨627437, by rfl⟩ : syracuseStep 836583 = 1254875) B1254875
theorem B1885175 : Blo 834351 1885175 := bstep (se 1 (by rfl) ⟨1413881, by rfl⟩ : syracuseStep 1885175 = 2827763) B2827763
theorem B5358595 : Blo 834351 5358595 := bstep (se 1 (by rfl) ⟨4018946, by rfl⟩ : syracuseStep 5358595 = 8037893) B8037893
theorem B108413963 : Blo 834351 108413963 := bstep (se 1 (by rfl) ⟨81310472, by rfl⟩ : syracuseStep 108413963 = 162620945) B162620945
theorem B2114657 : Blo 834351 2114657 := bstep (se 2 (by rfl) ⟨792996, by rfl⟩ : syracuseStep 2114657 = 1585993) B1585993
theorem B1787113 : Blo 834351 1787113 := bstep (se 2 (by rfl) ⟨670167, by rfl⟩ : syracuseStep 1787113 = 1340335) B1340335
theorem B836895 : Blo 834351 836895 := bstep (se 1 (by rfl) ⟨627671, by rfl⟩ : syracuseStep 836895 = 1255343) B1255343
theorem B836955 : Blo 834351 836955 := bstep (se 1 (by rfl) ⟨627716, by rfl⟩ : syracuseStep 836955 = 1255433) B1255433
theorem B1885535 : Blo 834351 1885535 := bstep (se 1 (by rfl) ⟨1414151, by rfl⟩ : syracuseStep 1885535 = 2828303) B2828303
theorem B3622249 : Blo 834351 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B4015469 : Blo 834351 4015469 := bstep (se 3 (by rfl) ⟨752900, by rfl⟩ : syracuseStep 4015469 = 1505801) B1505801
theorem B836975 : Blo 834351 836975 := bstep (se 1 (by rfl) ⟨627731, by rfl⟩ : syracuseStep 836975 = 1255463) B1255463
theorem B837031 : Blo 834351 837031 := bstep (se 1 (by rfl) ⟨627773, by rfl⟩ : syracuseStep 837031 = 1255547) B1255547
theorem B2115031 : Blo 834351 2115031 := bstep (se 1 (by rfl) ⟨1586273, by rfl⟩ : syracuseStep 2115031 = 3172547) B3172547
theorem B7161331 : Blo 834351 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B837115 : Blo 834351 837115 := bstep (se 1 (by rfl) ⟨627836, by rfl⟩ : syracuseStep 837115 = 1255673) B1255673
theorem B837183 : Blo 834351 837183 := bstep (se 1 (by rfl) ⟨627887, by rfl⟩ : syracuseStep 837183 = 1255775) B1255775
theorem B837191 : Blo 834351 837191 := bstep (se 1 (by rfl) ⟨627893, by rfl⟩ : syracuseStep 837191 = 1255787) B1255787
theorem B837343 : Blo 834351 837343 := bstep (se 1 (by rfl) ⟨628007, by rfl⟩ : syracuseStep 837343 = 1256015) B1256015
theorem B1885931 : Blo 834351 1885931 := bstep (se 1 (by rfl) ⟨1414448, by rfl⟩ : syracuseStep 1885931 = 2828897) B2828897
theorem B2115335 : Blo 834351 2115335 := bstep (se 1 (by rfl) ⟨1586501, by rfl⟩ : syracuseStep 2115335 = 3173003) B3173003
theorem B837423 : Blo 834351 837423 := bstep (se 1 (by rfl) ⟨628067, by rfl⟩ : syracuseStep 837423 = 1256135) B1256135
theorem B1886057 : Blo 834351 1886057 := bstep (se 2 (by rfl) ⟨707271, by rfl⟩ : syracuseStep 1886057 = 1414543) B1414543
theorem B837531 : Blo 834351 837531 := bstep (se 1 (by rfl) ⟨628148, by rfl⟩ : syracuseStep 837531 = 1256297) B1256297
theorem B837583 : Blo 834351 837583 := bstep (se 1 (by rfl) ⟨628187, by rfl⟩ : syracuseStep 837583 = 1256375) B1256375
theorem B837607 : Blo 834351 837607 := bstep (se 1 (by rfl) ⟨628205, by rfl⟩ : syracuseStep 837607 = 1256411) B1256411
theorem B6342785 : Blo 834351 6342785 := bstep (se 2 (by rfl) ⟨2378544, by rfl⟩ : syracuseStep 6342785 = 4757089) B4757089
theorem B14469313 : Blo 834351 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B21743873 : Blo 834351 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B837919 : Blo 834351 837919 := bstep (se 1 (by rfl) ⟨628439, by rfl⟩ : syracuseStep 837919 = 1256879) B1256879
theorem B837979 : Blo 834351 837979 := bstep (se 1 (by rfl) ⟨628484, by rfl⟩ : syracuseStep 837979 = 1256969) B1256969
theorem B837999 : Blo 834351 837999 := bstep (se 1 (by rfl) ⟨628499, by rfl⟩ : syracuseStep 837999 = 1256999) B1256999
theorem B838055 : Blo 834351 838055 := bstep (se 1 (by rfl) ⟨628541, by rfl⟩ : syracuseStep 838055 = 1257083) B1257083
theorem B838139 : Blo 834351 838139 := bstep (se 1 (by rfl) ⟨628604, by rfl⟩ : syracuseStep 838139 = 1257209) B1257209
theorem B2116115 : Blo 834351 2116115 := bstep (se 1 (by rfl) ⟨1587086, by rfl⟩ : syracuseStep 2116115 = 3174173) B3174173
theorem B838207 : Blo 834351 838207 := bstep (se 1 (by rfl) ⟨628655, by rfl⟩ : syracuseStep 838207 = 1257311) B1257311
theorem B838215 : Blo 834351 838215 := bstep (se 1 (by rfl) ⟨628661, by rfl⟩ : syracuseStep 838215 = 1257323) B1257323
theorem B2411183 : Blo 834351 2411183 := bstep (se 1 (by rfl) ⟨1808387, by rfl⟩ : syracuseStep 2411183 = 3616775) B3616775
theorem B5360519 : Blo 834351 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B6343757 : Blo 834351 6343757 := bstep (se 3 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 6343757 = 2378909) B2378909
theorem B4574323 : Blo 834351 4574323 := bstep (se 1 (by rfl) ⟨3430742, by rfl⟩ : syracuseStep 4574323 = 6861485) B6861485
theorem B58019105 : Blo 834351 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B1002791 : Blo 834351 1002791 := bstep (se 1 (by rfl) ⟨752093, by rfl⟩ : syracuseStep 1002791 = 1504187) B1504187
theorem B4771169 : Blo 834351 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B6344729 : Blo 834351 6344729 := bstep (se 2 (by rfl) ⟨2379273, by rfl⟩ : syracuseStep 6344729 = 4758547) B4758547
theorem B2412569 : Blo 834351 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B2117897 : Blo 834351 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B1790299 : Blo 834351 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B1790419 : Blo 834351 1790419 := bstep (se 1 (by rfl) ⟨1342814, by rfl⟩ : syracuseStep 1790419 = 2685629) B2685629
theorem B2118251 : Blo 834351 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B938983 : Blo 834351 938983 := bstep (se 1 (by rfl) ⟨704237, by rfl⟩ : syracuseStep 938983 = 1408475) B1408475
theorem B3921095 : Blo 834351 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2118899 : Blo 834351 2118899 := bstep (se 1 (by rfl) ⟨1589174, by rfl⟩ : syracuseStep 2118899 = 3178349) B3178349
theorem B3823037 : Blo 834351 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B6346187 : Blo 834351 6346187 := bstep (se 1 (by rfl) ⟨4759640, by rfl⟩ : syracuseStep 6346187 = 9519281) B9519281
theorem B1005151 : Blo 834351 1005151 := bstep (se 1 (by rfl) ⟨753863, by rfl⟩ : syracuseStep 1005151 = 1507727) B1507727
theorem B2119355 : Blo 834351 2119355 := bstep (se 1 (by rfl) ⟨1589516, by rfl⟩ : syracuseStep 2119355 = 3179033) B3179033
theorem B1005367 : Blo 834351 1005367 := bstep (se 1 (by rfl) ⟨754025, by rfl⟩ : syracuseStep 1005367 = 1508051) B1508051
theorem B15292423 : Blo 834351 15292423 := bstep (se 1 (by rfl) ⟨11469317, by rfl⟩ : syracuseStep 15292423 = 22938635) B22938635
theorem B2119891 : Blo 834351 2119891 := bstep (se 1 (by rfl) ⟨1589918, by rfl⟩ : syracuseStep 2119891 = 3179837) B3179837
theorem B17193467 : Blo 834351 17193467 := bstep (se 1 (by rfl) ⟨12895100, by rfl⟩ : syracuseStep 17193467 = 25790201) B25790201
theorem B3168841 : Blo 834351 3168841 := bstep (se 2 (by rfl) ⟨1188315, by rfl⟩ : syracuseStep 3168841 = 2376631) B2376631
theorem B940639 : Blo 834351 940639 := bstep (se 1 (by rfl) ⟨705479, by rfl⟩ : syracuseStep 940639 = 1410959) B1410959
theorem B2677799 : Blo 834351 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B2120843 : Blo 834351 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B2121299 : Blo 834351 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B12902003 : Blo 834351 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B941791 : Blo 834351 941791 := bstep (se 1 (by rfl) ⟨706343, by rfl⟩ : syracuseStep 941791 = 1412687) B1412687
theorem B2547463 : Blo 834351 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B6348617 : Blo 834351 6348617 := bstep (se 2 (by rfl) ⟨2380731, by rfl⟩ : syracuseStep 6348617 = 4761463) B4761463
theorem B8052655 : Blo 834351 8052655 := bstep (se 1 (by rfl) ⟨6039491, by rfl⟩ : syracuseStep 8052655 = 12078983) B12078983
theorem B4513963 : Blo 834351 4513963 := bstep (se 1 (by rfl) ⟨3385472, by rfl⟩ : syracuseStep 4513963 = 6770945) B6770945
theorem B942367 : Blo 834351 942367 := bstep (se 1 (by rfl) ⟨706775, by rfl⟩ : syracuseStep 942367 = 1413551) B1413551
theorem B14344535 : Blo 834351 14344535 := bstep (se 1 (by rfl) ⟨10758401, by rfl⟩ : syracuseStep 14344535 = 21516803) B21516803
theorem B3170785 : Blo 834351 3170785 := bstep (se 2 (by rfl) ⟨1189044, by rfl⟩ : syracuseStep 3170785 = 2378089) B2378089
theorem B27124253 : Blo 834351 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B942655 : Blo 834351 942655 := bstep (se 1 (by rfl) ⟨706991, by rfl⟩ : syracuseStep 942655 = 1413983) B1413983
theorem B1696987 : Blo 834351 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B7628377 : Blo 834351 7628377 := bstep (se 2 (by rfl) ⟨2860641, by rfl⟩ : syracuseStep 7628377 = 5721283) B5721283
theorem B12871457 : Blo 834351 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B8054963 : Blo 834351 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B25783193 : Blo 834351 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B4025483 : Blo 834351 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B2682143 : Blo 834351 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B24080921 : Blo 834351 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B14480117 : Blo 834351 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B3011833 : Blo 834351 3011833 := bstep (se 2 (by rfl) ⟨1129437, by rfl⟩ : syracuseStep 3011833 = 2258875) B2258875
theorem B1504649 : Blo 834351 1504649 := bstep (se 2 (by rfl) ⟨564243, by rfl⟩ : syracuseStep 1504649 = 1128487) B1128487
theorem B173930165 : Blo 834351 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B5437115 : Blo 834351 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B2684603 : Blo 834351 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B4224797 : Blo 834351 4224797 := bstep (se 3 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 4224797 = 1584299) B1584299
theorem B2259049 : Blo 834351 2259049 := bstep (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) B1694287
theorem B2816423 : Blo 834351 2816423 := bstep (se 1 (by rfl) ⟨2112317, by rfl⟩ : syracuseStep 2816423 = 4224635) B4224635
theorem B2816585 : Blo 834351 2816585 := bstep (se 2 (by rfl) ⟨1056219, by rfl⟩ : syracuseStep 2816585 = 2112439) B2112439
theorem B3570551 : Blo 834351 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B3013519 : Blo 834351 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B4291471 : Blo 834351 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B3570587 : Blo 834351 3570587 := bstep (se 1 (by rfl) ⟨2677940, by rfl⟩ : syracuseStep 3570587 = 5355881) B5355881
theorem B9043109 : Blo 834351 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B2260637 : Blo 834351 2260637 := bstep (se 3 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 2260637 = 847739) B847739
theorem B5078791 : Blo 834351 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B4292459 : Blo 834351 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B4522439 : Blo 834351 4522439 := bstep (se 1 (by rfl) ⟨3391829, by rfl⟩ : syracuseStep 4522439 = 6783659) B6783659
theorem B1507783 : Blo 834351 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B4227713 : Blo 834351 4227713 := bstep (se 2 (by rfl) ⟨1585392, by rfl⟩ : syracuseStep 4227713 = 3170785) B3170785
theorem B1409771 : Blo 834351 1409771 := bstep (se 1 (by rfl) ⟨1057328, by rfl⟩ : syracuseStep 1409771 = 2114657) B2114657
theorem B10158857 : Blo 834351 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B2819177 : Blo 834351 2819177 := bstep (se 2 (by rfl) ⟨1057191, by rfl⟩ : syracuseStep 2819177 = 2114383) B2114383
theorem B1410223 : Blo 834351 1410223 := bstep (se 1 (by rfl) ⟨1057667, by rfl⟩ : syracuseStep 1410223 = 2115335) B2115335
theorem B7144793 : Blo 834351 7144793 := bstep (se 2 (by rfl) ⟨2679297, by rfl⟩ : syracuseStep 7144793 = 5358595) B5358595
theorem B4228523 : Blo 834351 4228523 := bstep (se 1 (by rfl) ⟨3171392, by rfl⟩ : syracuseStep 4228523 = 6342785) B6342785
theorem B2262649 : Blo 834351 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B1410743 : Blo 834351 1410743 := bstep (se 1 (by rfl) ⟨1058057, by rfl⟩ : syracuseStep 1410743 = 2116115) B2116115
theorem B1607455 : Blo 834351 1607455 := bstep (se 1 (by rfl) ⟨1205591, by rfl⟩ : syracuseStep 1607455 = 2411183) B2411183
theorem B3573679 : Blo 834351 3573679 := bstep (se 1 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 3573679 = 5360519) B5360519
theorem B2820041 : Blo 834351 2820041 := bstep (se 2 (by rfl) ⟨1057515, by rfl⟩ : syracuseStep 2820041 = 2115031) B2115031
theorem B16058411 : Blo 834351 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B4229171 : Blo 834351 4229171 := bstep (se 1 (by rfl) ⟨3171878, by rfl⟩ : syracuseStep 4229171 = 6343757) B6343757
theorem B10717393 : Blo 834351 10717393 := bstep (se 2 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 10717393 = 8038045) B8038045
theorem B2820311 : Blo 834351 2820311 := bstep (se 1 (by rfl) ⟨2115233, by rfl⟩ : syracuseStep 2820311 = 4230467) B4230467
theorem B3180779 : Blo 834351 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B1509671 : Blo 834351 1509671 := bstep (se 1 (by rfl) ⟨1132253, by rfl⟩ : syracuseStep 1509671 = 2264507) B2264507
theorem B7145819 : Blo 834351 7145819 := bstep (se 1 (by rfl) ⟨5359364, by rfl⟩ : syracuseStep 7145819 = 10718729) B10718729
theorem B1902943 : Blo 834351 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B2820635 : Blo 834351 2820635 := bstep (se 1 (by rfl) ⟨2115476, by rfl⟩ : syracuseStep 2820635 = 4230953) B4230953
theorem B4229819 : Blo 834351 4229819 := bstep (se 1 (by rfl) ⟨3172364, by rfl⟩ : syracuseStep 4229819 = 6344729) B6344729
theorem B1608379 : Blo 834351 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B1411931 : Blo 834351 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B1412167 : Blo 834351 1412167 := bstep (se 1 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 1412167 = 2118251) B2118251
theorem B10456253 : Blo 834351 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2821499 : Blo 834351 2821499 := bstep (se 1 (by rfl) ⟨2116124, by rfl⟩ : syracuseStep 2821499 = 4232249) B4232249
theorem B1412599 : Blo 834351 1412599 := bstep (se 1 (by rfl) ⟨1059449, by rfl⟩ : syracuseStep 1412599 = 2118899) B2118899
theorem B4230791 : Blo 834351 4230791 := bstep (se 1 (by rfl) ⟨3173093, by rfl⟩ : syracuseStep 4230791 = 6346187) B6346187
theorem B3182237 : Blo 834351 3182237 := bstep (se 3 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 3182237 = 1193339) B1193339
theorem B1412903 : Blo 834351 1412903 := bstep (se 1 (by rfl) ⟨1059677, by rfl⟩ : syracuseStep 1412903 = 2119355) B2119355
theorem B1413625 : Blo 834351 1413625 := bstep (se 2 (by rfl) ⟨530109, by rfl⟩ : syracuseStep 1413625 = 1060219) B1060219
theorem B66130499 : Blo 834351 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B4756157 : Blo 834351 4756157 := bstep (se 3 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 4756157 = 1783559) B1783559
theorem B2822903 : Blo 834351 2822903 := bstep (se 1 (by rfl) ⟨2117177, by rfl⟩ : syracuseStep 2822903 = 4234355) B4234355
theorem B1413895 : Blo 834351 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B1413929 : Blo 834351 1413929 := bstep (se 2 (by rfl) ⟨530223, by rfl⟩ : syracuseStep 1413929 = 1060447) B1060447
theorem B7148483 : Blo 834351 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B2855945 : Blo 834351 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B1414199 : Blo 834351 1414199 := bstep (se 1 (by rfl) ⟨1060649, by rfl⟩ : syracuseStep 1414199 = 2121299) B2121299
theorem B4232411 : Blo 834351 4232411 := bstep (se 1 (by rfl) ⟨3174308, by rfl⟩ : syracuseStep 4232411 = 6348617) B6348617
theorem B2823443 : Blo 834351 2823443 := bstep (se 1 (by rfl) ⟨2117582, by rfl⟩ : syracuseStep 2823443 = 4235165) B4235165
theorem B2823983 : Blo 834351 2823983 := bstep (se 1 (by rfl) ⟨2117987, by rfl⟩ : syracuseStep 2823983 = 4235975) B4235975
theorem B5576663 : Blo 834351 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B1251563 : Blo 834351 1251563 := bstep (se 1 (by rfl) ⟨938672, by rfl⟩ : syracuseStep 1251563 = 1877345) B1877345
theorem B1251623 : Blo 834351 1251623 := bstep (se 1 (by rfl) ⟨938717, by rfl⟩ : syracuseStep 1251623 = 1877435) B1877435
theorem B1251707 : Blo 834351 1251707 := bstep (se 1 (by rfl) ⟨938780, by rfl⟩ : syracuseStep 1251707 = 1877561) B1877561
theorem B1251977 : Blo 834351 1251977 := bstep (se 2 (by rfl) ⟨469491, by rfl⟩ : syracuseStep 1251977 = 938983) B938983
theorem B1252151 : Blo 834351 1252151 := bstep (se 1 (by rfl) ⟨939113, by rfl⟩ : syracuseStep 1252151 = 1878227) B1878227
theorem B1252187 : Blo 834351 1252187 := bstep (se 1 (by rfl) ⟨939140, by rfl⟩ : syracuseStep 1252187 = 1878281) B1878281
theorem B1252331 : Blo 834351 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B3808403 : Blo 834351 3808403 := bstep (se 1 (by rfl) ⟨2856302, by rfl⟩ : syracuseStep 3808403 = 5712605) B5712605
theorem B1252535 : Blo 834351 1252535 := bstep (se 1 (by rfl) ⟨939401, by rfl⟩ : syracuseStep 1252535 = 1878803) B1878803
theorem B7150943 : Blo 834351 7150943 := bstep (se 1 (by rfl) ⟨5363207, by rfl⟩ : syracuseStep 7150943 = 10726415) B10726415
theorem B1252775 : Blo 834351 1252775 := bstep (se 1 (by rfl) ⟨939581, by rfl⟩ : syracuseStep 1252775 = 1879163) B1879163
theorem B1252859 : Blo 834351 1252859 := bstep (se 1 (by rfl) ⟨939644, by rfl⟩ : syracuseStep 1252859 = 1879289) B1879289
theorem B2825819 : Blo 834351 2825819 := bstep (se 1 (by rfl) ⟨2119364, by rfl⟩ : syracuseStep 2825819 = 4238729) B4238729
theorem B1252955 : Blo 834351 1252955 := bstep (se 1 (by rfl) ⟨939716, by rfl⟩ : syracuseStep 1252955 = 1879433) B1879433
theorem B1253039 : Blo 834351 1253039 := bstep (se 1 (by rfl) ⟨939779, by rfl⟩ : syracuseStep 1253039 = 1879559) B1879559
theorem B1253159 : Blo 834351 1253159 := bstep (se 1 (by rfl) ⟨939869, by rfl⟩ : syracuseStep 1253159 = 1879739) B1879739
theorem B1253243 : Blo 834351 1253243 := bstep (se 1 (by rfl) ⟨939932, by rfl⟩ : syracuseStep 1253243 = 1879865) B1879865
theorem B20389897 : Blo 834351 20389897 := bstep (se 2 (by rfl) ⟨7646211, by rfl⟩ : syracuseStep 20389897 = 15292423) B15292423
theorem B2826521 : Blo 834351 2826521 := bstep (se 2 (by rfl) ⟨1059945, by rfl⟩ : syracuseStep 2826521 = 2119891) B2119891
theorem B1253663 : Blo 834351 1253663 := bstep (se 1 (by rfl) ⟨940247, by rfl⟩ : syracuseStep 1253663 = 1880495) B1880495
theorem B1253687 : Blo 834351 1253687 := bstep (se 1 (by rfl) ⟨940265, by rfl⟩ : syracuseStep 1253687 = 1880531) B1880531
theorem B9052489 : Blo 834351 9052489 := bstep (se 2 (by rfl) ⟨3394683, by rfl⟩ : syracuseStep 9052489 = 6789367) B6789367
theorem B1057151 : Blo 834351 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B1253759 : Blo 834351 1253759 := bstep (se 1 (by rfl) ⟨940319, by rfl⟩ : syracuseStep 1253759 = 1880639) B1880639
theorem B2826683 : Blo 834351 2826683 := bstep (se 1 (by rfl) ⟨2120012, by rfl⟩ : syracuseStep 2826683 = 4240025) B4240025
theorem B1253831 : Blo 834351 1253831 := bstep (se 1 (by rfl) ⟨940373, by rfl⟩ : syracuseStep 1253831 = 1880747) B1880747
theorem B18064073 : Blo 834351 18064073 := bstep (se 2 (by rfl) ⟨6774027, by rfl⟩ : syracuseStep 18064073 = 13548055) B13548055
theorem B1254185 : Blo 834351 1254185 := bstep (se 2 (by rfl) ⟨470319, by rfl⟩ : syracuseStep 1254185 = 940639) B940639
theorem B1254191 : Blo 834351 1254191 := bstep (se 1 (by rfl) ⟨940643, by rfl⟩ : syracuseStep 1254191 = 1881287) B1881287
theorem B1254311 : Blo 834351 1254311 := bstep (se 1 (by rfl) ⟨940733, by rfl⟩ : syracuseStep 1254311 = 1881467) B1881467
theorem B1254395 : Blo 834351 1254395 := bstep (se 1 (by rfl) ⟨940796, by rfl⟩ : syracuseStep 1254395 = 1881593) B1881593
theorem B1254455 : Blo 834351 1254455 := bstep (se 1 (by rfl) ⟨940841, by rfl⟩ : syracuseStep 1254455 = 1881683) B1881683
theorem B1057855 : Blo 834351 1057855 := bstep (se 1 (by rfl) ⟨793391, by rfl⟩ : syracuseStep 1057855 = 1586783) B1586783
theorem B1254575 : Blo 834351 1254575 := bstep (se 1 (by rfl) ⟨940931, by rfl⟩ : syracuseStep 1254575 = 1881863) B1881863
theorem B20358373 : Blo 834351 20358373 := bstep (se 4 (by rfl) ⟨1908597, by rfl⟩ : syracuseStep 20358373 = 3817195) B3817195
theorem B1254983 : Blo 834351 1254983 := bstep (se 1 (by rfl) ⟨941237, by rfl⟩ : syracuseStep 1254983 = 1882475) B1882475
theorem B2827871 : Blo 834351 2827871 := bstep (se 1 (by rfl) ⟨2120903, by rfl⟩ : syracuseStep 2827871 = 4241807) B4241807
theorem B1877615 : Blo 834351 1877615 := bstep (se 1 (by rfl) ⟨1408211, by rfl⟩ : syracuseStep 1877615 = 2816423) B2816423
theorem B1255079 : Blo 834351 1255079 := bstep (se 1 (by rfl) ⟨941309, by rfl⟩ : syracuseStep 1255079 = 1882619) B1882619
theorem B1877723 : Blo 834351 1877723 := bstep (se 1 (by rfl) ⟨1408292, by rfl⟩ : syracuseStep 1877723 = 2816585) B2816585
theorem B1255163 : Blo 834351 1255163 := bstep (se 1 (by rfl) ⟨941372, by rfl⟩ : syracuseStep 1255163 = 1882745) B1882745
theorem B1255199 : Blo 834351 1255199 := bstep (se 1 (by rfl) ⟨941399, by rfl⟩ : syracuseStep 1255199 = 1882799) B1882799
theorem B1255247 : Blo 834351 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B10692485 : Blo 834351 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B1189831 : Blo 834351 1189831 := bstep (se 1 (by rfl) ⟨892373, by rfl⟩ : syracuseStep 1189831 = 1784747) B1784747
theorem B1255367 : Blo 834351 1255367 := bstep (se 1 (by rfl) ⟨941525, by rfl⟩ : syracuseStep 1255367 = 1883051) B1883051
theorem B2894015 : Blo 834351 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B1255721 : Blo 834351 1255721 := bstep (se 2 (by rfl) ⟨470895, by rfl⟩ : syracuseStep 1255721 = 941791) B941791
theorem B1255727 : Blo 834351 1255727 := bstep (se 1 (by rfl) ⟨941795, by rfl⟩ : syracuseStep 1255727 = 1883591) B1883591
theorem B1255967 : Blo 834351 1255967 := bstep (se 1 (by rfl) ⟨941975, by rfl⟩ : syracuseStep 1255967 = 1883951) B1883951
theorem B2861639 : Blo 834351 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B1878839 : Blo 834351 1878839 := bstep (se 1 (by rfl) ⟨1409129, by rfl⟩ : syracuseStep 1878839 = 2818259) B2818259
theorem B21441347 : Blo 834351 21441347 := bstep (se 1 (by rfl) ⟨16081010, by rfl⟩ : syracuseStep 21441347 = 32162021) B32162021
theorem B1059743 : Blo 834351 1059743 := bstep (se 1 (by rfl) ⟨794807, by rfl⟩ : syracuseStep 1059743 = 1589615) B1589615
theorem B1256351 : Blo 834351 1256351 := bstep (se 1 (by rfl) ⟨942263, by rfl⟩ : syracuseStep 1256351 = 1884527) B1884527
theorem B1256399 : Blo 834351 1256399 := bstep (se 1 (by rfl) ⟨942299, by rfl⟩ : syracuseStep 1256399 = 1884599) B1884599
theorem B2829275 : Blo 834351 2829275 := bstep (se 1 (by rfl) ⟨2121956, by rfl⟩ : syracuseStep 2829275 = 4243913) B4243913
theorem B99167203 : Blo 834351 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B1879019 : Blo 834351 1879019 := bstep (se 1 (by rfl) ⟨1409264, by rfl⟩ : syracuseStep 1879019 = 2818529) B2818529
theorem B1190953 : Blo 834351 1190953 := bstep (se 2 (by rfl) ⟨446607, by rfl⟩ : syracuseStep 1190953 = 893215) B893215
theorem B1256489 : Blo 834351 1256489 := bstep (se 2 (by rfl) ⟨471183, by rfl⟩ : syracuseStep 1256489 = 942367) B942367
theorem B1256495 : Blo 834351 1256495 := bstep (se 1 (by rfl) ⟨942371, by rfl⟩ : syracuseStep 1256495 = 1884743) B1884743
theorem B1256519 : Blo 834351 1256519 := bstep (se 1 (by rfl) ⟨942389, by rfl⟩ : syracuseStep 1256519 = 1884779) B1884779
theorem B1912031 : Blo 834351 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B1256783 : Blo 834351 1256783 := bstep (se 1 (by rfl) ⟨942587, by rfl⟩ : syracuseStep 1256783 = 1885175) B1885175
theorem B1256873 : Blo 834351 1256873 := bstep (se 2 (by rfl) ⟨471327, by rfl⟩ : syracuseStep 1256873 = 942655) B942655
theorem B1257023 : Blo 834351 1257023 := bstep (se 1 (by rfl) ⟨942767, by rfl⟩ : syracuseStep 1257023 = 1885535) B1885535
theorem B1879847 : Blo 834351 1879847 := bstep (se 1 (by rfl) ⟨1409885, by rfl⟩ : syracuseStep 1879847 = 2819771) B2819771
theorem B1257287 : Blo 834351 1257287 := bstep (se 1 (by rfl) ⟨942965, by rfl⟩ : syracuseStep 1257287 = 1885931) B1885931
theorem B1257371 : Blo 834351 1257371 := bstep (se 1 (by rfl) ⟨943028, by rfl⟩ : syracuseStep 1257371 = 1886057) B1886057
theorem B14495915 : Blo 834351 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B12202649 : Blo 834351 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B9548441 : Blo 834351 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B10171169 : Blo 834351 10171169 := bstep (se 2 (by rfl) ⟨3814188, by rfl⟩ : syracuseStep 10171169 = 7628377) B7628377
theorem B1880873 : Blo 834351 1880873 := bstep (se 2 (by rfl) ⟨705327, by rfl⟩ : syracuseStep 1880873 = 1410655) B1410655
theorem B38679403 : Blo 834351 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B1881143 : Blo 834351 1881143 := bstep (se 1 (by rfl) ⟨1410857, by rfl⟩ : syracuseStep 1881143 = 2821715) B2821715
theorem B1881161 : Blo 834351 1881161 := bstep (se 2 (by rfl) ⟨705435, by rfl⟩ : syracuseStep 1881161 = 1410871) B1410871
theorem B8566361 : Blo 834351 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B834395 : Blo 834351 834395 := bstep (se 1 (by rfl) ⟨625796, by rfl⟩ : syracuseStep 834395 = 1251593) B1251593
theorem B834463 : Blo 834351 834463 := bstep (se 1 (by rfl) ⟨625847, by rfl⟩ : syracuseStep 834463 = 1251695) B1251695
theorem B1883087 : Blo 834351 1883087 := bstep (se 1 (by rfl) ⟨1412315, by rfl⟩ : syracuseStep 1883087 = 2824631) B2824631
theorem B1883105 : Blo 834351 1883105 := bstep (se 2 (by rfl) ⟨706164, by rfl⟩ : syracuseStep 1883105 = 1412329) B1412329
theorem B10730515 : Blo 834351 10730515 := bstep (se 1 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 10730515 = 16095773) B16095773
theorem B1883177 : Blo 834351 1883177 := bstep (se 2 (by rfl) ⟨706191, by rfl⟩ : syracuseStep 1883177 = 1412383) B1412383
theorem B834607 : Blo 834351 834607 := bstep (se 1 (by rfl) ⟨625955, by rfl⟩ : syracuseStep 834607 = 1251911) B1251911
theorem B834631 : Blo 834351 834631 := bstep (se 1 (by rfl) ⟨625973, by rfl⟩ : syracuseStep 834631 = 1251947) B1251947
theorem B7158941 : Blo 834351 7158941 := bstep (se 3 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 7158941 = 2684603) B2684603
theorem B834783 : Blo 834351 834783 := bstep (se 1 (by rfl) ⟨626087, by rfl⟩ : syracuseStep 834783 = 1252175) B1252175
theorem B22887845 : Blo 834351 22887845 := bstep (se 4 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 22887845 = 4291471) B4291471
theorem B835047 : Blo 834351 835047 := bstep (se 1 (by rfl) ⟨626285, by rfl⟩ : syracuseStep 835047 = 1252571) B1252571
theorem B835163 : Blo 834351 835163 := bstep (se 1 (by rfl) ⟨626372, by rfl⟩ : syracuseStep 835163 = 1252745) B1252745
theorem B2113249 : Blo 834351 2113249 := bstep (se 2 (by rfl) ⟨792468, by rfl⟩ : syracuseStep 2113249 = 1584937) B1584937
theorem B8601335 : Blo 834351 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B835399 : Blo 834351 835399 := bstep (se 1 (by rfl) ⟨626549, by rfl⟩ : syracuseStep 835399 = 1253099) B1253099
theorem B835551 : Blo 834351 835551 := bstep (se 1 (by rfl) ⟨626663, by rfl⟩ : syracuseStep 835551 = 1253327) B1253327
theorem B835815 : Blo 834351 835815 := bstep (se 1 (by rfl) ⟨626861, by rfl⟩ : syracuseStep 835815 = 1253723) B1253723
theorem B835967 : Blo 834351 835967 := bstep (se 1 (by rfl) ⟨626975, by rfl⟩ : syracuseStep 835967 = 1253951) B1253951
theorem B836047 : Blo 834351 836047 := bstep (se 1 (by rfl) ⟨627035, by rfl⟩ : syracuseStep 836047 = 1254071) B1254071
theorem B24396389 : Blo 834351 24396389 := bstep (se 4 (by rfl) ⟨2287161, by rfl⟩ : syracuseStep 24396389 = 4574323) B4574323
theorem B836199 : Blo 834351 836199 := bstep (se 1 (by rfl) ⟨627149, by rfl⟩ : syracuseStep 836199 = 1254299) B1254299
theorem B4244075 : Blo 834351 4244075 := bstep (se 1 (by rfl) ⟨3183056, by rfl⟩ : syracuseStep 4244075 = 6366113) B6366113
theorem B1590025 : Blo 834351 1590025 := bstep (se 2 (by rfl) ⟨596259, by rfl⟩ : syracuseStep 1590025 = 1192519) B1192519
theorem B836463 : Blo 834351 836463 := bstep (se 1 (by rfl) ⟨627347, by rfl⟩ : syracuseStep 836463 = 1254695) B1254695
theorem B836519 : Blo 834351 836519 := bstep (se 1 (by rfl) ⟨627389, by rfl⟩ : syracuseStep 836519 = 1254779) B1254779
theorem B1885139 : Blo 834351 1885139 := bstep (se 1 (by rfl) ⟨1413854, by rfl⟩ : syracuseStep 1885139 = 2827709) B2827709
theorem B836603 : Blo 834351 836603 := bstep (se 1 (by rfl) ⟨627452, by rfl⟩ : syracuseStep 836603 = 1254905) B1254905
theorem B836671 : Blo 834351 836671 := bstep (se 1 (by rfl) ⟨627503, by rfl⟩ : syracuseStep 836671 = 1255007) B1255007
theorem B836815 : Blo 834351 836815 := bstep (se 1 (by rfl) ⟨627611, by rfl⟩ : syracuseStep 836815 = 1255223) B1255223
theorem B1885391 : Blo 834351 1885391 := bstep (se 1 (by rfl) ⟨1414043, by rfl⟩ : syracuseStep 1885391 = 2828087) B2828087
theorem B4769027 : Blo 834351 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B837019 : Blo 834351 837019 := bstep (se 1 (by rfl) ⟨627764, by rfl⟩ : syracuseStep 837019 = 1255529) B1255529
theorem B1885715 : Blo 834351 1885715 := bstep (se 1 (by rfl) ⟨1414286, by rfl⟩ : syracuseStep 1885715 = 2828573) B2828573
theorem B837231 : Blo 834351 837231 := bstep (se 1 (by rfl) ⟨627923, by rfl⟩ : syracuseStep 837231 = 1255847) B1255847
theorem B2115193 : Blo 834351 2115193 := bstep (se 2 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 2115193 = 1586395) B1586395
theorem B4015777 : Blo 834351 4015777 := bstep (se 2 (by rfl) ⟨1505916, by rfl⟩ : syracuseStep 4015777 = 3011833) B3011833
theorem B837287 : Blo 834351 837287 := bstep (se 1 (by rfl) ⟨627965, by rfl⟩ : syracuseStep 837287 = 1255931) B1255931
theorem B837371 : Blo 834351 837371 := bstep (se 1 (by rfl) ⟨628028, by rfl⟩ : syracuseStep 837371 = 1256057) B1256057
theorem B837407 : Blo 834351 837407 := bstep (se 1 (by rfl) ⟨628055, by rfl⟩ : syracuseStep 837407 = 1256111) B1256111
theorem B837439 : Blo 834351 837439 := bstep (se 1 (by rfl) ⟨628079, by rfl⟩ : syracuseStep 837439 = 1256159) B1256159
theorem B19318661 : Blo 834351 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B4769711 : Blo 834351 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B17188795 : Blo 834351 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B837615 : Blo 834351 837615 := bstep (se 1 (by rfl) ⟨628211, by rfl⟩ : syracuseStep 837615 = 1256423) B1256423
theorem B837787 : Blo 834351 837787 := bstep (se 1 (by rfl) ⟨628340, by rfl⟩ : syracuseStep 837787 = 1256681) B1256681
theorem B1788095 : Blo 834351 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B837823 : Blo 834351 837823 := bstep (se 1 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 837823 = 1256735) B1256735
theorem B837935 : Blo 834351 837935 := bstep (se 1 (by rfl) ⟨628451, by rfl⟩ : syracuseStep 837935 = 1256903) B1256903
theorem B838171 : Blo 834351 838171 := bstep (se 1 (by rfl) ⟨628628, by rfl⟩ : syracuseStep 838171 = 1257257) B1257257
theorem B838175 : Blo 834351 838175 := bstep (se 1 (by rfl) ⟨628631, by rfl⟩ : syracuseStep 838175 = 1257263) B1257263
theorem B9653411 : Blo 834351 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B2674109 : Blo 834351 2674109 := bstep (se 3 (by rfl) ⟨501395, by rfl⟩ : syracuseStep 2674109 = 1002791) B1002791
theorem B7130713 : Blo 834351 7130713 := bstep (se 2 (by rfl) ⟨2674017, by rfl⟩ : syracuseStep 7130713 = 5348035) B5348035
theorem B1003099 : Blo 834351 1003099 := bstep (se 1 (by rfl) ⟨752324, by rfl⟩ : syracuseStep 1003099 = 1504649) B1504649
theorem B6016771 : Blo 834351 6016771 := bstep (se 1 (by rfl) ⟨4512578, by rfl⟩ : syracuseStep 6016771 = 9025157) B9025157
theorem B115953443 : Blo 834351 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B3624743 : Blo 834351 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B4018025 : Blo 834351 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B27086885 : Blo 834351 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B36720701 : Blo 834351 36720701 := bstep (se 3 (by rfl) ⟨6885131, by rfl⟩ : syracuseStep 36720701 = 13770263) B13770263
theorem B2380367 : Blo 834351 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B2380391 : Blo 834351 2380391 := bstep (se 1 (by rfl) ⟨1785293, by rfl⟩ : syracuseStep 2380391 = 3570587) B3570587
theorem B3396617 : Blo 834351 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B4772945 : Blo 834351 4772945 := bstep (se 2 (by rfl) ⟨1789854, by rfl⟩ : syracuseStep 4772945 = 3579709) B3579709
theorem B10736873 : Blo 834351 10736873 := bstep (se 2 (by rfl) ⟨4026327, by rfl⟩ : syracuseStep 10736873 = 8052655) B8052655
theorem B1430875 : Blo 834351 1430875 := bstep (se 1 (by rfl) ⟨1073156, by rfl⟩ : syracuseStep 1430875 = 2146313) B2146313
theorem B6018617 : Blo 834351 6018617 := bstep (se 2 (by rfl) ⟨2256981, by rfl⟩ : syracuseStep 6018617 = 4513963) B4513963
theorem B939631 : Blo 834351 939631 := bstep (se 1 (by rfl) ⟨704723, by rfl⟩ : syracuseStep 939631 = 1409447) B1409447
theorem B939739 : Blo 834351 939739 := bstep (se 1 (by rfl) ⟨704804, by rfl⟩ : syracuseStep 939739 = 1409609) B1409609
theorem B72275975 : Blo 834351 72275975 := bstep (se 1 (by rfl) ⟨54206981, by rfl⟩ : syracuseStep 72275975 = 108413963) B108413963
theorem B2381849 : Blo 834351 2381849 := bstep (se 2 (by rfl) ⟨893193, by rfl⟩ : syracuseStep 2381849 = 1786387) B1786387
theorem B2119841 : Blo 834351 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B2676979 : Blo 834351 2676979 := bstep (se 1 (by rfl) ⟨2007734, by rfl⟩ : syracuseStep 2676979 = 4015469) B4015469
theorem B6773021 : Blo 834351 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B17127787 : Blo 834351 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B30497579 : Blo 834351 30497579 := bstep (se 1 (by rfl) ⟨22873184, by rfl⟩ : syracuseStep 30497579 = 45746369) B45746369
theorem B12409649 : Blo 834351 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B3169115 : Blo 834351 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B940891 : Blo 834351 940891 := bstep (se 1 (by rfl) ⟨705668, by rfl⟩ : syracuseStep 940891 = 1411337) B1411337
theorem B2120539 : Blo 834351 2120539 := bstep (se 1 (by rfl) ⟨1590404, by rfl⟩ : syracuseStep 2120539 = 3180809) B3180809
theorem B2382817 : Blo 834351 2382817 := bstep (se 2 (by rfl) ⟨893556, by rfl⟩ : syracuseStep 2382817 = 1787113) B1787113
theorem B3169631 : Blo 834351 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B2711015 : Blo 834351 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B941863 : Blo 834351 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B2383739 : Blo 834351 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B2121947 : Blo 834351 2121947 := bstep (se 1 (by rfl) ⟨1591460, by rfl⟩ : syracuseStep 2121947 = 3182921) B3182921
theorem B19292417 : Blo 834351 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B2384491 : Blo 834351 2384491 := bstep (se 1 (by rfl) ⟨1788368, by rfl⟩ : syracuseStep 2384491 = 3576737) B3576737
theorem B943015 : Blo 834351 943015 := bstep (se 1 (by rfl) ⟨707261, by rfl⟩ : syracuseStep 943015 = 1414523) B1414523
theorem B2548691 : Blo 834351 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B6514057 : Blo 834351 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B11462311 : Blo 834351 11462311 := bstep (se 1 (by rfl) ⟨8596733, by rfl⟩ : syracuseStep 11462311 = 17193467) B17193467
theorem B16050257 : Blo 834351 16050257 := bstep (se 2 (by rfl) ⟨6018846, by rfl⟩ : syracuseStep 16050257 = 12037693) B12037693
theorem B2386223 : Blo 834351 2386223 := bstep (se 1 (by rfl) ⟨1789667, by rfl⟩ : syracuseStep 2386223 = 3579335) B3579335
theorem B9563023 : Blo 834351 9563023 := bstep (se 1 (by rfl) ⟨7172267, by rfl⟩ : syracuseStep 9563023 = 14344535) B14344535
theorem B18082835 : Blo 834351 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B1338439 : Blo 834351 1338439 := bstep (se 1 (by rfl) ⟨1003829, by rfl⟩ : syracuseStep 1338439 = 2007659) B2007659
theorem B2387065 : Blo 834351 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B3173519 : Blo 834351 3173519 := bstep (se 1 (by rfl) ⟨2380139, by rfl⟩ : syracuseStep 3173519 = 4760279) B4760279
theorem B2387225 : Blo 834351 2387225 := bstep (se 2 (by rfl) ⟨895209, by rfl⟩ : syracuseStep 2387225 = 1790419) B1790419
theorem B19296107 : Blo 834351 19296107 := bstep (se 1 (by rfl) ⟨14472080, by rfl⟩ : syracuseStep 19296107 = 28944161) B28944161
theorem B8580971 : Blo 834351 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B5369975 : Blo 834351 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B5075677 : Blo 834351 5075677 := bstep (se 3 (by rfl) ⟨951689, by rfl⟩ : syracuseStep 5075677 = 1903379) B1903379
theorem B3175159 : Blo 834351 3175159 := bstep (se 1 (by rfl) ⟨2381369, by rfl⟩ : syracuseStep 3175159 = 4762739) B4762739
theorem B2683655 : Blo 834351 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B1340201 : Blo 834351 1340201 := bstep (se 2 (by rfl) ⟨502575, by rfl⟩ : syracuseStep 1340201 = 1005151) B1005151
theorem B1340489 : Blo 834351 1340489 := bstep (se 2 (by rfl) ⟨502683, by rfl⟩ : syracuseStep 1340489 = 1005367) B1005367
theorem B7140797 : Blo 834351 7140797 := bstep (se 3 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 7140797 = 2677799) B2677799
theorem B3012065 : Blo 834351 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B16053947 : Blo 834351 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B1341431 : Blo 834351 1341431 := bstep (se 1 (by rfl) ⟨1006073, by rfl⟩ : syracuseStep 1341431 = 2012147) B2012147
theorem B4225121 : Blo 834351 4225121 := bstep (se 2 (by rfl) ⟨1584420, by rfl⟩ : syracuseStep 4225121 = 3168841) B3168841
theorem B4225283 : Blo 834351 4225283 := bstep (se 1 (by rfl) ⟨3168962, by rfl⟩ : syracuseStep 4225283 = 6337925) B6337925
theorem B6781295 : Blo 834351 6781295 := bstep (se 1 (by rfl) ⟨5085971, by rfl⟩ : syracuseStep 6781295 = 10171943) B10171943
theorem B2816531 : Blo 834351 2816531 := bstep (se 1 (by rfl) ⟨2112398, by rfl⟩ : syracuseStep 2816531 = 4224797) B4224797
theorem B1408367 : Blo 834351 1408367 := bstep (se 1 (by rfl) ⟨1056275, by rfl⟩ : syracuseStep 1408367 = 2112551) B2112551
theorem B6028739 : Blo 834351 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B3178075 : Blo 834351 3178075 := bstep (se 1 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 3178075 = 4767113) B4767113
theorem B1408603 : Blo 834351 1408603 := bstep (se 1 (by rfl) ⟨1056452, by rfl⟩ : syracuseStep 1408603 = 2112905) B2112905
theorem B1408745 : Blo 834351 1408745 := bstep (se 2 (by rfl) ⟨528279, by rfl⟩ : syracuseStep 1408745 = 1056559) B1056559
theorem B1507091 : Blo 834351 1507091 := bstep (se 1 (by rfl) ⟨1130318, by rfl⟩ : syracuseStep 1507091 = 2260637) B2260637
theorem B9535319 : Blo 834351 9535319 := bstep (se 1 (by rfl) ⟨7151489, by rfl⟩ : syracuseStep 9535319 = 14302979) B14302979
theorem B4226903 : Blo 834351 4226903 := bstep (se 1 (by rfl) ⟨3170177, by rfl⟩ : syracuseStep 4226903 = 6340355) B6340355
theorem B2818475 : Blo 834351 2818475 := bstep (se 1 (by rfl) ⟨2113856, by rfl⟩ : syracuseStep 2818475 = 4227713) B4227713
theorem B3179321 : Blo 834351 3179321 := bstep (se 2 (by rfl) ⟨1192245, by rfl⟩ : syracuseStep 3179321 = 2384491) B2384491
theorem B3179351 : Blo 834351 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B2819015 : Blo 834351 2819015 := bstep (se 1 (by rfl) ⟨2114261, by rfl⟩ : syracuseStep 2819015 = 4228523) B4228523
theorem B2819069 : Blo 834351 2819069 := bstep (se 3 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 2819069 = 1057151) B1057151
theorem B12059837 : Blo 834351 12059837 := bstep (se 3 (by rfl) ⟨2261219, by rfl⟩ : syracuseStep 12059837 = 4522439) B4522439
theorem B12879107 : Blo 834351 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B3179807 : Blo 834351 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B2819447 : Blo 834351 2819447 := bstep (se 1 (by rfl) ⟨2114585, by rfl⟩ : syracuseStep 2819447 = 4229171) B4229171
theorem B1410473 : Blo 834351 1410473 := bstep (se 2 (by rfl) ⟨528927, by rfl⟩ : syracuseStep 1410473 = 1057855) B1057855
theorem B2819879 : Blo 834351 2819879 := bstep (se 1 (by rfl) ⟨2114909, by rfl⟩ : syracuseStep 2819879 = 4229819) B4229819
theorem B8685409 : Blo 834351 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B2820257 : Blo 834351 2820257 := bstep (se 2 (by rfl) ⟨1057596, by rfl⟩ : syracuseStep 2820257 = 2115193) B2115193
theorem B3016865 : Blo 834351 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B2820527 : Blo 834351 2820527 := bstep (se 1 (by rfl) ⟨2115395, by rfl⟩ : syracuseStep 2820527 = 4230791) B4230791
theorem B77302295 : Blo 834351 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B18057923 : Blo 834351 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B24480467 : Blo 834351 24480467 := bstep (se 1 (by rfl) ⟨18360350, by rfl⟩ : syracuseStep 24480467 = 36720701) B36720701
theorem B3574637 : Blo 834351 3574637 := bstep (se 3 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 3574637 = 1340489) B1340489
theorem B14289857 : Blo 834351 14289857 := bstep (se 2 (by rfl) ⟨5358696, by rfl⟩ : syracuseStep 14289857 = 10717393) B10717393
theorem B2264411 : Blo 834351 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B3181963 : Blo 834351 3181963 := bstep (se 1 (by rfl) ⟨2386472, by rfl⟩ : syracuseStep 3181963 = 4772945) B4772945
theorem B2821607 : Blo 834351 2821607 := bstep (se 1 (by rfl) ⟨2116205, by rfl⟩ : syracuseStep 2821607 = 4232411) B4232411
theorem B12750697 : Blo 834351 12750697 := bstep (se 2 (by rfl) ⟨4781511, by rfl⟩ : syracuseStep 12750697 = 9563023) B9563023
theorem B34312085 : Blo 834351 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B132222937 : Blo 834351 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B1413227 : Blo 834351 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B3182753 : Blo 834351 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B9507617 : Blo 834351 9507617 := bstep (se 2 (by rfl) ⟨3565356, by rfl⟩ : syracuseStep 9507617 = 7130713) B7130713
theorem B1807343 : Blo 834351 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B1414631 : Blo 834351 1414631 := bstep (se 1 (by rfl) ⟨1060973, by rfl⟩ : syracuseStep 1414631 = 2121947) B2121947
theorem B4233545 : Blo 834351 4233545 := bstep (se 2 (by rfl) ⟨1587579, by rfl⟩ : syracuseStep 4233545 = 3175159) B3175159
theorem B1251743 : Blo 834351 1251743 := bstep (se 1 (by rfl) ⟨938807, by rfl⟩ : syracuseStep 1251743 = 1877615) B1877615
theorem B1251815 : Blo 834351 1251815 := bstep (se 1 (by rfl) ⟨938861, by rfl⟩ : syracuseStep 1251815 = 1877723) B1877723
theorem B1907759 : Blo 834351 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B1252559 : Blo 834351 1252559 := bstep (se 1 (by rfl) ⟨939419, by rfl⟩ : syracuseStep 1252559 = 1878839) B1878839
theorem B14294231 : Blo 834351 14294231 := bstep (se 1 (by rfl) ⟨10720673, by rfl⟩ : syracuseStep 14294231 = 21441347) B21441347
theorem B1252679 : Blo 834351 1252679 := bstep (se 1 (by rfl) ⟨939509, by rfl⟩ : syracuseStep 1252679 = 1879019) B1879019
theorem B1252841 : Blo 834351 1252841 := bstep (se 2 (by rfl) ⟨469815, by rfl⟩ : syracuseStep 1252841 = 939631) B939631
theorem B1252985 : Blo 834351 1252985 := bstep (se 2 (by rfl) ⟨469869, by rfl⟩ : syracuseStep 1252985 = 939739) B939739
theorem B2825981 : Blo 834351 2825981 := bstep (se 3 (by rfl) ⟨529871, by rfl⟩ : syracuseStep 2825981 = 1059743) B1059743
theorem B1253231 : Blo 834351 1253231 := bstep (se 1 (by rfl) ⟨939923, by rfl⟩ : syracuseStep 1253231 = 1879847) B1879847
theorem B3579983 : Blo 834351 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B8135099 : Blo 834351 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B6365627 : Blo 834351 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B1253915 : Blo 834351 1253915 := bstep (se 1 (by rfl) ⟨940436, by rfl⟩ : syracuseStep 1253915 = 1880873) B1880873
theorem B893467 : Blo 834351 893467 := bstep (se 1 (by rfl) ⟨670100, by rfl⟩ : syracuseStep 893467 = 1340201) B1340201
theorem B1254095 : Blo 834351 1254095 := bstep (se 1 (by rfl) ⟨940571, by rfl⟩ : syracuseStep 1254095 = 1881143) B1881143
theorem B1254107 : Blo 834351 1254107 := bstep (se 1 (by rfl) ⟨940580, by rfl⟩ : syracuseStep 1254107 = 1881161) B1881161
theorem B4760531 : Blo 834351 4760531 := bstep (se 1 (by rfl) ⟨3570398, by rfl⟩ : syracuseStep 4760531 = 7140797) B7140797
theorem B2008043 : Blo 834351 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B5710907 : Blo 834351 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B1254521 : Blo 834351 1254521 := bstep (se 2 (by rfl) ⟨470445, by rfl⟩ : syracuseStep 1254521 = 940891) B940891
theorem B2827385 : Blo 834351 2827385 := bstep (se 2 (by rfl) ⟨1060269, by rfl⟩ : syracuseStep 2827385 = 2120539) B2120539
theorem B894287 : Blo 834351 894287 := bstep (se 1 (by rfl) ⟨670715, by rfl⟩ : syracuseStep 894287 = 1341431) B1341431
theorem B1877687 : Blo 834351 1877687 := bstep (se 1 (by rfl) ⟨1408265, by rfl⟩ : syracuseStep 1877687 = 2816531) B2816531
theorem B1255391 : Blo 834351 1255391 := bstep (se 1 (by rfl) ⟨941543, by rfl⟩ : syracuseStep 1255391 = 1883087) B1883087
theorem B1255403 : Blo 834351 1255403 := bstep (se 1 (by rfl) ⟨941552, by rfl⟩ : syracuseStep 1255403 = 1883105) B1883105
theorem B1255451 : Blo 834351 1255451 := bstep (se 1 (by rfl) ⟨941588, by rfl⟩ : syracuseStep 1255451 = 1883177) B1883177
theorem B1878137 : Blo 834351 1878137 := bstep (se 2 (by rfl) ⟨704301, by rfl⟩ : syracuseStep 1878137 = 1408603) B1408603
theorem B4237433 : Blo 834351 4237433 := bstep (se 2 (by rfl) ⟨1589037, by rfl⟩ : syracuseStep 4237433 = 3178075) B3178075
theorem B1255817 : Blo 834351 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B16264259 : Blo 834351 16264259 := bstep (se 1 (by rfl) ⟨12198194, by rfl⟩ : syracuseStep 16264259 = 24396389) B24396389
theorem B2829383 : Blo 834351 2829383 := bstep (se 1 (by rfl) ⟨2122037, by rfl⟩ : syracuseStep 2829383 = 4244075) B4244075
theorem B12069985 : Blo 834351 12069985 := bstep (se 2 (by rfl) ⟨4526244, by rfl⟩ : syracuseStep 12069985 = 9052489) B9052489
theorem B2010377 : Blo 834351 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B1256759 : Blo 834351 1256759 := bstep (se 1 (by rfl) ⟨942569, by rfl⟩ : syracuseStep 1256759 = 1885139) B1885139
theorem B1879451 : Blo 834351 1879451 := bstep (se 1 (by rfl) ⟨1409588, by rfl⟩ : syracuseStep 1879451 = 2819177) B2819177
theorem B1256927 : Blo 834351 1256927 := bstep (se 1 (by rfl) ⟨942695, by rfl⟩ : syracuseStep 1256927 = 1885391) B1885391
theorem B4763195 : Blo 834351 4763195 := bstep (se 1 (by rfl) ⟨3572396, by rfl⟩ : syracuseStep 4763195 = 7144793) B7144793
theorem B1257143 : Blo 834351 1257143 := bstep (se 1 (by rfl) ⟨942857, by rfl⟩ : syracuseStep 1257143 = 1885715) B1885715
theorem B1257353 : Blo 834351 1257353 := bstep (se 2 (by rfl) ⟨471507, by rfl⟩ : syracuseStep 1257353 = 943015) B943015
theorem B1880027 : Blo 834351 1880027 := bstep (se 1 (by rfl) ⟨1410020, by rfl⟩ : syracuseStep 1880027 = 2820041) B2820041
theorem B1880207 : Blo 834351 1880207 := bstep (se 1 (by rfl) ⟨1410155, by rfl⟩ : syracuseStep 1880207 = 2820311) B2820311
theorem B4763879 : Blo 834351 4763879 := bstep (se 1 (by rfl) ⟨3572909, by rfl⟩ : syracuseStep 4763879 = 7145819) B7145819
theorem B1880297 : Blo 834351 1880297 := bstep (se 2 (by rfl) ⟨705111, by rfl⟩ : syracuseStep 1880297 = 1410223) B1410223
theorem B27144497 : Blo 834351 27144497 := bstep (se 2 (by rfl) ⟨10179186, by rfl⟩ : syracuseStep 27144497 = 20358373) B20358373
theorem B1880423 : Blo 834351 1880423 := bstep (se 1 (by rfl) ⟨1410317, by rfl⟩ : syracuseStep 1880423 = 2820635) B2820635
theorem B6435607 : Blo 834351 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B5354369 : Blo 834351 5354369 := bstep (se 2 (by rfl) ⟨2007888, by rfl⟩ : syracuseStep 5354369 = 4015777) B4015777
theorem B15283081 : Blo 834351 15283081 := bstep (se 2 (by rfl) ⟨5731155, by rfl⟩ : syracuseStep 15283081 = 11462311) B11462311
theorem B1880999 : Blo 834351 1880999 := bstep (se 1 (by rfl) ⟨1410749, by rfl⟩ : syracuseStep 1880999 = 2821499) B2821499
theorem B1782739 : Blo 834351 1782739 := bstep (se 1 (by rfl) ⟨1337054, by rfl⟩ : syracuseStep 1782739 = 2674109) B2674109
theorem B2143273 : Blo 834351 2143273 := bstep (se 2 (by rfl) ⟨803727, by rfl⟩ : syracuseStep 2143273 = 1607455) B1607455
theorem B4764905 : Blo 834351 4764905 := bstep (se 2 (by rfl) ⟨1786839, by rfl⟩ : syracuseStep 4764905 = 3573679) B3573679
theorem B22918393 : Blo 834351 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B1586441 : Blo 834351 1586441 := bstep (se 2 (by rfl) ⟨594915, by rfl⟩ : syracuseStep 1586441 = 1189831) B1189831
theorem B7615853 : Blo 834351 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B44086999 : Blo 834351 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B1586927 : Blo 834351 1586927 := bstep (se 1 (by rfl) ⟨1190195, by rfl⟩ : syracuseStep 1586927 = 2380391) B2380391
theorem B2537257 : Blo 834351 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B1881935 : Blo 834351 1881935 := bstep (se 1 (by rfl) ⟨1411451, by rfl⟩ : syracuseStep 1881935 = 2822903) B2822903
theorem B4765655 : Blo 834351 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B7157915 : Blo 834351 7157915 := bstep (se 1 (by rfl) ⟨5368436, by rfl⟩ : syracuseStep 7157915 = 10736873) B10736873
theorem B1882295 : Blo 834351 1882295 := bstep (se 1 (by rfl) ⟨1411721, by rfl⟩ : syracuseStep 1882295 = 2823443) B2823443
theorem B4012411 : Blo 834351 4012411 := bstep (se 1 (by rfl) ⟨3009308, by rfl⟩ : syracuseStep 4012411 = 6018617) B6018617
theorem B1882655 : Blo 834351 1882655 := bstep (se 1 (by rfl) ⟨1411991, by rfl⟩ : syracuseStep 1882655 = 2823983) B2823983
theorem B3717775 : Blo 834351 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B48183983 : Blo 834351 48183983 := bstep (se 1 (by rfl) ⟨36137987, by rfl⟩ : syracuseStep 48183983 = 72275975) B72275975
theorem B1587899 : Blo 834351 1587899 := bstep (se 1 (by rfl) ⟨1190924, by rfl⟩ : syracuseStep 1587899 = 2381849) B2381849
theorem B1587937 : Blo 834351 1587937 := bstep (se 2 (by rfl) ⟨595476, by rfl⟩ : syracuseStep 1587937 = 1190953) B1190953
theorem B1784585 : Blo 834351 1784585 := bstep (se 2 (by rfl) ⟨669219, by rfl⟩ : syracuseStep 1784585 = 1338439) B1338439
theorem B1882889 : Blo 834351 1882889 := bstep (se 2 (by rfl) ⟨706083, by rfl⟩ : syracuseStep 1882889 = 1412167) B1412167
theorem B834375 : Blo 834351 834375 := bstep (se 1 (by rfl) ⟨625781, by rfl⟩ : syracuseStep 834375 = 1251563) B1251563
theorem B834415 : Blo 834351 834415 := bstep (se 1 (by rfl) ⟨625811, by rfl⟩ : syracuseStep 834415 = 1251623) B1251623
theorem B834471 : Blo 834351 834471 := bstep (se 1 (by rfl) ⟨625853, by rfl⟩ : syracuseStep 834471 = 1251707) B1251707
theorem B834651 : Blo 834351 834651 := bstep (se 1 (by rfl) ⟨625988, by rfl⟩ : syracuseStep 834651 = 1251977) B1251977
theorem B20331719 : Blo 834351 20331719 := bstep (se 1 (by rfl) ⟨15248789, by rfl⟩ : syracuseStep 20331719 = 30497579) B30497579
theorem B8273099 : Blo 834351 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B834767 : Blo 834351 834767 := bstep (se 1 (by rfl) ⟨626075, by rfl⟩ : syracuseStep 834767 = 1252151) B1252151
theorem B2112743 : Blo 834351 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B834791 : Blo 834351 834791 := bstep (se 1 (by rfl) ⟨626093, by rfl⟩ : syracuseStep 834791 = 1252187) B1252187
theorem B834887 : Blo 834351 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B1883465 : Blo 834351 1883465 := bstep (se 2 (by rfl) ⟨706299, by rfl⟩ : syracuseStep 1883465 = 1412599) B1412599
theorem B2538935 : Blo 834351 2538935 := bstep (se 1 (by rfl) ⟨1904201, by rfl⟩ : syracuseStep 2538935 = 3808403) B3808403
theorem B835023 : Blo 834351 835023 := bstep (se 1 (by rfl) ⟨626267, by rfl⟩ : syracuseStep 835023 = 1252535) B1252535
theorem B2113087 : Blo 834351 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B4767295 : Blo 834351 4767295 := bstep (se 1 (by rfl) ⟨3575471, by rfl⟩ : syracuseStep 4767295 = 7150943) B7150943
theorem B835183 : Blo 834351 835183 := bstep (se 1 (by rfl) ⟨626387, by rfl⟩ : syracuseStep 835183 = 1252775) B1252775
theorem B835239 : Blo 834351 835239 := bstep (se 1 (by rfl) ⟨626429, by rfl⟩ : syracuseStep 835239 = 1252859) B1252859
theorem B835303 : Blo 834351 835303 := bstep (se 1 (by rfl) ⟨626477, by rfl⟩ : syracuseStep 835303 = 1252955) B1252955
theorem B1883879 : Blo 834351 1883879 := bstep (se 1 (by rfl) ⟨1412909, by rfl⟩ : syracuseStep 1883879 = 2825819) B2825819
theorem B835359 : Blo 834351 835359 := bstep (se 1 (by rfl) ⟨626519, by rfl⟩ : syracuseStep 835359 = 1253039) B1253039
theorem B835439 : Blo 834351 835439 := bstep (se 1 (by rfl) ⟨626579, by rfl⟩ : syracuseStep 835439 = 1253159) B1253159
theorem B835495 : Blo 834351 835495 := bstep (se 1 (by rfl) ⟨626621, by rfl⟩ : syracuseStep 835495 = 1253243) B1253243
theorem B1589159 : Blo 834351 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B12861611 : Blo 834351 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B1884347 : Blo 834351 1884347 := bstep (se 1 (by rfl) ⟨1413260, by rfl⟩ : syracuseStep 1884347 = 2826521) B2826521
theorem B835775 : Blo 834351 835775 := bstep (se 1 (by rfl) ⟨626831, by rfl⟩ : syracuseStep 835775 = 1253663) B1253663
theorem B835791 : Blo 834351 835791 := bstep (se 1 (by rfl) ⟨626843, by rfl⟩ : syracuseStep 835791 = 1253687) B1253687
theorem B835839 : Blo 834351 835839 := bstep (se 1 (by rfl) ⟨626879, by rfl⟩ : syracuseStep 835839 = 1253759) B1253759
theorem B1884455 : Blo 834351 1884455 := bstep (se 1 (by rfl) ⟨1413341, by rfl⟩ : syracuseStep 1884455 = 2826683) B2826683
theorem B835887 : Blo 834351 835887 := bstep (se 1 (by rfl) ⟨626915, by rfl⟩ : syracuseStep 835887 = 1253831) B1253831
theorem B12042715 : Blo 834351 12042715 := bstep (se 1 (by rfl) ⟨9032036, by rfl⟩ : syracuseStep 12042715 = 18064073) B18064073
theorem B4768253 : Blo 834351 4768253 := bstep (se 3 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 4768253 = 1788095) B1788095
theorem B836123 : Blo 834351 836123 := bstep (se 1 (by rfl) ⟨627092, by rfl⟩ : syracuseStep 836123 = 1254185) B1254185
theorem B836127 : Blo 834351 836127 := bstep (se 1 (by rfl) ⟨627095, by rfl⟩ : syracuseStep 836127 = 1254191) B1254191
theorem B836207 : Blo 834351 836207 := bstep (se 1 (by rfl) ⟨627155, by rfl⟩ : syracuseStep 836207 = 1254311) B1254311
theorem B1884833 : Blo 834351 1884833 := bstep (se 2 (by rfl) ⟨706812, by rfl⟩ : syracuseStep 1884833 = 1413625) B1413625
theorem B836263 : Blo 834351 836263 := bstep (se 1 (by rfl) ⟨627197, by rfl⟩ : syracuseStep 836263 = 1254395) B1254395
theorem B836303 : Blo 834351 836303 := bstep (se 1 (by rfl) ⟨627227, by rfl⟩ : syracuseStep 836303 = 1254455) B1254455
theorem B836383 : Blo 834351 836383 := bstep (se 1 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 836383 = 1254575) B1254575
theorem B6767569 : Blo 834351 6767569 := bstep (se 2 (by rfl) ⟨2537838, by rfl⟩ : syracuseStep 6767569 = 5075677) B5075677
theorem B1885193 : Blo 834351 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B836655 : Blo 834351 836655 := bstep (se 1 (by rfl) ⟨627491, by rfl⟩ : syracuseStep 836655 = 1254983) B1254983
theorem B1885247 : Blo 834351 1885247 := bstep (se 1 (by rfl) ⟨1413935, by rfl⟩ : syracuseStep 1885247 = 2827871) B2827871
theorem B836719 : Blo 834351 836719 := bstep (se 1 (by rfl) ⟨627539, by rfl⟩ : syracuseStep 836719 = 1255079) B1255079
theorem B836775 : Blo 834351 836775 := bstep (se 1 (by rfl) ⟨627581, by rfl⟩ : syracuseStep 836775 = 1255163) B1255163
theorem B836799 : Blo 834351 836799 := bstep (se 1 (by rfl) ⟨627599, by rfl⟩ : syracuseStep 836799 = 1255199) B1255199
theorem B836831 : Blo 834351 836831 := bstep (se 1 (by rfl) ⟨627623, by rfl⟩ : syracuseStep 836831 = 1255247) B1255247
theorem B7128323 : Blo 834351 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B836911 : Blo 834351 836911 := bstep (se 1 (by rfl) ⟨627683, by rfl⟩ : syracuseStep 836911 = 1255367) B1255367
theorem B10700171 : Blo 834351 10700171 := bstep (se 1 (by rfl) ⟨8025128, by rfl⟩ : syracuseStep 10700171 = 16050257) B16050257
theorem B837147 : Blo 834351 837147 := bstep (se 1 (by rfl) ⟨627860, by rfl⟩ : syracuseStep 837147 = 1255721) B1255721
theorem B837151 : Blo 834351 837151 := bstep (se 1 (by rfl) ⟨627863, by rfl⟩ : syracuseStep 837151 = 1255727) B1255727
theorem B1590815 : Blo 834351 1590815 := bstep (se 1 (by rfl) ⟨1193111, by rfl⟩ : syracuseStep 1590815 = 2386223) B2386223
theorem B837311 : Blo 834351 837311 := bstep (se 1 (by rfl) ⟨627983, by rfl⟩ : syracuseStep 837311 = 1255967) B1255967
theorem B837567 : Blo 834351 837567 := bstep (se 1 (by rfl) ⟨628175, by rfl⟩ : syracuseStep 837567 = 1256351) B1256351
theorem B837599 : Blo 834351 837599 := bstep (se 1 (by rfl) ⟨628199, by rfl⟩ : syracuseStep 837599 = 1256399) B1256399
theorem B1886183 : Blo 834351 1886183 := bstep (se 1 (by rfl) ⟨1414637, by rfl⟩ : syracuseStep 1886183 = 2829275) B2829275
theorem B837659 : Blo 834351 837659 := bstep (se 1 (by rfl) ⟨628244, by rfl⟩ : syracuseStep 837659 = 1256489) B1256489
theorem B837663 : Blo 834351 837663 := bstep (se 1 (by rfl) ⟨628247, by rfl⟩ : syracuseStep 837663 = 1256495) B1256495
theorem B837679 : Blo 834351 837679 := bstep (se 1 (by rfl) ⟨628259, by rfl⟩ : syracuseStep 837679 = 1256519) B1256519
theorem B2115679 : Blo 834351 2115679 := bstep (se 1 (by rfl) ⟨1586759, by rfl⟩ : syracuseStep 2115679 = 3173519) B3173519
theorem B1591483 : Blo 834351 1591483 := bstep (se 1 (by rfl) ⟨1193612, by rfl⟩ : syracuseStep 1591483 = 2387225) B2387225
theorem B837855 : Blo 834351 837855 := bstep (se 1 (by rfl) ⟨628391, by rfl⟩ : syracuseStep 837855 = 1256783) B1256783
theorem B837915 : Blo 834351 837915 := bstep (se 1 (by rfl) ⟨628436, by rfl⟩ : syracuseStep 837915 = 1256873) B1256873
theorem B838015 : Blo 834351 838015 := bstep (se 1 (by rfl) ⟨628511, by rfl⟩ : syracuseStep 838015 = 1257023) B1257023
theorem B838191 : Blo 834351 838191 := bstep (se 1 (by rfl) ⟨628643, by rfl⟩ : syracuseStep 838191 = 1257287) B1257287
theorem B12864071 : Blo 834351 12864071 := bstep (se 1 (by rfl) ⟨9648053, by rfl⟩ : syracuseStep 12864071 = 19296107) B19296107
theorem B5720647 : Blo 834351 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B838247 : Blo 834351 838247 := bstep (se 1 (by rfl) ⟨628685, by rfl⟩ : syracuseStep 838247 = 1257371) B1257371
theorem B1789103 : Blo 834351 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B10702631 : Blo 834351 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B14307353 : Blo 834351 14307353 := bstep (se 2 (by rfl) ⟨5365257, by rfl⟩ : syracuseStep 14307353 = 10730515) B10730515
theorem B4018909 : Blo 834351 4018909 := bstep (se 3 (by rfl) ⟨753545, by rfl⟩ : syracuseStep 4018909 = 1507091) B1507091
theorem B4772627 : Blo 834351 4772627 := bstep (se 1 (by rfl) ⟨3579470, by rfl⟩ : syracuseStep 4772627 = 7158941) B7158941
theorem B938911 : Blo 834351 938911 := bstep (se 1 (by rfl) ⟨704183, by rfl⟩ : syracuseStep 938911 = 1408367) B1408367
theorem B15258563 : Blo 834351 15258563 := bstep (se 1 (by rfl) ⟨11443922, by rfl⟩ : syracuseStep 15258563 = 22887845) B22887845
theorem B4019159 : Blo 834351 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B939163 : Blo 834351 939163 := bstep (se 1 (by rfl) ⟨704372, by rfl⟩ : syracuseStep 939163 = 1408745) B1408745
theorem B27186529 : Blo 834351 27186529 := bstep (se 2 (by rfl) ⟨10194948, by rfl⟩ : syracuseStep 27186529 = 20389897) B20389897
theorem B939847 : Blo 834351 939847 := bstep (se 1 (by rfl) ⟨704885, by rfl⟩ : syracuseStep 939847 = 1409771) B1409771
theorem B6772571 : Blo 834351 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B2120033 : Blo 834351 2120033 := bstep (se 2 (by rfl) ⟨795012, by rfl⟩ : syracuseStep 2120033 = 1590025) B1590025
theorem B940495 : Blo 834351 940495 := bstep (se 1 (by rfl) ⟨705371, by rfl⟩ : syracuseStep 940495 = 1410743) B1410743
theorem B10705607 : Blo 834351 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B2120519 : Blo 834351 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B6347645 : Blo 834351 6347645 := bstep (se 3 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 6347645 = 2380367) B2380367
theorem B941287 : Blo 834351 941287 := bstep (se 1 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 941287 = 1411931) B1411931
theorem B6970835 : Blo 834351 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B2121491 : Blo 834351 2121491 := bstep (se 1 (by rfl) ⟨1591118, by rfl⟩ : syracuseStep 2121491 = 3182237) B3182237
theorem B2416495 : Blo 834351 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B941935 : Blo 834351 941935 := bstep (se 1 (by rfl) ⟨706451, by rfl⟩ : syracuseStep 941935 = 1412903) B1412903
theorem B2678683 : Blo 834351 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B3170771 : Blo 834351 3170771 := bstep (se 1 (by rfl) ⟨2378078, by rfl⟩ : syracuseStep 3170771 = 4756157) B4756157
theorem B942619 : Blo 834351 942619 := bstep (se 1 (by rfl) ⟨706964, by rfl⟩ : syracuseStep 942619 = 1413929) B1413929
theorem B942799 : Blo 834351 942799 := bstep (se 1 (by rfl) ⟨707099, by rfl⟩ : syracuseStep 942799 = 1414199) B1414199
theorem B4515347 : Blo 834351 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B1337465 : Blo 834351 1337465 := bstep (se 2 (by rfl) ⟨501549, by rfl⟩ : syracuseStep 1337465 = 1003099) B1003099
theorem B8022361 : Blo 834351 8022361 := bstep (se 2 (by rfl) ⟨3008385, by rfl⟩ : syracuseStep 8022361 = 6016771) B6016771
theorem B1699127 : Blo 834351 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B4025789 : Blo 834351 4025789 := bstep (se 3 (by rfl) ⟨754835, by rfl⟩ : syracuseStep 4025789 = 1509671) B1509671
theorem B51572537 : Blo 834351 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B1929343 : Blo 834351 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B7631333 : Blo 834351 7631333 := bstep (se 4 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 7631333 = 1430875) B1430875
theorem B12055223 : Blo 834351 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B1274687 : Blo 834351 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B9663943 : Blo 834351 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B3569305 : Blo 834351 3569305 := bstep (se 2 (by rfl) ⟨1338489, by rfl⟩ : syracuseStep 3569305 = 2676979) B2676979
theorem B22837049 : Blo 834351 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B6780779 : Blo 834351 6780779 := bstep (se 1 (by rfl) ⟨5085584, by rfl⟩ : syracuseStep 6780779 = 10171169) B10171169
theorem B3177089 : Blo 834351 3177089 := bstep (se 2 (by rfl) ⟨1191408, by rfl⟩ : syracuseStep 3177089 = 2382817) B2382817
theorem B2816747 : Blo 834351 2816747 := bstep (se 1 (by rfl) ⟨2112560, by rfl⟩ : syracuseStep 2816747 = 4225121) B4225121
theorem B2816855 : Blo 834351 2816855 := bstep (se 1 (by rfl) ⟨2112641, by rfl⟩ : syracuseStep 2816855 = 4225283) B4225283
theorem B4520863 : Blo 834351 4520863 := bstep (se 1 (by rfl) ⟨3390647, by rfl⟩ : syracuseStep 4520863 = 6781295) B6781295
theorem B2817665 : Blo 834351 2817665 := bstep (se 2 (by rfl) ⟨1056624, by rfl⟩ : syracuseStep 2817665 = 2113249) B2113249
theorem B5734223 : Blo 834351 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B2817935 : Blo 834351 2817935 := bstep (se 1 (by rfl) ⟨2113451, by rfl⟩ : syracuseStep 2817935 = 4226903) B4226903
theorem B6356879 : Blo 834351 6356879 := bstep (se 1 (by rfl) ⟨4767659, by rfl⟩ : syracuseStep 6356879 = 9535319) B9535319
theorem B3178835 : Blo 834351 3178835 := bstep (se 1 (by rfl) ⟨2384126, by rfl⟩ : syracuseStep 3178835 = 4768253) B4768253
theorem B16056953 : Blo 834351 16056953 := bstep (se 2 (by rfl) ⟨6021357, by rfl⟩ : syracuseStep 16056953 = 12042715) B12042715
theorem B4752215 : Blo 834351 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B8586071 : Blo 834351 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B16320311 : Blo 834351 16320311 := bstep (se 1 (by rfl) ⟨12240233, by rfl⟩ : syracuseStep 16320311 = 24480467) B24480467
theorem B1509607 : Blo 834351 1509607 := bstep (se 1 (by rfl) ⟨1132205, by rfl⟩ : syracuseStep 1509607 = 2264411) B2264411
theorem B10717757 : Blo 834351 10717757 := bstep (se 3 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 10717757 = 4019159) B4019159
theorem B22874723 : Blo 834351 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B9538235 : Blo 834351 9538235 := bstep (se 1 (by rfl) ⟨7153676, by rfl⟩ : syracuseStep 9538235 = 14307353) B14307353
theorem B2820905 : Blo 834351 2820905 := bstep (se 2 (by rfl) ⟨1057839, by rfl⟩ : syracuseStep 2820905 = 2115679) B2115679
theorem B3181751 : Blo 834351 3181751 := bstep (se 1 (by rfl) ⟨2386313, by rfl⟩ : syracuseStep 3181751 = 4772627) B4772627
theorem B16093313 : Blo 834351 16093313 := bstep (se 2 (by rfl) ⟨6034992, by rfl⟩ : syracuseStep 16093313 = 12069985) B12069985
theorem B2822363 : Blo 834351 2822363 := bstep (se 1 (by rfl) ⟨2116772, by rfl⟩ : syracuseStep 2822363 = 4233545) B4233545
theorem B1413355 : Blo 834351 1413355 := bstep (se 1 (by rfl) ⟨1060016, by rfl⟩ : syracuseStep 1413355 = 2120033) B2120033
theorem B1413679 : Blo 834351 1413679 := bstep (se 1 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 1413679 = 2120519) B2120519
theorem B4231763 : Blo 834351 4231763 := bstep (se 1 (by rfl) ⟨3173822, by rfl⟩ : syracuseStep 4231763 = 6347645) B6347645
theorem B1414327 : Blo 834351 1414327 := bstep (se 1 (by rfl) ⟨1060745, by rfl⟩ : syracuseStep 1414327 = 2121491) B2121491
theorem B176297249 : Blo 834351 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B3807271 : Blo 834351 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B1251791 : Blo 834351 1251791 := bstep (se 1 (by rfl) ⟨938843, by rfl⟩ : syracuseStep 1251791 = 1877687) B1877687
theorem B1251881 : Blo 834351 1251881 := bstep (se 2 (by rfl) ⟨469455, by rfl⟩ : syracuseStep 1251881 = 938911) B938911
theorem B122231429 : Blo 834351 122231429 := bstep (se 4 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 122231429 = 22918393) B22918393
theorem B2857697 : Blo 834351 2857697 := bstep (se 2 (by rfl) ⟨1071636, by rfl⟩ : syracuseStep 2857697 = 2143273) B2143273
theorem B1252091 : Blo 834351 1252091 := bstep (se 1 (by rfl) ⟨939068, by rfl⟩ : syracuseStep 1252091 = 1878137) B1878137
theorem B891643 : Blo 834351 891643 := bstep (se 1 (by rfl) ⟨668732, by rfl⟩ : syracuseStep 891643 = 1337465) B1337465
theorem B2824955 : Blo 834351 2824955 := bstep (se 1 (by rfl) ⟨2118716, by rfl⟩ : syracuseStep 2824955 = 4237433) B4237433
theorem B1252217 : Blo 834351 1252217 := bstep (se 2 (by rfl) ⟨469581, by rfl⟩ : syracuseStep 1252217 = 939163) B939163
theorem B36248705 : Blo 834351 36248705 := bstep (se 2 (by rfl) ⟨13593264, by rfl⟩ : syracuseStep 36248705 = 27186529) B27186529
theorem B12885257 : Blo 834351 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B4759073 : Blo 834351 4759073 := bstep (se 2 (by rfl) ⟨1784652, by rfl⟩ : syracuseStep 4759073 = 3569305) B3569305
theorem B1252967 : Blo 834351 1252967 := bstep (se 1 (by rfl) ⟨939725, by rfl⟩ : syracuseStep 1252967 = 1879451) B1879451
theorem B3383009 : Blo 834351 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B1253129 : Blo 834351 1253129 := bstep (se 2 (by rfl) ⟨469923, by rfl⟩ : syracuseStep 1253129 = 939847) B939847
theorem B34381691 : Blo 834351 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B1253351 : Blo 834351 1253351 := bstep (se 1 (by rfl) ⟨940013, by rfl⟩ : syracuseStep 1253351 = 1880027) B1880027
theorem B1253471 : Blo 834351 1253471 := bstep (se 1 (by rfl) ⟨940103, by rfl⟩ : syracuseStep 1253471 = 1880207) B1880207
theorem B5087357 : Blo 834351 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B1253531 : Blo 834351 1253531 := bstep (se 1 (by rfl) ⟨940148, by rfl⟩ : syracuseStep 1253531 = 1880297) B1880297
theorem B18096331 : Blo 834351 18096331 := bstep (se 1 (by rfl) ⟨13572248, by rfl⟩ : syracuseStep 18096331 = 27144497) B27144497
theorem B1253615 : Blo 834351 1253615 := bstep (se 1 (by rfl) ⟨940211, by rfl⟩ : syracuseStep 1253615 = 1880423) B1880423
theorem B5087555 : Blo 834351 5087555 := bstep (se 1 (by rfl) ⟨3815666, by rfl⟩ : syracuseStep 5087555 = 7631333) B7631333
theorem B8036815 : Blo 834351 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B5349881 : Blo 834351 5349881 := bstep (se 2 (by rfl) ⟨2006205, by rfl⟩ : syracuseStep 5349881 = 4012411) B4012411
theorem B1253993 : Blo 834351 1253993 := bstep (se 2 (by rfl) ⟨470247, by rfl⟩ : syracuseStep 1253993 = 940495) B940495
theorem B1253999 : Blo 834351 1253999 := bstep (se 1 (by rfl) ⟨940499, by rfl⟩ : syracuseStep 1253999 = 1880999) B1880999
theorem B1057627 : Blo 834351 1057627 := bstep (se 1 (by rfl) ⟨793220, by rfl⟩ : syracuseStep 1057627 = 1586441) B1586441
theorem B4957033 : Blo 834351 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B1057951 : Blo 834351 1057951 := bstep (se 1 (by rfl) ⟨793463, by rfl⟩ : syracuseStep 1057951 = 1586927) B1586927
theorem B1254623 : Blo 834351 1254623 := bstep (se 1 (by rfl) ⟨940967, by rfl⟩ : syracuseStep 1254623 = 1881935) B1881935
theorem B1254863 : Blo 834351 1254863 := bstep (se 1 (by rfl) ⟨941147, by rfl⟩ : syracuseStep 1254863 = 1882295) B1882295
theorem B1255049 : Blo 834351 1255049 := bstep (se 2 (by rfl) ⟨470643, by rfl⟩ : syracuseStep 1255049 = 941287) B941287
theorem B1255103 : Blo 834351 1255103 := bstep (se 1 (by rfl) ⟨941327, by rfl⟩ : syracuseStep 1255103 = 1882655) B1882655
theorem B32122655 : Blo 834351 32122655 := bstep (se 1 (by rfl) ⟨24091991, by rfl⟩ : syracuseStep 32122655 = 48183983) B48183983
theorem B1058599 : Blo 834351 1058599 := bstep (se 1 (by rfl) ⟨793949, by rfl⟩ : syracuseStep 1058599 = 1587899) B1587899
theorem B1877831 : Blo 834351 1877831 := bstep (se 1 (by rfl) ⟨1408373, by rfl⟩ : syracuseStep 1877831 = 2816747) B2816747
theorem B1189723 : Blo 834351 1189723 := bstep (se 1 (by rfl) ⟨892292, by rfl⟩ : syracuseStep 1189723 = 1784585) B1784585
theorem B1255259 : Blo 834351 1255259 := bstep (se 1 (by rfl) ⟨941444, by rfl⟩ : syracuseStep 1255259 = 1882889) B1882889
theorem B68003717 : Blo 834351 68003717 := bstep (se 4 (by rfl) ⟨6375348, by rfl⟩ : syracuseStep 68003717 = 12750697) B12750697
theorem B1877903 : Blo 834351 1877903 := bstep (se 1 (by rfl) ⟨1408427, by rfl⟩ : syracuseStep 1877903 = 2816855) B2816855
theorem B5515399 : Blo 834351 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B1255643 : Blo 834351 1255643 := bstep (se 1 (by rfl) ⟨941732, by rfl⟩ : syracuseStep 1255643 = 1883465) B1883465
theorem B1878443 : Blo 834351 1878443 := bstep (se 1 (by rfl) ⟨1408832, by rfl⟩ : syracuseStep 1878443 = 2817665) B2817665
theorem B4237757 : Blo 834351 4237757 := bstep (se 3 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 4237757 = 1589159) B1589159
theorem B3221993 : Blo 834351 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B1255913 : Blo 834351 1255913 := bstep (se 2 (by rfl) ⟨470967, by rfl⟩ : syracuseStep 1255913 = 941935) B941935
theorem B1255919 : Blo 834351 1255919 := bstep (se 1 (by rfl) ⟨941939, by rfl⟩ : syracuseStep 1255919 = 1883879) B1883879
theorem B1878623 : Blo 834351 1878623 := bstep (se 1 (by rfl) ⟨1408967, by rfl⟩ : syracuseStep 1878623 = 2817935) B2817935
theorem B4237919 : Blo 834351 4237919 := bstep (se 1 (by rfl) ⟨3178439, by rfl⟩ : syracuseStep 4237919 = 6356879) B6356879
theorem B1256231 : Blo 834351 1256231 := bstep (se 1 (by rfl) ⟨942173, by rfl⟩ : syracuseStep 1256231 = 1884347) B1884347
theorem B1256303 : Blo 834351 1256303 := bstep (se 1 (by rfl) ⟨942227, by rfl⟩ : syracuseStep 1256303 = 1884455) B1884455
theorem B1878983 : Blo 834351 1878983 := bstep (se 1 (by rfl) ⟨1409237, by rfl⟩ : syracuseStep 1878983 = 2818475) B2818475
theorem B1256555 : Blo 834351 1256555 := bstep (se 1 (by rfl) ⟨942416, by rfl⟩ : syracuseStep 1256555 = 1884833) B1884833
theorem B1879343 : Blo 834351 1879343 := bstep (se 1 (by rfl) ⟨1409507, by rfl⟩ : syracuseStep 1879343 = 2819015) B2819015
theorem B1879379 : Blo 834351 1879379 := bstep (se 1 (by rfl) ⟨1409534, by rfl⟩ : syracuseStep 1879379 = 2819069) B2819069
theorem B1256795 : Blo 834351 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B1191289 : Blo 834351 1191289 := bstep (se 2 (by rfl) ⟨446733, by rfl⟩ : syracuseStep 1191289 = 893467) B893467
theorem B1256825 : Blo 834351 1256825 := bstep (se 2 (by rfl) ⟨471309, by rfl⟩ : syracuseStep 1256825 = 942619) B942619
theorem B1256831 : Blo 834351 1256831 := bstep (se 1 (by rfl) ⟨942623, by rfl⟩ : syracuseStep 1256831 = 1885247) B1885247
theorem B8039891 : Blo 834351 8039891 := bstep (se 1 (by rfl) ⟨6029918, by rfl⟩ : syracuseStep 8039891 = 12059837) B12059837
theorem B1879631 : Blo 834351 1879631 := bstep (se 1 (by rfl) ⟨1409723, by rfl⟩ : syracuseStep 1879631 = 2819447) B2819447
theorem B1257065 : Blo 834351 1257065 := bstep (se 2 (by rfl) ⟨471399, by rfl⟩ : syracuseStep 1257065 = 942799) B942799
theorem B1060543 : Blo 834351 1060543 := bstep (se 1 (by rfl) ⟨795407, by rfl⟩ : syracuseStep 1060543 = 1590815) B1590815
theorem B1879919 : Blo 834351 1879919 := bstep (se 1 (by rfl) ⟨1409939, by rfl⟩ : syracuseStep 1879919 = 2819879) B2819879
theorem B1257455 : Blo 834351 1257455 := bstep (se 1 (by rfl) ⟨943091, by rfl⟩ : syracuseStep 1257455 = 1886183) B1886183
theorem B1880171 : Blo 834351 1880171 := bstep (se 1 (by rfl) ⟨1410128, by rfl⟩ : syracuseStep 1880171 = 2820257) B2820257
theorem B2011243 : Blo 834351 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B1880351 : Blo 834351 1880351 := bstep (se 1 (by rfl) ⟨1410263, by rfl⟩ : syracuseStep 1880351 = 2820527) B2820527
theorem B12038615 : Blo 834351 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B1192735 : Blo 834351 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B1881071 : Blo 834351 1881071 := bstep (se 1 (by rfl) ⟨1410803, by rfl⟩ : syracuseStep 1881071 = 2821607) B2821607
theorem B11580545 : Blo 834351 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B10696481 : Blo 834351 10696481 := bstep (se 2 (by rfl) ⟨4011180, by rfl⟩ : syracuseStep 10696481 = 8022361) B8022361
theorem B6338411 : Blo 834351 6338411 := bstep (se 1 (by rfl) ⟨4753808, by rfl⟩ : syracuseStep 6338411 = 9507617) B9507617
theorem B10172375 : Blo 834351 10172375 := bstep (se 1 (by rfl) ⟨7629281, by rfl⟩ : syracuseStep 10172375 = 15258563) B15258563
theorem B834495 : Blo 834351 834495 := bstep (se 1 (by rfl) ⟨625871, by rfl⟩ : syracuseStep 834495 = 1251743) B1251743
theorem B834543 : Blo 834351 834543 := bstep (se 1 (by rfl) ⟨625907, by rfl⟩ : syracuseStep 834543 = 1251815) B1251815
theorem B4242617 : Blo 834351 4242617 := bstep (se 2 (by rfl) ⟨1590981, by rfl⟩ : syracuseStep 4242617 = 3181963) B3181963
theorem B835039 : Blo 834351 835039 := bstep (se 1 (by rfl) ⟨626279, by rfl⟩ : syracuseStep 835039 = 1252559) B1252559
theorem B835119 : Blo 834351 835119 := bstep (se 1 (by rfl) ⟨626339, by rfl⟩ : syracuseStep 835119 = 1252679) B1252679
theorem B835227 : Blo 834351 835227 := bstep (se 1 (by rfl) ⟨626420, by rfl⟩ : syracuseStep 835227 = 1252841) B1252841
theorem B835323 : Blo 834351 835323 := bstep (se 1 (by rfl) ⟨626492, by rfl⟩ : syracuseStep 835323 = 1252985) B1252985
theorem B36093701 : Blo 834351 36093701 := bstep (se 4 (by rfl) ⟨3383784, by rfl⟩ : syracuseStep 36093701 = 6767569) B6767569
theorem B1883987 : Blo 834351 1883987 := bstep (se 1 (by rfl) ⟨1412990, by rfl⟩ : syracuseStep 1883987 = 2825981) B2825981
theorem B835487 : Blo 834351 835487 := bstep (se 1 (by rfl) ⟨626615, by rfl⟩ : syracuseStep 835487 = 1253231) B1253231
theorem B2572457 : Blo 834351 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B5423399 : Blo 834351 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B4243751 : Blo 834351 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B2113847 : Blo 834351 2113847 := bstep (se 1 (by rfl) ⟨1585385, by rfl⟩ : syracuseStep 2113847 = 3170771) B3170771
theorem B835943 : Blo 834351 835943 := bstep (se 1 (by rfl) ⟨626957, by rfl⟩ : syracuseStep 835943 = 1253915) B1253915
theorem B836063 : Blo 834351 836063 := bstep (se 1 (by rfl) ⟨627047, by rfl⟩ : syracuseStep 836063 = 1254095) B1254095
theorem B836071 : Blo 834351 836071 := bstep (se 1 (by rfl) ⟨627053, by rfl⟩ : syracuseStep 836071 = 1254107) B1254107
theorem B836347 : Blo 834351 836347 := bstep (se 1 (by rfl) ⟨627260, by rfl⟩ : syracuseStep 836347 = 1254521) B1254521
theorem B1884923 : Blo 834351 1884923 := bstep (se 1 (by rfl) ⟨1413692, by rfl⟩ : syracuseStep 1884923 = 2827385) B2827385
theorem B5358545 : Blo 834351 5358545 := bstep (se 2 (by rfl) ⟨2009454, by rfl⟩ : syracuseStep 5358545 = 4018909) B4018909
theorem B2376985 : Blo 834351 2376985 := bstep (se 2 (by rfl) ⟨891369, by rfl⟩ : syracuseStep 2376985 = 1782739) B1782739
theorem B836927 : Blo 834351 836927 := bstep (se 1 (by rfl) ⟨627695, by rfl⟩ : syracuseStep 836927 = 1255391) B1255391
theorem B836935 : Blo 834351 836935 := bstep (se 1 (by rfl) ⟨627701, by rfl⟩ : syracuseStep 836935 = 1255403) B1255403
theorem B836967 : Blo 834351 836967 := bstep (se 1 (by rfl) ⟨627725, by rfl⟩ : syracuseStep 836967 = 1255451) B1255451
theorem B837211 : Blo 834351 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B1886255 : Blo 834351 1886255 := bstep (se 1 (by rfl) ⟨1414691, by rfl⟩ : syracuseStep 1886255 = 2829383) B2829383
theorem B837839 : Blo 834351 837839 := bstep (se 1 (by rfl) ⟨628379, by rfl⟩ : syracuseStep 837839 = 1256759) B1256759
theorem B1132751 : Blo 834351 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B837951 : Blo 834351 837951 := bstep (se 1 (by rfl) ⟨628463, by rfl⟩ : syracuseStep 837951 = 1256927) B1256927
theorem B838095 : Blo 834351 838095 := bstep (se 1 (by rfl) ⟨628571, by rfl⟩ : syracuseStep 838095 = 1257143) B1257143
theorem B838235 : Blo 834351 838235 := bstep (se 1 (by rfl) ⟨628676, by rfl⟩ : syracuseStep 838235 = 1257353) B1257353
theorem B5361005 : Blo 834351 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B2117249 : Blo 834351 2117249 := bstep (se 2 (by rfl) ⟨793968, by rfl⟩ : syracuseStep 2117249 = 1587937) B1587937
theorem B15224699 : Blo 834351 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B4771943 : Blo 834351 4771943 := bstep (se 1 (by rfl) ⟨3578957, by rfl⟩ : syracuseStep 4771943 = 7157915) B7157915
theorem B2118059 : Blo 834351 2118059 := bstep (se 1 (by rfl) ⟨1588544, by rfl⟩ : syracuseStep 2118059 = 3177089) B3177089
theorem B13554479 : Blo 834351 13554479 := bstep (se 1 (by rfl) ⟨10165859, by rfl⟩ : syracuseStep 13554479 = 20331719) B20331719
theorem B1692623 : Blo 834351 1692623 := bstep (se 1 (by rfl) ⟨1269467, by rfl⟩ : syracuseStep 1692623 = 2538935) B2538935
theorem B3822815 : Blo 834351 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B8574407 : Blo 834351 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B2119547 : Blo 834351 2119547 := bstep (se 1 (by rfl) ⟨1589660, by rfl⟩ : syracuseStep 2119547 = 3179321) B3179321
theorem B2119567 : Blo 834351 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B2119871 : Blo 834351 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B7133447 : Blo 834351 7133447 := bstep (se 1 (by rfl) ⟨5350085, by rfl⟩ : syracuseStep 7133447 = 10700171) B10700171
theorem B940315 : Blo 834351 940315 := bstep (se 1 (by rfl) ⟨705236, by rfl⟩ : syracuseStep 940315 = 1410473) B1410473
theorem B51534863 : Blo 834351 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B8576047 : Blo 834351 8576047 := bstep (se 1 (by rfl) ⟨6432035, by rfl⟩ : syracuseStep 8576047 = 12864071) B12864071
theorem B2383091 : Blo 834351 2383091 := bstep (se 1 (by rfl) ⟨1787318, by rfl⟩ : syracuseStep 2383091 = 3574637) B3574637
theorem B9526571 : Blo 834351 9526571 := bstep (se 1 (by rfl) ⟨7144928, by rfl⟩ : syracuseStep 9526571 = 14289857) B14289857
theorem B7135087 : Blo 834351 7135087 := bstep (se 1 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 7135087 = 10702631) B10702631
theorem B942151 : Blo 834351 942151 := bstep (se 1 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 942151 = 1413227) B1413227
theorem B2121835 : Blo 834351 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B2121977 : Blo 834351 2121977 := bstep (se 2 (by rfl) ⟨795741, by rfl⟩ : syracuseStep 2121977 = 1591483) B1591483
theorem B1204895 : Blo 834351 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B7627529 : Blo 834351 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B2384765 : Blo 834351 2384765 := bstep (se 3 (by rfl) ⟨447143, by rfl⟩ : syracuseStep 2384765 = 894287) B894287
theorem B943087 : Blo 834351 943087 := bstep (se 1 (by rfl) ⟨707315, by rfl⟩ : syracuseStep 943087 = 1414631) B1414631
theorem B4515047 : Blo 834351 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B7137071 : Blo 834351 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B9529487 : Blo 834351 9529487 := bstep (se 1 (by rfl) ⟨7147115, by rfl⟩ : syracuseStep 9529487 = 14294231) B14294231
theorem B4647223 : Blo 834351 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B2386655 : Blo 834351 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B3173687 : Blo 834351 3173687 := bstep (se 1 (by rfl) ⟨2380265, by rfl⟩ : syracuseStep 3173687 = 4760531) B4760531
theorem B1338695 : Blo 834351 1338695 := bstep (se 1 (by rfl) ⟨1004021, by rfl⟩ : syracuseStep 1338695 = 2008043) B2008043
theorem B3010231 : Blo 834351 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B8580809 : Blo 834351 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B20377441 : Blo 834351 20377441 := bstep (se 2 (by rfl) ⟨7641540, by rfl⟩ : syracuseStep 20377441 = 15283081) B15283081
theorem B10842839 : Blo 834351 10842839 := bstep (se 1 (by rfl) ⟨8132129, by rfl⟩ : syracuseStep 10842839 = 16264259) B16264259
theorem B58782665 : Blo 834351 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B2683859 : Blo 834351 2683859 := bstep (se 1 (by rfl) ⟨2012894, by rfl⟩ : syracuseStep 2683859 = 4025789) B4025789
theorem B3175463 : Blo 834351 3175463 := bstep (se 1 (by rfl) ⟨2381597, by rfl⟩ : syracuseStep 3175463 = 4763195) B4763195
theorem B3175919 : Blo 834351 3175919 := bstep (se 1 (by rfl) ⟨2381939, by rfl⟩ : syracuseStep 3175919 = 4763879) B4763879
theorem B849791 : Blo 834351 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B3569579 : Blo 834351 3569579 := bstep (se 1 (by rfl) ⟨2677184, by rfl⟩ : syracuseStep 3569579 = 5354369) B5354369
theorem B3176603 : Blo 834351 3176603 := bstep (se 1 (by rfl) ⟨2382452, by rfl⟩ : syracuseStep 3176603 = 4764905) B4764905
theorem B5077235 : Blo 834351 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B6027817 : Blo 834351 6027817 := bstep (se 2 (by rfl) ⟨2260431, by rfl⟩ : syracuseStep 6027817 = 4520863) B4520863
theorem B4520519 : Blo 834351 4520519 := bstep (se 1 (by rfl) ⟨3390389, by rfl⟩ : syracuseStep 4520519 = 6780779) B6780779
theorem B3177103 : Blo 834351 3177103 := bstep (se 1 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 3177103 = 4765655) B4765655
theorem B2817449 : Blo 834351 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B6356393 : Blo 834351 6356393 := bstep (se 2 (by rfl) ⟨2383647, by rfl⟩ : syracuseStep 6356393 = 4767295) B4767295
theorem B1408495 : Blo 834351 1408495 := bstep (se 1 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 1408495 = 2112743) B2112743
theorem B3571577 : Blo 834351 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B1409231 : Blo 834351 1409231 := bstep (se 1 (by rfl) ⟨1056923, by rfl⟩ : syracuseStep 1409231 = 2113847) B2113847
theorem B10715753 : Blo 834351 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B3572363 : Blo 834351 3572363 := bstep (se 1 (by rfl) ⟨2679272, by rfl⟩ : syracuseStep 3572363 = 5358545) B5358545
theorem B1410169 : Blo 834351 1410169 := bstep (se 2 (by rfl) ⟨528813, by rfl⟩ : syracuseStep 1410169 = 1057627) B1057627
theorem B10880207 : Blo 834351 10880207 := bstep (se 1 (by rfl) ⟨8160155, by rfl⟩ : syracuseStep 10880207 = 16320311) B16320311
theorem B1410601 : Blo 834351 1410601 := bstep (se 2 (by rfl) ⟨528975, by rfl⟩ : syracuseStep 1410601 = 1057951) B1057951
theorem B7145171 : Blo 834351 7145171 := bstep (se 1 (by rfl) ⟨5358878, by rfl⟩ : syracuseStep 7145171 = 10717757) B10717757
theorem B3213053 : Blo 834351 3213053 := bstep (se 3 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 3213053 = 1204895) B1204895
theorem B6358823 : Blo 834351 6358823 := bstep (se 1 (by rfl) ⟨4769117, by rfl⟩ : syracuseStep 6358823 = 9538235) B9538235
theorem B3574003 : Blo 834351 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B1411465 : Blo 834351 1411465 := bstep (se 2 (by rfl) ⟨529299, by rfl⟩ : syracuseStep 1411465 = 1058599) B1058599
theorem B1411499 : Blo 834351 1411499 := bstep (se 1 (by rfl) ⟨1058624, by rfl⟩ : syracuseStep 1411499 = 2117249) B2117249
theorem B3181295 : Blo 834351 3181295 := bstep (se 1 (by rfl) ⟨2385971, by rfl⟩ : syracuseStep 3181295 = 4771943) B4771943
theorem B1412039 : Blo 834351 1412039 := bstep (se 1 (by rfl) ⟨1059029, by rfl⟩ : syracuseStep 1412039 = 2118059) B2118059
theorem B2821175 : Blo 834351 2821175 := bstep (se 1 (by rfl) ⟨2115881, by rfl⟩ : syracuseStep 2821175 = 4231763) B4231763
theorem B10194173 : Blo 834351 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B1413031 : Blo 834351 1413031 := bstep (se 1 (by rfl) ⟨1059773, by rfl⟩ : syracuseStep 1413031 = 2119547) B2119547
theorem B1413247 : Blo 834351 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B6361253 : Blo 834351 6361253 := bstep (se 4 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 6361253 = 1192735) B1192735
theorem B4755631 : Blo 834351 4755631 := bstep (se 1 (by rfl) ⟨3566723, by rfl⟩ : syracuseStep 4755631 = 7133447) B7133447
theorem B1905131 : Blo 834351 1905131 := bstep (se 1 (by rfl) ⟨1428848, by rfl⟩ : syracuseStep 1905131 = 2857697) B2857697
theorem B8590171 : Blo 834351 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B1414057 : Blo 834351 1414057 := bstep (se 2 (by rfl) ⟨530271, by rfl⟩ : syracuseStep 1414057 = 1060543) B1060543
theorem B2266109 : Blo 834351 2266109 := bstep (se 3 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 2266109 = 849791) B849791
theorem B181343245 : Blo 834351 181343245 := bstep (se 3 (by rfl) ⟨34001858, by rfl⟩ : syracuseStep 181343245 = 68003717) B68003717
theorem B27169921 : Blo 834351 27169921 := bstep (se 2 (by rfl) ⟨10188720, by rfl⟩ : syracuseStep 27169921 = 20377441) B20377441
theorem B1414651 : Blo 834351 1414651 := bstep (se 1 (by rfl) ⟨1060988, by rfl⟩ : syracuseStep 1414651 = 2121977) B2121977
theorem B5085019 : Blo 834351 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B3020669 : Blo 834351 3020669 := bstep (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) B1132751
theorem B4758047 : Blo 834351 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B1251887 : Blo 834351 1251887 := bstep (se 1 (by rfl) ⟨938915, by rfl⟩ : syracuseStep 1251887 = 1877831) B1877831
theorem B1251935 : Blo 834351 1251935 := bstep (se 1 (by rfl) ⟨938951, by rfl⟩ : syracuseStep 1251935 = 1877903) B1877903
theorem B1252295 : Blo 834351 1252295 := bstep (se 1 (by rfl) ⟨939221, by rfl⟩ : syracuseStep 1252295 = 1878443) B1878443
theorem B2825171 : Blo 834351 2825171 := bstep (se 1 (by rfl) ⟨2118878, by rfl⟩ : syracuseStep 2825171 = 4237757) B4237757
theorem B1252415 : Blo 834351 1252415 := bstep (se 1 (by rfl) ⟨939311, by rfl⟩ : syracuseStep 1252415 = 1878623) B1878623
theorem B2825279 : Blo 834351 2825279 := bstep (se 1 (by rfl) ⟨2118959, by rfl⟩ : syracuseStep 2825279 = 4237919) B4237919
theorem B1252655 : Blo 834351 1252655 := bstep (se 1 (by rfl) ⟨939491, by rfl⟩ : syracuseStep 1252655 = 1878983) B1878983
theorem B1252895 : Blo 834351 1252895 := bstep (se 1 (by rfl) ⟨939671, by rfl⟩ : syracuseStep 1252895 = 1879343) B1879343
theorem B892463 : Blo 834351 892463 := bstep (se 1 (by rfl) ⟨669347, by rfl⟩ : syracuseStep 892463 = 1338695) B1338695
theorem B1252919 : Blo 834351 1252919 := bstep (se 1 (by rfl) ⟨939689, by rfl⟩ : syracuseStep 1252919 = 1879379) B1879379
theorem B1253087 : Blo 834351 1253087 := bstep (se 1 (by rfl) ⟨939815, by rfl⟩ : syracuseStep 1253087 = 1879631) B1879631
theorem B2826089 : Blo 834351 2826089 := bstep (se 2 (by rfl) ⟨1059783, by rfl⟩ : syracuseStep 2826089 = 2119567) B2119567
theorem B1253279 : Blo 834351 1253279 := bstep (se 1 (by rfl) ⟨939959, by rfl⟩ : syracuseStep 1253279 = 1879919) B1879919
theorem B1253447 : Blo 834351 1253447 := bstep (se 1 (by rfl) ⟨940085, by rfl⟩ : syracuseStep 1253447 = 1880171) B1880171
theorem B1253567 : Blo 834351 1253567 := bstep (se 1 (by rfl) ⟨940175, by rfl⟩ : syracuseStep 1253567 = 1880351) B1880351
theorem B1253753 : Blo 834351 1253753 := bstep (se 2 (by rfl) ⟨470157, by rfl⟩ : syracuseStep 1253753 = 940315) B940315
theorem B1254047 : Blo 834351 1254047 := bstep (se 1 (by rfl) ⟨940535, by rfl⟩ : syracuseStep 1254047 = 1881071) B1881071
theorem B8037089 : Blo 834351 8037089 := bstep (se 2 (by rfl) ⟨3013908, by rfl⟩ : syracuseStep 8037089 = 6027817) B6027817
theorem B4236137 : Blo 834351 4236137 := bstep (se 2 (by rfl) ⟨1588551, by rfl⟩ : syracuseStep 4236137 = 3177103) B3177103
theorem B1188857 : Blo 834351 1188857 := bstep (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) B891643
theorem B3384823 : Blo 834351 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B1877993 : Blo 834351 1877993 := bstep (se 2 (by rfl) ⟨704247, by rfl⟩ : syracuseStep 1877993 = 1408495) B1408495
theorem B2828411 : Blo 834351 2828411 := bstep (se 1 (by rfl) ⟨2121308, by rfl⟩ : syracuseStep 2828411 = 4242617) B4242617
theorem B1878299 : Blo 834351 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B4237595 : Blo 834351 4237595 := bstep (se 1 (by rfl) ⟨3178196, by rfl⟩ : syracuseStep 4237595 = 6356393) B6356393
theorem B9513449 : Blo 834351 9513449 := bstep (se 2 (by rfl) ⟨3567543, by rfl⟩ : syracuseStep 9513449 = 7135087) B7135087
theorem B24062467 : Blo 834351 24062467 := bstep (se 1 (by rfl) ⟨18046850, by rfl⟩ : syracuseStep 24062467 = 36093701) B36093701
theorem B1255991 : Blo 834351 1255991 := bstep (se 1 (by rfl) ⟨941993, by rfl⟩ : syracuseStep 1255991 = 1883987) B1883987
theorem B1256201 : Blo 834351 1256201 := bstep (se 2 (by rfl) ⟨471075, by rfl⟩ : syracuseStep 1256201 = 942151) B942151
theorem B2829113 : Blo 834351 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B3615599 : Blo 834351 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B2829167 : Blo 834351 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B24128441 : Blo 834351 24128441 := bstep (se 2 (by rfl) ⟨9048165, by rfl⟩ : syracuseStep 24128441 = 18096331) B18096331
theorem B6859885 : Blo 834351 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B1256615 : Blo 834351 1256615 := bstep (se 1 (by rfl) ⟨942461, by rfl⟩ : syracuseStep 1256615 = 1884923) B1884923
theorem B1257449 : Blo 834351 1257449 := bstep (se 2 (by rfl) ⟨471543, by rfl⟩ : syracuseStep 1257449 = 943087) B943087
theorem B1257503 : Blo 834351 1257503 := bstep (se 1 (by rfl) ⟨943127, by rfl⟩ : syracuseStep 1257503 = 1886255) B1886255
theorem B24785189 : Blo 834351 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B15249815 : Blo 834351 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B1880603 : Blo 834351 1880603 := bstep (se 1 (by rfl) ⟨1410452, by rfl⟩ : syracuseStep 1880603 = 2820905) B2820905
theorem B1586297 : Blo 834351 1586297 := bstep (se 2 (by rfl) ⟨594861, by rfl⟩ : syracuseStep 1586297 = 1189723) B1189723
theorem B7156957 : Blo 834351 7156957 := bstep (se 3 (by rfl) ⟨1341929, by rfl⟩ : syracuseStep 7156957 = 2683859) B2683859
theorem B10728875 : Blo 834351 10728875 := bstep (se 1 (by rfl) ⟨8046656, by rfl⟩ : syracuseStep 10728875 = 16093313) B16093313
theorem B1881575 : Blo 834351 1881575 := bstep (se 1 (by rfl) ⟨1411181, by rfl⟩ : syracuseStep 1881575 = 2822363) B2822363
theorem B7353865 : Blo 834351 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B5716271 : Blo 834351 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B834527 : Blo 834351 834527 := bstep (se 1 (by rfl) ⟨625895, by rfl⟩ : syracuseStep 834527 = 1251791) B1251791
theorem B834587 : Blo 834351 834587 := bstep (se 1 (by rfl) ⟨625940, by rfl⟩ : syracuseStep 834587 = 1251881) B1251881
theorem B1588385 : Blo 834351 1588385 := bstep (se 2 (by rfl) ⟨595644, by rfl⟩ : syracuseStep 1588385 = 1191289) B1191289
theorem B834727 : Blo 834351 834727 := bstep (se 1 (by rfl) ⟨626045, by rfl⟩ : syracuseStep 834727 = 1252091) B1252091
theorem B1883303 : Blo 834351 1883303 := bstep (se 1 (by rfl) ⟨1412477, by rfl⟩ : syracuseStep 1883303 = 2824955) B2824955
theorem B834811 : Blo 834351 834811 := bstep (se 1 (by rfl) ⟨626108, by rfl⟩ : syracuseStep 834811 = 1252217) B1252217
theorem B34356575 : Blo 834351 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B24165803 : Blo 834351 24165803 := bstep (se 1 (by rfl) ⟨18124352, by rfl⟩ : syracuseStep 24165803 = 36248705) B36248705
theorem B1588727 : Blo 834351 1588727 := bstep (se 1 (by rfl) ⟨1191545, by rfl⟩ : syracuseStep 1588727 = 2383091) B2383091
theorem B4013641 : Blo 834351 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B835311 : Blo 834351 835311 := bstep (se 1 (by rfl) ⟨626483, by rfl⟩ : syracuseStep 835311 = 1252967) B1252967
theorem B835419 : Blo 834351 835419 := bstep (se 1 (by rfl) ⟨626564, by rfl⟩ : syracuseStep 835419 = 1253129) B1253129
theorem B22921127 : Blo 834351 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B835567 : Blo 834351 835567 := bstep (se 1 (by rfl) ⟨626675, by rfl⟩ : syracuseStep 835567 = 1253351) B1253351
theorem B835647 : Blo 834351 835647 := bstep (se 1 (by rfl) ⟨626735, by rfl⟩ : syracuseStep 835647 = 1253471) B1253471
theorem B3391571 : Blo 834351 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B835687 : Blo 834351 835687 := bstep (se 1 (by rfl) ⟨626765, by rfl⟩ : syracuseStep 835687 = 1253531) B1253531
theorem B835743 : Blo 834351 835743 := bstep (se 1 (by rfl) ⟨626807, by rfl⟩ : syracuseStep 835743 = 1253615) B1253615
theorem B3391703 : Blo 834351 3391703 := bstep (se 1 (by rfl) ⟨2543777, by rfl⟩ : syracuseStep 3391703 = 5087555) B5087555
theorem B1884473 : Blo 834351 1884473 := bstep (se 2 (by rfl) ⟨706677, by rfl⟩ : syracuseStep 1884473 = 1413355) B1413355
theorem B835995 : Blo 834351 835995 := bstep (se 1 (by rfl) ⟨626996, by rfl⟩ : syracuseStep 835995 = 1253993) B1253993
theorem B835999 : Blo 834351 835999 := bstep (se 1 (by rfl) ⟨626999, by rfl⟩ : syracuseStep 835999 = 1253999) B1253999
theorem B1589843 : Blo 834351 1589843 := bstep (se 1 (by rfl) ⟨1192382, by rfl⟩ : syracuseStep 1589843 = 2384765) B2384765
theorem B1884905 : Blo 834351 1884905 := bstep (se 2 (by rfl) ⟨706839, by rfl⟩ : syracuseStep 1884905 = 1413679) B1413679
theorem B836415 : Blo 834351 836415 := bstep (se 1 (by rfl) ⟨627311, by rfl⟩ : syracuseStep 836415 = 1254623) B1254623
theorem B836575 : Blo 834351 836575 := bstep (se 1 (by rfl) ⟨627431, by rfl⟩ : syracuseStep 836575 = 1254863) B1254863
theorem B836699 : Blo 834351 836699 := bstep (se 1 (by rfl) ⟨627524, by rfl⟩ : syracuseStep 836699 = 1255049) B1255049
theorem B836735 : Blo 834351 836735 := bstep (se 1 (by rfl) ⟨627551, by rfl⟩ : syracuseStep 836735 = 1255103) B1255103
theorem B21415103 : Blo 834351 21415103 := bstep (se 1 (by rfl) ⟨16061327, by rfl⟩ : syracuseStep 21415103 = 32122655) B32122655
theorem B836839 : Blo 834351 836839 := bstep (se 1 (by rfl) ⟨627629, by rfl⟩ : syracuseStep 836839 = 1255259) B1255259
theorem B837095 : Blo 834351 837095 := bstep (se 1 (by rfl) ⟨627821, by rfl⟩ : syracuseStep 837095 = 1255643) B1255643
theorem B1885769 : Blo 834351 1885769 := bstep (se 2 (by rfl) ⟨707163, by rfl⟩ : syracuseStep 1885769 = 1414327) B1414327
theorem B2147995 : Blo 834351 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B837275 : Blo 834351 837275 := bstep (se 1 (by rfl) ⟨627956, by rfl⟩ : syracuseStep 837275 = 1255913) B1255913
theorem B837279 : Blo 834351 837279 := bstep (se 1 (by rfl) ⟨627959, by rfl⟩ : syracuseStep 837279 = 1255919) B1255919
theorem B1591103 : Blo 834351 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B837487 : Blo 834351 837487 := bstep (se 1 (by rfl) ⟨628115, by rfl⟩ : syracuseStep 837487 = 1256231) B1256231
theorem B837535 : Blo 834351 837535 := bstep (se 1 (by rfl) ⟨628151, by rfl⟩ : syracuseStep 837535 = 1256303) B1256303
theorem B837703 : Blo 834351 837703 := bstep (se 1 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 837703 = 1256555) B1256555
theorem B2115791 : Blo 834351 2115791 := bstep (se 1 (by rfl) ⟨1586843, by rfl⟩ : syracuseStep 2115791 = 3173687) B3173687
theorem B837863 : Blo 834351 837863 := bstep (se 1 (by rfl) ⟨628397, by rfl⟩ : syracuseStep 837863 = 1256795) B1256795
theorem B837883 : Blo 834351 837883 := bstep (se 1 (by rfl) ⟨628412, by rfl⟩ : syracuseStep 837883 = 1256825) B1256825
theorem B837887 : Blo 834351 837887 := bstep (se 1 (by rfl) ⟨628415, by rfl⟩ : syracuseStep 837887 = 1256831) B1256831
theorem B5359927 : Blo 834351 5359927 := bstep (se 1 (by rfl) ⟨4019945, by rfl⟩ : syracuseStep 5359927 = 8039891) B8039891
theorem B838043 : Blo 834351 838043 := bstep (se 1 (by rfl) ⟨628532, by rfl⟩ : syracuseStep 838043 = 1257065) B1257065
theorem B5720539 : Blo 834351 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B838303 : Blo 834351 838303 := bstep (se 1 (by rfl) ⟨628727, by rfl⟩ : syracuseStep 838303 = 1257455) B1257455
theorem B7228559 : Blo 834351 7228559 := bstep (se 1 (by rfl) ⟨5421419, by rfl⟩ : syracuseStep 7228559 = 10842839) B10842839
theorem B2116975 : Blo 834351 2116975 := bstep (se 1 (by rfl) ⟨1587731, by rfl⟩ : syracuseStep 2116975 = 3175463) B3175463
theorem B7720363 : Blo 834351 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B2117279 : Blo 834351 2117279 := bstep (se 1 (by rfl) ⟨1587959, by rfl⟩ : syracuseStep 2117279 = 3175919) B3175919
theorem B7130987 : Blo 834351 7130987 := bstep (se 1 (by rfl) ⟨5348240, by rfl⟩ : syracuseStep 7130987 = 10696481) B10696481
theorem B2379719 : Blo 834351 2379719 := bstep (se 1 (by rfl) ⟨1784789, by rfl⟩ : syracuseStep 2379719 = 3569579) B3569579
theorem B2117735 : Blo 834351 2117735 := bstep (se 1 (by rfl) ⟨1588301, by rfl⟩ : syracuseStep 2117735 = 3176603) B3176603
theorem B2381051 : Blo 834351 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B2119223 : Blo 834351 2119223 := bstep (se 1 (by rfl) ⟨1589417, by rfl⟩ : syracuseStep 2119223 = 3178835) B3178835
theorem B10704635 : Blo 834351 10704635 := bstep (se 1 (by rfl) ⟨8028476, by rfl⟩ : syracuseStep 10704635 = 16056953) B16056953
theorem B3168143 : Blo 834351 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B5724047 : Blo 834351 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B6609377 : Blo 834351 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B8051237 : Blo 834351 8051237 := bstep (se 4 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 8051237 = 1509607) B1509607
theorem B3169313 : Blo 834351 3169313 := bstep (se 2 (by rfl) ⟨1188492, by rfl⟩ : syracuseStep 3169313 = 2376985) B2376985
theorem B2121167 : Blo 834351 2121167 := bstep (se 1 (by rfl) ⟨1590875, by rfl⟩ : syracuseStep 2121167 = 3181751) B3181751
theorem B4513661 : Blo 834351 4513661 := bstep (se 3 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 4513661 = 1692623) B1692623
theorem B10149799 : Blo 834351 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B9036319 : Blo 834351 9036319 := bstep (se 1 (by rfl) ⟨6777239, by rfl⟩ : syracuseStep 9036319 = 13554479) B13554479
theorem B117531499 : Blo 834351 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B81487619 : Blo 834351 81487619 := bstep (se 1 (by rfl) ⟨61115714, by rfl⟩ : syracuseStep 81487619 = 122231429) B122231429
theorem B6351047 : Blo 834351 6351047 := bstep (se 1 (by rfl) ⟨4763285, by rfl⟩ : syracuseStep 6351047 = 9526571) B9526571
theorem B3172715 : Blo 834351 3172715 := bstep (se 1 (by rfl) ⟨2379536, by rfl⟩ : syracuseStep 3172715 = 4759073) B4759073
theorem B2255339 : Blo 834351 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B2681657 : Blo 834351 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B45738917 : Blo 834351 45738917 := bstep (se 4 (by rfl) ⟨4288023, by rfl⟩ : syracuseStep 45738917 = 8576047) B8576047
theorem B3566587 : Blo 834351 3566587 := bstep (se 1 (by rfl) ⟨2674940, by rfl⟩ : syracuseStep 3566587 = 5349881) B5349881
theorem B3010031 : Blo 834351 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B6352991 : Blo 834351 6352991 := bstep (se 1 (by rfl) ⟨4764743, by rfl⟩ : syracuseStep 6352991 = 9529487) B9529487
theorem B5076361 : Blo 834351 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B8025743 : Blo 834351 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B39188443 : Blo 834351 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B4225607 : Blo 834351 4225607 := bstep (se 1 (by rfl) ⟨3169205, by rfl⟩ : syracuseStep 4225607 = 6338411) B6338411
theorem B6781583 : Blo 834351 6781583 := bstep (se 1 (by rfl) ⟨5086187, by rfl⟩ : syracuseStep 6781583 = 10172375) B10172375
theorem B3013679 : Blo 834351 3013679 := bstep (se 1 (by rfl) ⟨2260259, by rfl⟩ : syracuseStep 3013679 = 4520519) B4520519
theorem B2261047 : Blo 834351 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B2261135 : Blo 834351 2261135 := bstep (se 1 (by rfl) ⟨1695851, by rfl⟩ : syracuseStep 2261135 = 3391703) B3391703
theorem B7143835 : Blo 834351 7143835 := bstep (se 1 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 7143835 = 10715753) B10715753
theorem B1410527 : Blo 834351 1410527 := bstep (se 1 (by rfl) ⟨1057895, by rfl⟩ : syracuseStep 1410527 = 2115791) B2115791
theorem B1411519 : Blo 834351 1411519 := bstep (se 1 (by rfl) ⟨1058639, by rfl⟩ : syracuseStep 1411519 = 2117279) B2117279
theorem B4753991 : Blo 834351 4753991 := bstep (se 1 (by rfl) ⟨3565493, by rfl⟩ : syracuseStep 4753991 = 7130987) B7130987
theorem B1411823 : Blo 834351 1411823 := bstep (se 1 (by rfl) ⟨1058867, by rfl⟩ : syracuseStep 1411823 = 2117735) B2117735
theorem B7146569 : Blo 834351 7146569 := bstep (se 2 (by rfl) ⟨2679963, by rfl⟩ : syracuseStep 7146569 = 5359927) B5359927
theorem B1510739 : Blo 834351 1510739 := bstep (se 1 (by rfl) ⟨1133054, by rfl⟩ : syracuseStep 1510739 = 2266109) B2266109
theorem B32083289 : Blo 834351 32083289 := bstep (se 2 (by rfl) ⟨12031233, by rfl⟩ : syracuseStep 32083289 = 24062467) B24062467
theorem B1412815 : Blo 834351 1412815 := bstep (se 1 (by rfl) ⟨1059611, by rfl⟩ : syracuseStep 1412815 = 2119223) B2119223
theorem B4755449 : Blo 834351 4755449 := bstep (se 2 (by rfl) ⟨1783293, by rfl⟩ : syracuseStep 4755449 = 3566587) B3566587
theorem B9146513 : Blo 834351 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B21401981 : Blo 834351 21401981 := bstep (se 3 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 21401981 = 8025743) B8025743
theorem B2822633 : Blo 834351 2822633 := bstep (se 2 (by rfl) ⟨1058487, by rfl⟩ : syracuseStep 2822633 = 2116975) B2116975
theorem B10293817 : Blo 834351 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B1414111 : Blo 834351 1414111 := bstep (se 1 (by rfl) ⟨1060583, by rfl⟩ : syracuseStep 1414111 = 2121167) B2121167
theorem B2824091 : Blo 834351 2824091 := bstep (se 1 (by rfl) ⟨2118068, by rfl⟩ : syracuseStep 2824091 = 4236137) B4236137
theorem B15243389 : Blo 834351 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B1251995 : Blo 834351 1251995 := bstep (se 1 (by rfl) ⟨938996, by rfl⟩ : syracuseStep 1251995 = 1877993) B1877993
theorem B4234031 : Blo 834351 4234031 := bstep (se 1 (by rfl) ⟨3175523, by rfl⟩ : syracuseStep 4234031 = 6351047) B6351047
theorem B1252199 : Blo 834351 1252199 := bstep (se 1 (by rfl) ⟨939149, by rfl⟩ : syracuseStep 1252199 = 1878299) B1878299
theorem B2825063 : Blo 834351 2825063 := bstep (se 1 (by rfl) ⟨2118797, by rfl⟩ : syracuseStep 2825063 = 4237595) B4237595
theorem B9542609 : Blo 834351 9542609 := bstep (se 2 (by rfl) ⟨3578478, by rfl⟩ : syracuseStep 9542609 = 7156957) B7156957
theorem B9805153 : Blo 834351 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B2006687 : Blo 834351 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B4235327 : Blo 834351 4235327 := bstep (se 1 (by rfl) ⟨3176495, by rfl⟩ : syracuseStep 4235327 = 6352991) B6352991
theorem B16523459 : Blo 834351 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B10166543 : Blo 834351 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B1253735 : Blo 834351 1253735 := bstep (se 1 (by rfl) ⟨940301, by rfl⟩ : syracuseStep 1253735 = 1880603) B1880603
theorem B19276157 : Blo 834351 19276157 := bstep (se 3 (by rfl) ⟨3614279, by rfl⟩ : syracuseStep 19276157 = 7228559) B7228559
theorem B1057531 : Blo 834351 1057531 := bstep (se 1 (by rfl) ⟨793148, by rfl⟩ : syracuseStep 1057531 = 1586297) B1586297
theorem B7152583 : Blo 834351 7152583 := bstep (se 1 (by rfl) ⟨5364437, by rfl⟩ : syracuseStep 7152583 = 10728875) B10728875
theorem B1254383 : Blo 834351 1254383 := bstep (se 1 (by rfl) ⟨940787, by rfl⟩ : syracuseStep 1254383 = 1881575) B1881575
theorem B2009119 : Blo 834351 2009119 := bstep (se 1 (by rfl) ⟨1506839, by rfl⟩ : syracuseStep 2009119 = 3013679) B3013679
theorem B5351521 : Blo 834351 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B1058923 : Blo 834351 1058923 := bstep (se 1 (by rfl) ⟨794192, by rfl⟩ : syracuseStep 1058923 = 1588385) B1588385
theorem B1255535 : Blo 834351 1255535 := bstep (se 1 (by rfl) ⟨941651, by rfl⟩ : syracuseStep 1255535 = 1883303) B1883303
theorem B1059151 : Blo 834351 1059151 := bstep (se 1 (by rfl) ⟨794363, by rfl⟩ : syracuseStep 1059151 = 1588727) B1588727
theorem B15280751 : Blo 834351 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1256315 : Blo 834351 1256315 := bstep (se 1 (by rfl) ⟨942236, by rfl⟩ : syracuseStep 1256315 = 1884473) B1884473
theorem B1059895 : Blo 834351 1059895 := bstep (se 1 (by rfl) ⟨794921, by rfl⟩ : syracuseStep 1059895 = 1589843) B1589843
theorem B1256603 : Blo 834351 1256603 := bstep (se 1 (by rfl) ⟨942452, by rfl⟩ : syracuseStep 1256603 = 1884905) B1884905
theorem B7253471 : Blo 834351 7253471 := bstep (se 1 (by rfl) ⟨5440103, by rfl⟩ : syracuseStep 7253471 = 10880207) B10880207
theorem B1257179 : Blo 834351 1257179 := bstep (se 1 (by rfl) ⟨942884, by rfl⟩ : syracuseStep 1257179 = 1885769) B1885769
theorem B4763447 : Blo 834351 4763447 := bstep (se 1 (by rfl) ⟨3572585, by rfl⟩ : syracuseStep 4763447 = 7145171) B7145171
theorem B156708665 : Blo 834351 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B2142035 : Blo 834351 2142035 := bstep (se 1 (by rfl) ⟨1606526, by rfl⟩ : syracuseStep 2142035 = 3213053) B3213053
theorem B4239215 : Blo 834351 4239215 := bstep (se 1 (by rfl) ⟨3179411, by rfl⟩ : syracuseStep 4239215 = 6358823) B6358823
theorem B1880225 : Blo 834351 1880225 := bstep (se 2 (by rfl) ⟨705084, by rfl⟩ : syracuseStep 1880225 = 1410169) B1410169
theorem B1880783 : Blo 834351 1880783 := bstep (se 1 (by rfl) ⟨1410587, by rfl⟩ : syracuseStep 1880783 = 2821175) B2821175
theorem B1880801 : Blo 834351 1880801 := bstep (se 2 (by rfl) ⟨705300, by rfl⟩ : syracuseStep 1880801 = 1410601) B1410601
theorem B6796115 : Blo 834351 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B2863993 : Blo 834351 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B1586479 : Blo 834351 1586479 := bstep (se 1 (by rfl) ⟨1189859, by rfl⟩ : syracuseStep 1586479 = 2379719) B2379719
theorem B4240835 : Blo 834351 4240835 := bstep (se 1 (by rfl) ⟨3180626, by rfl⟩ : syracuseStep 4240835 = 6361253) B6361253
theorem B4765337 : Blo 834351 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B1881953 : Blo 834351 1881953 := bstep (se 2 (by rfl) ⟨705732, by rfl⟩ : syracuseStep 1881953 = 1411465) B1411465
theorem B1587367 : Blo 834351 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B2013779 : Blo 834351 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B2112095 : Blo 834351 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B3816031 : Blo 834351 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B4406251 : Blo 834351 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B834591 : Blo 834351 834591 := bstep (se 1 (by rfl) ⟨625943, by rfl⟩ : syracuseStep 834591 = 1251887) B1251887
theorem B834623 : Blo 834351 834623 := bstep (se 1 (by rfl) ⟨625967, by rfl⟩ : syracuseStep 834623 = 1251935) B1251935
theorem B834863 : Blo 834351 834863 := bstep (se 1 (by rfl) ⟨626147, by rfl⟩ : syracuseStep 834863 = 1252295) B1252295
theorem B1883447 : Blo 834351 1883447 := bstep (se 1 (by rfl) ⟨1412585, by rfl⟩ : syracuseStep 1883447 = 2825171) B2825171
theorem B2112875 : Blo 834351 2112875 := bstep (se 1 (by rfl) ⟨1584656, by rfl⟩ : syracuseStep 2112875 = 3169313) B3169313
theorem B834943 : Blo 834351 834943 := bstep (se 1 (by rfl) ⟨626207, by rfl⟩ : syracuseStep 834943 = 1252415) B1252415
theorem B1883519 : Blo 834351 1883519 := bstep (se 1 (by rfl) ⟨1412639, by rfl⟩ : syracuseStep 1883519 = 2825279) B2825279
theorem B4242941 : Blo 834351 4242941 := bstep (se 3 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 4242941 = 1591103) B1591103
theorem B835103 : Blo 834351 835103 := bstep (se 1 (by rfl) ⟨626327, by rfl⟩ : syracuseStep 835103 = 1252655) B1252655
theorem B835263 : Blo 834351 835263 := bstep (se 1 (by rfl) ⟨626447, by rfl⟩ : syracuseStep 835263 = 1252895) B1252895
theorem B835279 : Blo 834351 835279 := bstep (se 1 (by rfl) ⟨626459, by rfl⟩ : syracuseStep 835279 = 1252919) B1252919
theorem B835391 : Blo 834351 835391 := bstep (se 1 (by rfl) ⟨626543, by rfl⟩ : syracuseStep 835391 = 1253087) B1253087
theorem B1884041 : Blo 834351 1884041 := bstep (se 2 (by rfl) ⟨706515, by rfl⟩ : syracuseStep 1884041 = 1413031) B1413031
theorem B1884059 : Blo 834351 1884059 := bstep (se 1 (by rfl) ⟨1413044, by rfl⟩ : syracuseStep 1884059 = 2826089) B2826089
theorem B835519 : Blo 834351 835519 := bstep (se 1 (by rfl) ⟨626639, by rfl⟩ : syracuseStep 835519 = 1253279) B1253279
theorem B835631 : Blo 834351 835631 := bstep (se 1 (by rfl) ⟨626723, by rfl⟩ : syracuseStep 835631 = 1253447) B1253447
theorem B835711 : Blo 834351 835711 := bstep (se 1 (by rfl) ⟨626783, by rfl⟩ : syracuseStep 835711 = 1253567) B1253567
theorem B1884329 : Blo 834351 1884329 := bstep (se 2 (by rfl) ⟨706623, by rfl⟩ : syracuseStep 1884329 = 1413247) B1413247
theorem B6340841 : Blo 834351 6340841 := bstep (se 2 (by rfl) ⟨2377815, by rfl⟩ : syracuseStep 6340841 = 4755631) B4755631
theorem B835835 : Blo 834351 835835 := bstep (se 1 (by rfl) ⟨626876, by rfl⟩ : syracuseStep 835835 = 1253753) B1253753
theorem B836031 : Blo 834351 836031 := bstep (se 1 (by rfl) ⟨627023, by rfl⟩ : syracuseStep 836031 = 1254047) B1254047
theorem B5358059 : Blo 834351 5358059 := bstep (se 1 (by rfl) ⟨4018544, by rfl⟩ : syracuseStep 5358059 = 8037089) B8037089
theorem B11453561 : Blo 834351 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B1885409 : Blo 834351 1885409 := bstep (se 2 (by rfl) ⟨707028, by rfl⟩ : syracuseStep 1885409 = 1414057) B1414057
theorem B1885607 : Blo 834351 1885607 := bstep (se 1 (by rfl) ⟨1414205, by rfl⟩ : syracuseStep 1885607 = 2828411) B2828411
theorem B36226561 : Blo 834351 36226561 := bstep (se 2 (by rfl) ⟨13584960, by rfl⟩ : syracuseStep 36226561 = 27169921) B27169921
theorem B2115143 : Blo 834351 2115143 := bstep (se 1 (by rfl) ⟨1586357, by rfl⟩ : syracuseStep 2115143 = 3172715) B3172715
theorem B6342299 : Blo 834351 6342299 := bstep (se 1 (by rfl) ⟨4756724, by rfl⟩ : syracuseStep 6342299 = 9513449) B9513449
theorem B837327 : Blo 834351 837327 := bstep (se 1 (by rfl) ⟨627995, by rfl⟩ : syracuseStep 837327 = 1255991) B1255991
theorem B837467 : Blo 834351 837467 := bstep (se 1 (by rfl) ⟨628100, by rfl⟩ : syracuseStep 837467 = 1256201) B1256201
theorem B6768481 : Blo 834351 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B1787771 : Blo 834351 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B1886075 : Blo 834351 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B2410399 : Blo 834351 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B1886111 : Blo 834351 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B30492611 : Blo 834351 30492611 := bstep (se 1 (by rfl) ⟨22869458, by rfl⟩ : syracuseStep 30492611 = 45738917) B45738917
theorem B1886201 : Blo 834351 1886201 := bstep (se 2 (by rfl) ⟨707325, by rfl⟩ : syracuseStep 1886201 = 1414651) B1414651
theorem B837743 : Blo 834351 837743 := bstep (se 1 (by rfl) ⟨628307, by rfl⟩ : syracuseStep 837743 = 1256615) B1256615
theorem B52251257 : Blo 834351 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B838299 : Blo 834351 838299 := bstep (se 1 (by rfl) ⟨628724, by rfl⟩ : syracuseStep 838299 = 1257449) B1257449
theorem B838335 : Blo 834351 838335 := bstep (se 1 (by rfl) ⟨628751, by rfl⟩ : syracuseStep 838335 = 1257503) B1257503
theorem B2379901 : Blo 834351 2379901 := bstep (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) B892463
theorem B16110535 : Blo 834351 16110535 := bstep (se 1 (by rfl) ⟨12082901, by rfl⟩ : syracuseStep 16110535 = 24165803) B24165803
theorem B939487 : Blo 834351 939487 := bstep (se 1 (by rfl) ⟨704615, by rfl⟩ : syracuseStep 939487 = 1409231) B1409231
theorem B2381575 : Blo 834351 2381575 := bstep (se 1 (by rfl) ⟨1786181, by rfl⟩ : syracuseStep 2381575 = 3572363) B3572363
theorem B12048425 : Blo 834351 12048425 := bstep (se 2 (by rfl) ⟨4518159, by rfl⟩ : syracuseStep 12048425 = 9036319) B9036319
theorem B14276735 : Blo 834351 14276735 := bstep (se 1 (by rfl) ⟨10707551, by rfl⟩ : syracuseStep 14276735 = 21415103) B21415103
theorem B940999 : Blo 834351 940999 := bstep (se 1 (by rfl) ⟨705749, by rfl⟩ : syracuseStep 940999 = 1411499) B1411499
theorem B2120863 : Blo 834351 2120863 := bstep (se 1 (by rfl) ⟨1590647, by rfl⟩ : syracuseStep 2120863 = 3181295) B3181295
theorem B941359 : Blo 834351 941359 := bstep (se 1 (by rfl) ⟨706019, by rfl⟩ : syracuseStep 941359 = 1412039) B1412039
theorem B4513097 : Blo 834351 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B3170285 : Blo 834351 3170285 := bstep (se 3 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 3170285 = 1188857) B1188857
theorem B1270087 : Blo 834351 1270087 := bstep (se 1 (by rfl) ⟨952565, by rfl⟩ : syracuseStep 1270087 = 1905131) B1905131
theorem B7627385 : Blo 834351 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B7136423 : Blo 834351 7136423 := bstep (se 1 (by rfl) ⟨5352317, by rfl⟩ : syracuseStep 7136423 = 10704635) B10704635
theorem B3172031 : Blo 834351 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B5367491 : Blo 834351 5367491 := bstep (se 1 (by rfl) ⟨4025618, by rfl⟩ : syracuseStep 5367491 = 8051237) B8051237
theorem B3009107 : Blo 834351 3009107 := bstep (se 1 (by rfl) ⟨2256830, by rfl⟩ : syracuseStep 3009107 = 4513661) B4513661
theorem B54325079 : Blo 834351 54325079 := bstep (se 1 (by rfl) ⟨40743809, by rfl⟩ : syracuseStep 54325079 = 81487619) B81487619
theorem B241790993 : Blo 834351 241790993 := bstep (se 2 (by rfl) ⟨90671622, by rfl⟩ : syracuseStep 241790993 = 181343245) B181343245
theorem B1503559 : Blo 834351 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B18084221 : Blo 834351 18084221 := bstep (se 3 (by rfl) ⟨3390791, by rfl⟩ : syracuseStep 18084221 = 6781583) B6781583
theorem B16085627 : Blo 834351 16085627 := bstep (se 1 (by rfl) ⟨12064220, by rfl⟩ : syracuseStep 16085627 = 24128441) B24128441
theorem B6780025 : Blo 834351 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B2817071 : Blo 834351 2817071 := bstep (se 1 (by rfl) ⟨2112803, by rfl⟩ : syracuseStep 2817071 = 4225607) B4225607
theorem B22904383 : Blo 834351 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B13533065 : Blo 834351 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B3014729 : Blo 834351 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B1507423 : Blo 834351 1507423 := bstep (se 1 (by rfl) ⟨1130567, by rfl⟩ : syracuseStep 1507423 = 2261135) B2261135
theorem B4227227 : Blo 834351 4227227 := bstep (se 1 (by rfl) ⟨3170420, by rfl⟩ : syracuseStep 4227227 = 6340841) B6340841
theorem B3572039 : Blo 834351 3572039 := bstep (se 1 (by rfl) ⟨2679029, by rfl⟩ : syracuseStep 3572039 = 5358059) B5358059
theorem B7635707 : Blo 834351 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B1410041 : Blo 834351 1410041 := bstep (se 2 (by rfl) ⟨528765, by rfl⟩ : syracuseStep 1410041 = 1057531) B1057531
theorem B1410095 : Blo 834351 1410095 := bstep (se 1 (by rfl) ⟨1057571, by rfl⟩ : syracuseStep 1410095 = 2115143) B2115143
theorem B4228199 : Blo 834351 4228199 := bstep (se 1 (by rfl) ⟨3171149, by rfl⟩ : syracuseStep 4228199 = 6342299) B6342299
theorem B9536777 : Blo 834351 9536777 := bstep (se 2 (by rfl) ⟨3576291, by rfl⟩ : syracuseStep 9536777 = 7152583) B7152583
theorem B34834171 : Blo 834351 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B48302081 : Blo 834351 48302081 := bstep (se 2 (by rfl) ⟨18113280, by rfl⟩ : syracuseStep 48302081 = 36226561) B36226561
theorem B3213865 : Blo 834351 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B6097675 : Blo 834351 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B1411897 : Blo 834351 1411897 := bstep (se 2 (by rfl) ⟨529461, by rfl⟩ : syracuseStep 1411897 = 1058923) B1058923
theorem B1412201 : Blo 834351 1412201 := bstep (se 2 (by rfl) ⟨529575, by rfl⟩ : syracuseStep 1412201 = 1059151) B1059151
theorem B8032283 : Blo 834351 8032283 := bstep (se 1 (by rfl) ⟨6024212, by rfl⟩ : syracuseStep 8032283 = 12048425) B12048425
theorem B1413193 : Blo 834351 1413193 := bstep (se 2 (by rfl) ⟨529947, by rfl⟩ : syracuseStep 1413193 = 1059895) B1059895
theorem B10162259 : Blo 834351 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B2822687 : Blo 834351 2822687 := bstep (se 1 (by rfl) ⟨2117015, by rfl⟩ : syracuseStep 2822687 = 4234031) B4234031
theorem B6361739 : Blo 834351 6361739 := bstep (se 1 (by rfl) ⟨4771304, by rfl⟩ : syracuseStep 6361739 = 9542609) B9542609
theorem B2823551 : Blo 834351 2823551 := bstep (se 1 (by rfl) ⟨2117663, by rfl⟩ : syracuseStep 2823551 = 4235327) B4235327
theorem B11015639 : Blo 834351 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B12850771 : Blo 834351 12850771 := bstep (se 1 (by rfl) ⟨9638078, by rfl⟩ : syracuseStep 12850771 = 19276157) B19276157
theorem B2004745 : Blo 834351 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B4757615 : Blo 834351 4757615 := bstep (se 1 (by rfl) ⟨3568211, by rfl⟩ : syracuseStep 4757615 = 7136423) B7136423
theorem B3578327 : Blo 834351 3578327 := bstep (se 1 (by rfl) ⟨2683745, by rfl⟩ : syracuseStep 3578327 = 5367491) B5367491
theorem B1252649 : Blo 834351 1252649 := bstep (se 2 (by rfl) ⟨469743, by rfl⟩ : syracuseStep 1252649 = 939487) B939487
theorem B104472443 : Blo 834351 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B36216719 : Blo 834351 36216719 := bstep (se 1 (by rfl) ⟨27162539, by rfl⟩ : syracuseStep 36216719 = 54325079) B54325079
theorem B2826143 : Blo 834351 2826143 := bstep (se 1 (by rfl) ⟨2119607, by rfl⟩ : syracuseStep 2826143 = 4239215) B4239215
theorem B161193995 : Blo 834351 161193995 := bstep (se 1 (by rfl) ⟨120895496, by rfl⟩ : syracuseStep 161193995 = 241790993) B241790993
theorem B1253483 : Blo 834351 1253483 := bstep (se 1 (by rfl) ⟨940112, by rfl⟩ : syracuseStep 1253483 = 1880225) B1880225
theorem B10723751 : Blo 834351 10723751 := bstep (se 1 (by rfl) ⟨8042813, by rfl⟩ : syracuseStep 10723751 = 16085627) B16085627
theorem B1253855 : Blo 834351 1253855 := bstep (se 1 (by rfl) ⟨940391, by rfl⟩ : syracuseStep 1253855 = 1880783) B1880783
theorem B1253867 : Blo 834351 1253867 := bstep (se 1 (by rfl) ⟨940400, by rfl⟩ : syracuseStep 1253867 = 1880801) B1880801
theorem B4530743 : Blo 834351 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B5088041 : Blo 834351 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B12034925 : Blo 834351 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B2827223 : Blo 834351 2827223 := bstep (se 1 (by rfl) ⟨2120417, by rfl⟩ : syracuseStep 2827223 = 4240835) B4240835
theorem B1254635 : Blo 834351 1254635 := bstep (se 1 (by rfl) ⟨940976, by rfl⟩ : syracuseStep 1254635 = 1881953) B1881953
theorem B1254665 : Blo 834351 1254665 := bstep (se 2 (by rfl) ⟨470499, by rfl⟩ : syracuseStep 1254665 = 940999) B940999
theorem B5875001 : Blo 834351 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B2827817 : Blo 834351 2827817 := bstep (se 2 (by rfl) ⟨1060431, by rfl⟩ : syracuseStep 2827817 = 2120863) B2120863
theorem B1255145 : Blo 834351 1255145 := bstep (se 2 (by rfl) ⟨470679, by rfl⟩ : syracuseStep 1255145 = 941359) B941359
theorem B1878047 : Blo 834351 1878047 := bstep (se 1 (by rfl) ⟨1408535, by rfl⟩ : syracuseStep 1878047 = 2817071) B2817071
theorem B1255631 : Blo 834351 1255631 := bstep (se 1 (by rfl) ⟨941723, by rfl⟩ : syracuseStep 1255631 = 1883447) B1883447
theorem B1255679 : Blo 834351 1255679 := bstep (se 1 (by rfl) ⟨941759, by rfl⟩ : syracuseStep 1255679 = 1883519) B1883519
theorem B2828627 : Blo 834351 2828627 := bstep (se 1 (by rfl) ⟨2121470, by rfl⟩ : syracuseStep 2828627 = 4242941) B4242941
theorem B9022043 : Blo 834351 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B1256027 : Blo 834351 1256027 := bstep (se 1 (by rfl) ⟨942020, by rfl⟩ : syracuseStep 1256027 = 1884041) B1884041
theorem B1256039 : Blo 834351 1256039 := bstep (se 1 (by rfl) ⟨942029, by rfl⟩ : syracuseStep 1256039 = 1884059) B1884059
theorem B1256219 : Blo 834351 1256219 := bstep (se 1 (by rfl) ⟨942164, by rfl⟩ : syracuseStep 1256219 = 1884329) B1884329
theorem B1256939 : Blo 834351 1256939 := bstep (se 1 (by rfl) ⟨942704, by rfl⟩ : syracuseStep 1256939 = 1885409) B1885409
theorem B1257071 : Blo 834351 1257071 := bstep (se 1 (by rfl) ⟨942803, by rfl⟩ : syracuseStep 1257071 = 1885607) B1885607
theorem B1191847 : Blo 834351 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B1257383 : Blo 834351 1257383 := bstep (se 1 (by rfl) ⟨943037, by rfl⟩ : syracuseStep 1257383 = 1886075) B1886075
theorem B1257407 : Blo 834351 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B20328407 : Blo 834351 20328407 := bstep (se 1 (by rfl) ⟨15246305, by rfl⟩ : syracuseStep 20328407 = 30492611) B30492611
theorem B1257467 : Blo 834351 1257467 := bstep (se 1 (by rfl) ⟨943100, by rfl⟩ : syracuseStep 1257467 = 1886201) B1886201
theorem B4764379 : Blo 834351 4764379 := bstep (se 1 (by rfl) ⟨3573284, by rfl⟩ : syracuseStep 4764379 = 7146569) B7146569
theorem B9024641 : Blo 834351 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B14267987 : Blo 834351 14267987 := bstep (se 1 (by rfl) ⟨10700990, by rfl⟩ : syracuseStep 14267987 = 21401981) B21401981
theorem B1881755 : Blo 834351 1881755 := bstep (se 1 (by rfl) ⟨1411316, by rfl⟩ : syracuseStep 1881755 = 2822633) B2822633
theorem B1882025 : Blo 834351 1882025 := bstep (se 2 (by rfl) ⟨705759, by rfl⟩ : syracuseStep 1882025 = 1411519) B1411519
theorem B1882727 : Blo 834351 1882727 := bstep (se 1 (by rfl) ⟨1412045, by rfl⟩ : syracuseStep 1882727 = 2824091) B2824091
theorem B9517823 : Blo 834351 9517823 := bstep (se 1 (by rfl) ⟨7138367, by rfl⟩ : syracuseStep 9517823 = 14276735) B14276735
theorem B834663 : Blo 834351 834663 := bstep (se 1 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 834663 = 1251995) B1251995
theorem B834799 : Blo 834351 834799 := bstep (se 1 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 834799 = 1252199) B1252199
theorem B1883375 : Blo 834351 1883375 := bstep (se 1 (by rfl) ⟨1412531, by rfl⟩ : syracuseStep 1883375 = 2825063) B2825063
theorem B1883753 : Blo 834351 1883753 := bstep (se 2 (by rfl) ⟨706407, by rfl⟩ : syracuseStep 1883753 = 1412815) B1412815
theorem B2113523 : Blo 834351 2113523 := bstep (se 1 (by rfl) ⟨1585142, by rfl⟩ : syracuseStep 2113523 = 3170285) B3170285
theorem B835823 : Blo 834351 835823 := bstep (se 1 (by rfl) ⟨626867, by rfl⟩ : syracuseStep 835823 = 1253735) B1253735
theorem B836255 : Blo 834351 836255 := bstep (se 1 (by rfl) ⟨627191, by rfl⟩ : syracuseStep 836255 = 1254383) B1254383
theorem B2114687 : Blo 834351 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B3818657 : Blo 834351 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B21480713 : Blo 834351 21480713 := bstep (se 2 (by rfl) ⟨8055267, by rfl⟩ : syracuseStep 21480713 = 16110535) B16110535
theorem B1885481 : Blo 834351 1885481 := bstep (se 2 (by rfl) ⟨707055, by rfl⟩ : syracuseStep 1885481 = 1414111) B1414111
theorem B837023 : Blo 834351 837023 := bstep (se 1 (by rfl) ⟨627767, by rfl⟩ : syracuseStep 837023 = 1255535) B1255535
theorem B2115305 : Blo 834351 2115305 := bstep (se 2 (by rfl) ⟨793239, by rfl⟩ : syracuseStep 2115305 = 1586479) B1586479
theorem B837543 : Blo 834351 837543 := bstep (se 1 (by rfl) ⟨628157, by rfl⟩ : syracuseStep 837543 = 1256315) B1256315
theorem B837735 : Blo 834351 837735 := bstep (se 1 (by rfl) ⟨628301, by rfl⟩ : syracuseStep 837735 = 1256603) B1256603
theorem B4835647 : Blo 834351 4835647 := bstep (se 1 (by rfl) ⟨3626735, by rfl⟩ : syracuseStep 4835647 = 7253471) B7253471
theorem B838119 : Blo 834351 838119 := bstep (se 1 (by rfl) ⟨628589, by rfl⟩ : syracuseStep 838119 = 1257179) B1257179
theorem B1428023 : Blo 834351 1428023 := bstep (se 1 (by rfl) ⟨1071017, by rfl⟩ : syracuseStep 1428023 = 2142035) B2142035
theorem B2116489 : Blo 834351 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B9525113 : Blo 834351 9525113 := bstep (se 2 (by rfl) ⟨3571917, by rfl⟩ : syracuseStep 9525113 = 7143835) B7143835
theorem B940351 : Blo 834351 940351 := bstep (se 1 (by rfl) ⟨705263, by rfl⟩ : syracuseStep 940351 = 1410527) B1410527
theorem B20339693 : Blo 834351 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B6773797 : Blo 834351 6773797 := bstep (se 4 (by rfl) ⟨635043, by rfl⟩ : syracuseStep 6773797 = 1270087) B1270087
theorem B3169327 : Blo 834351 3169327 := bstep (se 1 (by rfl) ⟨2376995, by rfl⟩ : syracuseStep 3169327 = 4753991) B4753991
theorem B941215 : Blo 834351 941215 := bstep (se 1 (by rfl) ⟨705911, by rfl⟩ : syracuseStep 941215 = 1411823) B1411823
theorem B1007159 : Blo 834351 1007159 := bstep (se 1 (by rfl) ⟨755369, by rfl⟩ : syracuseStep 1007159 = 1510739) B1510739
theorem B21388859 : Blo 834351 21388859 := bstep (se 1 (by rfl) ⟨16041644, by rfl⟩ : syracuseStep 21388859 = 32083289) B32083289
theorem B3170299 : Blo 834351 3170299 := bstep (se 1 (by rfl) ⟨2377724, by rfl⟩ : syracuseStep 3170299 = 4755449) B4755449
theorem B2678825 : Blo 834351 2678825 := bstep (se 2 (by rfl) ⟨1004559, by rfl⟩ : syracuseStep 2678825 = 2009119) B2009119
theorem B7135361 : Blo 834351 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B1337791 : Blo 834351 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B3173201 : Blo 834351 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B6777695 : Blo 834351 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B13725089 : Blo 834351 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B9040033 : Blo 834351 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B8024285 : Blo 834351 8024285 := bstep (se 3 (by rfl) ⟨1504553, by rfl⟩ : syracuseStep 8024285 = 3009107) B3009107
theorem B5370077 : Blo 834351 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B10187167 : Blo 834351 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B3175433 : Blo 834351 3175433 := bstep (se 2 (by rfl) ⟨1190787, by rfl⟩ : syracuseStep 3175433 = 2381575) B2381575
theorem B3175631 : Blo 834351 3175631 := bstep (se 1 (by rfl) ⟨2381723, by rfl⟩ : syracuseStep 3175631 = 4763447) B4763447
theorem B12056147 : Blo 834351 12056147 := bstep (se 1 (by rfl) ⟨9042110, by rfl⟩ : syracuseStep 12056147 = 18084221) B18084221
theorem B3176891 : Blo 834351 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B1408063 : Blo 834351 1408063 := bstep (se 1 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 1408063 = 2112095) B2112095
theorem B13073537 : Blo 834351 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B30539177 : Blo 834351 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B1408583 : Blo 834351 1408583 := bstep (se 1 (by rfl) ⟨1056437, by rfl⟩ : syracuseStep 1408583 = 2112875) B2112875
theorem B2818151 : Blo 834351 2818151 := bstep (se 1 (by rfl) ⟨2113613, by rfl⟩ : syracuseStep 2818151 = 4227227) B4227227
theorem B2818799 : Blo 834351 2818799 := bstep (se 1 (by rfl) ⟨2114099, by rfl⟩ : syracuseStep 2818799 = 4228199) B4228199
theorem B1409791 : Blo 834351 1409791 := bstep (se 1 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 1409791 = 2114687) B2114687
theorem B6357851 : Blo 834351 6357851 := bstep (se 1 (by rfl) ⟨4768388, by rfl⟩ : syracuseStep 6357851 = 9536777) B9536777
theorem B14320475 : Blo 834351 14320475 := bstep (se 1 (by rfl) ⟨10740356, by rfl⟩ : syracuseStep 14320475 = 21480713) B21480713
theorem B1410203 : Blo 834351 1410203 := bstep (se 1 (by rfl) ⟨1057652, by rfl⟩ : syracuseStep 1410203 = 2115305) B2115305
theorem B952015 : Blo 834351 952015 := bstep (se 1 (by rfl) ⟨714011, by rfl⟩ : syracuseStep 952015 = 1428023) B1428023
theorem B7343759 : Blo 834351 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B8130233 : Blo 834351 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B2821985 : Blo 834351 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B14259239 : Blo 834351 14259239 := bstep (se 1 (by rfl) ⟨10694429, by rfl⟩ : syracuseStep 14259239 = 21388859) B21388859
theorem B4756907 : Blo 834351 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B7149167 : Blo 834351 7149167 := bstep (se 1 (by rfl) ⟨5361875, by rfl⟩ : syracuseStep 7149167 = 10723751) B10723751
theorem B3020495 : Blo 834351 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B1252031 : Blo 834351 1252031 := bstep (se 1 (by rfl) ⟨939023, by rfl⟩ : syracuseStep 1252031 = 1878047) B1878047
theorem B9150059 : Blo 834351 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B5349523 : Blo 834351 5349523 := bstep (se 1 (by rfl) ⟨4012142, by rfl⟩ : syracuseStep 5349523 = 8024285) B8024285
theorem B3580051 : Blo 834351 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B1253801 : Blo 834351 1253801 := bstep (se 2 (by rfl) ⟨470175, by rfl⟩ : syracuseStep 1253801 = 940351) B940351
theorem B9511991 : Blo 834351 9511991 := bstep (se 1 (by rfl) ⟨7133993, by rfl⟩ : syracuseStep 9511991 = 14267987) B14267987
theorem B8037431 : Blo 834351 8037431 := bstep (se 1 (by rfl) ⟨6028073, by rfl⟩ : syracuseStep 8037431 = 12056147) B12056147
theorem B1254503 : Blo 834351 1254503 := bstep (se 1 (by rfl) ⟨940877, by rfl⟩ : syracuseStep 1254503 = 1881755) B1881755
theorem B1254683 : Blo 834351 1254683 := bstep (se 1 (by rfl) ⟨941012, by rfl⟩ : syracuseStep 1254683 = 1882025) B1882025
theorem B1877417 : Blo 834351 1877417 := bstep (se 2 (by rfl) ⟨704031, by rfl⟩ : syracuseStep 1877417 = 1408063) B1408063
theorem B1254953 : Blo 834351 1254953 := bstep (se 2 (by rfl) ⟨470607, by rfl⟩ : syracuseStep 1254953 = 941215) B941215
theorem B1255151 : Blo 834351 1255151 := bstep (se 1 (by rfl) ⟨941363, by rfl⟩ : syracuseStep 1255151 = 1882727) B1882727
theorem B1255583 : Blo 834351 1255583 := bstep (se 1 (by rfl) ⟨941687, by rfl⟩ : syracuseStep 1255583 = 1883375) B1883375
theorem B20359451 : Blo 834351 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B1255835 : Blo 834351 1255835 := bstep (se 1 (by rfl) ⟨941876, by rfl⟩ : syracuseStep 1255835 = 1883753) B1883753
theorem B2009819 : Blo 834351 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B2009897 : Blo 834351 2009897 := bstep (se 2 (by rfl) ⟨753711, by rfl⟩ : syracuseStep 2009897 = 1507423) B1507423
theorem B5090471 : Blo 834351 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B1256987 : Blo 834351 1256987 := bstep (se 1 (by rfl) ⟨942740, by rfl⟩ : syracuseStep 1256987 = 1885481) B1885481
theorem B46445561 : Blo 834351 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B5354855 : Blo 834351 5354855 := bstep (se 1 (by rfl) ⟨4016141, by rfl⟩ : syracuseStep 5354855 = 8032283) B8032283
theorem B1881791 : Blo 834351 1881791 := bstep (se 1 (by rfl) ⟨1411343, by rfl⟩ : syracuseStep 1881791 = 2822687) B2822687
theorem B4241159 : Blo 834351 4241159 := bstep (se 1 (by rfl) ⟨3180869, by rfl⟩ : syracuseStep 4241159 = 6361739) B6361739
theorem B1783721 : Blo 834351 1783721 := bstep (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) B1337791
theorem B1882367 : Blo 834351 1882367 := bstep (se 1 (by rfl) ⟨1411775, by rfl⟩ : syracuseStep 1882367 = 2823551) B2823551
theorem B1882529 : Blo 834351 1882529 := bstep (se 2 (by rfl) ⟨705948, by rfl⟩ : syracuseStep 1882529 = 1411897) B1411897
theorem B835099 : Blo 834351 835099 := bstep (se 1 (by rfl) ⟨626324, by rfl⟩ : syracuseStep 835099 = 1252649) B1252649
theorem B1589129 : Blo 834351 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B1884095 : Blo 834351 1884095 := bstep (se 1 (by rfl) ⟨1413071, by rfl⟩ : syracuseStep 1884095 = 2826143) B2826143
theorem B107462663 : Blo 834351 107462663 := bstep (se 1 (by rfl) ⟨80596997, by rfl⟩ : syracuseStep 107462663 = 161193995) B161193995
theorem B1785883 : Blo 834351 1785883 := bstep (se 1 (by rfl) ⟨1339412, by rfl⟩ : syracuseStep 1785883 = 2678825) B2678825
theorem B835655 : Blo 834351 835655 := bstep (se 1 (by rfl) ⟨626741, by rfl⟩ : syracuseStep 835655 = 1253483) B1253483
theorem B1884257 : Blo 834351 1884257 := bstep (se 2 (by rfl) ⟨706596, by rfl⟩ : syracuseStep 1884257 = 1413193) B1413193
theorem B36126917 : Blo 834351 36126917 := bstep (se 4 (by rfl) ⟨3386898, by rfl⟩ : syracuseStep 36126917 = 6773797) B6773797
theorem B835903 : Blo 834351 835903 := bstep (se 1 (by rfl) ⟨626927, by rfl⟩ : syracuseStep 835903 = 1253855) B1253855
theorem B835911 : Blo 834351 835911 := bstep (se 1 (by rfl) ⟨626933, by rfl⟩ : syracuseStep 835911 = 1253867) B1253867
theorem B3392027 : Blo 834351 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B13582889 : Blo 834351 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B1884815 : Blo 834351 1884815 := bstep (se 1 (by rfl) ⟨1413611, by rfl⟩ : syracuseStep 1884815 = 2827223) B2827223
theorem B836423 : Blo 834351 836423 := bstep (se 1 (by rfl) ⟨627317, by rfl⟩ : syracuseStep 836423 = 1254635) B1254635
theorem B836443 : Blo 834351 836443 := bstep (se 1 (by rfl) ⟨627332, by rfl⟩ : syracuseStep 836443 = 1254665) B1254665
theorem B3916667 : Blo 834351 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B1885211 : Blo 834351 1885211 := bstep (se 1 (by rfl) ⟨1413908, by rfl⟩ : syracuseStep 1885211 = 2827817) B2827817
theorem B836763 : Blo 834351 836763 := bstep (se 1 (by rfl) ⟨627572, by rfl⟩ : syracuseStep 836763 = 1255145) B1255145
theorem B837087 : Blo 834351 837087 := bstep (se 1 (by rfl) ⟨627815, by rfl⟩ : syracuseStep 837087 = 1255631) B1255631
theorem B837119 : Blo 834351 837119 := bstep (se 1 (by rfl) ⟨627839, by rfl⟩ : syracuseStep 837119 = 1255679) B1255679
theorem B1885751 : Blo 834351 1885751 := bstep (se 1 (by rfl) ⟨1414313, by rfl⟩ : syracuseStep 1885751 = 2828627) B2828627
theorem B6014695 : Blo 834351 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B837351 : Blo 834351 837351 := bstep (se 1 (by rfl) ⟨628013, by rfl⟩ : syracuseStep 837351 = 1256027) B1256027
theorem B837359 : Blo 834351 837359 := bstep (se 1 (by rfl) ⟨628019, by rfl⟩ : syracuseStep 837359 = 1256039) B1256039
theorem B837479 : Blo 834351 837479 := bstep (se 1 (by rfl) ⟨628109, by rfl⟩ : syracuseStep 837479 = 1256219) B1256219
theorem B2115467 : Blo 834351 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B837959 : Blo 834351 837959 := bstep (se 1 (by rfl) ⟨628469, by rfl⟩ : syracuseStep 837959 = 1256939) B1256939
theorem B2672993 : Blo 834351 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B838047 : Blo 834351 838047 := bstep (se 1 (by rfl) ⟨628535, by rfl⟩ : syracuseStep 838047 = 1257071) B1257071
theorem B838255 : Blo 834351 838255 := bstep (se 1 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 838255 = 1257383) B1257383
theorem B838271 : Blo 834351 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B13552271 : Blo 834351 13552271 := bstep (se 1 (by rfl) ⟨10164203, by rfl⟩ : syracuseStep 13552271 = 20328407) B20328407
theorem B838311 : Blo 834351 838311 := bstep (se 1 (by rfl) ⟨628733, by rfl⟩ : syracuseStep 838311 = 1257467) B1257467
theorem B2116955 : Blo 834351 2116955 := bstep (se 1 (by rfl) ⟨1587716, by rfl⟩ : syracuseStep 2116955 = 3175433) B3175433
theorem B6016427 : Blo 834351 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B2117087 : Blo 834351 2117087 := bstep (se 1 (by rfl) ⟨1587815, by rfl⟩ : syracuseStep 2117087 = 3175631) B3175631
theorem B2117927 : Blo 834351 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B6345215 : Blo 834351 6345215 := bstep (se 1 (by rfl) ⟨4758911, by rfl⟩ : syracuseStep 6345215 = 9517823) B9517823
theorem B939055 : Blo 834351 939055 := bstep (se 1 (by rfl) ⟨704291, by rfl⟩ : syracuseStep 939055 = 1408583) B1408583
theorem B2381359 : Blo 834351 2381359 := bstep (se 1 (by rfl) ⟨1786019, by rfl⟩ : syracuseStep 2381359 = 3572039) B3572039
theorem B940027 : Blo 834351 940027 := bstep (se 1 (by rfl) ⟨705020, by rfl⟩ : syracuseStep 940027 = 1410041) B1410041
theorem B940063 : Blo 834351 940063 := bstep (se 1 (by rfl) ⟨705047, by rfl⟩ : syracuseStep 940063 = 1410095) B1410095
theorem B2545771 : Blo 834351 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B32201387 : Blo 834351 32201387 := bstep (se 1 (by rfl) ⟨24151040, by rfl⟩ : syracuseStep 32201387 = 48302081) B48302081
theorem B941467 : Blo 834351 941467 := bstep (se 1 (by rfl) ⟨706100, by rfl⟩ : syracuseStep 941467 = 1412201) B1412201
theorem B6774839 : Blo 834351 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B6447529 : Blo 834351 6447529 := bstep (se 2 (by rfl) ⟨2417823, by rfl⟩ : syracuseStep 6447529 = 4835647) B4835647
theorem B4285153 : Blo 834351 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B6350075 : Blo 834351 6350075 := bstep (se 1 (by rfl) ⟨4762556, by rfl⟩ : syracuseStep 6350075 = 9525113) B9525113
theorem B3171743 : Blo 834351 3171743 := bstep (se 1 (by rfl) ⟨2378807, by rfl⟩ : syracuseStep 3171743 = 4757615) B4757615
theorem B2385551 : Blo 834351 2385551 := bstep (se 1 (by rfl) ⟨1789163, by rfl⟩ : syracuseStep 2385551 = 3578327) B3578327
theorem B13559795 : Blo 834351 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B24144479 : Blo 834351 24144479 := bstep (se 1 (by rfl) ⟨18108359, by rfl⟩ : syracuseStep 24144479 = 36216719) B36216719
theorem B12053377 : Blo 834351 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B8023283 : Blo 834351 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B6352505 : Blo 834351 6352505 := bstep (se 2 (by rfl) ⟨2382189, by rfl⟩ : syracuseStep 6352505 = 4764379) B4764379
theorem B4518463 : Blo 834351 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B17134361 : Blo 834351 17134361 := bstep (se 2 (by rfl) ⟨6425385, by rfl⟩ : syracuseStep 17134361 = 12850771) B12850771
theorem B4225769 : Blo 834351 4225769 := bstep (se 2 (by rfl) ⟨1584663, by rfl⟩ : syracuseStep 4225769 = 3169327) B3169327
theorem B2685757 : Blo 834351 2685757 := bstep (se 3 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 2685757 = 1007159) B1007159
theorem B8715691 : Blo 834351 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B278593181 : Blo 834351 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B1409015 : Blo 834351 1409015 := bstep (se 1 (by rfl) ⟨1056761, by rfl⟩ : syracuseStep 1409015 = 2113523) B2113523
theorem B4227065 : Blo 834351 4227065 := bstep (se 2 (by rfl) ⟨1585149, by rfl⟩ : syracuseStep 4227065 = 3170299) B3170299
theorem B24084611 : Blo 834351 24084611 := bstep (se 1 (by rfl) ⟨18063458, by rfl⟩ : syracuseStep 24084611 = 36126917) B36126917
theorem B2261351 : Blo 834351 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B1410311 : Blo 834351 1410311 := bstep (se 1 (by rfl) ⟨1057733, by rfl⟩ : syracuseStep 1410311 = 2115467) B2115467
theorem B1411303 : Blo 834351 1411303 := bstep (se 1 (by rfl) ⟨1058477, by rfl⟩ : syracuseStep 1411303 = 2116955) B2116955
theorem B1411391 : Blo 834351 1411391 := bstep (se 1 (by rfl) ⟨1058543, by rfl⟩ : syracuseStep 1411391 = 2117087) B2117087
theorem B1411951 : Blo 834351 1411951 := bstep (se 1 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 1411951 = 2117927) B2117927
theorem B4230143 : Blo 834351 4230143 := bstep (se 1 (by rfl) ⟨3172607, by rfl⟩ : syracuseStep 4230143 = 6345215) B6345215
theorem B9506159 : Blo 834351 9506159 := bstep (se 1 (by rfl) ⟨7129619, by rfl⟩ : syracuseStep 9506159 = 14259239) B14259239
theorem B21467591 : Blo 834351 21467591 := bstep (se 1 (by rfl) ⟨16100693, by rfl⟩ : syracuseStep 21467591 = 32201387) B32201387
theorem B6100039 : Blo 834351 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B4756589 : Blo 834351 4756589 := bstep (se 3 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 4756589 = 1783721) B1783721
theorem B4233383 : Blo 834351 4233383 := bstep (se 1 (by rfl) ⟨3175037, by rfl⟩ : syracuseStep 4233383 = 6350075) B6350075
theorem B1251611 : Blo 834351 1251611 := bstep (se 1 (by rfl) ⟨938708, by rfl⟩ : syracuseStep 1251611 = 1877417) B1877417
theorem B1252073 : Blo 834351 1252073 := bstep (se 2 (by rfl) ⟨469527, by rfl⟩ : syracuseStep 1252073 = 939055) B939055
theorem B13572967 : Blo 834351 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B16096319 : Blo 834351 16096319 := bstep (se 1 (by rfl) ⟨12072239, by rfl⟩ : syracuseStep 16096319 = 24144479) B24144479
theorem B5348855 : Blo 834351 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B4235003 : Blo 834351 4235003 := bstep (se 1 (by rfl) ⟨3176252, by rfl⟩ : syracuseStep 4235003 = 6352505) B6352505
theorem B1253369 : Blo 834351 1253369 := bstep (se 2 (by rfl) ⟨470013, by rfl⟩ : syracuseStep 1253369 = 940027) B940027
theorem B1253417 : Blo 834351 1253417 := bstep (se 2 (by rfl) ⟨470031, by rfl⟩ : syracuseStep 1253417 = 940063) B940063
theorem B3581009 : Blo 834351 3581009 := bstep (se 2 (by rfl) ⟨1342878, by rfl⟩ : syracuseStep 3581009 = 2685757) B2685757
theorem B1254527 : Blo 834351 1254527 := bstep (se 1 (by rfl) ⟨940895, by rfl⟩ : syracuseStep 1254527 = 1881791) B1881791
theorem B2827439 : Blo 834351 2827439 := bstep (se 1 (by rfl) ⟨2120579, by rfl⟩ : syracuseStep 2827439 = 4241159) B4241159
theorem B1254911 : Blo 834351 1254911 := bstep (se 1 (by rfl) ⟨941183, by rfl⟩ : syracuseStep 1254911 = 1882367) B1882367
theorem B1255019 : Blo 834351 1255019 := bstep (se 1 (by rfl) ⟨941264, by rfl⟩ : syracuseStep 1255019 = 1882529) B1882529
theorem B1255289 : Blo 834351 1255289 := bstep (se 2 (by rfl) ⟨470733, by rfl⟩ : syracuseStep 1255289 = 941467) B941467
theorem B1059419 : Blo 834351 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B1256063 : Blo 834351 1256063 := bstep (se 1 (by rfl) ⟨942047, by rfl⟩ : syracuseStep 1256063 = 1884095) B1884095
theorem B71641775 : Blo 834351 71641775 := bstep (se 1 (by rfl) ⟨53731331, by rfl⟩ : syracuseStep 71641775 = 107462663) B107462663
theorem B1256171 : Blo 834351 1256171 := bstep (se 1 (by rfl) ⟨942128, by rfl⟩ : syracuseStep 1256171 = 1884257) B1884257
theorem B1878767 : Blo 834351 1878767 := bstep (se 1 (by rfl) ⟨1409075, by rfl⟩ : syracuseStep 1878767 = 2818151) B2818151
theorem B9055259 : Blo 834351 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B1256543 : Blo 834351 1256543 := bstep (se 1 (by rfl) ⟨942407, by rfl⟩ : syracuseStep 1256543 = 1884815) B1884815
theorem B1879199 : Blo 834351 1879199 := bstep (se 1 (by rfl) ⟨1409399, by rfl⟩ : syracuseStep 1879199 = 2818799) B2818799
theorem B8596705 : Blo 834351 8596705 := bstep (se 2 (by rfl) ⟨3223764, by rfl⟩ : syracuseStep 8596705 = 6447529) B6447529
theorem B4238567 : Blo 834351 4238567 := bstep (se 1 (by rfl) ⟨3178925, by rfl⟩ : syracuseStep 4238567 = 6357851) B6357851
theorem B9546983 : Blo 834351 9546983 := bstep (se 1 (by rfl) ⟨7160237, by rfl⟩ : syracuseStep 9546983 = 14320475) B14320475
theorem B1256807 : Blo 834351 1256807 := bstep (se 1 (by rfl) ⟨942605, by rfl⟩ : syracuseStep 1256807 = 1885211) B1885211
theorem B5713537 : Blo 834351 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B1879721 : Blo 834351 1879721 := bstep (se 2 (by rfl) ⟨704895, by rfl⟩ : syracuseStep 1879721 = 1409791) B1409791
theorem B1257167 : Blo 834351 1257167 := bstep (se 1 (by rfl) ⟨942875, by rfl⟩ : syracuseStep 1257167 = 1885751) B1885751
theorem B1781995 : Blo 834351 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B4010951 : Blo 834351 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B4895839 : Blo 834351 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B1881323 : Blo 834351 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B4766111 : Blo 834351 4766111 := bstep (se 1 (by rfl) ⟨3574583, by rfl⟩ : syracuseStep 4766111 = 7149167) B7149167
theorem B16071169 : Blo 834351 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B834687 : Blo 834351 834687 := bstep (se 1 (by rfl) ⟨626015, by rfl⟩ : syracuseStep 834687 = 1252031) B1252031
theorem B835867 : Blo 834351 835867 := bstep (se 1 (by rfl) ⟨626900, by rfl⟩ : syracuseStep 835867 = 1253801) B1253801
theorem B6341327 : Blo 834351 6341327 := bstep (se 1 (by rfl) ⟨4755995, by rfl⟩ : syracuseStep 6341327 = 9511991) B9511991
theorem B5358287 : Blo 834351 5358287 := bstep (se 1 (by rfl) ⟨4018715, by rfl⟩ : syracuseStep 5358287 = 8037431) B8037431
theorem B836335 : Blo 834351 836335 := bstep (se 1 (by rfl) ⟨627251, by rfl⟩ : syracuseStep 836335 = 1254503) B1254503
theorem B836455 : Blo 834351 836455 := bstep (se 1 (by rfl) ⟨627341, by rfl⟩ : syracuseStep 836455 = 1254683) B1254683
theorem B2114495 : Blo 834351 2114495 := bstep (se 1 (by rfl) ⟨1585871, by rfl⟩ : syracuseStep 2114495 = 3171743) B3171743
theorem B836635 : Blo 834351 836635 := bstep (se 1 (by rfl) ⟨627476, by rfl⟩ : syracuseStep 836635 = 1254953) B1254953
theorem B1590367 : Blo 834351 1590367 := bstep (se 1 (by rfl) ⟨1192775, by rfl⟩ : syracuseStep 1590367 = 2385551) B2385551
theorem B836767 : Blo 834351 836767 := bstep (se 1 (by rfl) ⟨627575, by rfl⟩ : syracuseStep 836767 = 1255151) B1255151
theorem B837055 : Blo 834351 837055 := bstep (se 1 (by rfl) ⟨627791, by rfl⟩ : syracuseStep 837055 = 1255583) B1255583
theorem B837223 : Blo 834351 837223 := bstep (se 1 (by rfl) ⟨627917, by rfl⟩ : syracuseStep 837223 = 1255835) B1255835
theorem B5359517 : Blo 834351 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B3393647 : Blo 834351 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B837991 : Blo 834351 837991 := bstep (se 1 (by rfl) ⟨628493, by rfl⟩ : syracuseStep 837991 = 1256987) B1256987
theorem B3394361 : Blo 834351 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B11422907 : Blo 834351 11422907 := bstep (se 1 (by rfl) ⟨8567180, by rfl⟩ : syracuseStep 11422907 = 17134361) B17134361
theorem B21680621 : Blo 834351 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B11620921 : Blo 834351 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B939343 : Blo 834351 939343 := bstep (se 1 (by rfl) ⟨704507, by rfl⟩ : syracuseStep 939343 = 1409015) B1409015
theorem B2381177 : Blo 834351 2381177 := bstep (se 2 (by rfl) ⟨892941, by rfl⟩ : syracuseStep 2381177 = 1785883) B1785883
theorem B7132697 : Blo 834351 7132697 := bstep (se 2 (by rfl) ⟨2674761, by rfl⟩ : syracuseStep 7132697 = 5349523) B5349523
theorem B4773401 : Blo 834351 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B2611111 : Blo 834351 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B940135 : Blo 834351 940135 := bstep (se 1 (by rfl) ⟨705101, by rfl⟩ : syracuseStep 940135 = 1410203) B1410203
theorem B9034847 : Blo 834351 9034847 := bstep (se 1 (by rfl) ⟨6776135, by rfl⟩ : syracuseStep 9034847 = 13552271) B13552271
theorem B1269353 : Blo 834351 1269353 := bstep (se 2 (by rfl) ⟨476007, by rfl⟩ : syracuseStep 1269353 = 952015) B952015
theorem B8019593 : Blo 834351 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B3171271 : Blo 834351 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B8054653 : Blo 834351 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B4516559 : Blo 834351 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B6024617 : Blo 834351 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B9039863 : Blo 834351 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B1339931 : Blo 834351 1339931 := bstep (se 1 (by rfl) ⟨1004948, by rfl⟩ : syracuseStep 1339931 = 2009897) B2009897
theorem B3175145 : Blo 834351 3175145 := bstep (se 2 (by rfl) ⟨1190679, by rfl⟩ : syracuseStep 3175145 = 2381359) B2381359
theorem B30963707 : Blo 834351 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B3569903 : Blo 834351 3569903 := bstep (se 1 (by rfl) ⟨2677427, by rfl⟩ : syracuseStep 3569903 = 5354855) B5354855
theorem B2817179 : Blo 834351 2817179 := bstep (se 1 (by rfl) ⟨2112884, by rfl⟩ : syracuseStep 2817179 = 4225769) B4225769
theorem B185728787 : Blo 834351 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B2818043 : Blo 834351 2818043 := bstep (se 1 (by rfl) ⟨2113532, by rfl⟩ : syracuseStep 2818043 = 4227065) B4227065
theorem B16056407 : Blo 834351 16056407 := bstep (se 1 (by rfl) ⟨12042305, by rfl⟩ : syracuseStep 16056407 = 24084611) B24084611
theorem B1507567 : Blo 834351 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B4227551 : Blo 834351 4227551 := bstep (se 1 (by rfl) ⟨3170663, by rfl⟩ : syracuseStep 4227551 = 6341327) B6341327
theorem B3572191 : Blo 834351 3572191 := bstep (se 1 (by rfl) ⟨2679143, by rfl⟩ : syracuseStep 3572191 = 5358287) B5358287
theorem B1409663 : Blo 834351 1409663 := bstep (se 1 (by rfl) ⟨1057247, by rfl⟩ : syracuseStep 1409663 = 2114495) B2114495
theorem B4228361 : Blo 834351 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B3573011 : Blo 834351 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B2262431 : Blo 834351 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B2262907 : Blo 834351 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B2820095 : Blo 834351 2820095 := bstep (se 1 (by rfl) ⟨2115071, by rfl⟩ : syracuseStep 2820095 = 4230143) B4230143
theorem B14453747 : Blo 834351 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B4755131 : Blo 834351 4755131 := bstep (se 1 (by rfl) ⟨3566348, by rfl⟩ : syracuseStep 4755131 = 7132697) B7132697
theorem B3182267 : Blo 834351 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B2822255 : Blo 834351 2822255 := bstep (se 1 (by rfl) ⟨2116691, by rfl⟩ : syracuseStep 2822255 = 4233383) B4233383
theorem B5346395 : Blo 834351 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B2823335 : Blo 834351 2823335 := bstep (se 1 (by rfl) ⟨2117501, by rfl⟩ : syracuseStep 2823335 = 4235003) B4235003
theorem B8133385 : Blo 834351 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B6527785 : Blo 834351 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B2825117 : Blo 834351 2825117 := bstep (se 3 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 2825117 = 1059419) B1059419
theorem B1252457 : Blo 834351 1252457 := bstep (se 2 (by rfl) ⟨469671, by rfl⟩ : syracuseStep 1252457 = 939343) B939343
theorem B1252511 : Blo 834351 1252511 := bstep (se 1 (by rfl) ⟨939383, by rfl⟩ : syracuseStep 1252511 = 1878767) B1878767
theorem B6036839 : Blo 834351 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B1252799 : Blo 834351 1252799 := bstep (se 1 (by rfl) ⟨939599, by rfl⟩ : syracuseStep 1252799 = 1879199) B1879199
theorem B2825711 : Blo 834351 2825711 := bstep (se 1 (by rfl) ⟨2119283, by rfl⟩ : syracuseStep 2825711 = 4238567) B4238567
theorem B6364655 : Blo 834351 6364655 := bstep (se 1 (by rfl) ⟨4773491, by rfl⟩ : syracuseStep 6364655 = 9546983) B9546983
theorem B1253147 : Blo 834351 1253147 := bstep (se 1 (by rfl) ⟨939860, by rfl⟩ : syracuseStep 1253147 = 1879721) B1879721
theorem B3481481 : Blo 834351 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B1253513 : Blo 834351 1253513 := bstep (se 2 (by rfl) ⟨470067, by rfl⟩ : syracuseStep 1253513 = 940135) B940135
theorem B893287 : Blo 834351 893287 := bstep (se 1 (by rfl) ⟨669965, by rfl⟩ : syracuseStep 893287 = 1339931) B1339931
theorem B1254215 : Blo 834351 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B18097289 : Blo 834351 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B14263613 : Blo 834351 14263613 := bstep (se 3 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 14263613 = 5348855) B5348855
theorem B1878119 : Blo 834351 1878119 := bstep (se 1 (by rfl) ⟨1408589, by rfl⟩ : syracuseStep 1878119 = 2817179) B2817179
theorem B1878695 : Blo 834351 1878695 := bstep (se 1 (by rfl) ⟨1409021, by rfl⟩ : syracuseStep 1878695 = 2818043) B2818043
theorem B7615271 : Blo 834351 7615271 := bstep (se 1 (by rfl) ⟨5711453, by rfl⟩ : syracuseStep 7615271 = 11422907) B11422907
theorem B6337439 : Blo 834351 6337439 := bstep (se 1 (by rfl) ⟨4753079, by rfl⟩ : syracuseStep 6337439 = 9506159) B9506159
theorem B1881737 : Blo 834351 1881737 := bstep (se 2 (by rfl) ⟨705651, by rfl⟩ : syracuseStep 1881737 = 1411303) B1411303
theorem B1587451 : Blo 834351 1587451 := bstep (se 1 (by rfl) ⟨1190588, by rfl⟩ : syracuseStep 1587451 = 2381177) B2381177
theorem B1882601 : Blo 834351 1882601 := bstep (se 2 (by rfl) ⟨705975, by rfl⟩ : syracuseStep 1882601 = 1411951) B1411951
theorem B834407 : Blo 834351 834407 := bstep (se 1 (by rfl) ⟨625805, by rfl⟩ : syracuseStep 834407 = 1251611) B1251611
theorem B834715 : Blo 834351 834715 := bstep (se 1 (by rfl) ⟨626036, by rfl⟩ : syracuseStep 834715 = 1252073) B1252073
theorem B10730879 : Blo 834351 10730879 := bstep (se 1 (by rfl) ⟨8048159, by rfl⟩ : syracuseStep 10730879 = 16096319) B16096319
theorem B7618049 : Blo 834351 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B835579 : Blo 834351 835579 := bstep (se 1 (by rfl) ⟨626684, by rfl⟩ : syracuseStep 835579 = 1253369) B1253369
theorem B835611 : Blo 834351 835611 := bstep (se 1 (by rfl) ⟨626708, by rfl⟩ : syracuseStep 835611 = 1253417) B1253417
theorem B2375993 : Blo 834351 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B836351 : Blo 834351 836351 := bstep (se 1 (by rfl) ⟨627263, by rfl⟩ : syracuseStep 836351 = 1254527) B1254527
theorem B1884959 : Blo 834351 1884959 := bstep (se 1 (by rfl) ⟨1413719, by rfl⟩ : syracuseStep 1884959 = 2827439) B2827439
theorem B836607 : Blo 834351 836607 := bstep (se 1 (by rfl) ⟨627455, by rfl⟩ : syracuseStep 836607 = 1254911) B1254911
theorem B836679 : Blo 834351 836679 := bstep (se 1 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 836679 = 1255019) B1255019
theorem B836859 : Blo 834351 836859 := bstep (se 1 (by rfl) ⟨627644, by rfl⟩ : syracuseStep 836859 = 1255289) B1255289
theorem B837375 : Blo 834351 837375 := bstep (se 1 (by rfl) ⟨628031, by rfl⟩ : syracuseStep 837375 = 1256063) B1256063
theorem B47761183 : Blo 834351 47761183 := bstep (se 1 (by rfl) ⟨35820887, by rfl⟩ : syracuseStep 47761183 = 71641775) B71641775
theorem B837447 : Blo 834351 837447 := bstep (se 1 (by rfl) ⟨628085, by rfl⟩ : syracuseStep 837447 = 1256171) B1256171
theorem B837695 : Blo 834351 837695 := bstep (se 1 (by rfl) ⟨628271, by rfl⟩ : syracuseStep 837695 = 1256543) B1256543
theorem B837871 : Blo 834351 837871 := bstep (se 1 (by rfl) ⟨628403, by rfl⟩ : syracuseStep 837871 = 1256807) B1256807
theorem B4016411 : Blo 834351 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B838111 : Blo 834351 838111 := bstep (se 1 (by rfl) ⟨628583, by rfl⟩ : syracuseStep 838111 = 1257167) B1257167
theorem B2116763 : Blo 834351 2116763 := bstep (se 1 (by rfl) ⟨1587572, by rfl⟩ : syracuseStep 2116763 = 3175145) B3175145
theorem B2673967 : Blo 834351 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B2379935 : Blo 834351 2379935 := bstep (se 1 (by rfl) ⟨1784951, by rfl⟩ : syracuseStep 2379935 = 3569903) B3569903
theorem B123819191 : Blo 834351 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B940207 : Blo 834351 940207 := bstep (se 1 (by rfl) ⟨705155, by rfl⟩ : syracuseStep 940207 = 1410311) B1410311
theorem B2120489 : Blo 834351 2120489 := bstep (se 2 (by rfl) ⟨795183, by rfl⟩ : syracuseStep 2120489 = 1590367) B1590367
theorem B940927 : Blo 834351 940927 := bstep (se 1 (by rfl) ⟨705695, by rfl⟩ : syracuseStep 940927 = 1411391) B1411391
theorem B10739537 : Blo 834351 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B14311727 : Blo 834351 14311727 := bstep (se 1 (by rfl) ⟨10733795, by rfl⟩ : syracuseStep 14311727 = 21467591) B21467591
theorem B3171059 : Blo 834351 3171059 := bstep (se 1 (by rfl) ⟨2378294, by rfl⟩ : syracuseStep 3171059 = 4756589) B4756589
theorem B11462273 : Blo 834351 11462273 := bstep (se 2 (by rfl) ⟨4298352, by rfl⟩ : syracuseStep 11462273 = 8596705) B8596705
theorem B6023231 : Blo 834351 6023231 := bstep (se 1 (by rfl) ⟨4517423, by rfl⟩ : syracuseStep 6023231 = 9034847) B9034847
theorem B846235 : Blo 834351 846235 := bstep (se 1 (by rfl) ⟨634676, by rfl⟩ : syracuseStep 846235 = 1269353) B1269353
theorem B2387339 : Blo 834351 2387339 := bstep (se 1 (by rfl) ⟨1790504, by rfl⟩ : syracuseStep 2387339 = 3581009) B3581009
theorem B15494561 : Blo 834351 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B3011039 : Blo 834351 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B6026575 : Blo 834351 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B21428225 : Blo 834351 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B20642471 : Blo 834351 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B3177407 : Blo 834351 3177407 := bstep (se 1 (by rfl) ⟨2383055, by rfl⟩ : syracuseStep 3177407 = 4766111) B4766111
theorem B2818367 : Blo 834351 2818367 := bstep (se 1 (by rfl) ⟨2113775, by rfl⟩ : syracuseStep 2818367 = 4227551) B4227551
theorem B2818907 : Blo 834351 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B9635831 : Blo 834351 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B1411175 : Blo 834351 1411175 := bstep (se 1 (by rfl) ⟨1058381, by rfl⟩ : syracuseStep 1411175 = 2116763) B2116763
theorem B82546127 : Blo 834351 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B6033149 : Blo 834351 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B1413659 : Blo 834351 1413659 := bstep (se 1 (by rfl) ⟨1060244, by rfl⟩ : syracuseStep 1413659 = 2120489) B2120489
theorem B9541151 : Blo 834351 9541151 := bstep (se 1 (by rfl) ⟨7155863, by rfl⟩ : syracuseStep 9541151 = 14311727) B14311727
theorem B12064859 : Blo 834351 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B9509075 : Blo 834351 9509075 := bstep (se 1 (by rfl) ⟨7131806, by rfl⟩ : syracuseStep 9509075 = 14263613) B14263613
theorem B7641515 : Blo 834351 7641515 := bstep (se 1 (by rfl) ⟨5731136, by rfl⟩ : syracuseStep 7641515 = 11462273) B11462273
theorem B1252079 : Blo 834351 1252079 := bstep (se 1 (by rfl) ⟨939059, by rfl⟩ : syracuseStep 1252079 = 1878119) B1878119
theorem B8035433 : Blo 834351 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B1252463 : Blo 834351 1252463 := bstep (se 1 (by rfl) ⟨939347, by rfl⟩ : syracuseStep 1252463 = 1878695) B1878695
theorem B10329707 : Blo 834351 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B1253609 : Blo 834351 1253609 := bstep (se 2 (by rfl) ⟨470103, by rfl⟩ : syracuseStep 1253609 = 940207) B940207
theorem B2007359 : Blo 834351 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B1254491 : Blo 834351 1254491 := bstep (se 1 (by rfl) ⟨940868, by rfl⟩ : syracuseStep 1254491 = 1881737) B1881737
theorem B1254569 : Blo 834351 1254569 := bstep (se 2 (by rfl) ⟨470463, by rfl⟩ : syracuseStep 1254569 = 940927) B940927
theorem B1255067 : Blo 834351 1255067 := bstep (se 1 (by rfl) ⟨941300, by rfl⟩ : syracuseStep 1255067 = 1882601) B1882601
theorem B12068837 : Blo 834351 12068837 := bstep (se 4 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 12068837 = 2262907) B2262907
theorem B7153919 : Blo 834351 7153919 := bstep (se 1 (by rfl) ⟨5365439, by rfl⟩ : syracuseStep 7153919 = 10730879) B10730879
theorem B9283949 : Blo 834351 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B2010089 : Blo 834351 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B1256639 : Blo 834351 1256639 := bstep (se 1 (by rfl) ⟨942479, by rfl⟩ : syracuseStep 1256639 = 1884959) B1884959
theorem B4762921 : Blo 834351 4762921 := bstep (se 2 (by rfl) ⟨1786095, by rfl⟩ : syracuseStep 4762921 = 3572191) B3572191
theorem B6335981 : Blo 834351 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B1880063 : Blo 834351 1880063 := bstep (se 1 (by rfl) ⟨1410047, by rfl⟩ : syracuseStep 1880063 = 2820095) B2820095
theorem B4764197 : Blo 834351 4764197 := bstep (se 4 (by rfl) ⟨446643, by rfl⟩ : syracuseStep 4764197 = 893287) B893287
theorem B1881503 : Blo 834351 1881503 := bstep (se 1 (by rfl) ⟨1411127, by rfl⟩ : syracuseStep 1881503 = 2822255) B2822255
theorem B1586623 : Blo 834351 1586623 := bstep (se 1 (by rfl) ⟨1189967, by rfl⟩ : syracuseStep 1586623 = 2379935) B2379935
theorem B1128313 : Blo 834351 1128313 := bstep (se 2 (by rfl) ⟨423117, by rfl⟩ : syracuseStep 1128313 = 846235) B846235
theorem B1882223 : Blo 834351 1882223 := bstep (se 1 (by rfl) ⟨1411667, by rfl⟩ : syracuseStep 1882223 = 2823335) B2823335
theorem B1883411 : Blo 834351 1883411 := bstep (se 1 (by rfl) ⟨1412558, by rfl⟩ : syracuseStep 1883411 = 2825117) B2825117
theorem B834971 : Blo 834351 834971 := bstep (se 1 (by rfl) ⟨626228, by rfl⟩ : syracuseStep 834971 = 1252457) B1252457
theorem B835007 : Blo 834351 835007 := bstep (se 1 (by rfl) ⟨626255, by rfl⟩ : syracuseStep 835007 = 1252511) B1252511
theorem B835199 : Blo 834351 835199 := bstep (se 1 (by rfl) ⟨626399, by rfl⟩ : syracuseStep 835199 = 1252799) B1252799
theorem B1883807 : Blo 834351 1883807 := bstep (se 1 (by rfl) ⟨1412855, by rfl⟩ : syracuseStep 1883807 = 2825711) B2825711
theorem B4243103 : Blo 834351 4243103 := bstep (se 1 (by rfl) ⟨3182327, by rfl⟩ : syracuseStep 4243103 = 6364655) B6364655
theorem B835431 : Blo 834351 835431 := bstep (se 1 (by rfl) ⟨626573, by rfl⟩ : syracuseStep 835431 = 1253147) B1253147
theorem B7159691 : Blo 834351 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B835675 : Blo 834351 835675 := bstep (se 1 (by rfl) ⟨626756, by rfl⟩ : syracuseStep 835675 = 1253513) B1253513
theorem B2114039 : Blo 834351 2114039 := bstep (se 1 (by rfl) ⟨1585529, by rfl⟩ : syracuseStep 2114039 = 3171059) B3171059
theorem B836143 : Blo 834351 836143 := bstep (se 1 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 836143 = 1254215) B1254215
theorem B4015487 : Blo 834351 4015487 := bstep (se 1 (by rfl) ⟨3011615, by rfl⟩ : syracuseStep 4015487 = 6023231) B6023231
theorem B1591559 : Blo 834351 1591559 := bstep (se 1 (by rfl) ⟨1193669, by rfl⟩ : syracuseStep 1591559 = 2387339) B2387339
theorem B2116601 : Blo 834351 2116601 := bstep (se 2 (by rfl) ⟨793725, by rfl⟩ : syracuseStep 2116601 = 1587451) B1587451
theorem B8703713 : Blo 834351 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B254726309 : Blo 834351 254726309 := bstep (se 4 (by rfl) ⟨23880591, by rfl⟩ : syracuseStep 254726309 = 47761183) B47761183
theorem B2118271 : Blo 834351 2118271 := bstep (se 1 (by rfl) ⟨1588703, by rfl⟩ : syracuseStep 2118271 = 3177407) B3177407
theorem B10704271 : Blo 834351 10704271 := bstep (se 1 (by rfl) ⟨8028203, by rfl⟩ : syracuseStep 10704271 = 16056407) B16056407
theorem B939775 : Blo 834351 939775 := bstep (se 1 (by rfl) ⟨704831, by rfl⟩ : syracuseStep 939775 = 1409663) B1409663
theorem B2677607 : Blo 834351 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B3170087 : Blo 834351 3170087 := bstep (se 1 (by rfl) ⟨2377565, by rfl⟩ : syracuseStep 3170087 = 4755131) B4755131
theorem B2121511 : Blo 834351 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B9528029 : Blo 834351 9528029 := bstep (se 3 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 9528029 = 3573011) B3573011
theorem B3564263 : Blo 834351 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B3565289 : Blo 834351 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B4024559 : Blo 834351 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B5076847 : Blo 834351 5076847 := bstep (se 1 (by rfl) ⟨3807635, by rfl⟩ : syracuseStep 5076847 = 7615271) B7615271
theorem B4224959 : Blo 834351 4224959 := bstep (se 1 (by rfl) ⟨3168719, by rfl⟩ : syracuseStep 4224959 = 6337439) B6337439
theorem B10844513 : Blo 834351 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B14285483 : Blo 834351 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B13761647 : Blo 834351 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B5078699 : Blo 834351 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B1409359 : Blo 834351 1409359 := bstep (se 1 (by rfl) ⟨1057019, by rfl⟩ : syracuseStep 1409359 = 2114039) B2114039
theorem B6423887 : Blo 834351 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B9504701 : Blo 834351 9504701 := bstep (se 3 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 9504701 = 3564263) B3564263
theorem B1411067 : Blo 834351 1411067 := bstep (se 1 (by rfl) ⟨1058300, by rfl⟩ : syracuseStep 1411067 = 2116601) B2116601
theorem B6360767 : Blo 834351 6360767 := bstep (se 1 (by rfl) ⟨4770575, by rfl⟩ : syracuseStep 6360767 = 9541151) B9541151
theorem B6886471 : Blo 834351 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B2824361 : Blo 834351 2824361 := bstep (se 2 (by rfl) ⟨1059135, by rfl⟩ : syracuseStep 2824361 = 2118271) B2118271
theorem B1253033 : Blo 834351 1253033 := bstep (se 2 (by rfl) ⟨469887, by rfl⟩ : syracuseStep 1253033 = 939775) B939775
theorem B1253375 : Blo 834351 1253375 := bstep (se 1 (by rfl) ⟨940031, by rfl⟩ : syracuseStep 1253375 = 1880063) B1880063
theorem B1254335 : Blo 834351 1254335 := bstep (se 1 (by rfl) ⟨940751, by rfl⟩ : syracuseStep 1254335 = 1881503) B1881503
theorem B1254815 : Blo 834351 1254815 := bstep (se 1 (by rfl) ⟨941111, by rfl⟩ : syracuseStep 1254815 = 1882223) B1882223
theorem B23209901 : Blo 834351 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B1255607 : Blo 834351 1255607 := bstep (se 1 (by rfl) ⟨941705, by rfl⟩ : syracuseStep 1255607 = 1883411) B1883411
theorem B2828681 : Blo 834351 2828681 := bstep (se 2 (by rfl) ⟨1060755, by rfl⟩ : syracuseStep 2828681 = 2121511) B2121511
theorem B1255871 : Blo 834351 1255871 := bstep (se 1 (by rfl) ⟨941903, by rfl⟩ : syracuseStep 1255871 = 1883807) B1883807
theorem B2828735 : Blo 834351 2828735 := bstep (se 1 (by rfl) ⟨2121551, by rfl⟩ : syracuseStep 2828735 = 4243103) B4243103
theorem B3385799 : Blo 834351 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B1878911 : Blo 834351 1878911 := bstep (se 1 (by rfl) ⟨1409183, by rfl⟩ : syracuseStep 1878911 = 2818367) B2818367
theorem B1879271 : Blo 834351 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B1061039 : Blo 834351 1061039 := bstep (se 1 (by rfl) ⟨795779, by rfl⟩ : syracuseStep 1061039 = 1591559) B1591559
theorem B55030751 : Blo 834351 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B8043239 : Blo 834351 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B6339383 : Blo 834351 6339383 := bstep (se 1 (by rfl) ⟨4754537, by rfl⟩ : syracuseStep 6339383 = 9509075) B9509075
theorem B5094343 : Blo 834351 5094343 := bstep (se 1 (by rfl) ⟨3820757, by rfl⟩ : syracuseStep 5094343 = 7641515) B7641515
theorem B834719 : Blo 834351 834719 := bstep (se 1 (by rfl) ⟨626039, by rfl⟩ : syracuseStep 834719 = 1252079) B1252079
theorem B1785071 : Blo 834351 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B5356955 : Blo 834351 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B834975 : Blo 834351 834975 := bstep (se 1 (by rfl) ⟨626231, by rfl⟩ : syracuseStep 834975 = 1252463) B1252463
theorem B2113391 : Blo 834351 2113391 := bstep (se 1 (by rfl) ⟨1585043, by rfl⟩ : syracuseStep 2113391 = 3170087) B3170087
theorem B835739 : Blo 834351 835739 := bstep (se 1 (by rfl) ⟨626804, by rfl⟩ : syracuseStep 835739 = 1253609) B1253609
theorem B836327 : Blo 834351 836327 := bstep (se 1 (by rfl) ⟨627245, by rfl⟩ : syracuseStep 836327 = 1254491) B1254491
theorem B836379 : Blo 834351 836379 := bstep (se 1 (by rfl) ⟨627284, by rfl⟩ : syracuseStep 836379 = 1254569) B1254569
theorem B836711 : Blo 834351 836711 := bstep (se 1 (by rfl) ⟨627533, by rfl⟩ : syracuseStep 836711 = 1255067) B1255067
theorem B2376859 : Blo 834351 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B8045891 : Blo 834351 8045891 := bstep (se 1 (by rfl) ⟨6034418, by rfl⟩ : syracuseStep 8045891 = 12068837) B12068837
theorem B4769279 : Blo 834351 4769279 := bstep (se 1 (by rfl) ⟨3576959, by rfl⟩ : syracuseStep 4769279 = 7153919) B7153919
theorem B14272361 : Blo 834351 14272361 := bstep (se 2 (by rfl) ⟨5352135, by rfl⟩ : syracuseStep 14272361 = 10704271) B10704271
theorem B2115497 : Blo 834351 2115497 := bstep (se 2 (by rfl) ⟨793311, by rfl⟩ : syracuseStep 2115497 = 1586623) B1586623
theorem B837759 : Blo 834351 837759 := bstep (se 1 (by rfl) ⟨628319, by rfl⟩ : syracuseStep 837759 = 1256639) B1256639
theorem B6769129 : Blo 834351 6769129 := bstep (se 2 (by rfl) ⟨2538423, by rfl⟩ : syracuseStep 6769129 = 5076847) B5076847
theorem B7229675 : Blo 834351 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B9523655 : Blo 834351 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B4773127 : Blo 834351 4773127 := bstep (se 1 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 4773127 = 7159691) B7159691
theorem B679270157 : Blo 834351 679270157 := bstep (se 3 (by rfl) ⟨127363154, by rfl⟩ : syracuseStep 679270157 = 254726309) B254726309
theorem B2676991 : Blo 834351 2676991 := bstep (se 1 (by rfl) ⟨2007743, by rfl⟩ : syracuseStep 2676991 = 4015487) B4015487
theorem B940783 : Blo 834351 940783 := bstep (se 1 (by rfl) ⟨705587, by rfl⟩ : syracuseStep 940783 = 1411175) B1411175
theorem B4022099 : Blo 834351 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B942439 : Blo 834351 942439 := bstep (se 1 (by rfl) ⟨706829, by rfl⟩ : syracuseStep 942439 = 1413659) B1413659
theorem B6350561 : Blo 834351 6350561 := bstep (se 2 (by rfl) ⟨2381460, by rfl⟩ : syracuseStep 6350561 = 4762921) B4762921
theorem B1338239 : Blo 834351 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B6352019 : Blo 834351 6352019 := bstep (se 1 (by rfl) ⟨4764014, by rfl⟩ : syracuseStep 6352019 = 9528029) B9528029
theorem B2683039 : Blo 834351 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B6189299 : Blo 834351 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B1340059 : Blo 834351 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B4223987 : Blo 834351 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B1504417 : Blo 834351 1504417 := bstep (se 2 (by rfl) ⟨564156, by rfl⟩ : syracuseStep 1504417 = 1128313) B1128313
theorem B3176131 : Blo 834351 3176131 := bstep (se 1 (by rfl) ⟨2382098, by rfl⟩ : syracuseStep 3176131 = 4764197) B4764197
theorem B2816639 : Blo 834351 2816639 := bstep (se 1 (by rfl) ⟨2112479, by rfl⟩ : syracuseStep 2816639 = 4224959) B4224959
theorem B9174431 : Blo 834351 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B3179519 : Blo 834351 3179519 := bstep (se 1 (by rfl) ⟨2384639, by rfl⟩ : syracuseStep 3179519 = 4769279) B4769279
theorem B1410331 : Blo 834351 1410331 := bstep (se 1 (by rfl) ⟨1057748, by rfl⟩ : syracuseStep 1410331 = 2115497) B2115497
theorem B4819783 : Blo 834351 4819783 := bstep (se 1 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 4819783 = 7229675) B7229675
theorem B3577385 : Blo 834351 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B4233707 : Blo 834351 4233707 := bstep (se 1 (by rfl) ⟨3175280, by rfl⟩ : syracuseStep 4233707 = 6350561) B6350561
theorem B15473267 : Blo 834351 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B9181961 : Blo 834351 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B2005889 : Blo 834351 2005889 := bstep (se 2 (by rfl) ⟨752208, by rfl⟩ : syracuseStep 2005889 = 1504417) B1504417
theorem B6364169 : Blo 834351 6364169 := bstep (se 2 (by rfl) ⟨2386563, by rfl⟩ : syracuseStep 6364169 = 4773127) B4773127
theorem B1252607 : Blo 834351 1252607 := bstep (se 1 (by rfl) ⟨939455, by rfl⟩ : syracuseStep 1252607 = 1878911) B1878911
theorem B4234679 : Blo 834351 4234679 := bstep (se 1 (by rfl) ⟨3176009, by rfl⟩ : syracuseStep 4234679 = 6352019) B6352019
theorem B1252847 : Blo 834351 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B4234841 : Blo 834351 4234841 := bstep (se 2 (by rfl) ⟨1588065, by rfl⟩ : syracuseStep 4234841 = 3176131) B3176131
theorem B1254377 : Blo 834351 1254377 := bstep (se 2 (by rfl) ⟨470391, by rfl⟩ : syracuseStep 1254377 = 940783) B940783
theorem B6792457 : Blo 834351 6792457 := bstep (se 2 (by rfl) ⟨2547171, by rfl⟩ : syracuseStep 6792457 = 5094343) B5094343
theorem B1877759 : Blo 834351 1877759 := bstep (se 1 (by rfl) ⟨1408319, by rfl⟩ : syracuseStep 1877759 = 2816639) B2816639
theorem B1190047 : Blo 834351 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B1879145 : Blo 834351 1879145 := bstep (se 2 (by rfl) ⟨704679, by rfl⟩ : syracuseStep 1879145 = 1409359) B1409359
theorem B2829437 : Blo 834351 2829437 := bstep (se 3 (by rfl) ⟨530519, by rfl⟩ : syracuseStep 2829437 = 1061039) B1061039
theorem B1256585 : Blo 834351 1256585 := bstep (se 2 (by rfl) ⟨471219, by rfl⟩ : syracuseStep 1256585 = 942439) B942439
theorem B9514907 : Blo 834351 9514907 := bstep (se 1 (by rfl) ⟨7136180, by rfl⟩ : syracuseStep 9514907 = 14272361) B14272361
theorem B6336467 : Blo 834351 6336467 := bstep (se 1 (by rfl) ⟨4752350, by rfl⟩ : syracuseStep 6336467 = 9504701) B9504701
theorem B4240511 : Blo 834351 4240511 := bstep (se 1 (by rfl) ⟨3180383, by rfl⟩ : syracuseStep 4240511 = 6360767) B6360767
theorem B9025505 : Blo 834351 9025505 := bstep (se 2 (by rfl) ⟨3384564, by rfl⟩ : syracuseStep 9025505 = 6769129) B6769129
theorem B1882907 : Blo 834351 1882907 := bstep (se 1 (by rfl) ⟨1412180, by rfl⟩ : syracuseStep 1882907 = 2824361) B2824361
theorem B835355 : Blo 834351 835355 := bstep (se 1 (by rfl) ⟨626516, by rfl⟩ : syracuseStep 835355 = 1253033) B1253033
theorem B835583 : Blo 834351 835583 := bstep (se 1 (by rfl) ⟨626687, by rfl⟩ : syracuseStep 835583 = 1253375) B1253375
theorem B836223 : Blo 834351 836223 := bstep (se 1 (by rfl) ⟨627167, by rfl⟩ : syracuseStep 836223 = 1254335) B1254335
theorem B1786745 : Blo 834351 1786745 := bstep (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) B1340059
theorem B836543 : Blo 834351 836543 := bstep (se 1 (by rfl) ⟨627407, by rfl⟩ : syracuseStep 836543 = 1254815) B1254815
theorem B837071 : Blo 834351 837071 := bstep (se 1 (by rfl) ⟨627803, by rfl⟩ : syracuseStep 837071 = 1255607) B1255607
theorem B1885787 : Blo 834351 1885787 := bstep (se 1 (by rfl) ⟨1414340, by rfl⟩ : syracuseStep 1885787 = 2828681) B2828681
theorem B837247 : Blo 834351 837247 := bstep (se 1 (by rfl) ⟨627935, by rfl⟩ : syracuseStep 837247 = 1255871) B1255871
theorem B1885823 : Blo 834351 1885823 := bstep (se 1 (by rfl) ⟨1414367, by rfl⟩ : syracuseStep 1885823 = 2828735) B2828735
theorem B36687167 : Blo 834351 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B24465149 : Blo 834351 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B5362159 : Blo 834351 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B5363927 : Blo 834351 5363927 := bstep (se 1 (by rfl) ⟨4022945, by rfl⟩ : syracuseStep 5363927 = 8045891) B8045891
theorem B4282591 : Blo 834351 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B940711 : Blo 834351 940711 := bstep (se 1 (by rfl) ⟨705533, by rfl⟩ : syracuseStep 940711 = 1411067) B1411067
theorem B3169145 : Blo 834351 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B6349103 : Blo 834351 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B452846771 : Blo 834351 452846771 := bstep (se 1 (by rfl) ⟨339635078, by rfl⟩ : syracuseStep 452846771 = 679270157) B679270157
theorem B2681399 : Blo 834351 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B2257199 : Blo 834351 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B3568637 : Blo 834351 3568637 := bstep (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) B1338239
theorem B4126199 : Blo 834351 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B3569321 : Blo 834351 3569321 := bstep (se 2 (by rfl) ⟨1338495, by rfl⟩ : syracuseStep 3569321 = 2676991) B2676991
theorem B2815991 : Blo 834351 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B4226255 : Blo 834351 4226255 := bstep (se 1 (by rfl) ⟨3169691, by rfl⟩ : syracuseStep 4226255 = 6339383) B6339383
theorem B3571303 : Blo 834351 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B1408927 : Blo 834351 1408927 := bstep (se 1 (by rfl) ⟨1056695, by rfl⟩ : syracuseStep 1408927 = 2113391) B2113391
theorem B6426377 : Blo 834351 6426377 := bstep (se 2 (by rfl) ⟨2409891, by rfl⟩ : syracuseStep 6426377 = 4819783) B4819783
theorem B9539693 : Blo 834351 9539693 := bstep (se 3 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 9539693 = 3577385) B3577385
theorem B3575951 : Blo 834351 3575951 := bstep (se 1 (by rfl) ⟨2681963, by rfl⟩ : syracuseStep 3575951 = 5363927) B5363927
theorem B2822471 : Blo 834351 2822471 := bstep (se 1 (by rfl) ⟨2116853, by rfl⟩ : syracuseStep 2822471 = 4233707) B4233707
theorem B2823119 : Blo 834351 2823119 := bstep (se 1 (by rfl) ⟨2117339, by rfl⟩ : syracuseStep 2823119 = 4234679) B4234679
theorem B2823227 : Blo 834351 2823227 := bstep (se 1 (by rfl) ⟨2117420, by rfl⟩ : syracuseStep 2823227 = 4234841) B4234841
theorem B44012789 : Blo 834351 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B4232735 : Blo 834351 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B7149545 : Blo 834351 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B301897847 : Blo 834351 301897847 := bstep (se 1 (by rfl) ⟨226423385, by rfl⟩ : syracuseStep 301897847 = 452846771) B452846771
theorem B1251839 : Blo 834351 1251839 := bstep (se 1 (by rfl) ⟨938879, by rfl⟩ : syracuseStep 1251839 = 1877759) B1877759
theorem B1252763 : Blo 834351 1252763 := bstep (se 1 (by rfl) ⟨939572, by rfl⟩ : syracuseStep 1252763 = 1879145) B1879145
theorem B5349037 : Blo 834351 5349037 := bstep (se 3 (by rfl) ⟨1002944, by rfl⟩ : syracuseStep 5349037 = 2005889) B2005889
theorem B5710121 : Blo 834351 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B2827007 : Blo 834351 2827007 := bstep (se 1 (by rfl) ⟨2120255, by rfl⟩ : syracuseStep 2827007 = 4240511) B4240511
theorem B1254281 : Blo 834351 1254281 := bstep (se 2 (by rfl) ⟨470355, by rfl⟩ : syracuseStep 1254281 = 940711) B940711
theorem B1877327 : Blo 834351 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B1255271 : Blo 834351 1255271 := bstep (se 1 (by rfl) ⟨941453, by rfl⟩ : syracuseStep 1255271 = 1882907) B1882907
theorem B4761737 : Blo 834351 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B1878569 : Blo 834351 1878569 := bstep (se 2 (by rfl) ⟨704463, by rfl⟩ : syracuseStep 1878569 = 1408927) B1408927
theorem B1257191 : Blo 834351 1257191 := bstep (se 1 (by rfl) ⟨942893, by rfl⟩ : syracuseStep 1257191 = 1885787) B1885787
theorem B1257215 : Blo 834351 1257215 := bstep (se 1 (by rfl) ⟨942911, by rfl⟩ : syracuseStep 1257215 = 1885823) B1885823
theorem B9056609 : Blo 834351 9056609 := bstep (se 2 (by rfl) ⟨3396228, by rfl⟩ : syracuseStep 9056609 = 6792457) B6792457
theorem B1880441 : Blo 834351 1880441 := bstep (se 2 (by rfl) ⟨705165, by rfl⟩ : syracuseStep 1880441 = 1410331) B1410331
theorem B24458111 : Blo 834351 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B4764653 : Blo 834351 4764653 := bstep (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) B1786745
theorem B9516365 : Blo 834351 9516365 := bstep (se 3 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 9516365 = 3568637) B3568637
theorem B1586729 : Blo 834351 1586729 := bstep (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) B1190047
theorem B2112763 : Blo 834351 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B4242779 : Blo 834351 4242779 := bstep (se 1 (by rfl) ⟨3182084, by rfl⟩ : syracuseStep 4242779 = 6364169) B6364169
theorem B835071 : Blo 834351 835071 := bstep (se 1 (by rfl) ⟨626303, by rfl⟩ : syracuseStep 835071 = 1252607) B1252607
theorem B835231 : Blo 834351 835231 := bstep (se 1 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 835231 = 1252847) B1252847
theorem B836251 : Blo 834351 836251 := bstep (se 1 (by rfl) ⟨627188, by rfl⟩ : syracuseStep 836251 = 1254377) B1254377
theorem B1787599 : Blo 834351 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B1886291 : Blo 834351 1886291 := bstep (se 1 (by rfl) ⟨1414718, by rfl⟩ : syracuseStep 1886291 = 2829437) B2829437
theorem B837723 : Blo 834351 837723 := bstep (se 1 (by rfl) ⟨628292, by rfl⟩ : syracuseStep 837723 = 1256585) B1256585
theorem B6343271 : Blo 834351 6343271 := bstep (se 1 (by rfl) ⟨4757453, by rfl⟩ : syracuseStep 6343271 = 9514907) B9514907
theorem B2379547 : Blo 834351 2379547 := bstep (se 1 (by rfl) ⟨1784660, by rfl⟩ : syracuseStep 2379547 = 3569321) B3569321
theorem B6017003 : Blo 834351 6017003 := bstep (se 1 (by rfl) ⟨4512752, by rfl⟩ : syracuseStep 6017003 = 9025505) B9025505
theorem B2119679 : Blo 834351 2119679 := bstep (se 1 (by rfl) ⟨1589759, by rfl⟩ : syracuseStep 2119679 = 3179519) B3179519
theorem B16310099 : Blo 834351 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B10315511 : Blo 834351 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B6121307 : Blo 834351 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B4224311 : Blo 834351 4224311 := bstep (se 1 (by rfl) ⟨3168233, by rfl⟩ : syracuseStep 4224311 = 6336467) B6336467
theorem B1504799 : Blo 834351 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B2817503 : Blo 834351 2817503 := bstep (se 1 (by rfl) ⟨2113127, by rfl⟩ : syracuseStep 2817503 = 4226255) B4226255
theorem B4228847 : Blo 834351 4228847 := bstep (se 1 (by rfl) ⟨3171635, by rfl⟩ : syracuseStep 4228847 = 6343271) B6343271
theorem B6359795 : Blo 834351 6359795 := bstep (se 1 (by rfl) ⟨4769846, by rfl⟩ : syracuseStep 6359795 = 9539693) B9539693
theorem B2821823 : Blo 834351 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B1413119 : Blo 834351 1413119 := bstep (se 1 (by rfl) ⟨1059839, by rfl⟩ : syracuseStep 1413119 = 2119679) B2119679
theorem B201265231 : Blo 834351 201265231 := bstep (se 1 (by rfl) ⟨150948923, by rfl⟩ : syracuseStep 201265231 = 301897847) B301897847
theorem B4231277 : Blo 834351 4231277 := bstep (se 3 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 4231277 = 1586729) B1586729
theorem B3806747 : Blo 834351 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B1251551 : Blo 834351 1251551 := bstep (se 1 (by rfl) ⟨938663, by rfl⟩ : syracuseStep 1251551 = 1877327) B1877327
theorem B1252379 : Blo 834351 1252379 := bstep (se 1 (by rfl) ⟨939284, by rfl⟩ : syracuseStep 1252379 = 1878569) B1878569
theorem B6037739 : Blo 834351 6037739 := bstep (se 1 (by rfl) ⟨4528304, by rfl⟩ : syracuseStep 6037739 = 9056609) B9056609
theorem B1253627 : Blo 834351 1253627 := bstep (se 1 (by rfl) ⟨940220, by rfl⟩ : syracuseStep 1253627 = 1880441) B1880441
theorem B2828519 : Blo 834351 2828519 := bstep (se 1 (by rfl) ⟨2121389, by rfl⟩ : syracuseStep 2828519 = 4242779) B4242779
theorem B1878335 : Blo 834351 1878335 := bstep (se 1 (by rfl) ⟨1408751, by rfl⟩ : syracuseStep 1878335 = 2817503) B2817503
theorem B1257527 : Blo 834351 1257527 := bstep (se 1 (by rfl) ⟨943145, by rfl⟩ : syracuseStep 1257527 = 1886291) B1886291
theorem B4011335 : Blo 834351 4011335 := bstep (se 1 (by rfl) ⟨3008501, by rfl⟩ : syracuseStep 4011335 = 6017003) B6017003
theorem B1881647 : Blo 834351 1881647 := bstep (se 1 (by rfl) ⟨1411235, by rfl⟩ : syracuseStep 1881647 = 2822471) B2822471
theorem B1882079 : Blo 834351 1882079 := bstep (se 1 (by rfl) ⟨1411559, by rfl⟩ : syracuseStep 1882079 = 2823119) B2823119
theorem B1882151 : Blo 834351 1882151 := bstep (se 1 (by rfl) ⟨1411613, by rfl⟩ : syracuseStep 1882151 = 2823227) B2823227
theorem B29341859 : Blo 834351 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B4766363 : Blo 834351 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B834559 : Blo 834351 834559 := bstep (se 1 (by rfl) ⟨625919, by rfl⟩ : syracuseStep 834559 = 1251839) B1251839
theorem B835175 : Blo 834351 835175 := bstep (se 1 (by rfl) ⟨626381, by rfl⟩ : syracuseStep 835175 = 1252763) B1252763
theorem B1884671 : Blo 834351 1884671 := bstep (se 1 (by rfl) ⟨1413503, by rfl⟩ : syracuseStep 1884671 = 2827007) B2827007
theorem B836187 : Blo 834351 836187 := bstep (se 1 (by rfl) ⟨627140, by rfl⟩ : syracuseStep 836187 = 1254281) B1254281
theorem B4080871 : Blo 834351 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B836847 : Blo 834351 836847 := bstep (se 1 (by rfl) ⟨627635, by rfl⟩ : syracuseStep 836847 = 1255271) B1255271
theorem B838127 : Blo 834351 838127 := bstep (se 1 (by rfl) ⟨628595, by rfl⟩ : syracuseStep 838127 = 1257191) B1257191
theorem B838143 : Blo 834351 838143 := bstep (se 1 (by rfl) ⟨628607, by rfl⟩ : syracuseStep 838143 = 1257215) B1257215
theorem B16305407 : Blo 834351 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B6344243 : Blo 834351 6344243 := bstep (se 1 (by rfl) ⟨4758182, by rfl⟩ : syracuseStep 6344243 = 9516365) B9516365
theorem B1003199 : Blo 834351 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B7132049 : Blo 834351 7132049 := bstep (se 2 (by rfl) ⟨2674518, by rfl⟩ : syracuseStep 7132049 = 5349037) B5349037
theorem B4284251 : Blo 834351 4284251 := bstep (se 1 (by rfl) ⟨3213188, by rfl⟩ : syracuseStep 4284251 = 6426377) B6426377
theorem B2383967 : Blo 834351 2383967 := bstep (se 1 (by rfl) ⟨1787975, by rfl⟩ : syracuseStep 2383967 = 3575951) B3575951
theorem B3172729 : Blo 834351 3172729 := bstep (se 2 (by rfl) ⟨1189773, by rfl⟩ : syracuseStep 3172729 = 2379547) B2379547
theorem B10873399 : Blo 834351 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B6877007 : Blo 834351 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B3174491 : Blo 834351 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B3176435 : Blo 834351 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B2816207 : Blo 834351 2816207 := bstep (se 1 (by rfl) ⟨2112155, by rfl⟩ : syracuseStep 2816207 = 4224311) B4224311
theorem B9533861 : Blo 834351 9533861 := bstep (se 4 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 9533861 = 1787599) B1787599
theorem B2817017 : Blo 834351 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B2819231 : Blo 834351 2819231 := bstep (se 1 (by rfl) ⟨2114423, by rfl⟩ : syracuseStep 2819231 = 4228847) B4228847
theorem B4229495 : Blo 834351 4229495 := bstep (se 1 (by rfl) ⟨3172121, by rfl⟩ : syracuseStep 4229495 = 6344243) B6344243
theorem B2820851 : Blo 834351 2820851 := bstep (se 1 (by rfl) ⟨2115638, by rfl⟩ : syracuseStep 2820851 = 4231277) B4231277
theorem B4230305 : Blo 834351 4230305 := bstep (se 2 (by rfl) ⟨1586364, by rfl⟩ : syracuseStep 4230305 = 3172729) B3172729
theorem B4754699 : Blo 834351 4754699 := bstep (se 1 (by rfl) ⟨3566024, by rfl⟩ : syracuseStep 4754699 = 7132049) B7132049
theorem B2856167 : Blo 834351 2856167 := bstep (se 1 (by rfl) ⟨2142125, by rfl⟩ : syracuseStep 2856167 = 4284251) B4284251
theorem B21764645 : Blo 834351 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B1252223 : Blo 834351 1252223 := bstep (se 1 (by rfl) ⟨939167, by rfl⟩ : syracuseStep 1252223 = 1878335) B1878335
theorem B1254431 : Blo 834351 1254431 := bstep (se 1 (by rfl) ⟨940823, by rfl⟩ : syracuseStep 1254431 = 1881647) B1881647
theorem B1254719 : Blo 834351 1254719 := bstep (se 1 (by rfl) ⟨941039, by rfl⟩ : syracuseStep 1254719 = 1882079) B1882079
theorem B1254767 : Blo 834351 1254767 := bstep (se 1 (by rfl) ⟨941075, by rfl⟩ : syracuseStep 1254767 = 1882151) B1882151
theorem B1877471 : Blo 834351 1877471 := bstep (se 1 (by rfl) ⟨1408103, by rfl⟩ : syracuseStep 1877471 = 2816207) B2816207
theorem B1878011 : Blo 834351 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B1256447 : Blo 834351 1256447 := bstep (se 1 (by rfl) ⟨942335, by rfl⟩ : syracuseStep 1256447 = 1884671) B1884671
theorem B4239863 : Blo 834351 4239863 := bstep (se 1 (by rfl) ⟨3179897, by rfl⟩ : syracuseStep 4239863 = 6359795) B6359795
theorem B1881215 : Blo 834351 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B14497865 : Blo 834351 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B2537831 : Blo 834351 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B834367 : Blo 834351 834367 := bstep (se 1 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 834367 = 1251551) B1251551
theorem B834919 : Blo 834351 834919 := bstep (se 1 (by rfl) ⟨626189, by rfl⟩ : syracuseStep 834919 = 1252379) B1252379
theorem B1589311 : Blo 834351 1589311 := bstep (se 1 (by rfl) ⟨1191983, by rfl⟩ : syracuseStep 1589311 = 2383967) B2383967
theorem B268353641 : Blo 834351 268353641 := bstep (se 2 (by rfl) ⟨100632615, by rfl⟩ : syracuseStep 268353641 = 201265231) B201265231
theorem B835751 : Blo 834351 835751 := bstep (se 1 (by rfl) ⟨626813, by rfl⟩ : syracuseStep 835751 = 1253627) B1253627
theorem B1885679 : Blo 834351 1885679 := bstep (se 1 (by rfl) ⟨1414259, by rfl⟩ : syracuseStep 1885679 = 2828519) B2828519
theorem B838351 : Blo 834351 838351 := bstep (se 1 (by rfl) ⟨628763, by rfl⟩ : syracuseStep 838351 = 1257527) B1257527
theorem B2116327 : Blo 834351 2116327 := bstep (se 1 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 2116327 = 3174491) B3174491
theorem B2674223 : Blo 834351 2674223 := bstep (se 1 (by rfl) ⟨2005667, by rfl⟩ : syracuseStep 2674223 = 4011335) B4011335
theorem B2117623 : Blo 834351 2117623 := bstep (se 1 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 2117623 = 3176435) B3176435
theorem B2675197 : Blo 834351 2675197 := bstep (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) B1003199
theorem B10870271 : Blo 834351 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B942079 : Blo 834351 942079 := bstep (se 1 (by rfl) ⟨706559, by rfl⟩ : syracuseStep 942079 = 1413119) B1413119
theorem B4025159 : Blo 834351 4025159 := bstep (se 1 (by rfl) ⟨3018869, by rfl⟩ : syracuseStep 4025159 = 6037739) B6037739
theorem B78244957 : Blo 834351 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B4584671 : Blo 834351 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B6355907 : Blo 834351 6355907 := bstep (se 1 (by rfl) ⟨4766930, by rfl⟩ : syracuseStep 6355907 = 9533861) B9533861
theorem B3177575 : Blo 834351 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B2819663 : Blo 834351 2819663 := bstep (se 1 (by rfl) ⟨2114747, by rfl⟩ : syracuseStep 2819663 = 4229495) B4229495
theorem B2820203 : Blo 834351 2820203 := bstep (se 1 (by rfl) ⟨2115152, by rfl⟩ : syracuseStep 2820203 = 4230305) B4230305
theorem B1904111 : Blo 834351 1904111 := bstep (se 1 (by rfl) ⟨1428083, by rfl⟩ : syracuseStep 1904111 = 2856167) B2856167
theorem B2821769 : Blo 834351 2821769 := bstep (se 2 (by rfl) ⟨1058163, by rfl⟩ : syracuseStep 2821769 = 2116327) B2116327
theorem B7246847 : Blo 834351 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B2823497 : Blo 834351 2823497 := bstep (se 2 (by rfl) ⟨1058811, by rfl⟩ : syracuseStep 2823497 = 2117623) B2117623
theorem B417306437 : Blo 834351 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B1251647 : Blo 834351 1251647 := bstep (se 1 (by rfl) ⟨938735, by rfl⟩ : syracuseStep 1251647 = 1877471) B1877471
theorem B1252007 : Blo 834351 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B2826575 : Blo 834351 2826575 := bstep (se 1 (by rfl) ⟨2119931, by rfl⟩ : syracuseStep 2826575 = 4239863) B4239863
theorem B1254143 : Blo 834351 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B3056447 : Blo 834351 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B4237271 : Blo 834351 4237271 := bstep (se 1 (by rfl) ⟨3177953, by rfl⟩ : syracuseStep 4237271 = 6355907) B6355907
theorem B1256105 : Blo 834351 1256105 := bstep (se 2 (by rfl) ⟨471039, by rfl⟩ : syracuseStep 1256105 = 942079) B942079
theorem B1879487 : Blo 834351 1879487 := bstep (se 1 (by rfl) ⟨1409615, by rfl⟩ : syracuseStep 1879487 = 2819231) B2819231
theorem B1257119 : Blo 834351 1257119 := bstep (se 1 (by rfl) ⟨942839, by rfl⟩ : syracuseStep 1257119 = 1885679) B1885679
theorem B1880567 : Blo 834351 1880567 := bstep (se 1 (by rfl) ⟨1410425, by rfl⟩ : syracuseStep 1880567 = 2820851) B2820851
theorem B1782815 : Blo 834351 1782815 := bstep (se 1 (by rfl) ⟨1337111, by rfl⟩ : syracuseStep 1782815 = 2674223) B2674223
theorem B834815 : Blo 834351 834815 := bstep (se 1 (by rfl) ⟨626111, by rfl⟩ : syracuseStep 834815 = 1252223) B1252223
theorem B836287 : Blo 834351 836287 := bstep (se 1 (by rfl) ⟨627215, by rfl⟩ : syracuseStep 836287 = 1254431) B1254431
theorem B836479 : Blo 834351 836479 := bstep (se 1 (by rfl) ⟨627359, by rfl⟩ : syracuseStep 836479 = 1254719) B1254719
theorem B836511 : Blo 834351 836511 := bstep (se 1 (by rfl) ⟨627383, by rfl⟩ : syracuseStep 836511 = 1254767) B1254767
theorem B6767549 : Blo 834351 6767549 := bstep (se 3 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 6767549 = 2537831) B2537831
theorem B837631 : Blo 834351 837631 := bstep (se 1 (by rfl) ⟨628223, by rfl⟩ : syracuseStep 837631 = 1256447) B1256447
theorem B2118383 : Blo 834351 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B178902427 : Blo 834351 178902427 := bstep (se 1 (by rfl) ⟨134176820, by rfl⟩ : syracuseStep 178902427 = 268353641) B268353641
theorem B2119081 : Blo 834351 2119081 := bstep (se 2 (by rfl) ⟨794655, by rfl⟩ : syracuseStep 2119081 = 1589311) B1589311
theorem B3169799 : Blo 834351 3169799 := bstep (se 1 (by rfl) ⟨2377349, by rfl⟩ : syracuseStep 3169799 = 4754699) B4754699
theorem B14509763 : Blo 834351 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B3566929 : Blo 834351 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B2683439 : Blo 834351 2683439 := bstep (se 1 (by rfl) ⟨2012579, by rfl⟩ : syracuseStep 2683439 = 4025159) B4025159
theorem B9665243 : Blo 834351 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B4754173 : Blo 834351 4754173 := bstep (se 3 (by rfl) ⟨891407, by rfl⟩ : syracuseStep 4754173 = 1782815) B1782815
theorem B1412255 : Blo 834351 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B278204291 : Blo 834351 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B4755905 : Blo 834351 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B2037631 : Blo 834351 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B9673175 : Blo 834351 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B2824847 : Blo 834351 2824847 := bstep (se 1 (by rfl) ⟨2118635, by rfl⟩ : syracuseStep 2824847 = 4237271) B4237271
theorem B2825441 : Blo 834351 2825441 := bstep (se 2 (by rfl) ⟨1059540, by rfl⟩ : syracuseStep 2825441 = 2119081) B2119081
theorem B1252991 : Blo 834351 1252991 := bstep (se 1 (by rfl) ⟨939743, by rfl⟩ : syracuseStep 1252991 = 1879487) B1879487
theorem B1253711 : Blo 834351 1253711 := bstep (se 1 (by rfl) ⟨940283, by rfl⟩ : syracuseStep 1253711 = 1880567) B1880567
theorem B1879775 : Blo 834351 1879775 := bstep (se 1 (by rfl) ⟨1409831, by rfl⟩ : syracuseStep 1879775 = 2819663) B2819663
theorem B1880135 : Blo 834351 1880135 := bstep (se 1 (by rfl) ⟨1410101, by rfl⟩ : syracuseStep 1880135 = 2820203) B2820203
theorem B1881179 : Blo 834351 1881179 := bstep (se 1 (by rfl) ⟨1410884, by rfl⟩ : syracuseStep 1881179 = 2821769) B2821769
theorem B1882331 : Blo 834351 1882331 := bstep (se 1 (by rfl) ⟨1411748, by rfl⟩ : syracuseStep 1882331 = 2823497) B2823497
theorem B834431 : Blo 834351 834431 := bstep (se 1 (by rfl) ⟨625823, by rfl⟩ : syracuseStep 834431 = 1251647) B1251647
theorem B834671 : Blo 834351 834671 := bstep (se 1 (by rfl) ⟨626003, by rfl⟩ : syracuseStep 834671 = 1252007) B1252007
theorem B2113199 : Blo 834351 2113199 := bstep (se 1 (by rfl) ⟨1584899, by rfl⟩ : syracuseStep 2113199 = 3169799) B3169799
theorem B1884383 : Blo 834351 1884383 := bstep (se 1 (by rfl) ⟨1413287, by rfl⟩ : syracuseStep 1884383 = 2826575) B2826575
theorem B836095 : Blo 834351 836095 := bstep (se 1 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 836095 = 1254143) B1254143
theorem B837403 : Blo 834351 837403 := bstep (se 1 (by rfl) ⟨628052, by rfl⟩ : syracuseStep 837403 = 1256105) B1256105
theorem B238536569 : Blo 834351 238536569 := bstep (se 2 (by rfl) ⟨89451213, by rfl⟩ : syracuseStep 238536569 = 178902427) B178902427
theorem B838079 : Blo 834351 838079 := bstep (se 1 (by rfl) ⟨628559, by rfl⟩ : syracuseStep 838079 = 1257119) B1257119
theorem B1788959 : Blo 834351 1788959 := bstep (se 1 (by rfl) ⟨1341719, by rfl⟩ : syracuseStep 1788959 = 2683439) B2683439
theorem B6443495 : Blo 834351 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B4511699 : Blo 834351 4511699 := bstep (se 1 (by rfl) ⟨3383774, by rfl⟩ : syracuseStep 4511699 = 6767549) B6767549
theorem B1269407 : Blo 834351 1269407 := bstep (se 1 (by rfl) ⟨952055, by rfl⟩ : syracuseStep 1269407 = 1904111) B1904111
theorem B19324925 : Blo 834351 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B159024379 : Blo 834351 159024379 := bstep (se 1 (by rfl) ⟨119268284, by rfl⟩ : syracuseStep 159024379 = 238536569) B238536569
theorem B185469527 : Blo 834351 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B4295663 : Blo 834351 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B12883283 : Blo 834351 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B1253183 : Blo 834351 1253183 := bstep (se 1 (by rfl) ⟨939887, by rfl⟩ : syracuseStep 1253183 = 1879775) B1879775
theorem B1253423 : Blo 834351 1253423 := bstep (se 1 (by rfl) ⟨940067, by rfl⟩ : syracuseStep 1253423 = 1880135) B1880135
theorem B1254119 : Blo 834351 1254119 := bstep (se 1 (by rfl) ⟨940589, by rfl⟩ : syracuseStep 1254119 = 1881179) B1881179
theorem B1254887 : Blo 834351 1254887 := bstep (se 1 (by rfl) ⟨941165, by rfl⟩ : syracuseStep 1254887 = 1882331) B1882331
theorem B1256255 : Blo 834351 1256255 := bstep (se 1 (by rfl) ⟨942191, by rfl⟩ : syracuseStep 1256255 = 1884383) B1884383
theorem B1192639 : Blo 834351 1192639 := bstep (se 1 (by rfl) ⟨894479, by rfl⟩ : syracuseStep 1192639 = 1788959) B1788959
theorem B6338897 : Blo 834351 6338897 := bstep (se 2 (by rfl) ⟨2377086, by rfl⟩ : syracuseStep 6338897 = 4754173) B4754173
theorem B1883231 : Blo 834351 1883231 := bstep (se 1 (by rfl) ⟨1412423, by rfl⟩ : syracuseStep 1883231 = 2824847) B2824847
theorem B1883627 : Blo 834351 1883627 := bstep (se 1 (by rfl) ⟨1412720, by rfl⟩ : syracuseStep 1883627 = 2825441) B2825441
theorem B835327 : Blo 834351 835327 := bstep (se 1 (by rfl) ⟨626495, by rfl⟩ : syracuseStep 835327 = 1252991) B1252991
theorem B835807 : Blo 834351 835807 := bstep (se 1 (by rfl) ⟨626855, by rfl⟩ : syracuseStep 835807 = 1253711) B1253711
theorem B941503 : Blo 834351 941503 := bstep (se 1 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 941503 = 1412255) B1412255
theorem B3170603 : Blo 834351 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B3007799 : Blo 834351 3007799 := bstep (se 1 (by rfl) ⟨2255849, by rfl⟩ : syracuseStep 3007799 = 4511699) B4511699
theorem B6448783 : Blo 834351 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B846271 : Blo 834351 846271 := bstep (se 1 (by rfl) ⟨634703, by rfl⟩ : syracuseStep 846271 = 1269407) B1269407
theorem B2716841 : Blo 834351 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B1408799 : Blo 834351 1408799 := bstep (se 1 (by rfl) ⟨1056599, by rfl⟩ : syracuseStep 1408799 = 2113199) B2113199
theorem B7244909 : Blo 834351 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B8588855 : Blo 834351 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B2005199 : Blo 834351 2005199 := bstep (se 1 (by rfl) ⟨1503899, by rfl⟩ : syracuseStep 2005199 = 3007799) B3007799
theorem B1255337 : Blo 834351 1255337 := bstep (se 2 (by rfl) ⟨470751, by rfl⟩ : syracuseStep 1255337 = 941503) B941503
theorem B1255487 : Blo 834351 1255487 := bstep (se 1 (by rfl) ⟨941615, by rfl⟩ : syracuseStep 1255487 = 1883231) B1883231
theorem B1255751 : Blo 834351 1255751 := bstep (se 1 (by rfl) ⟨941813, by rfl⟩ : syracuseStep 1255751 = 1883627) B1883627
theorem B123646351 : Blo 834351 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B2863775 : Blo 834351 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B8598377 : Blo 834351 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B835455 : Blo 834351 835455 := bstep (se 1 (by rfl) ⟨626591, by rfl⟩ : syracuseStep 835455 = 1253183) B1253183
theorem B835615 : Blo 834351 835615 := bstep (se 1 (by rfl) ⟨626711, by rfl⟩ : syracuseStep 835615 = 1253423) B1253423
theorem B2113735 : Blo 834351 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B836079 : Blo 834351 836079 := bstep (se 1 (by rfl) ⟨627059, by rfl⟩ : syracuseStep 836079 = 1254119) B1254119
theorem B1590185 : Blo 834351 1590185 := bstep (se 2 (by rfl) ⟨596319, by rfl⟩ : syracuseStep 1590185 = 1192639) B1192639
theorem B836591 : Blo 834351 836591 := bstep (se 1 (by rfl) ⟨627443, by rfl⟩ : syracuseStep 836591 = 1254887) B1254887
theorem B837503 : Blo 834351 837503 := bstep (se 1 (by rfl) ⟨628127, by rfl⟩ : syracuseStep 837503 = 1256255) B1256255
theorem B939199 : Blo 834351 939199 := bstep (se 1 (by rfl) ⟨704399, by rfl⟩ : syracuseStep 939199 = 1408799) B1408799
theorem B212032505 : Blo 834351 212032505 := bstep (se 2 (by rfl) ⟨79512189, by rfl⟩ : syracuseStep 212032505 = 159024379) B159024379
theorem B4513445 : Blo 834351 4513445 := bstep (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) B846271
theorem B4225931 : Blo 834351 4225931 := bstep (se 1 (by rfl) ⟨3169448, by rfl⟩ : syracuseStep 4225931 = 6338897) B6338897
theorem B2818313 : Blo 834351 2818313 := bstep (se 2 (by rfl) ⟨1056867, by rfl⟩ : syracuseStep 2818313 = 2113735) B2113735
theorem B164861801 : Blo 834351 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B1252265 : Blo 834351 1252265 := bstep (se 2 (by rfl) ⟨469599, by rfl⟩ : syracuseStep 1252265 = 939199) B939199
theorem B1909183 : Blo 834351 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B1060123 : Blo 834351 1060123 := bstep (se 1 (by rfl) ⟨795092, by rfl⟩ : syracuseStep 1060123 = 1590185) B1590185
theorem B4829939 : Blo 834351 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B836891 : Blo 834351 836891 := bstep (se 1 (by rfl) ⟨627668, by rfl⟩ : syracuseStep 836891 = 1255337) B1255337
theorem B836991 : Blo 834351 836991 := bstep (se 1 (by rfl) ⟨627743, by rfl⟩ : syracuseStep 836991 = 1255487) B1255487
theorem B837167 : Blo 834351 837167 := bstep (se 1 (by rfl) ⟨627875, by rfl⟩ : syracuseStep 837167 = 1255751) B1255751
theorem B5725903 : Blo 834351 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B1336799 : Blo 834351 1336799 := bstep (se 1 (by rfl) ⟨1002599, by rfl⟩ : syracuseStep 1336799 = 2005199) B2005199
theorem B141355003 : Blo 834351 141355003 := bstep (se 1 (by rfl) ⟨106016252, by rfl⟩ : syracuseStep 141355003 = 212032505) B212032505
theorem B3008963 : Blo 834351 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B5732251 : Blo 834351 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B2817287 : Blo 834351 2817287 := bstep (se 1 (by rfl) ⟨2112965, by rfl⟩ : syracuseStep 2817287 = 4225931) B4225931
theorem B109907867 : Blo 834351 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B1413497 : Blo 834351 1413497 := bstep (se 2 (by rfl) ⟨530061, by rfl⟩ : syracuseStep 1413497 = 1060123) B1060123
theorem B891199 : Blo 834351 891199 := bstep (se 1 (by rfl) ⟨668399, by rfl⟩ : syracuseStep 891199 = 1336799) B1336799
theorem B2005975 : Blo 834351 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B3219959 : Blo 834351 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B1878191 : Blo 834351 1878191 := bstep (se 1 (by rfl) ⟨1408643, by rfl⟩ : syracuseStep 1878191 = 2817287) B2817287
theorem B1878875 : Blo 834351 1878875 := bstep (se 1 (by rfl) ⟨1409156, by rfl⟩ : syracuseStep 1878875 = 2818313) B2818313
theorem B834843 : Blo 834351 834843 := bstep (se 1 (by rfl) ⟨626132, by rfl⟩ : syracuseStep 834843 = 1252265) B1252265
theorem B2545577 : Blo 834351 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B188473337 : Blo 834351 188473337 := bstep (se 2 (by rfl) ⟨70677501, by rfl⟩ : syracuseStep 188473337 = 141355003) B141355003
theorem B30572005 : Blo 834351 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B7634537 : Blo 834351 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B73271911 : Blo 834351 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B1252127 : Blo 834351 1252127 := bstep (se 1 (by rfl) ⟨939095, by rfl⟩ : syracuseStep 1252127 = 1878191) B1878191
theorem B1252583 : Blo 834351 1252583 := bstep (se 1 (by rfl) ⟨939437, by rfl⟩ : syracuseStep 1252583 = 1878875) B1878875
theorem B1188265 : Blo 834351 1188265 := bstep (se 2 (by rfl) ⟨445599, by rfl⟩ : syracuseStep 1188265 = 891199) B891199
theorem B5089691 : Blo 834351 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B125648891 : Blo 834351 125648891 := bstep (se 1 (by rfl) ⟨94236668, by rfl⟩ : syracuseStep 125648891 = 188473337) B188473337
theorem B2146639 : Blo 834351 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B2674633 : Blo 834351 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B942331 : Blo 834351 942331 := bstep (se 1 (by rfl) ⟨706748, by rfl⟩ : syracuseStep 942331 = 1413497) B1413497
theorem B1697051 : Blo 834351 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B40762673 : Blo 834351 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B4525469 : Blo 834351 4525469 := bstep (se 3 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 4525469 = 1697051) B1697051
theorem B27175115 : Blo 834351 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B83765927 : Blo 834351 83765927 := bstep (se 1 (by rfl) ⟨62824445, by rfl⟩ : syracuseStep 83765927 = 125648891) B125648891
theorem B1256441 : Blo 834351 1256441 := bstep (se 2 (by rfl) ⟨471165, by rfl⟩ : syracuseStep 1256441 = 942331) B942331
theorem B2862185 : Blo 834351 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B1584353 : Blo 834351 1584353 := bstep (se 2 (by rfl) ⟨594132, by rfl⟩ : syracuseStep 1584353 = 1188265) B1188265
theorem B97695881 : Blo 834351 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B834751 : Blo 834351 834751 := bstep (se 1 (by rfl) ⟨626063, by rfl⟩ : syracuseStep 834751 = 1252127) B1252127
theorem B835055 : Blo 834351 835055 := bstep (se 1 (by rfl) ⟨626291, by rfl⟩ : syracuseStep 835055 = 1252583) B1252583
theorem B3393127 : Blo 834351 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B3566177 : Blo 834351 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B4524169 : Blo 834351 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B3016979 : Blo 834351 3016979 := bstep (se 1 (by rfl) ⟨2262734, by rfl⟩ : syracuseStep 3016979 = 4525469) B4525469
theorem B1056235 : Blo 834351 1056235 := bstep (se 1 (by rfl) ⟨792176, by rfl⟩ : syracuseStep 1056235 = 1584353) B1584353
theorem B2377451 : Blo 834351 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B837627 : Blo 834351 837627 := bstep (se 1 (by rfl) ⟨628220, by rfl⟩ : syracuseStep 837627 = 1256441) B1256441
theorem B65130587 : Blo 834351 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B30529973 : Blo 834351 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B18116743 : Blo 834351 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B223375805 : Blo 834351 223375805 := bstep (se 3 (by rfl) ⟨41882963, by rfl⟩ : syracuseStep 223375805 = 83765927) B83765927
theorem B43420391 : Blo 834351 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B6032225 : Blo 834351 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B20353315 : Blo 834351 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B24155657 : Blo 834351 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B2011319 : Blo 834351 2011319 := bstep (se 1 (by rfl) ⟨1508489, by rfl⟩ : syracuseStep 2011319 = 3016979) B3016979
theorem B6339869 : Blo 834351 6339869 := bstep (se 3 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 6339869 = 2377451) B2377451
theorem B148917203 : Blo 834351 148917203 := bstep (se 1 (by rfl) ⟨111687902, by rfl⟩ : syracuseStep 148917203 = 223375805) B223375805
theorem B1408313 : Blo 834351 1408313 := bstep (se 2 (by rfl) ⟨528117, by rfl⟩ : syracuseStep 1408313 = 1056235) B1056235
theorem B27137753 : Blo 834351 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B28946927 : Blo 834351 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B16103771 : Blo 834351 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B938875 : Blo 834351 938875 := bstep (se 1 (by rfl) ⟨704156, by rfl⟩ : syracuseStep 938875 = 1408313) B1408313
theorem B4021483 : Blo 834351 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B99278135 : Blo 834351 99278135 := bstep (se 1 (by rfl) ⟨74458601, by rfl⟩ : syracuseStep 99278135 = 148917203) B148917203
theorem B1340879 : Blo 834351 1340879 := bstep (se 1 (by rfl) ⟨1005659, by rfl⟩ : syracuseStep 1340879 = 2011319) B2011319
theorem B4226579 : Blo 834351 4226579 := bstep (se 1 (by rfl) ⟨3169934, by rfl⟩ : syracuseStep 4226579 = 6339869) B6339869
theorem B18091835 : Blo 834351 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B3575677 : Blo 834351 3575677 := bstep (se 3 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 3575677 = 1340879) B1340879
theorem B1251833 : Blo 834351 1251833 := bstep (se 2 (by rfl) ⟨469437, by rfl⟩ : syracuseStep 1251833 = 938875) B938875
theorem B10735847 : Blo 834351 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B5361977 : Blo 834351 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B77191805 : Blo 834351 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B66185423 : Blo 834351 66185423 := bstep (se 1 (by rfl) ⟨49639067, by rfl⟩ : syracuseStep 66185423 = 99278135) B99278135
theorem B2817719 : Blo 834351 2817719 := bstep (se 1 (by rfl) ⟨2113289, by rfl⟩ : syracuseStep 2817719 = 4226579) B4226579
theorem B12061223 : Blo 834351 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B1878479 : Blo 834351 1878479 := bstep (se 1 (by rfl) ⟨1408859, by rfl⟩ : syracuseStep 1878479 = 2817719) B2817719
theorem B14298605 : Blo 834351 14298605 := bstep (se 3 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 14298605 = 5361977) B5361977
theorem B7157231 : Blo 834351 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B834555 : Blo 834351 834555 := bstep (se 1 (by rfl) ⟨625916, by rfl⟩ : syracuseStep 834555 = 1251833) B1251833
theorem B4767569 : Blo 834351 4767569 := bstep (se 2 (by rfl) ⟨1787838, by rfl⟩ : syracuseStep 4767569 = 3575677) B3575677
theorem B44123615 : Blo 834351 44123615 := bstep (se 1 (by rfl) ⟨33092711, by rfl⟩ : syracuseStep 44123615 = 66185423) B66185423
theorem B205844813 : Blo 834351 205844813 := bstep (se 3 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 205844813 = 77191805) B77191805
theorem B1252319 : Blo 834351 1252319 := bstep (se 1 (by rfl) ⟨939239, by rfl⟩ : syracuseStep 1252319 = 1878479) B1878479
theorem B8040815 : Blo 834351 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B4771487 : Blo 834351 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B29415743 : Blo 834351 29415743 := bstep (se 1 (by rfl) ⟨22061807, by rfl⟩ : syracuseStep 29415743 = 44123615) B44123615
theorem B9532403 : Blo 834351 9532403 := bstep (se 1 (by rfl) ⟨7149302, by rfl⟩ : syracuseStep 9532403 = 14298605) B14298605
theorem B137229875 : Blo 834351 137229875 := bstep (se 1 (by rfl) ⟨102922406, by rfl⟩ : syracuseStep 137229875 = 205844813) B205844813
theorem B3178379 : Blo 834351 3178379 := bstep (se 1 (by rfl) ⟨2383784, by rfl⟩ : syracuseStep 3178379 = 4767569) B4767569
theorem B3180991 : Blo 834351 3180991 := bstep (se 1 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 3180991 = 4771487) B4771487
theorem B19610495 : Blo 834351 19610495 := bstep (se 1 (by rfl) ⟨14707871, by rfl⟩ : syracuseStep 19610495 = 29415743) B29415743
theorem B834879 : Blo 834351 834879 := bstep (se 1 (by rfl) ⟨626159, by rfl⟩ : syracuseStep 834879 = 1252319) B1252319
theorem B5360543 : Blo 834351 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B2118919 : Blo 834351 2118919 := bstep (se 1 (by rfl) ⟨1589189, by rfl⟩ : syracuseStep 2118919 = 3178379) B3178379
theorem B6354935 : Blo 834351 6354935 := bstep (se 1 (by rfl) ⟨4766201, by rfl⟩ : syracuseStep 6354935 = 9532403) B9532403
theorem B91486583 : Blo 834351 91486583 := bstep (se 1 (by rfl) ⟨68614937, by rfl⟩ : syracuseStep 91486583 = 137229875) B137229875
theorem B3573695 : Blo 834351 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B2825225 : Blo 834351 2825225 := bstep (se 2 (by rfl) ⟨1059459, by rfl⟩ : syracuseStep 2825225 = 2118919) B2118919
theorem B4236623 : Blo 834351 4236623 := bstep (se 1 (by rfl) ⟨3177467, by rfl⟩ : syracuseStep 4236623 = 6354935) B6354935
theorem B60991055 : Blo 834351 60991055 := bstep (se 1 (by rfl) ⟨45743291, by rfl⟩ : syracuseStep 60991055 = 91486583) B91486583
theorem B4241321 : Blo 834351 4241321 := bstep (se 2 (by rfl) ⟨1590495, by rfl⟩ : syracuseStep 4241321 = 3180991) B3180991
theorem B13073663 : Blo 834351 13073663 := bstep (se 1 (by rfl) ⟨9805247, by rfl⟩ : syracuseStep 13073663 = 19610495) B19610495
theorem B2824415 : Blo 834351 2824415 := bstep (se 1 (by rfl) ⟨2118311, by rfl⟩ : syracuseStep 2824415 = 4236623) B4236623
theorem B2827547 : Blo 834351 2827547 := bstep (se 1 (by rfl) ⟨2120660, by rfl⟩ : syracuseStep 2827547 = 4241321) B4241321
theorem B1883483 : Blo 834351 1883483 := bstep (se 1 (by rfl) ⟨1412612, by rfl⟩ : syracuseStep 1883483 = 2825225) B2825225
theorem B2382463 : Blo 834351 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B40660703 : Blo 834351 40660703 := bstep (se 1 (by rfl) ⟨30495527, by rfl⟩ : syracuseStep 40660703 = 60991055) B60991055
theorem B34863101 : Blo 834351 34863101 := bstep (se 3 (by rfl) ⟨6536831, by rfl⟩ : syracuseStep 34863101 = 13073663) B13073663
theorem B27107135 : Blo 834351 27107135 := bstep (se 1 (by rfl) ⟨20330351, by rfl⟩ : syracuseStep 27107135 = 40660703) B40660703
theorem B23242067 : Blo 834351 23242067 := bstep (se 1 (by rfl) ⟨17431550, by rfl⟩ : syracuseStep 23242067 = 34863101) B34863101
theorem B1255655 : Blo 834351 1255655 := bstep (se 1 (by rfl) ⟨941741, by rfl⟩ : syracuseStep 1255655 = 1883483) B1883483
theorem B1882943 : Blo 834351 1882943 := bstep (se 1 (by rfl) ⟨1412207, by rfl⟩ : syracuseStep 1882943 = 2824415) B2824415
theorem B1885031 : Blo 834351 1885031 := bstep (se 1 (by rfl) ⟨1413773, by rfl⟩ : syracuseStep 1885031 = 2827547) B2827547
theorem B3176617 : Blo 834351 3176617 := bstep (se 2 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 3176617 = 2382463) B2382463
theorem B991661525 : Blo 834351 991661525 := bstep (se 7 (by rfl) ⟨11621033, by rfl⟩ : syracuseStep 991661525 = 23242067) B23242067
theorem B4235489 : Blo 834351 4235489 := bstep (se 2 (by rfl) ⟨1588308, by rfl⟩ : syracuseStep 4235489 = 3176617) B3176617
theorem B1255295 : Blo 834351 1255295 := bstep (se 1 (by rfl) ⟨941471, by rfl⟩ : syracuseStep 1255295 = 1882943) B1882943
theorem B1256687 : Blo 834351 1256687 := bstep (se 1 (by rfl) ⟨942515, by rfl⟩ : syracuseStep 1256687 = 1885031) B1885031
theorem B18071423 : Blo 834351 18071423 := bstep (se 1 (by rfl) ⟨13553567, by rfl⟩ : syracuseStep 18071423 = 27107135) B27107135
theorem B837103 : Blo 834351 837103 := bstep (se 1 (by rfl) ⟨627827, by rfl⟩ : syracuseStep 837103 = 1255655) B1255655
theorem B2823659 : Blo 834351 2823659 := bstep (se 1 (by rfl) ⟨2117744, by rfl⟩ : syracuseStep 2823659 = 4235489) B4235489
theorem B661107683 : Blo 834351 661107683 := bstep (se 1 (by rfl) ⟨495830762, by rfl⟩ : syracuseStep 661107683 = 991661525) B991661525
theorem B836863 : Blo 834351 836863 := bstep (se 1 (by rfl) ⟨627647, by rfl⟩ : syracuseStep 836863 = 1255295) B1255295
theorem B837791 : Blo 834351 837791 := bstep (se 1 (by rfl) ⟨628343, by rfl⟩ : syracuseStep 837791 = 1256687) B1256687
theorem B12047615 : Blo 834351 12047615 := bstep (se 1 (by rfl) ⟨9035711, by rfl⟩ : syracuseStep 12047615 = 18071423) B18071423
theorem B8031743 : Blo 834351 8031743 := bstep (se 1 (by rfl) ⟨6023807, by rfl⟩ : syracuseStep 8031743 = 12047615) B12047615
theorem B440738455 : Blo 834351 440738455 := bstep (se 1 (by rfl) ⟨330553841, by rfl⟩ : syracuseStep 440738455 = 661107683) B661107683
theorem B1882439 : Blo 834351 1882439 := bstep (se 1 (by rfl) ⟨1411829, by rfl⟩ : syracuseStep 1882439 = 2823659) B2823659
theorem B1254959 : Blo 834351 1254959 := bstep (se 1 (by rfl) ⟨941219, by rfl⟩ : syracuseStep 1254959 = 1882439) B1882439
theorem B5354495 : Blo 834351 5354495 := bstep (se 1 (by rfl) ⟨4015871, by rfl⟩ : syracuseStep 5354495 = 8031743) B8031743
theorem B587651273 : Blo 834351 587651273 := bstep (se 2 (by rfl) ⟨220369227, by rfl⟩ : syracuseStep 587651273 = 440738455) B440738455
theorem B836639 : Blo 834351 836639 := bstep (se 1 (by rfl) ⟨627479, by rfl⟩ : syracuseStep 836639 = 1254959) B1254959
theorem B391767515 : Blo 834351 391767515 := bstep (se 1 (by rfl) ⟨293825636, by rfl⟩ : syracuseStep 391767515 = 587651273) B587651273
theorem B3569663 : Blo 834351 3569663 := bstep (se 1 (by rfl) ⟨2677247, by rfl⟩ : syracuseStep 3569663 = 5354495) B5354495
theorem B261178343 : Blo 834351 261178343 := bstep (se 1 (by rfl) ⟨195883757, by rfl⟩ : syracuseStep 261178343 = 391767515) B391767515
theorem B2379775 : Blo 834351 2379775 := bstep (se 1 (by rfl) ⟨1784831, by rfl⟩ : syracuseStep 2379775 = 3569663) B3569663
theorem B174118895 : Blo 834351 174118895 := bstep (se 1 (by rfl) ⟨130589171, by rfl⟩ : syracuseStep 174118895 = 261178343) B261178343
theorem B3173033 : Blo 834351 3173033 := bstep (se 2 (by rfl) ⟨1189887, by rfl⟩ : syracuseStep 3173033 = 2379775) B2379775
theorem B116079263 : Blo 834351 116079263 := bstep (se 1 (by rfl) ⟨87059447, by rfl⟩ : syracuseStep 116079263 = 174118895) B174118895
theorem B2115355 : Blo 834351 2115355 := bstep (se 1 (by rfl) ⟨1586516, by rfl⟩ : syracuseStep 2115355 = 3173033) B3173033
theorem B2820473 : Blo 834351 2820473 := bstep (se 2 (by rfl) ⟨1057677, by rfl⟩ : syracuseStep 2820473 = 2115355) B2115355
theorem B77386175 : Blo 834351 77386175 := bstep (se 1 (by rfl) ⟨58039631, by rfl⟩ : syracuseStep 77386175 = 116079263) B116079263
theorem B1880315 : Blo 834351 1880315 := bstep (se 1 (by rfl) ⟨1410236, by rfl⟩ : syracuseStep 1880315 = 2820473) B2820473
theorem B51590783 : Blo 834351 51590783 := bstep (se 1 (by rfl) ⟨38693087, by rfl⟩ : syracuseStep 51590783 = 77386175) B77386175
theorem B1253543 : Blo 834351 1253543 := bstep (se 1 (by rfl) ⟨940157, by rfl⟩ : syracuseStep 1253543 = 1880315) B1880315
theorem B34393855 : Blo 834351 34393855 := bstep (se 1 (by rfl) ⟨25795391, by rfl⟩ : syracuseStep 34393855 = 51590783) B51590783
theorem B45858473 : Blo 834351 45858473 := bstep (se 2 (by rfl) ⟨17196927, by rfl⟩ : syracuseStep 45858473 = 34393855) B34393855
theorem B835695 : Blo 834351 835695 := bstep (se 1 (by rfl) ⟨626771, by rfl⟩ : syracuseStep 835695 = 1253543) B1253543
theorem B30572315 : Blo 834351 30572315 := bstep (se 1 (by rfl) ⟨22929236, by rfl⟩ : syracuseStep 30572315 = 45858473) B45858473
theorem B20381543 : Blo 834351 20381543 := bstep (se 1 (by rfl) ⟨15286157, by rfl⟩ : syracuseStep 20381543 = 30572315) B30572315
theorem B13587695 : Blo 834351 13587695 := bstep (se 1 (by rfl) ⟨10190771, by rfl⟩ : syracuseStep 13587695 = 20381543) B20381543
theorem B9058463 : Blo 834351 9058463 := bstep (se 1 (by rfl) ⟨6793847, by rfl⟩ : syracuseStep 9058463 = 13587695) B13587695
theorem B6038975 : Blo 834351 6038975 := bstep (se 1 (by rfl) ⟨4529231, by rfl⟩ : syracuseStep 6038975 = 9058463) B9058463
theorem B4025983 : Blo 834351 4025983 := bstep (se 1 (by rfl) ⟨3019487, by rfl⟩ : syracuseStep 4025983 = 6038975) B6038975
theorem B5367977 : Blo 834351 5367977 := bstep (se 2 (by rfl) ⟨2012991, by rfl⟩ : syracuseStep 5367977 = 4025983) B4025983
theorem B3578651 : Blo 834351 3578651 := bstep (se 1 (by rfl) ⟨2683988, by rfl⟩ : syracuseStep 3578651 = 5367977) B5367977
theorem B2385767 : Blo 834351 2385767 := bstep (se 1 (by rfl) ⟨1789325, by rfl⟩ : syracuseStep 2385767 = 3578651) B3578651
theorem B1590511 : Blo 834351 1590511 := bstep (se 1 (by rfl) ⟨1192883, by rfl⟩ : syracuseStep 1590511 = 2385767) B2385767
theorem B2120681 : Blo 834351 2120681 := bstep (se 2 (by rfl) ⟨795255, by rfl⟩ : syracuseStep 2120681 = 1590511) B1590511
theorem B1413787 : Blo 834351 1413787 := bstep (se 1 (by rfl) ⟨1060340, by rfl⟩ : syracuseStep 1413787 = 2120681) B2120681
theorem B1885049 : Blo 834351 1885049 := bstep (se 2 (by rfl) ⟨706893, by rfl⟩ : syracuseStep 1885049 = 1413787) B1413787
theorem B1256699 : Blo 834351 1256699 := bstep (se 1 (by rfl) ⟨942524, by rfl⟩ : syracuseStep 1256699 = 1885049) B1885049
theorem B837799 : Blo 834351 837799 := bstep (se 1 (by rfl) ⟨628349, by rfl⟩ : syracuseStep 837799 = 1256699) B1256699

theorem C0 (j : ℕ) (h1 : 208587 ≤ j) (h2 : j ≤ 209286) : Blo 834351 (4 * j + 3) := by
  interval_cases j
  · exact B834351
  · exact B834355
  · exact B834359
  · exact B834363
  · exact B834367
  · exact B834371
  · exact B834375
  · exact B834379
  · exact B834383
  · exact B834387
  · exact B834391
  · exact B834395
  · exact B834399
  · exact B834403
  · exact B834407
  · exact B834411
  · exact B834415
  · exact B834419
  · exact B834423
  · exact B834427
  · exact B834431
  · exact B834435
  · exact B834439
  · exact B834443
  · exact B834447
  · exact B834451
  · exact B834455
  · exact B834459
  · exact B834463
  · exact B834467
  · exact B834471
  · exact B834475
  · exact B834479
  · exact B834483
  · exact B834487
  · exact B834491
  · exact B834495
  · exact B834499
  · exact B834503
  · exact B834507
  · exact B834511
  · exact B834515
  · exact B834519
  · exact B834523
  · exact B834527
  · exact B834531
  · exact B834535
  · exact B834539
  · exact B834543
  · exact B834547
  · exact B834551
  · exact B834555
  · exact B834559
  · exact B834563
  · exact B834567
  · exact B834571
  · exact B834575
  · exact B834579
  · exact B834583
  · exact B834587
  · exact B834591
  · exact B834595
  · exact B834599
  · exact B834603
  · exact B834607
  · exact B834611
  · exact B834615
  · exact B834619
  · exact B834623
  · exact B834627
  · exact B834631
  · exact B834635
  · exact B834639
  · exact B834643
  · exact B834647
  · exact B834651
  · exact B834655
  · exact B834659
  · exact B834663
  · exact B834667
  · exact B834671
  · exact B834675
  · exact B834679
  · exact B834683
  · exact B834687
  · exact B834691
  · exact B834695
  · exact B834699
  · exact B834703
  · exact B834707
  · exact B834711
  · exact B834715
  · exact B834719
  · exact B834723
  · exact B834727
  · exact B834731
  · exact B834735
  · exact B834739
  · exact B834743
  · exact B834747
  · exact B834751
  · exact B834755
  · exact B834759
  · exact B834763
  · exact B834767
  · exact B834771
  · exact B834775
  · exact B834779
  · exact B834783
  · exact B834787
  · exact B834791
  · exact B834795
  · exact B834799
  · exact B834803
  · exact B834807
  · exact B834811
  · exact B834815
  · exact B834819
  · exact B834823
  · exact B834827
  · exact B834831
  · exact B834835
  · exact B834839
  · exact B834843
  · exact B834847
  · exact B834851
  · exact B834855
  · exact B834859
  · exact B834863
  · exact B834867
  · exact B834871
  · exact B834875
  · exact B834879
  · exact B834883
  · exact B834887
  · exact B834891
  · exact B834895
  · exact B834899
  · exact B834903
  · exact B834907
  · exact B834911
  · exact B834915
  · exact B834919
  · exact B834923
  · exact B834927
  · exact B834931
  · exact B834935
  · exact B834939
  · exact B834943
  · exact B834947
  · exact B834951
  · exact B834955
  · exact B834959
  · exact B834963
  · exact B834967
  · exact B834971
  · exact B834975
  · exact B834979
  · exact B834983
  · exact B834987
  · exact B834991
  · exact B834995
  · exact B834999
  · exact B835003
  · exact B835007
  · exact B835011
  · exact B835015
  · exact B835019
  · exact B835023
  · exact B835027
  · exact B835031
  · exact B835035
  · exact B835039
  · exact B835043
  · exact B835047
  · exact B835051
  · exact B835055
  · exact B835059
  · exact B835063
  · exact B835067
  · exact B835071
  · exact B835075
  · exact B835079
  · exact B835083
  · exact B835087
  · exact B835091
  · exact B835095
  · exact B835099
  · exact B835103
  · exact B835107
  · exact B835111
  · exact B835115
  · exact B835119
  · exact B835123
  · exact B835127
  · exact B835131
  · exact B835135
  · exact B835139
  · exact B835143
  · exact B835147
  · exact B835151
  · exact B835155
  · exact B835159
  · exact B835163
  · exact B835167
  · exact B835171
  · exact B835175
  · exact B835179
  · exact B835183
  · exact B835187
  · exact B835191
  · exact B835195
  · exact B835199
  · exact B835203
  · exact B835207
  · exact B835211
  · exact B835215
  · exact B835219
  · exact B835223
  · exact B835227
  · exact B835231
  · exact B835235
  · exact B835239
  · exact B835243
  · exact B835247
  · exact B835251
  · exact B835255
  · exact B835259
  · exact B835263
  · exact B835267
  · exact B835271
  · exact B835275
  · exact B835279
  · exact B835283
  · exact B835287
  · exact B835291
  · exact B835295
  · exact B835299
  · exact B835303
  · exact B835307
  · exact B835311
  · exact B835315
  · exact B835319
  · exact B835323
  · exact B835327
  · exact B835331
  · exact B835335
  · exact B835339
  · exact B835343
  · exact B835347
  · exact B835351
  · exact B835355
  · exact B835359
  · exact B835363
  · exact B835367
  · exact B835371
  · exact B835375
  · exact B835379
  · exact B835383
  · exact B835387
  · exact B835391
  · exact B835395
  · exact B835399
  · exact B835403
  · exact B835407
  · exact B835411
  · exact B835415
  · exact B835419
  · exact B835423
  · exact B835427
  · exact B835431
  · exact B835435
  · exact B835439
  · exact B835443
  · exact B835447
  · exact B835451
  · exact B835455
  · exact B835459
  · exact B835463
  · exact B835467
  · exact B835471
  · exact B835475
  · exact B835479
  · exact B835483
  · exact B835487
  · exact B835491
  · exact B835495
  · exact B835499
  · exact B835503
  · exact B835507
  · exact B835511
  · exact B835515
  · exact B835519
  · exact B835523
  · exact B835527
  · exact B835531
  · exact B835535
  · exact B835539
  · exact B835543
  · exact B835547
  · exact B835551
  · exact B835555
  · exact B835559
  · exact B835563
  · exact B835567
  · exact B835571
  · exact B835575
  · exact B835579
  · exact B835583
  · exact B835587
  · exact B835591
  · exact B835595
  · exact B835599
  · exact B835603
  · exact B835607
  · exact B835611
  · exact B835615
  · exact B835619
  · exact B835623
  · exact B835627
  · exact B835631
  · exact B835635
  · exact B835639
  · exact B835643
  · exact B835647
  · exact B835651
  · exact B835655
  · exact B835659
  · exact B835663
  · exact B835667
  · exact B835671
  · exact B835675
  · exact B835679
  · exact B835683
  · exact B835687
  · exact B835691
  · exact B835695
  · exact B835699
  · exact B835703
  · exact B835707
  · exact B835711
  · exact B835715
  · exact B835719
  · exact B835723
  · exact B835727
  · exact B835731
  · exact B835735
  · exact B835739
  · exact B835743
  · exact B835747
  · exact B835751
  · exact B835755
  · exact B835759
  · exact B835763
  · exact B835767
  · exact B835771
  · exact B835775
  · exact B835779
  · exact B835783
  · exact B835787
  · exact B835791
  · exact B835795
  · exact B835799
  · exact B835803
  · exact B835807
  · exact B835811
  · exact B835815
  · exact B835819
  · exact B835823
  · exact B835827
  · exact B835831
  · exact B835835
  · exact B835839
  · exact B835843
  · exact B835847
  · exact B835851
  · exact B835855
  · exact B835859
  · exact B835863
  · exact B835867
  · exact B835871
  · exact B835875
  · exact B835879
  · exact B835883
  · exact B835887
  · exact B835891
  · exact B835895
  · exact B835899
  · exact B835903
  · exact B835907
  · exact B835911
  · exact B835915
  · exact B835919
  · exact B835923
  · exact B835927
  · exact B835931
  · exact B835935
  · exact B835939
  · exact B835943
  · exact B835947
  · exact B835951
  · exact B835955
  · exact B835959
  · exact B835963
  · exact B835967
  · exact B835971
  · exact B835975
  · exact B835979
  · exact B835983
  · exact B835987
  · exact B835991
  · exact B835995
  · exact B835999
  · exact B836003
  · exact B836007
  · exact B836011
  · exact B836015
  · exact B836019
  · exact B836023
  · exact B836027
  · exact B836031
  · exact B836035
  · exact B836039
  · exact B836043
  · exact B836047
  · exact B836051
  · exact B836055
  · exact B836059
  · exact B836063
  · exact B836067
  · exact B836071
  · exact B836075
  · exact B836079
  · exact B836083
  · exact B836087
  · exact B836091
  · exact B836095
  · exact B836099
  · exact B836103
  · exact B836107
  · exact B836111
  · exact B836115
  · exact B836119
  · exact B836123
  · exact B836127
  · exact B836131
  · exact B836135
  · exact B836139
  · exact B836143
  · exact B836147
  · exact B836151
  · exact B836155
  · exact B836159
  · exact B836163
  · exact B836167
  · exact B836171
  · exact B836175
  · exact B836179
  · exact B836183
  · exact B836187
  · exact B836191
  · exact B836195
  · exact B836199
  · exact B836203
  · exact B836207
  · exact B836211
  · exact B836215
  · exact B836219
  · exact B836223
  · exact B836227
  · exact B836231
  · exact B836235
  · exact B836239
  · exact B836243
  · exact B836247
  · exact B836251
  · exact B836255
  · exact B836259
  · exact B836263
  · exact B836267
  · exact B836271
  · exact B836275
  · exact B836279
  · exact B836283
  · exact B836287
  · exact B836291
  · exact B836295
  · exact B836299
  · exact B836303
  · exact B836307
  · exact B836311
  · exact B836315
  · exact B836319
  · exact B836323
  · exact B836327
  · exact B836331
  · exact B836335
  · exact B836339
  · exact B836343
  · exact B836347
  · exact B836351
  · exact B836355
  · exact B836359
  · exact B836363
  · exact B836367
  · exact B836371
  · exact B836375
  · exact B836379
  · exact B836383
  · exact B836387
  · exact B836391
  · exact B836395
  · exact B836399
  · exact B836403
  · exact B836407
  · exact B836411
  · exact B836415
  · exact B836419
  · exact B836423
  · exact B836427
  · exact B836431
  · exact B836435
  · exact B836439
  · exact B836443
  · exact B836447
  · exact B836451
  · exact B836455
  · exact B836459
  · exact B836463
  · exact B836467
  · exact B836471
  · exact B836475
  · exact B836479
  · exact B836483
  · exact B836487
  · exact B836491
  · exact B836495
  · exact B836499
  · exact B836503
  · exact B836507
  · exact B836511
  · exact B836515
  · exact B836519
  · exact B836523
  · exact B836527
  · exact B836531
  · exact B836535
  · exact B836539
  · exact B836543
  · exact B836547
  · exact B836551
  · exact B836555
  · exact B836559
  · exact B836563
  · exact B836567
  · exact B836571
  · exact B836575
  · exact B836579
  · exact B836583
  · exact B836587
  · exact B836591
  · exact B836595
  · exact B836599
  · exact B836603
  · exact B836607
  · exact B836611
  · exact B836615
  · exact B836619
  · exact B836623
  · exact B836627
  · exact B836631
  · exact B836635
  · exact B836639
  · exact B836643
  · exact B836647
  · exact B836651
  · exact B836655
  · exact B836659
  · exact B836663
  · exact B836667
  · exact B836671
  · exact B836675
  · exact B836679
  · exact B836683
  · exact B836687
  · exact B836691
  · exact B836695
  · exact B836699
  · exact B836703
  · exact B836707
  · exact B836711
  · exact B836715
  · exact B836719
  · exact B836723
  · exact B836727
  · exact B836731
  · exact B836735
  · exact B836739
  · exact B836743
  · exact B836747
  · exact B836751
  · exact B836755
  · exact B836759
  · exact B836763
  · exact B836767
  · exact B836771
  · exact B836775
  · exact B836779
  · exact B836783
  · exact B836787
  · exact B836791
  · exact B836795
  · exact B836799
  · exact B836803
  · exact B836807
  · exact B836811
  · exact B836815
  · exact B836819
  · exact B836823
  · exact B836827
  · exact B836831
  · exact B836835
  · exact B836839
  · exact B836843
  · exact B836847
  · exact B836851
  · exact B836855
  · exact B836859
  · exact B836863
  · exact B836867
  · exact B836871
  · exact B836875
  · exact B836879
  · exact B836883
  · exact B836887
  · exact B836891
  · exact B836895
  · exact B836899
  · exact B836903
  · exact B836907
  · exact B836911
  · exact B836915
  · exact B836919
  · exact B836923
  · exact B836927
  · exact B836931
  · exact B836935
  · exact B836939
  · exact B836943
  · exact B836947
  · exact B836951
  · exact B836955
  · exact B836959
  · exact B836963
  · exact B836967
  · exact B836971
  · exact B836975
  · exact B836979
  · exact B836983
  · exact B836987
  · exact B836991
  · exact B836995
  · exact B836999
  · exact B837003
  · exact B837007
  · exact B837011
  · exact B837015
  · exact B837019
  · exact B837023
  · exact B837027
  · exact B837031
  · exact B837035
  · exact B837039
  · exact B837043
  · exact B837047
  · exact B837051
  · exact B837055
  · exact B837059
  · exact B837063
  · exact B837067
  · exact B837071
  · exact B837075
  · exact B837079
  · exact B837083
  · exact B837087
  · exact B837091
  · exact B837095
  · exact B837099
  · exact B837103
  · exact B837107
  · exact B837111
  · exact B837115
  · exact B837119
  · exact B837123
  · exact B837127
  · exact B837131
  · exact B837135
  · exact B837139
  · exact B837143
  · exact B837147

theorem C1 (j : ℕ) (h1 : 209287 ≤ j) (h2 : j ≤ 209587) : Blo 834351 (4 * j + 3) := by
  interval_cases j
  · exact B837151
  · exact B837155
  · exact B837159
  · exact B837163
  · exact B837167
  · exact B837171
  · exact B837175
  · exact B837179
  · exact B837183
  · exact B837187
  · exact B837191
  · exact B837195
  · exact B837199
  · exact B837203
  · exact B837207
  · exact B837211
  · exact B837215
  · exact B837219
  · exact B837223
  · exact B837227
  · exact B837231
  · exact B837235
  · exact B837239
  · exact B837243
  · exact B837247
  · exact B837251
  · exact B837255
  · exact B837259
  · exact B837263
  · exact B837267
  · exact B837271
  · exact B837275
  · exact B837279
  · exact B837283
  · exact B837287
  · exact B837291
  · exact B837295
  · exact B837299
  · exact B837303
  · exact B837307
  · exact B837311
  · exact B837315
  · exact B837319
  · exact B837323
  · exact B837327
  · exact B837331
  · exact B837335
  · exact B837339
  · exact B837343
  · exact B837347
  · exact B837351
  · exact B837355
  · exact B837359
  · exact B837363
  · exact B837367
  · exact B837371
  · exact B837375
  · exact B837379
  · exact B837383
  · exact B837387
  · exact B837391
  · exact B837395
  · exact B837399
  · exact B837403
  · exact B837407
  · exact B837411
  · exact B837415
  · exact B837419
  · exact B837423
  · exact B837427
  · exact B837431
  · exact B837435
  · exact B837439
  · exact B837443
  · exact B837447
  · exact B837451
  · exact B837455
  · exact B837459
  · exact B837463
  · exact B837467
  · exact B837471
  · exact B837475
  · exact B837479
  · exact B837483
  · exact B837487
  · exact B837491
  · exact B837495
  · exact B837499
  · exact B837503
  · exact B837507
  · exact B837511
  · exact B837515
  · exact B837519
  · exact B837523
  · exact B837527
  · exact B837531
  · exact B837535
  · exact B837539
  · exact B837543
  · exact B837547
  · exact B837551
  · exact B837555
  · exact B837559
  · exact B837563
  · exact B837567
  · exact B837571
  · exact B837575
  · exact B837579
  · exact B837583
  · exact B837587
  · exact B837591
  · exact B837595
  · exact B837599
  · exact B837603
  · exact B837607
  · exact B837611
  · exact B837615
  · exact B837619
  · exact B837623
  · exact B837627
  · exact B837631
  · exact B837635
  · exact B837639
  · exact B837643
  · exact B837647
  · exact B837651
  · exact B837655
  · exact B837659
  · exact B837663
  · exact B837667
  · exact B837671
  · exact B837675
  · exact B837679
  · exact B837683
  · exact B837687
  · exact B837691
  · exact B837695
  · exact B837699
  · exact B837703
  · exact B837707
  · exact B837711
  · exact B837715
  · exact B837719
  · exact B837723
  · exact B837727
  · exact B837731
  · exact B837735
  · exact B837739
  · exact B837743
  · exact B837747
  · exact B837751
  · exact B837755
  · exact B837759
  · exact B837763
  · exact B837767
  · exact B837771
  · exact B837775
  · exact B837779
  · exact B837783
  · exact B837787
  · exact B837791
  · exact B837795
  · exact B837799
  · exact B837803
  · exact B837807
  · exact B837811
  · exact B837815
  · exact B837819
  · exact B837823
  · exact B837827
  · exact B837831
  · exact B837835
  · exact B837839
  · exact B837843
  · exact B837847
  · exact B837851
  · exact B837855
  · exact B837859
  · exact B837863
  · exact B837867
  · exact B837871
  · exact B837875
  · exact B837879
  · exact B837883
  · exact B837887
  · exact B837891
  · exact B837895
  · exact B837899
  · exact B837903
  · exact B837907
  · exact B837911
  · exact B837915
  · exact B837919
  · exact B837923
  · exact B837927
  · exact B837931
  · exact B837935
  · exact B837939
  · exact B837943
  · exact B837947
  · exact B837951
  · exact B837955
  · exact B837959
  · exact B837963
  · exact B837967
  · exact B837971
  · exact B837975
  · exact B837979
  · exact B837983
  · exact B837987
  · exact B837991
  · exact B837995
  · exact B837999
  · exact B838003
  · exact B838007
  · exact B838011
  · exact B838015
  · exact B838019
  · exact B838023
  · exact B838027
  · exact B838031
  · exact B838035
  · exact B838039
  · exact B838043
  · exact B838047
  · exact B838051
  · exact B838055
  · exact B838059
  · exact B838063
  · exact B838067
  · exact B838071
  · exact B838075
  · exact B838079
  · exact B838083
  · exact B838087
  · exact B838091
  · exact B838095
  · exact B838099
  · exact B838103
  · exact B838107
  · exact B838111
  · exact B838115
  · exact B838119
  · exact B838123
  · exact B838127
  · exact B838131
  · exact B838135
  · exact B838139
  · exact B838143
  · exact B838147
  · exact B838151
  · exact B838155
  · exact B838159
  · exact B838163
  · exact B838167
  · exact B838171
  · exact B838175
  · exact B838179
  · exact B838183
  · exact B838187
  · exact B838191
  · exact B838195
  · exact B838199
  · exact B838203
  · exact B838207
  · exact B838211
  · exact B838215
  · exact B838219
  · exact B838223
  · exact B838227
  · exact B838231
  · exact B838235
  · exact B838239
  · exact B838243
  · exact B838247
  · exact B838251
  · exact B838255
  · exact B838259
  · exact B838263
  · exact B838267
  · exact B838271
  · exact B838275
  · exact B838279
  · exact B838283
  · exact B838287
  · exact B838291
  · exact B838295
  · exact B838299
  · exact B838303
  · exact B838307
  · exact B838311
  · exact B838315
  · exact B838319
  · exact B838323
  · exact B838327
  · exact B838331
  · exact B838335
  · exact B838339
  · exact B838343
  · exact B838347
  · exact B838351

theorem solution (m : ℕ) (hlo : 834351 ≤ m) (hhi : m ≤ 838351) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 208587 ≤ j := by omega
    have hj2 : j ≤ 209587 := by omega
    have hb : Blo 834351 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 209287 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
