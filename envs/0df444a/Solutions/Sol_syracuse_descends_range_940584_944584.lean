-- Prove2me | solution 1 for syracuse_descends_range_940584_944584
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:57.692387+00:00
-- url     : https://prove2.me/submissions/2e04f7c3-128c-4939-a264-aa6d028a4906

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


theorem B1146901 : Blo 940584 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B2293805 : Blo 940584 2293805 := bbase (se 3 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 2293805 = 860177) (by norm_num)
theorem B1507493 : Blo 940584 1507493 := bbase (se 4 (by rfl) ⟨141327, by rfl⟩ : syracuseStep 1507493 = 282655) (by norm_num)
theorem B3178709 : Blo 940584 3178709 := bbase (se 7 (by rfl) ⟨37250, by rfl⟩ : syracuseStep 3178709 = 74501) (by norm_num)
theorem B2687413 : Blo 940584 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B2261461 : Blo 940584 2261461 := bbase (se 7 (by rfl) ⟨26501, by rfl⟩ : syracuseStep 2261461 = 53003) (by norm_num)
theorem B1343957 : Blo 940584 1343957 := bbase (se 7 (by rfl) ⟨15749, by rfl⟩ : syracuseStep 1343957 = 31499) (by norm_num)
theorem B2687573 : Blo 940584 2687573 := bbase (se 8 (by rfl) ⟨15747, by rfl⟩ : syracuseStep 2687573 = 31495) (by norm_num)
theorem B6128245 : Blo 940584 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B3179141 : Blo 940584 3179141 := bbase (se 4 (by rfl) ⟨298044, by rfl⟩ : syracuseStep 3179141 = 596089) (by norm_num)
theorem B1508005 : Blo 940584 1508005 := bbase (se 4 (by rfl) ⟨141375, by rfl⟩ : syracuseStep 1508005 = 282751) (by norm_num)
theorem B4522709 : Blo 940584 4522709 := bbase (se 7 (by rfl) ⟨53000, by rfl⟩ : syracuseStep 4522709 = 106001) (by norm_num)
theorem B2687813 : Blo 940584 2687813 := bbase (se 4 (by rfl) ⟨251982, by rfl⟩ : syracuseStep 2687813 = 503965) (by norm_num)
theorem B3015589 : Blo 940584 3015589 := bbase (se 4 (by rfl) ⟨282711, by rfl⟩ : syracuseStep 3015589 = 565423) (by norm_num)
theorem B2294701 : Blo 940584 2294701 := bbase (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) (by norm_num)
theorem B3572693 : Blo 940584 3572693 := bbase (se 7 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 3572693 = 83735) (by norm_num)
theorem B4031461 : Blo 940584 4031461 := bbase (se 4 (by rfl) ⟨377949, by rfl⟩ : syracuseStep 4031461 = 755899) (by norm_num)
theorem B2688005 : Blo 940584 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B3179573 : Blo 940584 3179573 := bbase (se 5 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 3179573 = 298085) (by norm_num)
theorem B2262077 : Blo 940584 2262077 := bbase (se 3 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 2262077 = 848279) (by norm_num)
theorem B4523093 : Blo 940584 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B1344709 : Blo 940584 1344709 := bbase (se 4 (by rfl) ⟨126066, by rfl⟩ : syracuseStep 1344709 = 252133) (by norm_num)
theorem B3572981 : Blo 940584 3572981 := bbase (se 5 (by rfl) ⟨167483, by rfl⟩ : syracuseStep 3572981 = 334967) (by norm_num)
theorem B2262277 : Blo 940584 2262277 := bbase (se 4 (by rfl) ⟨212088, by rfl⟩ : syracuseStep 2262277 = 424177) (by norm_num)
theorem B6784469 : Blo 940584 6784469 := bbase (se 7 (by rfl) ⟨79505, by rfl⟩ : syracuseStep 6784469 = 159011) (by norm_num)
theorem B3180005 : Blo 940584 3180005 := bbase (se 4 (by rfl) ⟨298125, by rfl⟩ : syracuseStep 3180005 = 596251) (by norm_num)
theorem B1509005 : Blo 940584 1509005 := bbase (se 3 (by rfl) ⟨282938, by rfl⟩ : syracuseStep 1509005 = 565877) (by norm_num)
theorem B9176789 : Blo 940584 9176789 := bbase (se 7 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 9176789 = 215081) (by norm_num)
theorem B1509133 : Blo 940584 1509133 := bbase (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) (by norm_num)
theorem B1410893 : Blo 940584 1410893 := bbase (se 3 (by rfl) ⟨264542, by rfl⟩ : syracuseStep 1410893 = 529085) (by norm_num)
theorem B1509197 : Blo 940584 1509197 := bbase (se 3 (by rfl) ⟨282974, by rfl⟩ : syracuseStep 1509197 = 565949) (by norm_num)
theorem B1410917 : Blo 940584 1410917 := bbase (se 4 (by rfl) ⟨132273, by rfl⟩ : syracuseStep 1410917 = 264547) (by norm_num)
theorem B1148773 : Blo 940584 1148773 := bbase (se 4 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 1148773 = 215395) (by norm_num)
theorem B9045877 : Blo 940584 9045877 := bbase (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) (by norm_num)
theorem B1410941 : Blo 940584 1410941 := bbase (se 3 (by rfl) ⟨264551, by rfl⟩ : syracuseStep 1410941 = 529103) (by norm_num)
theorem B1410965 : Blo 940584 1410965 := bbase (se 6 (by rfl) ⟨33069, by rfl⟩ : syracuseStep 1410965 = 66139) (by norm_num)
theorem B3180437 : Blo 940584 3180437 := bbase (se 6 (by rfl) ⟨74541, by rfl⟩ : syracuseStep 3180437 = 149083) (by norm_num)
theorem B1410989 : Blo 940584 1410989 := bbase (se 3 (by rfl) ⟨264560, by rfl⟩ : syracuseStep 1410989 = 529121) (by norm_num)
theorem B1411013 : Blo 940584 1411013 := bbase (se 4 (by rfl) ⟨132282, by rfl⟩ : syracuseStep 1411013 = 264565) (by norm_num)
theorem B1411037 : Blo 940584 1411037 := bbase (se 3 (by rfl) ⟨264569, by rfl⟩ : syracuseStep 1411037 = 529139) (by norm_num)
theorem B2688997 : Blo 940584 2688997 := bbase (se 4 (by rfl) ⟨252093, by rfl⟩ : syracuseStep 2688997 = 504187) (by norm_num)
theorem B1411061 : Blo 940584 1411061 := bbase (se 5 (by rfl) ⟨66143, by rfl⟩ : syracuseStep 1411061 = 132287) (by norm_num)
theorem B1411085 : Blo 940584 1411085 := bbase (se 3 (by rfl) ⟨264578, by rfl⟩ : syracuseStep 1411085 = 529157) (by norm_num)
theorem B6031381 : Blo 940584 6031381 := bbase (se 6 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 6031381 = 282721) (by norm_num)
theorem B1411109 : Blo 940584 1411109 := bbase (se 4 (by rfl) ⟨132291, by rfl⟩ : syracuseStep 1411109 = 264583) (by norm_num)
theorem B2263085 : Blo 940584 2263085 := bbase (se 3 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 2263085 = 848657) (by norm_num)
theorem B1411133 : Blo 940584 1411133 := bbase (se 3 (by rfl) ⟨264587, by rfl⟩ : syracuseStep 1411133 = 529175) (by norm_num)
theorem B1411157 : Blo 940584 1411157 := bbase (se 8 (by rfl) ⟨8268, by rfl⟩ : syracuseStep 1411157 = 16537) (by norm_num)
theorem B1411181 : Blo 940584 1411181 := bbase (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) (by norm_num)
theorem B1411205 : Blo 940584 1411205 := bbase (se 4 (by rfl) ⟨132300, by rfl⟩ : syracuseStep 1411205 = 264601) (by norm_num)
theorem B1411229 : Blo 940584 1411229 := bbase (se 3 (by rfl) ⟨264605, by rfl⟩ : syracuseStep 1411229 = 529211) (by norm_num)
theorem B1149085 : Blo 940584 1149085 := bbase (se 3 (by rfl) ⟨215453, by rfl⟩ : syracuseStep 1149085 = 430907) (by norm_num)
theorem B1411253 : Blo 940584 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1411277 : Blo 940584 1411277 := bbase (se 3 (by rfl) ⟨264614, by rfl⟩ : syracuseStep 1411277 = 529229) (by norm_num)
theorem B1411301 : Blo 940584 1411301 := bbase (se 4 (by rfl) ⟨132309, by rfl⟩ : syracuseStep 1411301 = 264619) (by norm_num)
theorem B1411325 : Blo 940584 1411325 := bbase (se 3 (by rfl) ⟨264623, by rfl⟩ : syracuseStep 1411325 = 529247) (by norm_num)
theorem B1411349 : Blo 940584 1411349 := bbase (se 6 (by rfl) ⟨33078, by rfl⟩ : syracuseStep 1411349 = 66157) (by norm_num)
theorem B1411373 : Blo 940584 1411373 := bbase (se 3 (by rfl) ⟨264632, by rfl⟩ : syracuseStep 1411373 = 529265) (by norm_num)
theorem B1149241 : Blo 940584 1149241 := bbase (se 2 (by rfl) ⟨430965, by rfl⟩ : syracuseStep 1149241 = 861931) (by norm_num)
theorem B1411397 : Blo 940584 1411397 := bbase (se 4 (by rfl) ⟨132318, by rfl⟩ : syracuseStep 1411397 = 264637) (by norm_num)
theorem B3180869 : Blo 940584 3180869 := bbase (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) (by norm_num)
theorem B1411421 : Blo 940584 1411421 := bbase (se 3 (by rfl) ⟨264641, by rfl⟩ : syracuseStep 1411421 = 529283) (by norm_num)
theorem B1411445 : Blo 940584 1411445 := bbase (se 5 (by rfl) ⟨66161, by rfl⟩ : syracuseStep 1411445 = 132323) (by norm_num)
theorem B1411469 : Blo 940584 1411469 := bbase (se 3 (by rfl) ⟨264650, by rfl⟩ : syracuseStep 1411469 = 529301) (by norm_num)
theorem B3574165 : Blo 940584 3574165 := bbase (se 6 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 3574165 = 167539) (by norm_num)
theorem B1411493 : Blo 940584 1411493 := bbase (se 4 (by rfl) ⟨132327, by rfl⟩ : syracuseStep 1411493 = 264655) (by norm_num)
theorem B4032949 : Blo 940584 4032949 := bbase (se 5 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 4032949 = 378089) (by norm_num)
theorem B1411517 : Blo 940584 1411517 := bbase (se 3 (by rfl) ⟨264659, by rfl⟩ : syracuseStep 1411517 = 529319) (by norm_num)
theorem B4032965 : Blo 940584 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B1411541 : Blo 940584 1411541 := bbase (se 7 (by rfl) ⟨16541, by rfl⟩ : syracuseStep 1411541 = 33083) (by norm_num)
theorem B3017189 : Blo 940584 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B1411565 : Blo 940584 1411565 := bbase (se 3 (by rfl) ⟨264668, by rfl⟩ : syracuseStep 1411565 = 529337) (by norm_num)
theorem B1411589 : Blo 940584 1411589 := bbase (se 4 (by rfl) ⟨132336, by rfl⟩ : syracuseStep 1411589 = 264673) (by norm_num)
theorem B1411613 : Blo 940584 1411613 := bbase (se 3 (by rfl) ⟨264677, by rfl⟩ : syracuseStep 1411613 = 529355) (by norm_num)
theorem B1411637 : Blo 940584 1411637 := bbase (se 5 (by rfl) ⟨66170, by rfl⟩ : syracuseStep 1411637 = 132341) (by norm_num)
theorem B1411661 : Blo 940584 1411661 := bbase (se 3 (by rfl) ⟨264686, by rfl⟩ : syracuseStep 1411661 = 529373) (by norm_num)
theorem B1411685 : Blo 940584 1411685 := bbase (se 4 (by rfl) ⟨132345, by rfl⟩ : syracuseStep 1411685 = 264691) (by norm_num)
theorem B1149553 : Blo 940584 1149553 := bbase (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) (by norm_num)
theorem B1411709 : Blo 940584 1411709 := bbase (se 3 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 1411709 = 529391) (by norm_num)
theorem B1411733 : Blo 940584 1411733 := bbase (se 6 (by rfl) ⟨33087, by rfl⟩ : syracuseStep 1411733 = 66175) (by norm_num)
theorem B1411757 : Blo 940584 1411757 := bbase (se 3 (by rfl) ⟨264704, by rfl⟩ : syracuseStep 1411757 = 529409) (by norm_num)
theorem B1411781 : Blo 940584 1411781 := bbase (se 4 (by rfl) ⟨132354, by rfl⟩ : syracuseStep 1411781 = 264709) (by norm_num)
theorem B3574469 : Blo 940584 3574469 := bbase (se 4 (by rfl) ⟨335106, by rfl⟩ : syracuseStep 3574469 = 670213) (by norm_num)
theorem B1411805 : Blo 940584 1411805 := bbase (se 3 (by rfl) ⟨264713, by rfl⟩ : syracuseStep 1411805 = 529427) (by norm_num)
theorem B1411829 : Blo 940584 1411829 := bbase (se 5 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 1411829 = 132359) (by norm_num)
theorem B3181301 : Blo 940584 3181301 := bbase (se 5 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 3181301 = 298247) (by norm_num)
theorem B1018621 : Blo 940584 1018621 := bbase (se 3 (by rfl) ⟨190991, by rfl⟩ : syracuseStep 1018621 = 381983) (by norm_num)
theorem B1411853 : Blo 940584 1411853 := bbase (se 3 (by rfl) ⟨264722, by rfl⟩ : syracuseStep 1411853 = 529445) (by norm_num)
theorem B1411877 : Blo 940584 1411877 := bbase (se 4 (by rfl) ⟨132363, by rfl⟩ : syracuseStep 1411877 = 264727) (by norm_num)
theorem B2263853 : Blo 940584 2263853 := bbase (se 3 (by rfl) ⟨424472, by rfl⟩ : syracuseStep 2263853 = 848945) (by norm_num)
theorem B1411901 : Blo 940584 1411901 := bbase (se 3 (by rfl) ⟨264731, by rfl⟩ : syracuseStep 1411901 = 529463) (by norm_num)
theorem B1411925 : Blo 940584 1411925 := bbase (se 9 (by rfl) ⟨4136, by rfl⟩ : syracuseStep 1411925 = 8273) (by norm_num)
theorem B1411949 : Blo 940584 1411949 := bbase (se 3 (by rfl) ⟨264740, by rfl⟩ : syracuseStep 1411949 = 529481) (by norm_num)
theorem B1411973 : Blo 940584 1411973 := bbase (se 4 (by rfl) ⟨132372, by rfl⟩ : syracuseStep 1411973 = 264745) (by norm_num)
theorem B1411997 : Blo 940584 1411997 := bbase (se 3 (by rfl) ⟨264749, by rfl⟩ : syracuseStep 1411997 = 529499) (by norm_num)
theorem B1412021 : Blo 940584 1412021 := bbase (se 5 (by rfl) ⟨66188, by rfl⟩ : syracuseStep 1412021 = 132377) (by norm_num)
theorem B1412045 : Blo 940584 1412045 := bbase (se 3 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 1412045 = 529517) (by norm_num)
theorem B1412069 : Blo 940584 1412069 := bbase (se 4 (by rfl) ⟨132381, by rfl⟩ : syracuseStep 1412069 = 264763) (by norm_num)
theorem B5377013 : Blo 940584 5377013 := bbase (se 5 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 5377013 = 504095) (by norm_num)
theorem B1412093 : Blo 940584 1412093 := bbase (se 3 (by rfl) ⟨264767, by rfl⟩ : syracuseStep 1412093 = 529535) (by norm_num)
theorem B1412117 : Blo 940584 1412117 := bbase (se 6 (by rfl) ⟨33096, by rfl⟩ : syracuseStep 1412117 = 66193) (by norm_num)
theorem B1412141 : Blo 940584 1412141 := bbase (se 3 (by rfl) ⟨264776, by rfl⟩ : syracuseStep 1412141 = 529553) (by norm_num)
theorem B1412165 : Blo 940584 1412165 := bbase (se 4 (by rfl) ⟨132390, by rfl⟩ : syracuseStep 1412165 = 264781) (by norm_num)
theorem B1412189 : Blo 940584 1412189 := bbase (se 3 (by rfl) ⟨264785, by rfl⟩ : syracuseStep 1412189 = 529571) (by norm_num)
theorem B1412213 : Blo 940584 1412213 := bbase (se 5 (by rfl) ⟨66197, by rfl⟩ : syracuseStep 1412213 = 132395) (by norm_num)
theorem B1510517 : Blo 940584 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B1412237 : Blo 940584 1412237 := bbase (se 3 (by rfl) ⟨264794, by rfl⟩ : syracuseStep 1412237 = 529589) (by norm_num)
theorem B5442709 : Blo 940584 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B1412261 : Blo 940584 1412261 := bbase (se 4 (by rfl) ⟨132399, by rfl⟩ : syracuseStep 1412261 = 264799) (by norm_num)
theorem B3181733 : Blo 940584 3181733 := bbase (se 4 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 3181733 = 596575) (by norm_num)
theorem B1412285 : Blo 940584 1412285 := bbase (se 3 (by rfl) ⟨264803, by rfl⟩ : syracuseStep 1412285 = 529607) (by norm_num)
theorem B1412309 : Blo 940584 1412309 := bbase (se 7 (by rfl) ⟨16550, by rfl⟩ : syracuseStep 1412309 = 33101) (by norm_num)
theorem B1412333 : Blo 940584 1412333 := bbase (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) (by norm_num)
theorem B1510645 : Blo 940584 1510645 := bbase (se 5 (by rfl) ⟨70811, by rfl⟩ : syracuseStep 1510645 = 141623) (by norm_num)
theorem B1412357 : Blo 940584 1412357 := bbase (se 4 (by rfl) ⟨132408, by rfl⟩ : syracuseStep 1412357 = 264817) (by norm_num)
theorem B3673349 : Blo 940584 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B1412381 : Blo 940584 1412381 := bbase (se 3 (by rfl) ⟨264821, by rfl⟩ : syracuseStep 1412381 = 529643) (by norm_num)
theorem B953633 : Blo 940584 953633 := bbase (se 2 (by rfl) ⟨357612, by rfl⟩ : syracuseStep 953633 = 715225) (by norm_num)
theorem B1412405 : Blo 940584 1412405 := bbase (se 5 (by rfl) ⟨66206, by rfl⟩ : syracuseStep 1412405 = 132413) (by norm_num)
theorem B1412429 : Blo 940584 1412429 := bbase (se 3 (by rfl) ⟨264830, by rfl⟩ : syracuseStep 1412429 = 529661) (by norm_num)
theorem B1412453 : Blo 940584 1412453 := bbase (se 4 (by rfl) ⟨132417, by rfl⟩ : syracuseStep 1412453 = 264835) (by norm_num)
theorem B1412477 : Blo 940584 1412477 := bbase (se 3 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 1412477 = 529679) (by norm_num)
theorem B1412501 : Blo 940584 1412501 := bbase (se 6 (by rfl) ⟨33105, by rfl⟩ : syracuseStep 1412501 = 66211) (by norm_num)
theorem B1412525 : Blo 940584 1412525 := bbase (se 3 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 1412525 = 529697) (by norm_num)
theorem B1412549 : Blo 940584 1412549 := bbase (se 4 (by rfl) ⟨132426, by rfl⟩ : syracuseStep 1412549 = 264853) (by norm_num)
theorem B1412573 : Blo 940584 1412573 := bbase (se 3 (by rfl) ⟨264857, by rfl⟩ : syracuseStep 1412573 = 529715) (by norm_num)
theorem B1412597 : Blo 940584 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B1412621 : Blo 940584 1412621 := bbase (se 3 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 1412621 = 529733) (by norm_num)
theorem B953893 : Blo 940584 953893 := bbase (se 4 (by rfl) ⟨89427, by rfl⟩ : syracuseStep 953893 = 178855) (by norm_num)
theorem B1412645 : Blo 940584 1412645 := bbase (se 4 (by rfl) ⟨132435, by rfl⟩ : syracuseStep 1412645 = 264871) (by norm_num)
theorem B3018293 : Blo 940584 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B2068021 : Blo 940584 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B1412669 : Blo 940584 1412669 := bbase (se 3 (by rfl) ⟨264875, by rfl⟩ : syracuseStep 1412669 = 529751) (by norm_num)
theorem B1412693 : Blo 940584 1412693 := bbase (se 8 (by rfl) ⟨8277, by rfl⟩ : syracuseStep 1412693 = 16555) (by norm_num)
theorem B3182165 : Blo 940584 3182165 := bbase (se 8 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 3182165 = 37291) (by norm_num)
theorem B1412717 : Blo 940584 1412717 := bbase (se 3 (by rfl) ⟨264884, by rfl⟩ : syracuseStep 1412717 = 529769) (by norm_num)
theorem B1412741 : Blo 940584 1412741 := bbase (se 4 (by rfl) ⟨132444, by rfl⟩ : syracuseStep 1412741 = 264889) (by norm_num)
theorem B954001 : Blo 940584 954001 := bbase (se 2 (by rfl) ⟨357750, by rfl⟩ : syracuseStep 954001 = 715501) (by norm_num)
theorem B1412765 : Blo 940584 1412765 := bbase (se 3 (by rfl) ⟨264893, by rfl⟩ : syracuseStep 1412765 = 529787) (by norm_num)
theorem B954025 : Blo 940584 954025 := bbase (se 2 (by rfl) ⟨357759, by rfl⟩ : syracuseStep 954025 = 715519) (by norm_num)
theorem B1412789 : Blo 940584 1412789 := bbase (se 5 (by rfl) ⟨66224, by rfl⟩ : syracuseStep 1412789 = 132449) (by norm_num)
theorem B5738165 : Blo 940584 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B1412813 : Blo 940584 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B1412837 : Blo 940584 1412837 := bbase (se 4 (by rfl) ⟨132453, by rfl⟩ : syracuseStep 1412837 = 264907) (by norm_num)
theorem B1412861 : Blo 940584 1412861 := bbase (se 3 (by rfl) ⟨264911, by rfl⟩ : syracuseStep 1412861 = 529823) (by norm_num)
theorem B1412885 : Blo 940584 1412885 := bbase (se 6 (by rfl) ⟨33114, by rfl⟩ : syracuseStep 1412885 = 66229) (by norm_num)
theorem B1412909 : Blo 940584 1412909 := bbase (se 3 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 1412909 = 529841) (by norm_num)
theorem B1412933 : Blo 940584 1412933 := bbase (se 4 (by rfl) ⟨132462, by rfl⟩ : syracuseStep 1412933 = 264925) (by norm_num)
theorem B1412957 : Blo 940584 1412957 := bbase (se 3 (by rfl) ⟨264929, by rfl⟩ : syracuseStep 1412957 = 529859) (by norm_num)
theorem B1412981 : Blo 940584 1412981 := bbase (se 5 (by rfl) ⟨66233, by rfl⟩ : syracuseStep 1412981 = 132467) (by norm_num)
theorem B1413005 : Blo 940584 1413005 := bbase (se 3 (by rfl) ⟨264938, by rfl⟩ : syracuseStep 1413005 = 529877) (by norm_num)
theorem B1413029 : Blo 940584 1413029 := bbase (se 4 (by rfl) ⟨132471, by rfl⟩ : syracuseStep 1413029 = 264943) (by norm_num)
theorem B1413053 : Blo 940584 1413053 := bbase (se 3 (by rfl) ⟨264947, by rfl⟩ : syracuseStep 1413053 = 529895) (by norm_num)
theorem B1413077 : Blo 940584 1413077 := bbase (se 7 (by rfl) ⟨16559, by rfl⟩ : syracuseStep 1413077 = 33119) (by norm_num)
theorem B1413101 : Blo 940584 1413101 := bbase (se 3 (by rfl) ⟨264956, by rfl⟩ : syracuseStep 1413101 = 529913) (by norm_num)
theorem B1413125 : Blo 940584 1413125 := bbase (se 4 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 1413125 = 264961) (by norm_num)
theorem B3182597 : Blo 940584 3182597 := bbase (se 4 (by rfl) ⟨298368, by rfl⟩ : syracuseStep 3182597 = 596737) (by norm_num)
theorem B1413149 : Blo 940584 1413149 := bbase (se 3 (by rfl) ⟨264965, by rfl⟩ : syracuseStep 1413149 = 529931) (by norm_num)
theorem B1511453 : Blo 940584 1511453 := bbase (se 3 (by rfl) ⟨283397, by rfl⟩ : syracuseStep 1511453 = 566795) (by norm_num)
theorem B1413173 : Blo 940584 1413173 := bbase (se 5 (by rfl) ⟨66242, by rfl⟩ : syracuseStep 1413173 = 132485) (by norm_num)
theorem B1413197 : Blo 940584 1413197 := bbase (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) (by norm_num)
theorem B1019989 : Blo 940584 1019989 := bbase (se 8 (by rfl) ⟨5976, by rfl⟩ : syracuseStep 1019989 = 11953) (by norm_num)
theorem B8065109 : Blo 940584 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B1413221 : Blo 940584 1413221 := bbase (se 4 (by rfl) ⟨132489, by rfl⟩ : syracuseStep 1413221 = 264979) (by norm_num)
theorem B1413245 : Blo 940584 1413245 := bbase (se 3 (by rfl) ⟨264983, by rfl⟩ : syracuseStep 1413245 = 529967) (by norm_num)
theorem B1413269 : Blo 940584 1413269 := bbase (se 6 (by rfl) ⟨33123, by rfl⟩ : syracuseStep 1413269 = 66247) (by norm_num)
theorem B5378197 : Blo 940584 5378197 := bbase (se 6 (by rfl) ⟨126051, by rfl⟩ : syracuseStep 5378197 = 252103) (by norm_num)
theorem B2298013 : Blo 940584 2298013 := bbase (se 3 (by rfl) ⟨430877, by rfl⟩ : syracuseStep 2298013 = 861755) (by norm_num)
theorem B1413293 : Blo 940584 1413293 := bbase (se 3 (by rfl) ⟨264992, by rfl⟩ : syracuseStep 1413293 = 529985) (by norm_num)
theorem B1413317 : Blo 940584 1413317 := bbase (se 4 (by rfl) ⟨132498, by rfl⟩ : syracuseStep 1413317 = 264997) (by norm_num)
theorem B1413341 : Blo 940584 1413341 := bbase (se 3 (by rfl) ⟨265001, by rfl⟩ : syracuseStep 1413341 = 530003) (by norm_num)
theorem B1413365 : Blo 940584 1413365 := bbase (se 5 (by rfl) ⟨66251, by rfl⟩ : syracuseStep 1413365 = 132503) (by norm_num)
theorem B1413389 : Blo 940584 1413389 := bbase (se 3 (by rfl) ⟨265010, by rfl⟩ : syracuseStep 1413389 = 530021) (by norm_num)
theorem B2298133 : Blo 940584 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B3543317 : Blo 940584 3543317 := bbase (se 6 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 3543317 = 166093) (by norm_num)
theorem B1413413 : Blo 940584 1413413 := bbase (se 4 (by rfl) ⟨132507, by rfl⟩ : syracuseStep 1413413 = 265015) (by norm_num)
theorem B1413437 : Blo 940584 1413437 := bbase (se 3 (by rfl) ⟨265019, by rfl⟩ : syracuseStep 1413437 = 530039) (by norm_num)
theorem B1511741 : Blo 940584 1511741 := bbase (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) (by norm_num)
theorem B1413461 : Blo 940584 1413461 := bbase (se 10 (by rfl) ⟨2070, by rfl⟩ : syracuseStep 1413461 = 4141) (by norm_num)
theorem B4591973 : Blo 940584 4591973 := bbase (se 4 (by rfl) ⟨430497, by rfl⟩ : syracuseStep 4591973 = 860995) (by norm_num)
theorem B1413485 : Blo 940584 1413485 := bbase (se 3 (by rfl) ⟨265028, by rfl⟩ : syracuseStep 1413485 = 530057) (by norm_num)
theorem B1413509 : Blo 940584 1413509 := bbase (se 4 (by rfl) ⟨132516, by rfl⟩ : syracuseStep 1413509 = 265033) (by norm_num)
theorem B1413533 : Blo 940584 1413533 := bbase (se 3 (by rfl) ⟨265037, by rfl⟩ : syracuseStep 1413533 = 530075) (by norm_num)
theorem B1413557 : Blo 940584 1413557 := bbase (se 5 (by rfl) ⟨66260, by rfl⟩ : syracuseStep 1413557 = 132521) (by norm_num)
theorem B3183029 : Blo 940584 3183029 := bbase (se 5 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 3183029 = 298409) (by norm_num)
theorem B1413581 : Blo 940584 1413581 := bbase (se 3 (by rfl) ⟨265046, by rfl⟩ : syracuseStep 1413581 = 530093) (by norm_num)
theorem B2265565 : Blo 940584 2265565 := bbase (se 3 (by rfl) ⟨424793, by rfl⟩ : syracuseStep 2265565 = 849587) (by norm_num)
theorem B1413605 : Blo 940584 1413605 := bbase (se 4 (by rfl) ⟨132525, by rfl⟩ : syracuseStep 1413605 = 265051) (by norm_num)
theorem B1413629 : Blo 940584 1413629 := bbase (se 3 (by rfl) ⟨265055, by rfl⟩ : syracuseStep 1413629 = 530111) (by norm_num)
theorem B1413653 : Blo 940584 1413653 := bbase (se 6 (by rfl) ⟨33132, by rfl⟩ : syracuseStep 1413653 = 66265) (by norm_num)
theorem B1413677 : Blo 940584 1413677 := bbase (se 3 (by rfl) ⟨265064, by rfl⟩ : syracuseStep 1413677 = 530129) (by norm_num)
theorem B1413701 : Blo 940584 1413701 := bbase (se 4 (by rfl) ⟨132534, by rfl⟩ : syracuseStep 1413701 = 265069) (by norm_num)
theorem B1413725 : Blo 940584 1413725 := bbase (se 3 (by rfl) ⟨265073, by rfl⟩ : syracuseStep 1413725 = 530147) (by norm_num)
theorem B1413749 : Blo 940584 1413749 := bbase (se 5 (by rfl) ⟨66269, by rfl⟩ : syracuseStep 1413749 = 132539) (by norm_num)
theorem B1413773 : Blo 940584 1413773 := bbase (se 3 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 1413773 = 530165) (by norm_num)
theorem B1413797 : Blo 940584 1413797 := bbase (se 4 (by rfl) ⟨132543, by rfl⟩ : syracuseStep 1413797 = 265087) (by norm_num)
theorem B1413821 : Blo 940584 1413821 := bbase (se 3 (by rfl) ⟨265091, by rfl⟩ : syracuseStep 1413821 = 530183) (by norm_num)
theorem B1413845 : Blo 940584 1413845 := bbase (se 7 (by rfl) ⟨16568, by rfl⟩ : syracuseStep 1413845 = 33137) (by norm_num)
theorem B1512157 : Blo 940584 1512157 := bbase (se 3 (by rfl) ⟨283529, by rfl⟩ : syracuseStep 1512157 = 567059) (by norm_num)
theorem B1413869 : Blo 940584 1413869 := bbase (se 3 (by rfl) ⟨265100, by rfl⟩ : syracuseStep 1413869 = 530201) (by norm_num)
theorem B3576581 : Blo 940584 3576581 := bbase (se 4 (by rfl) ⟨335304, by rfl⟩ : syracuseStep 3576581 = 670609) (by norm_num)
theorem B1413893 : Blo 940584 1413893 := bbase (se 4 (by rfl) ⟨132552, by rfl⟩ : syracuseStep 1413893 = 265105) (by norm_num)
theorem B1413917 : Blo 940584 1413917 := bbase (se 3 (by rfl) ⟨265109, by rfl⟩ : syracuseStep 1413917 = 530219) (by norm_num)
theorem B1413941 : Blo 940584 1413941 := bbase (se 5 (by rfl) ⟨66278, by rfl⟩ : syracuseStep 1413941 = 132557) (by norm_num)
theorem B1413965 : Blo 940584 1413965 := bbase (se 3 (by rfl) ⟨265118, by rfl⟩ : syracuseStep 1413965 = 530237) (by norm_num)
theorem B1413989 : Blo 940584 1413989 := bbase (se 4 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 1413989 = 265123) (by norm_num)
theorem B3183461 : Blo 940584 3183461 := bbase (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) (by norm_num)
theorem B1414013 : Blo 940584 1414013 := bbase (se 3 (by rfl) ⟨265127, by rfl⟩ : syracuseStep 1414013 = 530255) (by norm_num)
theorem B1414037 : Blo 940584 1414037 := bbase (se 6 (by rfl) ⟨33141, by rfl⟩ : syracuseStep 1414037 = 66283) (by norm_num)
theorem B1414061 : Blo 940584 1414061 := bbase (se 3 (by rfl) ⟨265136, by rfl⟩ : syracuseStep 1414061 = 530273) (by norm_num)
theorem B1414085 : Blo 940584 1414085 := bbase (se 4 (by rfl) ⟨132570, by rfl⟩ : syracuseStep 1414085 = 265141) (by norm_num)
theorem B1414109 : Blo 940584 1414109 := bbase (se 3 (by rfl) ⟨265145, by rfl⟩ : syracuseStep 1414109 = 530291) (by norm_num)
theorem B1414133 : Blo 940584 1414133 := bbase (se 5 (by rfl) ⟨66287, by rfl⟩ : syracuseStep 1414133 = 132575) (by norm_num)
theorem B1414157 : Blo 940584 1414157 := bbase (se 3 (by rfl) ⟨265154, by rfl⟩ : syracuseStep 1414157 = 530309) (by norm_num)
theorem B3576869 : Blo 940584 3576869 := bbase (se 4 (by rfl) ⟨335331, by rfl⟩ : syracuseStep 3576869 = 670663) (by norm_num)
theorem B1414181 : Blo 940584 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B1414205 : Blo 940584 1414205 := bbase (se 3 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 1414205 = 530327) (by norm_num)
theorem B2266181 : Blo 940584 2266181 := bbase (se 4 (by rfl) ⟨212454, by rfl⟩ : syracuseStep 2266181 = 424909) (by norm_num)
theorem B1414229 : Blo 940584 1414229 := bbase (se 8 (by rfl) ⟨8286, by rfl⟩ : syracuseStep 1414229 = 16573) (by norm_num)
theorem B1414253 : Blo 940584 1414253 := bbase (se 3 (by rfl) ⟨265172, by rfl⟩ : syracuseStep 1414253 = 530345) (by norm_num)
theorem B1414277 : Blo 940584 1414277 := bbase (se 4 (by rfl) ⟨132588, by rfl⟩ : syracuseStep 1414277 = 265177) (by norm_num)
theorem B1414301 : Blo 940584 1414301 := bbase (se 3 (by rfl) ⟨265181, by rfl⟩ : syracuseStep 1414301 = 530363) (by norm_num)
theorem B1414325 : Blo 940584 1414325 := bbase (se 5 (by rfl) ⟨66296, by rfl⟩ : syracuseStep 1414325 = 132593) (by norm_num)
theorem B1414349 : Blo 940584 1414349 := bbase (se 3 (by rfl) ⟨265190, by rfl⟩ : syracuseStep 1414349 = 530381) (by norm_num)
theorem B1414373 : Blo 940584 1414373 := bbase (se 4 (by rfl) ⟨132597, by rfl⟩ : syracuseStep 1414373 = 265195) (by norm_num)
theorem B1414397 : Blo 940584 1414397 := bbase (se 3 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 1414397 = 530399) (by norm_num)
theorem B1414421 : Blo 940584 1414421 := bbase (se 6 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 1414421 = 66301) (by norm_num)
theorem B3183893 : Blo 940584 3183893 := bbase (se 6 (by rfl) ⟨74622, by rfl⟩ : syracuseStep 3183893 = 149245) (by norm_num)
theorem B1414445 : Blo 940584 1414445 := bbase (se 3 (by rfl) ⟨265208, by rfl⟩ : syracuseStep 1414445 = 530417) (by norm_num)
theorem B1414469 : Blo 940584 1414469 := bbase (se 4 (by rfl) ⟨132606, by rfl⟩ : syracuseStep 1414469 = 265213) (by norm_num)
theorem B1414493 : Blo 940584 1414493 := bbase (se 3 (by rfl) ⟨265217, by rfl⟩ : syracuseStep 1414493 = 530435) (by norm_num)
theorem B1414517 : Blo 940584 1414517 := bbase (se 5 (by rfl) ⟨66305, by rfl⟩ : syracuseStep 1414517 = 132611) (by norm_num)
theorem B1414541 : Blo 940584 1414541 := bbase (se 3 (by rfl) ⟨265226, by rfl⟩ : syracuseStep 1414541 = 530453) (by norm_num)
theorem B1414565 : Blo 940584 1414565 := bbase (se 4 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 1414565 = 265231) (by norm_num)
theorem B3020213 : Blo 940584 3020213 := bbase (se 5 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 3020213 = 283145) (by norm_num)
theorem B1414589 : Blo 940584 1414589 := bbase (se 3 (by rfl) ⟨265235, by rfl⟩ : syracuseStep 1414589 = 530471) (by norm_num)
theorem B1414613 : Blo 940584 1414613 := bbase (se 7 (by rfl) ⟨16577, by rfl⟩ : syracuseStep 1414613 = 33155) (by norm_num)
theorem B1414637 : Blo 940584 1414637 := bbase (se 3 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 1414637 = 530489) (by norm_num)
theorem B2266613 : Blo 940584 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B1414661 : Blo 940584 1414661 := bbase (se 4 (by rfl) ⟨132624, by rfl⟩ : syracuseStep 1414661 = 265249) (by norm_num)
theorem B1414685 : Blo 940584 1414685 := bbase (se 3 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 1414685 = 530507) (by norm_num)
theorem B1414709 : Blo 940584 1414709 := bbase (se 5 (by rfl) ⟨66314, by rfl⟩ : syracuseStep 1414709 = 132629) (by norm_num)
theorem B1414733 : Blo 940584 1414733 := bbase (se 3 (by rfl) ⟨265262, by rfl⟩ : syracuseStep 1414733 = 530525) (by norm_num)
theorem B1414757 : Blo 940584 1414757 := bbase (se 4 (by rfl) ⟨132633, by rfl⟩ : syracuseStep 1414757 = 265267) (by norm_num)
theorem B1414781 : Blo 940584 1414781 := bbase (se 3 (by rfl) ⟨265271, by rfl⟩ : syracuseStep 1414781 = 530543) (by norm_num)
theorem B1414805 : Blo 940584 1414805 := bbase (se 6 (by rfl) ⟨33159, by rfl⟩ : syracuseStep 1414805 = 66319) (by norm_num)
theorem B1414829 : Blo 940584 1414829 := bbase (se 3 (by rfl) ⟨265280, by rfl⟩ : syracuseStep 1414829 = 530561) (by norm_num)
theorem B1414853 : Blo 940584 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B3184325 : Blo 940584 3184325 := bbase (se 4 (by rfl) ⟨298530, by rfl⟩ : syracuseStep 3184325 = 597061) (by norm_num)
theorem B1414877 : Blo 940584 1414877 := bbase (se 3 (by rfl) ⟨265289, by rfl⟩ : syracuseStep 1414877 = 530579) (by norm_num)
theorem B1414901 : Blo 940584 1414901 := bbase (se 5 (by rfl) ⟨66323, by rfl⟩ : syracuseStep 1414901 = 132647) (by norm_num)
theorem B1611533 : Blo 940584 1611533 := bbase (se 3 (by rfl) ⟨302162, by rfl⟩ : syracuseStep 1611533 = 604325) (by norm_num)
theorem B1414925 : Blo 940584 1414925 := bbase (se 3 (by rfl) ⟨265298, by rfl⟩ : syracuseStep 1414925 = 530597) (by norm_num)
theorem B1414949 : Blo 940584 1414949 := bbase (se 4 (by rfl) ⟨132651, by rfl⟩ : syracuseStep 1414949 = 265303) (by norm_num)
theorem B1414973 : Blo 940584 1414973 := bbase (se 3 (by rfl) ⟨265307, by rfl⟩ : syracuseStep 1414973 = 530615) (by norm_num)
theorem B1414997 : Blo 940584 1414997 := bbase (se 9 (by rfl) ⟨4145, by rfl⟩ : syracuseStep 1414997 = 8291) (by norm_num)
theorem B1415021 : Blo 940584 1415021 := bbase (se 3 (by rfl) ⟨265316, by rfl⟩ : syracuseStep 1415021 = 530633) (by norm_num)
theorem B1415045 : Blo 940584 1415045 := bbase (se 4 (by rfl) ⟨132660, by rfl⟩ : syracuseStep 1415045 = 265321) (by norm_num)
theorem B1415069 : Blo 940584 1415069 := bbase (se 3 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 1415069 = 530651) (by norm_num)
theorem B1415093 : Blo 940584 1415093 := bbase (se 5 (by rfl) ⟨66332, by rfl⟩ : syracuseStep 1415093 = 132665) (by norm_num)
theorem B1415117 : Blo 940584 1415117 := bbase (se 3 (by rfl) ⟨265334, by rfl⟩ : syracuseStep 1415117 = 530669) (by norm_num)
theorem B1415141 : Blo 940584 1415141 := bbase (se 4 (by rfl) ⟨132669, by rfl⟩ : syracuseStep 1415141 = 265339) (by norm_num)
theorem B1415165 : Blo 940584 1415165 := bbase (se 3 (by rfl) ⟨265343, by rfl⟩ : syracuseStep 1415165 = 530687) (by norm_num)
theorem B1415189 : Blo 940584 1415189 := bbase (se 6 (by rfl) ⟨33168, by rfl⟩ : syracuseStep 1415189 = 66337) (by norm_num)
theorem B1415213 : Blo 940584 1415213 := bbase (se 3 (by rfl) ⟨265352, by rfl⟩ : syracuseStep 1415213 = 530705) (by norm_num)
theorem B1415237 : Blo 940584 1415237 := bbase (se 4 (by rfl) ⟨132678, by rfl⟩ : syracuseStep 1415237 = 265357) (by norm_num)
theorem B1415261 : Blo 940584 1415261 := bbase (se 3 (by rfl) ⟨265361, by rfl⟩ : syracuseStep 1415261 = 530723) (by norm_num)
theorem B1415285 : Blo 940584 1415285 := bbase (se 5 (by rfl) ⟨66341, by rfl⟩ : syracuseStep 1415285 = 132683) (by norm_num)
theorem B3184757 : Blo 940584 3184757 := bbase (se 5 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 3184757 = 298571) (by norm_num)
theorem B1415309 : Blo 940584 1415309 := bbase (se 3 (by rfl) ⟨265370, by rfl⟩ : syracuseStep 1415309 = 530741) (by norm_num)
theorem B1415333 : Blo 940584 1415333 := bbase (se 4 (by rfl) ⟨132687, by rfl⟩ : syracuseStep 1415333 = 265375) (by norm_num)
theorem B1415357 : Blo 940584 1415357 := bbase (se 3 (by rfl) ⟨265379, by rfl⟩ : syracuseStep 1415357 = 530759) (by norm_num)
theorem B3578053 : Blo 940584 3578053 := bbase (se 4 (by rfl) ⟨335442, by rfl⟩ : syracuseStep 3578053 = 670885) (by norm_num)
theorem B1415381 : Blo 940584 1415381 := bbase (se 7 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 1415381 = 33173) (by norm_num)
theorem B1415405 : Blo 940584 1415405 := bbase (se 3 (by rfl) ⟨265388, by rfl⟩ : syracuseStep 1415405 = 530777) (by norm_num)
theorem B1415429 : Blo 940584 1415429 := bbase (se 4 (by rfl) ⟨132696, by rfl⟩ : syracuseStep 1415429 = 265393) (by norm_num)
theorem B1415453 : Blo 940584 1415453 := bbase (se 3 (by rfl) ⟨265397, by rfl⟩ : syracuseStep 1415453 = 530795) (by norm_num)
theorem B1415477 : Blo 940584 1415477 := bbase (se 5 (by rfl) ⟨66350, by rfl⟩ : syracuseStep 1415477 = 132701) (by norm_num)
theorem B1415501 : Blo 940584 1415501 := bbase (se 3 (by rfl) ⟨265406, by rfl⟩ : syracuseStep 1415501 = 530813) (by norm_num)
theorem B1415525 : Blo 940584 1415525 := bbase (se 4 (by rfl) ⟨132705, by rfl⟩ : syracuseStep 1415525 = 265411) (by norm_num)
theorem B1415549 : Blo 940584 1415549 := bbase (se 3 (by rfl) ⟨265415, by rfl⟩ : syracuseStep 1415549 = 530831) (by norm_num)
theorem B1415573 : Blo 940584 1415573 := bbase (se 6 (by rfl) ⟨33177, by rfl⟩ : syracuseStep 1415573 = 66355) (by norm_num)
theorem B1415597 : Blo 940584 1415597 := bbase (se 3 (by rfl) ⟨265424, by rfl⟩ : syracuseStep 1415597 = 530849) (by norm_num)
theorem B1415621 : Blo 940584 1415621 := bbase (se 4 (by rfl) ⟨132714, by rfl⟩ : syracuseStep 1415621 = 265429) (by norm_num)
theorem B1415645 : Blo 940584 1415645 := bbase (se 3 (by rfl) ⟨265433, by rfl⟩ : syracuseStep 1415645 = 530867) (by norm_num)
theorem B3578357 : Blo 940584 3578357 := bbase (se 5 (by rfl) ⟨167735, by rfl⟩ : syracuseStep 3578357 = 335471) (by norm_num)
theorem B1415669 : Blo 940584 1415669 := bbase (se 5 (by rfl) ⟨66359, by rfl⟩ : syracuseStep 1415669 = 132719) (by norm_num)
theorem B1415693 : Blo 940584 1415693 := bbase (se 3 (by rfl) ⟨265442, by rfl⟩ : syracuseStep 1415693 = 530885) (by norm_num)
theorem B3185189 : Blo 940584 3185189 := bbase (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) (by norm_num)
theorem B1415717 : Blo 940584 1415717 := bbase (se 4 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 1415717 = 265447) (by norm_num)
theorem B1415741 : Blo 940584 1415741 := bbase (se 3 (by rfl) ⟨265451, by rfl⟩ : syracuseStep 1415741 = 530903) (by norm_num)
theorem B1415765 : Blo 940584 1415765 := bbase (se 8 (by rfl) ⟨8295, by rfl⟩ : syracuseStep 1415765 = 16591) (by norm_num)
theorem B1415789 : Blo 940584 1415789 := bbase (se 3 (by rfl) ⟨265460, by rfl⟩ : syracuseStep 1415789 = 530921) (by norm_num)
theorem B1415813 : Blo 940584 1415813 := bbase (se 4 (by rfl) ⟨132732, by rfl⟩ : syracuseStep 1415813 = 265465) (by norm_num)
theorem B1415837 : Blo 940584 1415837 := bbase (se 3 (by rfl) ⟨265469, by rfl⟩ : syracuseStep 1415837 = 530939) (by norm_num)
theorem B2267813 : Blo 940584 2267813 := bbase (se 4 (by rfl) ⟨212607, by rfl⟩ : syracuseStep 2267813 = 425215) (by norm_num)
theorem B1415861 : Blo 940584 1415861 := bbase (se 5 (by rfl) ⟨66368, by rfl⟩ : syracuseStep 1415861 = 132737) (by norm_num)
theorem B1415885 : Blo 940584 1415885 := bbase (se 3 (by rfl) ⟨265478, by rfl⟩ : syracuseStep 1415885 = 530957) (by norm_num)
theorem B1415909 : Blo 940584 1415909 := bbase (se 4 (by rfl) ⟨132741, by rfl⟩ : syracuseStep 1415909 = 265483) (by norm_num)
theorem B1415933 : Blo 940584 1415933 := bbase (se 3 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 1415933 = 530975) (by norm_num)
theorem B1415957 : Blo 940584 1415957 := bbase (se 6 (by rfl) ⟨33186, by rfl⟩ : syracuseStep 1415957 = 66373) (by norm_num)
theorem B1415981 : Blo 940584 1415981 := bbase (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) (by norm_num)
theorem B1940285 : Blo 940584 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B3021637 : Blo 940584 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B1416005 : Blo 940584 1416005 := bbase (se 4 (by rfl) ⟨132750, by rfl⟩ : syracuseStep 1416005 = 265501) (by norm_num)
theorem B957269 : Blo 940584 957269 := bbase (se 9 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 957269 = 5609) (by norm_num)
theorem B1416029 : Blo 940584 1416029 := bbase (se 3 (by rfl) ⟨265505, by rfl⟩ : syracuseStep 1416029 = 531011) (by norm_num)
theorem B1416053 : Blo 940584 1416053 := bbase (se 5 (by rfl) ⟨66377, by rfl⟩ : syracuseStep 1416053 = 132755) (by norm_num)
theorem B1416077 : Blo 940584 1416077 := bbase (se 3 (by rfl) ⟨265514, by rfl⟩ : syracuseStep 1416077 = 531029) (by norm_num)
theorem B1416101 : Blo 940584 1416101 := bbase (se 4 (by rfl) ⟨132759, by rfl⟩ : syracuseStep 1416101 = 265519) (by norm_num)
theorem B7150517 : Blo 940584 7150517 := bbase (se 5 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 7150517 = 670361) (by norm_num)
theorem B1416125 : Blo 940584 1416125 := bbase (se 3 (by rfl) ⟨265523, by rfl⟩ : syracuseStep 1416125 = 531047) (by norm_num)
theorem B3185621 : Blo 940584 3185621 := bbase (se 7 (by rfl) ⟨37331, by rfl⟩ : syracuseStep 3185621 = 74663) (by norm_num)
theorem B1416149 : Blo 940584 1416149 := bbase (se 7 (by rfl) ⟨16595, by rfl⟩ : syracuseStep 1416149 = 33191) (by norm_num)
theorem B1416173 : Blo 940584 1416173 := bbase (se 3 (by rfl) ⟨265532, by rfl⟩ : syracuseStep 1416173 = 531065) (by norm_num)
theorem B8068085 : Blo 940584 8068085 := bbase (se 5 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 8068085 = 756383) (by norm_num)
theorem B1416197 : Blo 940584 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B1416221 : Blo 940584 1416221 := bbase (se 3 (by rfl) ⟨265541, by rfl⟩ : syracuseStep 1416221 = 531083) (by norm_num)
theorem B1416245 : Blo 940584 1416245 := bbase (se 5 (by rfl) ⟨66386, by rfl⟩ : syracuseStep 1416245 = 132773) (by norm_num)
theorem B1416269 : Blo 940584 1416269 := bbase (se 3 (by rfl) ⟨265550, by rfl⟩ : syracuseStep 1416269 = 531101) (by norm_num)
theorem B1416293 : Blo 940584 1416293 := bbase (se 4 (by rfl) ⟨132777, by rfl⟩ : syracuseStep 1416293 = 265555) (by norm_num)
theorem B1416317 : Blo 940584 1416317 := bbase (se 3 (by rfl) ⟨265559, by rfl⟩ : syracuseStep 1416317 = 531119) (by norm_num)
theorem B1416341 : Blo 940584 1416341 := bbase (se 6 (by rfl) ⟨33195, by rfl⟩ : syracuseStep 1416341 = 66391) (by norm_num)
theorem B1416365 : Blo 940584 1416365 := bbase (se 3 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 1416365 = 531137) (by norm_num)
theorem B1416389 : Blo 940584 1416389 := bbase (se 4 (by rfl) ⟨132786, by rfl⟩ : syracuseStep 1416389 = 265573) (by norm_num)
theorem B1416413 : Blo 940584 1416413 := bbase (se 3 (by rfl) ⟨265577, by rfl⟩ : syracuseStep 1416413 = 531155) (by norm_num)
theorem B1416437 : Blo 940584 1416437 := bbase (se 5 (by rfl) ⟨66395, by rfl⟩ : syracuseStep 1416437 = 132791) (by norm_num)
theorem B3022085 : Blo 940584 3022085 := bbase (se 4 (by rfl) ⟨283320, by rfl⟩ : syracuseStep 3022085 = 566641) (by norm_num)
theorem B1416461 : Blo 940584 1416461 := bbase (se 3 (by rfl) ⟨265586, by rfl⟩ : syracuseStep 1416461 = 531173) (by norm_num)
theorem B1416485 : Blo 940584 1416485 := bbase (se 4 (by rfl) ⟨132795, by rfl⟩ : syracuseStep 1416485 = 265591) (by norm_num)
theorem B1416509 : Blo 940584 1416509 := bbase (se 3 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 1416509 = 531191) (by norm_num)
theorem B1416533 : Blo 940584 1416533 := bbase (se 11 (by rfl) ⟨1037, by rfl⟩ : syracuseStep 1416533 = 2075) (by norm_num)
theorem B1416557 : Blo 940584 1416557 := bbase (se 3 (by rfl) ⟨265604, by rfl⟩ : syracuseStep 1416557 = 531209) (by norm_num)
theorem B2039165 : Blo 940584 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B3186053 : Blo 940584 3186053 := bbase (se 4 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 3186053 = 597385) (by norm_num)
theorem B1416581 : Blo 940584 1416581 := bbase (se 4 (by rfl) ⟨132804, by rfl⟩ : syracuseStep 1416581 = 265609) (by norm_num)
theorem B1416605 : Blo 940584 1416605 := bbase (se 3 (by rfl) ⟨265613, by rfl⟩ : syracuseStep 1416605 = 531227) (by norm_num)
theorem B1416629 : Blo 940584 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B1416653 : Blo 940584 1416653 := bbase (se 3 (by rfl) ⟨265622, by rfl⟩ : syracuseStep 1416653 = 531245) (by norm_num)
theorem B1416677 : Blo 940584 1416677 := bbase (se 4 (by rfl) ⟨132813, by rfl⟩ : syracuseStep 1416677 = 265627) (by norm_num)
theorem B1416701 : Blo 940584 1416701 := bbase (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) (by norm_num)
theorem B1416725 : Blo 940584 1416725 := bbase (se 6 (by rfl) ⟨33204, by rfl⟩ : syracuseStep 1416725 = 66409) (by norm_num)
theorem B1416749 : Blo 940584 1416749 := bbase (se 3 (by rfl) ⟨265640, by rfl⟩ : syracuseStep 1416749 = 531281) (by norm_num)
theorem B1416773 : Blo 940584 1416773 := bbase (se 4 (by rfl) ⟨132822, by rfl⟩ : syracuseStep 1416773 = 265645) (by norm_num)
theorem B1416797 : Blo 940584 1416797 := bbase (se 3 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 1416797 = 531299) (by norm_num)
theorem B1416821 : Blo 940584 1416821 := bbase (se 5 (by rfl) ⟨66413, by rfl⟩ : syracuseStep 1416821 = 132827) (by norm_num)
theorem B1416845 : Blo 940584 1416845 := bbase (se 3 (by rfl) ⟨265658, by rfl⟩ : syracuseStep 1416845 = 531317) (by norm_num)
theorem B1416869 : Blo 940584 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B3186485 : Blo 940584 3186485 := bbase (se 5 (by rfl) ⟨149366, by rfl⟩ : syracuseStep 3186485 = 298733) (by norm_num)
theorem B1613765 : Blo 940584 1613765 := bbase (se 4 (by rfl) ⟨151290, by rfl⟩ : syracuseStep 1613765 = 302581) (by norm_num)
theorem B8036405 : Blo 940584 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B3186917 : Blo 940584 3186917 := bbase (se 4 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 3186917 = 597547) (by norm_num)
theorem B3580469 : Blo 940584 3580469 := bbase (se 5 (by rfl) ⟨167834, by rfl⟩ : syracuseStep 3580469 = 335669) (by norm_num)
theorem B3187349 : Blo 940584 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B1909405 : Blo 940584 1909405 := bbase (se 3 (by rfl) ⟨358013, by rfl⟩ : syracuseStep 1909405 = 716027) (by norm_num)
theorem B4530917 : Blo 940584 4530917 := bbase (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) (by norm_num)
theorem B3580757 : Blo 940584 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B3187781 : Blo 940584 3187781 := bbase (se 4 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 3187781 = 597709) (by norm_num)
theorem B1811605 : Blo 940584 1811605 := bbase (se 6 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 1811605 = 84919) (by norm_num)
theorem B3450005 : Blo 940584 3450005 := bbase (se 6 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 3450005 = 161719) (by norm_num)
theorem B1615133 : Blo 940584 1615133 := bbase (se 3 (by rfl) ⟨302837, by rfl⟩ : syracuseStep 1615133 = 605675) (by norm_num)
theorem B1058161 : Blo 940584 1058161 := bbase (se 2 (by rfl) ⟨396810, by rfl⟩ : syracuseStep 1058161 = 793621) (by norm_num)
theorem B1058197 : Blo 940584 1058197 := bbase (se 6 (by rfl) ⟨24801, by rfl⟩ : syracuseStep 1058197 = 49603) (by norm_num)
theorem B1058233 : Blo 940584 1058233 := bbase (se 2 (by rfl) ⟨396837, by rfl⟩ : syracuseStep 1058233 = 793675) (by norm_num)
theorem B3024341 : Blo 940584 3024341 := bbase (se 7 (by rfl) ⟨35441, by rfl⟩ : syracuseStep 3024341 = 70883) (by norm_num)
theorem B1058269 : Blo 940584 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B1058305 : Blo 940584 1058305 := bbase (se 2 (by rfl) ⟨396864, by rfl⟩ : syracuseStep 1058305 = 793729) (by norm_num)
theorem B1058341 : Blo 940584 1058341 := bbase (se 4 (by rfl) ⟨99219, by rfl⟩ : syracuseStep 1058341 = 198439) (by norm_num)
theorem B1058377 : Blo 940584 1058377 := bbase (se 2 (by rfl) ⟨396891, by rfl⟩ : syracuseStep 1058377 = 793783) (by norm_num)
theorem B1058413 : Blo 940584 1058413 := bbase (se 3 (by rfl) ⟨198452, by rfl⟩ : syracuseStep 1058413 = 396905) (by norm_num)
theorem B1058449 : Blo 940584 1058449 := bbase (se 2 (by rfl) ⟨396918, by rfl⟩ : syracuseStep 1058449 = 793837) (by norm_num)
theorem B1058485 : Blo 940584 1058485 := bbase (se 5 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 1058485 = 99233) (by norm_num)
theorem B1058521 : Blo 940584 1058521 := bbase (se 2 (by rfl) ⟨396945, by rfl⟩ : syracuseStep 1058521 = 793891) (by norm_num)
theorem B1058557 : Blo 940584 1058557 := bbase (se 3 (by rfl) ⟨198479, by rfl⟩ : syracuseStep 1058557 = 396959) (by norm_num)
theorem B1910533 : Blo 940584 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B4073237 : Blo 940584 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1058593 : Blo 940584 1058593 := bbase (se 2 (by rfl) ⟨396972, by rfl⟩ : syracuseStep 1058593 = 793945) (by norm_num)
theorem B1058629 : Blo 940584 1058629 := bbase (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) (by norm_num)
theorem B1058665 : Blo 940584 1058665 := bbase (se 2 (by rfl) ⟨396999, by rfl⟩ : syracuseStep 1058665 = 793999) (by norm_num)
theorem B2008957 : Blo 940584 2008957 := bbase (se 3 (by rfl) ⟨376679, by rfl⟩ : syracuseStep 2008957 = 753359) (by norm_num)
theorem B1058701 : Blo 940584 1058701 := bbase (se 3 (by rfl) ⟨198506, by rfl⟩ : syracuseStep 1058701 = 397013) (by norm_num)
theorem B1058737 : Blo 940584 1058737 := bbase (se 2 (by rfl) ⟨397026, by rfl⟩ : syracuseStep 1058737 = 794053) (by norm_num)
theorem B1058773 : Blo 940584 1058773 := bbase (se 7 (by rfl) ⟨12407, by rfl⟩ : syracuseStep 1058773 = 24815) (by norm_num)
theorem B3581941 : Blo 940584 3581941 := bbase (se 5 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 3581941 = 335807) (by norm_num)
theorem B1058809 : Blo 940584 1058809 := bbase (se 2 (by rfl) ⟨397053, by rfl⟩ : syracuseStep 1058809 = 794107) (by norm_num)
theorem B1058845 : Blo 940584 1058845 := bbase (se 3 (by rfl) ⟨198533, by rfl⟩ : syracuseStep 1058845 = 397067) (by norm_num)
theorem B1058881 : Blo 940584 1058881 := bbase (se 2 (by rfl) ⟨397080, by rfl⟩ : syracuseStep 1058881 = 794161) (by norm_num)
theorem B1058917 : Blo 940584 1058917 := bbase (se 4 (by rfl) ⟨99273, by rfl⟩ : syracuseStep 1058917 = 198547) (by norm_num)
theorem B1058953 : Blo 940584 1058953 := bbase (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) (by norm_num)
theorem B1058989 : Blo 940584 1058989 := bbase (se 3 (by rfl) ⟨198560, by rfl⟩ : syracuseStep 1058989 = 397121) (by norm_num)
theorem B1059025 : Blo 940584 1059025 := bbase (se 2 (by rfl) ⟨397134, by rfl⟩ : syracuseStep 1059025 = 794269) (by norm_num)
theorem B1059061 : Blo 940584 1059061 := bbase (se 5 (by rfl) ⟨49643, by rfl⟩ : syracuseStep 1059061 = 99287) (by norm_num)
theorem B1059097 : Blo 940584 1059097 := bbase (se 2 (by rfl) ⟨397161, by rfl⟩ : syracuseStep 1059097 = 794323) (by norm_num)
theorem B3582245 : Blo 940584 3582245 := bbase (se 4 (by rfl) ⟨335835, by rfl⟩ : syracuseStep 3582245 = 671671) (by norm_num)
theorem B1059133 : Blo 940584 1059133 := bbase (se 3 (by rfl) ⟨198587, by rfl⟩ : syracuseStep 1059133 = 397175) (by norm_num)
theorem B1059169 : Blo 940584 1059169 := bbase (se 2 (by rfl) ⟨397188, by rfl⟩ : syracuseStep 1059169 = 794377) (by norm_num)
theorem B2009461 : Blo 940584 2009461 := bbase (se 5 (by rfl) ⟨94193, by rfl⟩ : syracuseStep 2009461 = 188387) (by norm_num)
theorem B4761989 : Blo 940584 4761989 := bbase (se 4 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 4761989 = 892873) (by norm_num)
theorem B1059205 : Blo 940584 1059205 := bbase (se 4 (by rfl) ⟨99300, by rfl⟩ : syracuseStep 1059205 = 198601) (by norm_num)
theorem B1059241 : Blo 940584 1059241 := bbase (se 2 (by rfl) ⟨397215, by rfl⟩ : syracuseStep 1059241 = 794431) (by norm_num)
theorem B1550765 : Blo 940584 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B1059277 : Blo 940584 1059277 := bbase (se 3 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 1059277 = 397229) (by norm_num)
theorem B11446741 : Blo 940584 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B1059313 : Blo 940584 1059313 := bbase (se 2 (by rfl) ⟨397242, by rfl⟩ : syracuseStep 1059313 = 794485) (by norm_num)
theorem B2206205 : Blo 940584 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B1059349 : Blo 940584 1059349 := bbase (se 6 (by rfl) ⟨24828, by rfl⟩ : syracuseStep 1059349 = 49657) (by norm_num)
theorem B1059385 : Blo 940584 1059385 := bbase (se 2 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 1059385 = 794539) (by norm_num)
theorem B1190477 : Blo 940584 1190477 := bbase (se 3 (by rfl) ⟨223214, by rfl⟩ : syracuseStep 1190477 = 446429) (by norm_num)
theorem B1059421 : Blo 940584 1059421 := bbase (se 3 (by rfl) ⟨198641, by rfl⟩ : syracuseStep 1059421 = 397283) (by norm_num)
theorem B1059457 : Blo 940584 1059457 := bbase (se 2 (by rfl) ⟨397296, by rfl⟩ : syracuseStep 1059457 = 794593) (by norm_num)
theorem B1190533 : Blo 940584 1190533 := bbase (se 4 (by rfl) ⟨111612, by rfl⟩ : syracuseStep 1190533 = 223225) (by norm_num)
theorem B1059493 : Blo 940584 1059493 := bbase (se 4 (by rfl) ⟨99327, by rfl⟩ : syracuseStep 1059493 = 198655) (by norm_num)
theorem B1059529 : Blo 940584 1059529 := bbase (se 2 (by rfl) ⟨397323, by rfl⟩ : syracuseStep 1059529 = 794647) (by norm_num)
theorem B1190629 : Blo 940584 1190629 := bbase (se 4 (by rfl) ⟨111621, by rfl⟩ : syracuseStep 1190629 = 223243) (by norm_num)
theorem B1059565 : Blo 940584 1059565 := bbase (se 3 (by rfl) ⟨198668, by rfl⟩ : syracuseStep 1059565 = 397337) (by norm_num)
theorem B1059601 : Blo 940584 1059601 := bbase (se 2 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 1059601 = 794701) (by norm_num)
theorem B1059637 : Blo 940584 1059637 := bbase (se 5 (by rfl) ⟨49670, by rfl⟩ : syracuseStep 1059637 = 99341) (by norm_num)
theorem B1911613 : Blo 940584 1911613 := bbase (se 3 (by rfl) ⟨358427, by rfl⟩ : syracuseStep 1911613 = 716855) (by norm_num)
theorem B1059673 : Blo 940584 1059673 := bbase (se 2 (by rfl) ⟨397377, by rfl⟩ : syracuseStep 1059673 = 794755) (by norm_num)
theorem B1059709 : Blo 940584 1059709 := bbase (se 3 (by rfl) ⟨198695, by rfl⟩ : syracuseStep 1059709 = 397391) (by norm_num)
theorem B1190801 : Blo 940584 1190801 := bbase (se 2 (by rfl) ⟨446550, by rfl⟩ : syracuseStep 1190801 = 893101) (by norm_num)
theorem B1059745 : Blo 940584 1059745 := bbase (se 2 (by rfl) ⟨397404, by rfl⟩ : syracuseStep 1059745 = 794809) (by norm_num)
theorem B1059781 : Blo 940584 1059781 := bbase (se 4 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 1059781 = 198709) (by norm_num)
theorem B1190857 : Blo 940584 1190857 := bbase (se 2 (by rfl) ⟨446571, by rfl⟩ : syracuseStep 1190857 = 893143) (by norm_num)
theorem B1059817 : Blo 940584 1059817 := bbase (se 2 (by rfl) ⟨397431, by rfl⟩ : syracuseStep 1059817 = 794863) (by norm_num)
theorem B1059853 : Blo 940584 1059853 := bbase (se 3 (by rfl) ⟨198722, by rfl⟩ : syracuseStep 1059853 = 397445) (by norm_num)
theorem B1190953 : Blo 940584 1190953 := bbase (se 2 (by rfl) ⟨446607, by rfl⟩ : syracuseStep 1190953 = 893215) (by norm_num)
theorem B1059889 : Blo 940584 1059889 := bbase (se 2 (by rfl) ⟨397458, by rfl⟩ : syracuseStep 1059889 = 794917) (by norm_num)
theorem B1059925 : Blo 940584 1059925 := bbase (se 8 (by rfl) ⟨6210, by rfl⟩ : syracuseStep 1059925 = 12421) (by norm_num)
theorem B1059961 : Blo 940584 1059961 := bbase (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) (by norm_num)
theorem B1059997 : Blo 940584 1059997 := bbase (se 3 (by rfl) ⟨198749, by rfl⟩ : syracuseStep 1059997 = 397499) (by norm_num)
theorem B1060033 : Blo 940584 1060033 := bbase (se 2 (by rfl) ⟨397512, by rfl⟩ : syracuseStep 1060033 = 795025) (by norm_num)
theorem B1191125 : Blo 940584 1191125 := bbase (se 7 (by rfl) ⟨13958, by rfl⟩ : syracuseStep 1191125 = 27917) (by norm_num)
theorem B1060069 : Blo 940584 1060069 := bbase (se 4 (by rfl) ⟨99381, by rfl⟩ : syracuseStep 1060069 = 198763) (by norm_num)
theorem B2010349 : Blo 940584 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B1060105 : Blo 940584 1060105 := bbase (se 2 (by rfl) ⟨397539, by rfl⟩ : syracuseStep 1060105 = 795079) (by norm_num)
theorem B1191181 : Blo 940584 1191181 := bbase (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) (by norm_num)
theorem B1060141 : Blo 940584 1060141 := bbase (se 3 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 1060141 = 397553) (by norm_num)
theorem B1060177 : Blo 940584 1060177 := bbase (se 2 (by rfl) ⟨397566, by rfl⟩ : syracuseStep 1060177 = 795133) (by norm_num)
theorem B16100693 : Blo 940584 16100693 := bbase (se 11 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 16100693 = 23585) (by norm_num)
theorem B1191277 : Blo 940584 1191277 := bbase (se 3 (by rfl) ⟨223364, by rfl⟩ : syracuseStep 1191277 = 446729) (by norm_num)
theorem B1060213 : Blo 940584 1060213 := bbase (se 5 (by rfl) ⟨49697, by rfl⟩ : syracuseStep 1060213 = 99395) (by norm_num)
theorem B1060249 : Blo 940584 1060249 := bbase (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) (by norm_num)
theorem B1060285 : Blo 940584 1060285 := bbase (se 3 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 1060285 = 397607) (by norm_num)
theorem B1912261 : Blo 940584 1912261 := bbase (se 4 (by rfl) ⟨179274, by rfl⟩ : syracuseStep 1912261 = 358549) (by norm_num)
theorem B1060321 : Blo 940584 1060321 := bbase (se 2 (by rfl) ⟨397620, by rfl⟩ : syracuseStep 1060321 = 795241) (by norm_num)
theorem B1060357 : Blo 940584 1060357 := bbase (se 4 (by rfl) ⟨99408, by rfl⟩ : syracuseStep 1060357 = 198817) (by norm_num)
theorem B1191449 : Blo 940584 1191449 := bbase (se 2 (by rfl) ⟨446793, by rfl⟩ : syracuseStep 1191449 = 893587) (by norm_num)
theorem B3059237 : Blo 940584 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B1060393 : Blo 940584 1060393 := bbase (se 2 (by rfl) ⟨397647, by rfl⟩ : syracuseStep 1060393 = 795295) (by norm_num)
theorem B2862661 : Blo 940584 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B1060429 : Blo 940584 1060429 := bbase (se 3 (by rfl) ⟨198830, by rfl⟩ : syracuseStep 1060429 = 397661) (by norm_num)
theorem B1191505 : Blo 940584 1191505 := bbase (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) (by norm_num)
theorem B1912429 : Blo 940584 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B1060465 : Blo 940584 1060465 := bbase (se 2 (by rfl) ⟨397674, by rfl⟩ : syracuseStep 1060465 = 795349) (by norm_num)
theorem B3059333 : Blo 940584 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B4763285 : Blo 940584 4763285 := bbase (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) (by norm_num)
theorem B1060501 : Blo 940584 1060501 := bbase (se 6 (by rfl) ⟨24855, by rfl⟩ : syracuseStep 1060501 = 49711) (by norm_num)
theorem B1191601 : Blo 940584 1191601 := bbase (se 2 (by rfl) ⟨446850, by rfl⟩ : syracuseStep 1191601 = 893701) (by norm_num)
theorem B1060537 : Blo 940584 1060537 := bbase (se 2 (by rfl) ⟨397701, by rfl⟩ : syracuseStep 1060537 = 795403) (by norm_num)
theorem B2010845 : Blo 940584 2010845 := bbase (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) (by norm_num)
theorem B1060573 : Blo 940584 1060573 := bbase (se 3 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 1060573 = 397715) (by norm_num)
theorem B1289981 : Blo 940584 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B1060609 : Blo 940584 1060609 := bbase (se 2 (by rfl) ⟨397728, by rfl⟩ : syracuseStep 1060609 = 795457) (by norm_num)
theorem B1060645 : Blo 940584 1060645 := bbase (se 4 (by rfl) ⟨99435, by rfl⟩ : syracuseStep 1060645 = 198871) (by norm_num)
theorem B1060681 : Blo 940584 1060681 := bbase (se 2 (by rfl) ⟨397755, by rfl⟩ : syracuseStep 1060681 = 795511) (by norm_num)
theorem B1191773 : Blo 940584 1191773 := bbase (se 3 (by rfl) ⟨223457, by rfl⟩ : syracuseStep 1191773 = 446915) (by norm_num)
theorem B1060717 : Blo 940584 1060717 := bbase (se 3 (by rfl) ⟨198884, by rfl⟩ : syracuseStep 1060717 = 397769) (by norm_num)
theorem B1060753 : Blo 940584 1060753 := bbase (se 2 (by rfl) ⟨397782, by rfl⟩ : syracuseStep 1060753 = 795565) (by norm_num)
theorem B1191829 : Blo 940584 1191829 := bbase (se 6 (by rfl) ⟨27933, by rfl⟩ : syracuseStep 1191829 = 55867) (by norm_num)
theorem B1060789 : Blo 940584 1060789 := bbase (se 5 (by rfl) ⟨49724, by rfl⟩ : syracuseStep 1060789 = 99449) (by norm_num)
theorem B1060825 : Blo 940584 1060825 := bbase (se 2 (by rfl) ⟨397809, by rfl⟩ : syracuseStep 1060825 = 795619) (by norm_num)
theorem B1191925 : Blo 940584 1191925 := bbase (se 5 (by rfl) ⟨55871, by rfl⟩ : syracuseStep 1191925 = 111743) (by norm_num)
theorem B1060861 : Blo 940584 1060861 := bbase (se 3 (by rfl) ⟨198911, by rfl⟩ : syracuseStep 1060861 = 397823) (by norm_num)
theorem B1060897 : Blo 940584 1060897 := bbase (se 2 (by rfl) ⟨397836, by rfl⟩ : syracuseStep 1060897 = 795673) (by norm_num)
theorem B1060933 : Blo 940584 1060933 := bbase (se 4 (by rfl) ⟨99462, by rfl⟩ : syracuseStep 1060933 = 198925) (by norm_num)
theorem B1060969 : Blo 940584 1060969 := bbase (se 2 (by rfl) ⟨397863, by rfl⟩ : syracuseStep 1060969 = 795727) (by norm_num)
theorem B1061005 : Blo 940584 1061005 := bbase (se 3 (by rfl) ⟨198938, by rfl⟩ : syracuseStep 1061005 = 397877) (by norm_num)
theorem B1192097 : Blo 940584 1192097 := bbase (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) (by norm_num)
theorem B1061041 : Blo 940584 1061041 := bbase (se 2 (by rfl) ⟨397890, by rfl⟩ : syracuseStep 1061041 = 795781) (by norm_num)
theorem B1061077 : Blo 940584 1061077 := bbase (se 7 (by rfl) ⟨12434, by rfl⟩ : syracuseStep 1061077 = 24869) (by norm_num)
theorem B1192153 : Blo 940584 1192153 := bbase (se 2 (by rfl) ⟨447057, by rfl⟩ : syracuseStep 1192153 = 894115) (by norm_num)
theorem B1061113 : Blo 940584 1061113 := bbase (se 2 (by rfl) ⟨397917, by rfl⟩ : syracuseStep 1061113 = 795835) (by norm_num)
theorem B1061149 : Blo 940584 1061149 := bbase (se 3 (by rfl) ⟨198965, by rfl⟩ : syracuseStep 1061149 = 397931) (by norm_num)
theorem B1192249 : Blo 940584 1192249 := bbase (se 2 (by rfl) ⟨447093, by rfl⟩ : syracuseStep 1192249 = 894187) (by norm_num)
theorem B1061185 : Blo 940584 1061185 := bbase (se 2 (by rfl) ⟨397944, by rfl⟩ : syracuseStep 1061185 = 795889) (by norm_num)
theorem B1061221 : Blo 940584 1061221 := bbase (se 4 (by rfl) ⟨99489, by rfl⟩ : syracuseStep 1061221 = 198979) (by norm_num)
theorem B3584357 : Blo 940584 3584357 := bbase (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) (by norm_num)
theorem B1061257 : Blo 940584 1061257 := bbase (se 2 (by rfl) ⟨397971, by rfl⟩ : syracuseStep 1061257 = 795943) (by norm_num)
theorem B1061293 : Blo 940584 1061293 := bbase (se 3 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 1061293 = 397985) (by norm_num)
theorem B1061329 : Blo 940584 1061329 := bbase (se 2 (by rfl) ⟨397998, by rfl⟩ : syracuseStep 1061329 = 795997) (by norm_num)
theorem B1192421 : Blo 940584 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B1061365 : Blo 940584 1061365 := bbase (se 5 (by rfl) ⟨49751, by rfl⟩ : syracuseStep 1061365 = 99503) (by norm_num)
theorem B1061401 : Blo 940584 1061401 := bbase (se 2 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 1061401 = 796051) (by norm_num)
theorem B1192477 : Blo 940584 1192477 := bbase (se 3 (by rfl) ⟨223589, by rfl⟩ : syracuseStep 1192477 = 447179) (by norm_num)
theorem B1061437 : Blo 940584 1061437 := bbase (se 3 (by rfl) ⟨199019, by rfl⟩ : syracuseStep 1061437 = 398039) (by norm_num)
theorem B2011733 : Blo 940584 2011733 := bbase (se 8 (by rfl) ⟨11787, by rfl⟩ : syracuseStep 2011733 = 23575) (by norm_num)
theorem B1061473 : Blo 940584 1061473 := bbase (se 2 (by rfl) ⟨398052, by rfl⟩ : syracuseStep 1061473 = 796105) (by norm_num)
theorem B1192573 : Blo 940584 1192573 := bbase (se 3 (by rfl) ⟨223607, by rfl⟩ : syracuseStep 1192573 = 447215) (by norm_num)
theorem B1061509 : Blo 940584 1061509 := bbase (se 4 (by rfl) ⟨99516, by rfl⟩ : syracuseStep 1061509 = 199033) (by norm_num)
theorem B3584645 : Blo 940584 3584645 := bbase (se 4 (by rfl) ⟨336060, by rfl⟩ : syracuseStep 3584645 = 672121) (by norm_num)
theorem B1061545 : Blo 940584 1061545 := bbase (se 2 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 1061545 = 796159) (by norm_num)
theorem B2011853 : Blo 940584 2011853 := bbase (se 3 (by rfl) ⟨377222, by rfl⟩ : syracuseStep 2011853 = 754445) (by norm_num)
theorem B1061581 : Blo 940584 1061581 := bbase (se 3 (by rfl) ⟨199046, by rfl⟩ : syracuseStep 1061581 = 398093) (by norm_num)
theorem B1061617 : Blo 940584 1061617 := bbase (se 2 (by rfl) ⟨398106, by rfl⟩ : syracuseStep 1061617 = 796213) (by norm_num)
theorem B1061653 : Blo 940584 1061653 := bbase (se 6 (by rfl) ⟨24882, by rfl⟩ : syracuseStep 1061653 = 49765) (by norm_num)
theorem B1192745 : Blo 940584 1192745 := bbase (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) (by norm_num)
theorem B1061689 : Blo 940584 1061689 := bbase (se 2 (by rfl) ⟨398133, by rfl⟩ : syracuseStep 1061689 = 796267) (by norm_num)
theorem B1061725 : Blo 940584 1061725 := bbase (se 3 (by rfl) ⟨199073, by rfl⟩ : syracuseStep 1061725 = 398147) (by norm_num)
theorem B1192801 : Blo 940584 1192801 := bbase (se 2 (by rfl) ⟨447300, by rfl⟩ : syracuseStep 1192801 = 894601) (by norm_num)
theorem B1061761 : Blo 940584 1061761 := bbase (se 2 (by rfl) ⟨398160, by rfl⟩ : syracuseStep 1061761 = 796321) (by norm_num)
theorem B4764581 : Blo 940584 4764581 := bbase (se 4 (by rfl) ⟨446679, by rfl⟩ : syracuseStep 4764581 = 893359) (by norm_num)
theorem B1061797 : Blo 940584 1061797 := bbase (se 4 (by rfl) ⟨99543, by rfl⟩ : syracuseStep 1061797 = 199087) (by norm_num)
theorem B1192897 : Blo 940584 1192897 := bbase (se 2 (by rfl) ⟨447336, by rfl⟩ : syracuseStep 1192897 = 894673) (by norm_num)
theorem B1061833 : Blo 940584 1061833 := bbase (se 2 (by rfl) ⟨398187, by rfl⟩ : syracuseStep 1061833 = 796375) (by norm_num)
theorem B1061869 : Blo 940584 1061869 := bbase (se 3 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 1061869 = 398201) (by norm_num)
theorem B1061905 : Blo 940584 1061905 := bbase (se 2 (by rfl) ⟨398214, by rfl⟩ : syracuseStep 1061905 = 796429) (by norm_num)
theorem B1061941 : Blo 940584 1061941 := bbase (se 5 (by rfl) ⟨49778, by rfl⟩ : syracuseStep 1061941 = 99557) (by norm_num)
theorem B1061977 : Blo 940584 1061977 := bbase (se 2 (by rfl) ⟨398241, by rfl⟩ : syracuseStep 1061977 = 796483) (by norm_num)
theorem B1193069 : Blo 940584 1193069 := bbase (se 3 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 1193069 = 447401) (by norm_num)
theorem B1062013 : Blo 940584 1062013 := bbase (se 3 (by rfl) ⟨199127, by rfl⟩ : syracuseStep 1062013 = 398255) (by norm_num)
theorem B1062049 : Blo 940584 1062049 := bbase (se 2 (by rfl) ⟨398268, by rfl⟩ : syracuseStep 1062049 = 796537) (by norm_num)
theorem B1193125 : Blo 940584 1193125 := bbase (se 4 (by rfl) ⟨111855, by rfl⟩ : syracuseStep 1193125 = 223711) (by norm_num)
theorem B1062085 : Blo 940584 1062085 := bbase (se 4 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 1062085 = 199141) (by norm_num)
theorem B1062121 : Blo 940584 1062121 := bbase (se 2 (by rfl) ⟨398295, by rfl⟩ : syracuseStep 1062121 = 796591) (by norm_num)
theorem B1193221 : Blo 940584 1193221 := bbase (se 4 (by rfl) ⟨111864, by rfl⟩ : syracuseStep 1193221 = 223729) (by norm_num)
theorem B1062157 : Blo 940584 1062157 := bbase (se 3 (by rfl) ⟨199154, by rfl⟩ : syracuseStep 1062157 = 398309) (by norm_num)
theorem B1914149 : Blo 940584 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B1062193 : Blo 940584 1062193 := bbase (se 2 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 1062193 = 796645) (by norm_num)
theorem B1226045 : Blo 940584 1226045 := bbase (se 3 (by rfl) ⟨229883, by rfl⟩ : syracuseStep 1226045 = 459767) (by norm_num)
theorem B2012485 : Blo 940584 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B1062229 : Blo 940584 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B1062265 : Blo 940584 1062265 := bbase (se 2 (by rfl) ⟨398349, by rfl⟩ : syracuseStep 1062265 = 796699) (by norm_num)
theorem B1062301 : Blo 940584 1062301 := bbase (se 3 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 1062301 = 398363) (by norm_num)
theorem B1193393 : Blo 940584 1193393 := bbase (se 2 (by rfl) ⟨447522, by rfl⟩ : syracuseStep 1193393 = 895045) (by norm_num)
theorem B1062337 : Blo 940584 1062337 := bbase (se 2 (by rfl) ⟨398376, by rfl⟩ : syracuseStep 1062337 = 796753) (by norm_num)
theorem B1062373 : Blo 940584 1062373 := bbase (se 4 (by rfl) ⟨99597, by rfl⟩ : syracuseStep 1062373 = 199195) (by norm_num)
theorem B1193449 : Blo 940584 1193449 := bbase (se 2 (by rfl) ⟨447543, by rfl⟩ : syracuseStep 1193449 = 895087) (by norm_num)
theorem B1062409 : Blo 940584 1062409 := bbase (se 2 (by rfl) ⟨398403, by rfl⟩ : syracuseStep 1062409 = 796807) (by norm_num)
theorem B1062445 : Blo 940584 1062445 := bbase (se 3 (by rfl) ⟨199208, by rfl⟩ : syracuseStep 1062445 = 398417) (by norm_num)
theorem B1193545 : Blo 940584 1193545 := bbase (se 2 (by rfl) ⟨447579, by rfl⟩ : syracuseStep 1193545 = 895159) (by norm_num)
theorem B1062481 : Blo 940584 1062481 := bbase (se 2 (by rfl) ⟨398430, by rfl⟩ : syracuseStep 1062481 = 796861) (by norm_num)
theorem B1062517 : Blo 940584 1062517 := bbase (se 5 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 1062517 = 99611) (by norm_num)
theorem B1062553 : Blo 940584 1062553 := bbase (se 2 (by rfl) ⟨398457, by rfl⟩ : syracuseStep 1062553 = 796915) (by norm_num)
theorem B1062589 : Blo 940584 1062589 := bbase (se 3 (by rfl) ⟨199235, by rfl⟩ : syracuseStep 1062589 = 398471) (by norm_num)
theorem B6043349 : Blo 940584 6043349 := bbase (se 7 (by rfl) ⟨70820, by rfl⟩ : syracuseStep 6043349 = 141641) (by norm_num)
theorem B1062625 : Blo 940584 1062625 := bbase (se 2 (by rfl) ⟨398484, by rfl⟩ : syracuseStep 1062625 = 796969) (by norm_num)
theorem B1193717 : Blo 940584 1193717 := bbase (se 5 (by rfl) ⟨55955, by rfl⟩ : syracuseStep 1193717 = 111911) (by norm_num)
theorem B3585829 : Blo 940584 3585829 := bbase (se 4 (by rfl) ⟨336171, by rfl⟩ : syracuseStep 3585829 = 672343) (by norm_num)
theorem B1193773 : Blo 940584 1193773 := bbase (se 3 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 1193773 = 447665) (by norm_num)
theorem B1193869 : Blo 940584 1193869 := bbase (se 3 (by rfl) ⟨223850, by rfl⟩ : syracuseStep 1193869 = 447701) (by norm_num)
theorem B1194041 : Blo 940584 1194041 := bbase (se 2 (by rfl) ⟨447765, by rfl⟩ : syracuseStep 1194041 = 895531) (by norm_num)
theorem B1587269 : Blo 940584 1587269 := bbase (se 4 (by rfl) ⟨148806, by rfl⟩ : syracuseStep 1587269 = 297613) (by norm_num)
theorem B3586133 : Blo 940584 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B1194097 : Blo 940584 1194097 := bbase (se 2 (by rfl) ⟨447786, by rfl⟩ : syracuseStep 1194097 = 895573) (by norm_num)
theorem B4765877 : Blo 940584 4765877 := bbase (se 5 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 4765877 = 446801) (by norm_num)
theorem B2013373 : Blo 940584 2013373 := bbase (se 3 (by rfl) ⟨377507, by rfl⟩ : syracuseStep 2013373 = 755015) (by norm_num)
theorem B1587397 : Blo 940584 1587397 := bbase (se 4 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 1587397 = 297637) (by norm_num)
theorem B1194193 : Blo 940584 1194193 := bbase (se 2 (by rfl) ⟨447822, by rfl⟩ : syracuseStep 1194193 = 895645) (by norm_num)
theorem B1587485 : Blo 940584 1587485 := bbase (se 3 (by rfl) ⟨297653, by rfl⟩ : syracuseStep 1587485 = 595307) (by norm_num)
theorem B2013493 : Blo 940584 2013493 := bbase (se 5 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 2013493 = 188765) (by norm_num)
theorem B36256085 : Blo 940584 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B1194365 : Blo 940584 1194365 := bbase (se 3 (by rfl) ⟨223943, by rfl⟩ : syracuseStep 1194365 = 447887) (by norm_num)
theorem B1587613 : Blo 940584 1587613 := bbase (se 3 (by rfl) ⟨297677, by rfl⟩ : syracuseStep 1587613 = 595355) (by norm_num)
theorem B1194421 : Blo 940584 1194421 := bbase (se 5 (by rfl) ⟨55988, by rfl⟩ : syracuseStep 1194421 = 111977) (by norm_num)
theorem B1587701 : Blo 940584 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B3389957 : Blo 940584 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B7158293 : Blo 940584 7158293 := bbase (se 6 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 7158293 = 335545) (by norm_num)
theorem B1194517 : Blo 940584 1194517 := bbase (se 6 (by rfl) ⟨27996, by rfl⟩ : syracuseStep 1194517 = 55993) (by norm_num)
theorem B2013749 : Blo 940584 2013749 := bbase (se 5 (by rfl) ⟨94394, by rfl⟩ : syracuseStep 2013749 = 188789) (by norm_num)
theorem B4536917 : Blo 940584 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B1587829 : Blo 940584 1587829 := bbase (se 5 (by rfl) ⟨74429, by rfl⟩ : syracuseStep 1587829 = 148859) (by norm_num)
theorem B1194689 : Blo 940584 1194689 := bbase (se 2 (by rfl) ⟨448008, by rfl⟩ : syracuseStep 1194689 = 896017) (by norm_num)
theorem B1587917 : Blo 940584 1587917 := bbase (se 3 (by rfl) ⟨297734, by rfl⟩ : syracuseStep 1587917 = 595469) (by norm_num)
theorem B1194745 : Blo 940584 1194745 := bbase (se 2 (by rfl) ⟨448029, by rfl⟩ : syracuseStep 1194745 = 896059) (by norm_num)
theorem B1588045 : Blo 940584 1588045 := bbase (se 3 (by rfl) ⟨297758, by rfl⟩ : syracuseStep 1588045 = 595517) (by norm_num)
theorem B1194841 : Blo 940584 1194841 := bbase (se 2 (by rfl) ⟨448065, by rfl⟩ : syracuseStep 1194841 = 896131) (by norm_num)
theorem B1588133 : Blo 940584 1588133 := bbase (se 4 (by rfl) ⟨148887, by rfl⟩ : syracuseStep 1588133 = 297775) (by norm_num)
theorem B1195013 : Blo 940584 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B1588261 : Blo 940584 1588261 := bbase (se 4 (by rfl) ⟨148899, by rfl⟩ : syracuseStep 1588261 = 297799) (by norm_num)
theorem B1195069 : Blo 940584 1195069 := bbase (se 3 (by rfl) ⟨224075, by rfl⟩ : syracuseStep 1195069 = 448151) (by norm_num)
theorem B2866261 : Blo 940584 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B1588349 : Blo 940584 1588349 := bbase (se 3 (by rfl) ⟨297815, by rfl⟩ : syracuseStep 1588349 = 595631) (by norm_num)
theorem B1195165 : Blo 940584 1195165 := bbase (se 3 (by rfl) ⟨224093, by rfl⟩ : syracuseStep 1195165 = 448187) (by norm_num)
theorem B1588477 : Blo 940584 1588477 := bbase (se 3 (by rfl) ⟨297839, by rfl⟩ : syracuseStep 1588477 = 595679) (by norm_num)
theorem B1195337 : Blo 940584 1195337 := bbase (se 2 (by rfl) ⟨448251, by rfl⟩ : syracuseStep 1195337 = 896503) (by norm_num)
theorem B1588565 : Blo 940584 1588565 := bbase (se 11 (by rfl) ⟨1163, by rfl⟩ : syracuseStep 1588565 = 2327) (by norm_num)
theorem B1195393 : Blo 940584 1195393 := bbase (se 2 (by rfl) ⟨448272, by rfl⟩ : syracuseStep 1195393 = 896545) (by norm_num)
theorem B1228169 : Blo 940584 1228169 := bbase (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) (by norm_num)
theorem B2014637 : Blo 940584 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B4767173 : Blo 940584 4767173 := bbase (se 4 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 4767173 = 893845) (by norm_num)
theorem B1588693 : Blo 940584 1588693 := bbase (se 7 (by rfl) ⟨18617, by rfl⟩ : syracuseStep 1588693 = 37235) (by norm_num)
theorem B1195489 : Blo 940584 1195489 := bbase (se 2 (by rfl) ⟨448308, by rfl⟩ : syracuseStep 1195489 = 896617) (by norm_num)
theorem B1588781 : Blo 940584 1588781 := bbase (se 3 (by rfl) ⟨297896, by rfl⟩ : syracuseStep 1588781 = 595793) (by norm_num)
theorem B1130053 : Blo 940584 1130053 := bbase (se 4 (by rfl) ⟨105942, by rfl⟩ : syracuseStep 1130053 = 211885) (by norm_num)
theorem B1130081 : Blo 940584 1130081 := bbase (se 2 (by rfl) ⟨423780, by rfl⟩ : syracuseStep 1130081 = 847561) (by norm_num)
theorem B3620501 : Blo 940584 3620501 := bbase (se 6 (by rfl) ⟨84855, by rfl⟩ : syracuseStep 3620501 = 169711) (by norm_num)
theorem B2014877 : Blo 940584 2014877 := bbase (se 3 (by rfl) ⟨377789, by rfl⟩ : syracuseStep 2014877 = 755579) (by norm_num)
theorem B1588909 : Blo 940584 1588909 := bbase (se 3 (by rfl) ⟨297920, by rfl⟩ : syracuseStep 1588909 = 595841) (by norm_num)
theorem B1588997 : Blo 940584 1588997 := bbase (se 4 (by rfl) ⟨148968, by rfl⟩ : syracuseStep 1588997 = 297937) (by norm_num)
theorem B20954965 : Blo 940584 20954965 := bbase (se 9 (by rfl) ⟨61391, by rfl⟩ : syracuseStep 20954965 = 122783) (by norm_num)
theorem B1785701 : Blo 940584 1785701 := bbase (se 4 (by rfl) ⟨167409, by rfl⟩ : syracuseStep 1785701 = 334819) (by norm_num)
theorem B1589125 : Blo 940584 1589125 := bbase (se 4 (by rfl) ⟨148980, by rfl⟩ : syracuseStep 1589125 = 297961) (by norm_num)
theorem B3391397 : Blo 940584 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B1589213 : Blo 940584 1589213 := bbase (se 3 (by rfl) ⟨297977, by rfl⟩ : syracuseStep 1589213 = 595955) (by norm_num)
theorem B3620837 : Blo 940584 3620837 := bbase (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) (by norm_num)
theorem B1032229 : Blo 940584 1032229 := bbase (se 4 (by rfl) ⟨96771, by rfl⟩ : syracuseStep 1032229 = 193543) (by norm_num)
theorem B1130581 : Blo 940584 1130581 := bbase (se 8 (by rfl) ⟨6624, by rfl⟩ : syracuseStep 1130581 = 13249) (by norm_num)
theorem B1589341 : Blo 940584 1589341 := bbase (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) (by norm_num)
theorem B1785989 : Blo 940584 1785989 := bbase (se 4 (by rfl) ⟨167436, by rfl⟩ : syracuseStep 1785989 = 334873) (by norm_num)
theorem B2015381 : Blo 940584 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B2015389 : Blo 940584 2015389 := bbase (se 3 (by rfl) ⟨377885, by rfl⟩ : syracuseStep 2015389 = 755771) (by norm_num)
theorem B1589429 : Blo 940584 1589429 := bbase (se 5 (by rfl) ⟨74504, by rfl⟩ : syracuseStep 1589429 = 149009) (by norm_num)
theorem B1786141 : Blo 940584 1786141 := bbase (se 3 (by rfl) ⟨334901, by rfl⟩ : syracuseStep 1786141 = 669803) (by norm_num)
theorem B1589557 : Blo 940584 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1589645 : Blo 940584 1589645 := bbase (se 3 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 1589645 = 596117) (by norm_num)
theorem B1589773 : Blo 940584 1589773 := bbase (se 3 (by rfl) ⟨298082, by rfl⟩ : syracuseStep 1589773 = 596165) (by norm_num)
theorem B1786445 : Blo 940584 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B1589861 : Blo 940584 1589861 := bbase (se 4 (by rfl) ⟨149049, by rfl⟩ : syracuseStep 1589861 = 298099) (by norm_num)
theorem B4768469 : Blo 940584 4768469 := bbase (se 7 (by rfl) ⟨55880, by rfl⟩ : syracuseStep 4768469 = 111761) (by norm_num)
theorem B1589989 : Blo 940584 1589989 := bbase (se 4 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 1589989 = 298123) (by norm_num)
theorem B1590077 : Blo 940584 1590077 := bbase (se 3 (by rfl) ⟨298139, by rfl⟩ : syracuseStep 1590077 = 596279) (by norm_num)
theorem B2900821 : Blo 940584 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B1590205 : Blo 940584 1590205 := bbase (se 3 (by rfl) ⟨298163, by rfl⟩ : syracuseStep 1590205 = 596327) (by norm_num)
theorem B1590293 : Blo 940584 1590293 := bbase (se 6 (by rfl) ⟨37272, by rfl⟩ : syracuseStep 1590293 = 74545) (by norm_num)
theorem B1590421 : Blo 940584 1590421 := bbase (se 6 (by rfl) ⟨37275, by rfl⟩ : syracuseStep 1590421 = 74551) (by norm_num)
theorem B3392725 : Blo 940584 3392725 := bbase (se 7 (by rfl) ⟨39758, by rfl⟩ : syracuseStep 3392725 = 79517) (by norm_num)
theorem B967897 : Blo 940584 967897 := bbase (se 2 (by rfl) ⟨362961, by rfl⟩ : syracuseStep 967897 = 725923) (by norm_num)
theorem B1590509 : Blo 940584 1590509 := bbase (se 3 (by rfl) ⟨298220, by rfl⟩ : syracuseStep 1590509 = 596441) (by norm_num)
theorem B1131769 : Blo 940584 1131769 := bbase (se 2 (by rfl) ⟨424413, by rfl⟩ : syracuseStep 1131769 = 848827) (by norm_num)
theorem B2016517 : Blo 940584 2016517 := bbase (se 4 (by rfl) ⟨189048, by rfl⟩ : syracuseStep 2016517 = 378097) (by norm_num)
theorem B1787197 : Blo 940584 1787197 := bbase (se 3 (by rfl) ⟨335099, by rfl⟩ : syracuseStep 1787197 = 670199) (by norm_num)
theorem B1590637 : Blo 940584 1590637 := bbase (se 3 (by rfl) ⟨298244, by rfl⟩ : syracuseStep 1590637 = 596489) (by norm_num)
theorem B1131961 : Blo 940584 1131961 := bbase (se 2 (by rfl) ⟨424485, by rfl⟩ : syracuseStep 1131961 = 848971) (by norm_num)
theorem B1590725 : Blo 940584 1590725 := bbase (se 4 (by rfl) ⟨149130, by rfl⟩ : syracuseStep 1590725 = 298261) (by norm_num)
theorem B1787341 : Blo 940584 1787341 := bbase (se 3 (by rfl) ⟨335126, by rfl⟩ : syracuseStep 1787341 = 670253) (by norm_num)
theorem B5359061 : Blo 940584 5359061 := bbase (se 7 (by rfl) ⟨62801, by rfl⟩ : syracuseStep 5359061 = 125603) (by norm_num)
theorem B3261941 : Blo 940584 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B1132061 : Blo 940584 1132061 := bbase (se 3 (by rfl) ⟨212261, by rfl⟩ : syracuseStep 1132061 = 424523) (by norm_num)
theorem B1590853 : Blo 940584 1590853 := bbase (se 4 (by rfl) ⟨149142, by rfl⟩ : syracuseStep 1590853 = 298285) (by norm_num)
theorem B1787501 : Blo 940584 1787501 := bbase (se 3 (by rfl) ⟨335156, by rfl⟩ : syracuseStep 1787501 = 670313) (by norm_num)
theorem B2016893 : Blo 940584 2016893 := bbase (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) (by norm_num)
theorem B1590941 : Blo 940584 1590941 := bbase (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) (by norm_num)
theorem B1787645 : Blo 940584 1787645 := bbase (se 3 (by rfl) ⟨335183, by rfl⟩ : syracuseStep 1787645 = 670367) (by norm_num)
theorem B1591069 : Blo 940584 1591069 := bbase (se 3 (by rfl) ⟨298325, by rfl⟩ : syracuseStep 1591069 = 596651) (by norm_num)
theorem B1722197 : Blo 940584 1722197 := bbase (se 9 (by rfl) ⟨5045, by rfl⟩ : syracuseStep 1722197 = 10091) (by norm_num)
theorem B4835173 : Blo 940584 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B1591157 : Blo 940584 1591157 := bbase (se 5 (by rfl) ⟨74585, by rfl⟩ : syracuseStep 1591157 = 149171) (by norm_num)
theorem B4769765 : Blo 940584 4769765 := bbase (se 4 (by rfl) ⟨447165, by rfl⟩ : syracuseStep 4769765 = 894331) (by norm_num)
theorem B1591285 : Blo 940584 1591285 := bbase (se 5 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 1591285 = 149183) (by norm_num)
theorem B1787933 : Blo 940584 1787933 := bbase (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) (by norm_num)
theorem B3393589 : Blo 940584 3393589 := bbase (se 5 (by rfl) ⟨159074, by rfl⟩ : syracuseStep 3393589 = 318149) (by norm_num)
theorem B1591373 : Blo 940584 1591373 := bbase (se 3 (by rfl) ⟨298382, by rfl⟩ : syracuseStep 1591373 = 596765) (by norm_num)
theorem B1788085 : Blo 940584 1788085 := bbase (se 5 (by rfl) ⟨83816, by rfl⟩ : syracuseStep 1788085 = 167633) (by norm_num)
theorem B1591501 : Blo 940584 1591501 := bbase (se 3 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 1591501 = 596813) (by norm_num)
theorem B1591589 : Blo 940584 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B1132849 : Blo 940584 1132849 := bbase (se 2 (by rfl) ⟨424818, by rfl⟩ : syracuseStep 1132849 = 849637) (by norm_num)
theorem B1591717 : Blo 940584 1591717 := bbase (se 4 (by rfl) ⟨149223, by rfl⟩ : syracuseStep 1591717 = 298447) (by norm_num)
theorem B1788389 : Blo 940584 1788389 := bbase (se 4 (by rfl) ⟨167661, by rfl⟩ : syracuseStep 1788389 = 335323) (by norm_num)
theorem B3394037 : Blo 940584 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B1591805 : Blo 940584 1591805 := bbase (se 3 (by rfl) ⟨298463, by rfl⟩ : syracuseStep 1591805 = 596927) (by norm_num)
theorem B3394165 : Blo 940584 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B1591933 : Blo 940584 1591933 := bbase (se 3 (by rfl) ⟨298487, by rfl⟩ : syracuseStep 1591933 = 596975) (by norm_num)
theorem B1592021 : Blo 940584 1592021 := bbase (se 7 (by rfl) ⟨18656, by rfl⟩ : syracuseStep 1592021 = 37313) (by norm_num)
theorem B2116349 : Blo 940584 2116349 := bbase (se 3 (by rfl) ⟨396815, by rfl⟩ : syracuseStep 2116349 = 793631) (by norm_num)
theorem B2116421 : Blo 940584 2116421 := bbase (se 4 (by rfl) ⟨198414, by rfl⟩ : syracuseStep 2116421 = 396829) (by norm_num)
theorem B1592149 : Blo 940584 1592149 := bbase (se 9 (by rfl) ⟨4664, by rfl⟩ : syracuseStep 1592149 = 9329) (by norm_num)
theorem B2116493 : Blo 940584 2116493 := bbase (se 3 (by rfl) ⟨396842, by rfl⟩ : syracuseStep 2116493 = 793685) (by norm_num)
theorem B1592237 : Blo 940584 1592237 := bbase (se 3 (by rfl) ⟨298544, by rfl⟩ : syracuseStep 1592237 = 597089) (by norm_num)
theorem B2116565 : Blo 940584 2116565 := bbase (se 7 (by rfl) ⟨24803, by rfl⟩ : syracuseStep 2116565 = 49607) (by norm_num)
theorem B1133561 : Blo 940584 1133561 := bbase (se 2 (by rfl) ⟨425085, by rfl⟩ : syracuseStep 1133561 = 850171) (by norm_num)
theorem B2116637 : Blo 940584 2116637 := bbase (se 3 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 2116637 = 793739) (by norm_num)
theorem B1592365 : Blo 940584 1592365 := bbase (se 3 (by rfl) ⟨298568, by rfl⟩ : syracuseStep 1592365 = 597137) (by norm_num)
theorem B2116709 : Blo 940584 2116709 := bbase (se 4 (by rfl) ⟨198441, by rfl⟩ : syracuseStep 2116709 = 396883) (by norm_num)
theorem B969833 : Blo 940584 969833 := bbase (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) (by norm_num)
theorem B1592453 : Blo 940584 1592453 := bbase (se 4 (by rfl) ⟨149292, by rfl⟩ : syracuseStep 1592453 = 298585) (by norm_num)
theorem B2116781 : Blo 940584 2116781 := bbase (se 3 (by rfl) ⟨396896, by rfl⟩ : syracuseStep 2116781 = 793793) (by norm_num)
theorem B1789141 : Blo 940584 1789141 := bbase (se 7 (by rfl) ⟨20966, by rfl⟩ : syracuseStep 1789141 = 41933) (by norm_num)
theorem B2116853 : Blo 940584 2116853 := bbase (se 5 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 2116853 = 198455) (by norm_num)
theorem B4771061 : Blo 940584 4771061 := bbase (se 5 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 4771061 = 447287) (by norm_num)
theorem B1592581 : Blo 940584 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B2116925 : Blo 940584 2116925 := bbase (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) (by norm_num)
theorem B1133897 : Blo 940584 1133897 := bbase (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) (by norm_num)
theorem B1592669 : Blo 940584 1592669 := bbase (se 3 (by rfl) ⟨298625, by rfl⟩ : syracuseStep 1592669 = 597251) (by norm_num)
theorem B1789285 : Blo 940584 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B2149733 : Blo 940584 2149733 := bbase (se 4 (by rfl) ⟨201537, by rfl⟩ : syracuseStep 2149733 = 403075) (by norm_num)
theorem B2116997 : Blo 940584 2116997 := bbase (se 4 (by rfl) ⟨198468, by rfl⟩ : syracuseStep 2116997 = 396937) (by norm_num)
theorem B1134013 : Blo 940584 1134013 := bbase (se 3 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 1134013 = 425255) (by norm_num)
theorem B2117069 : Blo 940584 2117069 := bbase (se 3 (by rfl) ⟨396950, by rfl⟩ : syracuseStep 2117069 = 793901) (by norm_num)
theorem B1134037 : Blo 940584 1134037 := bbase (se 7 (by rfl) ⟨13289, by rfl⟩ : syracuseStep 1134037 = 26579) (by norm_num)
theorem B1592797 : Blo 940584 1592797 := bbase (se 3 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 1592797 = 597299) (by norm_num)
theorem B1789445 : Blo 940584 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B2117141 : Blo 940584 2117141 := bbase (se 6 (by rfl) ⟨49620, by rfl⟩ : syracuseStep 2117141 = 99241) (by norm_num)
theorem B1592885 : Blo 940584 1592885 := bbase (se 5 (by rfl) ⟨74666, by rfl⟩ : syracuseStep 1592885 = 149333) (by norm_num)
theorem B2117213 : Blo 940584 2117213 := bbase (se 3 (by rfl) ⟨396977, by rfl⟩ : syracuseStep 2117213 = 793955) (by norm_num)
theorem B10735253 : Blo 940584 10735253 := bbase (se 6 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 10735253 = 503215) (by norm_num)
theorem B1789589 : Blo 940584 1789589 := bbase (se 6 (by rfl) ⟨41943, by rfl⟩ : syracuseStep 1789589 = 83887) (by norm_num)
theorem B2117285 : Blo 940584 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B1593013 : Blo 940584 1593013 := bbase (se 5 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 1593013 = 149345) (by norm_num)
theorem B2117357 : Blo 940584 2117357 := bbase (se 3 (by rfl) ⟨397004, by rfl⟩ : syracuseStep 2117357 = 794009) (by norm_num)
theorem B1593101 : Blo 940584 1593101 := bbase (se 3 (by rfl) ⟨298706, by rfl⟩ : syracuseStep 1593101 = 597413) (by norm_num)
theorem B2117429 : Blo 940584 2117429 := bbase (se 5 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 2117429 = 198509) (by norm_num)
theorem B2117501 : Blo 940584 2117501 := bbase (se 3 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 2117501 = 794063) (by norm_num)
theorem B1593229 : Blo 940584 1593229 := bbase (se 3 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 1593229 = 597461) (by norm_num)
theorem B1789877 : Blo 940584 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B2117573 : Blo 940584 2117573 := bbase (se 4 (by rfl) ⟨198522, by rfl⟩ : syracuseStep 2117573 = 397045) (by norm_num)
theorem B1593317 : Blo 940584 1593317 := bbase (se 4 (by rfl) ⟨149373, by rfl⟩ : syracuseStep 1593317 = 298747) (by norm_num)
theorem B2117645 : Blo 940584 2117645 := bbase (se 3 (by rfl) ⟨397058, by rfl⟩ : syracuseStep 2117645 = 794117) (by norm_num)
theorem B1790029 : Blo 940584 1790029 := bbase (se 3 (by rfl) ⟨335630, by rfl⟩ : syracuseStep 1790029 = 671261) (by norm_num)
theorem B2117717 : Blo 940584 2117717 := bbase (se 8 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 2117717 = 24817) (by norm_num)
theorem B1593445 : Blo 940584 1593445 := bbase (se 4 (by rfl) ⟨149385, by rfl⟩ : syracuseStep 1593445 = 298771) (by norm_num)
theorem B1134733 : Blo 940584 1134733 := bbase (se 3 (by rfl) ⟨212762, by rfl⟩ : syracuseStep 1134733 = 425525) (by norm_num)
theorem B2117789 : Blo 940584 2117789 := bbase (se 3 (by rfl) ⟨397085, by rfl⟩ : syracuseStep 2117789 = 794171) (by norm_num)
theorem B1593533 : Blo 940584 1593533 := bbase (se 3 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 1593533 = 597575) (by norm_num)
theorem B2117861 : Blo 940584 2117861 := bbase (se 4 (by rfl) ⟨198549, by rfl⟩ : syracuseStep 2117861 = 397099) (by norm_num)
theorem B2117933 : Blo 940584 2117933 := bbase (se 3 (by rfl) ⟨397112, by rfl⟩ : syracuseStep 2117933 = 794225) (by norm_num)
theorem B1593661 : Blo 940584 1593661 := bbase (se 3 (by rfl) ⟨298811, by rfl⟩ : syracuseStep 1593661 = 597623) (by norm_num)
theorem B2118005 : Blo 940584 2118005 := bbase (se 5 (by rfl) ⟨99281, by rfl⟩ : syracuseStep 2118005 = 198563) (by norm_num)
theorem B1790333 : Blo 940584 1790333 := bbase (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) (by norm_num)
theorem B4837781 : Blo 940584 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B1593749 : Blo 940584 1593749 := bbase (se 6 (by rfl) ⟨37353, by rfl⟩ : syracuseStep 1593749 = 74707) (by norm_num)
theorem B3822005 : Blo 940584 3822005 := bbase (se 5 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 3822005 = 358313) (by norm_num)
theorem B2118077 : Blo 940584 2118077 := bbase (se 3 (by rfl) ⟨397139, by rfl⟩ : syracuseStep 2118077 = 794279) (by norm_num)
theorem B2118149 : Blo 940584 2118149 := bbase (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) (by norm_num)
theorem B4772357 : Blo 940584 4772357 := bbase (se 4 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 4772357 = 894817) (by norm_num)
theorem B1593877 : Blo 940584 1593877 := bbase (se 6 (by rfl) ⟨37356, by rfl⟩ : syracuseStep 1593877 = 74713) (by norm_num)
theorem B2118221 : Blo 940584 2118221 := bbase (se 3 (by rfl) ⟨397166, by rfl⟩ : syracuseStep 2118221 = 794333) (by norm_num)
theorem B1593965 : Blo 940584 1593965 := bbase (se 3 (by rfl) ⟨298868, by rfl⟩ : syracuseStep 1593965 = 597737) (by norm_num)
theorem B2118293 : Blo 940584 2118293 := bbase (se 6 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 2118293 = 99295) (by norm_num)
theorem B5100245 : Blo 940584 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B2118365 : Blo 940584 2118365 := bbase (se 3 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 2118365 = 794387) (by norm_num)
theorem B2118437 : Blo 940584 2118437 := bbase (se 4 (by rfl) ⟨198603, by rfl⟩ : syracuseStep 2118437 = 397207) (by norm_num)
theorem B2118509 : Blo 940584 2118509 := bbase (se 3 (by rfl) ⟨397220, by rfl⟩ : syracuseStep 2118509 = 794441) (by norm_num)
theorem B2118581 : Blo 940584 2118581 := bbase (se 5 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 2118581 = 198617) (by norm_num)
theorem B13095893 : Blo 940584 13095893 := bbase (se 7 (by rfl) ⟨153467, by rfl⟩ : syracuseStep 13095893 = 306935) (by norm_num)
theorem B2118653 : Blo 940584 2118653 := bbase (se 3 (by rfl) ⟨397247, by rfl⟩ : syracuseStep 2118653 = 794495) (by norm_num)
theorem B2118725 : Blo 940584 2118725 := bbase (se 4 (by rfl) ⟨198630, by rfl⟩ : syracuseStep 2118725 = 397261) (by norm_num)
theorem B1791085 : Blo 940584 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B2118797 : Blo 940584 2118797 := bbase (se 3 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 2118797 = 794549) (by norm_num)
theorem B2118869 : Blo 940584 2118869 := bbase (se 7 (by rfl) ⟨24830, by rfl⟩ : syracuseStep 2118869 = 49661) (by norm_num)
theorem B1004773 : Blo 940584 1004773 := bbase (se 4 (by rfl) ⟨94197, by rfl⟩ : syracuseStep 1004773 = 188395) (by norm_num)
theorem B1791229 : Blo 940584 1791229 := bbase (se 3 (by rfl) ⟨335855, by rfl⟩ : syracuseStep 1791229 = 671711) (by norm_num)
theorem B2118941 : Blo 940584 2118941 := bbase (se 3 (by rfl) ⟨397301, by rfl⟩ : syracuseStep 2118941 = 794603) (by norm_num)
theorem B1004833 : Blo 940584 1004833 := bbase (se 2 (by rfl) ⟨376812, by rfl⟩ : syracuseStep 1004833 = 753625) (by norm_num)
theorem B2119013 : Blo 940584 2119013 := bbase (se 4 (by rfl) ⟨198657, by rfl⟩ : syracuseStep 2119013 = 397315) (by norm_num)
theorem B7853429 : Blo 940584 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B2381197 : Blo 940584 2381197 := bbase (se 3 (by rfl) ⟨446474, by rfl⟩ : syracuseStep 2381197 = 892949) (by norm_num)
theorem B1791389 : Blo 940584 1791389 := bbase (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) (by norm_num)
theorem B2119085 : Blo 940584 2119085 := bbase (se 3 (by rfl) ⟨397328, by rfl⟩ : syracuseStep 2119085 = 794657) (by norm_num)
theorem B2119157 : Blo 940584 2119157 := bbase (se 5 (by rfl) ⟨99335, by rfl⟩ : syracuseStep 2119157 = 198671) (by norm_num)
theorem B2381309 : Blo 940584 2381309 := bbase (se 3 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 2381309 = 892991) (by norm_num)
theorem B3823109 : Blo 940584 3823109 := bbase (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) (by norm_num)
theorem B1791533 : Blo 940584 1791533 := bbase (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) (by norm_num)
theorem B2119229 : Blo 940584 2119229 := bbase (se 3 (by rfl) ⟨397355, by rfl⟩ : syracuseStep 2119229 = 794711) (by norm_num)
theorem B18142805 : Blo 940584 18142805 := bbase (se 8 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 18142805 = 212611) (by norm_num)
theorem B1005149 : Blo 940584 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B2119301 : Blo 940584 2119301 := bbase (se 4 (by rfl) ⟨198684, by rfl⟩ : syracuseStep 2119301 = 397369) (by norm_num)
theorem B2381501 : Blo 940584 2381501 := bbase (se 3 (by rfl) ⟨446531, by rfl⟩ : syracuseStep 2381501 = 893063) (by norm_num)
theorem B2119373 : Blo 940584 2119373 := bbase (se 3 (by rfl) ⟨397382, by rfl⟩ : syracuseStep 2119373 = 794765) (by norm_num)
theorem B2119445 : Blo 940584 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B4773653 : Blo 940584 4773653 := bbase (se 6 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 4773653 = 223765) (by norm_num)
theorem B2152213 : Blo 940584 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B1791821 : Blo 940584 1791821 := bbase (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) (by norm_num)
theorem B2119517 : Blo 940584 2119517 := bbase (se 3 (by rfl) ⟨397409, by rfl⟩ : syracuseStep 2119517 = 794819) (by norm_num)
theorem B4020101 : Blo 940584 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B2119589 : Blo 940584 2119589 := bbase (se 4 (by rfl) ⟨198711, by rfl⟩ : syracuseStep 2119589 = 397423) (by norm_num)
theorem B1791973 : Blo 940584 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B2119661 : Blo 940584 2119661 := bbase (se 3 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 2119661 = 794873) (by norm_num)
theorem B2381845 : Blo 940584 2381845 := bbase (se 6 (by rfl) ⟨55824, by rfl⟩ : syracuseStep 2381845 = 111649) (by norm_num)
theorem B2152469 : Blo 940584 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B1005593 : Blo 940584 1005593 := bbase (se 2 (by rfl) ⟨377097, by rfl⟩ : syracuseStep 1005593 = 754195) (by norm_num)
theorem B2119733 : Blo 940584 2119733 := bbase (se 5 (by rfl) ⟨99362, by rfl⟩ : syracuseStep 2119733 = 198725) (by norm_num)
theorem B1005653 : Blo 940584 1005653 := bbase (se 8 (by rfl) ⟨5892, by rfl⟩ : syracuseStep 1005653 = 11785) (by norm_num)
theorem B7166069 : Blo 940584 7166069 := bbase (se 5 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 7166069 = 671819) (by norm_num)
theorem B2119805 : Blo 940584 2119805 := bbase (se 3 (by rfl) ⟨397463, by rfl⟩ : syracuseStep 2119805 = 794927) (by norm_num)
theorem B2381957 : Blo 940584 2381957 := bbase (se 4 (by rfl) ⟨223308, by rfl⟩ : syracuseStep 2381957 = 446617) (by norm_num)
theorem B2119877 : Blo 940584 2119877 := bbase (se 4 (by rfl) ⟨198738, by rfl⟩ : syracuseStep 2119877 = 397477) (by norm_num)
theorem B1005781 : Blo 940584 1005781 := bbase (se 7 (by rfl) ⟨11786, by rfl⟩ : syracuseStep 1005781 = 23573) (by norm_num)
theorem B2119949 : Blo 940584 2119949 := bbase (se 3 (by rfl) ⟨397490, by rfl⟩ : syracuseStep 2119949 = 794981) (by norm_num)
theorem B1792277 : Blo 940584 1792277 := bbase (se 6 (by rfl) ⟨42006, by rfl⟩ : syracuseStep 1792277 = 84013) (by norm_num)
theorem B2382149 : Blo 940584 2382149 := bbase (se 4 (by rfl) ⟨223326, by rfl⟩ : syracuseStep 2382149 = 446653) (by norm_num)
theorem B2120021 : Blo 940584 2120021 := bbase (se 10 (by rfl) ⟨3105, by rfl⟩ : syracuseStep 2120021 = 6211) (by norm_num)
theorem B4905301 : Blo 940584 4905301 := bbase (se 10 (by rfl) ⟨7185, by rfl⟩ : syracuseStep 4905301 = 14371) (by norm_num)
theorem B2120093 : Blo 940584 2120093 := bbase (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) (by norm_num)
theorem B2120165 : Blo 940584 2120165 := bbase (se 4 (by rfl) ⟨198765, by rfl⟩ : syracuseStep 2120165 = 397531) (by norm_num)
theorem B2120237 : Blo 940584 2120237 := bbase (se 3 (by rfl) ⟨397544, by rfl⟩ : syracuseStep 2120237 = 795089) (by norm_num)
theorem B2120309 : Blo 940584 2120309 := bbase (se 5 (by rfl) ⟨99389, by rfl⟩ : syracuseStep 2120309 = 198779) (by norm_num)
theorem B1006225 : Blo 940584 1006225 := bbase (se 2 (by rfl) ⟨377334, by rfl⟩ : syracuseStep 1006225 = 754669) (by norm_num)
theorem B2382493 : Blo 940584 2382493 := bbase (se 3 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 2382493 = 893435) (by norm_num)
theorem B2120381 : Blo 940584 2120381 := bbase (se 3 (by rfl) ⟨397571, by rfl⟩ : syracuseStep 2120381 = 795143) (by norm_num)
theorem B3627733 : Blo 940584 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B2120453 : Blo 940584 2120453 := bbase (se 4 (by rfl) ⟨198792, by rfl⟩ : syracuseStep 2120453 = 397585) (by norm_num)
theorem B1006345 : Blo 940584 1006345 := bbase (se 2 (by rfl) ⟨377379, by rfl⟩ : syracuseStep 1006345 = 754759) (by norm_num)
theorem B2382605 : Blo 940584 2382605 := bbase (se 3 (by rfl) ⟨446738, by rfl⟩ : syracuseStep 2382605 = 893477) (by norm_num)
theorem B3824405 : Blo 940584 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B2120525 : Blo 940584 2120525 := bbase (se 3 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 2120525 = 795197) (by norm_num)
theorem B4021109 : Blo 940584 4021109 := bbase (se 5 (by rfl) ⟨188489, by rfl⟩ : syracuseStep 4021109 = 376979) (by norm_num)
theorem B2120597 : Blo 940584 2120597 := bbase (se 6 (by rfl) ⟨49701, by rfl⟩ : syracuseStep 2120597 = 99403) (by norm_num)
theorem B2382797 : Blo 940584 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B2120669 : Blo 940584 2120669 := bbase (se 3 (by rfl) ⟨397625, by rfl⟩ : syracuseStep 2120669 = 795251) (by norm_num)
theorem B1006597 : Blo 940584 1006597 := bbase (se 4 (by rfl) ⟨94368, by rfl⟩ : syracuseStep 1006597 = 188737) (by norm_num)
theorem B1793029 : Blo 940584 1793029 := bbase (se 4 (by rfl) ⟨168096, by rfl⟩ : syracuseStep 1793029 = 336193) (by norm_num)
theorem B1006601 : Blo 940584 1006601 := bbase (se 2 (by rfl) ⟨377475, by rfl⟩ : syracuseStep 1006601 = 754951) (by norm_num)
theorem B2120741 : Blo 940584 2120741 := bbase (se 4 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 2120741 = 397639) (by norm_num)
theorem B4774949 : Blo 940584 4774949 := bbase (se 4 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 4774949 = 895303) (by norm_num)
theorem B2120813 : Blo 940584 2120813 := bbase (se 3 (by rfl) ⟨397652, by rfl⟩ : syracuseStep 2120813 = 795305) (by norm_num)
theorem B1793173 : Blo 940584 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B1531037 : Blo 940584 1531037 := bbase (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) (by norm_num)
theorem B2415781 : Blo 940584 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B3267749 : Blo 940584 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B2120885 : Blo 940584 2120885 := bbase (se 5 (by rfl) ⟨99416, by rfl⟩ : syracuseStep 2120885 = 198833) (by norm_num)
theorem B2579653 : Blo 940584 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B2120957 : Blo 940584 2120957 := bbase (se 3 (by rfl) ⟨397679, by rfl⟩ : syracuseStep 2120957 = 795359) (by norm_num)
theorem B2383141 : Blo 940584 2383141 := bbase (se 4 (by rfl) ⟨223419, by rfl⟩ : syracuseStep 2383141 = 446839) (by norm_num)
theorem B2121029 : Blo 940584 2121029 := bbase (se 4 (by rfl) ⟨198846, by rfl⟩ : syracuseStep 2121029 = 397693) (by norm_num)
theorem B2121101 : Blo 940584 2121101 := bbase (se 3 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 2121101 = 795413) (by norm_num)
theorem B2383253 : Blo 940584 2383253 := bbase (se 6 (by rfl) ⟨55857, by rfl⟩ : syracuseStep 2383253 = 111715) (by norm_num)
theorem B1695173 : Blo 940584 1695173 := bbase (se 4 (by rfl) ⟨158922, by rfl⟩ : syracuseStep 1695173 = 317845) (by norm_num)
theorem B2121173 : Blo 940584 2121173 := bbase (se 7 (by rfl) ⟨24857, by rfl⟩ : syracuseStep 2121173 = 49715) (by norm_num)
theorem B9068021 : Blo 940584 9068021 := bbase (se 5 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 9068021 = 850127) (by norm_num)
theorem B2121245 : Blo 940584 2121245 := bbase (se 3 (by rfl) ⟨397733, by rfl⟩ : syracuseStep 2121245 = 795467) (by norm_num)
theorem B1007165 : Blo 940584 1007165 := bbase (se 3 (by rfl) ⟨188843, by rfl⟩ : syracuseStep 1007165 = 377687) (by norm_num)
theorem B2383445 : Blo 940584 2383445 := bbase (se 8 (by rfl) ⟨13965, by rfl⟩ : syracuseStep 2383445 = 27931) (by norm_num)
theorem B2121317 : Blo 940584 2121317 := bbase (se 4 (by rfl) ⟨198873, by rfl⟩ : syracuseStep 2121317 = 397747) (by norm_num)
theorem B3628709 : Blo 940584 3628709 := bbase (se 4 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 3628709 = 680383) (by norm_num)
theorem B2121389 : Blo 940584 2121389 := bbase (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) (by norm_num)
theorem B2121461 : Blo 940584 2121461 := bbase (se 5 (by rfl) ⟨99443, by rfl⟩ : syracuseStep 2121461 = 198887) (by norm_num)
theorem B1007353 : Blo 940584 1007353 := bbase (se 2 (by rfl) ⟨377757, by rfl⟩ : syracuseStep 1007353 = 755515) (by norm_num)
theorem B2154293 : Blo 940584 2154293 := bbase (se 5 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 2154293 = 201965) (by norm_num)
theorem B2121533 : Blo 940584 2121533 := bbase (se 3 (by rfl) ⟨397787, by rfl⟩ : syracuseStep 2121533 = 795575) (by norm_num)
theorem B2121605 : Blo 940584 2121605 := bbase (se 4 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 2121605 = 397801) (by norm_num)
theorem B2547605 : Blo 940584 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B2383789 : Blo 940584 2383789 := bbase (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) (by norm_num)
theorem B2121677 : Blo 940584 2121677 := bbase (se 3 (by rfl) ⟨397814, by rfl⟩ : syracuseStep 2121677 = 795629) (by norm_num)
theorem B1695757 : Blo 940584 1695757 := bbase (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) (by norm_num)
theorem B2121749 : Blo 940584 2121749 := bbase (se 6 (by rfl) ⟨49728, by rfl⟩ : syracuseStep 2121749 = 99457) (by norm_num)
theorem B2383901 : Blo 940584 2383901 := bbase (se 3 (by rfl) ⟨446981, by rfl⟩ : syracuseStep 2383901 = 893963) (by norm_num)
theorem B2121821 : Blo 940584 2121821 := bbase (se 3 (by rfl) ⟨397841, by rfl⟩ : syracuseStep 2121821 = 795683) (by norm_num)
theorem B5431445 : Blo 940584 5431445 := bbase (se 6 (by rfl) ⟨127299, by rfl⟩ : syracuseStep 5431445 = 254599) (by norm_num)
theorem B2121893 : Blo 940584 2121893 := bbase (se 4 (by rfl) ⟨198927, by rfl⟩ : syracuseStep 2121893 = 397855) (by norm_num)
theorem B2384093 : Blo 940584 2384093 := bbase (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) (by norm_num)
theorem B2121965 : Blo 940584 2121965 := bbase (se 3 (by rfl) ⟨397868, by rfl⟩ : syracuseStep 2121965 = 795737) (by norm_num)
theorem B5726485 : Blo 940584 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B1433909 : Blo 940584 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B2122037 : Blo 940584 2122037 := bbase (se 5 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 2122037 = 198941) (by norm_num)
theorem B4776245 : Blo 940584 4776245 := bbase (se 5 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 4776245 = 447773) (by norm_num)
theorem B2122109 : Blo 940584 2122109 := bbase (se 3 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 2122109 = 795791) (by norm_num)
theorem B2122181 : Blo 940584 2122181 := bbase (se 4 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 2122181 = 397909) (by norm_num)
theorem B2122253 : Blo 940584 2122253 := bbase (se 3 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 2122253 = 795845) (by norm_num)
theorem B1008173 : Blo 940584 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B2384437 : Blo 940584 2384437 := bbase (se 5 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 2384437 = 223541) (by norm_num)
theorem B2122325 : Blo 940584 2122325 := bbase (se 8 (by rfl) ⟨12435, by rfl⟩ : syracuseStep 2122325 = 24871) (by norm_num)
theorem B2482781 : Blo 940584 2482781 := bbase (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) (by norm_num)
theorem B4022885 : Blo 940584 4022885 := bbase (se 4 (by rfl) ⟨377145, by rfl⟩ : syracuseStep 4022885 = 754291) (by norm_num)
theorem B2122397 : Blo 940584 2122397 := bbase (se 3 (by rfl) ⟨397949, by rfl⟩ : syracuseStep 2122397 = 795899) (by norm_num)
theorem B2384549 : Blo 940584 2384549 := bbase (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) (by norm_num)
theorem B2122469 : Blo 940584 2122469 := bbase (se 4 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 2122469 = 397963) (by norm_num)
theorem B2417413 : Blo 940584 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B2122541 : Blo 940584 2122541 := bbase (se 3 (by rfl) ⟨397976, by rfl⟩ : syracuseStep 2122541 = 795953) (by norm_num)
theorem B6808373 : Blo 940584 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B2384741 : Blo 940584 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B2122613 : Blo 940584 2122613 := bbase (se 5 (by rfl) ⟨99497, by rfl⟩ : syracuseStep 2122613 = 198995) (by norm_num)
theorem B2122685 : Blo 940584 2122685 := bbase (se 3 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 2122685 = 796007) (by norm_num)
theorem B1008617 : Blo 940584 1008617 := bbase (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) (by norm_num)
theorem B2122757 : Blo 940584 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B2122829 : Blo 940584 2122829 := bbase (se 3 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 2122829 = 796061) (by norm_num)
theorem B2679941 : Blo 940584 2679941 := bbase (se 4 (by rfl) ⟨251244, by rfl⟩ : syracuseStep 2679941 = 502489) (by norm_num)
theorem B2122901 : Blo 940584 2122901 := bbase (se 6 (by rfl) ⟨49755, by rfl⟩ : syracuseStep 2122901 = 99511) (by norm_num)
theorem B1696925 : Blo 940584 1696925 := bbase (se 3 (by rfl) ⟨318173, by rfl⟩ : syracuseStep 1696925 = 636347) (by norm_num)
theorem B2385085 : Blo 940584 2385085 := bbase (se 3 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 2385085 = 894407) (by norm_num)
theorem B2122973 : Blo 940584 2122973 := bbase (se 3 (by rfl) ⟨398057, by rfl⟩ : syracuseStep 2122973 = 796115) (by norm_num)
theorem B2123045 : Blo 940584 2123045 := bbase (se 4 (by rfl) ⟨199035, by rfl⟩ : syracuseStep 2123045 = 398071) (by norm_num)
theorem B2385197 : Blo 940584 2385197 := bbase (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) (by norm_num)
theorem B30532949 : Blo 940584 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B2123117 : Blo 940584 2123117 := bbase (se 3 (by rfl) ⟨398084, by rfl⟩ : syracuseStep 2123117 = 796169) (by norm_num)
theorem B2418101 : Blo 940584 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B2123189 : Blo 940584 2123189 := bbase (se 5 (by rfl) ⟨99524, by rfl⟩ : syracuseStep 2123189 = 199049) (by norm_num)
theorem B3401189 : Blo 940584 3401189 := bbase (se 4 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 3401189 = 637723) (by norm_num)
theorem B2385389 : Blo 940584 2385389 := bbase (se 3 (by rfl) ⟨447260, by rfl⟩ : syracuseStep 2385389 = 894521) (by norm_num)
theorem B2123261 : Blo 940584 2123261 := bbase (se 3 (by rfl) ⟨398111, by rfl⟩ : syracuseStep 2123261 = 796223) (by norm_num)
theorem B2418245 : Blo 940584 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B2123333 : Blo 940584 2123333 := bbase (se 4 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 2123333 = 398125) (by norm_num)
theorem B4777541 : Blo 940584 4777541 := bbase (se 4 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 4777541 = 895789) (by norm_num)
theorem B1697365 : Blo 940584 1697365 := bbase (se 8 (by rfl) ⟨9945, by rfl⟩ : syracuseStep 1697365 = 19891) (by norm_num)
theorem B2123405 : Blo 940584 2123405 := bbase (se 3 (by rfl) ⟨398138, by rfl⟩ : syracuseStep 2123405 = 796277) (by norm_num)
theorem B1697429 : Blo 940584 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B2123477 : Blo 940584 2123477 := bbase (se 7 (by rfl) ⟨24884, by rfl⟩ : syracuseStep 2123477 = 49769) (by norm_num)
theorem B2123549 : Blo 940584 2123549 := bbase (se 3 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 2123549 = 796331) (by norm_num)
theorem B2385733 : Blo 940584 2385733 := bbase (se 4 (by rfl) ⟨223662, by rfl⟩ : syracuseStep 2385733 = 447325) (by norm_num)
theorem B2123621 : Blo 940584 2123621 := bbase (se 4 (by rfl) ⟨199089, by rfl⟩ : syracuseStep 2123621 = 398179) (by norm_num)
theorem B3401605 : Blo 940584 3401605 := bbase (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) (by norm_num)
theorem B2123693 : Blo 940584 2123693 := bbase (se 3 (by rfl) ⟨398192, by rfl⟩ : syracuseStep 2123693 = 796385) (by norm_num)
theorem B1697717 : Blo 940584 1697717 := bbase (se 5 (by rfl) ⟨79580, by rfl⟩ : syracuseStep 1697717 = 159161) (by norm_num)
theorem B2385845 : Blo 940584 2385845 := bbase (se 5 (by rfl) ⟨111836, by rfl⟩ : syracuseStep 2385845 = 223673) (by norm_num)
theorem B2123765 : Blo 940584 2123765 := bbase (se 5 (by rfl) ⟨99551, by rfl⟩ : syracuseStep 2123765 = 199103) (by norm_num)
theorem B2123837 : Blo 940584 2123837 := bbase (se 3 (by rfl) ⟨398219, by rfl⟩ : syracuseStep 2123837 = 796439) (by norm_num)
theorem B1435709 : Blo 940584 1435709 := bbase (se 3 (by rfl) ⟨269195, by rfl⟩ : syracuseStep 1435709 = 538391) (by norm_num)
theorem B1435757 : Blo 940584 1435757 := bbase (se 3 (by rfl) ⟨269204, by rfl⟩ : syracuseStep 1435757 = 538409) (by norm_num)
theorem B2386037 : Blo 940584 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B2123909 : Blo 940584 2123909 := bbase (se 4 (by rfl) ⟨199116, by rfl⟩ : syracuseStep 2123909 = 398233) (by norm_num)
theorem B2123981 : Blo 940584 2123981 := bbase (se 3 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 2123981 = 796493) (by norm_num)
theorem B2124053 : Blo 940584 2124053 := bbase (se 6 (by rfl) ⟨49782, by rfl⟩ : syracuseStep 2124053 = 99565) (by norm_num)
theorem B2124125 : Blo 940584 2124125 := bbase (se 3 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 2124125 = 796547) (by norm_num)
theorem B2124197 : Blo 940584 2124197 := bbase (se 4 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 2124197 = 398287) (by norm_num)
theorem B2386381 : Blo 940584 2386381 := bbase (se 3 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 2386381 = 894893) (by norm_num)
theorem B2124269 : Blo 940584 2124269 := bbase (se 3 (by rfl) ⟨398300, by rfl⟩ : syracuseStep 2124269 = 796601) (by norm_num)
theorem B2124341 : Blo 940584 2124341 := bbase (se 5 (by rfl) ⟨99578, by rfl⟩ : syracuseStep 2124341 = 199157) (by norm_num)
theorem B2386493 : Blo 940584 2386493 := bbase (se 3 (by rfl) ⟨447467, by rfl⟩ : syracuseStep 2386493 = 894935) (by norm_num)
theorem B2124413 : Blo 940584 2124413 := bbase (se 3 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 2124413 = 796655) (by norm_num)
theorem B1206925 : Blo 940584 1206925 := bbase (se 3 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 1206925 = 452597) (by norm_num)
theorem B2681525 : Blo 940584 2681525 := bbase (se 5 (by rfl) ⟨125696, by rfl⟩ : syracuseStep 2681525 = 251393) (by norm_num)
theorem B2124485 : Blo 940584 2124485 := bbase (se 4 (by rfl) ⟨199170, by rfl⟩ : syracuseStep 2124485 = 398341) (by norm_num)
theorem B2386685 : Blo 940584 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B2124557 : Blo 940584 2124557 := bbase (se 3 (by rfl) ⟨398354, by rfl⟩ : syracuseStep 2124557 = 796709) (by norm_num)
theorem B4778837 : Blo 940584 4778837 := bbase (se 9 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 4778837 = 28001) (by norm_num)
theorem B43608917 : Blo 940584 43608917 := bbase (se 9 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 43608917 = 255521) (by norm_num)
theorem B2124629 : Blo 940584 2124629 := bbase (se 9 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 2124629 = 12449) (by norm_num)
theorem B2124701 : Blo 940584 2124701 := bbase (se 3 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 2124701 = 796763) (by norm_num)
theorem B1698749 : Blo 940584 1698749 := bbase (se 3 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 1698749 = 637031) (by norm_num)
theorem B2124773 : Blo 940584 2124773 := bbase (se 4 (by rfl) ⟨199197, by rfl⟩ : syracuseStep 2124773 = 398395) (by norm_num)
theorem B2124845 : Blo 940584 2124845 := bbase (se 3 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 2124845 = 796817) (by norm_num)
theorem B2387029 : Blo 940584 2387029 := bbase (se 8 (by rfl) ⟨13986, by rfl⟩ : syracuseStep 2387029 = 27973) (by norm_num)
theorem B5368949 : Blo 940584 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B2124917 : Blo 940584 2124917 := bbase (se 5 (by rfl) ⟨99605, by rfl⟩ : syracuseStep 2124917 = 199211) (by norm_num)
theorem B2419885 : Blo 940584 2419885 := bbase (se 3 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 2419885 = 907457) (by norm_num)
theorem B2124989 : Blo 940584 2124989 := bbase (se 3 (by rfl) ⟨398435, by rfl⟩ : syracuseStep 2124989 = 796871) (by norm_num)
theorem B2387141 : Blo 940584 2387141 := bbase (se 4 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 2387141 = 447589) (by norm_num)
theorem B2125061 : Blo 940584 2125061 := bbase (se 4 (by rfl) ⟨199224, by rfl⟩ : syracuseStep 2125061 = 398449) (by norm_num)
theorem B2125133 : Blo 940584 2125133 := bbase (se 3 (by rfl) ⟨398462, by rfl⟩ : syracuseStep 2125133 = 796925) (by norm_num)
theorem B2682197 : Blo 940584 2682197 := bbase (se 11 (by rfl) ⟨1964, by rfl⟩ : syracuseStep 2682197 = 3929) (by norm_num)
theorem B2387333 : Blo 940584 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B2125205 : Blo 940584 2125205 := bbase (se 6 (by rfl) ⟨49809, by rfl⟩ : syracuseStep 2125205 = 99619) (by norm_num)
theorem B2125277 : Blo 940584 2125277 := bbase (se 3 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 2125277 = 796979) (by norm_num)
theorem B2387677 : Blo 940584 2387677 := bbase (se 3 (by rfl) ⟨447689, by rfl⟩ : syracuseStep 2387677 = 895379) (by norm_num)
theorem B2682629 : Blo 940584 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B2420533 : Blo 940584 2420533 := bbase (se 5 (by rfl) ⟨113462, by rfl⟩ : syracuseStep 2420533 = 226925) (by norm_num)
theorem B1208137 : Blo 940584 1208137 := bbase (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) (by norm_num)
theorem B2387789 : Blo 940584 2387789 := bbase (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) (by norm_num)
theorem B2551637 : Blo 940584 2551637 := bbase (se 9 (by rfl) ⟨7475, by rfl⟩ : syracuseStep 2551637 = 14951) (by norm_num)
theorem B2387981 : Blo 940584 2387981 := bbase (se 3 (by rfl) ⟨447746, by rfl⟩ : syracuseStep 2387981 = 895493) (by norm_num)
theorem B4780133 : Blo 940584 4780133 := bbase (se 4 (by rfl) ⟨448137, by rfl⟩ : syracuseStep 4780133 = 896275) (by norm_num)
theorem B1241285 : Blo 940584 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B1339669 : Blo 940584 1339669 := bbase (se 6 (by rfl) ⟨31398, by rfl⟩ : syracuseStep 1339669 = 62797) (by norm_num)
theorem B2388325 : Blo 940584 2388325 := bbase (se 4 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 2388325 = 447811) (by norm_num)
theorem B3174821 : Blo 940584 3174821 := bbase (se 4 (by rfl) ⟨297639, by rfl⟩ : syracuseStep 3174821 = 595279) (by norm_num)
theorem B2585029 : Blo 940584 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B2388437 : Blo 940584 2388437 := bbase (se 7 (by rfl) ⟨27989, by rfl⟩ : syracuseStep 2388437 = 55979) (by norm_num)
theorem B2683381 : Blo 940584 2683381 := bbase (se 5 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 2683381 = 251567) (by norm_num)
theorem B1340005 : Blo 940584 1340005 := bbase (se 4 (by rfl) ⟨125625, by rfl⟩ : syracuseStep 1340005 = 251251) (by norm_num)
theorem B1208953 : Blo 940584 1208953 := bbase (se 2 (by rfl) ⟨453357, by rfl⟩ : syracuseStep 1208953 = 906715) (by norm_num)
theorem B2388629 : Blo 940584 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B4027157 : Blo 940584 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B1340221 : Blo 940584 1340221 := bbase (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) (by norm_num)
theorem B3175253 : Blo 940584 3175253 := bbase (se 9 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 3175253 = 18605) (by norm_num)
theorem B1274845 : Blo 940584 1274845 := bbase (se 3 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 1274845 = 478067) (by norm_num)
theorem B2388973 : Blo 940584 2388973 := bbase (se 3 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 2388973 = 895865) (by norm_num)
theorem B2389085 : Blo 940584 2389085 := bbase (se 3 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 2389085 = 895907) (by norm_num)
theorem B4846709 : Blo 940584 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B1340597 : Blo 940584 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B3175685 : Blo 940584 3175685 := bbase (se 4 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 3175685 = 595441) (by norm_num)
theorem B2389277 : Blo 940584 2389277 := bbase (se 3 (by rfl) ⟨447989, by rfl⟩ : syracuseStep 2389277 = 895979) (by norm_num)
theorem B4781429 : Blo 940584 4781429 := bbase (se 5 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 4781429 = 448259) (by norm_num)
theorem B5174837 : Blo 940584 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B2389621 : Blo 940584 2389621 := bbase (se 5 (by rfl) ⟨112013, by rfl⟩ : syracuseStep 2389621 = 224027) (by norm_num)
theorem B2291381 : Blo 940584 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B3176117 : Blo 940584 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B1242805 : Blo 940584 1242805 := bbase (se 5 (by rfl) ⟨58256, by rfl⟩ : syracuseStep 1242805 = 116513) (by norm_num)
theorem B2389733 : Blo 940584 2389733 := bbase (se 4 (by rfl) ⟨224037, by rfl⟩ : syracuseStep 2389733 = 448075) (by norm_num)
theorem B1701653 : Blo 940584 1701653 := bbase (se 6 (by rfl) ⟨39882, by rfl⟩ : syracuseStep 1701653 = 79765) (by norm_num)
theorem B2422669 : Blo 940584 2422669 := bbase (se 3 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 2422669 = 908501) (by norm_num)
theorem B2389925 : Blo 940584 2389925 := bbase (se 4 (by rfl) ⟨224055, by rfl⟩ : syracuseStep 2389925 = 448111) (by norm_num)
theorem B1701805 : Blo 940584 1701805 := bbase (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) (by norm_num)
theorem B3176549 : Blo 940584 3176549 := bbase (se 4 (by rfl) ⟨297801, by rfl⟩ : syracuseStep 3176549 = 595603) (by norm_num)
theorem B7633109 : Blo 940584 7633109 := bbase (se 7 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 7633109 = 178901) (by norm_num)
theorem B6027509 : Blo 940584 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B2423029 : Blo 940584 2423029 := bbase (se 5 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 2423029 = 227159) (by norm_num)
theorem B2390269 : Blo 940584 2390269 := bbase (se 3 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 2390269 = 896351) (by norm_num)
theorem B1210693 : Blo 940584 1210693 := bbase (se 4 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 1210693 = 227005) (by norm_num)
theorem B2390381 : Blo 940584 2390381 := bbase (se 3 (by rfl) ⟨448196, by rfl⟩ : syracuseStep 2390381 = 896393) (by norm_num)
theorem B4028933 : Blo 940584 4028933 := bbase (se 4 (by rfl) ⟨377712, by rfl⟩ : syracuseStep 4028933 = 755425) (by norm_num)
theorem B3176981 : Blo 940584 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B1276445 : Blo 940584 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B2390573 : Blo 940584 2390573 := bbase (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) (by norm_num)
theorem B1342021 : Blo 940584 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B12057173 : Blo 940584 12057173 := bbase (se 8 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 12057173 = 141295) (by norm_num)
theorem B8583893 : Blo 940584 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B4029173 : Blo 940584 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B4193045 : Blo 940584 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B2390917 : Blo 940584 2390917 := bbase (se 4 (by rfl) ⟨224148, by rfl⟩ : syracuseStep 2390917 = 448297) (by norm_num)
theorem B3177413 : Blo 940584 3177413 := bbase (se 4 (by rfl) ⟨297882, by rfl⟩ : syracuseStep 3177413 = 595765) (by norm_num)
theorem B1342613 : Blo 940584 1342613 := bbase (se 6 (by rfl) ⟨31467, by rfl⟩ : syracuseStep 1342613 = 62935) (by norm_num)
theorem B1342693 : Blo 940584 1342693 := bbase (se 4 (by rfl) ⟨125877, by rfl⟩ : syracuseStep 1342693 = 251755) (by norm_num)
theorem B2686229 : Blo 940584 2686229 := bbase (se 6 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 2686229 = 125917) (by norm_num)
theorem B7142741 : Blo 940584 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B1342813 : Blo 940584 1342813 := bbase (se 3 (by rfl) ⟨251777, by rfl⟩ : syracuseStep 1342813 = 503555) (by norm_num)
theorem B3177845 : Blo 940584 3177845 := bbase (se 5 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 3177845 = 297923) (by norm_num)
theorem B1342909 : Blo 940584 1342909 := bbase (se 3 (by rfl) ⟨251795, by rfl⟩ : syracuseStep 1342909 = 503591) (by norm_num)
theorem B3014165 : Blo 940584 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B3178277 : Blo 940584 3178277 := bbase (se 4 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 3178277 = 595927) (by norm_num)
theorem B1343405 : Blo 940584 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B2261009 : Blo 940584 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B5505221 : Blo 940584 5505221 := bstep (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) B1032229
theorem B2687185 : Blo 940584 2687185 := bstep (se 2 (by rfl) ⟨1007694, by rfl⟩ : syracuseStep 2687185 = 2015389) B2015389
theorem B7635313 : Blo 940584 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B5374349 : Blo 940584 5374349 := bstep (se 3 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 5374349 = 2015381) B2015381
theorem B3178925 : Blo 940584 3178925 := bstep (se 3 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 3178925 = 1192097) B1192097
theorem B6029765 : Blo 940584 6029765 := bstep (se 4 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 6029765 = 1130581) B1130581
theorem B5439941 : Blo 940584 5439941 := bstep (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) B1019989
theorem B3015139 : Blo 940584 3015139 := bstep (se 1 (by rfl) ⟨2261354, by rfl⟩ : syracuseStep 3015139 = 4522709) B4522709
theorem B3178979 : Blo 940584 3178979 := bstep (se 1 (by rfl) ⟨2384234, by rfl⟩ : syracuseStep 3178979 = 4768469) B4768469
theorem B3310093 : Blo 940584 3310093 := bstep (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) B1241285
theorem B3015281 : Blo 940584 3015281 := bstep (se 2 (by rfl) ⟨1130730, by rfl⟩ : syracuseStep 3015281 = 2261461) B2261461
theorem B1508051 : Blo 940584 1508051 := bstep (se 1 (by rfl) ⟨1131038, by rfl⟩ : syracuseStep 1508051 = 2262077) B2262077
theorem B3015395 : Blo 940584 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B3179249 : Blo 940584 3179249 := bstep (se 2 (by rfl) ⟨1192218, by rfl⟩ : syracuseStep 3179249 = 2384437) B2384437
theorem B12256069 : Blo 940584 12256069 := bstep (se 4 (by rfl) ⟨1149006, by rfl⟩ : syracuseStep 12256069 = 2298013) B2298013
theorem B6128453 : Blo 940584 6128453 := bstep (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) B1149085
theorem B4031309 : Blo 940584 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B3572707 : Blo 940584 3572707 := bstep (se 1 (by rfl) ⟨2679530, by rfl⟩ : syracuseStep 3572707 = 5359061) B5359061
theorem B4522979 : Blo 940584 4522979 := bstep (se 1 (by rfl) ⟨3392234, by rfl⟩ : syracuseStep 4522979 = 6784469) B6784469
theorem B1344595 : Blo 940584 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B3867761 : Blo 940584 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B10192013 : Blo 940584 10192013 := bstep (se 3 (by rfl) ⟨1911002, by rfl⟩ : syracuseStep 10192013 = 3822005) B3822005
theorem B1148131 : Blo 940584 1148131 := bstep (se 1 (by rfl) ⟨861098, by rfl⟩ : syracuseStep 1148131 = 1722197) B1722197
theorem B3179789 : Blo 940584 3179789 := bstep (se 3 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 3179789 = 1192421) B1192421
theorem B5375281 : Blo 940584 5375281 := bstep (se 2 (by rfl) ⟨2015730, by rfl⟩ : syracuseStep 5375281 = 4031461) B4031461
theorem B3179843 : Blo 940584 3179843 := bstep (se 1 (by rfl) ⟨2384882, by rfl⟩ : syracuseStep 3179843 = 4769765) B4769765
theorem B1508723 : Blo 940584 1508723 := bstep (se 1 (by rfl) ⟨1131542, by rfl⟩ : syracuseStep 1508723 = 2263085) B2263085
theorem B2688461 : Blo 940584 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B3180113 : Blo 940584 3180113 := bstep (se 2 (by rfl) ⟨1192542, by rfl⟩ : syracuseStep 3180113 = 2385085) B2385085
theorem B4523633 : Blo 940584 4523633 := bstep (se 2 (by rfl) ⟨1696362, by rfl⟩ : syracuseStep 4523633 = 3392725) B3392725
theorem B2688643 : Blo 940584 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B1509025 : Blo 940584 1509025 := bstep (se 2 (by rfl) ⟨565884, by rfl⟩ : syracuseStep 1509025 = 1131769) B1131769
theorem B2262691 : Blo 940584 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B3016369 : Blo 940584 3016369 := bstep (se 2 (by rfl) ⟨1131138, by rfl⟩ : syracuseStep 3016369 = 2262277) B2262277
theorem B2688689 : Blo 940584 2688689 := bstep (se 2 (by rfl) ⟨1008258, by rfl⟩ : syracuseStep 2688689 = 2016517) B2016517
theorem B1410881 : Blo 940584 1410881 := bstep (se 2 (by rfl) ⟨529080, by rfl⟩ : syracuseStep 1410881 = 1058161) B1058161
theorem B1410899 : Blo 940584 1410899 := bstep (se 1 (by rfl) ⟨1058174, by rfl⟩ : syracuseStep 1410899 = 2116349) B2116349
theorem B1410929 : Blo 940584 1410929 := bstep (se 2 (by rfl) ⟨529098, by rfl⟩ : syracuseStep 1410929 = 1058197) B1058197
theorem B1509235 : Blo 940584 1509235 := bstep (se 1 (by rfl) ⟨1131926, by rfl⟩ : syracuseStep 1509235 = 2263853) B2263853
theorem B1410947 : Blo 940584 1410947 := bstep (se 1 (by rfl) ⟨1058210, by rfl⟩ : syracuseStep 1410947 = 2116421) B2116421
theorem B1410977 : Blo 940584 1410977 := bstep (se 2 (by rfl) ⟨529116, by rfl⟩ : syracuseStep 1410977 = 1058233) B1058233
theorem B1509281 : Blo 940584 1509281 := bstep (se 2 (by rfl) ⟨565980, by rfl⟩ : syracuseStep 1509281 = 1131961) B1131961
theorem B1410995 : Blo 940584 1410995 := bstep (se 1 (by rfl) ⟨1058246, by rfl⟩ : syracuseStep 1410995 = 2116493) B2116493
theorem B1411025 : Blo 940584 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B1411043 : Blo 940584 1411043 := bstep (se 1 (by rfl) ⟨1058282, by rfl⟩ : syracuseStep 1411043 = 2116565) B2116565
theorem B1411073 : Blo 940584 1411073 := bstep (se 2 (by rfl) ⟨529152, by rfl⟩ : syracuseStep 1411073 = 1058305) B1058305
theorem B1411091 : Blo 940584 1411091 := bstep (se 1 (by rfl) ⟨1058318, by rfl⟩ : syracuseStep 1411091 = 2116637) B2116637
theorem B1411121 : Blo 940584 1411121 := bstep (se 2 (by rfl) ⟨529170, by rfl⟩ : syracuseStep 1411121 = 1058341) B1058341
theorem B1411139 : Blo 940584 1411139 := bstep (se 1 (by rfl) ⟨1058354, by rfl⟩ : syracuseStep 1411139 = 2116709) B2116709
theorem B1411169 : Blo 940584 1411169 := bstep (se 2 (by rfl) ⟨529188, by rfl⟩ : syracuseStep 1411169 = 1058377) B1058377
theorem B3180653 : Blo 940584 3180653 := bstep (se 3 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 3180653 = 1192745) B1192745
theorem B2263153 : Blo 940584 2263153 := bstep (se 2 (by rfl) ⟨848682, by rfl⟩ : syracuseStep 2263153 = 1697365) B1697365
theorem B1411187 : Blo 940584 1411187 := bstep (se 1 (by rfl) ⟨1058390, by rfl⟩ : syracuseStep 1411187 = 2116781) B2116781
theorem B1411217 : Blo 940584 1411217 := bstep (se 2 (by rfl) ⟨529206, by rfl⟩ : syracuseStep 1411217 = 1058413) B1058413
theorem B1411235 : Blo 940584 1411235 := bstep (se 1 (by rfl) ⟨1058426, by rfl⟩ : syracuseStep 1411235 = 2116853) B2116853
theorem B3180707 : Blo 940584 3180707 := bstep (se 1 (by rfl) ⟨2385530, by rfl⟩ : syracuseStep 3180707 = 4771061) B4771061
theorem B1411265 : Blo 940584 1411265 := bstep (se 2 (by rfl) ⟨529224, by rfl⟩ : syracuseStep 1411265 = 1058449) B1058449
theorem B1411283 : Blo 940584 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B1411313 : Blo 940584 1411313 := bstep (se 2 (by rfl) ⟨529242, by rfl⟩ : syracuseStep 1411313 = 1058485) B1058485
theorem B1411331 : Blo 940584 1411331 := bstep (se 1 (by rfl) ⟨1058498, by rfl⟩ : syracuseStep 1411331 = 2116997) B2116997
theorem B1411361 : Blo 940584 1411361 := bstep (se 2 (by rfl) ⟨529260, by rfl⟩ : syracuseStep 1411361 = 1058521) B1058521
theorem B1411379 : Blo 940584 1411379 := bstep (se 1 (by rfl) ⟨1058534, by rfl⟩ : syracuseStep 1411379 = 2117069) B2117069
theorem B1411409 : Blo 940584 1411409 := bstep (se 2 (by rfl) ⟨529278, by rfl⟩ : syracuseStep 1411409 = 1058557) B1058557
theorem B1411427 : Blo 940584 1411427 := bstep (se 1 (by rfl) ⟨1058570, by rfl⟩ : syracuseStep 1411427 = 2117141) B2117141
theorem B1411457 : Blo 940584 1411457 := bstep (se 2 (by rfl) ⟨529296, by rfl⟩ : syracuseStep 1411457 = 1058593) B1058593
theorem B1411475 : Blo 940584 1411475 := bstep (se 1 (by rfl) ⟨1058606, by rfl⟩ : syracuseStep 1411475 = 2117213) B2117213
theorem B1411505 : Blo 940584 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B3180977 : Blo 940584 3180977 := bstep (se 2 (by rfl) ⟨1192866, by rfl⟩ : syracuseStep 3180977 = 2385733) B2385733
theorem B1411523 : Blo 940584 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B61049285 : Blo 940584 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B1411553 : Blo 940584 1411553 := bstep (se 2 (by rfl) ⟨529332, by rfl⟩ : syracuseStep 1411553 = 1058665) B1058665
theorem B12061169 : Blo 940584 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B1411571 : Blo 940584 1411571 := bstep (se 1 (by rfl) ⟨1058678, by rfl⟩ : syracuseStep 1411571 = 2117357) B2117357
theorem B1411601 : Blo 940584 1411601 := bstep (se 2 (by rfl) ⟨529350, by rfl⟩ : syracuseStep 1411601 = 1058701) B1058701
theorem B1411619 : Blo 940584 1411619 := bstep (se 1 (by rfl) ⟨1058714, by rfl⟩ : syracuseStep 1411619 = 2117429) B2117429
theorem B1411649 : Blo 940584 1411649 := bstep (se 2 (by rfl) ⟨529368, by rfl⟩ : syracuseStep 1411649 = 1058737) B1058737
theorem B1411667 : Blo 940584 1411667 := bstep (se 1 (by rfl) ⟨1058750, by rfl⟩ : syracuseStep 1411667 = 2117501) B2117501
theorem B1411697 : Blo 940584 1411697 := bstep (se 2 (by rfl) ⟨529386, by rfl⟩ : syracuseStep 1411697 = 1058773) B1058773
theorem B1411715 : Blo 940584 1411715 := bstep (se 1 (by rfl) ⟨1058786, by rfl⟩ : syracuseStep 1411715 = 2117573) B2117573
theorem B1411745 : Blo 940584 1411745 := bstep (se 2 (by rfl) ⟨529404, by rfl⟩ : syracuseStep 1411745 = 1058809) B1058809
theorem B1411763 : Blo 940584 1411763 := bstep (se 1 (by rfl) ⟨1058822, by rfl⟩ : syracuseStep 1411763 = 2117645) B2117645
theorem B1411793 : Blo 940584 1411793 := bstep (se 2 (by rfl) ⟨529422, by rfl⟩ : syracuseStep 1411793 = 1058845) B1058845
theorem B1411811 : Blo 940584 1411811 := bstep (se 1 (by rfl) ⟨1058858, by rfl⟩ : syracuseStep 1411811 = 2117717) B2117717
theorem B5376739 : Blo 940584 5376739 := bstep (se 1 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 5376739 = 8065109) B8065109
theorem B4524785 : Blo 940584 4524785 := bstep (se 2 (by rfl) ⟨1696794, by rfl⟩ : syracuseStep 4524785 = 3393589) B3393589
theorem B1411841 : Blo 940584 1411841 := bstep (se 2 (by rfl) ⟨529440, by rfl⟩ : syracuseStep 1411841 = 1058881) B1058881
theorem B1411859 : Blo 940584 1411859 := bstep (se 1 (by rfl) ⟨1058894, by rfl⟩ : syracuseStep 1411859 = 2117789) B2117789
theorem B1411889 : Blo 940584 1411889 := bstep (se 2 (by rfl) ⟨529458, by rfl⟩ : syracuseStep 1411889 = 1058917) B1058917
theorem B1411907 : Blo 940584 1411907 := bstep (se 1 (by rfl) ⟨1058930, by rfl⟩ : syracuseStep 1411907 = 2117861) B2117861
theorem B1411937 : Blo 940584 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B2362211 : Blo 940584 2362211 := bstep (se 1 (by rfl) ⟨1771658, by rfl⟩ : syracuseStep 2362211 = 3543317) B3543317
theorem B1411955 : Blo 940584 1411955 := bstep (se 1 (by rfl) ⟨1058966, by rfl⟩ : syracuseStep 1411955 = 2117933) B2117933
theorem B1411985 : Blo 940584 1411985 := bstep (se 2 (by rfl) ⟨529494, by rfl⟩ : syracuseStep 1411985 = 1058989) B1058989
theorem B1412003 : Blo 940584 1412003 := bstep (se 1 (by rfl) ⟨1059002, by rfl⟩ : syracuseStep 1412003 = 2118005) B2118005
theorem B1412033 : Blo 940584 1412033 := bstep (se 2 (by rfl) ⟨529512, by rfl⟩ : syracuseStep 1412033 = 1059025) B1059025
theorem B3181517 : Blo 940584 3181517 := bstep (se 3 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 3181517 = 1193069) B1193069
theorem B1412051 : Blo 940584 1412051 := bstep (se 1 (by rfl) ⟨1059038, by rfl⟩ : syracuseStep 1412051 = 2118077) B2118077
theorem B1412081 : Blo 940584 1412081 := bstep (se 2 (by rfl) ⟨529530, by rfl⟩ : syracuseStep 1412081 = 1059061) B1059061
theorem B1412099 : Blo 940584 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B3181571 : Blo 940584 3181571 := bstep (se 1 (by rfl) ⟨2386178, by rfl⟩ : syracuseStep 3181571 = 4772357) B4772357
theorem B1412129 : Blo 940584 1412129 := bstep (se 2 (by rfl) ⟨529548, by rfl⟩ : syracuseStep 1412129 = 1059097) B1059097
theorem B1412147 : Blo 940584 1412147 := bstep (se 1 (by rfl) ⟨1059110, by rfl⟩ : syracuseStep 1412147 = 2118221) B2118221
theorem B1412177 : Blo 940584 1412177 := bstep (se 2 (by rfl) ⟨529566, by rfl⟩ : syracuseStep 1412177 = 1059133) B1059133
theorem B1412195 : Blo 940584 1412195 := bstep (se 1 (by rfl) ⟨1059146, by rfl⟩ : syracuseStep 1412195 = 2118293) B2118293
theorem B1412225 : Blo 940584 1412225 := bstep (se 2 (by rfl) ⟨529584, by rfl⟩ : syracuseStep 1412225 = 1059169) B1059169
theorem B3574925 : Blo 940584 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B1412243 : Blo 940584 1412243 := bstep (se 1 (by rfl) ⟨1059182, by rfl⟩ : syracuseStep 1412243 = 2118365) B2118365
theorem B1412273 : Blo 940584 1412273 := bstep (se 2 (by rfl) ⟨529602, by rfl⟩ : syracuseStep 1412273 = 1059205) B1059205
theorem B1412291 : Blo 940584 1412291 := bstep (se 1 (by rfl) ⟨1059218, by rfl⟩ : syracuseStep 1412291 = 2118437) B2118437
theorem B1412321 : Blo 940584 1412321 := bstep (se 2 (by rfl) ⟨529620, by rfl⟩ : syracuseStep 1412321 = 1059241) B1059241
theorem B5377265 : Blo 940584 5377265 := bstep (se 2 (by rfl) ⟨2016474, by rfl⟩ : syracuseStep 5377265 = 4032949) B4032949
theorem B1412339 : Blo 940584 1412339 := bstep (se 1 (by rfl) ⟨1059254, by rfl⟩ : syracuseStep 1412339 = 2118509) B2118509
theorem B1412369 : Blo 940584 1412369 := bstep (se 2 (by rfl) ⟨529638, by rfl⟩ : syracuseStep 1412369 = 1059277) B1059277
theorem B3181841 : Blo 940584 3181841 := bstep (se 2 (by rfl) ⟨1193190, by rfl⟩ : syracuseStep 3181841 = 2386381) B2386381
theorem B1412387 : Blo 940584 1412387 := bstep (se 1 (by rfl) ⟨1059290, by rfl⟩ : syracuseStep 1412387 = 2118581) B2118581
theorem B1412417 : Blo 940584 1412417 := bstep (se 2 (by rfl) ⟨529656, by rfl⟩ : syracuseStep 1412417 = 1059313) B1059313
theorem B1412435 : Blo 940584 1412435 := bstep (se 1 (by rfl) ⟨1059326, by rfl⟩ : syracuseStep 1412435 = 2118653) B2118653
theorem B1412465 : Blo 940584 1412465 := bstep (se 2 (by rfl) ⟨529674, by rfl⟩ : syracuseStep 1412465 = 1059349) B1059349
theorem B1412483 : Blo 940584 1412483 := bstep (se 1 (by rfl) ⟨1059362, by rfl⟩ : syracuseStep 1412483 = 2118725) B2118725
theorem B1510787 : Blo 940584 1510787 := bstep (se 1 (by rfl) ⟨1133090, by rfl⟩ : syracuseStep 1510787 = 2266181) B2266181
theorem B1412513 : Blo 940584 1412513 := bstep (se 2 (by rfl) ⟨529692, by rfl⟩ : syracuseStep 1412513 = 1059385) B1059385
theorem B1412531 : Blo 940584 1412531 := bstep (se 1 (by rfl) ⟨1059398, by rfl⟩ : syracuseStep 1412531 = 2118797) B2118797
theorem B1412561 : Blo 940584 1412561 := bstep (se 2 (by rfl) ⟨529710, by rfl⟩ : syracuseStep 1412561 = 1059421) B1059421
theorem B1412579 : Blo 940584 1412579 := bstep (se 1 (by rfl) ⟨1059434, by rfl⟩ : syracuseStep 1412579 = 2118869) B2118869
theorem B4525553 : Blo 940584 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B1412609 : Blo 940584 1412609 := bstep (se 2 (by rfl) ⟨529728, by rfl⟩ : syracuseStep 1412609 = 1059457) B1059457
theorem B1412627 : Blo 940584 1412627 := bstep (se 1 (by rfl) ⟨1059470, by rfl⟩ : syracuseStep 1412627 = 2118941) B2118941
theorem B1412657 : Blo 940584 1412657 := bstep (se 2 (by rfl) ⟨529746, by rfl⟩ : syracuseStep 1412657 = 1059493) B1059493
theorem B1412675 : Blo 940584 1412675 := bstep (se 1 (by rfl) ⟨1059506, by rfl⟩ : syracuseStep 1412675 = 2119013) B2119013
theorem B1412705 : Blo 940584 1412705 := bstep (se 2 (by rfl) ⟨529764, by rfl⟩ : syracuseStep 1412705 = 1059529) B1059529
theorem B1412723 : Blo 940584 1412723 := bstep (se 1 (by rfl) ⟨1059542, by rfl⟩ : syracuseStep 1412723 = 2119085) B2119085
theorem B1412753 : Blo 940584 1412753 := bstep (se 2 (by rfl) ⟨529782, by rfl⟩ : syracuseStep 1412753 = 1059565) B1059565
theorem B1412771 : Blo 940584 1412771 := bstep (se 1 (by rfl) ⟨1059578, by rfl⟩ : syracuseStep 1412771 = 2119157) B2119157
theorem B1511075 : Blo 940584 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B1412801 : Blo 940584 1412801 := bstep (se 2 (by rfl) ⟨529800, by rfl⟩ : syracuseStep 1412801 = 1059601) B1059601
theorem B1412819 : Blo 940584 1412819 := bstep (se 1 (by rfl) ⟨1059614, by rfl⟩ : syracuseStep 1412819 = 2119229) B2119229
theorem B12095203 : Blo 940584 12095203 := bstep (se 1 (by rfl) ⟨9071402, by rfl⟩ : syracuseStep 12095203 = 18142805) B18142805
theorem B1412849 : Blo 940584 1412849 := bstep (se 2 (by rfl) ⟨529818, by rfl⟩ : syracuseStep 1412849 = 1059637) B1059637
theorem B1412867 : Blo 940584 1412867 := bstep (se 1 (by rfl) ⟨1059650, by rfl⟩ : syracuseStep 1412867 = 2119301) B2119301
theorem B1412897 : Blo 940584 1412897 := bstep (se 2 (by rfl) ⟨529836, by rfl⟩ : syracuseStep 1412897 = 1059673) B1059673
theorem B3182381 : Blo 940584 3182381 := bstep (se 3 (by rfl) ⟨596696, by rfl⟩ : syracuseStep 3182381 = 1193393) B1193393
theorem B1412915 : Blo 940584 1412915 := bstep (se 1 (by rfl) ⟨1059686, by rfl⟩ : syracuseStep 1412915 = 2119373) B2119373
theorem B1412945 : Blo 940584 1412945 := bstep (se 2 (by rfl) ⟨529854, by rfl⟩ : syracuseStep 1412945 = 1059709) B1059709
theorem B1412963 : Blo 940584 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B3182435 : Blo 940584 3182435 := bstep (se 1 (by rfl) ⟨2386826, by rfl⟩ : syracuseStep 3182435 = 4773653) B4773653
theorem B1412993 : Blo 940584 1412993 := bstep (se 2 (by rfl) ⟨529872, by rfl⟩ : syracuseStep 1412993 = 1059745) B1059745
theorem B1413011 : Blo 940584 1413011 := bstep (se 1 (by rfl) ⟨1059758, by rfl⟩ : syracuseStep 1413011 = 2119517) B2119517
theorem B1413041 : Blo 940584 1413041 := bstep (se 2 (by rfl) ⟨529890, by rfl⟩ : syracuseStep 1413041 = 1059781) B1059781
theorem B1413059 : Blo 940584 1413059 := bstep (se 1 (by rfl) ⟨1059794, by rfl⟩ : syracuseStep 1413059 = 2119589) B2119589
theorem B1413089 : Blo 940584 1413089 := bstep (se 2 (by rfl) ⟨529908, by rfl⟩ : syracuseStep 1413089 = 1059817) B1059817
theorem B1413107 : Blo 940584 1413107 := bstep (se 1 (by rfl) ⟨1059830, by rfl⟩ : syracuseStep 1413107 = 2119661) B2119661
theorem B1413137 : Blo 940584 1413137 := bstep (se 2 (by rfl) ⟨529926, by rfl⟩ : syracuseStep 1413137 = 1059853) B1059853
theorem B1413155 : Blo 940584 1413155 := bstep (se 1 (by rfl) ⟨1059866, by rfl⟩ : syracuseStep 1413155 = 2119733) B2119733
theorem B1413185 : Blo 940584 1413185 := bstep (se 2 (by rfl) ⟨529944, by rfl⟩ : syracuseStep 1413185 = 1059889) B1059889
theorem B1413203 : Blo 940584 1413203 := bstep (se 1 (by rfl) ⟨1059902, by rfl⟩ : syracuseStep 1413203 = 2119805) B2119805
theorem B1413233 : Blo 940584 1413233 := bstep (se 2 (by rfl) ⟨529962, by rfl⟩ : syracuseStep 1413233 = 1059925) B1059925
theorem B3182705 : Blo 940584 3182705 := bstep (se 2 (by rfl) ⟨1193514, by rfl⟩ : syracuseStep 3182705 = 2387029) B2387029
theorem B1413251 : Blo 940584 1413251 := bstep (se 1 (by rfl) ⟨1059938, by rfl⟩ : syracuseStep 1413251 = 2119877) B2119877
theorem B1413281 : Blo 940584 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B1413299 : Blo 940584 1413299 := bstep (se 1 (by rfl) ⟨1059974, by rfl⟩ : syracuseStep 1413299 = 2119949) B2119949
theorem B1413329 : Blo 940584 1413329 := bstep (se 2 (by rfl) ⟨529998, by rfl⟩ : syracuseStep 1413329 = 1059997) B1059997
theorem B1413347 : Blo 940584 1413347 := bstep (se 1 (by rfl) ⟨1060010, by rfl⟩ : syracuseStep 1413347 = 2120021) B2120021
theorem B1413377 : Blo 940584 1413377 := bstep (se 2 (by rfl) ⟨530016, by rfl⟩ : syracuseStep 1413377 = 1060033) B1060033
theorem B1413395 : Blo 940584 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B1413425 : Blo 940584 1413425 := bstep (se 2 (by rfl) ⟨530034, by rfl⟩ : syracuseStep 1413425 = 1060069) B1060069
theorem B1413443 : Blo 940584 1413443 := bstep (se 1 (by rfl) ⟨1060082, by rfl⟩ : syracuseStep 1413443 = 2120165) B2120165
theorem B1413473 : Blo 940584 1413473 := bstep (se 2 (by rfl) ⟨530052, by rfl⟩ : syracuseStep 1413473 = 1060105) B1060105
theorem B1413491 : Blo 940584 1413491 := bstep (se 1 (by rfl) ⟨1060118, by rfl⟩ : syracuseStep 1413491 = 2120237) B2120237
theorem B1413521 : Blo 940584 1413521 := bstep (se 2 (by rfl) ⟨530070, by rfl⟩ : syracuseStep 1413521 = 1060141) B1060141
theorem B1413539 : Blo 940584 1413539 := bstep (se 1 (by rfl) ⟨1060154, by rfl⟩ : syracuseStep 1413539 = 2120309) B2120309
theorem B1413569 : Blo 940584 1413569 := bstep (se 2 (by rfl) ⟨530088, by rfl⟩ : syracuseStep 1413569 = 1060177) B1060177
theorem B1511875 : Blo 940584 1511875 := bstep (se 1 (by rfl) ⟨1133906, by rfl⟩ : syracuseStep 1511875 = 2267813) B2267813
theorem B1413587 : Blo 940584 1413587 := bstep (se 1 (by rfl) ⟨1060190, by rfl⟩ : syracuseStep 1413587 = 2120381) B2120381
theorem B1413617 : Blo 940584 1413617 := bstep (se 2 (by rfl) ⟨530106, by rfl⟩ : syracuseStep 1413617 = 1060213) B1060213
theorem B1413635 : Blo 940584 1413635 := bstep (se 1 (by rfl) ⟨1060226, by rfl⟩ : syracuseStep 1413635 = 2120453) B2120453
theorem B1413665 : Blo 940584 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B1413683 : Blo 940584 1413683 := bstep (se 1 (by rfl) ⟨1060262, by rfl⟩ : syracuseStep 1413683 = 2120525) B2120525
theorem B1413713 : Blo 940584 1413713 := bstep (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) B1060285
theorem B1512017 : Blo 940584 1512017 := bstep (se 2 (by rfl) ⟨567006, by rfl⟩ : syracuseStep 1512017 = 1134013) B1134013
theorem B1413731 : Blo 940584 1413731 := bstep (se 1 (by rfl) ⟨1060298, by rfl⟩ : syracuseStep 1413731 = 2120597) B2120597
theorem B1512049 : Blo 940584 1512049 := bstep (se 2 (by rfl) ⟨567018, by rfl⟩ : syracuseStep 1512049 = 1134037) B1134037
theorem B1413761 : Blo 940584 1413761 := bstep (se 2 (by rfl) ⟨530160, by rfl⟩ : syracuseStep 1413761 = 1060321) B1060321
theorem B3183245 : Blo 940584 3183245 := bstep (se 3 (by rfl) ⟨596858, by rfl⟩ : syracuseStep 3183245 = 1193717) B1193717
theorem B1413779 : Blo 940584 1413779 := bstep (se 1 (by rfl) ⟨1060334, by rfl⟩ : syracuseStep 1413779 = 2120669) B2120669
theorem B5378723 : Blo 940584 5378723 := bstep (se 1 (by rfl) ⟨4034042, by rfl⟩ : syracuseStep 5378723 = 8068085) B8068085
theorem B1413809 : Blo 940584 1413809 := bstep (se 2 (by rfl) ⟨530178, by rfl⟩ : syracuseStep 1413809 = 1060357) B1060357
theorem B1413827 : Blo 940584 1413827 := bstep (se 1 (by rfl) ⟨1060370, by rfl⟩ : syracuseStep 1413827 = 2120741) B2120741
theorem B3183299 : Blo 940584 3183299 := bstep (se 1 (by rfl) ⟨2387474, by rfl⟩ : syracuseStep 3183299 = 4774949) B4774949
theorem B4297421 : Blo 940584 4297421 := bstep (se 3 (by rfl) ⟨805766, by rfl⟩ : syracuseStep 4297421 = 1611533) B1611533
theorem B1413857 : Blo 940584 1413857 := bstep (se 2 (by rfl) ⟨530196, by rfl⟩ : syracuseStep 1413857 = 1060393) B1060393
theorem B2757361 : Blo 940584 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B1413875 : Blo 940584 1413875 := bstep (se 1 (by rfl) ⟨1060406, by rfl⟩ : syracuseStep 1413875 = 2120813) B2120813
theorem B1413905 : Blo 940584 1413905 := bstep (se 2 (by rfl) ⟨530214, by rfl⟩ : syracuseStep 1413905 = 1060429) B1060429
theorem B1020691 : Blo 940584 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B1413923 : Blo 940584 1413923 := bstep (se 1 (by rfl) ⟨1060442, by rfl⟩ : syracuseStep 1413923 = 2120885) B2120885
theorem B1413953 : Blo 940584 1413953 := bstep (se 2 (by rfl) ⟨530232, by rfl⟩ : syracuseStep 1413953 = 1060465) B1060465
theorem B1413971 : Blo 940584 1413971 := bstep (se 1 (by rfl) ⟨1060478, by rfl⟩ : syracuseStep 1413971 = 2120957) B2120957
theorem B1414001 : Blo 940584 1414001 := bstep (se 2 (by rfl) ⟨530250, by rfl⟩ : syracuseStep 1414001 = 1060501) B1060501
theorem B1414019 : Blo 940584 1414019 := bstep (se 1 (by rfl) ⟨1060514, by rfl⟩ : syracuseStep 1414019 = 2121029) B2121029
theorem B1414049 : Blo 940584 1414049 := bstep (se 2 (by rfl) ⟨530268, by rfl⟩ : syracuseStep 1414049 = 1060537) B1060537
theorem B1414067 : Blo 940584 1414067 := bstep (se 1 (by rfl) ⟨1060550, by rfl⟩ : syracuseStep 1414067 = 2121101) B2121101
theorem B1414097 : Blo 940584 1414097 := bstep (se 2 (by rfl) ⟨530286, by rfl⟩ : syracuseStep 1414097 = 1060573) B1060573
theorem B3183569 : Blo 940584 3183569 := bstep (se 2 (by rfl) ⟨1193838, by rfl⟩ : syracuseStep 3183569 = 2387677) B2387677
theorem B1414115 : Blo 940584 1414115 := bstep (se 1 (by rfl) ⟨1060586, by rfl⟩ : syracuseStep 1414115 = 2121173) B2121173
theorem B1414145 : Blo 940584 1414145 := bstep (se 2 (by rfl) ⟨530304, by rfl⟩ : syracuseStep 1414145 = 1060609) B1060609
theorem B1414163 : Blo 940584 1414163 := bstep (se 1 (by rfl) ⟨1060622, by rfl⟩ : syracuseStep 1414163 = 2121245) B2121245
theorem B1414193 : Blo 940584 1414193 := bstep (se 2 (by rfl) ⟨530322, by rfl⟩ : syracuseStep 1414193 = 1060645) B1060645
theorem B1414211 : Blo 940584 1414211 := bstep (se 1 (by rfl) ⟨1060658, by rfl⟩ : syracuseStep 1414211 = 2121317) B2121317
theorem B1610849 : Blo 940584 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B1414241 : Blo 940584 1414241 := bstep (se 2 (by rfl) ⟨530340, by rfl⟩ : syracuseStep 1414241 = 1060681) B1060681
theorem B1414259 : Blo 940584 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B4527245 : Blo 940584 4527245 := bstep (se 3 (by rfl) ⟨848858, by rfl⟩ : syracuseStep 4527245 = 1697717) B1697717
theorem B1414289 : Blo 940584 1414289 := bstep (se 2 (by rfl) ⟨530358, by rfl⟩ : syracuseStep 1414289 = 1060717) B1060717
theorem B1414307 : Blo 940584 1414307 := bstep (se 1 (by rfl) ⟨1060730, by rfl⟩ : syracuseStep 1414307 = 2121461) B2121461
theorem B1414337 : Blo 940584 1414337 := bstep (se 2 (by rfl) ⟨530376, by rfl⟩ : syracuseStep 1414337 = 1060753) B1060753
theorem B1414355 : Blo 940584 1414355 := bstep (se 1 (by rfl) ⟨1060766, by rfl⟩ : syracuseStep 1414355 = 2121533) B2121533
theorem B1414385 : Blo 940584 1414385 := bstep (se 2 (by rfl) ⟨530394, by rfl⟩ : syracuseStep 1414385 = 1060789) B1060789
theorem B1414403 : Blo 940584 1414403 := bstep (se 1 (by rfl) ⟨1060802, by rfl⟩ : syracuseStep 1414403 = 2121605) B2121605
theorem B1414433 : Blo 940584 1414433 := bstep (se 2 (by rfl) ⟨530412, by rfl⟩ : syracuseStep 1414433 = 1060825) B1060825
theorem B1414451 : Blo 940584 1414451 := bstep (se 1 (by rfl) ⟨1060838, by rfl⟩ : syracuseStep 1414451 = 2121677) B2121677
theorem B1414481 : Blo 940584 1414481 := bstep (se 2 (by rfl) ⟨530430, by rfl⟩ : syracuseStep 1414481 = 1060861) B1060861
theorem B1414499 : Blo 940584 1414499 := bstep (se 1 (by rfl) ⟨1060874, by rfl⟩ : syracuseStep 1414499 = 2121749) B2121749
theorem B1414529 : Blo 940584 1414529 := bstep (se 2 (by rfl) ⟨530448, by rfl⟩ : syracuseStep 1414529 = 1060897) B1060897
theorem B1414547 : Blo 940584 1414547 := bstep (se 1 (by rfl) ⟨1060910, by rfl⟩ : syracuseStep 1414547 = 2121821) B2121821
theorem B1414577 : Blo 940584 1414577 := bstep (se 2 (by rfl) ⟨530466, by rfl⟩ : syracuseStep 1414577 = 1060933) B1060933
theorem B1414595 : Blo 940584 1414595 := bstep (se 1 (by rfl) ⟨1060946, by rfl⟩ : syracuseStep 1414595 = 2121893) B2121893
theorem B1414625 : Blo 940584 1414625 := bstep (se 2 (by rfl) ⟨530484, by rfl⟩ : syracuseStep 1414625 = 1060969) B1060969
theorem B3184109 : Blo 940584 3184109 := bstep (se 3 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 3184109 = 1194041) B1194041
theorem B1414643 : Blo 940584 1414643 := bstep (se 1 (by rfl) ⟨1060982, by rfl⟩ : syracuseStep 1414643 = 2121965) B2121965
theorem B1414673 : Blo 940584 1414673 := bstep (se 2 (by rfl) ⟨530502, by rfl⟩ : syracuseStep 1414673 = 1061005) B1061005
theorem B1512977 : Blo 940584 1512977 := bstep (se 2 (by rfl) ⟨567366, by rfl⟩ : syracuseStep 1512977 = 1134733) B1134733
theorem B1414691 : Blo 940584 1414691 := bstep (se 1 (by rfl) ⟨1061018, by rfl⟩ : syracuseStep 1414691 = 2122037) B2122037
theorem B3184163 : Blo 940584 3184163 := bstep (se 1 (by rfl) ⟨2388122, by rfl⟩ : syracuseStep 3184163 = 4776245) B4776245
theorem B1414721 : Blo 940584 1414721 := bstep (se 2 (by rfl) ⟨530520, by rfl⟩ : syracuseStep 1414721 = 1061041) B1061041
theorem B1414739 : Blo 940584 1414739 := bstep (se 1 (by rfl) ⟨1061054, by rfl⟩ : syracuseStep 1414739 = 2122109) B2122109
theorem B1414769 : Blo 940584 1414769 := bstep (se 2 (by rfl) ⟨530538, by rfl⟩ : syracuseStep 1414769 = 1061077) B1061077
theorem B1414787 : Blo 940584 1414787 := bstep (se 1 (by rfl) ⟨1061090, by rfl⟩ : syracuseStep 1414787 = 2122181) B2122181
theorem B1414817 : Blo 940584 1414817 := bstep (se 2 (by rfl) ⟨530556, by rfl⟩ : syracuseStep 1414817 = 1061113) B1061113
theorem B1414835 : Blo 940584 1414835 := bstep (se 1 (by rfl) ⟨1061126, by rfl⟩ : syracuseStep 1414835 = 2122253) B2122253
theorem B1414865 : Blo 940584 1414865 := bstep (se 2 (by rfl) ⟨530574, by rfl⟩ : syracuseStep 1414865 = 1061149) B1061149
theorem B1414883 : Blo 940584 1414883 := bstep (se 1 (by rfl) ⟨1061162, by rfl⟩ : syracuseStep 1414883 = 2122325) B2122325
theorem B1414913 : Blo 940584 1414913 := bstep (se 2 (by rfl) ⟨530592, by rfl⟩ : syracuseStep 1414913 = 1061185) B1061185
theorem B1414931 : Blo 940584 1414931 := bstep (se 1 (by rfl) ⟨1061198, by rfl⟩ : syracuseStep 1414931 = 2122397) B2122397
theorem B45913877 : Blo 940584 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B1414961 : Blo 940584 1414961 := bstep (se 2 (by rfl) ⟨530610, by rfl⟩ : syracuseStep 1414961 = 1061221) B1061221
theorem B3184433 : Blo 940584 3184433 := bstep (se 2 (by rfl) ⟨1194162, by rfl⟩ : syracuseStep 3184433 = 2388325) B2388325
theorem B1414979 : Blo 940584 1414979 := bstep (se 1 (by rfl) ⟨1061234, by rfl⟩ : syracuseStep 1414979 = 2122469) B2122469
theorem B1415009 : Blo 940584 1415009 := bstep (se 2 (by rfl) ⟨530628, by rfl⟩ : syracuseStep 1415009 = 1061257) B1061257
theorem B1415027 : Blo 940584 1415027 := bstep (se 1 (by rfl) ⟨1061270, by rfl⟩ : syracuseStep 1415027 = 2122541) B2122541
theorem B1415057 : Blo 940584 1415057 := bstep (se 2 (by rfl) ⟨530646, by rfl⟩ : syracuseStep 1415057 = 1061293) B1061293
theorem B1415075 : Blo 940584 1415075 := bstep (se 1 (by rfl) ⟨1061306, by rfl⟩ : syracuseStep 1415075 = 2122613) B2122613
theorem B3446705 : Blo 940584 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B1415105 : Blo 940584 1415105 := bstep (se 2 (by rfl) ⟨530664, by rfl⟩ : syracuseStep 1415105 = 1061329) B1061329
theorem B3020753 : Blo 940584 3020753 := bstep (se 2 (by rfl) ⟨1132782, by rfl⟩ : syracuseStep 3020753 = 2265565) B2265565
theorem B1415123 : Blo 940584 1415123 := bstep (se 1 (by rfl) ⟨1061342, by rfl⟩ : syracuseStep 1415123 = 2122685) B2122685
theorem B3577841 : Blo 940584 3577841 := bstep (se 2 (by rfl) ⟨1341690, by rfl⟩ : syracuseStep 3577841 = 2683381) B2683381
theorem B1415153 : Blo 940584 1415153 := bstep (se 2 (by rfl) ⟨530682, by rfl⟩ : syracuseStep 1415153 = 1061365) B1061365
theorem B1415171 : Blo 940584 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B1415201 : Blo 940584 1415201 := bstep (se 2 (by rfl) ⟨530700, by rfl⟩ : syracuseStep 1415201 = 1061401) B1061401
theorem B1415219 : Blo 940584 1415219 := bstep (se 1 (by rfl) ⟨1061414, by rfl⟩ : syracuseStep 1415219 = 2122829) B2122829
theorem B1415249 : Blo 940584 1415249 := bstep (se 2 (by rfl) ⟨530718, by rfl⟩ : syracuseStep 1415249 = 1061437) B1061437
theorem B1415267 : Blo 940584 1415267 := bstep (se 1 (by rfl) ⟨1061450, by rfl⟩ : syracuseStep 1415267 = 2122901) B2122901
theorem B2300003 : Blo 940584 2300003 := bstep (se 1 (by rfl) ⟨1725002, by rfl⟩ : syracuseStep 2300003 = 3450005) B3450005
theorem B1415297 : Blo 940584 1415297 := bstep (se 2 (by rfl) ⟨530736, by rfl⟩ : syracuseStep 1415297 = 1061473) B1061473
theorem B1415315 : Blo 940584 1415315 := bstep (se 1 (by rfl) ⟨1061486, by rfl⟩ : syracuseStep 1415315 = 2122973) B2122973
theorem B1611937 : Blo 940584 1611937 := bstep (se 2 (by rfl) ⟨604476, by rfl⟩ : syracuseStep 1611937 = 1208953) B1208953
theorem B1415345 : Blo 940584 1415345 := bstep (se 2 (by rfl) ⟨530754, by rfl⟩ : syracuseStep 1415345 = 1061509) B1061509
theorem B1415363 : Blo 940584 1415363 := bstep (se 1 (by rfl) ⟨1061522, by rfl⟩ : syracuseStep 1415363 = 2123045) B2123045
theorem B1415393 : Blo 940584 1415393 := bstep (se 2 (by rfl) ⟨530772, by rfl⟩ : syracuseStep 1415393 = 1061545) B1061545
theorem B20355299 : Blo 940584 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B1415411 : Blo 940584 1415411 := bstep (se 1 (by rfl) ⟨1061558, by rfl⟩ : syracuseStep 1415411 = 2123117) B2123117
theorem B1415441 : Blo 940584 1415441 := bstep (se 2 (by rfl) ⟨530790, by rfl⟩ : syracuseStep 1415441 = 1061581) B1061581
theorem B1612067 : Blo 940584 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B1415459 : Blo 940584 1415459 := bstep (se 1 (by rfl) ⟨1061594, by rfl⟩ : syracuseStep 1415459 = 2123189) B2123189
theorem B26482997 : Blo 940584 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B1415489 : Blo 940584 1415489 := bstep (se 2 (by rfl) ⟨530808, by rfl⟩ : syracuseStep 1415489 = 1061617) B1061617
theorem B2267459 : Blo 940584 2267459 := bstep (se 1 (by rfl) ⟨1700594, by rfl⟩ : syracuseStep 2267459 = 3401189) B3401189
theorem B3184973 : Blo 940584 3184973 := bstep (se 3 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 3184973 = 1194365) B1194365
theorem B1415507 : Blo 940584 1415507 := bstep (se 1 (by rfl) ⟨1061630, by rfl⟩ : syracuseStep 1415507 = 2123261) B2123261
theorem B1415537 : Blo 940584 1415537 := bstep (se 2 (by rfl) ⟨530826, by rfl⟩ : syracuseStep 1415537 = 1061653) B1061653
theorem B1612163 : Blo 940584 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B1415555 : Blo 940584 1415555 := bstep (se 1 (by rfl) ⟨1061666, by rfl⟩ : syracuseStep 1415555 = 2123333) B2123333
theorem B3185027 : Blo 940584 3185027 := bstep (se 1 (by rfl) ⟨2388770, by rfl⟩ : syracuseStep 3185027 = 4777541) B4777541
theorem B1415585 : Blo 940584 1415585 := bstep (se 2 (by rfl) ⟨530844, by rfl⟩ : syracuseStep 1415585 = 1061689) B1061689
theorem B1415603 : Blo 940584 1415603 := bstep (se 1 (by rfl) ⟨1061702, by rfl⟩ : syracuseStep 1415603 = 2123405) B2123405
theorem B4135373 : Blo 940584 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B1415633 : Blo 940584 1415633 := bstep (se 2 (by rfl) ⟨530862, by rfl⟩ : syracuseStep 1415633 = 1061725) B1061725
theorem B1415651 : Blo 940584 1415651 := bstep (se 1 (by rfl) ⟨1061738, by rfl⟩ : syracuseStep 1415651 = 2123477) B2123477
theorem B1415681 : Blo 940584 1415681 := bstep (se 2 (by rfl) ⟨530880, by rfl⟩ : syracuseStep 1415681 = 1061761) B1061761
theorem B1415699 : Blo 940584 1415699 := bstep (se 1 (by rfl) ⟨1061774, by rfl⟩ : syracuseStep 1415699 = 2123549) B2123549
theorem B1415729 : Blo 940584 1415729 := bstep (se 2 (by rfl) ⟨530898, by rfl⟩ : syracuseStep 1415729 = 1061797) B1061797
theorem B1415747 : Blo 940584 1415747 := bstep (se 1 (by rfl) ⟨1061810, by rfl⟩ : syracuseStep 1415747 = 2123621) B2123621
theorem B1415777 : Blo 940584 1415777 := bstep (se 2 (by rfl) ⟨530916, by rfl⟩ : syracuseStep 1415777 = 1061833) B1061833
theorem B1415795 : Blo 940584 1415795 := bstep (se 1 (by rfl) ⟨1061846, by rfl⟩ : syracuseStep 1415795 = 2123693) B2123693
theorem B3185297 : Blo 940584 3185297 := bstep (se 2 (by rfl) ⟨1194486, by rfl⟩ : syracuseStep 3185297 = 2388973) B2388973
theorem B1415825 : Blo 940584 1415825 := bstep (se 2 (by rfl) ⟨530934, by rfl⟩ : syracuseStep 1415825 = 1061869) B1061869
theorem B1415843 : Blo 940584 1415843 := bstep (se 1 (by rfl) ⟨1061882, by rfl⟩ : syracuseStep 1415843 = 2123765) B2123765
theorem B1415873 : Blo 940584 1415873 := bstep (se 2 (by rfl) ⟨530952, by rfl⟩ : syracuseStep 1415873 = 1061905) B1061905
theorem B1415891 : Blo 940584 1415891 := bstep (se 1 (by rfl) ⟨1061918, by rfl⟩ : syracuseStep 1415891 = 2123837) B2123837
theorem B957139 : Blo 940584 957139 := bstep (se 1 (by rfl) ⟨717854, by rfl⟩ : syracuseStep 957139 = 1435709) B1435709
theorem B1415921 : Blo 940584 1415921 := bstep (se 2 (by rfl) ⟨530970, by rfl⟩ : syracuseStep 1415921 = 1061941) B1061941
theorem B1415939 : Blo 940584 1415939 := bstep (se 1 (by rfl) ⟨1061954, by rfl⟩ : syracuseStep 1415939 = 2123909) B2123909
theorem B1415969 : Blo 940584 1415969 := bstep (se 2 (by rfl) ⟨530988, by rfl⟩ : syracuseStep 1415969 = 1061977) B1061977
theorem B1415987 : Blo 940584 1415987 := bstep (se 1 (by rfl) ⟨1061990, by rfl⟩ : syracuseStep 1415987 = 2123981) B2123981
theorem B1416017 : Blo 940584 1416017 := bstep (se 2 (by rfl) ⟨531006, by rfl⟩ : syracuseStep 1416017 = 1062013) B1062013
theorem B1416035 : Blo 940584 1416035 := bstep (se 1 (by rfl) ⟨1062026, by rfl⟩ : syracuseStep 1416035 = 2124053) B2124053
theorem B1416065 : Blo 940584 1416065 := bstep (se 2 (by rfl) ⟨531024, by rfl⟩ : syracuseStep 1416065 = 1062049) B1062049
theorem B1416083 : Blo 940584 1416083 := bstep (se 1 (by rfl) ⟨1062062, by rfl⟩ : syracuseStep 1416083 = 2124125) B2124125
theorem B1416113 : Blo 940584 1416113 := bstep (se 2 (by rfl) ⟨531042, by rfl⟩ : syracuseStep 1416113 = 1062085) B1062085
theorem B1416131 : Blo 940584 1416131 := bstep (se 1 (by rfl) ⟨1062098, by rfl⟩ : syracuseStep 1416131 = 2124197) B2124197
theorem B1416161 : Blo 940584 1416161 := bstep (se 2 (by rfl) ⟨531060, by rfl⟩ : syracuseStep 1416161 = 1062121) B1062121
theorem B1416179 : Blo 940584 1416179 := bstep (se 1 (by rfl) ⟨1062134, by rfl⟩ : syracuseStep 1416179 = 2124269) B2124269
theorem B1416209 : Blo 940584 1416209 := bstep (se 2 (by rfl) ⟨531078, by rfl⟩ : syracuseStep 1416209 = 1062157) B1062157
theorem B1416227 : Blo 940584 1416227 := bstep (se 1 (by rfl) ⟨1062170, by rfl⟩ : syracuseStep 1416227 = 2124341) B2124341
theorem B1416257 : Blo 940584 1416257 := bstep (se 2 (by rfl) ⟨531096, by rfl⟩ : syracuseStep 1416257 = 1062193) B1062193
theorem B1416275 : Blo 940584 1416275 := bstep (se 1 (by rfl) ⟨1062206, by rfl⟩ : syracuseStep 1416275 = 2124413) B2124413
theorem B1416305 : Blo 940584 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B1416323 : Blo 940584 1416323 := bstep (se 1 (by rfl) ⟨1062242, by rfl⟩ : syracuseStep 1416323 = 2124485) B2124485
theorem B1416353 : Blo 940584 1416353 := bstep (se 2 (by rfl) ⟨531132, by rfl⟩ : syracuseStep 1416353 = 1062265) B1062265
theorem B3185837 : Blo 940584 3185837 := bstep (se 3 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 3185837 = 1194689) B1194689
theorem B1416371 : Blo 940584 1416371 := bstep (se 1 (by rfl) ⟨1062278, by rfl⟩ : syracuseStep 1416371 = 2124557) B2124557
theorem B1416401 : Blo 940584 1416401 := bstep (se 2 (by rfl) ⟨531150, by rfl⟩ : syracuseStep 1416401 = 1062301) B1062301
theorem B3185891 : Blo 940584 3185891 := bstep (se 1 (by rfl) ⟨2389418, by rfl⟩ : syracuseStep 3185891 = 4778837) B4778837
theorem B29072611 : Blo 940584 29072611 := bstep (se 1 (by rfl) ⟨21804458, by rfl⟩ : syracuseStep 29072611 = 43608917) B43608917
theorem B1416419 : Blo 940584 1416419 := bstep (se 1 (by rfl) ⟨1062314, by rfl⟩ : syracuseStep 1416419 = 2124629) B2124629
theorem B1416449 : Blo 940584 1416449 := bstep (se 2 (by rfl) ⟨531168, by rfl⟩ : syracuseStep 1416449 = 1062337) B1062337
theorem B1416467 : Blo 940584 1416467 := bstep (se 1 (by rfl) ⟨1062350, by rfl⟩ : syracuseStep 1416467 = 2124701) B2124701
theorem B1416497 : Blo 940584 1416497 := bstep (se 2 (by rfl) ⟨531186, by rfl⟩ : syracuseStep 1416497 = 1062373) B1062373
theorem B1416515 : Blo 940584 1416515 := bstep (se 1 (by rfl) ⟨1062386, by rfl⟩ : syracuseStep 1416515 = 2124773) B2124773
theorem B1416545 : Blo 940584 1416545 := bstep (se 2 (by rfl) ⟨531204, by rfl⟩ : syracuseStep 1416545 = 1062409) B1062409
theorem B1416563 : Blo 940584 1416563 := bstep (se 1 (by rfl) ⟨1062422, by rfl⟩ : syracuseStep 1416563 = 2124845) B2124845
theorem B1416593 : Blo 940584 1416593 := bstep (se 2 (by rfl) ⟨531222, by rfl⟩ : syracuseStep 1416593 = 1062445) B1062445
theorem B3579299 : Blo 940584 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B1416611 : Blo 940584 1416611 := bstep (se 1 (by rfl) ⟨1062458, by rfl⟩ : syracuseStep 1416611 = 2124917) B2124917
theorem B1416641 : Blo 940584 1416641 := bstep (se 2 (by rfl) ⟨531240, by rfl⟩ : syracuseStep 1416641 = 1062481) B1062481
theorem B1416659 : Blo 940584 1416659 := bstep (se 1 (by rfl) ⟨1062494, by rfl⟩ : syracuseStep 1416659 = 2124989) B2124989
theorem B3186161 : Blo 940584 3186161 := bstep (se 2 (by rfl) ⟨1194810, by rfl⟩ : syracuseStep 3186161 = 2389621) B2389621
theorem B1416689 : Blo 940584 1416689 := bstep (se 2 (by rfl) ⟨531258, by rfl⟩ : syracuseStep 1416689 = 1062517) B1062517
theorem B1416707 : Blo 940584 1416707 := bstep (se 1 (by rfl) ⟨1062530, by rfl⟩ : syracuseStep 1416707 = 2125061) B2125061
theorem B1416737 : Blo 940584 1416737 := bstep (se 2 (by rfl) ⟨531276, by rfl⟩ : syracuseStep 1416737 = 1062553) B1062553
theorem B1416755 : Blo 940584 1416755 := bstep (se 1 (by rfl) ⟨1062566, by rfl⟩ : syracuseStep 1416755 = 2125133) B2125133
theorem B1416785 : Blo 940584 1416785 := bstep (se 2 (by rfl) ⟨531294, by rfl⟩ : syracuseStep 1416785 = 1062589) B1062589
theorem B1416803 : Blo 940584 1416803 := bstep (se 1 (by rfl) ⟨1062602, by rfl⟩ : syracuseStep 1416803 = 2125205) B2125205
theorem B1416833 : Blo 940584 1416833 := bstep (se 2 (by rfl) ⟨531312, by rfl⟩ : syracuseStep 1416833 = 1062625) B1062625
theorem B1416851 : Blo 940584 1416851 := bstep (se 1 (by rfl) ⟨1062638, by rfl⟩ : syracuseStep 1416851 = 2125277) B2125277
theorem B2039491 : Blo 940584 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B2039555 : Blo 940584 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B2269073 : Blo 940584 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B3022829 : Blo 940584 3022829 := bstep (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) B1133561
theorem B3186701 : Blo 940584 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B3186755 : Blo 940584 3186755 := bstep (se 1 (by rfl) ⟨2390066, by rfl⟩ : syracuseStep 3186755 = 4780133) B4780133
theorem B3187025 : Blo 940584 3187025 := bstep (se 2 (by rfl) ⟨1195134, by rfl⟩ : syracuseStep 3187025 = 2390269) B2390269
theorem B3580301 : Blo 940584 3580301 := bstep (se 3 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 3580301 = 1342613) B1342613
theorem B1614257 : Blo 940584 1614257 := bstep (se 2 (by rfl) ⟨605346, by rfl⟩ : syracuseStep 1614257 = 1210693) B1210693
theorem B10199621 : Blo 940584 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B5088005 : Blo 940584 5088005 := bstep (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) B954001
theorem B3023725 : Blo 940584 3023725 := bstep (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) B1133897
theorem B3187565 : Blo 940584 3187565 := bstep (se 3 (by rfl) ⟨597668, by rfl⟩ : syracuseStep 3187565 = 1195337) B1195337
theorem B5088133 : Blo 940584 5088133 := bstep (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) B954025
theorem B3187619 : Blo 940584 3187619 := bstep (se 1 (by rfl) ⟨2390714, by rfl⟩ : syracuseStep 3187619 = 4781429) B4781429
theorem B3449891 : Blo 940584 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B3187889 : Blo 940584 3187889 := bstep (se 2 (by rfl) ⟨1195458, by rfl⟩ : syracuseStep 3187889 = 2390917) B2390917
theorem B1058179 : Blo 940584 1058179 := bstep (se 1 (by rfl) ⟨793634, by rfl⟩ : syracuseStep 1058179 = 1587269) B1587269
theorem B5088739 : Blo 940584 5088739 := bstep (se 1 (by rfl) ⟨3816554, by rfl⟩ : syracuseStep 5088739 = 7633109) B7633109
theorem B1058323 : Blo 940584 1058323 := bstep (se 1 (by rfl) ⟨793742, by rfl⟩ : syracuseStep 1058323 = 1587485) B1587485
theorem B3221041 : Blo 940584 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1058467 : Blo 940584 1058467 := bstep (se 1 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 1058467 = 1587701) B1587701
theorem B8038115 : Blo 940584 8038115 := bstep (se 1 (by rfl) ⟨6028586, by rfl⟩ : syracuseStep 8038115 = 12057173) B12057173
theorem B3024611 : Blo 940584 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B1058611 : Blo 940584 1058611 := bstep (se 1 (by rfl) ⟨793958, by rfl⟩ : syracuseStep 1058611 = 1587917) B1587917
theorem B2795363 : Blo 940584 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B1058755 : Blo 940584 1058755 := bstep (se 1 (by rfl) ⟨794066, by rfl⟩ : syracuseStep 1058755 = 1588133) B1588133
theorem B1058899 : Blo 940584 1058899 := bstep (se 1 (by rfl) ⟨794174, by rfl⟩ : syracuseStep 1058899 = 1588349) B1588349
theorem B4761827 : Blo 940584 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B1059043 : Blo 940584 1059043 := bstep (se 1 (by rfl) ⟨794282, by rfl⟩ : syracuseStep 1059043 = 1588565) B1588565
theorem B2009443 : Blo 940584 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B1059187 : Blo 940584 1059187 := bstep (se 1 (by rfl) ⟨794390, by rfl⟩ : syracuseStep 1059187 = 1588781) B1588781
theorem B10758581 : Blo 940584 10758581 := bstep (se 5 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 10758581 = 1008617) B1008617
theorem B3582413 : Blo 940584 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B1059331 : Blo 940584 1059331 := bstep (se 1 (by rfl) ⟨794498, by rfl⟩ : syracuseStep 1059331 = 1588997) B1588997
theorem B1190467 : Blo 940584 1190467 := bstep (se 1 (by rfl) ⟨892850, by rfl⟩ : syracuseStep 1190467 = 1785701) B1785701
theorem B1059475 : Blo 940584 1059475 := bstep (se 1 (by rfl) ⟨794606, by rfl⟩ : syracuseStep 1059475 = 1589213) B1589213
theorem B1059619 : Blo 940584 1059619 := bstep (se 1 (by rfl) ⟨794714, by rfl⟩ : syracuseStep 1059619 = 1589429) B1589429
theorem B1059763 : Blo 940584 1059763 := bstep (se 1 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 1059763 = 1589645) B1589645
theorem B4762637 : Blo 940584 4762637 := bstep (se 3 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 4762637 = 1785989) B1785989
theorem B1190963 : Blo 940584 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B1059907 : Blo 940584 1059907 := bstep (se 1 (by rfl) ⟨794930, by rfl⟩ : syracuseStep 1059907 = 1589861) B1589861
theorem B1060051 : Blo 940584 1060051 := bstep (se 1 (by rfl) ⟨795038, by rfl⟩ : syracuseStep 1060051 = 1590077) B1590077
theorem B3583217 : Blo 940584 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B1060195 : Blo 940584 1060195 := bstep (se 1 (by rfl) ⟨795146, by rfl⟩ : syracuseStep 1060195 = 1590293) B1590293
theorem B8170993 : Blo 940584 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B1060339 : Blo 940584 1060339 := bstep (se 1 (by rfl) ⟨795254, by rfl⟩ : syracuseStep 1060339 = 1590509) B1590509
theorem B2010673 : Blo 940584 2010673 := bstep (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) B1508005
theorem B1060483 : Blo 940584 1060483 := bstep (se 1 (by rfl) ⟨795362, by rfl⟩ : syracuseStep 1060483 = 1590725) B1590725
theorem B2174627 : Blo 940584 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B3223217 : Blo 940584 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B1191667 : Blo 940584 1191667 := bstep (se 1 (by rfl) ⟨893750, by rfl⟩ : syracuseStep 1191667 = 1787501) B1787501
theorem B1060627 : Blo 940584 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B15314741 : Blo 940584 15314741 := bstep (se 5 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 15314741 = 1435757) B1435757
theorem B1191763 : Blo 940584 1191763 := bstep (se 1 (by rfl) ⟨893822, by rfl⟩ : syracuseStep 1191763 = 1787645) B1787645
theorem B3583885 : Blo 940584 3583885 := bstep (se 3 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 3583885 = 1343957) B1343957
theorem B1060771 : Blo 940584 1060771 := bstep (se 1 (by rfl) ⟨795578, by rfl⟩ : syracuseStep 1060771 = 1591157) B1591157
theorem B1060915 : Blo 940584 1060915 := bstep (se 1 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 1060915 = 1591373) B1591373
theorem B1061059 : Blo 940584 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B6041861 : Blo 940584 6041861 := bstep (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) B1132849
theorem B1290529 : Blo 940584 1290529 := bstep (se 2 (by rfl) ⟨483948, by rfl⟩ : syracuseStep 1290529 = 967897) B967897
theorem B1192259 : Blo 940584 1192259 := bstep (se 1 (by rfl) ⟨894194, by rfl⟩ : syracuseStep 1192259 = 1788389) B1788389
theorem B1061203 : Blo 940584 1061203 := bstep (se 1 (by rfl) ⟨795902, by rfl⟩ : syracuseStep 1061203 = 1591805) B1591805
theorem B1061347 : Blo 940584 1061347 := bstep (se 1 (by rfl) ⟨796010, by rfl⟩ : syracuseStep 1061347 = 1592021) B1592021
theorem B1061491 : Blo 940584 1061491 := bstep (se 1 (by rfl) ⟨796118, by rfl⟩ : syracuseStep 1061491 = 1592237) B1592237
theorem B3584675 : Blo 940584 3584675 := bstep (se 1 (by rfl) ⟨2688506, by rfl⟩ : syracuseStep 3584675 = 5377013) B5377013
theorem B1061635 : Blo 940584 1061635 := bstep (se 1 (by rfl) ⟨796226, by rfl⟩ : syracuseStep 1061635 = 1592453) B1592453
theorem B1061779 : Blo 940584 1061779 := bstep (se 1 (by rfl) ⟨796334, by rfl⟩ : syracuseStep 1061779 = 1592669) B1592669
theorem B1192963 : Blo 940584 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B2012177 : Blo 940584 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B2012195 : Blo 940584 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B1061923 : Blo 940584 1061923 := bstep (se 1 (by rfl) ⟨796442, by rfl⟩ : syracuseStep 1061923 = 1592885) B1592885
theorem B7156835 : Blo 940584 7156835 := bstep (se 1 (by rfl) ⟨5367626, by rfl⟩ : syracuseStep 7156835 = 10735253) B10735253
theorem B1193059 : Blo 940584 1193059 := bstep (se 1 (by rfl) ⟨894794, by rfl⟩ : syracuseStep 1193059 = 1789589) B1789589
theorem B4535473 : Blo 940584 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B1062067 : Blo 940584 1062067 := bstep (se 1 (by rfl) ⟨796550, by rfl⟩ : syracuseStep 1062067 = 1593101) B1593101
theorem B3585329 : Blo 940584 3585329 := bstep (se 2 (by rfl) ⟨1344498, by rfl⟩ : syracuseStep 3585329 = 2688997) B2688997
theorem B1062211 : Blo 940584 1062211 := bstep (se 1 (by rfl) ⟨796658, by rfl⟩ : syracuseStep 1062211 = 1593317) B1593317
theorem B8041841 : Blo 940584 8041841 := bstep (se 2 (by rfl) ⟨3015690, by rfl⟩ : syracuseStep 8041841 = 6031381) B6031381
theorem B1062355 : Blo 940584 1062355 := bstep (se 1 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 1062355 = 1593533) B1593533
theorem B1193555 : Blo 940584 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B3225187 : Blo 940584 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B1062499 : Blo 940584 1062499 := bstep (se 1 (by rfl) ⟨796874, by rfl⟩ : syracuseStep 1062499 = 1593749) B1593749
theorem B1062643 : Blo 940584 1062643 := bstep (se 1 (by rfl) ⟨796982, by rfl⟩ : syracuseStep 1062643 = 1593965) B1593965
theorem B4765553 : Blo 940584 4765553 := bstep (se 2 (by rfl) ⟨1787082, by rfl⟩ : syracuseStep 4765553 = 3574165) B3574165
theorem B8730595 : Blo 940584 8730595 := bstep (se 1 (by rfl) ⟨6547946, by rfl⟩ : syracuseStep 8730595 = 13095893) B13095893
theorem B1587377 : Blo 940584 1587377 := bstep (se 2 (by rfl) ⟨595266, by rfl⟩ : syracuseStep 1587377 = 1190533) B1190533
theorem B1194259 : Blo 940584 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B1587505 : Blo 940584 1587505 := bstep (se 2 (by rfl) ⟨595314, by rfl⟩ : syracuseStep 1587505 = 1190629) B1190629
theorem B1587539 : Blo 940584 1587539 := bstep (se 1 (by rfl) ⟨1190654, by rfl⟩ : syracuseStep 1587539 = 2381309) B2381309
theorem B1194355 : Blo 940584 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B1587667 : Blo 940584 1587667 := bstep (se 1 (by rfl) ⟨1190750, by rfl⟩ : syracuseStep 1587667 = 2381501) B2381501
theorem B1587809 : Blo 940584 1587809 := bstep (se 2 (by rfl) ⟨595428, by rfl⟩ : syracuseStep 1587809 = 1190857) B1190857
theorem B1587937 : Blo 940584 1587937 := bstep (se 2 (by rfl) ⟨595476, by rfl⟩ : syracuseStep 1587937 = 1190953) B1190953
theorem B1587971 : Blo 940584 1587971 := bstep (se 1 (by rfl) ⟨1190978, by rfl⟩ : syracuseStep 1587971 = 2381957) B2381957
theorem B1194851 : Blo 940584 1194851 := bstep (se 1 (by rfl) ⟨896138, by rfl⟩ : syracuseStep 1194851 = 1792277) B1792277
theorem B7256945 : Blo 940584 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B1588099 : Blo 940584 1588099 := bstep (se 1 (by rfl) ⟨1191074, by rfl⟩ : syracuseStep 1588099 = 2382149) B2382149
theorem B2014193 : Blo 940584 2014193 := bstep (se 2 (by rfl) ⟨755322, by rfl⟩ : syracuseStep 2014193 = 1510645) B1510645
theorem B1588241 : Blo 940584 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B1588369 : Blo 940584 1588369 := bstep (se 2 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 1588369 = 1191277) B1191277
theorem B1588403 : Blo 940584 1588403 := bstep (se 1 (by rfl) ⟨1191302, by rfl⟩ : syracuseStep 1588403 = 2382605) B2382605
theorem B4767011 : Blo 940584 4767011 := bstep (se 1 (by rfl) ⟨3575258, by rfl⟩ : syracuseStep 4767011 = 7150517) B7150517
theorem B1588531 : Blo 940584 1588531 := bstep (se 1 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 1588531 = 2382797) B2382797
theorem B4537741 : Blo 940584 4537741 := bstep (se 3 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 4537741 = 1701653) B1701653
theorem B3816881 : Blo 940584 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B1588673 : Blo 940584 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B2178499 : Blo 940584 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B2014723 : Blo 940584 2014723 := bstep (se 1 (by rfl) ⟨1511042, by rfl⟩ : syracuseStep 2014723 = 3022085) B3022085
theorem B1588801 : Blo 940584 1588801 := bstep (se 2 (by rfl) ⟨595800, by rfl⟩ : syracuseStep 1588801 = 1191601) B1191601
theorem B1359443 : Blo 940584 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B1588835 : Blo 940584 1588835 := bstep (se 1 (by rfl) ⟨1191626, by rfl⟩ : syracuseStep 1588835 = 2383253) B2383253
theorem B6045347 : Blo 940584 6045347 := bstep (se 1 (by rfl) ⟨4534010, by rfl⟩ : syracuseStep 6045347 = 9068021) B9068021
theorem B1588963 : Blo 940584 1588963 := bstep (se 1 (by rfl) ⟨1191722, by rfl⟩ : syracuseStep 1588963 = 2383445) B2383445
theorem B3227377 : Blo 940584 3227377 := bstep (se 2 (by rfl) ⟨1210266, by rfl⟩ : syracuseStep 3227377 = 2420533) B2420533
theorem B1589105 : Blo 940584 1589105 := bstep (se 2 (by rfl) ⟨595914, by rfl⟩ : syracuseStep 1589105 = 1191829) B1191829
theorem B1589233 : Blo 940584 1589233 := bstep (se 2 (by rfl) ⟨595962, by rfl⟩ : syracuseStep 1589233 = 1191925) B1191925
theorem B1589267 : Blo 940584 1589267 := bstep (se 1 (by rfl) ⟨1191950, by rfl⟩ : syracuseStep 1589267 = 2383901) B2383901
theorem B5357603 : Blo 940584 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B4767821 : Blo 940584 4767821 := bstep (se 3 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 4767821 = 1787933) B1787933
theorem B3620963 : Blo 940584 3620963 := bstep (se 1 (by rfl) ⟨2715722, by rfl⟩ : syracuseStep 3620963 = 5431445) B5431445
theorem B1589395 : Blo 940584 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B1589537 : Blo 940584 1589537 := bstep (se 2 (by rfl) ⟨596076, by rfl⟩ : syracuseStep 1589537 = 1192153) B1192153
theorem B12075317 : Blo 940584 12075317 := bstep (se 5 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 12075317 = 1132061) B1132061
theorem B1786225 : Blo 940584 1786225 := bstep (se 2 (by rfl) ⟨669834, by rfl⟩ : syracuseStep 1786225 = 1339669) B1339669
theorem B3064177 : Blo 940584 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B1589665 : Blo 940584 1589665 := bstep (se 2 (by rfl) ⟨596124, by rfl⟩ : syracuseStep 1589665 = 1192249) B1192249
theorem B1589699 : Blo 940584 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B4538915 : Blo 940584 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B1589827 : Blo 940584 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B1589969 : Blo 940584 1589969 := bstep (se 2 (by rfl) ⟨596238, by rfl⟩ : syracuseStep 1589969 = 1192477) B1192477
theorem B1786627 : Blo 940584 1786627 := bstep (se 1 (by rfl) ⟨1339970, by rfl⟩ : syracuseStep 1786627 = 2679941) B2679941
theorem B1131283 : Blo 940584 1131283 := bstep (se 1 (by rfl) ⟨848462, by rfl⟩ : syracuseStep 1131283 = 1696925) B1696925
theorem B1786673 : Blo 940584 1786673 := bstep (se 2 (by rfl) ⟨670002, by rfl⟩ : syracuseStep 1786673 = 1340005) B1340005
theorem B1590097 : Blo 940584 1590097 := bstep (se 2 (by rfl) ⟨596286, by rfl⟩ : syracuseStep 1590097 = 1192573) B1192573
theorem B1590131 : Blo 940584 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B2016209 : Blo 940584 2016209 := bstep (se 2 (by rfl) ⟨756078, by rfl⟩ : syracuseStep 2016209 = 1512157) B1512157
theorem B2016227 : Blo 940584 2016227 := bstep (se 1 (by rfl) ⟨1512170, by rfl⟩ : syracuseStep 2016227 = 3024341) B3024341
theorem B1590259 : Blo 940584 1590259 := bstep (se 1 (by rfl) ⟨1192694, by rfl⟩ : syracuseStep 1590259 = 2385389) B2385389
theorem B1786961 : Blo 940584 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B1131619 : Blo 940584 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B1590401 : Blo 940584 1590401 := bstep (se 2 (by rfl) ⟨596400, by rfl⟩ : syracuseStep 1590401 = 1192801) B1192801
theorem B1590529 : Blo 940584 1590529 := bstep (se 2 (by rfl) ⟨596448, by rfl⟩ : syracuseStep 1590529 = 1192897) B1192897
theorem B8045837 : Blo 940584 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B1590563 : Blo 940584 1590563 := bstep (se 1 (by rfl) ⟨1192922, by rfl⟩ : syracuseStep 1590563 = 2385845) B2385845
theorem B1590691 : Blo 940584 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B1590833 : Blo 940584 1590833 := bstep (se 2 (by rfl) ⟨596562, by rfl⟩ : syracuseStep 1590833 = 1193125) B1193125
theorem B1590961 : Blo 940584 1590961 := bstep (se 2 (by rfl) ⟨596610, by rfl⟩ : syracuseStep 1590961 = 1193221) B1193221
theorem B1590995 : Blo 940584 1590995 := bstep (se 1 (by rfl) ⟨1193246, by rfl⟩ : syracuseStep 1590995 = 2386493) B2386493
theorem B1787683 : Blo 940584 1787683 := bstep (se 1 (by rfl) ⟨1340762, by rfl⟩ : syracuseStep 1787683 = 2681525) B2681525
theorem B1591123 : Blo 940584 1591123 := bstep (se 1 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 1591123 = 2386685) B2386685
theorem B1132499 : Blo 940584 1132499 := bstep (se 1 (by rfl) ⟨849374, by rfl⟩ : syracuseStep 1132499 = 1698749) B1698749
theorem B1591265 : Blo 940584 1591265 := bstep (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) B1193449
theorem B1591393 : Blo 940584 1591393 := bstep (se 2 (by rfl) ⟨596772, by rfl⟩ : syracuseStep 1591393 = 1193545) B1193545
theorem B1591427 : Blo 940584 1591427 := bstep (se 1 (by rfl) ⟨1193570, by rfl⟩ : syracuseStep 1591427 = 2387141) B2387141
theorem B1788131 : Blo 940584 1788131 := bstep (se 1 (by rfl) ⟨1341098, by rfl⟩ : syracuseStep 1788131 = 2682197) B2682197
theorem B10733795 : Blo 940584 10733795 := bstep (se 1 (by rfl) ⟨8050346, by rfl⟩ : syracuseStep 10733795 = 16100693) B16100693
theorem B1657073 : Blo 940584 1657073 := bstep (se 2 (by rfl) ⟨621402, by rfl⟩ : syracuseStep 1657073 = 1242805) B1242805
theorem B1591555 : Blo 940584 1591555 := bstep (se 1 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 1591555 = 2387333) B2387333
theorem B7162181 : Blo 940584 7162181 := bstep (se 4 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 7162181 = 1342909) B1342909
theorem B1591697 : Blo 940584 1591697 := bstep (se 2 (by rfl) ⟨596886, by rfl⟩ : syracuseStep 1591697 = 1193773) B1193773
theorem B1788419 : Blo 940584 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B1591825 : Blo 940584 1591825 := bstep (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) B1193869
theorem B3230225 : Blo 940584 3230225 := bstep (se 2 (by rfl) ⟨1211334, by rfl⟩ : syracuseStep 3230225 = 2422669) B2422669
theorem B1591859 : Blo 940584 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B1591987 : Blo 940584 1591987 := bstep (se 1 (by rfl) ⟨1193990, by rfl⟩ : syracuseStep 1591987 = 2387981) B2387981
theorem B1592129 : Blo 940584 1592129 := bstep (se 2 (by rfl) ⟨597048, by rfl⟩ : syracuseStep 1592129 = 1194097) B1194097
theorem B2116529 : Blo 940584 2116529 := bstep (se 2 (by rfl) ⟨793698, by rfl⟩ : syracuseStep 2116529 = 1587397) B1587397
theorem B4770737 : Blo 940584 4770737 := bstep (se 2 (by rfl) ⟨1789026, by rfl⟩ : syracuseStep 4770737 = 3578053) B3578053
theorem B1592257 : Blo 940584 1592257 := bstep (se 2 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 1592257 = 1194193) B1194193
theorem B2116547 : Blo 940584 2116547 := bstep (se 1 (by rfl) ⟨1587410, by rfl⟩ : syracuseStep 2116547 = 3174821) B3174821
theorem B1592291 : Blo 940584 1592291 := bstep (se 1 (by rfl) ⟨1194218, by rfl⟩ : syracuseStep 1592291 = 2388437) B2388437
theorem B3230705 : Blo 940584 3230705 := bstep (se 2 (by rfl) ⟨1211514, by rfl⟩ : syracuseStep 3230705 = 2423029) B2423029
theorem B1592419 : Blo 940584 1592419 := bstep (se 1 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 1592419 = 2388629) B2388629
theorem B6540401 : Blo 940584 6540401 := bstep (se 2 (by rfl) ⟨2452650, by rfl⟩ : syracuseStep 6540401 = 4905301) B4905301
theorem B2116817 : Blo 940584 2116817 := bstep (se 2 (by rfl) ⟨793806, by rfl⟩ : syracuseStep 2116817 = 1587613) B1587613
theorem B2116835 : Blo 940584 2116835 := bstep (se 1 (by rfl) ⟨1587626, by rfl⟩ : syracuseStep 2116835 = 3175253) B3175253
theorem B1592561 : Blo 940584 1592561 := bstep (se 2 (by rfl) ⟨597210, by rfl⟩ : syracuseStep 1592561 = 1194421) B1194421
theorem B1592689 : Blo 940584 1592689 := bstep (se 2 (by rfl) ⟨597258, by rfl⟩ : syracuseStep 1592689 = 1194517) B1194517
theorem B1592723 : Blo 940584 1592723 := bstep (se 1 (by rfl) ⟨1194542, by rfl⟩ : syracuseStep 1592723 = 2389085) B2389085
theorem B3231139 : Blo 940584 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B2543021 : Blo 940584 2543021 := bstep (se 3 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 2543021 = 953633) B953633
theorem B1789361 : Blo 940584 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B2117105 : Blo 940584 2117105 := bstep (se 2 (by rfl) ⟨793914, by rfl⟩ : syracuseStep 2117105 = 1587829) B1587829
theorem B2117123 : Blo 940584 2117123 := bstep (se 1 (by rfl) ⟨1587842, by rfl⟩ : syracuseStep 2117123 = 3175685) B3175685
theorem B1592851 : Blo 940584 1592851 := bstep (se 1 (by rfl) ⟨1194638, by rfl⟩ : syracuseStep 1592851 = 2389277) B2389277
theorem B4836977 : Blo 940584 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B1592993 : Blo 940584 1592993 := bstep (se 2 (by rfl) ⟨597372, by rfl⟩ : syracuseStep 1592993 = 1194745) B1194745
theorem B2117393 : Blo 940584 2117393 := bstep (se 2 (by rfl) ⟨794022, by rfl⟩ : syracuseStep 2117393 = 1588045) B1588045
theorem B1593121 : Blo 940584 1593121 := bstep (se 2 (by rfl) ⟨597420, by rfl⟩ : syracuseStep 1593121 = 1194841) B1194841
theorem B1527587 : Blo 940584 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B2117411 : Blo 940584 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B1593155 : Blo 940584 1593155 := bstep (se 1 (by rfl) ⟨1194866, by rfl⟩ : syracuseStep 1593155 = 2389733) B2389733
theorem B1593283 : Blo 940584 1593283 := bstep (se 1 (by rfl) ⟨1194962, by rfl⟩ : syracuseStep 1593283 = 2389925) B2389925
theorem B2117681 : Blo 940584 2117681 := bstep (se 2 (by rfl) ⟨794130, by rfl⟩ : syracuseStep 2117681 = 1588261) B1588261
theorem B2117699 : Blo 940584 2117699 := bstep (se 1 (by rfl) ⟨1588274, by rfl⟩ : syracuseStep 2117699 = 3176549) B3176549
theorem B1593425 : Blo 940584 1593425 := bstep (se 2 (by rfl) ⟨597534, by rfl⟩ : syracuseStep 1593425 = 1195069) B1195069
theorem B3821681 : Blo 940584 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B4018339 : Blo 940584 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B1593553 : Blo 940584 1593553 := bstep (se 2 (by rfl) ⟨597582, by rfl⟩ : syracuseStep 1593553 = 1195165) B1195165
theorem B24170723 : Blo 940584 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B1593587 : Blo 940584 1593587 := bstep (se 1 (by rfl) ⟨1195190, by rfl⟩ : syracuseStep 1593587 = 2390381) B2390381
theorem B1790257 : Blo 940584 1790257 := bstep (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) B1342693
theorem B2117969 : Blo 940584 2117969 := bstep (se 2 (by rfl) ⟨794238, by rfl⟩ : syracuseStep 2117969 = 1588477) B1588477
theorem B2117987 : Blo 940584 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B4772195 : Blo 940584 4772195 := bstep (se 1 (by rfl) ⟨3579146, by rfl⟩ : syracuseStep 4772195 = 7158293) B7158293
theorem B1593715 : Blo 940584 1593715 := bstep (se 1 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 1593715 = 2390573) B2390573
theorem B1790417 : Blo 940584 1790417 := bstep (se 2 (by rfl) ⟨671406, by rfl⟩ : syracuseStep 1790417 = 1342813) B1342813
theorem B5722595 : Blo 940584 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B1593857 : Blo 940584 1593857 := bstep (se 2 (by rfl) ⟨597696, by rfl⟩ : syracuseStep 1593857 = 1195393) B1195393
theorem B2118257 : Blo 940584 2118257 := bstep (se 2 (by rfl) ⟨794346, by rfl⟩ : syracuseStep 2118257 = 1588693) B1588693
theorem B1593985 : Blo 940584 1593985 := bstep (se 2 (by rfl) ⟨597744, by rfl⟩ : syracuseStep 1593985 = 1195489) B1195489
theorem B2118275 : Blo 940584 2118275 := bstep (se 1 (by rfl) ⟨1588706, by rfl⟩ : syracuseStep 2118275 = 3177413) B3177413
theorem B1790819 : Blo 940584 1790819 := bstep (se 1 (by rfl) ⟨1343114, by rfl⟩ : syracuseStep 1790819 = 2686229) B2686229
theorem B2118545 : Blo 940584 2118545 := bstep (se 2 (by rfl) ⟨794454, by rfl⟩ : syracuseStep 2118545 = 1588909) B1588909
theorem B2118563 : Blo 940584 2118563 := bstep (se 1 (by rfl) ⟨1588922, by rfl⟩ : syracuseStep 2118563 = 3177845) B3177845
theorem B2413667 : Blo 940584 2413667 := bstep (se 1 (by rfl) ⟨1810250, by rfl⟩ : syracuseStep 2413667 = 3620501) B3620501
theorem B27939953 : Blo 940584 27939953 := bstep (se 2 (by rfl) ⟨10477482, by rfl⟩ : syracuseStep 27939953 = 20954965) B20954965
theorem B4773005 : Blo 940584 4773005 := bstep (se 3 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 4773005 = 1789877) B1789877
theorem B2118833 : Blo 940584 2118833 := bstep (se 2 (by rfl) ⟨794562, by rfl⟩ : syracuseStep 2118833 = 1589125) B1589125
theorem B2118851 : Blo 940584 2118851 := bstep (se 1 (by rfl) ⟨1589138, by rfl⟩ : syracuseStep 2118851 = 3178277) B3178277
theorem B2413891 : Blo 940584 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B1529201 : Blo 940584 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B1529203 : Blo 940584 1529203 := bstep (se 1 (by rfl) ⟨1146902, by rfl⟩ : syracuseStep 1529203 = 2293805) B2293805
theorem B1004995 : Blo 940584 1004995 := bstep (se 1 (by rfl) ⟨753746, by rfl⟩ : syracuseStep 1004995 = 1507493) B1507493
theorem B2119121 : Blo 940584 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B2119139 : Blo 940584 2119139 := bstep (se 1 (by rfl) ⟨1589354, by rfl⟩ : syracuseStep 2119139 = 3178709) B3178709
theorem B2381521 : Blo 940584 2381521 := bstep (se 2 (by rfl) ⟨893070, by rfl⟩ : syracuseStep 2381521 = 1786141) B1786141
theorem B1791715 : Blo 940584 1791715 := bstep (se 1 (by rfl) ⟨1343786, by rfl⟩ : syracuseStep 1791715 = 2687573) B2687573
theorem B2119409 : Blo 940584 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B2119427 : Blo 940584 2119427 := bstep (se 1 (by rfl) ⟨1589570, by rfl⟩ : syracuseStep 2119427 = 3179141) B3179141
theorem B1791875 : Blo 940584 1791875 := bstep (se 1 (by rfl) ⟨1343906, by rfl⟩ : syracuseStep 1791875 = 2687813) B2687813
theorem B2381795 : Blo 940584 2381795 := bstep (se 1 (by rfl) ⟨1786346, by rfl⟩ : syracuseStep 2381795 = 3572693) B3572693
theorem B2119697 : Blo 940584 2119697 := bstep (se 2 (by rfl) ⟨794886, by rfl⟩ : syracuseStep 2119697 = 1589773) B1589773
theorem B2119715 : Blo 940584 2119715 := bstep (se 1 (by rfl) ⟨1589786, by rfl⟩ : syracuseStep 2119715 = 3179573) B3179573
theorem B3823757 : Blo 940584 3823757 := bstep (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) B1433909
theorem B2381987 : Blo 940584 2381987 := bstep (se 1 (by rfl) ⟨1786490, by rfl⟩ : syracuseStep 2381987 = 3572981) B3572981
theorem B2545873 : Blo 940584 2545873 := bstep (se 2 (by rfl) ⟨954702, by rfl⟩ : syracuseStep 2545873 = 1909405) B1909405
theorem B12245261 : Blo 940584 12245261 := bstep (se 3 (by rfl) ⟨2295986, by rfl⟩ : syracuseStep 12245261 = 4591973) B4591973
theorem B2119985 : Blo 940584 2119985 := bstep (se 2 (by rfl) ⟨794994, by rfl⟩ : syracuseStep 2119985 = 1589989) B1589989
theorem B2120003 : Blo 940584 2120003 := bstep (se 1 (by rfl) ⟨1590002, by rfl⟩ : syracuseStep 2120003 = 3180005) B3180005
theorem B1006003 : Blo 940584 1006003 := bstep (se 1 (by rfl) ⟨754502, by rfl⟩ : syracuseStep 1006003 = 1509005) B1509005
theorem B6117859 : Blo 940584 6117859 := bstep (se 1 (by rfl) ⟨4588394, by rfl⟩ : syracuseStep 6117859 = 9176789) B9176789
theorem B4020785 : Blo 940584 4020785 := bstep (se 2 (by rfl) ⟨1507794, by rfl⟩ : syracuseStep 4020785 = 3015589) B3015589
theorem B940595 : Blo 940584 940595 := bstep (se 1 (by rfl) ⟨705446, by rfl⟩ : syracuseStep 940595 = 1410893) B1410893
theorem B940611 : Blo 940584 940611 := bstep (se 1 (by rfl) ⟨705458, by rfl⟩ : syracuseStep 940611 = 1410917) B1410917
theorem B2120273 : Blo 940584 2120273 := bstep (se 2 (by rfl) ⟨795102, by rfl⟩ : syracuseStep 2120273 = 1590205) B1590205
theorem B940627 : Blo 940584 940627 := bstep (se 1 (by rfl) ⟨705470, by rfl⟩ : syracuseStep 940627 = 1410941) B1410941
theorem B940643 : Blo 940584 940643 := bstep (se 1 (by rfl) ⟨705482, by rfl⟩ : syracuseStep 940643 = 1410965) B1410965
theorem B2120291 : Blo 940584 2120291 := bstep (se 1 (by rfl) ⟨1590218, by rfl⟩ : syracuseStep 2120291 = 3180437) B3180437
theorem B940659 : Blo 940584 940659 := bstep (se 1 (by rfl) ⟨705494, by rfl⟩ : syracuseStep 940659 = 1410989) B1410989
theorem B940675 : Blo 940584 940675 := bstep (se 1 (by rfl) ⟨705506, by rfl⟩ : syracuseStep 940675 = 1411013) B1411013
theorem B940691 : Blo 940584 940691 := bstep (se 1 (by rfl) ⟨705518, by rfl⟩ : syracuseStep 940691 = 1411037) B1411037
theorem B940707 : Blo 940584 940707 := bstep (se 1 (by rfl) ⟨705530, by rfl⟩ : syracuseStep 940707 = 1411061) B1411061
theorem B940723 : Blo 940584 940723 := bstep (se 1 (by rfl) ⟨705542, by rfl⟩ : syracuseStep 940723 = 1411085) B1411085
theorem B940739 : Blo 940584 940739 := bstep (se 1 (by rfl) ⟨705554, by rfl⟩ : syracuseStep 940739 = 1411109) B1411109
theorem B940755 : Blo 940584 940755 := bstep (se 1 (by rfl) ⟨705566, by rfl⟩ : syracuseStep 940755 = 1411133) B1411133
theorem B940771 : Blo 940584 940771 := bstep (se 1 (by rfl) ⟨705578, by rfl⟩ : syracuseStep 940771 = 1411157) B1411157
theorem B940787 : Blo 940584 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B940803 : Blo 940584 940803 := bstep (se 1 (by rfl) ⟨705602, by rfl⟩ : syracuseStep 940803 = 1411205) B1411205
theorem B940819 : Blo 940584 940819 := bstep (se 1 (by rfl) ⟨705614, by rfl⟩ : syracuseStep 940819 = 1411229) B1411229
theorem B940835 : Blo 940584 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B940851 : Blo 940584 940851 := bstep (se 1 (by rfl) ⟨705638, by rfl⟩ : syracuseStep 940851 = 1411277) B1411277
theorem B940867 : Blo 940584 940867 := bstep (se 1 (by rfl) ⟨705650, by rfl⟩ : syracuseStep 940867 = 1411301) B1411301
theorem B940883 : Blo 940584 940883 := bstep (se 1 (by rfl) ⟨705662, by rfl⟩ : syracuseStep 940883 = 1411325) B1411325
theorem B940899 : Blo 940584 940899 := bstep (se 1 (by rfl) ⟨705674, by rfl⟩ : syracuseStep 940899 = 1411349) B1411349
theorem B2415473 : Blo 940584 2415473 := bstep (se 2 (by rfl) ⟨905802, by rfl⟩ : syracuseStep 2415473 = 1811605) B1811605
theorem B2120561 : Blo 940584 2120561 := bstep (se 2 (by rfl) ⟨795210, by rfl⟩ : syracuseStep 2120561 = 1590421) B1590421
theorem B940915 : Blo 940584 940915 := bstep (se 1 (by rfl) ⟨705686, by rfl⟩ : syracuseStep 940915 = 1411373) B1411373
theorem B940931 : Blo 940584 940931 := bstep (se 1 (by rfl) ⟨705698, by rfl⟩ : syracuseStep 940931 = 1411397) B1411397
theorem B2120579 : Blo 940584 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B940947 : Blo 940584 940947 := bstep (se 1 (by rfl) ⟨705710, by rfl⟩ : syracuseStep 940947 = 1411421) B1411421
theorem B940963 : Blo 940584 940963 := bstep (se 1 (by rfl) ⟨705722, by rfl⟩ : syracuseStep 940963 = 1411445) B1411445
theorem B1792945 : Blo 940584 1792945 := bstep (se 2 (by rfl) ⟨672354, by rfl⟩ : syracuseStep 1792945 = 1344709) B1344709
theorem B940979 : Blo 940584 940979 := bstep (se 1 (by rfl) ⟨705734, by rfl⟩ : syracuseStep 940979 = 1411469) B1411469
theorem B940995 : Blo 940584 940995 := bstep (se 1 (by rfl) ⟨705746, by rfl⟩ : syracuseStep 940995 = 1411493) B1411493
theorem B941011 : Blo 940584 941011 := bstep (se 1 (by rfl) ⟨705758, by rfl⟩ : syracuseStep 941011 = 1411517) B1411517
theorem B941027 : Blo 940584 941027 := bstep (se 1 (by rfl) ⟨705770, by rfl⟩ : syracuseStep 941027 = 1411541) B1411541
theorem B941043 : Blo 940584 941043 := bstep (se 1 (by rfl) ⟨705782, by rfl⟩ : syracuseStep 941043 = 1411565) B1411565
theorem B941059 : Blo 940584 941059 := bstep (se 1 (by rfl) ⟨705794, by rfl⟩ : syracuseStep 941059 = 1411589) B1411589
theorem B941075 : Blo 940584 941075 := bstep (se 1 (by rfl) ⟨705806, by rfl⟩ : syracuseStep 941075 = 1411613) B1411613
theorem B941091 : Blo 940584 941091 := bstep (se 1 (by rfl) ⟨705818, by rfl⟩ : syracuseStep 941091 = 1411637) B1411637
theorem B941107 : Blo 940584 941107 := bstep (se 1 (by rfl) ⟨705830, by rfl⟩ : syracuseStep 941107 = 1411661) B1411661
theorem B941123 : Blo 940584 941123 := bstep (se 1 (by rfl) ⟨705842, by rfl⟩ : syracuseStep 941123 = 1411685) B1411685
theorem B2382929 : Blo 940584 2382929 := bstep (se 2 (by rfl) ⟨893598, by rfl⟩ : syracuseStep 2382929 = 1787197) B1787197
theorem B941139 : Blo 940584 941139 := bstep (se 1 (by rfl) ⟨705854, by rfl⟩ : syracuseStep 941139 = 1411709) B1411709
theorem B941155 : Blo 940584 941155 := bstep (se 1 (by rfl) ⟨705866, by rfl⟩ : syracuseStep 941155 = 1411733) B1411733
theorem B941171 : Blo 940584 941171 := bstep (se 1 (by rfl) ⟨705878, by rfl⟩ : syracuseStep 941171 = 1411757) B1411757
theorem B941187 : Blo 940584 941187 := bstep (se 1 (by rfl) ⟨705890, by rfl⟩ : syracuseStep 941187 = 1411781) B1411781
theorem B2382979 : Blo 940584 2382979 := bstep (se 1 (by rfl) ⟨1787234, by rfl⟩ : syracuseStep 2382979 = 3574469) B3574469
theorem B2120849 : Blo 940584 2120849 := bstep (se 2 (by rfl) ⟨795318, by rfl⟩ : syracuseStep 2120849 = 1590637) B1590637
theorem B941203 : Blo 940584 941203 := bstep (se 1 (by rfl) ⟨705902, by rfl⟩ : syracuseStep 941203 = 1411805) B1411805
theorem B941219 : Blo 940584 941219 := bstep (se 1 (by rfl) ⟨705914, by rfl⟩ : syracuseStep 941219 = 1411829) B1411829
theorem B2120867 : Blo 940584 2120867 := bstep (se 1 (by rfl) ⟨1590650, by rfl⟩ : syracuseStep 2120867 = 3181301) B3181301
theorem B941235 : Blo 940584 941235 := bstep (se 1 (by rfl) ⟨705926, by rfl⟩ : syracuseStep 941235 = 1411853) B1411853
theorem B941251 : Blo 940584 941251 := bstep (se 1 (by rfl) ⟨705938, by rfl⟩ : syracuseStep 941251 = 1411877) B1411877
theorem B941267 : Blo 940584 941267 := bstep (se 1 (by rfl) ⟨705950, by rfl⟩ : syracuseStep 941267 = 1411901) B1411901
theorem B941283 : Blo 940584 941283 := bstep (se 1 (by rfl) ⟨705962, by rfl⟩ : syracuseStep 941283 = 1411925) B1411925
theorem B941299 : Blo 940584 941299 := bstep (se 1 (by rfl) ⟨705974, by rfl⟩ : syracuseStep 941299 = 1411949) B1411949
theorem B941315 : Blo 940584 941315 := bstep (se 1 (by rfl) ⟨705986, by rfl⟩ : syracuseStep 941315 = 1411973) B1411973
theorem B12082445 : Blo 940584 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B2383121 : Blo 940584 2383121 := bstep (se 2 (by rfl) ⟨893670, by rfl⟩ : syracuseStep 2383121 = 1787341) B1787341
theorem B941331 : Blo 940584 941331 := bstep (se 1 (by rfl) ⟨705998, by rfl⟩ : syracuseStep 941331 = 1411997) B1411997
theorem B941347 : Blo 940584 941347 := bstep (se 1 (by rfl) ⟨706010, by rfl⟩ : syracuseStep 941347 = 1412021) B1412021
theorem B941363 : Blo 940584 941363 := bstep (se 1 (by rfl) ⟨706022, by rfl⟩ : syracuseStep 941363 = 1412045) B1412045
theorem B941379 : Blo 940584 941379 := bstep (se 1 (by rfl) ⟨706034, by rfl⟩ : syracuseStep 941379 = 1412069) B1412069
theorem B941395 : Blo 940584 941395 := bstep (se 1 (by rfl) ⟨706046, by rfl⟩ : syracuseStep 941395 = 1412093) B1412093
theorem B941411 : Blo 940584 941411 := bstep (se 1 (by rfl) ⟨706058, by rfl⟩ : syracuseStep 941411 = 1412117) B1412117
theorem B941427 : Blo 940584 941427 := bstep (se 1 (by rfl) ⟨706070, by rfl⟩ : syracuseStep 941427 = 1412141) B1412141
theorem B941443 : Blo 940584 941443 := bstep (se 1 (by rfl) ⟨706082, by rfl⟩ : syracuseStep 941443 = 1412165) B1412165
theorem B941459 : Blo 940584 941459 := bstep (se 1 (by rfl) ⟨706094, by rfl⟩ : syracuseStep 941459 = 1412189) B1412189
theorem B941475 : Blo 940584 941475 := bstep (se 1 (by rfl) ⟨706106, by rfl⟩ : syracuseStep 941475 = 1412213) B1412213
theorem B1007011 : Blo 940584 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B2121137 : Blo 940584 2121137 := bstep (se 2 (by rfl) ⟨795426, by rfl⟩ : syracuseStep 2121137 = 1590853) B1590853
theorem B941491 : Blo 940584 941491 := bstep (se 1 (by rfl) ⟨706118, by rfl⟩ : syracuseStep 941491 = 1412237) B1412237
theorem B941507 : Blo 940584 941507 := bstep (se 1 (by rfl) ⟨706130, by rfl⟩ : syracuseStep 941507 = 1412261) B1412261
theorem B2121155 : Blo 940584 2121155 := bstep (se 1 (by rfl) ⟨1590866, by rfl⟩ : syracuseStep 2121155 = 3181733) B3181733
theorem B941523 : Blo 940584 941523 := bstep (se 1 (by rfl) ⟨706142, by rfl⟩ : syracuseStep 941523 = 1412285) B1412285
theorem B941539 : Blo 940584 941539 := bstep (se 1 (by rfl) ⟨706154, by rfl⟩ : syracuseStep 941539 = 1412309) B1412309
theorem B941555 : Blo 940584 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B941571 : Blo 940584 941571 := bstep (se 1 (by rfl) ⟨706178, by rfl⟩ : syracuseStep 941571 = 1412357) B1412357
theorem B2448899 : Blo 940584 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B941587 : Blo 940584 941587 := bstep (se 1 (by rfl) ⟨706190, by rfl⟩ : syracuseStep 941587 = 1412381) B1412381
theorem B941603 : Blo 940584 941603 := bstep (se 1 (by rfl) ⟨706202, by rfl⟩ : syracuseStep 941603 = 1412405) B1412405
theorem B941619 : Blo 940584 941619 := bstep (se 1 (by rfl) ⟨706214, by rfl⟩ : syracuseStep 941619 = 1412429) B1412429
theorem B941635 : Blo 940584 941635 := bstep (se 1 (by rfl) ⟨706226, by rfl⟩ : syracuseStep 941635 = 1412453) B1412453
theorem B1433155 : Blo 940584 1433155 := bstep (se 1 (by rfl) ⟨1074866, by rfl⟩ : syracuseStep 1433155 = 2149733) B2149733
theorem B941651 : Blo 940584 941651 := bstep (se 1 (by rfl) ⟨706238, by rfl⟩ : syracuseStep 941651 = 1412477) B1412477
theorem B941667 : Blo 940584 941667 := bstep (se 1 (by rfl) ⟨706250, by rfl⟩ : syracuseStep 941667 = 1412501) B1412501
theorem B941683 : Blo 940584 941683 := bstep (se 1 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 941683 = 1412525) B1412525
theorem B941699 : Blo 940584 941699 := bstep (se 1 (by rfl) ⟨706274, by rfl⟩ : syracuseStep 941699 = 1412549) B1412549
theorem B941715 : Blo 940584 941715 := bstep (se 1 (by rfl) ⟨706286, by rfl⟩ : syracuseStep 941715 = 1412573) B1412573
theorem B941731 : Blo 940584 941731 := bstep (se 1 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 941731 = 1412597) B1412597
theorem B2547377 : Blo 940584 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B941747 : Blo 940584 941747 := bstep (se 1 (by rfl) ⟨706310, by rfl⟩ : syracuseStep 941747 = 1412621) B1412621
theorem B941763 : Blo 940584 941763 := bstep (se 1 (by rfl) ⟨706322, by rfl⟩ : syracuseStep 941763 = 1412645) B1412645
theorem B2121425 : Blo 940584 2121425 := bstep (se 2 (by rfl) ⟨795534, by rfl⟩ : syracuseStep 2121425 = 1591069) B1591069
theorem B941779 : Blo 940584 941779 := bstep (se 1 (by rfl) ⟨706334, by rfl⟩ : syracuseStep 941779 = 1412669) B1412669
theorem B941795 : Blo 940584 941795 := bstep (se 1 (by rfl) ⟨706346, by rfl⟩ : syracuseStep 941795 = 1412693) B1412693
theorem B2121443 : Blo 940584 2121443 := bstep (se 1 (by rfl) ⟨1591082, by rfl⟩ : syracuseStep 2121443 = 3182165) B3182165
theorem B941811 : Blo 940584 941811 := bstep (se 1 (by rfl) ⟨706358, by rfl⟩ : syracuseStep 941811 = 1412717) B1412717
theorem B941827 : Blo 940584 941827 := bstep (se 1 (by rfl) ⟨706370, by rfl⟩ : syracuseStep 941827 = 1412741) B1412741
theorem B941843 : Blo 940584 941843 := bstep (se 1 (by rfl) ⟨706382, by rfl⟩ : syracuseStep 941843 = 1412765) B1412765
theorem B941859 : Blo 940584 941859 := bstep (se 1 (by rfl) ⟨706394, by rfl⟩ : syracuseStep 941859 = 1412789) B1412789
theorem B3825443 : Blo 940584 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B6446897 : Blo 940584 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B941875 : Blo 940584 941875 := bstep (se 1 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 941875 = 1412813) B1412813
theorem B941891 : Blo 940584 941891 := bstep (se 1 (by rfl) ⟨706418, by rfl⟩ : syracuseStep 941891 = 1412837) B1412837
theorem B2678609 : Blo 940584 2678609 := bstep (se 2 (by rfl) ⟨1004478, by rfl⟩ : syracuseStep 2678609 = 2008957) B2008957
theorem B941907 : Blo 940584 941907 := bstep (se 1 (by rfl) ⟨706430, by rfl⟩ : syracuseStep 941907 = 1412861) B1412861
theorem B941923 : Blo 940584 941923 := bstep (se 1 (by rfl) ⟨706442, by rfl⟩ : syracuseStep 941923 = 1412885) B1412885
theorem B941939 : Blo 940584 941939 := bstep (se 1 (by rfl) ⟨706454, by rfl⟩ : syracuseStep 941939 = 1412909) B1412909
theorem B941955 : Blo 940584 941955 := bstep (se 1 (by rfl) ⟨706466, by rfl⟩ : syracuseStep 941955 = 1412933) B1412933
theorem B941971 : Blo 940584 941971 := bstep (se 1 (by rfl) ⟨706478, by rfl⟩ : syracuseStep 941971 = 1412957) B1412957
theorem B941987 : Blo 940584 941987 := bstep (se 1 (by rfl) ⟨706490, by rfl⟩ : syracuseStep 941987 = 1412981) B1412981
theorem B942003 : Blo 940584 942003 := bstep (se 1 (by rfl) ⟨706502, by rfl⟩ : syracuseStep 942003 = 1413005) B1413005
theorem B942019 : Blo 940584 942019 := bstep (se 1 (by rfl) ⟨706514, by rfl⟩ : syracuseStep 942019 = 1413029) B1413029
theorem B942035 : Blo 940584 942035 := bstep (se 1 (by rfl) ⟨706526, by rfl⟩ : syracuseStep 942035 = 1413053) B1413053
theorem B942051 : Blo 940584 942051 := bstep (se 1 (by rfl) ⟨706538, by rfl⟩ : syracuseStep 942051 = 1413077) B1413077
theorem B2121713 : Blo 940584 2121713 := bstep (se 2 (by rfl) ⟨795642, by rfl⟩ : syracuseStep 2121713 = 1591285) B1591285
theorem B4775921 : Blo 940584 4775921 := bstep (se 2 (by rfl) ⟨1790970, by rfl⟩ : syracuseStep 4775921 = 3581941) B3581941
theorem B942067 : Blo 940584 942067 := bstep (se 1 (by rfl) ⟨706550, by rfl⟩ : syracuseStep 942067 = 1413101) B1413101
theorem B942083 : Blo 940584 942083 := bstep (se 1 (by rfl) ⟨706562, by rfl⟩ : syracuseStep 942083 = 1413125) B1413125
theorem B2121731 : Blo 940584 2121731 := bstep (se 1 (by rfl) ⟨1591298, by rfl⟩ : syracuseStep 2121731 = 3182597) B3182597
theorem B7168013 : Blo 940584 7168013 := bstep (se 3 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 7168013 = 2688005) B2688005
theorem B942099 : Blo 940584 942099 := bstep (se 1 (by rfl) ⟨706574, by rfl⟩ : syracuseStep 942099 = 1413149) B1413149
theorem B1007635 : Blo 940584 1007635 := bstep (se 1 (by rfl) ⟨755726, by rfl⟩ : syracuseStep 1007635 = 1511453) B1511453
theorem B942115 : Blo 940584 942115 := bstep (se 1 (by rfl) ⟨706586, by rfl⟩ : syracuseStep 942115 = 1413173) B1413173
theorem B942131 : Blo 940584 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B942147 : Blo 940584 942147 := bstep (se 1 (by rfl) ⟨706610, by rfl⟩ : syracuseStep 942147 = 1413221) B1413221
theorem B942163 : Blo 940584 942163 := bstep (se 1 (by rfl) ⟨706622, by rfl⟩ : syracuseStep 942163 = 1413245) B1413245
theorem B942179 : Blo 940584 942179 := bstep (se 1 (by rfl) ⟨706634, by rfl⟩ : syracuseStep 942179 = 1413269) B1413269
theorem B942195 : Blo 940584 942195 := bstep (se 1 (by rfl) ⟨706646, by rfl⟩ : syracuseStep 942195 = 1413293) B1413293
theorem B942211 : Blo 940584 942211 := bstep (se 1 (by rfl) ⟨706658, by rfl⟩ : syracuseStep 942211 = 1413317) B1413317
theorem B942227 : Blo 940584 942227 := bstep (se 1 (by rfl) ⟨706670, by rfl⟩ : syracuseStep 942227 = 1413341) B1413341
theorem B942243 : Blo 940584 942243 := bstep (se 1 (by rfl) ⟨706682, by rfl⟩ : syracuseStep 942243 = 1413365) B1413365
theorem B942259 : Blo 940584 942259 := bstep (se 1 (by rfl) ⟨706694, by rfl⟩ : syracuseStep 942259 = 1413389) B1413389
theorem B942275 : Blo 940584 942275 := bstep (se 1 (by rfl) ⟨706706, by rfl⟩ : syracuseStep 942275 = 1413413) B1413413
theorem B942291 : Blo 940584 942291 := bstep (se 1 (by rfl) ⟨706718, by rfl⟩ : syracuseStep 942291 = 1413437) B1413437
theorem B942307 : Blo 940584 942307 := bstep (se 1 (by rfl) ⟨706730, by rfl⟩ : syracuseStep 942307 = 1413461) B1413461
theorem B2384113 : Blo 940584 2384113 := bstep (se 2 (by rfl) ⟨894042, by rfl⟩ : syracuseStep 2384113 = 1788085) B1788085
theorem B942323 : Blo 940584 942323 := bstep (se 1 (by rfl) ⟨706742, by rfl⟩ : syracuseStep 942323 = 1413485) B1413485
theorem B942339 : Blo 940584 942339 := bstep (se 1 (by rfl) ⟨706754, by rfl⟩ : syracuseStep 942339 = 1413509) B1413509
theorem B2122001 : Blo 940584 2122001 := bstep (se 2 (by rfl) ⟨795750, by rfl⟩ : syracuseStep 2122001 = 1591501) B1591501
theorem B942355 : Blo 940584 942355 := bstep (se 1 (by rfl) ⟨706766, by rfl⟩ : syracuseStep 942355 = 1413533) B1413533
theorem B25747733 : Blo 940584 25747733 := bstep (se 6 (by rfl) ⟨603462, by rfl⟩ : syracuseStep 25747733 = 1206925) B1206925
theorem B942371 : Blo 940584 942371 := bstep (se 1 (by rfl) ⟨706778, by rfl⟩ : syracuseStep 942371 = 1413557) B1413557
theorem B2122019 : Blo 940584 2122019 := bstep (se 1 (by rfl) ⟨1591514, by rfl⟩ : syracuseStep 2122019 = 3183029) B3183029
theorem B942387 : Blo 940584 942387 := bstep (se 1 (by rfl) ⟨706790, by rfl⟩ : syracuseStep 942387 = 1413581) B1413581
theorem B942403 : Blo 940584 942403 := bstep (se 1 (by rfl) ⟨706802, by rfl⟩ : syracuseStep 942403 = 1413605) B1413605
theorem B942419 : Blo 940584 942419 := bstep (se 1 (by rfl) ⟨706814, by rfl⟩ : syracuseStep 942419 = 1413629) B1413629
theorem B942435 : Blo 940584 942435 := bstep (se 1 (by rfl) ⟨706826, by rfl⟩ : syracuseStep 942435 = 1413653) B1413653
theorem B942451 : Blo 940584 942451 := bstep (se 1 (by rfl) ⟨706838, by rfl⟩ : syracuseStep 942451 = 1413677) B1413677
theorem B942467 : Blo 940584 942467 := bstep (se 1 (by rfl) ⟨706850, by rfl⟩ : syracuseStep 942467 = 1413701) B1413701
theorem B942483 : Blo 940584 942483 := bstep (se 1 (by rfl) ⟨706862, by rfl⟩ : syracuseStep 942483 = 1413725) B1413725
theorem B1532321 : Blo 940584 1532321 := bstep (se 2 (by rfl) ⟨574620, by rfl⟩ : syracuseStep 1532321 = 1149241) B1149241
theorem B942499 : Blo 940584 942499 := bstep (se 1 (by rfl) ⟨706874, by rfl⟩ : syracuseStep 942499 = 1413749) B1413749
theorem B942515 : Blo 940584 942515 := bstep (se 1 (by rfl) ⟨706886, by rfl⟩ : syracuseStep 942515 = 1413773) B1413773
theorem B942531 : Blo 940584 942531 := bstep (se 1 (by rfl) ⟨706898, by rfl⟩ : syracuseStep 942531 = 1413797) B1413797
theorem B942547 : Blo 940584 942547 := bstep (se 1 (by rfl) ⟨706910, by rfl⟩ : syracuseStep 942547 = 1413821) B1413821
theorem B942563 : Blo 940584 942563 := bstep (se 1 (by rfl) ⟨706922, by rfl⟩ : syracuseStep 942563 = 1413845) B1413845
theorem B3400163 : Blo 940584 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B2679281 : Blo 940584 2679281 := bstep (se 2 (by rfl) ⟨1004730, by rfl⟩ : syracuseStep 2679281 = 2009461) B2009461
theorem B942579 : Blo 940584 942579 := bstep (se 1 (by rfl) ⟨706934, by rfl⟩ : syracuseStep 942579 = 1413869) B1413869
theorem B2384387 : Blo 940584 2384387 := bstep (se 1 (by rfl) ⟨1788290, by rfl⟩ : syracuseStep 2384387 = 3576581) B3576581
theorem B942595 : Blo 940584 942595 := bstep (se 1 (by rfl) ⟨706946, by rfl⟩ : syracuseStep 942595 = 1413893) B1413893
theorem B942611 : Blo 940584 942611 := bstep (se 1 (by rfl) ⟨706958, by rfl⟩ : syracuseStep 942611 = 1413917) B1413917
theorem B942627 : Blo 940584 942627 := bstep (se 1 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 942627 = 1413941) B1413941
theorem B2122289 : Blo 940584 2122289 := bstep (se 2 (by rfl) ⟨795858, by rfl⟩ : syracuseStep 2122289 = 1591717) B1591717
theorem B942643 : Blo 940584 942643 := bstep (se 1 (by rfl) ⟨706982, by rfl⟩ : syracuseStep 942643 = 1413965) B1413965
theorem B942659 : Blo 940584 942659 := bstep (se 1 (by rfl) ⟨706994, by rfl⟩ : syracuseStep 942659 = 1413989) B1413989
theorem B2122307 : Blo 940584 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B942675 : Blo 940584 942675 := bstep (se 1 (by rfl) ⟨707006, by rfl⟩ : syracuseStep 942675 = 1414013) B1414013
theorem B942691 : Blo 940584 942691 := bstep (se 1 (by rfl) ⟨707018, by rfl⟩ : syracuseStep 942691 = 1414037) B1414037
theorem B942707 : Blo 940584 942707 := bstep (se 1 (by rfl) ⟨707030, by rfl⟩ : syracuseStep 942707 = 1414061) B1414061
theorem B942723 : Blo 940584 942723 := bstep (se 1 (by rfl) ⟨707042, by rfl⟩ : syracuseStep 942723 = 1414085) B1414085
theorem B942739 : Blo 940584 942739 := bstep (se 1 (by rfl) ⟨707054, by rfl⟩ : syracuseStep 942739 = 1414109) B1414109
theorem B942755 : Blo 940584 942755 := bstep (se 1 (by rfl) ⟨707066, by rfl⟩ : syracuseStep 942755 = 1414133) B1414133
theorem B942771 : Blo 940584 942771 := bstep (se 1 (by rfl) ⟨707078, by rfl⟩ : syracuseStep 942771 = 1414157) B1414157
theorem B2384579 : Blo 940584 2384579 := bstep (se 1 (by rfl) ⟨1788434, by rfl⟩ : syracuseStep 2384579 = 3576869) B3576869
theorem B942787 : Blo 940584 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B942803 : Blo 940584 942803 := bstep (se 1 (by rfl) ⟨707102, by rfl⟩ : syracuseStep 942803 = 1414205) B1414205
theorem B942819 : Blo 940584 942819 := bstep (se 1 (by rfl) ⟨707114, by rfl⟩ : syracuseStep 942819 = 1414229) B1414229
theorem B942835 : Blo 940584 942835 := bstep (se 1 (by rfl) ⟨707126, by rfl⟩ : syracuseStep 942835 = 1414253) B1414253
theorem B942851 : Blo 940584 942851 := bstep (se 1 (by rfl) ⟨707138, by rfl⟩ : syracuseStep 942851 = 1414277) B1414277
theorem B5366533 : Blo 940584 5366533 := bstep (se 4 (by rfl) ⟨503112, by rfl⟩ : syracuseStep 5366533 = 1006225) B1006225
theorem B5104397 : Blo 940584 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B942867 : Blo 940584 942867 := bstep (se 1 (by rfl) ⟨707150, by rfl⟩ : syracuseStep 942867 = 1414301) B1414301
theorem B942883 : Blo 940584 942883 := bstep (se 1 (by rfl) ⟨707162, by rfl⟩ : syracuseStep 942883 = 1414325) B1414325
theorem B942899 : Blo 940584 942899 := bstep (se 1 (by rfl) ⟨707174, by rfl⟩ : syracuseStep 942899 = 1414349) B1414349
theorem B1532737 : Blo 940584 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B942915 : Blo 940584 942915 := bstep (se 1 (by rfl) ⟨707186, by rfl⟩ : syracuseStep 942915 = 1414373) B1414373
theorem B3269453 : Blo 940584 3269453 := bstep (se 3 (by rfl) ⟨613022, by rfl⟩ : syracuseStep 3269453 = 1226045) B1226045
theorem B2122577 : Blo 940584 2122577 := bstep (se 2 (by rfl) ⟨795966, by rfl⟩ : syracuseStep 2122577 = 1591933) B1591933
theorem B942931 : Blo 940584 942931 := bstep (se 1 (by rfl) ⟨707198, by rfl⟩ : syracuseStep 942931 = 1414397) B1414397
theorem B942947 : Blo 940584 942947 := bstep (se 1 (by rfl) ⟨707210, by rfl⟩ : syracuseStep 942947 = 1414421) B1414421
theorem B2122595 : Blo 940584 2122595 := bstep (se 1 (by rfl) ⟨1591946, by rfl⟩ : syracuseStep 2122595 = 3183893) B3183893
theorem B942963 : Blo 940584 942963 := bstep (se 1 (by rfl) ⟨707222, by rfl⟩ : syracuseStep 942963 = 1414445) B1414445
theorem B942979 : Blo 940584 942979 := bstep (se 1 (by rfl) ⟨707234, by rfl⟩ : syracuseStep 942979 = 1414469) B1414469
theorem B942995 : Blo 940584 942995 := bstep (se 1 (by rfl) ⟨707246, by rfl⟩ : syracuseStep 942995 = 1414493) B1414493
theorem B5235619 : Blo 940584 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B943011 : Blo 940584 943011 := bstep (se 1 (by rfl) ⟨707258, by rfl⟩ : syracuseStep 943011 = 1414517) B1414517
theorem B943027 : Blo 940584 943027 := bstep (se 1 (by rfl) ⟨707270, by rfl⟩ : syracuseStep 943027 = 1414541) B1414541
theorem B943043 : Blo 940584 943043 := bstep (se 1 (by rfl) ⟨707282, by rfl⟩ : syracuseStep 943043 = 1414565) B1414565
theorem B943059 : Blo 940584 943059 := bstep (se 1 (by rfl) ⟨707294, by rfl⟩ : syracuseStep 943059 = 1414589) B1414589
theorem B943075 : Blo 940584 943075 := bstep (se 1 (by rfl) ⟨707306, by rfl⟩ : syracuseStep 943075 = 1414613) B1414613
theorem B943091 : Blo 940584 943091 := bstep (se 1 (by rfl) ⟨707318, by rfl⟩ : syracuseStep 943091 = 1414637) B1414637
theorem B2548739 : Blo 940584 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B943107 : Blo 940584 943107 := bstep (se 1 (by rfl) ⟨707330, by rfl⟩ : syracuseStep 943107 = 1414661) B1414661
theorem B943123 : Blo 940584 943123 := bstep (se 1 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 943123 = 1414685) B1414685
theorem B943139 : Blo 940584 943139 := bstep (se 1 (by rfl) ⟨707354, by rfl⟩ : syracuseStep 943139 = 1414709) B1414709
theorem B943155 : Blo 940584 943155 := bstep (se 1 (by rfl) ⟨707366, by rfl⟩ : syracuseStep 943155 = 1414733) B1414733
theorem B943171 : Blo 940584 943171 := bstep (se 1 (by rfl) ⟨707378, by rfl⟩ : syracuseStep 943171 = 1414757) B1414757
theorem B2548817 : Blo 940584 2548817 := bstep (se 2 (by rfl) ⟨955806, by rfl⟩ : syracuseStep 2548817 = 1911613) B1911613
theorem B943187 : Blo 940584 943187 := bstep (se 1 (by rfl) ⟨707390, by rfl⟩ : syracuseStep 943187 = 1414781) B1414781
theorem B943203 : Blo 940584 943203 := bstep (se 1 (by rfl) ⟨707402, by rfl⟩ : syracuseStep 943203 = 1414805) B1414805
theorem B2122865 : Blo 940584 2122865 := bstep (se 2 (by rfl) ⟨796074, by rfl⟩ : syracuseStep 2122865 = 1592149) B1592149
theorem B943219 : Blo 940584 943219 := bstep (se 1 (by rfl) ⟨707414, by rfl⟩ : syracuseStep 943219 = 1414829) B1414829
theorem B943235 : Blo 940584 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B2122883 : Blo 940584 2122883 := bstep (se 1 (by rfl) ⟨1592162, by rfl⟩ : syracuseStep 2122883 = 3184325) B3184325
theorem B8053901 : Blo 940584 8053901 := bstep (se 3 (by rfl) ⟨1510106, by rfl⟩ : syracuseStep 8053901 = 3020213) B3020213
theorem B943251 : Blo 940584 943251 := bstep (se 1 (by rfl) ⟨707438, by rfl⟩ : syracuseStep 943251 = 1414877) B1414877
theorem B943267 : Blo 940584 943267 := bstep (se 1 (by rfl) ⟨707450, by rfl⟩ : syracuseStep 943267 = 1414901) B1414901
theorem B943283 : Blo 940584 943283 := bstep (se 1 (by rfl) ⟨707462, by rfl⟩ : syracuseStep 943283 = 1414925) B1414925
theorem B943299 : Blo 940584 943299 := bstep (se 1 (by rfl) ⟨707474, by rfl⟩ : syracuseStep 943299 = 1414949) B1414949
theorem B943315 : Blo 940584 943315 := bstep (se 1 (by rfl) ⟨707486, by rfl⟩ : syracuseStep 943315 = 1414973) B1414973
theorem B943331 : Blo 940584 943331 := bstep (se 1 (by rfl) ⟨707498, by rfl⟩ : syracuseStep 943331 = 1414997) B1414997
theorem B943347 : Blo 940584 943347 := bstep (se 1 (by rfl) ⟨707510, by rfl⟩ : syracuseStep 943347 = 1415021) B1415021
theorem B2680067 : Blo 940584 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B943363 : Blo 940584 943363 := bstep (se 1 (by rfl) ⟨707522, by rfl⟩ : syracuseStep 943363 = 1415045) B1415045
theorem B943379 : Blo 940584 943379 := bstep (se 1 (by rfl) ⟨707534, by rfl⟩ : syracuseStep 943379 = 1415069) B1415069
theorem B943395 : Blo 940584 943395 := bstep (se 1 (by rfl) ⟨707546, by rfl⟩ : syracuseStep 943395 = 1415093) B1415093
theorem B943411 : Blo 940584 943411 := bstep (se 1 (by rfl) ⟨707558, by rfl⟩ : syracuseStep 943411 = 1415117) B1415117
theorem B943427 : Blo 940584 943427 := bstep (se 1 (by rfl) ⟨707570, by rfl⟩ : syracuseStep 943427 = 1415141) B1415141
theorem B5432645 : Blo 940584 5432645 := bstep (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) B1018621
theorem B943443 : Blo 940584 943443 := bstep (se 1 (by rfl) ⟨707582, by rfl⟩ : syracuseStep 943443 = 1415165) B1415165
theorem B943459 : Blo 940584 943459 := bstep (se 1 (by rfl) ⟨707594, by rfl⟩ : syracuseStep 943459 = 1415189) B1415189
theorem B1434979 : Blo 940584 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B943475 : Blo 940584 943475 := bstep (se 1 (by rfl) ⟨707606, by rfl⟩ : syracuseStep 943475 = 1415213) B1415213
theorem B943491 : Blo 940584 943491 := bstep (se 1 (by rfl) ⟨707618, by rfl⟩ : syracuseStep 943491 = 1415237) B1415237
theorem B2123153 : Blo 940584 2123153 := bstep (se 2 (by rfl) ⟨796182, by rfl⟩ : syracuseStep 2123153 = 1592365) B1592365
theorem B943507 : Blo 940584 943507 := bstep (se 1 (by rfl) ⟨707630, by rfl⟩ : syracuseStep 943507 = 1415261) B1415261
theorem B943523 : Blo 940584 943523 := bstep (se 1 (by rfl) ⟨707642, by rfl⟩ : syracuseStep 943523 = 1415285) B1415285
theorem B2123171 : Blo 940584 2123171 := bstep (se 1 (by rfl) ⟨1592378, by rfl⟩ : syracuseStep 2123171 = 3184757) B3184757
theorem B4777379 : Blo 940584 4777379 := bstep (se 1 (by rfl) ⟨3583034, by rfl⟩ : syracuseStep 4777379 = 7166069) B7166069
theorem B943539 : Blo 940584 943539 := bstep (se 1 (by rfl) ⟨707654, by rfl⟩ : syracuseStep 943539 = 1415309) B1415309
theorem B943555 : Blo 940584 943555 := bstep (se 1 (by rfl) ⟨707666, by rfl⟩ : syracuseStep 943555 = 1415333) B1415333
theorem B943571 : Blo 940584 943571 := bstep (se 1 (by rfl) ⟨707678, by rfl⟩ : syracuseStep 943571 = 1415357) B1415357
theorem B943587 : Blo 940584 943587 := bstep (se 1 (by rfl) ⟨707690, by rfl⟩ : syracuseStep 943587 = 1415381) B1415381
theorem B943603 : Blo 940584 943603 := bstep (se 1 (by rfl) ⟨707702, by rfl⟩ : syracuseStep 943603 = 1415405) B1415405
theorem B943619 : Blo 940584 943619 := bstep (se 1 (by rfl) ⟨707714, by rfl⟩ : syracuseStep 943619 = 1415429) B1415429
theorem B943635 : Blo 940584 943635 := bstep (se 1 (by rfl) ⟨707726, by rfl⟩ : syracuseStep 943635 = 1415453) B1415453
theorem B943651 : Blo 940584 943651 := bstep (se 1 (by rfl) ⟨707738, by rfl⟩ : syracuseStep 943651 = 1415477) B1415477
theorem B943667 : Blo 940584 943667 := bstep (se 1 (by rfl) ⟨707750, by rfl⟩ : syracuseStep 943667 = 1415501) B1415501
theorem B943683 : Blo 940584 943683 := bstep (se 1 (by rfl) ⟨707762, by rfl⟩ : syracuseStep 943683 = 1415525) B1415525
theorem B2680397 : Blo 940584 2680397 := bstep (se 3 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 2680397 = 1005149) B1005149
theorem B943699 : Blo 940584 943699 := bstep (se 1 (by rfl) ⟨707774, by rfl⟩ : syracuseStep 943699 = 1415549) B1415549
theorem B943715 : Blo 940584 943715 := bstep (se 1 (by rfl) ⟨707786, by rfl⟩ : syracuseStep 943715 = 1415573) B1415573
theorem B2385521 : Blo 940584 2385521 := bstep (se 2 (by rfl) ⟨894570, by rfl⟩ : syracuseStep 2385521 = 1789141) B1789141
theorem B943731 : Blo 940584 943731 := bstep (se 1 (by rfl) ⟨707798, by rfl⟩ : syracuseStep 943731 = 1415597) B1415597
theorem B943747 : Blo 940584 943747 := bstep (se 1 (by rfl) ⟨707810, by rfl⟩ : syracuseStep 943747 = 1415621) B1415621
theorem B2680465 : Blo 940584 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B943763 : Blo 940584 943763 := bstep (se 1 (by rfl) ⟨707822, by rfl⟩ : syracuseStep 943763 = 1415645) B1415645
theorem B2385571 : Blo 940584 2385571 := bstep (se 1 (by rfl) ⟨1789178, by rfl⟩ : syracuseStep 2385571 = 3578357) B3578357
theorem B943779 : Blo 940584 943779 := bstep (se 1 (by rfl) ⟨707834, by rfl⟩ : syracuseStep 943779 = 1415669) B1415669
theorem B2123441 : Blo 940584 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B943795 : Blo 940584 943795 := bstep (se 1 (by rfl) ⟨707846, by rfl⟩ : syracuseStep 943795 = 1415693) B1415693
theorem B2123459 : Blo 940584 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B943811 : Blo 940584 943811 := bstep (se 1 (by rfl) ⟨707858, by rfl⟩ : syracuseStep 943811 = 1415717) B1415717
theorem B943827 : Blo 940584 943827 := bstep (se 1 (by rfl) ⟨707870, by rfl⟩ : syracuseStep 943827 = 1415741) B1415741
theorem B943843 : Blo 940584 943843 := bstep (se 1 (by rfl) ⟨707882, by rfl⟩ : syracuseStep 943843 = 1415765) B1415765
theorem B943859 : Blo 940584 943859 := bstep (se 1 (by rfl) ⟨707894, by rfl⟩ : syracuseStep 943859 = 1415789) B1415789
theorem B943875 : Blo 940584 943875 := bstep (se 1 (by rfl) ⟨707906, by rfl⟩ : syracuseStep 943875 = 1415813) B1415813
theorem B943891 : Blo 940584 943891 := bstep (se 1 (by rfl) ⟨707918, by rfl⟩ : syracuseStep 943891 = 1415837) B1415837
theorem B943907 : Blo 940584 943907 := bstep (se 1 (by rfl) ⟨707930, by rfl⟩ : syracuseStep 943907 = 1415861) B1415861
theorem B2385713 : Blo 940584 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B943923 : Blo 940584 943923 := bstep (se 1 (by rfl) ⟨707942, by rfl⟩ : syracuseStep 943923 = 1415885) B1415885
theorem B943939 : Blo 940584 943939 := bstep (se 1 (by rfl) ⟨707954, by rfl⟩ : syracuseStep 943939 = 1415909) B1415909
theorem B943955 : Blo 940584 943955 := bstep (se 1 (by rfl) ⟨707966, by rfl⟩ : syracuseStep 943955 = 1415933) B1415933
theorem B2549603 : Blo 940584 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B943971 : Blo 940584 943971 := bstep (se 1 (by rfl) ⟨707978, by rfl⟩ : syracuseStep 943971 = 1415957) B1415957
theorem B943987 : Blo 940584 943987 := bstep (se 1 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 943987 = 1415981) B1415981
theorem B944003 : Blo 940584 944003 := bstep (se 1 (by rfl) ⟨708002, by rfl⟩ : syracuseStep 944003 = 1416005) B1416005
theorem B944019 : Blo 940584 944019 := bstep (se 1 (by rfl) ⟨708014, by rfl⟩ : syracuseStep 944019 = 1416029) B1416029
theorem B2680739 : Blo 940584 2680739 := bstep (se 1 (by rfl) ⟨2010554, by rfl⟩ : syracuseStep 2680739 = 4021109) B4021109
theorem B944035 : Blo 940584 944035 := bstep (se 1 (by rfl) ⟨708026, by rfl⟩ : syracuseStep 944035 = 1416053) B1416053
theorem B2549681 : Blo 940584 2549681 := bstep (se 2 (by rfl) ⟨956130, by rfl⟩ : syracuseStep 2549681 = 1912261) B1912261
theorem B944051 : Blo 940584 944051 := bstep (se 1 (by rfl) ⟨708038, by rfl⟩ : syracuseStep 944051 = 1416077) B1416077
theorem B944067 : Blo 940584 944067 := bstep (se 1 (by rfl) ⟨708050, by rfl⟩ : syracuseStep 944067 = 1416101) B1416101
theorem B2123729 : Blo 940584 2123729 := bstep (se 2 (by rfl) ⟨796398, by rfl⟩ : syracuseStep 2123729 = 1592797) B1592797
theorem B944083 : Blo 940584 944083 := bstep (se 1 (by rfl) ⟨708062, by rfl⟩ : syracuseStep 944083 = 1416125) B1416125
theorem B2123747 : Blo 940584 2123747 := bstep (se 1 (by rfl) ⟨1592810, by rfl⟩ : syracuseStep 2123747 = 3185621) B3185621
theorem B944099 : Blo 940584 944099 := bstep (se 1 (by rfl) ⟨708074, by rfl⟩ : syracuseStep 944099 = 1416149) B1416149
theorem B944115 : Blo 940584 944115 := bstep (se 1 (by rfl) ⟨708086, by rfl⟩ : syracuseStep 944115 = 1416173) B1416173
theorem B944131 : Blo 940584 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B944147 : Blo 940584 944147 := bstep (se 1 (by rfl) ⟨708110, by rfl⟩ : syracuseStep 944147 = 1416221) B1416221
theorem B944163 : Blo 940584 944163 := bstep (se 1 (by rfl) ⟨708122, by rfl⟩ : syracuseStep 944163 = 1416245) B1416245
theorem B1271857 : Blo 940584 1271857 := bstep (se 2 (by rfl) ⟨476946, by rfl⟩ : syracuseStep 1271857 = 953893) B953893
theorem B944179 : Blo 940584 944179 := bstep (se 1 (by rfl) ⟨708134, by rfl⟩ : syracuseStep 944179 = 1416269) B1416269
theorem B944195 : Blo 940584 944195 := bstep (se 1 (by rfl) ⟨708146, by rfl⟩ : syracuseStep 944195 = 1416293) B1416293
theorem B944211 : Blo 940584 944211 := bstep (se 1 (by rfl) ⟨708158, by rfl⟩ : syracuseStep 944211 = 1416317) B1416317
theorem B944227 : Blo 940584 944227 := bstep (se 1 (by rfl) ⟨708170, by rfl⟩ : syracuseStep 944227 = 1416341) B1416341
theorem B944243 : Blo 940584 944243 := bstep (se 1 (by rfl) ⟨708182, by rfl⟩ : syracuseStep 944243 = 1416365) B1416365
theorem B944259 : Blo 940584 944259 := bstep (se 1 (by rfl) ⟨708194, by rfl⟩ : syracuseStep 944259 = 1416389) B1416389
theorem B944275 : Blo 940584 944275 := bstep (se 1 (by rfl) ⟨708206, by rfl⟩ : syracuseStep 944275 = 1416413) B1416413
theorem B944291 : Blo 940584 944291 := bstep (se 1 (by rfl) ⟨708218, by rfl⟩ : syracuseStep 944291 = 1416437) B1416437
theorem B944307 : Blo 940584 944307 := bstep (se 1 (by rfl) ⟨708230, by rfl⟩ : syracuseStep 944307 = 1416461) B1416461
theorem B944323 : Blo 940584 944323 := bstep (se 1 (by rfl) ⟨708242, by rfl⟩ : syracuseStep 944323 = 1416485) B1416485
theorem B4024525 : Blo 940584 4024525 := bstep (se 3 (by rfl) ⟨754598, by rfl⟩ : syracuseStep 4024525 = 1509197) B1509197
theorem B4778189 : Blo 940584 4778189 := bstep (se 3 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 4778189 = 1791821) B1791821
theorem B944339 : Blo 940584 944339 := bstep (se 1 (by rfl) ⟨708254, by rfl⟩ : syracuseStep 944339 = 1416509) B1416509
theorem B944355 : Blo 940584 944355 := bstep (se 1 (by rfl) ⟨708266, by rfl⟩ : syracuseStep 944355 = 1416533) B1416533
theorem B2124017 : Blo 940584 2124017 := bstep (se 2 (by rfl) ⟨796506, by rfl⟩ : syracuseStep 2124017 = 1593013) B1593013
theorem B944371 : Blo 940584 944371 := bstep (se 1 (by rfl) ⟨708278, by rfl⟩ : syracuseStep 944371 = 1416557) B1416557
theorem B2124035 : Blo 940584 2124035 := bstep (se 1 (by rfl) ⟨1593026, by rfl⟩ : syracuseStep 2124035 = 3186053) B3186053
theorem B944387 : Blo 940584 944387 := bstep (se 1 (by rfl) ⟨708290, by rfl⟩ : syracuseStep 944387 = 1416581) B1416581
theorem B944403 : Blo 940584 944403 := bstep (se 1 (by rfl) ⟨708302, by rfl⟩ : syracuseStep 944403 = 1416605) B1416605
theorem B944419 : Blo 940584 944419 := bstep (se 1 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 944419 = 1416629) B1416629
theorem B944435 : Blo 940584 944435 := bstep (se 1 (by rfl) ⟨708326, by rfl⟩ : syracuseStep 944435 = 1416653) B1416653
theorem B944451 : Blo 940584 944451 := bstep (se 1 (by rfl) ⟨708338, by rfl⟩ : syracuseStep 944451 = 1416677) B1416677
theorem B944467 : Blo 940584 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B944483 : Blo 940584 944483 := bstep (se 1 (by rfl) ⟨708362, by rfl⟩ : syracuseStep 944483 = 1416725) B1416725
theorem B944499 : Blo 940584 944499 := bstep (se 1 (by rfl) ⟨708374, by rfl⟩ : syracuseStep 944499 = 1416749) B1416749
theorem B944515 : Blo 940584 944515 := bstep (se 1 (by rfl) ⟨708386, by rfl⟩ : syracuseStep 944515 = 1416773) B1416773
theorem B944531 : Blo 940584 944531 := bstep (se 1 (by rfl) ⟨708398, by rfl⟩ : syracuseStep 944531 = 1416797) B1416797
theorem B944547 : Blo 940584 944547 := bstep (se 1 (by rfl) ⟨708410, by rfl⟩ : syracuseStep 944547 = 1416821) B1416821
theorem B944563 : Blo 940584 944563 := bstep (se 1 (by rfl) ⟨708422, by rfl⟩ : syracuseStep 944563 = 1416845) B1416845
theorem B2419139 : Blo 940584 2419139 := bstep (se 1 (by rfl) ⟨1814354, by rfl⟩ : syracuseStep 2419139 = 3628709) B3628709
theorem B944579 : Blo 940584 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B2124305 : Blo 940584 2124305 := bstep (se 2 (by rfl) ⟨796614, by rfl⟩ : syracuseStep 2124305 = 1593229) B1593229
theorem B2124323 : Blo 940584 2124323 := bstep (se 1 (by rfl) ⟨1593242, by rfl⟩ : syracuseStep 2124323 = 3186485) B3186485
theorem B1436195 : Blo 940584 1436195 := bstep (se 1 (by rfl) ⟨1077146, by rfl⟩ : syracuseStep 1436195 = 2154293) B2154293
theorem B1698403 : Blo 940584 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1075843 : Blo 940584 1075843 := bstep (se 1 (by rfl) ⟨806882, by rfl⟩ : syracuseStep 1075843 = 1613765) B1613765
theorem B5368517 : Blo 940584 5368517 := bstep (se 4 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 5368517 = 1006597) B1006597
theorem B2681581 : Blo 940584 2681581 := bstep (se 3 (by rfl) ⟨502796, by rfl⟩ : syracuseStep 2681581 = 1005593) B1005593
theorem B2386705 : Blo 940584 2386705 := bstep (se 2 (by rfl) ⟨895014, by rfl⟩ : syracuseStep 2386705 = 1790029) B1790029
theorem B2124593 : Blo 940584 2124593 := bstep (se 2 (by rfl) ⟨796722, by rfl⟩ : syracuseStep 2124593 = 1593445) B1593445
theorem B2124611 : Blo 940584 2124611 := bstep (se 1 (by rfl) ⟨1593458, by rfl⟩ : syracuseStep 2124611 = 3186917) B3186917
theorem B7170929 : Blo 940584 7170929 := bstep (se 2 (by rfl) ⟨2689098, by rfl⟩ : syracuseStep 7170929 = 5378197) B5378197
theorem B2681741 : Blo 940584 2681741 := bstep (se 3 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 2681741 = 1005653) B1005653
theorem B2386979 : Blo 940584 2386979 := bstep (se 1 (by rfl) ⟨1790234, by rfl⟩ : syracuseStep 2386979 = 3580469) B3580469
theorem B2681923 : Blo 940584 2681923 := bstep (se 1 (by rfl) ⟨2011442, by rfl⟩ : syracuseStep 2681923 = 4022885) B4022885
theorem B2124881 : Blo 940584 2124881 := bstep (se 2 (by rfl) ⟨796830, by rfl⟩ : syracuseStep 2124881 = 1593661) B1593661
theorem B2124899 : Blo 940584 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B2387171 : Blo 940584 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B2125169 : Blo 940584 2125169 := bstep (se 2 (by rfl) ⟨796938, by rfl⟩ : syracuseStep 2125169 = 1593877) B1593877
theorem B2125187 : Blo 940584 2125187 := bstep (se 1 (by rfl) ⟨1593890, by rfl⟩ : syracuseStep 2125187 = 3187781) B3187781
theorem B1076755 : Blo 940584 1076755 := bstep (se 1 (by rfl) ⟨807566, by rfl⟩ : syracuseStep 1076755 = 1615133) B1615133
theorem B12906053 : Blo 940584 12906053 := bstep (se 4 (by rfl) ⟨1209942, by rfl⟩ : syracuseStep 12906053 = 2419885) B2419885
theorem B12054197 : Blo 940584 12054197 := bstep (se 5 (by rfl) ⟨565040, by rfl⟩ : syracuseStep 12054197 = 1130081) B1130081
theorem B13758149 : Blo 940584 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B2715491 : Blo 940584 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B1699793 : Blo 940584 1699793 := bstep (se 2 (by rfl) ⟨637422, by rfl⟩ : syracuseStep 1699793 = 1274845) B1274845
theorem B3403853 : Blo 940584 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B2388113 : Blo 940584 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B2388163 : Blo 940584 2388163 := bstep (se 1 (by rfl) ⟨1791122, by rfl⟩ : syracuseStep 2388163 = 3582245) B3582245
theorem B3174605 : Blo 940584 3174605 := bstep (se 3 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 3174605 = 1190477) B1190477
theorem B3174659 : Blo 940584 3174659 := bstep (se 1 (by rfl) ⟨2380994, by rfl⟩ : syracuseStep 3174659 = 4761989) B4761989
theorem B1339697 : Blo 940584 1339697 := bstep (se 2 (by rfl) ⟨502386, by rfl⟩ : syracuseStep 1339697 = 1004773) B1004773
theorem B2388305 : Blo 940584 2388305 := bstep (se 2 (by rfl) ⟨895614, by rfl⟩ : syracuseStep 2388305 = 1791229) B1791229
theorem B1470803 : Blo 940584 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B1339777 : Blo 940584 1339777 := bstep (se 2 (by rfl) ⟨502416, by rfl⟩ : syracuseStep 1339777 = 1004833) B1004833
theorem B2683313 : Blo 940584 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B3174929 : Blo 940584 3174929 := bstep (se 2 (by rfl) ⟨1190598, by rfl⟩ : syracuseStep 3174929 = 2381197) B2381197
theorem B24507157 : Blo 940584 24507157 := bstep (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) B1148773
theorem B5174093 : Blo 940584 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B2552717 : Blo 940584 2552717 := bstep (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) B957269
theorem B3175469 : Blo 940584 3175469 := bstep (se 3 (by rfl) ⟨595400, by rfl⟩ : syracuseStep 3175469 = 1190801) B1190801
theorem B4781105 : Blo 940584 4781105 := bstep (se 2 (by rfl) ⟨1792914, by rfl⟩ : syracuseStep 4781105 = 3585829) B3585829
theorem B3175523 : Blo 940584 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B1340563 : Blo 940584 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B1701091 : Blo 940584 1701091 := bstep (se 1 (by rfl) ⟨1275818, by rfl⟩ : syracuseStep 1701091 = 2551637) B2551637
theorem B2389297 : Blo 940584 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B2684269 : Blo 940584 2684269 := bstep (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) B1006601
theorem B3175793 : Blo 940584 3175793 := bstep (se 2 (by rfl) ⟨1190922, by rfl⟩ : syracuseStep 3175793 = 2381845) B2381845
theorem B2389571 : Blo 940584 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B2684497 : Blo 940584 2684497 := bstep (se 2 (by rfl) ⟨1006686, by rfl⟩ : syracuseStep 2684497 = 2013373) B2013373
theorem B2586221 : Blo 940584 2586221 := bstep (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) B969833
theorem B1341041 : Blo 940584 1341041 := bstep (se 2 (by rfl) ⟨502890, by rfl⟩ : syracuseStep 1341041 = 1005781) B1005781
theorem B1341155 : Blo 940584 1341155 := bstep (se 1 (by rfl) ⟨1005866, by rfl⟩ : syracuseStep 1341155 = 2011733) B2011733
theorem B2684657 : Blo 940584 2684657 := bstep (se 2 (by rfl) ⟨1006746, by rfl⟩ : syracuseStep 2684657 = 2013493) B2013493
theorem B2389763 : Blo 940584 2389763 := bstep (se 1 (by rfl) ⟨1792322, by rfl⟩ : syracuseStep 2389763 = 3584645) B3584645
theorem B1341235 : Blo 940584 1341235 := bstep (se 1 (by rfl) ⟨1005926, by rfl⟩ : syracuseStep 1341235 = 2011853) B2011853
theorem B2684771 : Blo 940584 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B3176333 : Blo 940584 3176333 := bstep (se 3 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 3176333 = 1191125) B1191125
theorem B3176387 : Blo 940584 3176387 := bstep (se 1 (by rfl) ⟨2382290, by rfl⟩ : syracuseStep 3176387 = 4764581) B4764581
theorem B3176657 : Blo 940584 3176657 := bstep (se 2 (by rfl) ⟨1191246, by rfl⟩ : syracuseStep 3176657 = 2382493) B2382493
theorem B48953621 : Blo 940584 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B1341793 : Blo 940584 1341793 := bstep (se 2 (by rfl) ⟨503172, by rfl⟩ : syracuseStep 1341793 = 1006345) B1006345
theorem B3275117 : Blo 940584 3275117 := bstep (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) B1228169
theorem B4028849 : Blo 940584 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B5372365 : Blo 940584 5372365 := bstep (se 3 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 5372365 = 2014637) B2014637
theorem B4028899 : Blo 940584 4028899 := bstep (se 1 (by rfl) ⟨3021674, by rfl⟩ : syracuseStep 4028899 = 6043349) B6043349
theorem B4520461 : Blo 940584 4520461 := bstep (se 3 (by rfl) ⟨847586, by rfl⟩ : syracuseStep 4520461 = 1695173) B1695173
theorem B2390705 : Blo 940584 2390705 := bstep (se 2 (by rfl) ⟨896514, by rfl⟩ : syracuseStep 2390705 = 1793029) B1793029
theorem B2390755 : Blo 940584 2390755 := bstep (se 1 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 2390755 = 3586133) B3586133
theorem B3177197 : Blo 940584 3177197 := bstep (se 3 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 3177197 = 1191449) B1191449
theorem B3177251 : Blo 940584 3177251 := bstep (se 1 (by rfl) ⟨2382938, by rfl⟩ : syracuseStep 3177251 = 4765877) B4765877
theorem B2685773 : Blo 940584 2685773 := bstep (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) B1007165
theorem B2390897 : Blo 940584 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B2259971 : Blo 940584 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B2685955 : Blo 940584 2685955 := bstep (se 1 (by rfl) ⟨2014466, by rfl⟩ : syracuseStep 2685955 = 4028933) B4028933
theorem B1342499 : Blo 940584 1342499 := bstep (se 1 (by rfl) ⟨1006874, by rfl⟩ : syracuseStep 1342499 = 2013749) B2013749
theorem B3177521 : Blo 940584 3177521 := bstep (se 2 (by rfl) ⟨1191570, by rfl⟩ : syracuseStep 3177521 = 2383141) B2383141
theorem B2686115 : Blo 940584 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B3439949 : Blo 940584 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B1506737 : Blo 940584 1506737 := bstep (se 2 (by rfl) ⟨565026, by rfl⟩ : syracuseStep 1506737 = 1130053) B1130053
theorem B3178061 : Blo 940584 3178061 := bstep (se 3 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 3178061 = 1191773) B1191773
theorem B3178115 : Blo 940584 3178115 := bstep (se 1 (by rfl) ⟨2383586, by rfl⟩ : syracuseStep 3178115 = 4767173) B4767173
theorem B1343137 : Blo 940584 1343137 := bstep (se 2 (by rfl) ⟨503676, by rfl⟩ : syracuseStep 1343137 = 1007353) B1007353
theorem B1343251 : Blo 940584 1343251 := bstep (se 1 (by rfl) ⟨1007438, by rfl⟩ : syracuseStep 1343251 = 2014877) B2014877
theorem B3178385 : Blo 940584 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B2260931 : Blo 940584 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B1507339 : Blo 940584 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B3571735 : Blo 940584 3571735 := bstep (se 1 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 3571735 = 5357603) B5357603
theorem B1343513 : Blo 940584 1343513 := bstep (se 2 (by rfl) ⟨503817, by rfl⟩ : syracuseStep 1343513 = 1007635) B1007635
theorem B3178547 : Blo 940584 3178547 := bstep (se 1 (by rfl) ⟨2383910, by rfl⟩ : syracuseStep 3178547 = 4767821) B4767821
theorem B3670147 : Blo 940584 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B3178817 : Blo 940584 3178817 := bstep (se 2 (by rfl) ⟨1192056, by rfl⟩ : syracuseStep 3178817 = 2384113) B2384113
theorem B2687539 : Blo 940584 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B3015319 : Blo 940584 3015319 := bstep (se 1 (by rfl) ⟨2261489, by rfl⟩ : syracuseStep 3015319 = 4522979) B4522979
theorem B1344151 : Blo 940584 1344151 := bstep (se 1 (by rfl) ⟨1008113, by rfl⟩ : syracuseStep 1344151 = 2016227) B2016227
theorem B3572525 : Blo 940584 3572525 := bstep (se 3 (by rfl) ⟨669848, by rfl⟩ : syracuseStep 3572525 = 1339697) B1339697
theorem B3179357 : Blo 940584 3179357 := bstep (se 3 (by rfl) ⟨596129, by rfl⟩ : syracuseStep 3179357 = 1192259) B1192259
theorem B1508377 : Blo 940584 1508377 := bstep (se 2 (by rfl) ⟨565641, by rfl⟩ : syracuseStep 1508377 = 1131283) B1131283
theorem B3015755 : Blo 940584 3015755 := bstep (se 1 (by rfl) ⟨2261816, by rfl⟩ : syracuseStep 3015755 = 4523633) B4523633
theorem B4031633 : Blo 940584 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B6784177 : Blo 940584 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B6980825 : Blo 940584 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1508825 : Blo 940584 1508825 := bstep (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) B1131619
theorem B27198989 : Blo 940584 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B40699523 : Blo 940584 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B3016523 : Blo 940584 3016523 := bstep (se 1 (by rfl) ⟨2262392, by rfl⟩ : syracuseStep 3016523 = 4524785) B4524785
theorem B1410905 : Blo 940584 1410905 := bstep (se 2 (by rfl) ⟨529089, by rfl⟩ : syracuseStep 1410905 = 1058179) B1058179
theorem B1574807 : Blo 940584 1574807 := bstep (se 1 (by rfl) ⟨1181105, by rfl⟩ : syracuseStep 1574807 = 2362211) B2362211
theorem B1411019 : Blo 940584 1411019 := bstep (se 1 (by rfl) ⟨1058264, by rfl⟩ : syracuseStep 1411019 = 2116529) B2116529
theorem B3180491 : Blo 940584 3180491 := bstep (se 1 (by rfl) ⟨2385368, by rfl⟩ : syracuseStep 3180491 = 4770737) B4770737
theorem B1411031 : Blo 940584 1411031 := bstep (se 1 (by rfl) ⟨1058273, by rfl⟩ : syracuseStep 1411031 = 2116547) B2116547
theorem B6784985 : Blo 940584 6784985 := bstep (se 2 (by rfl) ⟨2544369, by rfl⟩ : syracuseStep 6784985 = 5088739) B5088739
theorem B1411097 : Blo 940584 1411097 := bstep (se 2 (by rfl) ⟨529161, by rfl⟩ : syracuseStep 1411097 = 1058323) B1058323
theorem B4294721 : Blo 940584 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B4360267 : Blo 940584 4360267 := bstep (se 1 (by rfl) ⟨3270200, by rfl⟩ : syracuseStep 4360267 = 6540401) B6540401
theorem B1411211 : Blo 940584 1411211 := bstep (se 1 (by rfl) ⟨1058408, by rfl⟩ : syracuseStep 1411211 = 2116817) B2116817
theorem B1411223 : Blo 940584 1411223 := bstep (se 1 (by rfl) ⟨1058417, by rfl⟩ : syracuseStep 1411223 = 2116835) B2116835
theorem B3573953 : Blo 940584 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B1411289 : Blo 940584 1411289 := bstep (se 2 (by rfl) ⟨529233, by rfl⟩ : syracuseStep 1411289 = 1058467) B1058467
theorem B3016921 : Blo 940584 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B3180761 : Blo 940584 3180761 := bstep (se 2 (by rfl) ⟨1192785, by rfl⟩ : syracuseStep 3180761 = 2385571) B2385571
theorem B1411403 : Blo 940584 1411403 := bstep (se 1 (by rfl) ⟨1058552, by rfl⟩ : syracuseStep 1411403 = 2117105) B2117105
theorem B3017035 : Blo 940584 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B1411415 : Blo 940584 1411415 := bstep (se 1 (by rfl) ⟨1058561, by rfl⟩ : syracuseStep 1411415 = 2117123) B2117123
theorem B8063333 : Blo 940584 8063333 := bstep (se 4 (by rfl) ⟨755937, by rfl⟩ : syracuseStep 8063333 = 1511875) B1511875
theorem B1411481 : Blo 940584 1411481 := bstep (se 2 (by rfl) ⟨529305, by rfl⟩ : syracuseStep 1411481 = 1058611) B1058611
theorem B1411595 : Blo 940584 1411595 := bstep (se 1 (by rfl) ⟨1058696, by rfl⟩ : syracuseStep 1411595 = 2117393) B2117393
theorem B1018391 : Blo 940584 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B1411607 : Blo 940584 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B5376557 : Blo 940584 5376557 := bstep (se 3 (by rfl) ⟨1008104, by rfl⟩ : syracuseStep 5376557 = 2016209) B2016209
theorem B1411673 : Blo 940584 1411673 := bstep (se 2 (by rfl) ⟨529377, by rfl⟩ : syracuseStep 1411673 = 1058755) B1058755
theorem B1411787 : Blo 940584 1411787 := bstep (se 1 (by rfl) ⟨1058840, by rfl⟩ : syracuseStep 1411787 = 2117681) B2117681
theorem B1411799 : Blo 940584 1411799 := bstep (se 1 (by rfl) ⟨1058849, by rfl⟩ : syracuseStep 1411799 = 2117699) B2117699
theorem B1411865 : Blo 940584 1411865 := bstep (se 2 (by rfl) ⟨529449, by rfl⟩ : syracuseStep 1411865 = 1058899) B1058899
theorem B3017537 : Blo 940584 3017537 := bstep (se 2 (by rfl) ⟨1131576, by rfl⟩ : syracuseStep 3017537 = 2263153) B2263153
theorem B1411979 : Blo 940584 1411979 := bstep (se 1 (by rfl) ⟨1058984, by rfl⟩ : syracuseStep 1411979 = 2117969) B2117969
theorem B1411991 : Blo 940584 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B3181463 : Blo 940584 3181463 := bstep (se 1 (by rfl) ⟨2386097, by rfl⟩ : syracuseStep 3181463 = 4772195) B4772195
theorem B1412057 : Blo 940584 1412057 := bstep (se 2 (by rfl) ⟨529521, by rfl⟩ : syracuseStep 1412057 = 1059043) B1059043
theorem B1412171 : Blo 940584 1412171 := bstep (se 1 (by rfl) ⟨1059128, by rfl⟩ : syracuseStep 1412171 = 2118257) B2118257
theorem B1412183 : Blo 940584 1412183 := bstep (se 1 (by rfl) ⟨1059137, by rfl⟩ : syracuseStep 1412183 = 2118275) B2118275
theorem B1412249 : Blo 940584 1412249 := bstep (se 2 (by rfl) ⟨529593, by rfl⟩ : syracuseStep 1412249 = 1059187) B1059187
theorem B1412363 : Blo 940584 1412363 := bstep (se 1 (by rfl) ⟨1059272, by rfl⟩ : syracuseStep 1412363 = 2118545) B2118545
theorem B1412375 : Blo 940584 1412375 := bstep (se 1 (by rfl) ⟨1059281, by rfl⟩ : syracuseStep 1412375 = 2118563) B2118563
theorem B1412441 : Blo 940584 1412441 := bstep (se 2 (by rfl) ⟨529665, by rfl⟩ : syracuseStep 1412441 = 1059331) B1059331
theorem B1609111 : Blo 940584 1609111 := bstep (se 1 (by rfl) ⟨1206833, by rfl⟩ : syracuseStep 1609111 = 2413667) B2413667
theorem B3018163 : Blo 940584 3018163 := bstep (se 1 (by rfl) ⟨2263622, by rfl⟩ : syracuseStep 3018163 = 4527245) B4527245
theorem B3182003 : Blo 940584 3182003 := bstep (se 1 (by rfl) ⟨2386502, by rfl⟩ : syracuseStep 3182003 = 4773005) B4773005
theorem B1412555 : Blo 940584 1412555 := bstep (se 1 (by rfl) ⟨1059416, by rfl⟩ : syracuseStep 1412555 = 2118833) B2118833
theorem B1412567 : Blo 940584 1412567 := bstep (se 1 (by rfl) ⟨1059425, by rfl⟩ : syracuseStep 1412567 = 2118851) B2118851
theorem B2264537 : Blo 940584 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B1412633 : Blo 940584 1412633 := bstep (se 2 (by rfl) ⟨529737, by rfl⟩ : syracuseStep 1412633 = 1059475) B1059475
theorem B1019467 : Blo 940584 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B1412747 : Blo 940584 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B3575441 : Blo 940584 3575441 := bstep (se 2 (by rfl) ⟨1340790, by rfl⟩ : syracuseStep 3575441 = 2681581) B2681581
theorem B1412759 : Blo 940584 1412759 := bstep (se 1 (by rfl) ⟨1059569, by rfl⟩ : syracuseStep 1412759 = 2119139) B2119139
theorem B3182273 : Blo 940584 3182273 := bstep (se 2 (by rfl) ⟨1193352, by rfl⟩ : syracuseStep 3182273 = 2386705) B2386705
theorem B1412825 : Blo 940584 1412825 := bstep (se 2 (by rfl) ⟨529809, by rfl⟩ : syracuseStep 1412825 = 1059619) B1059619
theorem B1412939 : Blo 940584 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B1412951 : Blo 940584 1412951 := bstep (se 1 (by rfl) ⟨1059713, by rfl⟩ : syracuseStep 1412951 = 2119427) B2119427
theorem B30609251 : Blo 940584 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B1413017 : Blo 940584 1413017 := bstep (se 2 (by rfl) ⟨529881, by rfl⟩ : syracuseStep 1413017 = 1059763) B1059763
theorem B2297803 : Blo 940584 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B1413131 : Blo 940584 1413131 := bstep (se 1 (by rfl) ⟨1059848, by rfl⟩ : syracuseStep 1413131 = 2119697) B2119697
theorem B1413143 : Blo 940584 1413143 := bstep (se 1 (by rfl) ⟨1059857, by rfl⟩ : syracuseStep 1413143 = 2119715) B2119715
theorem B4034605 : Blo 940584 4034605 := bstep (se 3 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 4034605 = 1512977) B1512977
theorem B3575897 : Blo 940584 3575897 := bstep (se 2 (by rfl) ⟨1340961, by rfl⟩ : syracuseStep 3575897 = 2681923) B2681923
theorem B1413209 : Blo 940584 1413209 := bstep (se 2 (by rfl) ⟨529953, by rfl⟩ : syracuseStep 1413209 = 1059907) B1059907
theorem B5443685 : Blo 940584 5443685 := bstep (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) B1020691
theorem B13570199 : Blo 940584 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B1413323 : Blo 940584 1413323 := bstep (se 1 (by rfl) ⟨1059992, by rfl⟩ : syracuseStep 1413323 = 2119985) B2119985
theorem B1413335 : Blo 940584 1413335 := bstep (se 1 (by rfl) ⟨1060001, by rfl⟩ : syracuseStep 1413335 = 2120003) B2120003
theorem B1511639 : Blo 940584 1511639 := bstep (se 1 (by rfl) ⟨1133729, by rfl⟩ : syracuseStep 1511639 = 2267459) B2267459
theorem B3182813 : Blo 940584 3182813 := bstep (se 3 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 3182813 = 1193555) B1193555
theorem B1413401 : Blo 940584 1413401 := bstep (se 2 (by rfl) ⟨530025, by rfl⟩ : syracuseStep 1413401 = 1060051) B1060051
theorem B3576109 : Blo 940584 3576109 := bstep (se 3 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 3576109 = 1341041) B1341041
theorem B2756915 : Blo 940584 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1413515 : Blo 940584 1413515 := bstep (se 1 (by rfl) ⟨1060136, by rfl⟩ : syracuseStep 1413515 = 2120273) B2120273
theorem B1413527 : Blo 940584 1413527 := bstep (se 1 (by rfl) ⟨1060145, by rfl⟩ : syracuseStep 1413527 = 2120291) B2120291
theorem B1413593 : Blo 940584 1413593 := bstep (se 2 (by rfl) ⟨530097, by rfl⟩ : syracuseStep 1413593 = 1060195) B1060195
theorem B1610315 : Blo 940584 1610315 := bstep (se 1 (by rfl) ⟨1207736, by rfl⟩ : syracuseStep 1610315 = 2415473) B2415473
theorem B1413707 : Blo 940584 1413707 := bstep (se 1 (by rfl) ⟨1060280, by rfl⟩ : syracuseStep 1413707 = 2120561) B2120561
theorem B1413719 : Blo 940584 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B3576413 : Blo 940584 3576413 := bstep (se 3 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 3576413 = 1341155) B1341155
theorem B1413785 : Blo 940584 1413785 := bstep (se 2 (by rfl) ⟨530169, by rfl⟩ : syracuseStep 1413785 = 1060339) B1060339
theorem B1413899 : Blo 940584 1413899 := bstep (se 1 (by rfl) ⟨1060424, by rfl⟩ : syracuseStep 1413899 = 2120849) B2120849
theorem B1413911 : Blo 940584 1413911 := bstep (se 1 (by rfl) ⟨1060433, by rfl⟩ : syracuseStep 1413911 = 2120867) B2120867
theorem B1413977 : Blo 940584 1413977 := bstep (se 2 (by rfl) ⟨530241, by rfl⟩ : syracuseStep 1413977 = 1060483) B1060483
theorem B1414091 : Blo 940584 1414091 := bstep (se 1 (by rfl) ⟨1060568, by rfl⟩ : syracuseStep 1414091 = 2121137) B2121137
theorem B1414103 : Blo 940584 1414103 := bstep (se 1 (by rfl) ⟨1060577, by rfl⟩ : syracuseStep 1414103 = 2121155) B2121155
theorem B16126937 : Blo 940584 16126937 := bstep (se 2 (by rfl) ⟨6047601, by rfl⟩ : syracuseStep 16126937 = 12095203) B12095203
theorem B1414169 : Blo 940584 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B1414283 : Blo 940584 1414283 := bstep (se 1 (by rfl) ⟨1060712, by rfl⟩ : syracuseStep 1414283 = 2121425) B2121425
theorem B1414295 : Blo 940584 1414295 := bstep (se 1 (by rfl) ⟨1060721, by rfl⟩ : syracuseStep 1414295 = 2121443) B2121443
theorem B4297931 : Blo 940584 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B1414361 : Blo 940584 1414361 := bstep (se 2 (by rfl) ⟨530385, by rfl⟩ : syracuseStep 1414361 = 1060771) B1060771
theorem B3019997 : Blo 940584 3019997 := bstep (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) B1132499
theorem B1414475 : Blo 940584 1414475 := bstep (se 1 (by rfl) ⟨1060856, by rfl⟩ : syracuseStep 1414475 = 2121713) B2121713
theorem B3183947 : Blo 940584 3183947 := bstep (se 1 (by rfl) ⟨2387960, by rfl⟩ : syracuseStep 3183947 = 4775921) B4775921
theorem B1414487 : Blo 940584 1414487 := bstep (se 1 (by rfl) ⟨1060865, by rfl⟩ : syracuseStep 1414487 = 2121731) B2121731
theorem B1414553 : Blo 940584 1414553 := bstep (se 2 (by rfl) ⟨530457, by rfl⟩ : syracuseStep 1414553 = 1060915) B1060915
theorem B1414667 : Blo 940584 1414667 := bstep (se 1 (by rfl) ⟨1061000, by rfl⟩ : syracuseStep 1414667 = 2122001) B2122001
theorem B1414679 : Blo 940584 1414679 := bstep (se 1 (by rfl) ⟨1061009, by rfl⟩ : syracuseStep 1414679 = 2122019) B2122019
theorem B1414745 : Blo 940584 1414745 := bstep (se 2 (by rfl) ⟨530529, by rfl⟩ : syracuseStep 1414745 = 1061059) B1061059
theorem B3184217 : Blo 940584 3184217 := bstep (se 2 (by rfl) ⟨1194081, by rfl⟩ : syracuseStep 3184217 = 2388163) B2388163
theorem B1021547 : Blo 940584 1021547 := bstep (se 1 (by rfl) ⟨766160, by rfl⟩ : syracuseStep 1021547 = 1532321) B1532321
theorem B2266775 : Blo 940584 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B1414859 : Blo 940584 1414859 := bstep (se 1 (by rfl) ⟨1061144, by rfl⟩ : syracuseStep 1414859 = 2122289) B2122289
theorem B1414871 : Blo 940584 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B1414937 : Blo 940584 1414937 := bstep (se 2 (by rfl) ⟨530601, by rfl⟩ : syracuseStep 1414937 = 1061203) B1061203
theorem B1415051 : Blo 940584 1415051 := bstep (se 1 (by rfl) ⟨1061288, by rfl⟩ : syracuseStep 1415051 = 2122577) B2122577
theorem B1415063 : Blo 940584 1415063 := bstep (se 1 (by rfl) ⟨1061297, by rfl⟩ : syracuseStep 1415063 = 2122595) B2122595
theorem B1415129 : Blo 940584 1415129 := bstep (se 2 (by rfl) ⟨530673, by rfl⟩ : syracuseStep 1415129 = 1061347) B1061347
theorem B2299927 : Blo 940584 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B1415243 : Blo 940584 1415243 := bstep (se 1 (by rfl) ⟨1061432, by rfl⟩ : syracuseStep 1415243 = 2122865) B2122865
theorem B1415255 : Blo 940584 1415255 := bstep (se 1 (by rfl) ⟨1061441, by rfl⟩ : syracuseStep 1415255 = 2122883) B2122883
theorem B4298845 : Blo 940584 4298845 := bstep (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) B1612067
theorem B1415321 : Blo 940584 1415321 := bstep (se 2 (by rfl) ⟨530745, by rfl⟩ : syracuseStep 1415321 = 1061491) B1061491
theorem B1415435 : Blo 940584 1415435 := bstep (se 1 (by rfl) ⟨1061576, by rfl⟩ : syracuseStep 1415435 = 2123153) B2123153
theorem B1415447 : Blo 940584 1415447 := bstep (se 1 (by rfl) ⟨1061585, by rfl⟩ : syracuseStep 1415447 = 2123171) B2123171
theorem B3184919 : Blo 940584 3184919 := bstep (se 1 (by rfl) ⟨2388689, by rfl⟩ : syracuseStep 3184919 = 4777379) B4777379
theorem B3676481 : Blo 940584 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B1415513 : Blo 940584 1415513 := bstep (se 2 (by rfl) ⟨530817, by rfl⟩ : syracuseStep 1415513 = 1061635) B1061635
theorem B4299101 : Blo 940584 4299101 := bstep (se 3 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 4299101 = 1612163) B1612163
theorem B32676209 : Blo 940584 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B1415627 : Blo 940584 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B1415639 : Blo 940584 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B1415705 : Blo 940584 1415705 := bstep (se 2 (by rfl) ⟨530889, by rfl⟩ : syracuseStep 1415705 = 1061779) B1061779
theorem B1415819 : Blo 940584 1415819 := bstep (se 1 (by rfl) ⟨1061864, by rfl⟩ : syracuseStep 1415819 = 2123729) B2123729
theorem B1415831 : Blo 940584 1415831 := bstep (se 1 (by rfl) ⟨1061873, by rfl⟩ : syracuseStep 1415831 = 2123747) B2123747
theorem B1415897 : Blo 940584 1415897 := bstep (se 2 (by rfl) ⟨530961, by rfl⟩ : syracuseStep 1415897 = 1061923) B1061923
theorem B3185459 : Blo 940584 3185459 := bstep (se 1 (by rfl) ⟨2389094, by rfl⟩ : syracuseStep 3185459 = 4778189) B4778189
theorem B1416011 : Blo 940584 1416011 := bstep (se 1 (by rfl) ⟨1062008, by rfl⟩ : syracuseStep 1416011 = 2124017) B2124017
theorem B1416023 : Blo 940584 1416023 := bstep (se 1 (by rfl) ⟨1062017, by rfl⟩ : syracuseStep 1416023 = 2124035) B2124035
theorem B1416089 : Blo 940584 1416089 := bstep (se 2 (by rfl) ⟨531033, by rfl⟩ : syracuseStep 1416089 = 1062067) B1062067
theorem B1612759 : Blo 940584 1612759 := bstep (se 1 (by rfl) ⟨1209569, by rfl⟩ : syracuseStep 1612759 = 2419139) B2419139
theorem B2268121 : Blo 940584 2268121 := bstep (se 2 (by rfl) ⟨850545, by rfl⟩ : syracuseStep 2268121 = 1701091) B1701091
theorem B1416203 : Blo 940584 1416203 := bstep (se 1 (by rfl) ⟨1062152, by rfl⟩ : syracuseStep 1416203 = 2124305) B2124305
theorem B1416215 : Blo 940584 1416215 := bstep (se 1 (by rfl) ⟨1062161, by rfl⟩ : syracuseStep 1416215 = 2124323) B2124323
theorem B3185729 : Blo 940584 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B1416281 : Blo 940584 1416281 := bstep (se 2 (by rfl) ⟨531105, by rfl⟩ : syracuseStep 1416281 = 1062211) B1062211
theorem B3579011 : Blo 940584 3579011 := bstep (se 1 (by rfl) ⟨2684258, by rfl⟩ : syracuseStep 3579011 = 5368517) B5368517
theorem B3579025 : Blo 940584 3579025 := bstep (se 2 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 3579025 = 2684269) B2684269
theorem B2038937 : Blo 940584 2038937 := bstep (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) B1529203
theorem B1416395 : Blo 940584 1416395 := bstep (se 1 (by rfl) ⟨1062296, by rfl⟩ : syracuseStep 1416395 = 2124593) B2124593
theorem B1416407 : Blo 940584 1416407 := bstep (se 1 (by rfl) ⟨1062305, by rfl⟩ : syracuseStep 1416407 = 2124611) B2124611
theorem B1416473 : Blo 940584 1416473 := bstep (se 2 (by rfl) ⟨531177, by rfl⟩ : syracuseStep 1416473 = 1062355) B1062355
theorem B1416587 : Blo 940584 1416587 := bstep (se 1 (by rfl) ⟨1062440, by rfl⟩ : syracuseStep 1416587 = 2124881) B2124881
theorem B1416599 : Blo 940584 1416599 := bstep (se 1 (by rfl) ⟨1062449, by rfl⟩ : syracuseStep 1416599 = 2124899) B2124899
theorem B3579329 : Blo 940584 3579329 := bstep (se 2 (by rfl) ⟨1342248, by rfl⟩ : syracuseStep 3579329 = 2684497) B2684497
theorem B1416665 : Blo 940584 1416665 := bstep (se 2 (by rfl) ⟨531249, by rfl⟩ : syracuseStep 1416665 = 1062499) B1062499
theorem B1416779 : Blo 940584 1416779 := bstep (se 1 (by rfl) ⟨1062584, by rfl⟩ : syracuseStep 1416779 = 2125169) B2125169
theorem B1416791 : Blo 940584 1416791 := bstep (se 1 (by rfl) ⟨1062593, by rfl⟩ : syracuseStep 1416791 = 2125187) B2125187
theorem B3186269 : Blo 940584 3186269 := bstep (se 3 (by rfl) ⟨597425, by rfl⟩ : syracuseStep 3186269 = 1194851) B1194851
theorem B1416857 : Blo 940584 1416857 := bstep (se 2 (by rfl) ⟨531321, by rfl⟩ : syracuseStep 1416857 = 1062643) B1062643
theorem B1449751 : Blo 940584 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B8036131 : Blo 940584 8036131 := bstep (se 1 (by rfl) ⟨6027098, by rfl⟩ : syracuseStep 8036131 = 12054197) B12054197
theorem B11640793 : Blo 940584 11640793 := bstep (se 2 (by rfl) ⟨4365297, by rfl⟩ : syracuseStep 11640793 = 8730595) B8730595
theorem B2269235 : Blo 940584 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B3579997 : Blo 940584 3579997 := bstep (se 3 (by rfl) ⟨671249, by rfl⟩ : syracuseStep 3579997 = 1342499) B1342499
theorem B10723589 : Blo 940584 10723589 := bstep (se 4 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 10723589 = 2010673) B2010673
theorem B3449395 : Blo 940584 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B3187403 : Blo 940584 3187403 := bstep (se 1 (by rfl) ⟨2390552, by rfl⟩ : syracuseStep 3187403 = 4781105) B4781105
theorem B34874165 : Blo 940584 34874165 := bstep (se 5 (by rfl) ⟨1634726, by rfl⟩ : syracuseStep 34874165 = 3269453) B3269453
theorem B3187673 : Blo 940584 3187673 := bstep (se 2 (by rfl) ⟨1195377, by rfl⟩ : syracuseStep 3187673 = 2390755) B2390755
theorem B3581273 : Blo 940584 3581273 := bstep (se 2 (by rfl) ⟨1342977, by rfl⟩ : syracuseStep 3581273 = 2685955) B2685955
theorem B1058251 : Blo 940584 1058251 := bstep (se 1 (by rfl) ⟨793688, by rfl⟩ : syracuseStep 1058251 = 1587377) B1587377
theorem B1058359 : Blo 940584 1058359 := bstep (se 1 (by rfl) ⟨793769, by rfl⟩ : syracuseStep 1058359 = 1587539) B1587539
theorem B1058539 : Blo 940584 1058539 := bstep (se 1 (by rfl) ⟨793904, by rfl⟩ : syracuseStep 1058539 = 1587809) B1587809
theorem B1058647 : Blo 940584 1058647 := bstep (se 1 (by rfl) ⟨793985, by rfl⟩ : syracuseStep 1058647 = 1587971) B1587971
theorem B1058827 : Blo 940584 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B1910873 : Blo 940584 1910873 := bstep (se 2 (by rfl) ⟨716577, by rfl⟩ : syracuseStep 1910873 = 1433155) B1433155
theorem B1058935 : Blo 940584 1058935 := bstep (se 1 (by rfl) ⟨794201, by rfl⟩ : syracuseStep 1058935 = 1588403) B1588403
theorem B1059115 : Blo 940584 1059115 := bstep (se 1 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 1059115 = 1588673) B1588673
theorem B4303169 : Blo 940584 4303169 := bstep (se 2 (by rfl) ⟨1613688, by rfl⟩ : syracuseStep 4303169 = 3227377) B3227377
theorem B1059223 : Blo 940584 1059223 := bstep (se 1 (by rfl) ⟨794417, by rfl⟩ : syracuseStep 1059223 = 1588835) B1588835
theorem B1059403 : Blo 940584 1059403 := bstep (se 1 (by rfl) ⟨794552, by rfl⟩ : syracuseStep 1059403 = 1589105) B1589105
theorem B1059511 : Blo 940584 1059511 := bstep (se 1 (by rfl) ⟨794633, by rfl⟩ : syracuseStep 1059511 = 1589267) B1589267
theorem B1059691 : Blo 940584 1059691 := bstep (se 1 (by rfl) ⟨794768, by rfl⟩ : syracuseStep 1059691 = 1589537) B1589537
theorem B3582899 : Blo 940584 3582899 := bstep (se 1 (by rfl) ⟨2687174, by rfl⟩ : syracuseStep 3582899 = 5374349) B5374349
theorem B3582913 : Blo 940584 3582913 := bstep (se 2 (by rfl) ⟨1343592, by rfl⟩ : syracuseStep 3582913 = 2687185) B2687185
theorem B1059799 : Blo 940584 1059799 := bstep (se 1 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 1059799 = 1589699) B1589699
theorem B3025943 : Blo 940584 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B2010187 : Blo 940584 2010187 := bstep (se 1 (by rfl) ⟨1507640, by rfl⟩ : syracuseStep 2010187 = 3015281) B3015281
theorem B1059979 : Blo 940584 1059979 := bstep (se 1 (by rfl) ⟨794984, by rfl⟩ : syracuseStep 1059979 = 1589969) B1589969
theorem B2010263 : Blo 940584 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B1191115 : Blo 940584 1191115 := bstep (se 1 (by rfl) ⟨893336, by rfl⟩ : syracuseStep 1191115 = 1786673) B1786673
theorem B1060087 : Blo 940584 1060087 := bstep (se 1 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 1060087 = 1590131) B1590131
theorem B1060267 : Blo 940584 1060267 := bstep (se 1 (by rfl) ⟨795200, by rfl⟩ : syracuseStep 1060267 = 1590401) B1590401
theorem B6794675 : Blo 940584 6794675 := bstep (se 1 (by rfl) ⟨5096006, by rfl⟩ : syracuseStep 6794675 = 10192013) B10192013
theorem B1060375 : Blo 940584 1060375 := bstep (se 1 (by rfl) ⟨795281, by rfl⟩ : syracuseStep 1060375 = 1590563) B1590563
theorem B7155377 : Blo 940584 7155377 := bstep (se 2 (by rfl) ⟨2683266, by rfl⟩ : syracuseStep 7155377 = 5366533) B5366533
theorem B1060555 : Blo 940584 1060555 := bstep (se 1 (by rfl) ⟨795416, by rfl⟩ : syracuseStep 1060555 = 1590833) B1590833
theorem B2043649 : Blo 940584 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B13577989 : Blo 940584 13577989 := bstep (se 4 (by rfl) ⟨1272936, by rfl⟩ : syracuseStep 13577989 = 2545873) B2545873
theorem B1060663 : Blo 940584 1060663 := bstep (se 1 (by rfl) ⟨795497, by rfl⟩ : syracuseStep 1060663 = 1590995) B1590995
theorem B4763609 : Blo 940584 4763609 := bstep (se 2 (by rfl) ⟨1786353, by rfl⟩ : syracuseStep 4763609 = 3572707) B3572707
theorem B1060843 : Blo 940584 1060843 := bstep (se 1 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 1060843 = 1591265) B1591265
theorem B1060951 : Blo 940584 1060951 := bstep (se 1 (by rfl) ⟨795713, by rfl⟩ : syracuseStep 1060951 = 1591427) B1591427
theorem B1192087 : Blo 940584 1192087 := bstep (se 1 (by rfl) ⟨894065, by rfl⟩ : syracuseStep 1192087 = 1788131) B1788131
theorem B7155863 : Blo 940584 7155863 := bstep (se 1 (by rfl) ⟨5366897, by rfl⟩ : syracuseStep 7155863 = 10733795) B10733795
theorem B1061131 : Blo 940584 1061131 := bstep (se 1 (by rfl) ⟨795848, by rfl⟩ : syracuseStep 1061131 = 1591697) B1591697
theorem B8040779 : Blo 940584 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B1061239 : Blo 940584 1061239 := bstep (se 1 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 1061239 = 1591859) B1591859
theorem B1913305 : Blo 940584 1913305 := bstep (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) B1434979
theorem B1061419 : Blo 940584 1061419 := bstep (se 1 (by rfl) ⟨796064, by rfl⟩ : syracuseStep 1061419 = 1592129) B1592129
theorem B1061527 : Blo 940584 1061527 := bstep (se 1 (by rfl) ⟨796145, by rfl⟩ : syracuseStep 1061527 = 1592291) B1592291
theorem B1061707 : Blo 940584 1061707 := bstep (se 1 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 1061707 = 1592561) B1592561
theorem B3584843 : Blo 940584 3584843 := bstep (se 1 (by rfl) ⟨2688632, by rfl⟩ : syracuseStep 3584843 = 5377265) B5377265
theorem B3584857 : Blo 940584 3584857 := bstep (se 2 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 3584857 = 2688643) B2688643
theorem B2012033 : Blo 940584 2012033 := bstep (se 2 (by rfl) ⟨754512, by rfl⟩ : syracuseStep 2012033 = 1509025) B1509025
theorem B1061815 : Blo 940584 1061815 := bstep (se 1 (by rfl) ⟨796361, by rfl⟩ : syracuseStep 1061815 = 1592723) B1592723
theorem B1192907 : Blo 940584 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B3224651 : Blo 940584 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B1061995 : Blo 940584 1061995 := bstep (se 1 (by rfl) ⟨796496, by rfl⟩ : syracuseStep 1061995 = 1592993) B1592993
theorem B1062103 : Blo 940584 1062103 := bstep (se 1 (by rfl) ⟨796577, by rfl⟩ : syracuseStep 1062103 = 1593155) B1593155
theorem B1062283 : Blo 940584 1062283 := bstep (se 1 (by rfl) ⟨796712, by rfl⟩ : syracuseStep 1062283 = 1593425) B1593425
theorem B1062391 : Blo 940584 1062391 := bstep (se 1 (by rfl) ⟨796793, by rfl⟩ : syracuseStep 1062391 = 1593587) B1593587
theorem B4765229 : Blo 940584 4765229 := bstep (se 3 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 4765229 = 1786961) B1786961
theorem B1193611 : Blo 940584 1193611 := bstep (se 1 (by rfl) ⟨895208, by rfl⟩ : syracuseStep 1193611 = 1790417) B1790417
theorem B3815063 : Blo 940584 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B1062571 : Blo 940584 1062571 := bstep (se 1 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 1062571 = 1593857) B1593857
theorem B3585815 : Blo 940584 3585815 := bstep (se 1 (by rfl) ⟨2689361, by rfl⟩ : syracuseStep 3585815 = 5378723) B5378723
theorem B1193879 : Blo 940584 1193879 := bstep (se 1 (by rfl) ⟨895409, by rfl⟩ : syracuseStep 1193879 = 1790819) B1790819
theorem B18626635 : Blo 940584 18626635 := bstep (se 1 (by rfl) ⟨13969976, by rfl⟩ : syracuseStep 18626635 = 27939953) B27939953
theorem B1587289 : Blo 940584 1587289 := bstep (se 2 (by rfl) ⟨595233, by rfl⟩ : syracuseStep 1587289 = 1190467) B1190467
theorem B1194583 : Blo 940584 1194583 := bstep (se 1 (by rfl) ⟨895937, by rfl⟩ : syracuseStep 1194583 = 1791875) B1791875
theorem B2013835 : Blo 940584 2013835 := bstep (se 1 (by rfl) ⟨1510376, by rfl⟩ : syracuseStep 2013835 = 3020753) B3020753
theorem B1587863 : Blo 940584 1587863 := bstep (se 1 (by rfl) ⟨1190897, by rfl⟩ : syracuseStep 1587863 = 2381795) B2381795
theorem B1587991 : Blo 940584 1587991 := bstep (se 1 (by rfl) ⟨1190993, by rfl⟩ : syracuseStep 1587991 = 2381987) B2381987
theorem B4308185 : Blo 940584 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B10894657 : Blo 940584 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B1588619 : Blo 940584 1588619 := bstep (se 1 (by rfl) ⟨1191464, by rfl⟩ : syracuseStep 1588619 = 2382929) B2382929
theorem B1588747 : Blo 940584 1588747 := bstep (se 1 (by rfl) ⟨1191560, by rfl⟩ : syracuseStep 1588747 = 2383121) B2383121
theorem B1588889 : Blo 940584 1588889 := bstep (se 2 (by rfl) ⟨595833, by rfl⟩ : syracuseStep 1588889 = 1191667) B1191667
theorem B1589017 : Blo 940584 1589017 := bstep (se 2 (by rfl) ⟨595881, by rfl⟩ : syracuseStep 1589017 = 1191763) B1191763
theorem B1359703 : Blo 940584 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B1785739 : Blo 940584 1785739 := bstep (se 1 (by rfl) ⟨1339304, by rfl⟩ : syracuseStep 1785739 = 2678609) B2678609
theorem B2015219 : Blo 940584 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B5357785 : Blo 940584 5357785 := bstep (se 2 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 5357785 = 4018339) B4018339
theorem B1786187 : Blo 940584 1786187 := bstep (se 1 (by rfl) ⟨1339640, by rfl⟩ : syracuseStep 1786187 = 2679281) B2679281
theorem B1589591 : Blo 940584 1589591 := bstep (se 1 (by rfl) ⟨1192193, by rfl⟩ : syracuseStep 1589591 = 2384387) B2384387
theorem B1720705 : Blo 940584 1720705 := bstep (se 2 (by rfl) ⟨645264, by rfl⟩ : syracuseStep 1720705 = 1290529) B1290529
theorem B1589719 : Blo 940584 1589719 := bstep (se 1 (by rfl) ⟨1192289, by rfl⟩ : syracuseStep 1589719 = 2384579) B2384579
theorem B1786369 : Blo 940584 1786369 := bstep (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) B1339777
theorem B3392003 : Blo 940584 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B32654029 : Blo 940584 32654029 := bstep (se 3 (by rfl) ⟨6122630, by rfl⟩ : syracuseStep 32654029 = 12245261) B12245261
theorem B2016065 : Blo 940584 2016065 := bstep (se 2 (by rfl) ⟨756024, by rfl⟩ : syracuseStep 2016065 = 1512049) B1512049
theorem B1786711 : Blo 940584 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B3621763 : Blo 940584 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B1786931 : Blo 940584 1786931 := bstep (se 1 (by rfl) ⟨1340198, by rfl⟩ : syracuseStep 1786931 = 2680397) B2680397
theorem B1590347 : Blo 940584 1590347 := bstep (se 1 (by rfl) ⟨1192760, by rfl⟩ : syracuseStep 1590347 = 2385521) B2385521
theorem B5358743 : Blo 940584 5358743 := bstep (se 1 (by rfl) ⟨4019057, by rfl⟩ : syracuseStep 5358743 = 8038115) B8038115
theorem B2016407 : Blo 940584 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B1590475 : Blo 940584 1590475 := bstep (se 1 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 1590475 = 2385713) B2385713
theorem B1787159 : Blo 940584 1787159 := bstep (se 1 (by rfl) ⟨1340369, by rfl⟩ : syracuseStep 1787159 = 2680739) B2680739
theorem B1590617 : Blo 940584 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B4769117 : Blo 940584 4769117 := bstep (se 3 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 4769117 = 1788419) B1788419
theorem B1590745 : Blo 940584 1590745 := bstep (se 2 (by rfl) ⟨596529, by rfl⟩ : syracuseStep 1590745 = 1193059) B1193059
theorem B1787417 : Blo 940584 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B6047297 : Blo 940584 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B1787827 : Blo 940584 1787827 := bstep (se 1 (by rfl) ⟨1340870, by rfl⟩ : syracuseStep 1787827 = 2681741) B2681741
theorem B1591319 : Blo 940584 1591319 := bstep (se 1 (by rfl) ⟨1193489, by rfl⟩ : syracuseStep 1591319 = 2386979) B2386979
theorem B1591447 : Blo 940584 1591447 := bstep (se 1 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 1591447 = 2387171) B2387171
theorem B8604035 : Blo 940584 8604035 := bstep (se 1 (by rfl) ⟨6453026, by rfl⟩ : syracuseStep 8604035 = 12906053) B12906053
theorem B1788313 : Blo 940584 1788313 := bstep (se 2 (by rfl) ⟨670617, by rfl⟩ : syracuseStep 1788313 = 1341235) B1341235
theorem B2148811 : Blo 940584 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B10209827 : Blo 940584 10209827 := bstep (se 1 (by rfl) ⟨7657370, by rfl⟩ : syracuseStep 10209827 = 15314741) B15314741
theorem B1133195 : Blo 940584 1133195 := bstep (se 1 (by rfl) ⟨849896, by rfl⟩ : syracuseStep 1133195 = 1699793) B1699793
theorem B1592075 : Blo 940584 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B2116403 : Blo 940584 2116403 := bstep (se 1 (by rfl) ⟨1587302, by rfl⟩ : syracuseStep 2116403 = 3174605) B3174605
theorem B2116439 : Blo 940584 2116439 := bstep (se 1 (by rfl) ⟨1587329, by rfl⟩ : syracuseStep 2116439 = 3174659) B3174659
theorem B2149249 : Blo 940584 2149249 := bstep (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) B1611937
theorem B1592203 : Blo 940584 1592203 := bstep (se 1 (by rfl) ⟨1194152, by rfl⟩ : syracuseStep 1592203 = 2388305) B2388305
theorem B1788875 : Blo 940584 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B2116619 : Blo 940584 2116619 := bstep (se 1 (by rfl) ⟨1587464, by rfl⟩ : syracuseStep 2116619 = 3174929) B3174929
theorem B1592345 : Blo 940584 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B2116673 : Blo 940584 2116673 := bstep (se 2 (by rfl) ⟨793752, by rfl⟩ : syracuseStep 2116673 = 1587505) B1587505
theorem B1789057 : Blo 940584 1789057 := bstep (se 2 (by rfl) ⟨670896, by rfl⟩ : syracuseStep 1789057 = 1341793) B1341793
theorem B1592473 : Blo 940584 1592473 := bstep (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) B1194355
theorem B7163153 : Blo 940584 7163153 := bstep (se 2 (by rfl) ⟨2686182, by rfl⟩ : syracuseStep 7163153 = 5372365) B5372365
theorem B2116889 : Blo 940584 2116889 := bstep (se 2 (by rfl) ⟨793833, by rfl⟩ : syracuseStep 2116889 = 1587667) B1587667
theorem B2116979 : Blo 940584 2116979 := bstep (se 1 (by rfl) ⟨1587734, by rfl⟩ : syracuseStep 2116979 = 3175469) B3175469
theorem B2117015 : Blo 940584 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B4771223 : Blo 940584 4771223 := bstep (se 1 (by rfl) ⟨3578417, by rfl⟩ : syracuseStep 4771223 = 7156835) B7156835
theorem B2117195 : Blo 940584 2117195 := bstep (se 1 (by rfl) ⟨1587896, by rfl⟩ : syracuseStep 2117195 = 3175793) B3175793
theorem B5361227 : Blo 940584 5361227 := bstep (se 1 (by rfl) ⟨4020920, by rfl⟩ : syracuseStep 5361227 = 8041841) B8041841
theorem B2117249 : Blo 940584 2117249 := bstep (se 2 (by rfl) ⟨793968, by rfl⟩ : syracuseStep 2117249 = 1587937) B1587937
theorem B1593047 : Blo 940584 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B1724147 : Blo 940584 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1789771 : Blo 940584 1789771 := bstep (se 1 (by rfl) ⟨1342328, by rfl⟩ : syracuseStep 1789771 = 2684657) B2684657
theorem B1593175 : Blo 940584 1593175 := bstep (se 1 (by rfl) ⟨1194881, by rfl⟩ : syracuseStep 1593175 = 2389763) B2389763
theorem B2117465 : Blo 940584 2117465 := bstep (se 2 (by rfl) ⟨794049, by rfl⟩ : syracuseStep 2117465 = 1588099) B1588099
theorem B1789847 : Blo 940584 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B2117555 : Blo 940584 2117555 := bstep (se 1 (by rfl) ⟨1588166, by rfl⟩ : syracuseStep 2117555 = 3176333) B3176333
theorem B2117591 : Blo 940584 2117591 := bstep (se 1 (by rfl) ⟨1588193, by rfl⟩ : syracuseStep 2117591 = 3176387) B3176387
theorem B2117771 : Blo 940584 2117771 := bstep (se 1 (by rfl) ⟨1588328, by rfl⟩ : syracuseStep 2117771 = 3176657) B3176657
theorem B2117825 : Blo 940584 2117825 := bstep (se 2 (by rfl) ⟨794184, by rfl⟩ : syracuseStep 2117825 = 1588369) B1588369
theorem B3625181 : Blo 940584 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B2183411 : Blo 940584 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B2118041 : Blo 940584 2118041 := bstep (se 2 (by rfl) ⟨794265, by rfl⟩ : syracuseStep 2118041 = 1588531) B1588531
theorem B1593803 : Blo 940584 1593803 := bstep (se 1 (by rfl) ⟨1195352, by rfl⟩ : syracuseStep 1593803 = 2390705) B2390705
theorem B2118131 : Blo 940584 2118131 := bstep (se 1 (by rfl) ⟨1588598, by rfl⟩ : syracuseStep 2118131 = 3177197) B3177197
theorem B6050321 : Blo 940584 6050321 := bstep (se 2 (by rfl) ⟨2268870, by rfl⟩ : syracuseStep 6050321 = 4537741) B4537741
theorem B2118167 : Blo 940584 2118167 := bstep (se 1 (by rfl) ⟨1588625, by rfl⟩ : syracuseStep 2118167 = 3177251) B3177251
theorem B1790515 : Blo 940584 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B4837963 : Blo 940584 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B1593931 : Blo 940584 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B2904665 : Blo 940584 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B8049253 : Blo 940584 8049253 := bstep (se 4 (by rfl) ⟨754617, by rfl⟩ : syracuseStep 8049253 = 1509235) B1509235
theorem B2118347 : Blo 940584 2118347 := bstep (se 1 (by rfl) ⟨1588760, by rfl⟩ : syracuseStep 2118347 = 3177521) B3177521
theorem B2118401 : Blo 940584 2118401 := bstep (se 2 (by rfl) ⟨794400, by rfl⟩ : syracuseStep 2118401 = 1588801) B1588801
theorem B1790743 : Blo 940584 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B1790849 : Blo 940584 1790849 := bstep (se 2 (by rfl) ⟨671568, by rfl⟩ : syracuseStep 1790849 = 1343137) B1343137
theorem B1004491 : Blo 940584 1004491 := bstep (se 1 (by rfl) ⟨753368, by rfl⟩ : syracuseStep 1004491 = 1506737) B1506737
theorem B2544587 : Blo 940584 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B2118617 : Blo 940584 2118617 := bstep (se 2 (by rfl) ⟨794481, by rfl⟩ : syracuseStep 2118617 = 1588963) B1588963
theorem B1791001 : Blo 940584 1791001 := bstep (se 2 (by rfl) ⟨671625, by rfl⟩ : syracuseStep 1791001 = 1343251) B1343251
theorem B6050861 : Blo 940584 6050861 := bstep (se 3 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 6050861 = 2269073) B2269073
theorem B2118707 : Blo 940584 2118707 := bstep (se 1 (by rfl) ⟨1589030, by rfl⟩ : syracuseStep 2118707 = 3178061) B3178061
theorem B2118743 : Blo 940584 2118743 := bstep (se 1 (by rfl) ⟨1589057, by rfl⟩ : syracuseStep 2118743 = 3178115) B3178115
theorem B2118923 : Blo 940584 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B2118977 : Blo 940584 2118977 := bstep (se 2 (by rfl) ⟨794616, by rfl⟩ : syracuseStep 2118977 = 1589233) B1589233
theorem B2413975 : Blo 940584 2413975 := bstep (se 1 (by rfl) ⟨1810481, by rfl⟩ : syracuseStep 2413975 = 3620963) B3620963
theorem B2119193 : Blo 940584 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B8050211 : Blo 940584 8050211 := bstep (se 1 (by rfl) ⟨6037658, by rfl⟩ : syracuseStep 8050211 = 12075317) B12075317
theorem B2119283 : Blo 940584 2119283 := bstep (se 1 (by rfl) ⟨1589462, by rfl⟩ : syracuseStep 2119283 = 3178925) B3178925
theorem B4019843 : Blo 940584 4019843 := bstep (se 1 (by rfl) ⟨3014882, by rfl⟩ : syracuseStep 4019843 = 6029765) B6029765
theorem B3626627 : Blo 940584 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B2119319 : Blo 940584 2119319 := bstep (se 1 (by rfl) ⟨1589489, by rfl⟩ : syracuseStep 2119319 = 3178979) B3178979
theorem B1005367 : Blo 940584 1005367 := bstep (se 1 (by rfl) ⟨754025, by rfl⟩ : syracuseStep 1005367 = 1508051) B1508051
theorem B2381633 : Blo 940584 2381633 := bstep (se 2 (by rfl) ⟨893112, by rfl⟩ : syracuseStep 2381633 = 1786225) B1786225
theorem B10180417 : Blo 940584 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B4085569 : Blo 940584 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B2119499 : Blo 940584 2119499 := bstep (se 1 (by rfl) ⟨1589624, by rfl⟩ : syracuseStep 2119499 = 3179249) B3179249
theorem B2119553 : Blo 940584 2119553 := bstep (se 2 (by rfl) ⟨794832, by rfl⟩ : syracuseStep 2119553 = 1589665) B1589665
theorem B4085635 : Blo 940584 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B4020185 : Blo 940584 4020185 := bstep (se 2 (by rfl) ⟨1507569, by rfl⟩ : syracuseStep 4020185 = 3015139) B3015139
theorem B4413457 : Blo 940584 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B2119769 : Blo 940584 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B5363891 : Blo 940584 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B2119859 : Blo 940584 2119859 := bstep (se 1 (by rfl) ⟨1589894, by rfl⟩ : syracuseStep 2119859 = 3179789) B3179789
theorem B2119895 : Blo 940584 2119895 := bstep (se 1 (by rfl) ⟨1589921, by rfl⟩ : syracuseStep 2119895 = 3179843) B3179843
theorem B3922141 : Blo 940584 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B1005815 : Blo 940584 1005815 := bstep (se 1 (by rfl) ⟨754361, by rfl⟩ : syracuseStep 1005815 = 1508723) B1508723
theorem B1792307 : Blo 940584 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B2382169 : Blo 940584 2382169 := bstep (se 2 (by rfl) ⟨893313, by rfl⟩ : syracuseStep 2382169 = 1786627) B1786627
theorem B2120075 : Blo 940584 2120075 := bstep (se 1 (by rfl) ⟨1590056, by rfl⟩ : syracuseStep 2120075 = 3180113) B3180113
theorem B16341425 : Blo 940584 16341425 := bstep (se 2 (by rfl) ⟨6128034, by rfl⟩ : syracuseStep 16341425 = 12256069) B12256069
theorem B2120129 : Blo 940584 2120129 := bstep (se 2 (by rfl) ⟨795048, by rfl⟩ : syracuseStep 2120129 = 1590097) B1590097
theorem B1792459 : Blo 940584 1792459 := bstep (se 1 (by rfl) ⟨1344344, by rfl⟩ : syracuseStep 1792459 = 2688689) B2688689
theorem B940587 : Blo 940584 940587 := bstep (se 1 (by rfl) ⟨705440, by rfl⟩ : syracuseStep 940587 = 1410881) B1410881
theorem B940599 : Blo 940584 940599 := bstep (se 1 (by rfl) ⟨705449, by rfl⟩ : syracuseStep 940599 = 1410899) B1410899
theorem B940619 : Blo 940584 940619 := bstep (se 1 (by rfl) ⟨705464, by rfl⟩ : syracuseStep 940619 = 1410929) B1410929
theorem B940631 : Blo 940584 940631 := bstep (se 1 (by rfl) ⟨705473, by rfl⟩ : syracuseStep 940631 = 1410947) B1410947
theorem B940651 : Blo 940584 940651 := bstep (se 1 (by rfl) ⟨705488, by rfl⟩ : syracuseStep 940651 = 1410977) B1410977
theorem B1006187 : Blo 940584 1006187 := bstep (se 1 (by rfl) ⟨754640, by rfl⟩ : syracuseStep 1006187 = 1509281) B1509281
theorem B940663 : Blo 940584 940663 := bstep (se 1 (by rfl) ⟨705497, by rfl⟩ : syracuseStep 940663 = 1410995) B1410995
theorem B940683 : Blo 940584 940683 := bstep (se 1 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 940683 = 1411025) B1411025
theorem B940695 : Blo 940584 940695 := bstep (se 1 (by rfl) ⟨705521, by rfl⟩ : syracuseStep 940695 = 1411043) B1411043
theorem B2120345 : Blo 940584 2120345 := bstep (se 2 (by rfl) ⟨795129, by rfl⟩ : syracuseStep 2120345 = 1590259) B1590259
theorem B940715 : Blo 940584 940715 := bstep (se 1 (by rfl) ⟨705536, by rfl⟩ : syracuseStep 940715 = 1411073) B1411073
theorem B940727 : Blo 940584 940727 := bstep (se 1 (by rfl) ⟨705545, by rfl⟩ : syracuseStep 940727 = 1411091) B1411091
theorem B940747 : Blo 940584 940747 := bstep (se 1 (by rfl) ⟨705560, by rfl⟩ : syracuseStep 940747 = 1411121) B1411121
theorem B940759 : Blo 940584 940759 := bstep (se 1 (by rfl) ⟨705569, by rfl⟩ : syracuseStep 940759 = 1411139) B1411139
theorem B940779 : Blo 940584 940779 := bstep (se 1 (by rfl) ⟨705584, by rfl⟩ : syracuseStep 940779 = 1411169) B1411169
theorem B2120435 : Blo 940584 2120435 := bstep (se 1 (by rfl) ⟨1590326, by rfl⟩ : syracuseStep 2120435 = 3180653) B3180653
theorem B940791 : Blo 940584 940791 := bstep (se 1 (by rfl) ⟨705593, by rfl⟩ : syracuseStep 940791 = 1411187) B1411187
theorem B940811 : Blo 940584 940811 := bstep (se 1 (by rfl) ⟨705608, by rfl⟩ : syracuseStep 940811 = 1411217) B1411217
theorem B940823 : Blo 940584 940823 := bstep (se 1 (by rfl) ⟨705617, by rfl⟩ : syracuseStep 940823 = 1411235) B1411235
theorem B2120471 : Blo 940584 2120471 := bstep (se 1 (by rfl) ⟨1590353, by rfl⟩ : syracuseStep 2120471 = 3180707) B3180707
theorem B1792793 : Blo 940584 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B940843 : Blo 940584 940843 := bstep (se 1 (by rfl) ⟨705632, by rfl⟩ : syracuseStep 940843 = 1411265) B1411265
theorem B940855 : Blo 940584 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B940875 : Blo 940584 940875 := bstep (se 1 (by rfl) ⟨705656, by rfl⟩ : syracuseStep 940875 = 1411313) B1411313
theorem B1104715 : Blo 940584 1104715 := bstep (se 1 (by rfl) ⟨828536, by rfl⟩ : syracuseStep 1104715 = 1657073) B1657073
theorem B940887 : Blo 940584 940887 := bstep (se 1 (by rfl) ⟨705665, by rfl⟩ : syracuseStep 940887 = 1411331) B1411331
theorem B940907 : Blo 940584 940907 := bstep (se 1 (by rfl) ⟨705680, by rfl⟩ : syracuseStep 940907 = 1411361) B1411361
theorem B940919 : Blo 940584 940919 := bstep (se 1 (by rfl) ⟨705689, by rfl⟩ : syracuseStep 940919 = 1411379) B1411379
theorem B4774787 : Blo 940584 4774787 := bstep (se 1 (by rfl) ⟨3581090, by rfl⟩ : syracuseStep 4774787 = 7162181) B7162181
theorem B940939 : Blo 940584 940939 := bstep (se 1 (by rfl) ⟨705704, by rfl⟩ : syracuseStep 940939 = 1411409) B1411409
theorem B940951 : Blo 940584 940951 := bstep (se 1 (by rfl) ⟨705713, by rfl⟩ : syracuseStep 940951 = 1411427) B1411427
theorem B940971 : Blo 940584 940971 := bstep (se 1 (by rfl) ⟨705728, by rfl⟩ : syracuseStep 940971 = 1411457) B1411457
theorem B940983 : Blo 940584 940983 := bstep (se 1 (by rfl) ⟨705737, by rfl⟩ : syracuseStep 940983 = 1411475) B1411475
theorem B941003 : Blo 940584 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B2120651 : Blo 940584 2120651 := bstep (se 1 (by rfl) ⟨1590488, by rfl⟩ : syracuseStep 2120651 = 3180977) B3180977
theorem B941015 : Blo 940584 941015 := bstep (se 1 (by rfl) ⟨705761, by rfl⟩ : syracuseStep 941015 = 1411523) B1411523
theorem B1530841 : Blo 940584 1530841 := bstep (se 2 (by rfl) ⟨574065, by rfl⟩ : syracuseStep 1530841 = 1148131) B1148131
theorem B941035 : Blo 940584 941035 := bstep (se 1 (by rfl) ⟨705776, by rfl⟩ : syracuseStep 941035 = 1411553) B1411553
theorem B941047 : Blo 940584 941047 := bstep (se 1 (by rfl) ⟨705785, by rfl⟩ : syracuseStep 941047 = 1411571) B1411571
theorem B2120705 : Blo 940584 2120705 := bstep (se 2 (by rfl) ⟨795264, by rfl⟩ : syracuseStep 2120705 = 1590529) B1590529
theorem B941067 : Blo 940584 941067 := bstep (se 1 (by rfl) ⟨705800, by rfl⟩ : syracuseStep 941067 = 1411601) B1411601
theorem B2153483 : Blo 940584 2153483 := bstep (se 1 (by rfl) ⟨1615112, by rfl⟩ : syracuseStep 2153483 = 3230225) B3230225
theorem B941079 : Blo 940584 941079 := bstep (se 1 (by rfl) ⟨705809, by rfl⟩ : syracuseStep 941079 = 1411619) B1411619
theorem B941099 : Blo 940584 941099 := bstep (se 1 (by rfl) ⟨705824, by rfl⟩ : syracuseStep 941099 = 1411649) B1411649
theorem B941111 : Blo 940584 941111 := bstep (se 1 (by rfl) ⟨705833, by rfl⟩ : syracuseStep 941111 = 1411667) B1411667
theorem B7167041 : Blo 940584 7167041 := bstep (se 2 (by rfl) ⟨2687640, by rfl⟩ : syracuseStep 7167041 = 5375281) B5375281
theorem B941131 : Blo 940584 941131 := bstep (se 1 (by rfl) ⟨705848, by rfl⟩ : syracuseStep 941131 = 1411697) B1411697
theorem B941143 : Blo 940584 941143 := bstep (se 1 (by rfl) ⟨705857, by rfl⟩ : syracuseStep 941143 = 1411715) B1411715
theorem B941163 : Blo 940584 941163 := bstep (se 1 (by rfl) ⟨705872, by rfl⟩ : syracuseStep 941163 = 1411745) B1411745
theorem B941175 : Blo 940584 941175 := bstep (se 1 (by rfl) ⟨705881, by rfl⟩ : syracuseStep 941175 = 1411763) B1411763
theorem B941195 : Blo 940584 941195 := bstep (se 1 (by rfl) ⟨705896, by rfl⟩ : syracuseStep 941195 = 1411793) B1411793
theorem B941207 : Blo 940584 941207 := bstep (se 1 (by rfl) ⟨705905, by rfl⟩ : syracuseStep 941207 = 1411811) B1411811
theorem B941227 : Blo 940584 941227 := bstep (se 1 (by rfl) ⟨705920, by rfl⟩ : syracuseStep 941227 = 1411841) B1411841
theorem B941239 : Blo 940584 941239 := bstep (se 1 (by rfl) ⟨705929, by rfl⟩ : syracuseStep 941239 = 1411859) B1411859
theorem B941259 : Blo 940584 941259 := bstep (se 1 (by rfl) ⟨705944, by rfl⟩ : syracuseStep 941259 = 1411889) B1411889
theorem B11459789 : Blo 940584 11459789 := bstep (se 3 (by rfl) ⟨2148710, by rfl⟩ : syracuseStep 11459789 = 4297421) B4297421
theorem B941271 : Blo 940584 941271 := bstep (se 1 (by rfl) ⟨705953, by rfl⟩ : syracuseStep 941271 = 1411907) B1411907
theorem B2120921 : Blo 940584 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B941291 : Blo 940584 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B941303 : Blo 940584 941303 := bstep (se 1 (by rfl) ⟨705977, by rfl⟩ : syracuseStep 941303 = 1411955) B1411955
theorem B941323 : Blo 940584 941323 := bstep (se 1 (by rfl) ⟨705992, by rfl⟩ : syracuseStep 941323 = 1411985) B1411985
theorem B941335 : Blo 940584 941335 := bstep (se 1 (by rfl) ⟨706001, by rfl⟩ : syracuseStep 941335 = 1412003) B1412003
theorem B941355 : Blo 940584 941355 := bstep (se 1 (by rfl) ⟨706016, by rfl⟩ : syracuseStep 941355 = 1412033) B1412033
theorem B2121011 : Blo 940584 2121011 := bstep (se 1 (by rfl) ⟨1590758, by rfl⟩ : syracuseStep 2121011 = 3181517) B3181517
theorem B941367 : Blo 940584 941367 := bstep (se 1 (by rfl) ⟨706025, by rfl⟩ : syracuseStep 941367 = 1412051) B1412051
theorem B941387 : Blo 940584 941387 := bstep (se 1 (by rfl) ⟨706040, by rfl⟩ : syracuseStep 941387 = 1412081) B1412081
theorem B2153803 : Blo 940584 2153803 := bstep (se 1 (by rfl) ⟨1615352, by rfl⟩ : syracuseStep 2153803 = 3230705) B3230705
theorem B941399 : Blo 940584 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B2121047 : Blo 940584 2121047 := bstep (se 1 (by rfl) ⟨1590785, by rfl⟩ : syracuseStep 2121047 = 3181571) B3181571
theorem B941419 : Blo 940584 941419 := bstep (se 1 (by rfl) ⟨706064, by rfl⟩ : syracuseStep 941419 = 1412129) B1412129
theorem B941431 : Blo 940584 941431 := bstep (se 1 (by rfl) ⟨706073, by rfl⟩ : syracuseStep 941431 = 1412147) B1412147
theorem B941451 : Blo 940584 941451 := bstep (se 1 (by rfl) ⟨706088, by rfl⟩ : syracuseStep 941451 = 1412177) B1412177
theorem B941463 : Blo 940584 941463 := bstep (se 1 (by rfl) ⟨706097, by rfl⟩ : syracuseStep 941463 = 1412195) B1412195
theorem B941483 : Blo 940584 941483 := bstep (se 1 (by rfl) ⟨706112, by rfl⟩ : syracuseStep 941483 = 1412225) B1412225
theorem B2383283 : Blo 940584 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B941495 : Blo 940584 941495 := bstep (se 1 (by rfl) ⟨706121, by rfl⟩ : syracuseStep 941495 = 1412243) B1412243
theorem B941515 : Blo 940584 941515 := bstep (se 1 (by rfl) ⟨706136, by rfl⟩ : syracuseStep 941515 = 1412273) B1412273
theorem B941527 : Blo 940584 941527 := bstep (se 1 (by rfl) ⟨706145, by rfl⟩ : syracuseStep 941527 = 1412291) B1412291
theorem B941547 : Blo 940584 941547 := bstep (se 1 (by rfl) ⟨706160, by rfl⟩ : syracuseStep 941547 = 1412321) B1412321
theorem B941559 : Blo 940584 941559 := bstep (se 1 (by rfl) ⟨706169, by rfl⟩ : syracuseStep 941559 = 1412339) B1412339
theorem B941579 : Blo 940584 941579 := bstep (se 1 (by rfl) ⟨706184, by rfl⟩ : syracuseStep 941579 = 1412369) B1412369
theorem B2121227 : Blo 940584 2121227 := bstep (se 1 (by rfl) ⟨1590920, by rfl⟩ : syracuseStep 2121227 = 3181841) B3181841
theorem B941591 : Blo 940584 941591 := bstep (se 1 (by rfl) ⟨706193, by rfl⟩ : syracuseStep 941591 = 1412387) B1412387
theorem B941611 : Blo 940584 941611 := bstep (se 1 (by rfl) ⟨706208, by rfl⟩ : syracuseStep 941611 = 1412417) B1412417
theorem B941623 : Blo 940584 941623 := bstep (se 1 (by rfl) ⟨706217, by rfl⟩ : syracuseStep 941623 = 1412435) B1412435
theorem B4021825 : Blo 940584 4021825 := bstep (se 2 (by rfl) ⟨1508184, by rfl⟩ : syracuseStep 4021825 = 3016369) B3016369
theorem B2121281 : Blo 940584 2121281 := bstep (se 2 (by rfl) ⟨795480, by rfl⟩ : syracuseStep 2121281 = 1590961) B1590961
theorem B941643 : Blo 940584 941643 := bstep (se 1 (by rfl) ⟨706232, by rfl⟩ : syracuseStep 941643 = 1412465) B1412465
theorem B941655 : Blo 940584 941655 := bstep (se 1 (by rfl) ⟨706241, by rfl⟩ : syracuseStep 941655 = 1412483) B1412483
theorem B1007191 : Blo 940584 1007191 := bstep (se 1 (by rfl) ⟨755393, by rfl⟩ : syracuseStep 1007191 = 1510787) B1510787
theorem B5365349 : Blo 940584 5365349 := bstep (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) B1006003
theorem B941675 : Blo 940584 941675 := bstep (se 1 (by rfl) ⟨706256, by rfl⟩ : syracuseStep 941675 = 1412513) B1412513
theorem B1695347 : Blo 940584 1695347 := bstep (se 1 (by rfl) ⟨1271510, by rfl⟩ : syracuseStep 1695347 = 2543021) B2543021
theorem B941687 : Blo 940584 941687 := bstep (se 1 (by rfl) ⟨706265, by rfl⟩ : syracuseStep 941687 = 1412531) B1412531
theorem B941707 : Blo 940584 941707 := bstep (se 1 (by rfl) ⟨706280, by rfl⟩ : syracuseStep 941707 = 1412561) B1412561
theorem B941719 : Blo 940584 941719 := bstep (se 1 (by rfl) ⟨706289, by rfl⟩ : syracuseStep 941719 = 1412579) B1412579
theorem B941739 : Blo 940584 941739 := bstep (se 1 (by rfl) ⟨706304, by rfl⟩ : syracuseStep 941739 = 1412609) B1412609
theorem B941751 : Blo 940584 941751 := bstep (se 1 (by rfl) ⟨706313, by rfl⟩ : syracuseStep 941751 = 1412627) B1412627
theorem B941771 : Blo 940584 941771 := bstep (se 1 (by rfl) ⟨706328, by rfl⟩ : syracuseStep 941771 = 1412657) B1412657
theorem B941783 : Blo 940584 941783 := bstep (se 1 (by rfl) ⟨706337, by rfl⟩ : syracuseStep 941783 = 1412675) B1412675
theorem B2383577 : Blo 940584 2383577 := bstep (se 2 (by rfl) ⟨893841, by rfl⟩ : syracuseStep 2383577 = 1787683) B1787683
theorem B941803 : Blo 940584 941803 := bstep (se 1 (by rfl) ⟨706352, by rfl⟩ : syracuseStep 941803 = 1412705) B1412705
theorem B941815 : Blo 940584 941815 := bstep (se 1 (by rfl) ⟨706361, by rfl⟩ : syracuseStep 941815 = 1412723) B1412723
theorem B941835 : Blo 940584 941835 := bstep (se 1 (by rfl) ⟨706376, by rfl⟩ : syracuseStep 941835 = 1412753) B1412753
theorem B941847 : Blo 940584 941847 := bstep (se 1 (by rfl) ⟨706385, by rfl⟩ : syracuseStep 941847 = 1412771) B1412771
theorem B2121497 : Blo 940584 2121497 := bstep (se 2 (by rfl) ⟨795561, by rfl⟩ : syracuseStep 2121497 = 1591123) B1591123
theorem B941867 : Blo 940584 941867 := bstep (se 1 (by rfl) ⟨706400, by rfl⟩ : syracuseStep 941867 = 1412801) B1412801
theorem B941879 : Blo 940584 941879 := bstep (se 1 (by rfl) ⟨706409, by rfl⟩ : syracuseStep 941879 = 1412819) B1412819
theorem B941899 : Blo 940584 941899 := bstep (se 1 (by rfl) ⟨706424, by rfl⟩ : syracuseStep 941899 = 1412849) B1412849
theorem B941911 : Blo 940584 941911 := bstep (se 1 (by rfl) ⟨706433, by rfl⟩ : syracuseStep 941911 = 1412867) B1412867
theorem B941931 : Blo 940584 941931 := bstep (se 1 (by rfl) ⟨706448, by rfl⟩ : syracuseStep 941931 = 1412897) B1412897
theorem B2121587 : Blo 940584 2121587 := bstep (se 1 (by rfl) ⟨1591190, by rfl⟩ : syracuseStep 2121587 = 3182381) B3182381
theorem B941943 : Blo 940584 941943 := bstep (se 1 (by rfl) ⟨706457, by rfl⟩ : syracuseStep 941943 = 1412915) B1412915
theorem B941963 : Blo 940584 941963 := bstep (se 1 (by rfl) ⟨706472, by rfl⟩ : syracuseStep 941963 = 1412945) B1412945
theorem B941975 : Blo 940584 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B2121623 : Blo 940584 2121623 := bstep (se 1 (by rfl) ⟨1591217, by rfl⟩ : syracuseStep 2121623 = 3182435) B3182435
theorem B941995 : Blo 940584 941995 := bstep (se 1 (by rfl) ⟨706496, by rfl⟩ : syracuseStep 941995 = 1412993) B1412993
theorem B942007 : Blo 940584 942007 := bstep (se 1 (by rfl) ⟨706505, by rfl⟩ : syracuseStep 942007 = 1413011) B1413011
theorem B942027 : Blo 940584 942027 := bstep (se 1 (by rfl) ⟨706520, by rfl⟩ : syracuseStep 942027 = 1413041) B1413041
theorem B942039 : Blo 940584 942039 := bstep (se 1 (by rfl) ⟨706529, by rfl⟩ : syracuseStep 942039 = 1413059) B1413059
theorem B942059 : Blo 940584 942059 := bstep (se 1 (by rfl) ⟨706544, by rfl⟩ : syracuseStep 942059 = 1413089) B1413089
theorem B942071 : Blo 940584 942071 := bstep (se 1 (by rfl) ⟨706553, by rfl⟩ : syracuseStep 942071 = 1413107) B1413107
theorem B942091 : Blo 940584 942091 := bstep (se 1 (by rfl) ⟨706568, by rfl⟩ : syracuseStep 942091 = 1413137) B1413137
theorem B942103 : Blo 940584 942103 := bstep (se 1 (by rfl) ⟨706577, by rfl⟩ : syracuseStep 942103 = 1413155) B1413155
theorem B942123 : Blo 940584 942123 := bstep (se 1 (by rfl) ⟨706592, by rfl⟩ : syracuseStep 942123 = 1413185) B1413185
theorem B942135 : Blo 940584 942135 := bstep (se 1 (by rfl) ⟨706601, by rfl⟩ : syracuseStep 942135 = 1413203) B1413203
theorem B1695809 : Blo 940584 1695809 := bstep (se 2 (by rfl) ⟨635928, by rfl⟩ : syracuseStep 1695809 = 1271857) B1271857
theorem B942155 : Blo 940584 942155 := bstep (se 1 (by rfl) ⟨706616, by rfl⟩ : syracuseStep 942155 = 1413233) B1413233
theorem B2547787 : Blo 940584 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B2121803 : Blo 940584 2121803 := bstep (se 1 (by rfl) ⟨1591352, by rfl⟩ : syracuseStep 2121803 = 3182705) B3182705
theorem B942167 : Blo 940584 942167 := bstep (se 1 (by rfl) ⟨706625, by rfl⟩ : syracuseStep 942167 = 1413251) B1413251
theorem B942187 : Blo 940584 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B942199 : Blo 940584 942199 := bstep (se 1 (by rfl) ⟨706649, by rfl⟩ : syracuseStep 942199 = 1413299) B1413299
theorem B2121857 : Blo 940584 2121857 := bstep (se 2 (by rfl) ⟨795696, by rfl⟩ : syracuseStep 2121857 = 1591393) B1591393
theorem B942219 : Blo 940584 942219 := bstep (se 1 (by rfl) ⟨706664, by rfl⟩ : syracuseStep 942219 = 1413329) B1413329
theorem B942231 : Blo 940584 942231 := bstep (se 1 (by rfl) ⟨706673, by rfl⟩ : syracuseStep 942231 = 1413347) B1413347
theorem B16113815 : Blo 940584 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B942251 : Blo 940584 942251 := bstep (se 1 (by rfl) ⟨706688, by rfl⟩ : syracuseStep 942251 = 1413377) B1413377
theorem B942263 : Blo 940584 942263 := bstep (se 1 (by rfl) ⟨706697, by rfl⟩ : syracuseStep 942263 = 1413395) B1413395
theorem B942283 : Blo 940584 942283 := bstep (se 1 (by rfl) ⟨706712, by rfl⟩ : syracuseStep 942283 = 1413425) B1413425
theorem B942295 : Blo 940584 942295 := bstep (se 1 (by rfl) ⟨706721, by rfl⟩ : syracuseStep 942295 = 1413443) B1413443
theorem B942315 : Blo 940584 942315 := bstep (se 1 (by rfl) ⟨706736, by rfl⟩ : syracuseStep 942315 = 1413473) B1413473
theorem B942327 : Blo 940584 942327 := bstep (se 1 (by rfl) ⟨706745, by rfl⟩ : syracuseStep 942327 = 1413491) B1413491
theorem B942347 : Blo 940584 942347 := bstep (se 1 (by rfl) ⟨706760, by rfl⟩ : syracuseStep 942347 = 1413521) B1413521
theorem B5366033 : Blo 940584 5366033 := bstep (se 2 (by rfl) ⟨2012262, by rfl⟩ : syracuseStep 5366033 = 4024525) B4024525
theorem B942359 : Blo 940584 942359 := bstep (se 1 (by rfl) ⟨706769, by rfl⟩ : syracuseStep 942359 = 1413539) B1413539
theorem B942379 : Blo 940584 942379 := bstep (se 1 (by rfl) ⟨706784, by rfl⟩ : syracuseStep 942379 = 1413569) B1413569
theorem B10314029 : Blo 940584 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B942391 : Blo 940584 942391 := bstep (se 1 (by rfl) ⟨706793, by rfl⟩ : syracuseStep 942391 = 1413587) B1413587
theorem B942411 : Blo 940584 942411 := bstep (se 1 (by rfl) ⟨706808, by rfl⟩ : syracuseStep 942411 = 1413617) B1413617
theorem B942423 : Blo 940584 942423 := bstep (se 1 (by rfl) ⟨706817, by rfl⟩ : syracuseStep 942423 = 1413635) B1413635
theorem B2122073 : Blo 940584 2122073 := bstep (se 2 (by rfl) ⟨795777, by rfl⟩ : syracuseStep 2122073 = 1591555) B1591555
theorem B942443 : Blo 940584 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B942455 : Blo 940584 942455 := bstep (se 1 (by rfl) ⟨706841, by rfl⟩ : syracuseStep 942455 = 1413683) B1413683
theorem B942475 : Blo 940584 942475 := bstep (se 1 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 942475 = 1413713) B1413713
theorem B1008011 : Blo 940584 1008011 := bstep (se 1 (by rfl) ⟨756008, by rfl⟩ : syracuseStep 1008011 = 1512017) B1512017
theorem B942487 : Blo 940584 942487 := bstep (se 1 (by rfl) ⟨706865, by rfl⟩ : syracuseStep 942487 = 1413731) B1413731
theorem B942507 : Blo 940584 942507 := bstep (se 1 (by rfl) ⟨706880, by rfl⟩ : syracuseStep 942507 = 1413761) B1413761
theorem B2122163 : Blo 940584 2122163 := bstep (se 1 (by rfl) ⟨1591622, by rfl⟩ : syracuseStep 2122163 = 3183245) B3183245
theorem B942519 : Blo 940584 942519 := bstep (se 1 (by rfl) ⟨706889, by rfl⟩ : syracuseStep 942519 = 1413779) B1413779
theorem B942539 : Blo 940584 942539 := bstep (se 1 (by rfl) ⟨706904, by rfl⟩ : syracuseStep 942539 = 1413809) B1413809
theorem B942551 : Blo 940584 942551 := bstep (se 1 (by rfl) ⟨706913, by rfl⟩ : syracuseStep 942551 = 1413827) B1413827
theorem B2122199 : Blo 940584 2122199 := bstep (se 1 (by rfl) ⟨1591649, by rfl⟩ : syracuseStep 2122199 = 3183299) B3183299
theorem B2679257 : Blo 940584 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B942571 : Blo 940584 942571 := bstep (se 1 (by rfl) ⟨706928, by rfl⟩ : syracuseStep 942571 = 1413857) B1413857
theorem B942583 : Blo 940584 942583 := bstep (se 1 (by rfl) ⟨706937, by rfl⟩ : syracuseStep 942583 = 1413875) B1413875
theorem B942603 : Blo 940584 942603 := bstep (se 1 (by rfl) ⟨706952, by rfl⟩ : syracuseStep 942603 = 1413905) B1413905
theorem B942615 : Blo 940584 942615 := bstep (se 1 (by rfl) ⟨706961, by rfl⟩ : syracuseStep 942615 = 1413923) B1413923
theorem B942635 : Blo 940584 942635 := bstep (se 1 (by rfl) ⟨706976, by rfl⟩ : syracuseStep 942635 = 1413953) B1413953
theorem B942647 : Blo 940584 942647 := bstep (se 1 (by rfl) ⟨706985, by rfl⟩ : syracuseStep 942647 = 1413971) B1413971
theorem B942667 : Blo 940584 942667 := bstep (se 1 (by rfl) ⟨707000, by rfl⟩ : syracuseStep 942667 = 1414001) B1414001
theorem B942679 : Blo 940584 942679 := bstep (se 1 (by rfl) ⟨707009, by rfl⟩ : syracuseStep 942679 = 1414019) B1414019
theorem B942699 : Blo 940584 942699 := bstep (se 1 (by rfl) ⟨707024, by rfl⟩ : syracuseStep 942699 = 1414049) B1414049
theorem B942711 : Blo 940584 942711 := bstep (se 1 (by rfl) ⟨707033, by rfl⟩ : syracuseStep 942711 = 1414067) B1414067
theorem B942731 : Blo 940584 942731 := bstep (se 1 (by rfl) ⟨707048, by rfl⟩ : syracuseStep 942731 = 1414097) B1414097
theorem B2122379 : Blo 940584 2122379 := bstep (se 1 (by rfl) ⟨1591784, by rfl⟩ : syracuseStep 2122379 = 3183569) B3183569
theorem B942743 : Blo 940584 942743 := bstep (se 1 (by rfl) ⟨707057, by rfl⟩ : syracuseStep 942743 = 1414115) B1414115
theorem B942763 : Blo 940584 942763 := bstep (se 1 (by rfl) ⟨707072, by rfl⟩ : syracuseStep 942763 = 1414145) B1414145
theorem B942775 : Blo 940584 942775 := bstep (se 1 (by rfl) ⟨707081, by rfl⟩ : syracuseStep 942775 = 1414163) B1414163
theorem B2122433 : Blo 940584 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B942795 : Blo 940584 942795 := bstep (se 1 (by rfl) ⟨707096, by rfl⟩ : syracuseStep 942795 = 1414193) B1414193
theorem B942807 : Blo 940584 942807 := bstep (se 1 (by rfl) ⟨707105, by rfl⟩ : syracuseStep 942807 = 1414211) B1414211
theorem B1073899 : Blo 940584 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B942827 : Blo 940584 942827 := bstep (se 1 (by rfl) ⟨707120, by rfl⟩ : syracuseStep 942827 = 1414241) B1414241
theorem B942839 : Blo 940584 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B942859 : Blo 940584 942859 := bstep (se 1 (by rfl) ⟨707144, by rfl⟩ : syracuseStep 942859 = 1414289) B1414289
theorem B942871 : Blo 940584 942871 := bstep (se 1 (by rfl) ⟨707153, by rfl⟩ : syracuseStep 942871 = 1414307) B1414307
theorem B942891 : Blo 940584 942891 := bstep (se 1 (by rfl) ⟨707168, by rfl⟩ : syracuseStep 942891 = 1414337) B1414337
theorem B942903 : Blo 940584 942903 := bstep (se 1 (by rfl) ⟨707177, by rfl⟩ : syracuseStep 942903 = 1414355) B1414355
theorem B942923 : Blo 940584 942923 := bstep (se 1 (by rfl) ⟨707192, by rfl⟩ : syracuseStep 942923 = 1414385) B1414385
theorem B942935 : Blo 940584 942935 := bstep (se 1 (by rfl) ⟨707201, by rfl⟩ : syracuseStep 942935 = 1414403) B1414403
theorem B1434457 : Blo 940584 1434457 := bstep (se 2 (by rfl) ⟨537921, by rfl⟩ : syracuseStep 1434457 = 1075843) B1075843
theorem B942955 : Blo 940584 942955 := bstep (se 1 (by rfl) ⟨707216, by rfl⟩ : syracuseStep 942955 = 1414433) B1414433
theorem B942967 : Blo 940584 942967 := bstep (se 1 (by rfl) ⟨707225, by rfl⟩ : syracuseStep 942967 = 1414451) B1414451
theorem B942987 : Blo 940584 942987 := bstep (se 1 (by rfl) ⟨707240, by rfl⟩ : syracuseStep 942987 = 1414481) B1414481
theorem B942999 : Blo 940584 942999 := bstep (se 1 (by rfl) ⟨707249, by rfl⟩ : syracuseStep 942999 = 1414499) B1414499
theorem B2122649 : Blo 940584 2122649 := bstep (se 2 (by rfl) ⟨795993, by rfl⟩ : syracuseStep 2122649 = 1591987) B1591987
theorem B943019 : Blo 940584 943019 := bstep (se 1 (by rfl) ⟨707264, by rfl⟩ : syracuseStep 943019 = 1414529) B1414529
theorem B943031 : Blo 940584 943031 := bstep (se 1 (by rfl) ⟨707273, by rfl⟩ : syracuseStep 943031 = 1414547) B1414547
theorem B943051 : Blo 940584 943051 := bstep (se 1 (by rfl) ⟨707288, by rfl⟩ : syracuseStep 943051 = 1414577) B1414577
theorem B943063 : Blo 940584 943063 := bstep (se 1 (by rfl) ⟨707297, by rfl⟩ : syracuseStep 943063 = 1414595) B1414595
theorem B7168985 : Blo 940584 7168985 := bstep (se 2 (by rfl) ⟨2688369, by rfl⟩ : syracuseStep 7168985 = 5376739) B5376739
theorem B943083 : Blo 940584 943083 := bstep (se 1 (by rfl) ⟨707312, by rfl⟩ : syracuseStep 943083 = 1414625) B1414625
theorem B2122739 : Blo 940584 2122739 := bstep (se 1 (by rfl) ⟨1592054, by rfl⟩ : syracuseStep 2122739 = 3184109) B3184109
theorem B943095 : Blo 940584 943095 := bstep (se 1 (by rfl) ⟨707321, by rfl⟩ : syracuseStep 943095 = 1414643) B1414643
theorem B943115 : Blo 940584 943115 := bstep (se 1 (by rfl) ⟨707336, by rfl⟩ : syracuseStep 943115 = 1414673) B1414673
theorem B943127 : Blo 940584 943127 := bstep (se 1 (by rfl) ⟨707345, by rfl⟩ : syracuseStep 943127 = 1414691) B1414691
theorem B2122775 : Blo 940584 2122775 := bstep (se 1 (by rfl) ⟨1592081, by rfl⟩ : syracuseStep 2122775 = 3184163) B3184163
theorem B943147 : Blo 940584 943147 := bstep (se 1 (by rfl) ⟨707360, by rfl⟩ : syracuseStep 943147 = 1414721) B1414721
theorem B943159 : Blo 940584 943159 := bstep (se 1 (by rfl) ⟨707369, by rfl⟩ : syracuseStep 943159 = 1414739) B1414739
theorem B943179 : Blo 940584 943179 := bstep (se 1 (by rfl) ⟨707384, by rfl⟩ : syracuseStep 943179 = 1414769) B1414769
theorem B943191 : Blo 940584 943191 := bstep (se 1 (by rfl) ⟨707393, by rfl⟩ : syracuseStep 943191 = 1414787) B1414787
theorem B5104741 : Blo 940584 5104741 := bstep (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) B957139
theorem B943211 : Blo 940584 943211 := bstep (se 1 (by rfl) ⟨707408, by rfl⟩ : syracuseStep 943211 = 1414817) B1414817
theorem B943223 : Blo 940584 943223 := bstep (se 1 (by rfl) ⟨707417, by rfl⟩ : syracuseStep 943223 = 1414835) B1414835
theorem B943243 : Blo 940584 943243 := bstep (se 1 (by rfl) ⟨707432, by rfl⟩ : syracuseStep 943243 = 1414865) B1414865
theorem B943255 : Blo 940584 943255 := bstep (se 1 (by rfl) ⟨707441, by rfl⟩ : syracuseStep 943255 = 1414883) B1414883
theorem B943275 : Blo 940584 943275 := bstep (se 1 (by rfl) ⟨707456, by rfl⟩ : syracuseStep 943275 = 1414913) B1414913
theorem B943287 : Blo 940584 943287 := bstep (se 1 (by rfl) ⟨707465, by rfl⟩ : syracuseStep 943287 = 1414931) B1414931
theorem B943307 : Blo 940584 943307 := bstep (se 1 (by rfl) ⟨707480, by rfl⟩ : syracuseStep 943307 = 1414961) B1414961
theorem B2122955 : Blo 940584 2122955 := bstep (se 1 (by rfl) ⟨1592216, by rfl⟩ : syracuseStep 2122955 = 3184433) B3184433
theorem B943319 : Blo 940584 943319 := bstep (se 1 (by rfl) ⟨707489, by rfl⟩ : syracuseStep 943319 = 1414979) B1414979
theorem B943339 : Blo 940584 943339 := bstep (se 1 (by rfl) ⟨707504, by rfl⟩ : syracuseStep 943339 = 1415009) B1415009
theorem B943351 : Blo 940584 943351 := bstep (se 1 (by rfl) ⟨707513, by rfl⟩ : syracuseStep 943351 = 1415027) B1415027
theorem B2123009 : Blo 940584 2123009 := bstep (se 2 (by rfl) ⟨796128, by rfl⟩ : syracuseStep 2123009 = 1592257) B1592257
theorem B943371 : Blo 940584 943371 := bstep (se 1 (by rfl) ⟨707528, by rfl⟩ : syracuseStep 943371 = 1415057) B1415057
theorem B943383 : Blo 940584 943383 := bstep (se 1 (by rfl) ⟨707537, by rfl⟩ : syracuseStep 943383 = 1415075) B1415075
theorem B943403 : Blo 940584 943403 := bstep (se 1 (by rfl) ⟨707552, by rfl⟩ : syracuseStep 943403 = 1415105) B1415105
theorem B943415 : Blo 940584 943415 := bstep (se 1 (by rfl) ⟨707561, by rfl⟩ : syracuseStep 943415 = 1415123) B1415123
theorem B2385227 : Blo 940584 2385227 := bstep (se 1 (by rfl) ⟨1788920, by rfl⟩ : syracuseStep 2385227 = 3577841) B3577841
theorem B943435 : Blo 940584 943435 := bstep (se 1 (by rfl) ⟨707576, by rfl⟩ : syracuseStep 943435 = 1415153) B1415153
theorem B943447 : Blo 940584 943447 := bstep (se 1 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 943447 = 1415171) B1415171
theorem B943467 : Blo 940584 943467 := bstep (se 1 (by rfl) ⟨707600, by rfl⟩ : syracuseStep 943467 = 1415201) B1415201
theorem B943479 : Blo 940584 943479 := bstep (se 1 (by rfl) ⟨707609, by rfl⟩ : syracuseStep 943479 = 1415219) B1415219
theorem B943499 : Blo 940584 943499 := bstep (se 1 (by rfl) ⟨707624, by rfl⟩ : syracuseStep 943499 = 1415249) B1415249
theorem B943511 : Blo 940584 943511 := bstep (se 1 (by rfl) ⟨707633, by rfl⟩ : syracuseStep 943511 = 1415267) B1415267
theorem B1533335 : Blo 940584 1533335 := bstep (se 1 (by rfl) ⟨1150001, by rfl⟩ : syracuseStep 1533335 = 2300003) B2300003
theorem B943531 : Blo 940584 943531 := bstep (se 1 (by rfl) ⟨707648, by rfl⟩ : syracuseStep 943531 = 1415297) B1415297
theorem B2549171 : Blo 940584 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B943543 : Blo 940584 943543 := bstep (se 1 (by rfl) ⟨707657, by rfl⟩ : syracuseStep 943543 = 1415315) B1415315
theorem B943563 : Blo 940584 943563 := bstep (se 1 (by rfl) ⟨707672, by rfl⟩ : syracuseStep 943563 = 1415345) B1415345
theorem B943575 : Blo 940584 943575 := bstep (se 1 (by rfl) ⟨707681, by rfl⟩ : syracuseStep 943575 = 1415363) B1415363
theorem B2123225 : Blo 940584 2123225 := bstep (se 2 (by rfl) ⟨796209, by rfl⟩ : syracuseStep 2123225 = 1592419) B1592419
theorem B943595 : Blo 940584 943595 := bstep (se 1 (by rfl) ⟨707696, by rfl⟩ : syracuseStep 943595 = 1415393) B1415393
theorem B943607 : Blo 940584 943607 := bstep (se 1 (by rfl) ⟨707705, by rfl⟩ : syracuseStep 943607 = 1415411) B1415411
theorem B943627 : Blo 940584 943627 := bstep (se 1 (by rfl) ⟨707720, by rfl⟩ : syracuseStep 943627 = 1415441) B1415441
theorem B943639 : Blo 940584 943639 := bstep (se 1 (by rfl) ⟨707729, by rfl⟩ : syracuseStep 943639 = 1415459) B1415459
theorem B17655331 : Blo 940584 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B943659 : Blo 940584 943659 := bstep (se 1 (by rfl) ⟨707744, by rfl⟩ : syracuseStep 943659 = 1415489) B1415489
theorem B2123315 : Blo 940584 2123315 := bstep (se 1 (by rfl) ⟨1592486, by rfl⟩ : syracuseStep 2123315 = 3184973) B3184973
theorem B943671 : Blo 940584 943671 := bstep (se 1 (by rfl) ⟨707753, by rfl⟩ : syracuseStep 943671 = 1415507) B1415507
theorem B943691 : Blo 940584 943691 := bstep (se 1 (by rfl) ⟨707768, by rfl⟩ : syracuseStep 943691 = 1415537) B1415537
theorem B943703 : Blo 940584 943703 := bstep (se 1 (by rfl) ⟨707777, by rfl⟩ : syracuseStep 943703 = 1415555) B1415555
theorem B2123351 : Blo 940584 2123351 := bstep (se 1 (by rfl) ⟨1592513, by rfl⟩ : syracuseStep 2123351 = 3185027) B3185027
theorem B943723 : Blo 940584 943723 := bstep (se 1 (by rfl) ⟨707792, by rfl⟩ : syracuseStep 943723 = 1415585) B1415585
theorem B943735 : Blo 940584 943735 := bstep (se 1 (by rfl) ⟨707801, by rfl⟩ : syracuseStep 943735 = 1415603) B1415603
theorem B943755 : Blo 940584 943755 := bstep (se 1 (by rfl) ⟨707816, by rfl⟩ : syracuseStep 943755 = 1415633) B1415633
theorem B943767 : Blo 940584 943767 := bstep (se 1 (by rfl) ⟨707825, by rfl⟩ : syracuseStep 943767 = 1415651) B1415651
theorem B943787 : Blo 940584 943787 := bstep (se 1 (by rfl) ⟨707840, by rfl⟩ : syracuseStep 943787 = 1415681) B1415681
theorem B943799 : Blo 940584 943799 := bstep (se 1 (by rfl) ⟨707849, by rfl⟩ : syracuseStep 943799 = 1415699) B1415699
theorem B2680523 : Blo 940584 2680523 := bstep (se 1 (by rfl) ⟨2010392, by rfl⟩ : syracuseStep 2680523 = 4020785) B4020785
theorem B943819 : Blo 940584 943819 := bstep (se 1 (by rfl) ⟨707864, by rfl⟩ : syracuseStep 943819 = 1415729) B1415729
theorem B943831 : Blo 940584 943831 := bstep (se 1 (by rfl) ⟨707873, by rfl⟩ : syracuseStep 943831 = 1415747) B1415747
theorem B943851 : Blo 940584 943851 := bstep (se 1 (by rfl) ⟨707888, by rfl⟩ : syracuseStep 943851 = 1415777) B1415777
theorem B943863 : Blo 940584 943863 := bstep (se 1 (by rfl) ⟨707897, by rfl⟩ : syracuseStep 943863 = 1415795) B1415795
theorem B2123531 : Blo 940584 2123531 := bstep (se 1 (by rfl) ⟨1592648, by rfl⟩ : syracuseStep 2123531 = 3185297) B3185297
theorem B943883 : Blo 940584 943883 := bstep (se 1 (by rfl) ⟨707912, by rfl⟩ : syracuseStep 943883 = 1415825) B1415825
theorem B943895 : Blo 940584 943895 := bstep (se 1 (by rfl) ⟨707921, by rfl⟩ : syracuseStep 943895 = 1415843) B1415843
theorem B943915 : Blo 940584 943915 := bstep (se 1 (by rfl) ⟨707936, by rfl⟩ : syracuseStep 943915 = 1415873) B1415873
theorem B943927 : Blo 940584 943927 := bstep (se 1 (by rfl) ⟨707945, by rfl⟩ : syracuseStep 943927 = 1415891) B1415891
theorem B2123585 : Blo 940584 2123585 := bstep (se 2 (by rfl) ⟨796344, by rfl⟩ : syracuseStep 2123585 = 1592689) B1592689
theorem B943947 : Blo 940584 943947 := bstep (se 1 (by rfl) ⟨707960, by rfl⟩ : syracuseStep 943947 = 1415921) B1415921
theorem B943959 : Blo 940584 943959 := bstep (se 1 (by rfl) ⟨707969, by rfl⟩ : syracuseStep 943959 = 1415939) B1415939
theorem B943979 : Blo 940584 943979 := bstep (se 1 (by rfl) ⟨707984, by rfl⟩ : syracuseStep 943979 = 1415969) B1415969
theorem B943991 : Blo 940584 943991 := bstep (se 1 (by rfl) ⟨707993, by rfl⟩ : syracuseStep 943991 = 1415987) B1415987
theorem B944011 : Blo 940584 944011 := bstep (se 1 (by rfl) ⟨708008, by rfl⟩ : syracuseStep 944011 = 1416017) B1416017
theorem B944023 : Blo 940584 944023 := bstep (se 1 (by rfl) ⟨708017, by rfl⟩ : syracuseStep 944023 = 1416035) B1416035
theorem B944043 : Blo 940584 944043 := bstep (se 1 (by rfl) ⟨708032, by rfl⟩ : syracuseStep 944043 = 1416065) B1416065
theorem B944055 : Blo 940584 944055 := bstep (se 1 (by rfl) ⟨708041, by rfl⟩ : syracuseStep 944055 = 1416083) B1416083
theorem B944075 : Blo 940584 944075 := bstep (se 1 (by rfl) ⟨708056, by rfl⟩ : syracuseStep 944075 = 1416113) B1416113
theorem B944087 : Blo 940584 944087 := bstep (se 1 (by rfl) ⟨708065, by rfl⟩ : syracuseStep 944087 = 1416131) B1416131
theorem B944107 : Blo 940584 944107 := bstep (se 1 (by rfl) ⟨708080, by rfl⟩ : syracuseStep 944107 = 1416161) B1416161
theorem B944119 : Blo 940584 944119 := bstep (se 1 (by rfl) ⟨708089, by rfl⟩ : syracuseStep 944119 = 1416179) B1416179
theorem B944139 : Blo 940584 944139 := bstep (se 1 (by rfl) ⟨708104, by rfl⟩ : syracuseStep 944139 = 1416209) B1416209
theorem B944151 : Blo 940584 944151 := bstep (se 1 (by rfl) ⟨708113, by rfl⟩ : syracuseStep 944151 = 1416227) B1416227
theorem B2123801 : Blo 940584 2123801 := bstep (se 2 (by rfl) ⟨796425, by rfl⟩ : syracuseStep 2123801 = 1592851) B1592851
theorem B1435673 : Blo 940584 1435673 := bstep (se 2 (by rfl) ⟨538377, by rfl⟩ : syracuseStep 1435673 = 1076755) B1076755
theorem B944171 : Blo 940584 944171 := bstep (se 1 (by rfl) ⟨708128, by rfl⟩ : syracuseStep 944171 = 1416257) B1416257
theorem B944183 : Blo 940584 944183 := bstep (se 1 (by rfl) ⟨708137, by rfl⟩ : syracuseStep 944183 = 1416275) B1416275
theorem B944203 : Blo 940584 944203 := bstep (se 1 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 944203 = 1416305) B1416305
theorem B944215 : Blo 940584 944215 := bstep (se 1 (by rfl) ⟨708161, by rfl⟩ : syracuseStep 944215 = 1416323) B1416323
theorem B944235 : Blo 940584 944235 := bstep (se 1 (by rfl) ⟨708176, by rfl⟩ : syracuseStep 944235 = 1416353) B1416353
theorem B2123891 : Blo 940584 2123891 := bstep (se 1 (by rfl) ⟨1592918, by rfl⟩ : syracuseStep 2123891 = 3185837) B3185837
theorem B944247 : Blo 940584 944247 := bstep (se 1 (by rfl) ⟨708185, by rfl⟩ : syracuseStep 944247 = 1416371) B1416371
theorem B944267 : Blo 940584 944267 := bstep (se 1 (by rfl) ⟨708200, by rfl⟩ : syracuseStep 944267 = 1416401) B1416401
theorem B2123927 : Blo 940584 2123927 := bstep (se 1 (by rfl) ⟨1592945, by rfl⟩ : syracuseStep 2123927 = 3185891) B3185891
theorem B944279 : Blo 940584 944279 := bstep (se 1 (by rfl) ⟨708209, by rfl⟩ : syracuseStep 944279 = 1416419) B1416419
theorem B944299 : Blo 940584 944299 := bstep (se 1 (by rfl) ⟨708224, by rfl⟩ : syracuseStep 944299 = 1416449) B1416449
theorem B8054963 : Blo 940584 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B944311 : Blo 940584 944311 := bstep (se 1 (by rfl) ⟨708233, by rfl⟩ : syracuseStep 944311 = 1416467) B1416467
theorem B944331 : Blo 940584 944331 := bstep (se 1 (by rfl) ⟨708248, by rfl⟩ : syracuseStep 944331 = 1416497) B1416497
theorem B944343 : Blo 940584 944343 := bstep (se 1 (by rfl) ⟨708257, by rfl⟩ : syracuseStep 944343 = 1416515) B1416515
theorem B944363 : Blo 940584 944363 := bstep (se 1 (by rfl) ⟨708272, by rfl⟩ : syracuseStep 944363 = 1416545) B1416545
theorem B944375 : Blo 940584 944375 := bstep (se 1 (by rfl) ⟨708281, by rfl⟩ : syracuseStep 944375 = 1416563) B1416563
theorem B944395 : Blo 940584 944395 := bstep (se 1 (by rfl) ⟨708296, by rfl⟩ : syracuseStep 944395 = 1416593) B1416593
theorem B2386199 : Blo 940584 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B944407 : Blo 940584 944407 := bstep (se 1 (by rfl) ⟨708305, by rfl⟩ : syracuseStep 944407 = 1416611) B1416611
theorem B944427 : Blo 940584 944427 := bstep (se 1 (by rfl) ⟨708320, by rfl⟩ : syracuseStep 944427 = 1416641) B1416641
theorem B944439 : Blo 940584 944439 := bstep (se 1 (by rfl) ⟨708329, by rfl⟩ : syracuseStep 944439 = 1416659) B1416659
theorem B2124107 : Blo 940584 2124107 := bstep (se 1 (by rfl) ⟨1593080, by rfl⟩ : syracuseStep 2124107 = 3186161) B3186161
theorem B944459 : Blo 940584 944459 := bstep (se 1 (by rfl) ⟨708344, by rfl⟩ : syracuseStep 944459 = 1416689) B1416689
theorem B1632599 : Blo 940584 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B944471 : Blo 940584 944471 := bstep (se 1 (by rfl) ⟨708353, by rfl⟩ : syracuseStep 944471 = 1416707) B1416707
theorem B944491 : Blo 940584 944491 := bstep (se 1 (by rfl) ⟨708368, by rfl⟩ : syracuseStep 944491 = 1416737) B1416737
theorem B944503 : Blo 940584 944503 := bstep (se 1 (by rfl) ⟨708377, by rfl⟩ : syracuseStep 944503 = 1416755) B1416755
theorem B2124161 : Blo 940584 2124161 := bstep (se 2 (by rfl) ⟨796560, by rfl⟩ : syracuseStep 2124161 = 1593121) B1593121
theorem B944523 : Blo 940584 944523 := bstep (se 1 (by rfl) ⟨708392, by rfl⟩ : syracuseStep 944523 = 1416785) B1416785
theorem B944535 : Blo 940584 944535 := bstep (se 1 (by rfl) ⟨708401, by rfl⟩ : syracuseStep 944535 = 1416803) B1416803
theorem B944555 : Blo 940584 944555 := bstep (se 1 (by rfl) ⟨708416, by rfl⟩ : syracuseStep 944555 = 1416833) B1416833
theorem B944567 : Blo 940584 944567 := bstep (se 1 (by rfl) ⟨708425, by rfl⟩ : syracuseStep 944567 = 1416851) B1416851
theorem B1698251 : Blo 940584 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B4778513 : Blo 940584 4778513 := bstep (se 2 (by rfl) ⟨1791942, by rfl⟩ : syracuseStep 4778513 = 3583885) B3583885
theorem B2550295 : Blo 940584 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B2124377 : Blo 940584 2124377 := bstep (se 2 (by rfl) ⟨796641, by rfl⟩ : syracuseStep 2124377 = 1593283) B1593283
theorem B4778675 : Blo 940584 4778675 := bstep (se 1 (by rfl) ⟨3584006, by rfl⟩ : syracuseStep 4778675 = 7168013) B7168013
theorem B2124467 : Blo 940584 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B2124503 : Blo 940584 2124503 := bstep (se 1 (by rfl) ⟨1593377, by rfl⟩ : syracuseStep 2124503 = 3186755) B3186755
theorem B17165155 : Blo 940584 17165155 := bstep (se 1 (by rfl) ⟨12873866, by rfl⟩ : syracuseStep 17165155 = 25747733) B25747733
theorem B2124683 : Blo 940584 2124683 := bstep (se 1 (by rfl) ⟨1593512, by rfl⟩ : syracuseStep 2124683 = 3187025) B3187025
theorem B2386867 : Blo 940584 2386867 := bstep (se 1 (by rfl) ⟨1790150, by rfl⟩ : syracuseStep 2386867 = 3580301) B3580301
theorem B2124737 : Blo 940584 2124737 := bstep (se 2 (by rfl) ⟨796776, by rfl⟩ : syracuseStep 2124737 = 1593553) B1593553
theorem B1076171 : Blo 940584 1076171 := bstep (se 1 (by rfl) ⟨807128, by rfl⟩ : syracuseStep 1076171 = 1614257) B1614257
theorem B2387009 : Blo 940584 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B2124953 : Blo 940584 2124953 := bstep (se 2 (by rfl) ⟨796857, by rfl⟩ : syracuseStep 2124953 = 1593715) B1593715
theorem B3402931 : Blo 940584 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B2125043 : Blo 940584 2125043 := bstep (se 1 (by rfl) ⟨1593782, by rfl⟩ : syracuseStep 2125043 = 3187565) B3187565
theorem B2125079 : Blo 940584 2125079 := bstep (se 1 (by rfl) ⟨1593809, by rfl⟩ : syracuseStep 2125079 = 3187619) B3187619
theorem B1699159 : Blo 940584 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B1699211 : Blo 940584 1699211 := bstep (se 1 (by rfl) ⟨1274408, by rfl⟩ : syracuseStep 1699211 = 2548817) B2548817
theorem B5369267 : Blo 940584 5369267 := bstep (se 1 (by rfl) ⟨4026950, by rfl⟩ : syracuseStep 5369267 = 8053901) B8053901
theorem B2125259 : Blo 940584 2125259 := bstep (se 1 (by rfl) ⟨1593944, by rfl⟩ : syracuseStep 2125259 = 3187889) B3187889
theorem B2125313 : Blo 940584 2125313 := bstep (se 2 (by rfl) ⟨796992, by rfl⟩ : syracuseStep 2125313 = 1593985) B1593985
theorem B1863575 : Blo 940584 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B1699735 : Blo 940584 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B1699787 : Blo 940584 1699787 := bstep (se 1 (by rfl) ⟨1274840, by rfl⟩ : syracuseStep 1699787 = 2549681) B2549681
theorem B3829853 : Blo 940584 3829853 := bstep (se 3 (by rfl) ⟨718097, by rfl⟩ : syracuseStep 3829853 = 1436195) B1436195
theorem B3174551 : Blo 940584 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B7172387 : Blo 940584 7172387 := bstep (se 1 (by rfl) ⟨5379290, by rfl⟩ : syracuseStep 7172387 = 10758581) B10758581
theorem B2388275 : Blo 940584 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B12874085 : Blo 940584 12874085 := bstep (se 4 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 12874085 = 2413891) B2413891
theorem B4780619 : Blo 940584 4780619 := bstep (se 1 (by rfl) ⟨3585464, by rfl⟩ : syracuseStep 4780619 = 7170929) B7170929
theorem B1339993 : Blo 940584 1339993 := bstep (se 2 (by rfl) ⟨502497, by rfl⟩ : syracuseStep 1339993 = 1004995) B1004995
theorem B3175091 : Blo 940584 3175091 := bstep (se 1 (by rfl) ⟨2381318, by rfl⟩ : syracuseStep 3175091 = 4762637) B4762637
theorem B2388811 : Blo 940584 2388811 := bstep (se 1 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 2388811 = 3583217) B3583217
theorem B5370725 : Blo 940584 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B3175361 : Blo 940584 3175361 := bstep (se 2 (by rfl) ⟨1190760, by rfl⟩ : syracuseStep 3175361 = 2381521) B2381521
theorem B2388953 : Blo 940584 2388953 := bstep (se 2 (by rfl) ⟨895857, by rfl⟩ : syracuseStep 2388953 = 1791715) B1791715
theorem B9172099 : Blo 940584 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B5371181 : Blo 940584 5371181 := bstep (se 3 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 5371181 = 2014193) B2014193
theorem B3175901 : Blo 940584 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B4027907 : Blo 940584 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B2389783 : Blo 940584 2389783 := bstep (se 1 (by rfl) ⟨1792337, by rfl⟩ : syracuseStep 2389783 = 3584675) B3584675
theorem B17200997 : Blo 940584 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B1701811 : Blo 940584 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B8157145 : Blo 940584 8157145 := bstep (se 2 (by rfl) ⟨3058929, by rfl⟩ : syracuseStep 8157145 = 6117859) B6117859
theorem B5371865 : Blo 940584 5371865 := bstep (se 2 (by rfl) ⟨2014449, by rfl⟩ : syracuseStep 5371865 = 4028899) B4028899
theorem B1341451 : Blo 940584 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B6027281 : Blo 940584 6027281 := bstep (se 2 (by rfl) ⟨2260230, by rfl⟩ : syracuseStep 6027281 = 4520461) B4520461
theorem B1341463 : Blo 940584 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B2390219 : Blo 940584 2390219 := bstep (se 1 (by rfl) ⟨1792664, by rfl⟩ : syracuseStep 2390219 = 3585329) B3585329
theorem B9173197 : Blo 940584 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B10877285 : Blo 940584 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B2390593 : Blo 940584 2390593 := bstep (se 2 (by rfl) ⟨896472, by rfl⟩ : syracuseStep 2390593 = 1792945) B1792945
theorem B3177035 : Blo 940584 3177035 := bstep (se 1 (by rfl) ⟨2382776, by rfl⟩ : syracuseStep 3177035 = 4765553) B4765553
theorem B3177305 : Blo 940584 3177305 := bstep (se 2 (by rfl) ⟨1191489, by rfl⟩ : syracuseStep 3177305 = 2382979) B2382979
theorem B32635747 : Blo 940584 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B2685899 : Blo 940584 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B38763481 : Blo 940584 38763481 := bstep (se 2 (by rfl) ⟨14536305, by rfl⟩ : syracuseStep 38763481 = 29072611) B29072611
theorem B4029533 : Blo 940584 4029533 := bstep (se 3 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 4029533 = 1511075) B1511075
theorem B1506647 : Blo 940584 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B2686297 : Blo 940584 2686297 := bstep (se 2 (by rfl) ⟨1007361, by rfl⟩ : syracuseStep 2686297 = 2014723) B2014723
theorem B3178007 : Blo 940584 3178007 := bstep (se 1 (by rfl) ⟨2383505, by rfl⟩ : syracuseStep 3178007 = 4767011) B4767011
theorem B7241309 : Blo 940584 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B4030231 : Blo 940584 4030231 := bstep (se 1 (by rfl) ⟨3022673, by rfl⟩ : syracuseStep 4030231 = 6045347) B6045347
theorem B6029149 : Blo 940584 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B7143713 : Blo 940584 7143713 := bstep (se 2 (by rfl) ⟨2678892, by rfl⟩ : syracuseStep 7143713 = 5357785) B5357785
theorem B2294273 : Blo 940584 2294273 := bstep (se 2 (by rfl) ⟨860352, by rfl⟩ : syracuseStep 2294273 = 1720705) B1720705
theorem B1344043 : Blo 940584 1344043 := bstep (se 1 (by rfl) ⟨1008032, by rfl⟩ : syracuseStep 1344043 = 2016065) B2016065
theorem B2687755 : Blo 940584 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B3572495 : Blo 940584 3572495 := bstep (se 1 (by rfl) ⟨2679371, by rfl⟩ : syracuseStep 3572495 = 5358743) B5358743
theorem B1344271 : Blo 940584 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B4653883 : Blo 940584 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B3179411 : Blo 940584 3179411 := bstep (se 1 (by rfl) ⟨2384558, by rfl⟩ : syracuseStep 3179411 = 4769117) B4769117
theorem B2688029 : Blo 940584 2688029 := bstep (se 3 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 2688029 = 1008011) B1008011
theorem B4031531 : Blo 940584 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B27133015 : Blo 940584 27133015 := bstep (se 1 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 27133015 = 40699523) B40699523
theorem B7144685 : Blo 940584 7144685 := bstep (se 3 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 7144685 = 2679257) B2679257
theorem B9045341 : Blo 940584 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B9045569 : Blo 940584 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B5375555 : Blo 940584 5375555 := bstep (se 1 (by rfl) ⟨4031666, by rfl⟩ : syracuseStep 5375555 = 8063333) B8063333
theorem B5736023 : Blo 940584 5736023 := bstep (se 1 (by rfl) ⟨4302017, by rfl⟩ : syracuseStep 5736023 = 8604035) B8604035
theorem B1410935 : Blo 940584 1410935 := bstep (se 1 (by rfl) ⟨1058201, by rfl⟩ : syracuseStep 1410935 = 2116403) B2116403
theorem B1410959 : Blo 940584 1410959 := bstep (se 1 (by rfl) ⟨1058219, by rfl⟩ : syracuseStep 1410959 = 2116439) B2116439
theorem B1411001 : Blo 940584 1411001 := bstep (se 2 (by rfl) ⟨529125, by rfl⟩ : syracuseStep 1411001 = 1058251) B1058251
theorem B1411079 : Blo 940584 1411079 := bstep (se 1 (by rfl) ⟨1058309, by rfl⟩ : syracuseStep 1411079 = 2116619) B2116619
theorem B1411115 : Blo 940584 1411115 := bstep (se 1 (by rfl) ⟨1058336, by rfl⟩ : syracuseStep 1411115 = 2116673) B2116673
theorem B1411145 : Blo 940584 1411145 := bstep (se 2 (by rfl) ⟨529179, by rfl⟩ : syracuseStep 1411145 = 1058359) B1058359
theorem B1411259 : Blo 940584 1411259 := bstep (se 1 (by rfl) ⟨1058444, by rfl⟩ : syracuseStep 1411259 = 2116889) B2116889
theorem B1411319 : Blo 940584 1411319 := bstep (se 1 (by rfl) ⟨1058489, by rfl⟩ : syracuseStep 1411319 = 2116979) B2116979
theorem B1411343 : Blo 940584 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B3180815 : Blo 940584 3180815 := bstep (se 1 (by rfl) ⟨2385611, by rfl⟩ : syracuseStep 3180815 = 4771223) B4771223
theorem B1411385 : Blo 940584 1411385 := bstep (se 2 (by rfl) ⟨529269, by rfl⟩ : syracuseStep 1411385 = 1058539) B1058539
theorem B1509691 : Blo 940584 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B1411463 : Blo 940584 1411463 := bstep (se 1 (by rfl) ⟨1058597, by rfl⟩ : syracuseStep 1411463 = 2117195) B2117195
theorem B3574151 : Blo 940584 3574151 := bstep (se 1 (by rfl) ⟨2680613, by rfl⟩ : syracuseStep 3574151 = 5361227) B5361227
theorem B1411499 : Blo 940584 1411499 := bstep (se 1 (by rfl) ⟨1058624, by rfl⟩ : syracuseStep 1411499 = 2117249) B2117249
theorem B1411529 : Blo 940584 1411529 := bstep (se 2 (by rfl) ⟨529323, by rfl⟩ : syracuseStep 1411529 = 1058647) B1058647
theorem B1149431 : Blo 940584 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B3181085 : Blo 940584 3181085 := bstep (se 3 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 3181085 = 1192907) B1192907
theorem B1411643 : Blo 940584 1411643 := bstep (se 1 (by rfl) ⟨1058732, by rfl⟩ : syracuseStep 1411643 = 2117465) B2117465
theorem B1411703 : Blo 940584 1411703 := bstep (se 1 (by rfl) ⟨1058777, by rfl⟩ : syracuseStep 1411703 = 2117555) B2117555
theorem B1411727 : Blo 940584 1411727 := bstep (se 1 (by rfl) ⟨1058795, by rfl⟩ : syracuseStep 1411727 = 2117591) B2117591
theorem B1411769 : Blo 940584 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B1411847 : Blo 940584 1411847 := bstep (se 1 (by rfl) ⟨1058885, by rfl⟩ : syracuseStep 1411847 = 2117771) B2117771
theorem B9046799 : Blo 940584 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B1411883 : Blo 940584 1411883 := bstep (se 1 (by rfl) ⟨1058912, by rfl⟩ : syracuseStep 1411883 = 2117825) B2117825
theorem B1411913 : Blo 940584 1411913 := bstep (se 2 (by rfl) ⟨529467, by rfl⟩ : syracuseStep 1411913 = 1058935) B1058935
theorem B1412027 : Blo 940584 1412027 := bstep (se 1 (by rfl) ⟨1059020, by rfl⟩ : syracuseStep 1412027 = 2118041) B2118041
theorem B1412087 : Blo 940584 1412087 := bstep (se 1 (by rfl) ⟨1059065, by rfl⟩ : syracuseStep 1412087 = 2118131) B2118131
theorem B4033547 : Blo 940584 4033547 := bstep (se 1 (by rfl) ⟨3025160, by rfl⟩ : syracuseStep 4033547 = 6050321) B6050321
theorem B1412111 : Blo 940584 1412111 := bstep (se 1 (by rfl) ⟨1059083, by rfl⟩ : syracuseStep 1412111 = 2118167) B2118167
theorem B1412153 : Blo 940584 1412153 := bstep (se 2 (by rfl) ⟨529557, by rfl⟩ : syracuseStep 1412153 = 1059115) B1059115
theorem B7146629 : Blo 940584 7146629 := bstep (se 4 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 7146629 = 1339993) B1339993
theorem B1412231 : Blo 940584 1412231 := bstep (se 1 (by rfl) ⟨1059173, by rfl⟩ : syracuseStep 1412231 = 2118347) B2118347
theorem B1412267 : Blo 940584 1412267 := bstep (se 1 (by rfl) ⟨1059200, by rfl⟩ : syracuseStep 1412267 = 2118401) B2118401
theorem B1412297 : Blo 940584 1412297 := bstep (se 2 (by rfl) ⟨529611, by rfl⟩ : syracuseStep 1412297 = 1059223) B1059223
theorem B1412411 : Blo 940584 1412411 := bstep (se 1 (by rfl) ⟨1059308, by rfl⟩ : syracuseStep 1412411 = 2118617) B2118617
theorem B10751291 : Blo 940584 10751291 := bstep (se 1 (by rfl) ⟨8063468, by rfl⟩ : syracuseStep 10751291 = 16126937) B16126937
theorem B4033907 : Blo 940584 4033907 := bstep (se 1 (by rfl) ⟨3025430, by rfl⟩ : syracuseStep 4033907 = 6050861) B6050861
theorem B1412471 : Blo 940584 1412471 := bstep (se 1 (by rfl) ⟨1059353, by rfl⟩ : syracuseStep 1412471 = 2118707) B2118707
theorem B1412495 : Blo 940584 1412495 := bstep (se 1 (by rfl) ⟨1059371, by rfl⟩ : syracuseStep 1412495 = 2118743) B2118743
theorem B1412537 : Blo 940584 1412537 := bstep (se 2 (by rfl) ⟨529701, by rfl⟩ : syracuseStep 1412537 = 1059403) B1059403
theorem B1412615 : Blo 940584 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B1412651 : Blo 940584 1412651 := bstep (se 1 (by rfl) ⟨1059488, by rfl⟩ : syracuseStep 1412651 = 2118977) B2118977
theorem B1412681 : Blo 940584 1412681 := bstep (se 2 (by rfl) ⟨529755, by rfl⟩ : syracuseStep 1412681 = 1059511) B1059511
theorem B1412795 : Blo 940584 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B1412855 : Blo 940584 1412855 := bstep (se 1 (by rfl) ⟨1059641, by rfl⟩ : syracuseStep 1412855 = 2119283) B2119283
theorem B1412879 : Blo 940584 1412879 := bstep (se 1 (by rfl) ⟨1059659, by rfl⟩ : syracuseStep 1412879 = 2119319) B2119319
theorem B1511183 : Blo 940584 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B1412921 : Blo 940584 1412921 := bstep (se 2 (by rfl) ⟨529845, by rfl⟩ : syracuseStep 1412921 = 1059691) B1059691
theorem B1412999 : Blo 940584 1412999 := bstep (se 1 (by rfl) ⟨1059749, by rfl⟩ : syracuseStep 1412999 = 2119499) B2119499
theorem B3182489 : Blo 940584 3182489 := bstep (se 2 (by rfl) ⟨1193433, by rfl⟩ : syracuseStep 3182489 = 2386867) B2386867
theorem B1413035 : Blo 940584 1413035 := bstep (se 1 (by rfl) ⟨1059776, by rfl⟩ : syracuseStep 1413035 = 2119553) B2119553
theorem B1413065 : Blo 940584 1413065 := bstep (se 2 (by rfl) ⟨529899, by rfl⟩ : syracuseStep 1413065 = 1059799) B1059799
theorem B1413179 : Blo 940584 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B3575927 : Blo 940584 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B1413239 : Blo 940584 1413239 := bstep (se 1 (by rfl) ⟨1059929, by rfl⟩ : syracuseStep 1413239 = 2119859) B2119859
theorem B1413263 : Blo 940584 1413263 := bstep (se 1 (by rfl) ⟨1059947, by rfl⟩ : syracuseStep 1413263 = 2119895) B2119895
theorem B1413305 : Blo 940584 1413305 := bstep (se 2 (by rfl) ⟨529989, by rfl⟩ : syracuseStep 1413305 = 1059979) B1059979
theorem B1413383 : Blo 940584 1413383 := bstep (se 1 (by rfl) ⟨1060037, by rfl⟩ : syracuseStep 1413383 = 2120075) B2120075
theorem B2724125 : Blo 940584 2724125 := bstep (se 3 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 2724125 = 1021547) B1021547
theorem B1413419 : Blo 940584 1413419 := bstep (se 1 (by rfl) ⟨1060064, by rfl⟩ : syracuseStep 1413419 = 2120129) B2120129
theorem B1413449 : Blo 940584 1413449 := bstep (se 2 (by rfl) ⟨530043, by rfl⟩ : syracuseStep 1413449 = 1060087) B1060087
theorem B9671005 : Blo 940584 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B1413563 : Blo 940584 1413563 := bstep (se 1 (by rfl) ⟨1060172, by rfl⟩ : syracuseStep 1413563 = 2120345) B2120345
theorem B2265545 : Blo 940584 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B1413623 : Blo 940584 1413623 := bstep (se 1 (by rfl) ⟨1060217, by rfl⟩ : syracuseStep 1413623 = 2120435) B2120435
theorem B1413647 : Blo 940584 1413647 := bstep (se 1 (by rfl) ⟨1060235, by rfl⟩ : syracuseStep 1413647 = 2120471) B2120471
theorem B1413689 : Blo 940584 1413689 := bstep (se 2 (by rfl) ⟨530133, by rfl⟩ : syracuseStep 1413689 = 1060267) B1060267
theorem B3183191 : Blo 940584 3183191 := bstep (se 1 (by rfl) ⟨2387393, by rfl⟩ : syracuseStep 3183191 = 4774787) B4774787
theorem B1413767 : Blo 940584 1413767 := bstep (se 1 (by rfl) ⟨1060325, by rfl⟩ : syracuseStep 1413767 = 2120651) B2120651
theorem B1413803 : Blo 940584 1413803 := bstep (se 1 (by rfl) ⟨1060352, by rfl⟩ : syracuseStep 1413803 = 2120705) B2120705
theorem B1413833 : Blo 940584 1413833 := bstep (se 2 (by rfl) ⟨530187, by rfl⟩ : syracuseStep 1413833 = 1060375) B1060375
theorem B7639859 : Blo 940584 7639859 := bstep (se 1 (by rfl) ⟨5729894, by rfl⟩ : syracuseStep 7639859 = 11459789) B11459789
theorem B1413947 : Blo 940584 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B1414007 : Blo 940584 1414007 := bstep (se 1 (by rfl) ⟨1060505, by rfl⟩ : syracuseStep 1414007 = 2121011) B2121011
theorem B1414031 : Blo 940584 1414031 := bstep (se 1 (by rfl) ⟨1060523, by rfl⟩ : syracuseStep 1414031 = 2121047) B2121047
theorem B1414073 : Blo 940584 1414073 := bstep (se 2 (by rfl) ⟨530277, by rfl⟩ : syracuseStep 1414073 = 1060555) B1060555
theorem B1414151 : Blo 940584 1414151 := bstep (se 1 (by rfl) ⟨1060613, by rfl⟩ : syracuseStep 1414151 = 2121227) B2121227
theorem B1414187 : Blo 940584 1414187 := bstep (se 1 (by rfl) ⟨1060640, by rfl⟩ : syracuseStep 1414187 = 2121281) B2121281
theorem B3183677 : Blo 940584 3183677 := bstep (se 3 (by rfl) ⟨596939, by rfl⟩ : syracuseStep 3183677 = 1193879) B1193879
theorem B4199485 : Blo 940584 4199485 := bstep (se 3 (by rfl) ⟨787403, by rfl⟩ : syracuseStep 4199485 = 1574807) B1574807
theorem B3576899 : Blo 940584 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B1414217 : Blo 940584 1414217 := bstep (se 2 (by rfl) ⟨530331, by rfl⟩ : syracuseStep 1414217 = 1060663) B1060663
theorem B1414331 : Blo 940584 1414331 := bstep (se 1 (by rfl) ⟨1060748, by rfl⟩ : syracuseStep 1414331 = 2121497) B2121497
theorem B2266313 : Blo 940584 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B18093293 : Blo 940584 18093293 := bstep (se 3 (by rfl) ⟨3392492, by rfl⟩ : syracuseStep 18093293 = 6784985) B6784985
theorem B1414391 : Blo 940584 1414391 := bstep (se 1 (by rfl) ⟨1060793, by rfl⟩ : syracuseStep 1414391 = 2121587) B2121587
theorem B1414415 : Blo 940584 1414415 := bstep (se 1 (by rfl) ⟨1060811, by rfl⟩ : syracuseStep 1414415 = 2121623) B2121623
theorem B1414457 : Blo 940584 1414457 := bstep (se 2 (by rfl) ⟨530421, by rfl⟩ : syracuseStep 1414457 = 1060843) B1060843
theorem B1414535 : Blo 940584 1414535 := bstep (se 1 (by rfl) ⟨1060901, by rfl⟩ : syracuseStep 1414535 = 2121803) B2121803
theorem B5379473 : Blo 940584 5379473 := bstep (se 2 (by rfl) ⟨2017302, by rfl⟩ : syracuseStep 5379473 = 4034605) B4034605
theorem B1414571 : Blo 940584 1414571 := bstep (se 1 (by rfl) ⟨1060928, by rfl⟩ : syracuseStep 1414571 = 2121857) B2121857
theorem B1414601 : Blo 940584 1414601 := bstep (se 2 (by rfl) ⟨530475, by rfl⟩ : syracuseStep 1414601 = 1060951) B1060951
theorem B7149059 : Blo 940584 7149059 := bstep (se 1 (by rfl) ⟨5361794, by rfl⟩ : syracuseStep 7149059 = 10723589) B10723589
theorem B3577355 : Blo 940584 3577355 := bstep (se 1 (by rfl) ⟨2683016, by rfl⟩ : syracuseStep 3577355 = 5366033) B5366033
theorem B1414715 : Blo 940584 1414715 := bstep (se 1 (by rfl) ⟨1061036, by rfl⟩ : syracuseStep 1414715 = 2122073) B2122073
theorem B1414775 : Blo 940584 1414775 := bstep (se 1 (by rfl) ⟨1061081, by rfl⟩ : syracuseStep 1414775 = 2122163) B2122163
theorem B1414799 : Blo 940584 1414799 := bstep (se 1 (by rfl) ⟨1061099, by rfl⟩ : syracuseStep 1414799 = 2122199) B2122199
theorem B1414841 : Blo 940584 1414841 := bstep (se 2 (by rfl) ⟨530565, by rfl⟩ : syracuseStep 1414841 = 1061131) B1061131
theorem B1414919 : Blo 940584 1414919 := bstep (se 1 (by rfl) ⟨1061189, by rfl⟩ : syracuseStep 1414919 = 2122379) B2122379
theorem B1414955 : Blo 940584 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B1414985 : Blo 940584 1414985 := bstep (se 2 (by rfl) ⟨530619, by rfl⟩ : syracuseStep 1414985 = 1061239) B1061239
theorem B1415099 : Blo 940584 1415099 := bstep (se 1 (by rfl) ⟨1061324, by rfl⟩ : syracuseStep 1415099 = 2122649) B2122649
theorem B1415159 : Blo 940584 1415159 := bstep (se 1 (by rfl) ⟨1061369, by rfl⟩ : syracuseStep 1415159 = 2122739) B2122739
theorem B1415183 : Blo 940584 1415183 := bstep (se 1 (by rfl) ⟨1061387, by rfl⟩ : syracuseStep 1415183 = 2122775) B2122775
theorem B1415225 : Blo 940584 1415225 := bstep (se 2 (by rfl) ⟨530709, by rfl⟩ : syracuseStep 1415225 = 1061419) B1061419
theorem B1415303 : Blo 940584 1415303 := bstep (se 1 (by rfl) ⟨1061477, by rfl⟩ : syracuseStep 1415303 = 2122955) B2122955
theorem B1415339 : Blo 940584 1415339 := bstep (se 1 (by rfl) ⟨1061504, by rfl⟩ : syracuseStep 1415339 = 2123009) B2123009
theorem B1415369 : Blo 940584 1415369 := bstep (se 2 (by rfl) ⟨530763, by rfl⟩ : syracuseStep 1415369 = 1061527) B1061527
theorem B29006093 : Blo 940584 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B1415483 : Blo 940584 1415483 := bstep (se 1 (by rfl) ⟨1061612, by rfl⟩ : syracuseStep 1415483 = 2123225) B2123225
theorem B1415543 : Blo 940584 1415543 := bstep (se 1 (by rfl) ⟨1061657, by rfl⟩ : syracuseStep 1415543 = 2123315) B2123315
theorem B1415567 : Blo 940584 1415567 := bstep (se 1 (by rfl) ⟨1061675, by rfl⟩ : syracuseStep 1415567 = 2123351) B2123351
theorem B3185081 : Blo 940584 3185081 := bstep (se 2 (by rfl) ⟨1194405, by rfl⟩ : syracuseStep 3185081 = 2388811) B2388811
theorem B1415609 : Blo 940584 1415609 := bstep (se 2 (by rfl) ⟨530853, by rfl⟩ : syracuseStep 1415609 = 1061707) B1061707
theorem B1415687 : Blo 940584 1415687 := bstep (se 1 (by rfl) ⟨1061765, by rfl⟩ : syracuseStep 1415687 = 2123531) B2123531
theorem B4528669 : Blo 940584 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B1415723 : Blo 940584 1415723 := bstep (se 1 (by rfl) ⟨1061792, by rfl⟩ : syracuseStep 1415723 = 2123585) B2123585
theorem B1415753 : Blo 940584 1415753 := bstep (se 2 (by rfl) ⟨530907, by rfl⟩ : syracuseStep 1415753 = 1061815) B1061815
theorem B1415867 : Blo 940584 1415867 := bstep (se 1 (by rfl) ⟨1061900, by rfl⟩ : syracuseStep 1415867 = 2123801) B2123801
theorem B957115 : Blo 940584 957115 := bstep (se 1 (by rfl) ⟨717836, by rfl⟩ : syracuseStep 957115 = 1435673) B1435673
theorem B1415927 : Blo 940584 1415927 := bstep (se 1 (by rfl) ⟨1061945, by rfl⟩ : syracuseStep 1415927 = 2123891) B2123891
theorem B1415951 : Blo 940584 1415951 := bstep (se 1 (by rfl) ⟨1061963, by rfl⟩ : syracuseStep 1415951 = 2123927) B2123927
theorem B1415993 : Blo 940584 1415993 := bstep (se 2 (by rfl) ⟨530997, by rfl⟩ : syracuseStep 1415993 = 1061995) B1061995
theorem B12229465 : Blo 940584 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B1416071 : Blo 940584 1416071 := bstep (se 1 (by rfl) ⟨1062053, by rfl⟩ : syracuseStep 1416071 = 2124107) B2124107
theorem B1088399 : Blo 940584 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B1416107 : Blo 940584 1416107 := bstep (se 1 (by rfl) ⟨1062080, by rfl⟩ : syracuseStep 1416107 = 2124161) B2124161
theorem B1416137 : Blo 940584 1416137 := bstep (se 2 (by rfl) ⟨531051, by rfl⟩ : syracuseStep 1416137 = 1062103) B1062103
theorem B3185675 : Blo 940584 3185675 := bstep (se 1 (by rfl) ⟨2389256, by rfl⟩ : syracuseStep 3185675 = 4778513) B4778513
theorem B1416251 : Blo 940584 1416251 := bstep (se 1 (by rfl) ⟨1062188, by rfl⟩ : syracuseStep 1416251 = 2124377) B2124377
theorem B3185783 : Blo 940584 3185783 := bstep (se 1 (by rfl) ⟨2389337, by rfl⟩ : syracuseStep 3185783 = 4778675) B4778675
theorem B1416311 : Blo 940584 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B1416335 : Blo 940584 1416335 := bstep (se 1 (by rfl) ⟨1062251, by rfl⟩ : syracuseStep 1416335 = 2124503) B2124503
theorem B1416377 : Blo 940584 1416377 := bstep (se 2 (by rfl) ⟨531141, by rfl⟩ : syracuseStep 1416377 = 1062283) B1062283
theorem B3218633 : Blo 940584 3218633 := bstep (se 2 (by rfl) ⟨1206987, by rfl⟩ : syracuseStep 3218633 = 2413975) B2413975
theorem B1416455 : Blo 940584 1416455 := bstep (se 1 (by rfl) ⟨1062341, by rfl⟩ : syracuseStep 1416455 = 2124683) B2124683
theorem B1416491 : Blo 940584 1416491 := bstep (se 1 (by rfl) ⟨1062368, by rfl⟩ : syracuseStep 1416491 = 2124737) B2124737
theorem B1416521 : Blo 940584 1416521 := bstep (se 2 (by rfl) ⟨531195, by rfl⟩ : syracuseStep 1416521 = 1062391) B1062391
theorem B1416635 : Blo 940584 1416635 := bstep (se 1 (by rfl) ⟨1062476, by rfl⟩ : syracuseStep 1416635 = 2124953) B2124953
theorem B1416695 : Blo 940584 1416695 := bstep (se 1 (by rfl) ⟨1062521, by rfl⟩ : syracuseStep 1416695 = 2125043) B2125043
theorem B1416719 : Blo 940584 1416719 := bstep (se 1 (by rfl) ⟨1062539, by rfl⟩ : syracuseStep 1416719 = 2125079) B2125079
theorem B1416761 : Blo 940584 1416761 := bstep (se 2 (by rfl) ⟨531285, by rfl⟩ : syracuseStep 1416761 = 1062571) B1062571
theorem B4529783 : Blo 940584 4529783 := bstep (se 1 (by rfl) ⟨3397337, by rfl⟩ : syracuseStep 4529783 = 6794675) B6794675
theorem B3579511 : Blo 940584 3579511 := bstep (se 1 (by rfl) ⟨2684633, by rfl⟩ : syracuseStep 3579511 = 5369267) B5369267
theorem B1416839 : Blo 940584 1416839 := bstep (se 1 (by rfl) ⟨1062629, by rfl⟩ : syracuseStep 1416839 = 2125259) B2125259
theorem B1416875 : Blo 940584 1416875 := bstep (se 1 (by rfl) ⟨1062656, by rfl⟩ : syracuseStep 1416875 = 2125313) B2125313
theorem B3186377 : Blo 940584 3186377 := bstep (se 2 (by rfl) ⟨1194891, by rfl⟩ : syracuseStep 3186377 = 2389783) B2389783
theorem B13573889 : Blo 940584 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B5447425 : Blo 940584 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B5447513 : Blo 940584 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B2269081 : Blo 940584 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B12230929 : Blo 940584 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B3187079 : Blo 940584 3187079 := bstep (se 1 (by rfl) ⟨2390309, by rfl⟩ : syracuseStep 3187079 = 4780619) B4780619
theorem B3580483 : Blo 940584 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B3187457 : Blo 940584 3187457 := bstep (se 2 (by rfl) ⟨1195296, by rfl⟩ : syracuseStep 3187457 = 2390593) B2390593
theorem B3580787 : Blo 940584 3580787 := bstep (se 1 (by rfl) ⟨2685590, by rfl⟩ : syracuseStep 3580787 = 5371181) B5371181
theorem B2041121 : Blo 940584 2041121 := bstep (se 2 (by rfl) ⟨765420, by rfl⟩ : syracuseStep 2041121 = 1530841) B1530841
theorem B3024161 : Blo 940584 3024161 := bstep (se 2 (by rfl) ⟨1134060, by rfl⟩ : syracuseStep 3024161 = 2268121) B2268121
theorem B51684641 : Blo 940584 51684641 := bstep (se 2 (by rfl) ⟨19381740, by rfl⟩ : syracuseStep 51684641 = 38763481) B38763481
theorem B3581243 : Blo 940584 3581243 := bstep (se 1 (by rfl) ⟨2685932, by rfl⟩ : syracuseStep 3581243 = 5371865) B5371865
theorem B14526209 : Blo 940584 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B1058575 : Blo 940584 1058575 := bstep (se 1 (by rfl) ⟨793931, by rfl⟩ : syracuseStep 1058575 = 1587863) B1587863
theorem B3581729 : Blo 940584 3581729 := bstep (se 2 (by rfl) ⟨1343148, by rfl⟩ : syracuseStep 3581729 = 2686297) B2686297
theorem B1059079 : Blo 940584 1059079 := bstep (se 1 (by rfl) ⟨794309, by rfl⟩ : syracuseStep 1059079 = 1588619) B1588619
theorem B4827539 : Blo 940584 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B1059259 : Blo 940584 1059259 := bstep (se 1 (by rfl) ⟨794444, by rfl⟩ : syracuseStep 1059259 = 1588889) B1588889
theorem B1812937 : Blo 940584 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B8038865 : Blo 940584 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B2009785 : Blo 940584 2009785 := bstep (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) B1507339
theorem B4762313 : Blo 940584 4762313 := bstep (se 2 (by rfl) ⟨1785867, by rfl⟩ : syracuseStep 4762313 = 3571735) B3571735
theorem B7154405 : Blo 940584 7154405 := bstep (se 4 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 7154405 = 1341451) B1341451
theorem B3582701 : Blo 940584 3582701 := bstep (se 3 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 3582701 = 1343513) B1343513
theorem B23538437 : Blo 940584 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B4893529 : Blo 940584 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B1190791 : Blo 940584 1190791 := bstep (se 1 (by rfl) ⟨893093, by rfl⟩ : syracuseStep 1190791 = 1786187) B1786187
theorem B1059727 : Blo 940584 1059727 := bstep (se 1 (by rfl) ⟨794795, by rfl⟩ : syracuseStep 1059727 = 1589591) B1589591
theorem B1191287 : Blo 940584 1191287 := bstep (se 1 (by rfl) ⟨893465, by rfl⟩ : syracuseStep 1191287 = 1786931) B1786931
theorem B2010503 : Blo 940584 2010503 := bstep (se 1 (by rfl) ⟨1507877, by rfl⟩ : syracuseStep 2010503 = 3015755) B3015755
theorem B1060231 : Blo 940584 1060231 := bstep (se 1 (by rfl) ⟨795173, by rfl⟩ : syracuseStep 1060231 = 1590347) B1590347
theorem B3583385 : Blo 940584 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B4599193 : Blo 940584 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B1191439 : Blo 940584 1191439 := bstep (se 1 (by rfl) ⟨893579, by rfl⟩ : syracuseStep 1191439 = 1787159) B1787159
theorem B1060411 : Blo 940584 1060411 := bstep (se 1 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 1060411 = 1590617) B1590617
theorem B18132659 : Blo 940584 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B1191611 : Blo 940584 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B1912609 : Blo 940584 1912609 := bstep (se 2 (by rfl) ⟨717228, by rfl⟩ : syracuseStep 1912609 = 1434457) B1434457
theorem B4829017 : Blo 940584 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B2011015 : Blo 940584 2011015 := bstep (se 1 (by rfl) ⟨1508261, by rfl⟩ : syracuseStep 2011015 = 3016523) B3016523
theorem B1060879 : Blo 940584 1060879 := bstep (se 1 (by rfl) ⟨795659, by rfl⟩ : syracuseStep 1060879 = 1591319) B1591319
theorem B2011169 : Blo 940584 2011169 := bstep (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) B1508377
theorem B3584371 : Blo 940584 3584371 := bstep (se 1 (by rfl) ⟨2688278, by rfl⟩ : syracuseStep 3584371 = 5376557) B5376557
theorem B1061383 : Blo 940584 1061383 := bstep (se 1 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 1061383 = 1592075) B1592075
theorem B2011691 : Blo 940584 2011691 := bstep (se 1 (by rfl) ⟨1508768, by rfl⟩ : syracuseStep 2011691 = 3017537) B3017537
theorem B1192583 : Blo 940584 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B1061563 : Blo 940584 1061563 := bstep (se 1 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 1061563 = 1592345) B1592345
theorem B23540441 : Blo 940584 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B1062031 : Blo 940584 1062031 := bstep (se 1 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 1062031 = 1593047) B1593047
theorem B1193231 : Blo 940584 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B5813689 : Blo 940584 5813689 := bstep (se 2 (by rfl) ⟨2180133, by rfl⟩ : syracuseStep 5813689 = 4360267) B4360267
theorem B1455607 : Blo 940584 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B8599069 : Blo 940584 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B1062535 : Blo 940584 1062535 := bstep (se 1 (by rfl) ⟨796901, by rfl⟩ : syracuseStep 1062535 = 1593803) B1593803
theorem B29407093 : Blo 940584 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B2865287 : Blo 940584 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B2013331 : Blo 940584 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B22886873 : Blo 940584 22886873 := bstep (se 2 (by rfl) ⟨8582577, by rfl⟩ : syracuseStep 22886873 = 17165155) B17165155
theorem B6797789 : Blo 940584 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B2865665 : Blo 940584 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B1587755 : Blo 940584 1587755 := bstep (se 1 (by rfl) ⟨1190816, by rfl⟩ : syracuseStep 1587755 = 2381633) B2381633
theorem B2866067 : Blo 940584 2866067 := bstep (se 1 (by rfl) ⟨2149550, by rfl⟩ : syracuseStep 2866067 = 4299101) B4299101
theorem B4537241 : Blo 940584 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B1588153 : Blo 940584 1588153 := bstep (se 2 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 1588153 = 1191115) B1191115
theorem B10894283 : Blo 940584 10894283 := bstep (se 1 (by rfl) ⟨8170712, by rfl⟩ : syracuseStep 10894283 = 16341425) B16341425
theorem B1359289 : Blo 940584 1359289 := bstep (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) B1019467
theorem B1588855 : Blo 940584 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B18103985 : Blo 940584 18103985 := bstep (se 2 (by rfl) ⟨6788994, by rfl⟩ : syracuseStep 18103985 = 13577989) B13577989
theorem B5357285 : Blo 940584 5357285 := bstep (se 4 (by rfl) ⟨502245, by rfl⟩ : syracuseStep 5357285 = 1004491) B1004491
theorem B1130231 : Blo 940584 1130231 := bstep (se 1 (by rfl) ⟨847673, by rfl⟩ : syracuseStep 1130231 = 1695347) B1695347
theorem B1589051 : Blo 940584 1589051 := bstep (se 1 (by rfl) ⟨1191788, by rfl⟩ : syracuseStep 1589051 = 2383577) B2383577
theorem B3063737 : Blo 940584 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B1130539 : Blo 940584 1130539 := bstep (se 1 (by rfl) ⟨847904, by rfl⟩ : syracuseStep 1130539 = 1695809) B1695809
theorem B11452589 : Blo 940584 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B1589449 : Blo 940584 1589449 := bstep (se 2 (by rfl) ⟨596043, by rfl⟩ : syracuseStep 1589449 = 1192087) B1192087
theorem B4768145 : Blo 940584 4768145 := bstep (se 2 (by rfl) ⟨1788054, by rfl⟩ : syracuseStep 4768145 = 3576109) B3576109
theorem B23249443 : Blo 940584 23249443 := bstep (se 1 (by rfl) ⟨17437082, by rfl⟩ : syracuseStep 23249443 = 34874165) B34874165
theorem B10732337 : Blo 940584 10732337 := bstep (se 2 (by rfl) ⟨4024626, by rfl⟩ : syracuseStep 10732337 = 8049253) B8049253
theorem B1590151 : Blo 940584 1590151 := bstep (se 1 (by rfl) ⟨1192613, by rfl⟩ : syracuseStep 1590151 = 2385227) B2385227
theorem B30983093 : Blo 940584 30983093 := bstep (se 5 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 30983093 = 2904665) B2904665
theorem B1787015 : Blo 940584 1787015 := bstep (se 1 (by rfl) ⟨1340261, by rfl⟩ : syracuseStep 1787015 = 2680523) B2680523
theorem B1590799 : Blo 940584 1590799 := bstep (se 1 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 1590799 = 2386199) B2386199
theorem B2868779 : Blo 940584 2868779 := bstep (se 1 (by rfl) ⟨2151584, by rfl⟩ : syracuseStep 2868779 = 4303169) B4303169
theorem B2017295 : Blo 940584 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B1591339 : Blo 940584 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B1591481 : Blo 940584 1591481 := bstep (se 2 (by rfl) ⟨596805, by rfl⟩ : syracuseStep 1591481 = 1193611) B1193611
theorem B1132807 : Blo 940584 1132807 := bstep (se 1 (by rfl) ⟨849605, by rfl⟩ : syracuseStep 1132807 = 1699211) B1699211
theorem B4770251 : Blo 940584 4770251 := bstep (se 1 (by rfl) ⟨3577688, by rfl⟩ : syracuseStep 4770251 = 7155377) B7155377
theorem B2869789 : Blo 940584 2869789 := bstep (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) B1076171
theorem B1133191 : Blo 940584 1133191 := bstep (se 1 (by rfl) ⟨849893, by rfl⟩ : syracuseStep 1133191 = 1699787) B1699787
theorem B1788617 : Blo 940584 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B3066569 : Blo 940584 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B2116367 : Blo 940584 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B4770575 : Blo 940584 4770575 := bstep (se 1 (by rfl) ⟨3577931, by rfl⟩ : syracuseStep 4770575 = 7155863) B7155863
theorem B2116385 : Blo 940584 2116385 := bstep (se 2 (by rfl) ⟨793644, by rfl⟩ : syracuseStep 2116385 = 1587289) B1587289
theorem B1592183 : Blo 940584 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B5360519 : Blo 940584 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B5229521 : Blo 940584 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B5360701 : Blo 940584 5360701 := bstep (se 3 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 5360701 = 2010263) B2010263
theorem B2116727 : Blo 940584 2116727 := bstep (se 1 (by rfl) ⟨1587545, by rfl⟩ : syracuseStep 2116727 = 3175091) B3175091
theorem B11488493 : Blo 940584 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B2116907 : Blo 940584 2116907 := bstep (se 1 (by rfl) ⟨1587680, by rfl⟩ : syracuseStep 2116907 = 3175361) B3175361
theorem B1592635 : Blo 940584 1592635 := bstep (se 1 (by rfl) ⟨1194476, by rfl⟩ : syracuseStep 1592635 = 2388953) B2388953
theorem B1592777 : Blo 940584 1592777 := bstep (se 2 (by rfl) ⟨597291, by rfl⟩ : syracuseStep 1592777 = 1194583) B1194583
theorem B4017725 : Blo 940584 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B2117267 : Blo 940584 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B2117321 : Blo 940584 2117321 := bstep (se 2 (by rfl) ⟨793995, by rfl⟩ : syracuseStep 2117321 = 1587991) B1587991
theorem B2543375 : Blo 940584 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B2150345 : Blo 940584 2150345 := bstep (se 2 (by rfl) ⟨806379, by rfl⟩ : syracuseStep 2150345 = 1612759) B1612759
theorem B10899461 : Blo 940584 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B4018187 : Blo 940584 4018187 := bstep (se 1 (by rfl) ⟨3013640, by rfl⟩ : syracuseStep 4018187 = 6027281) B6027281
theorem B1593479 : Blo 940584 1593479 := bstep (se 1 (by rfl) ⟨1195109, by rfl⟩ : syracuseStep 1593479 = 2390219) B2390219
theorem B4772033 : Blo 940584 4772033 := bstep (se 2 (by rfl) ⟨1789512, by rfl⟩ : syracuseStep 4772033 = 3579025) B3579025
theorem B2118023 : Blo 940584 2118023 := bstep (se 1 (by rfl) ⟨1588517, by rfl⟩ : syracuseStep 2118023 = 3177035) B3177035
theorem B2871737 : Blo 940584 2871737 := bstep (se 2 (by rfl) ⟨1076901, by rfl⟩ : syracuseStep 2871737 = 2153803) B2153803
theorem B2118203 : Blo 940584 2118203 := bstep (se 1 (by rfl) ⟨1588652, by rfl⟩ : syracuseStep 2118203 = 3177305) B3177305
theorem B1790599 : Blo 940584 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B2118329 : Blo 940584 2118329 := bstep (se 2 (by rfl) ⟨794373, by rfl⟩ : syracuseStep 2118329 = 1588747) B1588747
theorem B5362433 : Blo 940584 5362433 := bstep (se 2 (by rfl) ⟨2010912, by rfl⟩ : syracuseStep 5362433 = 4021825) B4021825
theorem B2118671 : Blo 940584 2118671 := bstep (se 1 (by rfl) ⟨1589003, by rfl⟩ : syracuseStep 2118671 = 3178007) B3178007
theorem B2118689 : Blo 940584 2118689 := bstep (se 2 (by rfl) ⟨794508, by rfl⟩ : syracuseStep 2118689 = 1589017) B1589017
theorem B2380985 : Blo 940584 2380985 := bstep (se 2 (by rfl) ⟨892869, by rfl⟩ : syracuseStep 2380985 = 1785739) B1785739
theorem B15521057 : Blo 940584 15521057 := bstep (se 2 (by rfl) ⟨5820396, by rfl⟩ : syracuseStep 15521057 = 11640793) B11640793
theorem B2119031 : Blo 940584 2119031 := bstep (se 1 (by rfl) ⟨1589273, by rfl⟩ : syracuseStep 2119031 = 3178547) B3178547
theorem B3397049 : Blo 940584 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B4773329 : Blo 940584 4773329 := bstep (se 2 (by rfl) ⟨1789998, by rfl⟩ : syracuseStep 4773329 = 3579997) B3579997
theorem B6051293 : Blo 940584 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B2119211 : Blo 940584 2119211 := bstep (se 1 (by rfl) ⟨1589408, by rfl⟩ : syracuseStep 2119211 = 3178817) B3178817
theorem B10212941 : Blo 940584 10212941 := bstep (se 3 (by rfl) ⟨1914926, by rfl⟩ : syracuseStep 10212941 = 3829853) B3829853
theorem B2381683 : Blo 940584 2381683 := bstep (se 1 (by rfl) ⟨1786262, by rfl⟩ : syracuseStep 2381683 = 3572525) B3572525
theorem B2119571 : Blo 940584 2119571 := bstep (se 1 (by rfl) ⟨1589678, by rfl⟩ : syracuseStep 2119571 = 3179357) B3179357
theorem B2119625 : Blo 940584 2119625 := bstep (se 2 (by rfl) ⟨794859, by rfl⟩ : syracuseStep 2119625 = 1589719) B1589719
theorem B2381825 : Blo 940584 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B4020425 : Blo 940584 4020425 := bstep (se 2 (by rfl) ⟨1507659, by rfl⟩ : syracuseStep 4020425 = 3015319) B3015319
theorem B1792201 : Blo 940584 1792201 := bstep (se 2 (by rfl) ⟨672075, by rfl⟩ : syracuseStep 1792201 = 1344151) B1344151
theorem B43538705 : Blo 940584 43538705 := bstep (se 2 (by rfl) ⟨16327014, by rfl⟩ : syracuseStep 43538705 = 32654029) B32654029
theorem B1431865 : Blo 940584 1431865 := bstep (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) B1073899
theorem B2382281 : Blo 940584 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B940603 : Blo 940584 940603 := bstep (se 1 (by rfl) ⟨705452, by rfl⟩ : syracuseStep 940603 = 1410905) B1410905
theorem B940679 : Blo 940584 940679 := bstep (se 1 (by rfl) ⟨705509, by rfl⟩ : syracuseStep 940679 = 1411019) B1411019
theorem B2120327 : Blo 940584 2120327 := bstep (se 1 (by rfl) ⟨1590245, by rfl⟩ : syracuseStep 2120327 = 3180491) B3180491
theorem B940687 : Blo 940584 940687 := bstep (se 1 (by rfl) ⟨705515, by rfl⟩ : syracuseStep 940687 = 1411031) B1411031
theorem B940731 : Blo 940584 940731 := bstep (se 1 (by rfl) ⟨705548, by rfl⟩ : syracuseStep 940731 = 1411097) B1411097
theorem B940807 : Blo 940584 940807 := bstep (se 1 (by rfl) ⟨705605, by rfl⟩ : syracuseStep 940807 = 1411211) B1411211
theorem B940815 : Blo 940584 940815 := bstep (se 1 (by rfl) ⟨705611, by rfl⟩ : syracuseStep 940815 = 1411223) B1411223
theorem B2382635 : Blo 940584 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B6806321 : Blo 940584 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B940859 : Blo 940584 940859 := bstep (se 1 (by rfl) ⟨705644, by rfl⟩ : syracuseStep 940859 = 1411289) B1411289
theorem B2120507 : Blo 940584 2120507 := bstep (se 1 (by rfl) ⟨1590380, by rfl⟩ : syracuseStep 2120507 = 3180761) B3180761
theorem B940935 : Blo 940584 940935 := bstep (se 1 (by rfl) ⟨705701, by rfl⟩ : syracuseStep 940935 = 1411403) B1411403
theorem B940943 : Blo 940584 940943 := bstep (se 1 (by rfl) ⟨705707, by rfl⟩ : syracuseStep 940943 = 1411415) B1411415
theorem B21748661 : Blo 940584 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B2120633 : Blo 940584 2120633 := bstep (se 2 (by rfl) ⟨795237, by rfl⟩ : syracuseStep 2120633 = 1590475) B1590475
theorem B940987 : Blo 940584 940987 := bstep (se 1 (by rfl) ⟨705740, by rfl⟩ : syracuseStep 940987 = 1411481) B1411481
theorem B941063 : Blo 940584 941063 := bstep (se 1 (by rfl) ⟨705797, by rfl⟩ : syracuseStep 941063 = 1411595) B1411595
theorem B941071 : Blo 940584 941071 := bstep (se 1 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 941071 = 1411607) B1411607
theorem B941115 : Blo 940584 941115 := bstep (se 1 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 941115 = 1411673) B1411673
theorem B941191 : Blo 940584 941191 := bstep (se 1 (by rfl) ⟨705893, by rfl⟩ : syracuseStep 941191 = 1411787) B1411787
theorem B941199 : Blo 940584 941199 := bstep (se 1 (by rfl) ⟨705899, by rfl⟩ : syracuseStep 941199 = 1411799) B1411799
theorem B941243 : Blo 940584 941243 := bstep (se 1 (by rfl) ⟨705932, by rfl⟩ : syracuseStep 941243 = 1411865) B1411865
theorem B941319 : Blo 940584 941319 := bstep (se 1 (by rfl) ⟨705989, by rfl⟩ : syracuseStep 941319 = 1411979) B1411979
theorem B941327 : Blo 940584 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B2120975 : Blo 940584 2120975 := bstep (se 1 (by rfl) ⟨1590731, by rfl⟩ : syracuseStep 2120975 = 3181463) B3181463
theorem B2120993 : Blo 940584 2120993 := bstep (se 2 (by rfl) ⟨795372, by rfl⟩ : syracuseStep 2120993 = 1590745) B1590745
theorem B941371 : Blo 940584 941371 := bstep (se 1 (by rfl) ⟨706028, by rfl⟩ : syracuseStep 941371 = 1412057) B1412057
theorem B941447 : Blo 940584 941447 := bstep (se 1 (by rfl) ⟨706085, by rfl⟩ : syracuseStep 941447 = 1412171) B1412171
theorem B941455 : Blo 940584 941455 := bstep (se 1 (by rfl) ⟨706091, by rfl⟩ : syracuseStep 941455 = 1412183) B1412183
theorem B941499 : Blo 940584 941499 := bstep (se 1 (by rfl) ⟨706124, by rfl⟩ : syracuseStep 941499 = 1412249) B1412249
theorem B941575 : Blo 940584 941575 := bstep (se 1 (by rfl) ⟨706181, by rfl⟩ : syracuseStep 941575 = 1412363) B1412363
theorem B4775435 : Blo 940584 4775435 := bstep (se 1 (by rfl) ⟨3581576, by rfl⟩ : syracuseStep 4775435 = 7163153) B7163153
theorem B941583 : Blo 940584 941583 := bstep (se 1 (by rfl) ⟨706187, by rfl⟩ : syracuseStep 941583 = 1412375) B1412375
theorem B941627 : Blo 940584 941627 := bstep (se 1 (by rfl) ⟨706220, by rfl⟩ : syracuseStep 941627 = 1412441) B1412441
theorem B2121335 : Blo 940584 2121335 := bstep (se 1 (by rfl) ⟨1591001, by rfl⟩ : syracuseStep 2121335 = 3182003) B3182003
theorem B941703 : Blo 940584 941703 := bstep (se 1 (by rfl) ⟨706277, by rfl⟩ : syracuseStep 941703 = 1412555) B1412555
theorem B941711 : Blo 940584 941711 := bstep (se 1 (by rfl) ⟨706283, by rfl⟩ : syracuseStep 941711 = 1412567) B1412567
theorem B4775597 : Blo 940584 4775597 := bstep (se 3 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 4775597 = 1790849) B1790849
theorem B941755 : Blo 940584 941755 := bstep (se 1 (by rfl) ⟨706316, by rfl⟩ : syracuseStep 941755 = 1412633) B1412633
theorem B11460325 : Blo 940584 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B941831 : Blo 940584 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B2383627 : Blo 940584 2383627 := bstep (se 1 (by rfl) ⟨1787720, by rfl⟩ : syracuseStep 2383627 = 3575441) B3575441
theorem B941839 : Blo 940584 941839 := bstep (se 1 (by rfl) ⟨706379, by rfl⟩ : syracuseStep 941839 = 1412759) B1412759
theorem B2121515 : Blo 940584 2121515 := bstep (se 1 (by rfl) ⟨1591136, by rfl⟩ : syracuseStep 2121515 = 3182273) B3182273
theorem B941883 : Blo 940584 941883 := bstep (se 1 (by rfl) ⟨706412, by rfl⟩ : syracuseStep 941883 = 1412825) B1412825
theorem B941959 : Blo 940584 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B941967 : Blo 940584 941967 := bstep (se 1 (by rfl) ⟨706475, by rfl⟩ : syracuseStep 941967 = 1412951) B1412951
theorem B2383769 : Blo 940584 2383769 := bstep (se 2 (by rfl) ⟨893913, by rfl⟩ : syracuseStep 2383769 = 1787827) B1787827
theorem B20406167 : Blo 940584 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B942011 : Blo 940584 942011 := bstep (se 1 (by rfl) ⟨706508, by rfl⟩ : syracuseStep 942011 = 1413017) B1413017
theorem B942087 : Blo 940584 942087 := bstep (se 1 (by rfl) ⟨706565, by rfl⟩ : syracuseStep 942087 = 1413131) B1413131
theorem B942095 : Blo 940584 942095 := bstep (se 1 (by rfl) ⟨706571, by rfl⟩ : syracuseStep 942095 = 1413143) B1413143
theorem B2383931 : Blo 940584 2383931 := bstep (se 1 (by rfl) ⟨1787948, by rfl⟩ : syracuseStep 2383931 = 3575897) B3575897
theorem B942139 : Blo 940584 942139 := bstep (se 1 (by rfl) ⟨706604, by rfl⟩ : syracuseStep 942139 = 1413209) B1413209
theorem B3629123 : Blo 940584 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B942215 : Blo 940584 942215 := bstep (se 1 (by rfl) ⟨706661, by rfl⟩ : syracuseStep 942215 = 1413323) B1413323
theorem B942223 : Blo 940584 942223 := bstep (se 1 (by rfl) ⟨706667, by rfl⟩ : syracuseStep 942223 = 1413335) B1413335
theorem B1007759 : Blo 940584 1007759 := bstep (se 1 (by rfl) ⟨755819, by rfl⟩ : syracuseStep 1007759 = 1511639) B1511639
theorem B2416787 : Blo 940584 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B2121875 : Blo 940584 2121875 := bstep (se 1 (by rfl) ⟨1591406, by rfl⟩ : syracuseStep 2121875 = 3182813) B3182813
theorem B942267 : Blo 940584 942267 := bstep (se 1 (by rfl) ⟨706700, by rfl⟩ : syracuseStep 942267 = 1413401) B1413401
theorem B2121929 : Blo 940584 2121929 := bstep (se 2 (by rfl) ⟨795723, by rfl⟩ : syracuseStep 2121929 = 1591447) B1591447
theorem B942343 : Blo 940584 942343 := bstep (se 1 (by rfl) ⟨706757, by rfl⟩ : syracuseStep 942343 = 1413515) B1413515
theorem B942351 : Blo 940584 942351 := bstep (se 1 (by rfl) ⟨706763, by rfl⟩ : syracuseStep 942351 = 1413527) B1413527
theorem B4022561 : Blo 940584 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B942395 : Blo 940584 942395 := bstep (se 1 (by rfl) ⟨706796, by rfl⟩ : syracuseStep 942395 = 1413593) B1413593
theorem B1073543 : Blo 940584 1073543 := bstep (se 1 (by rfl) ⟨805157, by rfl⟩ : syracuseStep 1073543 = 1610315) B1610315
theorem B942471 : Blo 940584 942471 := bstep (se 1 (by rfl) ⟨706853, by rfl⟩ : syracuseStep 942471 = 1413707) B1413707
theorem B942479 : Blo 940584 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B2384275 : Blo 940584 2384275 := bstep (se 1 (by rfl) ⟨1788206, by rfl⟩ : syracuseStep 2384275 = 3576413) B3576413
theorem B4022713 : Blo 940584 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B942523 : Blo 940584 942523 := bstep (se 1 (by rfl) ⟨706892, by rfl⟩ : syracuseStep 942523 = 1413785) B1413785
theorem B942599 : Blo 940584 942599 := bstep (se 1 (by rfl) ⟨706949, by rfl⟩ : syracuseStep 942599 = 1413899) B1413899
theorem B942607 : Blo 940584 942607 := bstep (se 1 (by rfl) ⟨706955, by rfl⟩ : syracuseStep 942607 = 1413911) B1413911
theorem B2384417 : Blo 940584 2384417 := bstep (se 2 (by rfl) ⟨894156, by rfl⟩ : syracuseStep 2384417 = 1788313) B1788313
theorem B942651 : Blo 940584 942651 := bstep (se 1 (by rfl) ⟨706988, by rfl⟩ : syracuseStep 942651 = 1413977) B1413977
theorem B1696391 : Blo 940584 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B942727 : Blo 940584 942727 := bstep (se 1 (by rfl) ⟨707045, by rfl⟩ : syracuseStep 942727 = 1414091) B1414091
theorem B942735 : Blo 940584 942735 := bstep (se 1 (by rfl) ⟨707051, by rfl⟩ : syracuseStep 942735 = 1414103) B1414103
theorem B942779 : Blo 940584 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B3400393 : Blo 940584 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B942855 : Blo 940584 942855 := bstep (se 1 (by rfl) ⟨707141, by rfl⟩ : syracuseStep 942855 = 1414283) B1414283
theorem B942863 : Blo 940584 942863 := bstep (se 1 (by rfl) ⟨707147, by rfl⟩ : syracuseStep 942863 = 1414295) B1414295
theorem B942907 : Blo 940584 942907 := bstep (se 1 (by rfl) ⟨707180, by rfl⟩ : syracuseStep 942907 = 1414361) B1414361
theorem B942983 : Blo 940584 942983 := bstep (se 1 (by rfl) ⟨707237, by rfl⟩ : syracuseStep 942983 = 1414475) B1414475
theorem B2122631 : Blo 940584 2122631 := bstep (se 1 (by rfl) ⟨1591973, by rfl⟩ : syracuseStep 2122631 = 3183947) B3183947
theorem B942991 : Blo 940584 942991 := bstep (se 1 (by rfl) ⟨707243, by rfl⟩ : syracuseStep 942991 = 1414487) B1414487
theorem B943035 : Blo 940584 943035 := bstep (se 1 (by rfl) ⟨707276, by rfl⟩ : syracuseStep 943035 = 1414553) B1414553
theorem B943111 : Blo 940584 943111 := bstep (se 1 (by rfl) ⟨707333, by rfl⟩ : syracuseStep 943111 = 1414667) B1414667
theorem B943119 : Blo 940584 943119 := bstep (se 1 (by rfl) ⟨707339, by rfl⟩ : syracuseStep 943119 = 1414679) B1414679
theorem B5366807 : Blo 940584 5366807 := bstep (se 1 (by rfl) ⟨4025105, by rfl⟩ : syracuseStep 5366807 = 8050211) B8050211
theorem B943163 : Blo 940584 943163 := bstep (se 1 (by rfl) ⟨707372, by rfl⟩ : syracuseStep 943163 = 1414745) B1414745
theorem B2122811 : Blo 940584 2122811 := bstep (se 1 (by rfl) ⟨1592108, by rfl⟩ : syracuseStep 2122811 = 3184217) B3184217
theorem B4088893 : Blo 940584 4088893 := bstep (se 3 (by rfl) ⟨766667, by rfl⟩ : syracuseStep 4088893 = 1533335) B1533335
theorem B2679895 : Blo 940584 2679895 := bstep (se 1 (by rfl) ⟨2009921, by rfl⟩ : syracuseStep 2679895 = 4019843) B4019843
theorem B943239 : Blo 940584 943239 := bstep (se 1 (by rfl) ⟨707429, by rfl⟩ : syracuseStep 943239 = 1414859) B1414859
theorem B943247 : Blo 940584 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B2122937 : Blo 940584 2122937 := bstep (se 2 (by rfl) ⟨796101, by rfl⟩ : syracuseStep 2122937 = 1592203) B1592203
theorem B943291 : Blo 940584 943291 := bstep (se 1 (by rfl) ⟨707468, by rfl⟩ : syracuseStep 943291 = 1414937) B1414937
theorem B4023533 : Blo 940584 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B4777217 : Blo 940584 4777217 := bstep (se 2 (by rfl) ⟨1791456, by rfl⟩ : syracuseStep 4777217 = 3582913) B3582913
theorem B943367 : Blo 940584 943367 := bstep (se 1 (by rfl) ⟨707525, by rfl⟩ : syracuseStep 943367 = 1415051) B1415051
theorem B943375 : Blo 940584 943375 := bstep (se 1 (by rfl) ⟨707531, by rfl⟩ : syracuseStep 943375 = 1415063) B1415063
theorem B2680123 : Blo 940584 2680123 := bstep (se 1 (by rfl) ⟨2010092, by rfl⟩ : syracuseStep 2680123 = 4020185) B4020185
theorem B943419 : Blo 940584 943419 := bstep (se 1 (by rfl) ⟨707564, by rfl⟩ : syracuseStep 943419 = 1415129) B1415129
theorem B10741085 : Blo 940584 10741085 := bstep (se 3 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 10741085 = 4027907) B4027907
theorem B943495 : Blo 940584 943495 := bstep (se 1 (by rfl) ⟨707621, by rfl⟩ : syracuseStep 943495 = 1415243) B1415243
theorem B943503 : Blo 940584 943503 := bstep (se 1 (by rfl) ⟨707627, by rfl⟩ : syracuseStep 943503 = 1415255) B1415255
theorem B2680249 : Blo 940584 2680249 := bstep (se 2 (by rfl) ⟨1005093, by rfl⟩ : syracuseStep 2680249 = 2010187) B2010187
theorem B943547 : Blo 940584 943547 := bstep (se 1 (by rfl) ⟨707660, by rfl⟩ : syracuseStep 943547 = 1415321) B1415321
theorem B2385409 : Blo 940584 2385409 := bstep (se 2 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 2385409 = 1789057) B1789057
theorem B943623 : Blo 940584 943623 := bstep (se 1 (by rfl) ⟨707717, by rfl⟩ : syracuseStep 943623 = 1415435) B1415435
theorem B943631 : Blo 940584 943631 := bstep (se 1 (by rfl) ⟨707723, by rfl⟩ : syracuseStep 943631 = 1415447) B1415447
theorem B2123279 : Blo 940584 2123279 := bstep (se 1 (by rfl) ⟨1592459, by rfl⟩ : syracuseStep 2123279 = 3184919) B3184919
theorem B2123297 : Blo 940584 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B2450987 : Blo 940584 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B943675 : Blo 940584 943675 := bstep (se 1 (by rfl) ⟨707756, by rfl⟩ : syracuseStep 943675 = 1415513) B1415513
theorem B21784139 : Blo 940584 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B943751 : Blo 940584 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B943759 : Blo 940584 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B943803 : Blo 940584 943803 := bstep (se 1 (by rfl) ⟨707852, by rfl⟩ : syracuseStep 943803 = 1415705) B1415705
theorem B943879 : Blo 940584 943879 := bstep (se 1 (by rfl) ⟨707909, by rfl⟩ : syracuseStep 943879 = 1415819) B1415819
theorem B943887 : Blo 940584 943887 := bstep (se 1 (by rfl) ⟨707915, by rfl⟩ : syracuseStep 943887 = 1415831) B1415831
theorem B943931 : Blo 940584 943931 := bstep (se 1 (by rfl) ⟨707948, by rfl⟩ : syracuseStep 943931 = 1415897) B1415897
theorem B2123639 : Blo 940584 2123639 := bstep (se 1 (by rfl) ⟨1592729, by rfl⟩ : syracuseStep 2123639 = 3185459) B3185459
theorem B944007 : Blo 940584 944007 := bstep (se 1 (by rfl) ⟨708005, by rfl⟩ : syracuseStep 944007 = 1416011) B1416011
theorem B944015 : Blo 940584 944015 := bstep (se 1 (by rfl) ⟨708011, by rfl⟩ : syracuseStep 944015 = 1416023) B1416023
theorem B4024217 : Blo 940584 4024217 := bstep (se 2 (by rfl) ⟨1509081, by rfl⟩ : syracuseStep 4024217 = 3018163) B3018163
theorem B944059 : Blo 940584 944059 := bstep (se 1 (by rfl) ⟨708044, by rfl⟩ : syracuseStep 944059 = 1416089) B1416089
theorem B944135 : Blo 940584 944135 := bstep (se 1 (by rfl) ⟨708101, by rfl⟩ : syracuseStep 944135 = 1416203) B1416203
theorem B1435655 : Blo 940584 1435655 := bstep (se 1 (by rfl) ⟨1076741, by rfl⟩ : syracuseStep 1435655 = 2153483) B2153483
theorem B944143 : Blo 940584 944143 := bstep (se 1 (by rfl) ⟨708107, by rfl⟩ : syracuseStep 944143 = 1416215) B1416215
theorem B4778027 : Blo 940584 4778027 := bstep (se 1 (by rfl) ⟨3583520, by rfl⟩ : syracuseStep 4778027 = 7167041) B7167041
theorem B2123819 : Blo 940584 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B944187 : Blo 940584 944187 := bstep (se 1 (by rfl) ⟨708140, by rfl⟩ : syracuseStep 944187 = 1416281) B1416281
theorem B2386007 : Blo 940584 2386007 := bstep (se 1 (by rfl) ⟨1789505, by rfl⟩ : syracuseStep 2386007 = 3579011) B3579011
theorem B944263 : Blo 940584 944263 := bstep (se 1 (by rfl) ⟨708197, by rfl⟩ : syracuseStep 944263 = 1416395) B1416395
theorem B944271 : Blo 940584 944271 := bstep (se 1 (by rfl) ⟨708203, by rfl⟩ : syracuseStep 944271 = 1416407) B1416407
theorem B944315 : Blo 940584 944315 := bstep (se 1 (by rfl) ⟨708236, by rfl⟩ : syracuseStep 944315 = 1416473) B1416473
theorem B944391 : Blo 940584 944391 := bstep (se 1 (by rfl) ⟨708293, by rfl⟩ : syracuseStep 944391 = 1416587) B1416587
theorem B944399 : Blo 940584 944399 := bstep (se 1 (by rfl) ⟨708299, by rfl⟩ : syracuseStep 944399 = 1416599) B1416599
theorem B2386219 : Blo 940584 2386219 := bstep (se 1 (by rfl) ⟨1789664, by rfl⟩ : syracuseStep 2386219 = 3579329) B3579329
theorem B944443 : Blo 940584 944443 := bstep (se 1 (by rfl) ⟨708332, by rfl⟩ : syracuseStep 944443 = 1416665) B1416665
theorem B944519 : Blo 940584 944519 := bstep (se 1 (by rfl) ⟨708389, by rfl⟩ : syracuseStep 944519 = 1416779) B1416779
theorem B944527 : Blo 940584 944527 := bstep (se 1 (by rfl) ⟨708395, by rfl⟩ : syracuseStep 944527 = 1416791) B1416791
theorem B2124179 : Blo 940584 2124179 := bstep (se 1 (by rfl) ⟨1593134, by rfl⟩ : syracuseStep 2124179 = 3186269) B3186269
theorem B2386361 : Blo 940584 2386361 := bstep (se 2 (by rfl) ⟨894885, by rfl⟩ : syracuseStep 2386361 = 1789771) B1789771
theorem B944571 : Blo 940584 944571 := bstep (se 1 (by rfl) ⟨708428, by rfl⟩ : syracuseStep 944571 = 1416857) B1416857
theorem B2124233 : Blo 940584 2124233 := bstep (se 2 (by rfl) ⟨796587, by rfl⟩ : syracuseStep 2124233 = 1593175) B1593175
theorem B10742543 : Blo 940584 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B6876019 : Blo 940584 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B2124935 : Blo 940584 2124935 := bstep (se 1 (by rfl) ⟨1593701, by rfl⟩ : syracuseStep 2124935 = 3187403) B3187403
theorem B2551073 : Blo 940584 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B4779323 : Blo 940584 4779323 := bstep (se 1 (by rfl) ⟨3584492, by rfl⟩ : syracuseStep 4779323 = 7168985) B7168985
theorem B2125115 : Blo 940584 2125115 := bstep (se 1 (by rfl) ⟨1593836, by rfl⟩ : syracuseStep 2125115 = 3187673) B3187673
theorem B2682173 : Blo 940584 2682173 := bstep (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) B1005815
theorem B2387353 : Blo 940584 2387353 := bstep (se 2 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 2387353 = 1790515) B1790515
theorem B6450617 : Blo 940584 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B2125241 : Blo 940584 2125241 := bstep (se 2 (by rfl) ⟨796965, by rfl⟩ : syracuseStep 2125241 = 1593931) B1593931
theorem B4779485 : Blo 940584 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B2387515 : Blo 940584 2387515 := bstep (se 1 (by rfl) ⟨1790636, by rfl⟩ : syracuseStep 2387515 = 3581273) B3581273
theorem B2387657 : Blo 940584 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B4779809 : Blo 940584 4779809 := bstep (se 2 (by rfl) ⟨1792428, by rfl⟩ : syracuseStep 4779809 = 3584857) B3584857
theorem B2388001 : Blo 940584 2388001 := bstep (se 2 (by rfl) ⟨895500, by rfl⟩ : syracuseStep 2388001 = 1791001) B1791001
theorem B1273915 : Blo 940584 1273915 := bstep (se 1 (by rfl) ⟨955436, by rfl⟩ : syracuseStep 1273915 = 1910873) B1910873
theorem B2715709 : Blo 940584 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B27226205 : Blo 940584 27226205 := bstep (se 3 (by rfl) ⟨5104913, by rfl⟩ : syracuseStep 27226205 = 10209827) B10209827
theorem B12087413 : Blo 940584 12087413 := bstep (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) B1133195
theorem B5369975 : Blo 940584 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B2683165 : Blo 940584 2683165 := bstep (se 3 (by rfl) ⟨503093, by rfl⟩ : syracuseStep 2683165 = 1006187) B1006187
theorem B2388599 : Blo 940584 2388599 := bstep (se 1 (by rfl) ⟨1791449, by rfl⟩ : syracuseStep 2388599 = 3582899) B3582899
theorem B4780781 : Blo 940584 4780781 := bstep (se 3 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 4780781 = 1792793) B1792793
theorem B8581925 : Blo 940584 8581925 := bstep (se 4 (by rfl) ⟨804555, by rfl⟩ : syracuseStep 8581925 = 1609111) B1609111
theorem B1340489 : Blo 940584 1340489 := bstep (se 2 (by rfl) ⟨502683, by rfl⟩ : syracuseStep 1340489 = 1005367) B1005367
theorem B1242383 : Blo 940584 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B10876193 : Blo 940584 10876193 := bstep (se 2 (by rfl) ⟨4078572, by rfl⟩ : syracuseStep 10876193 = 8157145) B8157145
theorem B3175739 : Blo 940584 3175739 := bstep (se 1 (by rfl) ⟨2381804, by rfl⟩ : syracuseStep 3175739 = 4763609) B4763609
theorem B24835513 : Blo 940584 24835513 := bstep (se 2 (by rfl) ⟨9313317, by rfl⟩ : syracuseStep 24835513 = 18626635) B18626635
theorem B5731793 : Blo 940584 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B4781591 : Blo 940584 4781591 := bstep (se 1 (by rfl) ⟨3586193, by rfl⟩ : syracuseStep 4781591 = 7172387) B7172387
theorem B8582723 : Blo 940584 8582723 := bstep (se 1 (by rfl) ⟨6437042, by rfl⟩ : syracuseStep 8582723 = 12874085) B12874085
theorem B3176225 : Blo 940584 3176225 := bstep (se 2 (by rfl) ⟨1191084, by rfl⟩ : syracuseStep 3176225 = 2382169) B2382169
theorem B2389895 : Blo 940584 2389895 := bstep (se 1 (by rfl) ⟨1792421, by rfl⟩ : syracuseStep 2389895 = 3584843) B3584843
theorem B1341355 : Blo 940584 1341355 := bstep (se 1 (by rfl) ⟨1006016, by rfl⟩ : syracuseStep 1341355 = 2012033) B2012033
theorem B2389945 : Blo 940584 2389945 := bstep (se 2 (by rfl) ⟨896229, by rfl⟩ : syracuseStep 2389945 = 1792459) B1792459
theorem B2685113 : Blo 940584 2685113 := bstep (se 2 (by rfl) ⟨1006917, by rfl⟩ : syracuseStep 2685113 = 2013835) B2013835
theorem B3176819 : Blo 940584 3176819 := bstep (se 1 (by rfl) ⟨2382614, by rfl⟩ : syracuseStep 3176819 = 4765229) B4765229
theorem B1472953 : Blo 940584 1472953 := bstep (se 2 (by rfl) ⟨552357, by rfl⟩ : syracuseStep 1472953 = 1104715) B1104715
theorem B43514329 : Blo 940584 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B2390543 : Blo 940584 2390543 := bstep (se 1 (by rfl) ⟨1792907, by rfl⟩ : syracuseStep 2390543 = 3585815) B3585815
theorem B11467331 : Blo 940584 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B2686355 : Blo 940584 2686355 := bstep (se 1 (by rfl) ⟨2014766, by rfl⟩ : syracuseStep 2686355 = 4029533) B4029533
theorem B1342921 : Blo 940584 1342921 := bstep (se 2 (by rfl) ⟨503595, by rfl⟩ : syracuseStep 1342921 = 1007191) B1007191
theorem B1933001 : Blo 940584 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B5373641 : Blo 940584 5373641 := bstep (se 2 (by rfl) ⟨2015115, by rfl⟩ : syracuseStep 5373641 = 4030231) B4030231
theorem B10714841 : Blo 940584 10714841 := bstep (se 2 (by rfl) ⟨4018065, by rfl⟩ : syracuseStep 10714841 = 8036131) B8036131
theorem B1343479 : Blo 940584 1343479 := bstep (se 1 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 1343479 = 2015219) B2015219
theorem B29065229 : Blo 940584 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B1507385 : Blo 940584 1507385 := bstep (se 2 (by rfl) ⟨565269, by rfl⟩ : syracuseStep 1507385 = 1130539) B1130539
theorem B7635059 : Blo 940584 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B3178763 : Blo 940584 3178763 := bstep (se 1 (by rfl) ⟨2384072, by rfl⟩ : syracuseStep 3178763 = 4768145) B4768145
theorem B2687357 : Blo 940584 2687357 := bstep (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) B1007759
theorem B3179033 : Blo 940584 3179033 := bstep (se 2 (by rfl) ⟨1192137, by rfl⟩ : syracuseStep 3179033 = 2384275) B2384275
theorem B2687687 : Blo 940584 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B30999257 : Blo 940584 30999257 := bstep (se 2 (by rfl) ⟨11624721, by rfl⟩ : syracuseStep 30999257 = 23249443) B23249443
theorem B6030227 : Blo 940584 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B6030379 : Blo 940584 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B1344863 : Blo 940584 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B36177353 : Blo 940584 36177353 := bstep (se 2 (by rfl) ⟨13566507, by rfl⟩ : syracuseStep 36177353 = 27133015) B27133015
theorem B3573193 : Blo 940584 3573193 := bstep (se 2 (by rfl) ⟨1339947, by rfl⟩ : syracuseStep 3573193 = 2679895) B2679895
theorem B3180167 : Blo 940584 3180167 := bstep (se 1 (by rfl) ⟨2385125, by rfl⟩ : syracuseStep 3180167 = 4770251) B4770251
theorem B3180221 : Blo 940584 3180221 := bstep (se 3 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 3180221 = 1192583) B1192583
theorem B3573497 : Blo 940584 3573497 := bstep (se 2 (by rfl) ⟨1340061, by rfl⟩ : syracuseStep 3573497 = 2680123) B2680123
theorem B1410911 : Blo 940584 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B6031199 : Blo 940584 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B3180383 : Blo 940584 3180383 := bstep (se 1 (by rfl) ⟨2385287, by rfl⟩ : syracuseStep 3180383 = 4770575) B4770575
theorem B1410923 : Blo 940584 1410923 := bstep (se 1 (by rfl) ⟨1058192, by rfl⟩ : syracuseStep 1410923 = 2116385) B2116385
theorem B3573665 : Blo 940584 3573665 := bstep (se 2 (by rfl) ⟨1340124, by rfl⟩ : syracuseStep 3573665 = 2680249) B2680249
theorem B3573679 : Blo 940584 3573679 := bstep (se 1 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 3573679 = 5360519) B5360519
theorem B3180545 : Blo 940584 3180545 := bstep (se 2 (by rfl) ⟨1192704, by rfl⟩ : syracuseStep 3180545 = 2385409) B2385409
theorem B2689031 : Blo 940584 2689031 := bstep (se 1 (by rfl) ⟨2016773, by rfl⟩ : syracuseStep 2689031 = 4033547) B4033547
theorem B1411151 : Blo 940584 1411151 := bstep (se 1 (by rfl) ⟨1058363, by rfl⟩ : syracuseStep 1411151 = 2116727) B2116727
theorem B1411271 : Blo 940584 1411271 := bstep (se 1 (by rfl) ⟨1058453, by rfl⟩ : syracuseStep 1411271 = 2116907) B2116907
theorem B2689271 : Blo 940584 2689271 := bstep (se 1 (by rfl) ⟨2016953, by rfl⟩ : syracuseStep 2689271 = 4033907) B4033907
theorem B1411433 : Blo 940584 1411433 := bstep (se 2 (by rfl) ⟨529287, by rfl⟩ : syracuseStep 1411433 = 1058575) B1058575
theorem B1411511 : Blo 940584 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B1411547 : Blo 940584 1411547 := bstep (se 1 (by rfl) ⟨1058660, by rfl⟩ : syracuseStep 1411547 = 2117321) B2117321
theorem B3181355 : Blo 940584 3181355 := bstep (se 1 (by rfl) ⟨2386016, by rfl⟩ : syracuseStep 3181355 = 4772033) B4772033
theorem B3574637 : Blo 940584 3574637 := bstep (se 3 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 3574637 = 1340489) B1340489
theorem B1412015 : Blo 940584 1412015 := bstep (se 1 (by rfl) ⟨1059011, by rfl⟩ : syracuseStep 1412015 = 2118023) B2118023
theorem B1510363 : Blo 940584 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B1412105 : Blo 940584 1412105 := bstep (se 2 (by rfl) ⟨529539, by rfl⟩ : syracuseStep 1412105 = 1059079) B1059079
theorem B1510409 : Blo 940584 1510409 := bstep (se 2 (by rfl) ⟨566403, by rfl⟩ : syracuseStep 1510409 = 1132807) B1132807
theorem B1412135 : Blo 940584 1412135 := bstep (se 1 (by rfl) ⟨1059101, by rfl⟩ : syracuseStep 1412135 = 2118203) B2118203
theorem B3181625 : Blo 940584 3181625 := bstep (se 2 (by rfl) ⟨1193109, by rfl⟩ : syracuseStep 3181625 = 2386219) B2386219
theorem B1412219 : Blo 940584 1412219 := bstep (se 1 (by rfl) ⟨1059164, by rfl⟩ : syracuseStep 1412219 = 2118329) B2118329
theorem B3574955 : Blo 940584 3574955 := bstep (se 1 (by rfl) ⟨2681216, by rfl⟩ : syracuseStep 3574955 = 5362433) B5362433
theorem B1412345 : Blo 940584 1412345 := bstep (se 2 (by rfl) ⟨529629, by rfl⟩ : syracuseStep 1412345 = 1059259) B1059259
theorem B1412447 : Blo 940584 1412447 := bstep (se 1 (by rfl) ⟨1059335, by rfl⟩ : syracuseStep 1412447 = 2118671) B2118671
theorem B1412459 : Blo 940584 1412459 := bstep (se 1 (by rfl) ⟨1059344, by rfl⟩ : syracuseStep 1412459 = 2118689) B2118689
theorem B3313021 : Blo 940584 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B3181949 : Blo 940584 3181949 := bstep (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) B1193231
theorem B12062195 : Blo 940584 12062195 := bstep (se 1 (by rfl) ⟨9046646, by rfl⟩ : syracuseStep 12062195 = 18093293) B18093293
theorem B1510921 : Blo 940584 1510921 := bstep (se 2 (by rfl) ⟨566595, by rfl⟩ : syracuseStep 1510921 = 1133191) B1133191
theorem B1412687 : Blo 940584 1412687 := bstep (se 1 (by rfl) ⟨1059515, by rfl⟩ : syracuseStep 1412687 = 2119031) B2119031
theorem B2264699 : Blo 940584 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B3182219 : Blo 940584 3182219 := bstep (se 1 (by rfl) ⟨2386664, by rfl⟩ : syracuseStep 3182219 = 4773329) B4773329
theorem B4034195 : Blo 940584 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B1412807 : Blo 940584 1412807 := bstep (se 1 (by rfl) ⟨1059605, by rfl⟩ : syracuseStep 1412807 = 2119211) B2119211
theorem B6524705 : Blo 940584 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B1412969 : Blo 940584 1412969 := bstep (se 2 (by rfl) ⟨529863, by rfl⟩ : syracuseStep 1412969 = 1059727) B1059727
theorem B1413047 : Blo 940584 1413047 := bstep (se 1 (by rfl) ⟨1059785, by rfl⟩ : syracuseStep 1413047 = 2119571) B2119571
theorem B1413083 : Blo 940584 1413083 := bstep (se 1 (by rfl) ⟨1059812, by rfl⟩ : syracuseStep 1413083 = 2119625) B2119625
theorem B7147601 : Blo 940584 7147601 := bstep (se 2 (by rfl) ⟨2680350, by rfl⟩ : syracuseStep 7147601 = 5360701) B5360701
theorem B19337395 : Blo 940584 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B1413551 : Blo 940584 1413551 := bstep (se 1 (by rfl) ⟨1060163, by rfl⟩ : syracuseStep 1413551 = 2120327) B2120327
theorem B1413641 : Blo 940584 1413641 := bstep (se 2 (by rfl) ⟨530115, by rfl⟩ : syracuseStep 1413641 = 1060231) B1060231
theorem B3183137 : Blo 940584 3183137 := bstep (se 2 (by rfl) ⟨1193676, by rfl⟩ : syracuseStep 3183137 = 2387353) B2387353
theorem B6132257 : Blo 940584 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B1413671 : Blo 940584 1413671 := bstep (se 1 (by rfl) ⟨1060253, by rfl⟩ : syracuseStep 1413671 = 2120507) B2120507
theorem B1413755 : Blo 940584 1413755 := bstep (se 1 (by rfl) ⟨1060316, by rfl⟩ : syracuseStep 1413755 = 2120633) B2120633
theorem B1413881 : Blo 940584 1413881 := bstep (se 2 (by rfl) ⟨530205, by rfl⟩ : syracuseStep 1413881 = 1060411) B1060411
theorem B3183353 : Blo 940584 3183353 := bstep (se 2 (by rfl) ⟨1193757, by rfl⟩ : syracuseStep 3183353 = 2387515) B2387515
theorem B1413983 : Blo 940584 1413983 := bstep (se 1 (by rfl) ⟨1060487, by rfl⟩ : syracuseStep 1413983 = 2120975) B2120975
theorem B1413995 : Blo 940584 1413995 := bstep (se 1 (by rfl) ⟨1060496, by rfl⟩ : syracuseStep 1413995 = 2120993) B2120993
theorem B3183623 : Blo 940584 3183623 := bstep (se 1 (by rfl) ⟨2387717, by rfl⟩ : syracuseStep 3183623 = 4775435) B4775435
theorem B3019855 : Blo 940584 3019855 := bstep (se 1 (by rfl) ⟨2264891, by rfl⟩ : syracuseStep 3019855 = 4529783) B4529783
theorem B1414223 : Blo 940584 1414223 := bstep (se 1 (by rfl) ⟨1060667, by rfl⟩ : syracuseStep 1414223 = 2121335) B2121335
theorem B3183731 : Blo 940584 3183731 := bstep (se 1 (by rfl) ⟨2387798, by rfl⟩ : syracuseStep 3183731 = 4775597) B4775597
theorem B9049259 : Blo 940584 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B1414343 : Blo 940584 1414343 := bstep (se 1 (by rfl) ⟨1060757, by rfl⟩ : syracuseStep 1414343 = 2121515) B2121515
theorem B13604111 : Blo 940584 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B1414505 : Blo 940584 1414505 := bstep (se 2 (by rfl) ⟨530439, by rfl⟩ : syracuseStep 1414505 = 1060879) B1060879
theorem B3184001 : Blo 940584 3184001 := bstep (se 2 (by rfl) ⟨1194000, by rfl⟩ : syracuseStep 3184001 = 2388001) B2388001
theorem B1611191 : Blo 940584 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B1414583 : Blo 940584 1414583 := bstep (se 1 (by rfl) ⟨1060937, by rfl⟩ : syracuseStep 1414583 = 2121875) B2121875
theorem B1414619 : Blo 940584 1414619 := bstep (se 1 (by rfl) ⟨1060964, by rfl⟩ : syracuseStep 1414619 = 2121929) B2121929
theorem B3577553 : Blo 940584 3577553 := bstep (se 2 (by rfl) ⟨1341582, by rfl⟩ : syracuseStep 3577553 = 2683165) B2683165
theorem B1415087 : Blo 940584 1415087 := bstep (se 1 (by rfl) ⟨1061315, by rfl⟩ : syracuseStep 1415087 = 2122631) B2122631
theorem B1415177 : Blo 940584 1415177 := bstep (se 2 (by rfl) ⟨530691, by rfl⟩ : syracuseStep 1415177 = 1061383) B1061383
theorem B3577871 : Blo 940584 3577871 := bstep (se 1 (by rfl) ⟨2683403, by rfl⟩ : syracuseStep 3577871 = 5366807) B5366807
theorem B1415207 : Blo 940584 1415207 := bstep (se 1 (by rfl) ⟨1061405, by rfl⟩ : syracuseStep 1415207 = 2122811) B2122811
theorem B1415291 : Blo 940584 1415291 := bstep (se 1 (by rfl) ⟨1061468, by rfl⟩ : syracuseStep 1415291 = 2122937) B2122937
theorem B3184811 : Blo 940584 3184811 := bstep (se 1 (by rfl) ⟨2388608, by rfl⟩ : syracuseStep 3184811 = 4777217) B4777217
theorem B1415417 : Blo 940584 1415417 := bstep (se 2 (by rfl) ⟨530781, by rfl⟩ : syracuseStep 1415417 = 1061563) B1061563
theorem B1415519 : Blo 940584 1415519 := bstep (se 1 (by rfl) ⟨1061639, by rfl⟩ : syracuseStep 1415519 = 2123279) B2123279
theorem B1415531 : Blo 940584 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B14522759 : Blo 940584 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B1415759 : Blo 940584 1415759 := bstep (se 1 (by rfl) ⟨1061819, by rfl⟩ : syracuseStep 1415759 = 2123639) B2123639
theorem B7641773 : Blo 940584 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B957103 : Blo 940584 957103 := bstep (se 1 (by rfl) ⟨717827, by rfl⟩ : syracuseStep 957103 = 1435655) B1435655
theorem B3185351 : Blo 940584 3185351 := bstep (se 1 (by rfl) ⟨2389013, by rfl⟩ : syracuseStep 3185351 = 4778027) B4778027
theorem B1415879 : Blo 940584 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B1416041 : Blo 940584 1416041 := bstep (se 2 (by rfl) ⟨531015, by rfl⟩ : syracuseStep 1416041 = 1062031) B1062031
theorem B3218359 : Blo 940584 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B1416119 : Blo 940584 1416119 := bstep (se 1 (by rfl) ⟨1062089, by rfl⟩ : syracuseStep 1416119 = 2124179) B2124179
theorem B1416155 : Blo 940584 1416155 := bstep (se 1 (by rfl) ⟨1062116, by rfl⟩ : syracuseStep 1416155 = 2124233) B2124233
theorem B1940809 : Blo 940584 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B1416623 : Blo 940584 1416623 := bstep (se 1 (by rfl) ⟨1062467, by rfl⟩ : syracuseStep 1416623 = 2124935) B2124935
theorem B1416713 : Blo 940584 1416713 := bstep (se 2 (by rfl) ⟨531267, by rfl⟩ : syracuseStep 1416713 = 1062535) B1062535
theorem B3186215 : Blo 940584 3186215 := bstep (se 1 (by rfl) ⟨2389661, by rfl⟩ : syracuseStep 3186215 = 4779323) B4779323
theorem B1416743 : Blo 940584 1416743 := bstep (se 1 (by rfl) ⟨1062557, by rfl⟩ : syracuseStep 1416743 = 2125115) B2125115
theorem B1416827 : Blo 940584 1416827 := bstep (se 1 (by rfl) ⟨1062620, by rfl⟩ : syracuseStep 1416827 = 2125241) B2125241
theorem B3186323 : Blo 940584 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B627351317 : Blo 940584 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B3186539 : Blo 940584 3186539 := bstep (se 1 (by rfl) ⟨2389904, by rfl⟩ : syracuseStep 3186539 = 4779809) B4779809
theorem B3186593 : Blo 940584 3186593 := bstep (se 2 (by rfl) ⟨1194972, by rfl⟩ : syracuseStep 3186593 = 2389945) B2389945
theorem B3579983 : Blo 940584 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B1909153 : Blo 940584 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B3187187 : Blo 940584 3187187 := bstep (se 1 (by rfl) ⟨2390390, by rfl⟩ : syracuseStep 3187187 = 4780781) B4780781
theorem B6038225 : Blo 940584 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B7152461 : Blo 940584 7152461 := bstep (se 3 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 7152461 = 2682173) B2682173
theorem B7250795 : Blo 940584 7250795 := bstep (se 1 (by rfl) ⟨5438096, by rfl⟩ : syracuseStep 7250795 = 10876193) B10876193
theorem B3187727 : Blo 940584 3187727 := bstep (se 1 (by rfl) ⟨2390795, by rfl⟩ : syracuseStep 3187727 = 4781591) B4781591
theorem B1910191 : Blo 940584 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B4531859 : Blo 940584 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B1058503 : Blo 940584 1058503 := bstep (se 1 (by rfl) ⟨793877, by rfl⟩ : syracuseStep 1058503 = 1587755) B1587755
theorem B7644887 : Blo 940584 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B1812385 : Blo 940584 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B1910711 : Blo 940584 1910711 := bstep (se 1 (by rfl) ⟨1433033, by rfl⟩ : syracuseStep 1910711 = 2866067) B2866067
theorem B3024827 : Blo 940584 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B15280433 : Blo 940584 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B12069323 : Blo 940584 12069323 := bstep (se 1 (by rfl) ⟨9051992, by rfl⟩ : syracuseStep 12069323 = 18103985) B18103985
theorem B1288667 : Blo 940584 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B3582427 : Blo 940584 3582427 := bstep (se 1 (by rfl) ⟨2686820, by rfl⟩ : syracuseStep 3582427 = 5373641) B5373641
theorem B3025441 : Blo 940584 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B1059367 : Blo 940584 1059367 := bstep (se 1 (by rfl) ⟨794525, by rfl⟩ : syracuseStep 1059367 = 1589051) B1589051
theorem B2042491 : Blo 940584 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B4762475 : Blo 940584 4762475 := bstep (se 1 (by rfl) ⟨3571856, by rfl⟩ : syracuseStep 4762475 = 7143713) B7143713
theorem B7154891 : Blo 940584 7154891 := bstep (se 1 (by rfl) ⟨5366168, by rfl⟩ : syracuseStep 7154891 = 10732337) B10732337
theorem B20655395 : Blo 940584 20655395 := bstep (se 1 (by rfl) ⟨15491546, by rfl⟩ : syracuseStep 20655395 = 30983093) B30983093
theorem B1191343 : Blo 940584 1191343 := bstep (se 1 (by rfl) ⟨893507, by rfl⟩ : syracuseStep 1191343 = 1787015) B1787015
theorem B4763123 : Blo 940584 4763123 := bstep (se 1 (by rfl) ⟨3572342, by rfl⟩ : syracuseStep 4763123 = 7144685) B7144685
theorem B4533857 : Blo 940584 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B3583673 : Blo 940584 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B1912519 : Blo 940584 1912519 := bstep (se 1 (by rfl) ⟨1434389, by rfl⟩ : syracuseStep 1912519 = 2868779) B2868779
theorem B3583703 : Blo 940584 3583703 := bstep (se 1 (by rfl) ⟨2687777, by rfl⟩ : syracuseStep 3583703 = 5375555) B5375555
theorem B6205177 : Blo 940584 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B5451857 : Blo 940584 5451857 := bstep (se 2 (by rfl) ⟨2044446, by rfl⟩ : syracuseStep 5451857 = 4088893) B4088893
theorem B1060987 : Blo 940584 1060987 := bstep (se 1 (by rfl) ⟨795740, by rfl⟩ : syracuseStep 1060987 = 1591481) B1591481
theorem B1192411 : Blo 940584 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B2044379 : Blo 940584 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B1061455 : Blo 940584 1061455 := bstep (se 1 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 1061455 = 1592183) B1592183
theorem B3486347 : Blo 940584 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B4764419 : Blo 940584 4764419 := bstep (se 1 (by rfl) ⟨3573314, by rfl⟩ : syracuseStep 4764419 = 7146629) B7146629
theorem B1061851 : Blo 940584 1061851 := bstep (se 1 (by rfl) ⟨796388, by rfl⟩ : syracuseStep 1061851 = 1592777) B1592777
theorem B1062319 : Blo 940584 1062319 := bstep (se 1 (by rfl) ⟨796739, by rfl⟩ : syracuseStep 1062319 = 1593479) B1593479
theorem B1914491 : Blo 940584 1914491 := bstep (se 1 (by rfl) ⟨1435868, by rfl⟩ : syracuseStep 1914491 = 2871737) B2871737
theorem B2012921 : Blo 940584 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B6043501 : Blo 940584 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B5093239 : Blo 940584 5093239 := bstep (se 1 (by rfl) ⟨3819929, by rfl⟩ : syracuseStep 5093239 = 7639859) B7639859
theorem B10729421 : Blo 940584 10729421 := bstep (se 3 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 10729421 = 4023533) B4023533
theorem B1587323 : Blo 940584 1587323 := bstep (se 1 (by rfl) ⟨1190492, by rfl⟩ : syracuseStep 1587323 = 2380985) B2380985
theorem B3586315 : Blo 940584 3586315 := bstep (se 1 (by rfl) ⟨2689736, by rfl⟩ : syracuseStep 3586315 = 5379473) B5379473
theorem B4766039 : Blo 940584 4766039 := bstep (se 1 (by rfl) ⟨3574529, by rfl⟩ : syracuseStep 4766039 = 7149059) B7149059
theorem B1587721 : Blo 940584 1587721 := bstep (se 2 (by rfl) ⟨595395, by rfl⟩ : syracuseStep 1587721 = 1190791) B1190791
theorem B1587883 : Blo 940584 1587883 := bstep (se 1 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 1587883 = 2381825) B2381825
theorem B11451125 : Blo 940584 11451125 := bstep (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) B1073543
theorem B1588187 : Blo 940584 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B1588423 : Blo 940584 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B4537547 : Blo 940584 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B14499107 : Blo 940584 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B1588585 : Blo 940584 1588585 := bstep (se 2 (by rfl) ⟨595719, by rfl⟩ : syracuseStep 1588585 = 1191439) B1191439
theorem B2145755 : Blo 940584 2145755 := bstep (se 1 (by rfl) ⟨1609316, by rfl⟩ : syracuseStep 2145755 = 3218633) B3218633
theorem B6438689 : Blo 940584 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B1589179 : Blo 940584 1589179 := bstep (se 1 (by rfl) ⟨1191884, by rfl⟩ : syracuseStep 1589179 = 2383769) B2383769
theorem B1589287 : Blo 940584 1589287 := bstep (se 1 (by rfl) ⟨1191965, by rfl⟩ : syracuseStep 1589287 = 2383931) B2383931
theorem B3620945 : Blo 940584 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B1589611 : Blo 940584 1589611 := bstep (se 1 (by rfl) ⟨1192208, by rfl⟩ : syracuseStep 1589611 = 2384417) B2384417
theorem B1130927 : Blo 940584 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B12894673 : Blo 940584 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B1360747 : Blo 940584 1360747 := bstep (se 1 (by rfl) ⟨1020560, by rfl⟩ : syracuseStep 1360747 = 2041121) B2041121
theorem B2016107 : Blo 940584 2016107 := bstep (se 1 (by rfl) ⟨1512080, by rfl⟩ : syracuseStep 2016107 = 3024161) B3024161
theorem B34456427 : Blo 940584 34456427 := bstep (se 1 (by rfl) ⟨25842320, by rfl⟩ : syracuseStep 34456427 = 51684641) B51684641
theorem B7160723 : Blo 940584 7160723 := bstep (se 1 (by rfl) ⟨5370542, by rfl⟩ : syracuseStep 7160723 = 10741085) B10741085
theorem B9684139 : Blo 940584 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B3065149 : Blo 940584 3065149 := bstep (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) B1149431
theorem B1590671 : Blo 940584 1590671 := bstep (se 1 (by rfl) ⟨1193003, by rfl⟩ : syracuseStep 1590671 = 2386007) B2386007
theorem B1590907 : Blo 940584 1590907 := bstep (se 1 (by rfl) ⟨1193180, by rfl⟩ : syracuseStep 1590907 = 2386361) B2386361
theorem B5359243 : Blo 940584 5359243 := bstep (se 1 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 5359243 = 8038865) B8038865
theorem B4769603 : Blo 940584 4769603 := bstep (se 1 (by rfl) ⟨3577202, by rfl⟩ : syracuseStep 4769603 = 7154405) B7154405
theorem B7161695 : Blo 940584 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B7751585 : Blo 940584 7751585 := bstep (se 2 (by rfl) ⟨2906844, by rfl⟩ : syracuseStep 7751585 = 5813689) B5813689
theorem B33114017 : Blo 940584 33114017 := bstep (se 2 (by rfl) ⟨12417756, by rfl⟩ : syracuseStep 33114017 = 24835513) B24835513
theorem B2902397 : Blo 940584 2902397 := bstep (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) B1088399
theorem B1591771 : Blo 940584 1591771 := bstep (se 1 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 1591771 = 2387657) B2387657
theorem B1788473 : Blo 940584 1788473 := bstep (se 2 (by rfl) ⟨670677, by rfl⟩ : syracuseStep 1788473 = 1341355) B1341355
theorem B1592399 : Blo 940584 1592399 := bstep (se 1 (by rfl) ⟨1194299, by rfl⟩ : syracuseStep 1592399 = 2388599) B2388599
theorem B5721283 : Blo 940584 5721283 := bstep (se 1 (by rfl) ⟨4290962, by rfl⟩ : syracuseStep 5721283 = 8581925) B8581925
theorem B58019105 : Blo 940584 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B6802861 : Blo 940584 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B2117159 : Blo 940584 2117159 := bstep (se 1 (by rfl) ⟨1587869, by rfl⟩ : syracuseStep 2117159 = 3175739) B3175739
theorem B3821195 : Blo 940584 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B5721815 : Blo 940584 5721815 := bstep (se 1 (by rfl) ⟨4291361, by rfl⟩ : syracuseStep 5721815 = 8582723) B8582723
theorem B16305953 : Blo 940584 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B2117483 : Blo 940584 2117483 := bstep (se 1 (by rfl) ⟨1588112, by rfl⟩ : syracuseStep 2117483 = 3176225) B3176225
theorem B2117537 : Blo 940584 2117537 := bstep (se 2 (by rfl) ⟨794076, by rfl⟩ : syracuseStep 2117537 = 1588153) B1588153
theorem B1593263 : Blo 940584 1593263 := bstep (se 1 (by rfl) ⟨1194947, by rfl⟩ : syracuseStep 1593263 = 2389895) B2389895
theorem B1790075 : Blo 940584 1790075 := bstep (se 1 (by rfl) ⟨1342556, by rfl⟩ : syracuseStep 1790075 = 2685113) B2685113
theorem B2117879 : Blo 940584 2117879 := bstep (se 1 (by rfl) ⟨1588409, by rfl⟩ : syracuseStep 2117879 = 3176819) B3176819
theorem B15257915 : Blo 940584 15257915 := bstep (se 1 (by rfl) ⟨11443436, by rfl⟩ : syracuseStep 15257915 = 22886873) B22886873
theorem B1593695 : Blo 940584 1593695 := bstep (se 1 (by rfl) ⟨1195271, by rfl⟩ : syracuseStep 1593695 = 2390543) B2390543
theorem B1790561 : Blo 940584 1790561 := bstep (se 2 (by rfl) ⟨671460, by rfl⟩ : syracuseStep 1790561 = 1342921) B1342921
theorem B7262855 : Blo 940584 7262855 := bstep (se 1 (by rfl) ⟨5447141, by rfl⟩ : syracuseStep 7262855 = 10894283) B10894283
theorem B2118473 : Blo 940584 2118473 := bstep (se 2 (by rfl) ⟨794427, by rfl⟩ : syracuseStep 2118473 = 1588855) B1588855
theorem B4772681 : Blo 940584 4772681 := bstep (se 2 (by rfl) ⟨1789755, by rfl⟩ : syracuseStep 4772681 = 3579511) B3579511
theorem B1790903 : Blo 940584 1790903 := bstep (se 1 (by rfl) ⟨1343177, by rfl⟩ : syracuseStep 1790903 = 2686355) B2686355
theorem B7263233 : Blo 940584 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B1791305 : Blo 940584 1791305 := bstep (se 2 (by rfl) ⟨671739, by rfl⟩ : syracuseStep 1791305 = 1343479) B1343479
theorem B5363117 : Blo 940584 5363117 := bstep (se 3 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 5363117 = 2011169) B2011169
theorem B2119265 : Blo 940584 2119265 := bstep (se 2 (by rfl) ⟨794724, by rfl⟩ : syracuseStep 2119265 = 1589449) B1589449
theorem B1529515 : Blo 940584 1529515 := bstep (se 1 (by rfl) ⟨1147136, by rfl⟩ : syracuseStep 1529515 = 2294273) B2294273
theorem B16307905 : Blo 940584 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B2381663 : Blo 940584 2381663 := bstep (se 1 (by rfl) ⟨1786247, by rfl⟩ : syracuseStep 2381663 = 3572495) B3572495
theorem B5363617 : Blo 940584 5363617 := bstep (se 2 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 5363617 = 4022713) B4022713
theorem B2119607 : Blo 940584 2119607 := bstep (se 1 (by rfl) ⟨1589705, by rfl⟩ : syracuseStep 2119607 = 3179411) B3179411
theorem B1792019 : Blo 940584 1792019 := bstep (se 1 (by rfl) ⟨1344014, by rfl⟩ : syracuseStep 1792019 = 2688029) B2688029
theorem B1792057 : Blo 940584 1792057 := bstep (se 2 (by rfl) ⟨672021, by rfl⟩ : syracuseStep 1792057 = 1344043) B1344043
theorem B7264333 : Blo 940584 7264333 := bstep (se 3 (by rfl) ⟨1362062, by rfl⟩ : syracuseStep 7264333 = 2724125) B2724125
theorem B4773977 : Blo 940584 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B1792361 : Blo 940584 1792361 := bstep (se 2 (by rfl) ⟨672135, by rfl⟩ : syracuseStep 1792361 = 1344271) B1344271
theorem B3824015 : Blo 940584 3824015 := bstep (se 1 (by rfl) ⟨2868011, by rfl⟩ : syracuseStep 3824015 = 5736023) B5736023
theorem B2120201 : Blo 940584 2120201 := bstep (se 2 (by rfl) ⟨795075, by rfl⟩ : syracuseStep 2120201 = 1590151) B1590151
theorem B940623 : Blo 940584 940623 := bstep (se 1 (by rfl) ⟨705467, by rfl⟩ : syracuseStep 940623 = 1410935) B1410935
theorem B940639 : Blo 940584 940639 := bstep (se 1 (by rfl) ⟨705479, by rfl⟩ : syracuseStep 940639 = 1410959) B1410959
theorem B940667 : Blo 940584 940667 := bstep (se 1 (by rfl) ⟨705500, by rfl⟩ : syracuseStep 940667 = 1411001) B1411001
theorem B940719 : Blo 940584 940719 := bstep (se 1 (by rfl) ⟨705539, by rfl⟩ : syracuseStep 940719 = 1411079) B1411079
theorem B940743 : Blo 940584 940743 := bstep (se 1 (by rfl) ⟨705557, by rfl⟩ : syracuseStep 940743 = 1411115) B1411115
theorem B940763 : Blo 940584 940763 := bstep (se 1 (by rfl) ⟨705572, by rfl⟩ : syracuseStep 940763 = 1411145) B1411145
theorem B940839 : Blo 940584 940839 := bstep (se 1 (by rfl) ⟨705629, by rfl⟩ : syracuseStep 940839 = 1411259) B1411259
theorem B940879 : Blo 940584 940879 := bstep (se 1 (by rfl) ⟨705659, by rfl⟩ : syracuseStep 940879 = 1411319) B1411319
theorem B940895 : Blo 940584 940895 := bstep (se 1 (by rfl) ⟨705671, by rfl⟩ : syracuseStep 940895 = 1411343) B1411343
theorem B2120543 : Blo 940584 2120543 := bstep (se 1 (by rfl) ⟨1590407, by rfl⟩ : syracuseStep 2120543 = 3180815) B3180815
theorem B940923 : Blo 940584 940923 := bstep (se 1 (by rfl) ⟨705692, by rfl⟩ : syracuseStep 940923 = 1411385) B1411385
theorem B940975 : Blo 940584 940975 := bstep (se 1 (by rfl) ⟨705731, by rfl⟩ : syracuseStep 940975 = 1411463) B1411463
theorem B2382767 : Blo 940584 2382767 := bstep (se 1 (by rfl) ⟨1787075, by rfl⟩ : syracuseStep 2382767 = 3574151) B3574151
theorem B940999 : Blo 940584 940999 := bstep (se 1 (by rfl) ⟨705749, by rfl⟩ : syracuseStep 940999 = 1411499) B1411499
theorem B941019 : Blo 940584 941019 := bstep (se 1 (by rfl) ⟨705764, by rfl⟩ : syracuseStep 941019 = 1411529) B1411529
theorem B2120723 : Blo 940584 2120723 := bstep (se 1 (by rfl) ⟨1590542, by rfl⟩ : syracuseStep 2120723 = 3181085) B3181085
theorem B941095 : Blo 940584 941095 := bstep (se 1 (by rfl) ⟨705821, by rfl⟩ : syracuseStep 941095 = 1411643) B1411643
theorem B941135 : Blo 940584 941135 := bstep (se 1 (by rfl) ⟨705851, by rfl⟩ : syracuseStep 941135 = 1411703) B1411703
theorem B941151 : Blo 940584 941151 := bstep (se 1 (by rfl) ⟨705863, by rfl⟩ : syracuseStep 941151 = 1411727) B1411727
theorem B941179 : Blo 940584 941179 := bstep (se 1 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 941179 = 1411769) B1411769
theorem B941231 : Blo 940584 941231 := bstep (se 1 (by rfl) ⟨705923, by rfl⟩ : syracuseStep 941231 = 1411847) B1411847
theorem B941255 : Blo 940584 941255 := bstep (se 1 (by rfl) ⟨705941, by rfl⟩ : syracuseStep 941255 = 1411883) B1411883
theorem B941275 : Blo 940584 941275 := bstep (se 1 (by rfl) ⟨705956, by rfl⟩ : syracuseStep 941275 = 1411913) B1411913
theorem B62774509 : Blo 940584 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B941351 : Blo 940584 941351 := bstep (se 1 (by rfl) ⟨706013, by rfl⟩ : syracuseStep 941351 = 1412027) B1412027
theorem B941391 : Blo 940584 941391 := bstep (se 1 (by rfl) ⟨706043, by rfl⟩ : syracuseStep 941391 = 1412087) B1412087
theorem B941407 : Blo 940584 941407 := bstep (se 1 (by rfl) ⟨706055, by rfl⟩ : syracuseStep 941407 = 1412111) B1412111
theorem B2121065 : Blo 940584 2121065 := bstep (se 2 (by rfl) ⟨795399, by rfl⟩ : syracuseStep 2121065 = 1590799) B1590799
theorem B941435 : Blo 940584 941435 := bstep (se 1 (by rfl) ⟨706076, by rfl⟩ : syracuseStep 941435 = 1412153) B1412153
theorem B941487 : Blo 940584 941487 := bstep (se 1 (by rfl) ⟨706115, by rfl⟩ : syracuseStep 941487 = 1412231) B1412231
theorem B941511 : Blo 940584 941511 := bstep (se 1 (by rfl) ⟨706133, by rfl⟩ : syracuseStep 941511 = 1412267) B1412267
theorem B941531 : Blo 940584 941531 := bstep (se 1 (by rfl) ⟨706148, by rfl⟩ : syracuseStep 941531 = 1412297) B1412297
theorem B7658995 : Blo 940584 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B941607 : Blo 940584 941607 := bstep (se 1 (by rfl) ⟨706205, by rfl⟩ : syracuseStep 941607 = 1412411) B1412411
theorem B7167527 : Blo 940584 7167527 := bstep (se 1 (by rfl) ⟨5375645, by rfl⟩ : syracuseStep 7167527 = 10751291) B10751291
theorem B941647 : Blo 940584 941647 := bstep (se 1 (by rfl) ⟨706235, by rfl⟩ : syracuseStep 941647 = 1412471) B1412471
theorem B941663 : Blo 940584 941663 := bstep (se 1 (by rfl) ⟨706247, by rfl⟩ : syracuseStep 941663 = 1412495) B1412495
theorem B941691 : Blo 940584 941691 := bstep (se 1 (by rfl) ⟨706268, by rfl⟩ : syracuseStep 941691 = 1412537) B1412537
theorem B941743 : Blo 940584 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B941767 : Blo 940584 941767 := bstep (se 1 (by rfl) ⟨706325, by rfl⟩ : syracuseStep 941767 = 1412651) B1412651
theorem B2678483 : Blo 940584 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B941787 : Blo 940584 941787 := bstep (se 1 (by rfl) ⟨706340, by rfl⟩ : syracuseStep 941787 = 1412681) B1412681
theorem B941863 : Blo 940584 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B941903 : Blo 940584 941903 := bstep (se 1 (by rfl) ⟨706427, by rfl⟩ : syracuseStep 941903 = 1412855) B1412855
theorem B1695583 : Blo 940584 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B941919 : Blo 940584 941919 := bstep (se 1 (by rfl) ⟨706439, by rfl⟩ : syracuseStep 941919 = 1412879) B1412879
theorem B941947 : Blo 940584 941947 := bstep (se 1 (by rfl) ⟨706460, by rfl⟩ : syracuseStep 941947 = 1412921) B1412921
theorem B941999 : Blo 940584 941999 := bstep (se 1 (by rfl) ⟨706499, by rfl⟩ : syracuseStep 941999 = 1412999) B1412999
theorem B2121659 : Blo 940584 2121659 := bstep (se 1 (by rfl) ⟨1591244, by rfl⟩ : syracuseStep 2121659 = 3182489) B3182489
theorem B942023 : Blo 940584 942023 := bstep (se 1 (by rfl) ⟨706517, by rfl⟩ : syracuseStep 942023 = 1413035) B1413035
theorem B942043 : Blo 940584 942043 := bstep (se 1 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 942043 = 1413065) B1413065
theorem B2678791 : Blo 940584 2678791 := bstep (se 1 (by rfl) ⟨2009093, by rfl⟩ : syracuseStep 2678791 = 4018187) B4018187
theorem B942119 : Blo 940584 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B2121785 : Blo 940584 2121785 := bstep (se 2 (by rfl) ⟨795669, by rfl⟩ : syracuseStep 2121785 = 1591339) B1591339
theorem B2383951 : Blo 940584 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B942159 : Blo 940584 942159 := bstep (se 1 (by rfl) ⟨706619, by rfl⟩ : syracuseStep 942159 = 1413239) B1413239
theorem B942175 : Blo 940584 942175 := bstep (se 1 (by rfl) ⟨706631, by rfl⟩ : syracuseStep 942175 = 1413263) B1413263
theorem B942203 : Blo 940584 942203 := bstep (se 1 (by rfl) ⟨706652, by rfl⟩ : syracuseStep 942203 = 1413305) B1413305
theorem B942255 : Blo 940584 942255 := bstep (se 1 (by rfl) ⟨706691, by rfl⟩ : syracuseStep 942255 = 1413383) B1413383
theorem B942279 : Blo 940584 942279 := bstep (se 1 (by rfl) ⟨706709, by rfl⟩ : syracuseStep 942279 = 1413419) B1413419
theorem B942299 : Blo 940584 942299 := bstep (se 1 (by rfl) ⟨706724, by rfl⟩ : syracuseStep 942299 = 1413449) B1413449
theorem B942375 : Blo 940584 942375 := bstep (se 1 (by rfl) ⟨706781, by rfl⟩ : syracuseStep 942375 = 1413563) B1413563
theorem B942415 : Blo 940584 942415 := bstep (se 1 (by rfl) ⟨706811, by rfl⟩ : syracuseStep 942415 = 1413623) B1413623
theorem B942431 : Blo 940584 942431 := bstep (se 1 (by rfl) ⟨706823, by rfl⟩ : syracuseStep 942431 = 1413647) B1413647
theorem B942459 : Blo 940584 942459 := bstep (se 1 (by rfl) ⟨706844, by rfl⟩ : syracuseStep 942459 = 1413689) B1413689
theorem B2122127 : Blo 940584 2122127 := bstep (se 1 (by rfl) ⟨1591595, by rfl⟩ : syracuseStep 2122127 = 3183191) B3183191
theorem B942511 : Blo 940584 942511 := bstep (se 1 (by rfl) ⟨706883, by rfl⟩ : syracuseStep 942511 = 1413767) B1413767
theorem B942535 : Blo 940584 942535 := bstep (se 1 (by rfl) ⟨706901, by rfl⟩ : syracuseStep 942535 = 1413803) B1413803
theorem B942555 : Blo 940584 942555 := bstep (se 1 (by rfl) ⟨706916, by rfl⟩ : syracuseStep 942555 = 1413833) B1413833
theorem B942631 : Blo 940584 942631 := bstep (se 1 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 942631 = 1413947) B1413947
theorem B942671 : Blo 940584 942671 := bstep (se 1 (by rfl) ⟨707003, by rfl⟩ : syracuseStep 942671 = 1414007) B1414007
theorem B942687 : Blo 940584 942687 := bstep (se 1 (by rfl) ⟨707015, by rfl⟩ : syracuseStep 942687 = 1414031) B1414031
theorem B2417249 : Blo 940584 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B942715 : Blo 940584 942715 := bstep (se 1 (by rfl) ⟨707036, by rfl⟩ : syracuseStep 942715 = 1414073) B1414073
theorem B942767 : Blo 940584 942767 := bstep (se 1 (by rfl) ⟨707075, by rfl⟩ : syracuseStep 942767 = 1414151) B1414151
theorem B942791 : Blo 940584 942791 := bstep (se 1 (by rfl) ⟨707093, by rfl⟩ : syracuseStep 942791 = 1414187) B1414187
theorem B3826385 : Blo 940584 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B2122451 : Blo 940584 2122451 := bstep (se 1 (by rfl) ⟨1591838, by rfl⟩ : syracuseStep 2122451 = 3183677) B3183677
theorem B2384599 : Blo 940584 2384599 := bstep (se 1 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 2384599 = 3576899) B3576899
theorem B942811 : Blo 940584 942811 := bstep (se 1 (by rfl) ⟨707108, by rfl⟩ : syracuseStep 942811 = 1414217) B1414217
theorem B942887 : Blo 940584 942887 := bstep (se 1 (by rfl) ⟨707165, by rfl⟩ : syracuseStep 942887 = 1414331) B1414331
theorem B942927 : Blo 940584 942927 := bstep (se 1 (by rfl) ⟨707195, by rfl⟩ : syracuseStep 942927 = 1414391) B1414391
theorem B942943 : Blo 940584 942943 := bstep (se 1 (by rfl) ⟨707207, by rfl⟩ : syracuseStep 942943 = 1414415) B1414415
theorem B10347371 : Blo 940584 10347371 := bstep (se 1 (by rfl) ⟨7760528, by rfl⟩ : syracuseStep 10347371 = 15521057) B15521057
theorem B942971 : Blo 940584 942971 := bstep (se 1 (by rfl) ⟨707228, by rfl⟩ : syracuseStep 942971 = 1414457) B1414457
theorem B2679713 : Blo 940584 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B943023 : Blo 940584 943023 := bstep (se 1 (by rfl) ⟨707267, by rfl⟩ : syracuseStep 943023 = 1414535) B1414535
theorem B943047 : Blo 940584 943047 := bstep (se 1 (by rfl) ⟨707285, by rfl⟩ : syracuseStep 943047 = 1414571) B1414571
theorem B943067 : Blo 940584 943067 := bstep (se 1 (by rfl) ⟨707300, by rfl⟩ : syracuseStep 943067 = 1414601) B1414601
theorem B5104613 : Blo 940584 5104613 := bstep (se 4 (by rfl) ⟨478557, by rfl⟩ : syracuseStep 5104613 = 957115) B957115
theorem B2384903 : Blo 940584 2384903 := bstep (se 1 (by rfl) ⟨1788677, by rfl⟩ : syracuseStep 2384903 = 3577355) B3577355
theorem B943143 : Blo 940584 943143 := bstep (se 1 (by rfl) ⟨707357, by rfl⟩ : syracuseStep 943143 = 1414715) B1414715
theorem B6808627 : Blo 940584 6808627 := bstep (se 1 (by rfl) ⟨5106470, by rfl⟩ : syracuseStep 6808627 = 10212941) B10212941
theorem B943183 : Blo 940584 943183 := bstep (se 1 (by rfl) ⟨707387, by rfl⟩ : syracuseStep 943183 = 1414775) B1414775
theorem B943199 : Blo 940584 943199 := bstep (se 1 (by rfl) ⟨707399, by rfl⟩ : syracuseStep 943199 = 1414799) B1414799
theorem B943227 : Blo 940584 943227 := bstep (se 1 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 943227 = 1414841) B1414841
theorem B9168025 : Blo 940584 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B943279 : Blo 940584 943279 := bstep (se 1 (by rfl) ⟨707459, by rfl⟩ : syracuseStep 943279 = 1414919) B1414919
theorem B943303 : Blo 940584 943303 := bstep (se 1 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 943303 = 1414955) B1414955
theorem B943323 : Blo 940584 943323 := bstep (se 1 (by rfl) ⟨707492, by rfl⟩ : syracuseStep 943323 = 1414985) B1414985
theorem B943399 : Blo 940584 943399 := bstep (se 1 (by rfl) ⟨707549, by rfl⟩ : syracuseStep 943399 = 1415099) B1415099
theorem B943439 : Blo 940584 943439 := bstep (se 1 (by rfl) ⟨707579, by rfl⟩ : syracuseStep 943439 = 1415159) B1415159
theorem B943455 : Blo 940584 943455 := bstep (se 1 (by rfl) ⟨707591, by rfl⟩ : syracuseStep 943455 = 1415183) B1415183
theorem B943483 : Blo 940584 943483 := bstep (se 1 (by rfl) ⟨707612, by rfl⟩ : syracuseStep 943483 = 1415225) B1415225
theorem B943535 : Blo 940584 943535 := bstep (se 1 (by rfl) ⟨707651, by rfl⟩ : syracuseStep 943535 = 1415303) B1415303
theorem B943559 : Blo 940584 943559 := bstep (se 1 (by rfl) ⟨707669, by rfl⟩ : syracuseStep 943559 = 1415339) B1415339
theorem B2680283 : Blo 940584 2680283 := bstep (se 1 (by rfl) ⟨2010212, by rfl⟩ : syracuseStep 2680283 = 4020425) B4020425
theorem B943579 : Blo 940584 943579 := bstep (se 1 (by rfl) ⟨707684, by rfl⟩ : syracuseStep 943579 = 1415369) B1415369
theorem B29025803 : Blo 940584 29025803 := bstep (se 1 (by rfl) ⟨21769352, by rfl⟩ : syracuseStep 29025803 = 43538705) B43538705
theorem B943655 : Blo 940584 943655 := bstep (se 1 (by rfl) ⟨707741, by rfl⟩ : syracuseStep 943655 = 1415483) B1415483
theorem B943695 : Blo 940584 943695 := bstep (se 1 (by rfl) ⟨707771, by rfl⟩ : syracuseStep 943695 = 1415543) B1415543
theorem B943711 : Blo 940584 943711 := bstep (se 1 (by rfl) ⟨707783, by rfl⟩ : syracuseStep 943711 = 1415567) B1415567
theorem B2123387 : Blo 940584 2123387 := bstep (se 1 (by rfl) ⟨1592540, by rfl⟩ : syracuseStep 2123387 = 3185081) B3185081
theorem B943739 : Blo 940584 943739 := bstep (se 1 (by rfl) ⟨707804, by rfl⟩ : syracuseStep 943739 = 1415609) B1415609
theorem B943791 : Blo 940584 943791 := bstep (se 1 (by rfl) ⟨707843, by rfl⟩ : syracuseStep 943791 = 1415687) B1415687
theorem B943815 : Blo 940584 943815 := bstep (se 1 (by rfl) ⟨707861, by rfl⟩ : syracuseStep 943815 = 1415723) B1415723
theorem B943835 : Blo 940584 943835 := bstep (se 1 (by rfl) ⟨707876, by rfl⟩ : syracuseStep 943835 = 1415753) B1415753
theorem B2123513 : Blo 940584 2123513 := bstep (se 2 (by rfl) ⟨796317, by rfl⟩ : syracuseStep 2123513 = 1592635) B1592635
theorem B943911 : Blo 940584 943911 := bstep (se 1 (by rfl) ⟨707933, by rfl⟩ : syracuseStep 943911 = 1415867) B1415867
theorem B943951 : Blo 940584 943951 := bstep (se 1 (by rfl) ⟨707963, by rfl⟩ : syracuseStep 943951 = 1415927) B1415927
theorem B943967 : Blo 940584 943967 := bstep (se 1 (by rfl) ⟨707975, by rfl⟩ : syracuseStep 943967 = 1415951) B1415951
theorem B943995 : Blo 940584 943995 := bstep (se 1 (by rfl) ⟨707996, by rfl⟩ : syracuseStep 943995 = 1415993) B1415993
theorem B944047 : Blo 940584 944047 := bstep (se 1 (by rfl) ⟨708035, by rfl⟩ : syracuseStep 944047 = 1416071) B1416071
theorem B944071 : Blo 940584 944071 := bstep (se 1 (by rfl) ⟨708053, by rfl⟩ : syracuseStep 944071 = 1416107) B1416107
theorem B944091 : Blo 940584 944091 := bstep (se 1 (by rfl) ⟨708068, by rfl⟩ : syracuseStep 944091 = 1416137) B1416137
theorem B2123783 : Blo 940584 2123783 := bstep (se 1 (by rfl) ⟨1592837, by rfl⟩ : syracuseStep 2123783 = 3185675) B3185675
theorem B944167 : Blo 940584 944167 := bstep (se 1 (by rfl) ⟨708125, by rfl⟩ : syracuseStep 944167 = 1416251) B1416251
theorem B2123855 : Blo 940584 2123855 := bstep (se 1 (by rfl) ⟨1592891, by rfl⟩ : syracuseStep 2123855 = 3185783) B3185783
theorem B944207 : Blo 940584 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B944223 : Blo 940584 944223 := bstep (se 1 (by rfl) ⟨708167, by rfl⟩ : syracuseStep 944223 = 1416335) B1416335
theorem B944251 : Blo 940584 944251 := bstep (se 1 (by rfl) ⟨708188, by rfl⟩ : syracuseStep 944251 = 1416377) B1416377
theorem B944303 : Blo 940584 944303 := bstep (se 1 (by rfl) ⟨708227, by rfl⟩ : syracuseStep 944303 = 1416455) B1416455
theorem B944327 : Blo 940584 944327 := bstep (se 1 (by rfl) ⟨708245, by rfl⟩ : syracuseStep 944327 = 1416491) B1416491
theorem B944347 : Blo 940584 944347 := bstep (se 1 (by rfl) ⟨708260, by rfl⟩ : syracuseStep 944347 = 1416521) B1416521
theorem B944423 : Blo 940584 944423 := bstep (se 1 (by rfl) ⟨708317, by rfl⟩ : syracuseStep 944423 = 1416635) B1416635
theorem B944463 : Blo 940584 944463 := bstep (se 1 (by rfl) ⟨708347, by rfl⟩ : syracuseStep 944463 = 1416695) B1416695
theorem B944479 : Blo 940584 944479 := bstep (se 1 (by rfl) ⟨708359, by rfl⟩ : syracuseStep 944479 = 1416719) B1416719
theorem B944507 : Blo 940584 944507 := bstep (se 1 (by rfl) ⟨708380, by rfl⟩ : syracuseStep 944507 = 1416761) B1416761
theorem B2550145 : Blo 940584 2550145 := bstep (se 2 (by rfl) ⟨956304, by rfl⟩ : syracuseStep 2550145 = 1912609) B1912609
theorem B944559 : Blo 940584 944559 := bstep (se 1 (by rfl) ⟨708419, by rfl⟩ : syracuseStep 944559 = 1416839) B1416839
theorem B944583 : Blo 940584 944583 := bstep (se 1 (by rfl) ⟨708437, by rfl⟩ : syracuseStep 944583 = 1416875) B1416875
theorem B2124251 : Blo 940584 2124251 := bstep (se 1 (by rfl) ⟨1593188, by rfl⟩ : syracuseStep 2124251 = 3186377) B3186377
theorem B2681353 : Blo 940584 2681353 := bstep (se 2 (by rfl) ⟨1005507, by rfl⟩ : syracuseStep 2681353 = 2011015) B2011015
theorem B3631675 : Blo 940584 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B2419415 : Blo 940584 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B1698553 : Blo 940584 1698553 := bstep (se 2 (by rfl) ⟨636957, by rfl⟩ : syracuseStep 1698553 = 1273915) B1273915
theorem B2681707 : Blo 940584 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B2124719 : Blo 940584 2124719 := bstep (se 1 (by rfl) ⟨1593539, by rfl⟩ : syracuseStep 2124719 = 3187079) B3187079
theorem B4779161 : Blo 940584 4779161 := bstep (se 2 (by rfl) ⟨1792185, by rfl⟩ : syracuseStep 4779161 = 3584371) B3584371
theorem B2124971 : Blo 940584 2124971 := bstep (se 1 (by rfl) ⟨1593728, by rfl⟩ : syracuseStep 2124971 = 3187457) B3187457
theorem B2387191 : Blo 940584 2387191 := bstep (se 1 (by rfl) ⟨1790393, by rfl⟩ : syracuseStep 2387191 = 3580787) B3580787
theorem B2387465 : Blo 940584 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B2387495 : Blo 940584 2387495 := bstep (se 1 (by rfl) ⟨1790621, by rfl⟩ : syracuseStep 2387495 = 3581243) B3581243
theorem B1633991 : Blo 940584 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B2387819 : Blo 940584 2387819 := bstep (se 1 (by rfl) ⟨1790864, by rfl⟩ : syracuseStep 2387819 = 3581729) B3581729
theorem B2682811 : Blo 940584 2682811 := bstep (se 1 (by rfl) ⟨2012108, by rfl⟩ : syracuseStep 2682811 = 4024217) B4024217
theorem B5599313 : Blo 940584 5599313 := bstep (se 2 (by rfl) ⟨2099742, by rfl⟩ : syracuseStep 5599313 = 4199485) B4199485
theorem B3174875 : Blo 940584 3174875 := bstep (se 1 (by rfl) ⟨2381156, by rfl⟩ : syracuseStep 3174875 = 4762313) B4762313
theorem B2388467 : Blo 940584 2388467 := bstep (se 1 (by rfl) ⟨1791350, by rfl⟩ : syracuseStep 2388467 = 3582701) B3582701
theorem B15692291 : Blo 940584 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B11465425 : Blo 940584 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B1340335 : Blo 940584 1340335 := bstep (se 1 (by rfl) ⟨1005251, by rfl⟩ : syracuseStep 1340335 = 2010503) B2010503
theorem B2388923 : Blo 940584 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B12088439 : Blo 940584 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B3175577 : Blo 940584 3175577 := bstep (se 2 (by rfl) ⟨1190841, by rfl⟩ : syracuseStep 3175577 = 2381683) B2381683
theorem B18150803 : Blo 940584 18150803 := bstep (se 1 (by rfl) ⟨13613102, by rfl⟩ : syracuseStep 18150803 = 27226205) B27226205
theorem B8058275 : Blo 940584 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B2684441 : Blo 940584 2684441 := bstep (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) B2013331
theorem B2389601 : Blo 940584 2389601 := bstep (se 2 (by rfl) ⟨896100, by rfl⟩ : syracuseStep 2389601 = 1792201) B1792201
theorem B1341127 : Blo 940584 1341127 := bstep (se 1 (by rfl) ⟨1005845, by rfl⟩ : syracuseStep 1341127 = 2011691) B2011691
theorem B1963937 : Blo 940584 1963937 := bstep (se 2 (by rfl) ⟨736476, by rfl⟩ : syracuseStep 1963937 = 1472953) B1472953
theorem B3176765 : Blo 940584 3176765 := bstep (se 3 (by rfl) ⟨595643, by rfl⟩ : syracuseStep 3176765 = 1191287) B1191287
theorem B17201645 : Blo 940584 17201645 := bstep (se 3 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 17201645 = 6450617) B6450617
theorem B3177629 : Blo 940584 3177629 := bstep (se 3 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 3177629 = 1191611) B1191611
theorem B3013949 : Blo 940584 3013949 := bstep (se 3 (by rfl) ⟨565115, by rfl⟩ : syracuseStep 3013949 = 1130231) B1130231
theorem B4029821 : Blo 940584 4029821 := bstep (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) B1511183
theorem B3178169 : Blo 940584 3178169 := bstep (se 2 (by rfl) ⟨1191813, by rfl⟩ : syracuseStep 3178169 = 2383627) B2383627
theorem B7143227 : Blo 940584 7143227 := bstep (se 1 (by rfl) ⟨5357420, by rfl⟩ : syracuseStep 7143227 = 10714841) B10714841
theorem B3571523 : Blo 940584 3571523 := bstep (se 1 (by rfl) ⟨2678642, by rfl⟩ : syracuseStep 3571523 = 5357285) B5357285
theorem B5734253 : Blo 940584 5734253 := bstep (se 3 (by rfl) ⟨1075172, by rfl⟩ : syracuseStep 5734253 = 2150345) B2150345
theorem B3571721 : Blo 940584 3571721 := bstep (se 2 (by rfl) ⟨1339395, by rfl⟩ : syracuseStep 3571721 = 2678791) B2678791
theorem B3178601 : Blo 940584 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B1344071 : Blo 940584 1344071 := bstep (se 1 (by rfl) ⟨1008053, by rfl⟩ : syracuseStep 1344071 = 2016107) B2016107
theorem B22970951 : Blo 940584 22970951 := bstep (se 1 (by rfl) ⟨17228213, by rfl⟩ : syracuseStep 22970951 = 34456427) B34456427
theorem B3179465 : Blo 940584 3179465 := bstep (se 2 (by rfl) ⟨1192299, by rfl⟩ : syracuseStep 3179465 = 2384599) B2384599
theorem B24118235 : Blo 940584 24118235 := bstep (se 1 (by rfl) ⟨18088676, by rfl⟩ : syracuseStep 24118235 = 36177353) B36177353
theorem B3015805 : Blo 940584 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B3179735 : Blo 940584 3179735 := bstep (se 1 (by rfl) ⟨2384801, by rfl⟩ : syracuseStep 3179735 = 4769603) B4769603
theorem B9078169 : Blo 940584 9078169 := bstep (se 2 (by rfl) ⟨3404313, by rfl⟩ : syracuseStep 9078169 = 6808627) B6808627
theorem B12224033 : Blo 940584 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B12912185 : Blo 940584 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B7145657 : Blo 940584 7145657 := bstep (se 2 (by rfl) ⟨2679621, by rfl⟩ : syracuseStep 7145657 = 5359243) B5359243
theorem B1411337 : Blo 940584 1411337 := bstep (se 2 (by rfl) ⟨529251, by rfl⟩ : syracuseStep 1411337 = 1058503) B1058503
theorem B1411439 : Blo 940584 1411439 := bstep (se 1 (by rfl) ⟨1058579, by rfl⟩ : syracuseStep 1411439 = 2117159) B2117159
theorem B2689463 : Blo 940584 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B1411655 : Blo 940584 1411655 := bstep (se 1 (by rfl) ⟨1058741, by rfl⟩ : syracuseStep 1411655 = 2117483) B2117483
theorem B1411691 : Blo 940584 1411691 := bstep (se 1 (by rfl) ⟨1058768, by rfl⟩ : syracuseStep 1411691 = 2117537) B2117537
theorem B1411919 : Blo 940584 1411919 := bstep (se 1 (by rfl) ⟨1058939, by rfl⟩ : syracuseStep 1411919 = 2117879) B2117879
theorem B1412315 : Blo 940584 1412315 := bstep (se 1 (by rfl) ⟨1059236, by rfl⟩ : syracuseStep 1412315 = 2118473) B2118473
theorem B3181787 : Blo 940584 3181787 := bstep (se 1 (by rfl) ⟨2386340, by rfl⟩ : syracuseStep 3181787 = 4772681) B4772681
theorem B3575137 : Blo 940584 3575137 := bstep (se 2 (by rfl) ⟨1340676, by rfl⟩ : syracuseStep 3575137 = 2681353) B2681353
theorem B1412489 : Blo 940584 1412489 := bstep (se 2 (by rfl) ⟨529683, by rfl⟩ : syracuseStep 1412489 = 1059367) B1059367
theorem B2723321 : Blo 940584 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B3575411 : Blo 940584 3575411 := bstep (se 1 (by rfl) ⟨2681558, by rfl⟩ : syracuseStep 3575411 = 5363117) B5363117
theorem B1412843 : Blo 940584 1412843 := bstep (se 1 (by rfl) ⟨1059632, by rfl⟩ : syracuseStep 1412843 = 2119265) B2119265
theorem B3575609 : Blo 940584 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B4296509 : Blo 940584 4296509 := bstep (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) B1611191
theorem B1413071 : Blo 940584 1413071 := bstep (se 1 (by rfl) ⟨1059803, by rfl⟩ : syracuseStep 1413071 = 2119607) B2119607
theorem B3182651 : Blo 940584 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B3182921 : Blo 940584 3182921 := bstep (se 2 (by rfl) ⟨1193595, by rfl⟩ : syracuseStep 3182921 = 2387191) B2387191
theorem B1413467 : Blo 940584 1413467 := bstep (se 1 (by rfl) ⟨1060100, by rfl⟩ : syracuseStep 1413467 = 2120201) B2120201
theorem B1413695 : Blo 940584 1413695 := bstep (se 1 (by rfl) ⟨1060271, by rfl⟩ : syracuseStep 1413695 = 2120543) B2120543
theorem B1413815 : Blo 940584 1413815 := bstep (se 1 (by rfl) ⟨1060361, by rfl⟩ : syracuseStep 1413815 = 2120723) B2120723
theorem B1414043 : Blo 940584 1414043 := bstep (se 1 (by rfl) ⟨1060532, by rfl⟩ : syracuseStep 1414043 = 2121065) B2121065
theorem B3577081 : Blo 940584 3577081 := bstep (se 2 (by rfl) ⟨1341405, by rfl⟩ : syracuseStep 3577081 = 2682811) B2682811
theorem B1414439 : Blo 940584 1414439 := bstep (se 1 (by rfl) ⟨1060829, by rfl⟩ : syracuseStep 1414439 = 2121659) B2121659
theorem B1414523 : Blo 940584 1414523 := bstep (se 1 (by rfl) ⟨1060892, by rfl⟩ : syracuseStep 1414523 = 2121785) B2121785
theorem B1414649 : Blo 940584 1414649 := bstep (se 2 (by rfl) ⟨530493, by rfl⟩ : syracuseStep 1414649 = 1060987) B1060987
theorem B1414751 : Blo 940584 1414751 := bstep (se 1 (by rfl) ⟨1061063, by rfl⟩ : syracuseStep 1414751 = 2122127) B2122127
theorem B1611499 : Blo 940584 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B1414967 : Blo 940584 1414967 := bstep (se 1 (by rfl) ⟨1061225, by rfl⟩ : syracuseStep 1414967 = 2122451) B2122451
theorem B1415273 : Blo 940584 1415273 := bstep (se 2 (by rfl) ⟨530727, by rfl⟩ : syracuseStep 1415273 = 1061455) B1061455
theorem B7739725 : Blo 940584 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B10197373 : Blo 940584 10197373 := bstep (se 3 (by rfl) ⟨1912007, by rfl⟩ : syracuseStep 10197373 = 3824015) B3824015
theorem B1415591 : Blo 940584 1415591 := bstep (se 1 (by rfl) ⟨1061693, by rfl⟩ : syracuseStep 1415591 = 2123387) B2123387
theorem B3021239 : Blo 940584 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B1415675 : Blo 940584 1415675 := bstep (se 1 (by rfl) ⟨1061756, by rfl⟩ : syracuseStep 1415675 = 2123513) B2123513
theorem B1415801 : Blo 940584 1415801 := bstep (se 2 (by rfl) ⟨530925, by rfl⟩ : syracuseStep 1415801 = 1061851) B1061851
theorem B1415855 : Blo 940584 1415855 := bstep (se 1 (by rfl) ⟨1061891, by rfl⟩ : syracuseStep 1415855 = 2123783) B2123783
theorem B1415903 : Blo 940584 1415903 := bstep (se 1 (by rfl) ⟨1061927, by rfl⟩ : syracuseStep 1415903 = 2123855) B2123855
theorem B1416167 : Blo 940584 1416167 := bstep (se 1 (by rfl) ⟨1062125, by rfl⟩ : syracuseStep 1416167 = 2124251) B2124251
theorem B1612943 : Blo 940584 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B1416425 : Blo 940584 1416425 := bstep (se 2 (by rfl) ⟨531159, by rfl⟩ : syracuseStep 1416425 = 1062319) B1062319
theorem B1416479 : Blo 940584 1416479 := bstep (se 1 (by rfl) ⟨1062359, by rfl⟩ : syracuseStep 1416479 = 2124719) B2124719
theorem B3186107 : Blo 940584 3186107 := bstep (se 1 (by rfl) ⟨2389580, by rfl⟩ : syracuseStep 3186107 = 4779161) B4779161
theorem B1416647 : Blo 940584 1416647 := bstep (se 1 (by rfl) ⟨1062485, by rfl⟩ : syracuseStep 1416647 = 2124971) B2124971
theorem B13770263 : Blo 940584 13770263 := bstep (se 1 (by rfl) ⟨10327697, by rfl⟩ : syracuseStep 13770263 = 20655395) B20655395
theorem B2039353 : Blo 940584 2039353 := bstep (se 2 (by rfl) ⟨764757, by rfl⟩ : syracuseStep 2039353 = 1529515) B1529515
theorem B3022571 : Blo 940584 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B6790985 : Blo 940584 6790985 := bstep (se 2 (by rfl) ⟨2546619, by rfl⟩ : syracuseStep 6790985 = 5093239) B5093239
theorem B7151489 : Blo 940584 7151489 := bstep (se 2 (by rfl) ⟨2681808, by rfl⟩ : syracuseStep 7151489 = 5363617) B5363617
theorem B10461527 : Blo 940584 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B12100535 : Blo 940584 12100535 := bstep (se 1 (by rfl) ⟨9075401, by rfl⟩ : syracuseStep 12100535 = 18150803) B18150803
theorem B7152947 : Blo 940584 7152947 := bstep (se 1 (by rfl) ⟨5364710, by rfl⟩ : syracuseStep 7152947 = 10729421) B10729421
theorem B1058215 : Blo 940584 1058215 := bstep (se 1 (by rfl) ⟨793661, by rfl⟩ : syracuseStep 1058215 = 1587323) B1587323
theorem B83699345 : Blo 940584 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B6039197 : Blo 940584 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B1058791 : Blo 940584 1058791 := bstep (se 1 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 1058791 = 1588187) B1588187
theorem B3025031 : Blo 940584 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B2009299 : Blo 940584 2009299 := bstep (se 1 (by rfl) ⟨1506974, by rfl⟩ : syracuseStep 2009299 = 3013949) B3013949
theorem B4762151 : Blo 940584 4762151 := bstep (se 1 (by rfl) ⟨3571613, by rfl⟩ : syracuseStep 4762151 = 7143227) B7143227
theorem B19376819 : Blo 940584 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B5090039 : Blo 940584 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B1060447 : Blo 940584 1060447 := bstep (se 1 (by rfl) ⟨795335, by rfl⟩ : syracuseStep 1060447 = 1590671) B1590671
theorem B1814329 : Blo 940584 1814329 := bstep (se 2 (by rfl) ⟨680373, by rfl⟩ : syracuseStep 1814329 = 1360747) B1360747
theorem B8040505 : Blo 940584 8040505 := bstep (se 2 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 8040505 = 6030379) B6030379
theorem B1192315 : Blo 940584 1192315 := bstep (se 1 (by rfl) ⟨894236, by rfl⟩ : syracuseStep 1192315 = 1788473) B1788473
theorem B4764257 : Blo 940584 4764257 := bstep (se 2 (by rfl) ⟨1786596, by rfl⟩ : syracuseStep 4764257 = 3573193) B3573193
theorem B1061599 : Blo 940584 1061599 := bstep (se 1 (by rfl) ⟨796199, by rfl⟩ : syracuseStep 1061599 = 1592399) B1592399
theorem B38679403 : Blo 940584 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B8041463 : Blo 940584 8041463 := bstep (se 1 (by rfl) ⟨6031097, by rfl⟩ : syracuseStep 8041463 = 12062195) B12062195
theorem B3814543 : Blo 940584 3814543 := bstep (se 1 (by rfl) ⟨2860907, by rfl⟩ : syracuseStep 3814543 = 5721815) B5721815
theorem B4764905 : Blo 940584 4764905 := bstep (se 2 (by rfl) ⟨1786839, by rfl⟩ : syracuseStep 4764905 = 3573679) B3573679
theorem B1062175 : Blo 940584 1062175 := bstep (se 1 (by rfl) ⟨796631, by rfl⟩ : syracuseStep 1062175 = 1593263) B1593263
theorem B4765067 : Blo 940584 4765067 := bstep (se 1 (by rfl) ⟨3573800, by rfl⟩ : syracuseStep 4765067 = 7147601) B7147601
theorem B1193383 : Blo 940584 1193383 := bstep (se 1 (by rfl) ⟨895037, by rfl⟩ : syracuseStep 1193383 = 1790075) B1790075
theorem B16135685 : Blo 940584 16135685 := bstep (se 4 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 16135685 = 3025441) B3025441
theorem B10171943 : Blo 940584 10171943 := bstep (se 1 (by rfl) ⟨7628957, by rfl⟩ : syracuseStep 10171943 = 15257915) B15257915
theorem B1062463 : Blo 940584 1062463 := bstep (se 1 (by rfl) ⟨796847, by rfl⟩ : syracuseStep 1062463 = 1593695) B1593695
theorem B1193707 : Blo 940584 1193707 := bstep (se 1 (by rfl) ⟨895280, by rfl⟩ : syracuseStep 1193707 = 1790561) B1790561
theorem B24131357 : Blo 940584 24131357 := bstep (se 3 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 24131357 = 9049259) B9049259
theorem B1193935 : Blo 940584 1193935 := bstep (se 1 (by rfl) ⟨895451, by rfl⟩ : syracuseStep 1193935 = 1790903) B1790903
theorem B1194203 : Blo 940584 1194203 := bstep (se 1 (by rfl) ⟨895652, by rfl⟩ : syracuseStep 1194203 = 1791305) B1791305
theorem B3586301 : Blo 940584 3586301 := bstep (se 3 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 3586301 = 1344863) B1344863
theorem B1587775 : Blo 940584 1587775 := bstep (se 1 (by rfl) ⟨1190831, by rfl⟩ : syracuseStep 1587775 = 2381663) B2381663
theorem B2013817 : Blo 940584 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B9058949 : Blo 940584 9058949 := bstep (se 4 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 9058949 = 1698553) B1698553
theorem B1194679 : Blo 940584 1194679 := bstep (se 1 (by rfl) ⟨896009, by rfl⟩ : syracuseStep 1194679 = 1792019) B1792019
theorem B1194907 : Blo 940584 1194907 := bstep (se 1 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 1194907 = 1792361) B1792361
theorem B9681839 : Blo 940584 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B5094515 : Blo 940584 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B1588457 : Blo 940584 1588457 := bstep (se 2 (by rfl) ⟨595671, by rfl⟩ : syracuseStep 1588457 = 1191343) B1191343
theorem B1588511 : Blo 940584 1588511 := bstep (se 1 (by rfl) ⟨1191383, by rfl⟩ : syracuseStep 1588511 = 2382767) B2382767
theorem B2014561 : Blo 940584 2014561 := bstep (se 2 (by rfl) ⟨755460, by rfl⟩ : syracuseStep 2014561 = 1510921) B1510921
theorem B1785655 : Blo 940584 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B418234211 : Blo 940584 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B148750805 : Blo 940584 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B4768307 : Blo 940584 4768307 := bstep (se 1 (by rfl) ⟨3576230, by rfl⟩ : syracuseStep 4768307 = 7152461) B7152461
theorem B4833863 : Blo 940584 4833863 := bstep (se 1 (by rfl) ⟨3625397, by rfl⟩ : syracuseStep 4833863 = 7250795) B7250795
theorem B6898247 : Blo 940584 6898247 := bstep (se 1 (by rfl) ⟨5173685, by rfl⟩ : syracuseStep 6898247 = 10347371) B10347371
theorem B1786475 : Blo 940584 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B1589881 : Blo 940584 1589881 := bstep (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) B1192411
theorem B1589935 : Blo 940584 1589935 := bstep (se 1 (by rfl) ⟨1192451, by rfl⟩ : syracuseStep 1589935 = 2384903) B2384903
theorem B15287233 : Blo 940584 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B1786855 : Blo 940584 1786855 := bstep (se 1 (by rfl) ⟨1340141, by rfl⟩ : syracuseStep 1786855 = 2680283) B2680283
theorem B19350535 : Blo 940584 19350535 := bstep (se 1 (by rfl) ⟨14512901, by rfl⟩ : syracuseStep 19350535 = 29025803) B29025803
theorem B5096591 : Blo 940584 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B1787113 : Blo 940584 1787113 := bstep (se 2 (by rfl) ⟨670167, by rfl⟩ : syracuseStep 1787113 = 1340335) B1340335
theorem B2016551 : Blo 940584 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B8046215 : Blo 940584 8046215 := bstep (se 1 (by rfl) ⟨6034661, by rfl⟩ : syracuseStep 8046215 = 12069323) B12069323
theorem B4769927 : Blo 940584 4769927 := bstep (se 1 (by rfl) ⟨3577445, by rfl⟩ : syracuseStep 4769927 = 7154891) B7154891
theorem B21743873 : Blo 940584 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B1788169 : Blo 940584 1788169 := bstep (se 2 (by rfl) ⟨670563, by rfl⟩ : syracuseStep 1788169 = 1341127) B1341127
theorem B1591643 : Blo 940584 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B1591663 : Blo 940584 1591663 := bstep (se 1 (by rfl) ⟨1193747, by rfl⟩ : syracuseStep 1591663 = 2387495) B2387495
theorem B1591879 : Blo 940584 1591879 := bstep (se 1 (by rfl) ⟨1193909, by rfl⟩ : syracuseStep 1591879 = 2387819) B2387819
theorem B9685777 : Blo 940584 9685777 := bstep (se 2 (by rfl) ⟨3632166, by rfl⟩ : syracuseStep 9685777 = 7264333) B7264333
theorem B2116583 : Blo 940584 2116583 := bstep (se 1 (by rfl) ⟨1587437, by rfl⟩ : syracuseStep 2116583 = 3174875) B3174875
theorem B1362919 : Blo 940584 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B1592311 : Blo 940584 1592311 := bstep (se 1 (by rfl) ⟨1194233, by rfl⟩ : syracuseStep 1592311 = 2388467) B2388467
theorem B1592615 : Blo 940584 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B2116961 : Blo 940584 2116961 := bstep (se 2 (by rfl) ⟨793860, by rfl⟩ : syracuseStep 2116961 = 1587721) B1587721
theorem B2117051 : Blo 940584 2117051 := bstep (se 1 (by rfl) ⟨1587788, by rfl⟩ : syracuseStep 2117051 = 3175577) B3175577
theorem B2117177 : Blo 940584 2117177 := bstep (se 2 (by rfl) ⟨793941, by rfl⟩ : syracuseStep 2117177 = 1587883) B1587883
theorem B1789627 : Blo 940584 1789627 := bstep (se 1 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 1789627 = 2684441) B2684441
theorem B1593067 : Blo 940584 1593067 := bstep (se 1 (by rfl) ⟨1194800, by rfl⟩ : syracuseStep 1593067 = 2389601) B2389601
theorem B2117843 : Blo 940584 2117843 := bstep (se 1 (by rfl) ⟨1588382, by rfl⟩ : syracuseStep 2117843 = 3176765) B3176765
theorem B2117897 : Blo 940584 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B2118113 : Blo 940584 2118113 := bstep (se 2 (by rfl) ⟨794292, by rfl⟩ : syracuseStep 2118113 = 1588585) B1588585
theorem B10211993 : Blo 940584 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B2118419 : Blo 940584 2118419 := bstep (se 1 (by rfl) ⟨1588814, by rfl⟩ : syracuseStep 2118419 = 3177629) B3177629
theorem B1430503 : Blo 940584 1430503 := bstep (se 1 (by rfl) ⟨1072877, by rfl⟩ : syracuseStep 1430503 = 2145755) B2145755
theorem B2118779 : Blo 940584 2118779 := bstep (se 1 (by rfl) ⟨1589084, by rfl⟩ : syracuseStep 2118779 = 3178169) B3178169
theorem B2381015 : Blo 940584 2381015 := bstep (se 1 (by rfl) ⟨1785761, by rfl⟩ : syracuseStep 2381015 = 3571523) B3571523
theorem B3822835 : Blo 940584 3822835 := bstep (se 1 (by rfl) ⟨2867126, by rfl⟩ : syracuseStep 3822835 = 5734253) B5734253
theorem B2118905 : Blo 940584 2118905 := bstep (se 2 (by rfl) ⟨794589, by rfl⟩ : syracuseStep 2118905 = 1589179) B1589179
theorem B1004923 : Blo 940584 1004923 := bstep (se 1 (by rfl) ⟨753692, by rfl⟩ : syracuseStep 1004923 = 1507385) B1507385
theorem B2119049 : Blo 940584 2119049 := bstep (se 2 (by rfl) ⟨794643, by rfl⟩ : syracuseStep 2119049 = 1589287) B1589287
theorem B2119175 : Blo 940584 2119175 := bstep (se 1 (by rfl) ⟨1589381, by rfl⟩ : syracuseStep 2119175 = 3178763) B3178763
theorem B9655853 : Blo 940584 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B1791571 : Blo 940584 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B2119355 : Blo 940584 2119355 := bstep (se 1 (by rfl) ⟨1589516, by rfl⟩ : syracuseStep 2119355 = 3179033) B3179033
theorem B1791791 : Blo 940584 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B2119481 : Blo 940584 2119481 := bstep (se 2 (by rfl) ⟨794805, by rfl⟩ : syracuseStep 2119481 = 1589611) B1589611
theorem B20666171 : Blo 940584 20666171 := bstep (se 1 (by rfl) ⟨15499628, by rfl⟩ : syracuseStep 20666171 = 30999257) B30999257
theorem B4020151 : Blo 940584 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B4773815 : Blo 940584 4773815 := bstep (se 1 (by rfl) ⟨3580361, by rfl⟩ : syracuseStep 4773815 = 7160723) B7160723
theorem B17192897 : Blo 940584 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B2120111 : Blo 940584 2120111 := bstep (se 1 (by rfl) ⟨1590083, by rfl⟩ : syracuseStep 2120111 = 3180167) B3180167
theorem B2120147 : Blo 940584 2120147 := bstep (se 1 (by rfl) ⟨1590110, by rfl⟩ : syracuseStep 2120147 = 3180221) B3180221
theorem B2382331 : Blo 940584 2382331 := bstep (se 1 (by rfl) ⟨1786748, by rfl⟩ : syracuseStep 2382331 = 3573497) B3573497
theorem B940607 : Blo 940584 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B2120255 : Blo 940584 2120255 := bstep (se 1 (by rfl) ⟨1590191, by rfl⟩ : syracuseStep 2120255 = 3180383) B3180383
theorem B4774463 : Blo 940584 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B940615 : Blo 940584 940615 := bstep (se 1 (by rfl) ⟨705461, by rfl⟩ : syracuseStep 940615 = 1410923) B1410923
theorem B2382443 : Blo 940584 2382443 := bstep (se 1 (by rfl) ⟨1786832, by rfl⟩ : syracuseStep 2382443 = 3573665) B3573665
theorem B22076011 : Blo 940584 22076011 := bstep (se 1 (by rfl) ⟨16557008, by rfl⟩ : syracuseStep 22076011 = 33114017) B33114017
theorem B2120363 : Blo 940584 2120363 := bstep (se 1 (by rfl) ⟨1590272, by rfl⟩ : syracuseStep 2120363 = 3180545) B3180545
theorem B1792687 : Blo 940584 1792687 := bstep (se 1 (by rfl) ⟨1344515, by rfl⟩ : syracuseStep 1792687 = 2689031) B2689031
theorem B940767 : Blo 940584 940767 := bstep (se 1 (by rfl) ⟨705575, by rfl⟩ : syracuseStep 940767 = 1411151) B1411151
theorem B940847 : Blo 940584 940847 := bstep (se 1 (by rfl) ⟨705635, by rfl⟩ : syracuseStep 940847 = 1411271) B1411271
theorem B1792847 : Blo 940584 1792847 := bstep (se 1 (by rfl) ⟨1344635, by rfl⟩ : syracuseStep 1792847 = 2689271) B2689271
theorem B940955 : Blo 940584 940955 := bstep (se 1 (by rfl) ⟨705716, by rfl⟩ : syracuseStep 940955 = 1411433) B1411433
theorem B941007 : Blo 940584 941007 := bstep (se 1 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 941007 = 1411511) B1411511
theorem B941031 : Blo 940584 941031 := bstep (se 1 (by rfl) ⟨705773, by rfl⟩ : syracuseStep 941031 = 1411547) B1411547
theorem B4086865 : Blo 940584 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B2120903 : Blo 940584 2120903 := bstep (se 1 (by rfl) ⟨1590677, by rfl⟩ : syracuseStep 2120903 = 3181355) B3181355
theorem B2546921 : Blo 940584 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B2383091 : Blo 940584 2383091 := bstep (se 1 (by rfl) ⟨1787318, by rfl⟩ : syracuseStep 2383091 = 3574637) B3574637
theorem B941343 : Blo 940584 941343 := bstep (se 1 (by rfl) ⟨706007, by rfl⟩ : syracuseStep 941343 = 1412015) B1412015
theorem B941403 : Blo 940584 941403 := bstep (se 1 (by rfl) ⟨706052, by rfl⟩ : syracuseStep 941403 = 1412105) B1412105
theorem B1006939 : Blo 940584 1006939 := bstep (se 1 (by rfl) ⟨755204, by rfl⟩ : syracuseStep 1006939 = 1510409) B1510409
theorem B941423 : Blo 940584 941423 := bstep (se 1 (by rfl) ⟨706067, by rfl⟩ : syracuseStep 941423 = 1412135) B1412135
theorem B2121083 : Blo 940584 2121083 := bstep (se 1 (by rfl) ⟨1590812, by rfl⟩ : syracuseStep 2121083 = 3181625) B3181625
theorem B941479 : Blo 940584 941479 := bstep (se 1 (by rfl) ⟨706109, by rfl⟩ : syracuseStep 941479 = 1412219) B1412219
theorem B2383303 : Blo 940584 2383303 := bstep (se 1 (by rfl) ⟨1787477, by rfl⟩ : syracuseStep 2383303 = 3574955) B3574955
theorem B2121209 : Blo 940584 2121209 := bstep (se 2 (by rfl) ⟨795453, by rfl⟩ : syracuseStep 2121209 = 1590907) B1590907
theorem B941563 : Blo 940584 941563 := bstep (se 1 (by rfl) ⟨706172, by rfl⟩ : syracuseStep 941563 = 1412345) B1412345
theorem B10182149 : Blo 940584 10182149 := bstep (se 4 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 10182149 = 1909153) B1909153
theorem B941631 : Blo 940584 941631 := bstep (se 1 (by rfl) ⟨706223, by rfl⟩ : syracuseStep 941631 = 1412447) B1412447
theorem B941639 : Blo 940584 941639 := bstep (se 1 (by rfl) ⟨706229, by rfl⟩ : syracuseStep 941639 = 1412459) B1412459
theorem B2121299 : Blo 940584 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B941791 : Blo 940584 941791 := bstep (se 1 (by rfl) ⟨706343, by rfl⟩ : syracuseStep 941791 = 1412687) B1412687
theorem B2547463 : Blo 940584 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B2121479 : Blo 940584 2121479 := bstep (se 1 (by rfl) ⟨1591109, by rfl⟩ : syracuseStep 2121479 = 3182219) B3182219
theorem B941871 : Blo 940584 941871 := bstep (se 1 (by rfl) ⟨706403, by rfl⟩ : syracuseStep 941871 = 1412807) B1412807
theorem B4349803 : Blo 940584 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B2416513 : Blo 940584 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B941979 : Blo 940584 941979 := bstep (se 1 (by rfl) ⟨706484, by rfl⟩ : syracuseStep 941979 = 1412969) B1412969
theorem B942031 : Blo 940584 942031 := bstep (se 1 (by rfl) ⟨706523, by rfl⟩ : syracuseStep 942031 = 1413047) B1413047
theorem B942055 : Blo 940584 942055 := bstep (se 1 (by rfl) ⟨706541, by rfl⟩ : syracuseStep 942055 = 1413083) B1413083
theorem B942367 : Blo 940584 942367 := bstep (se 1 (by rfl) ⟨706775, by rfl⟩ : syracuseStep 942367 = 1413551) B1413551
theorem B942427 : Blo 940584 942427 := bstep (se 1 (by rfl) ⟨706820, by rfl⟩ : syracuseStep 942427 = 1413641) B1413641
theorem B2122091 : Blo 940584 2122091 := bstep (se 1 (by rfl) ⟨1591568, by rfl⟩ : syracuseStep 2122091 = 3183137) B3183137
theorem B4088171 : Blo 940584 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B942447 : Blo 940584 942447 := bstep (se 1 (by rfl) ⟨706835, by rfl⟩ : syracuseStep 942447 = 1413671) B1413671
theorem B942503 : Blo 940584 942503 := bstep (se 1 (by rfl) ⟨706877, by rfl⟩ : syracuseStep 942503 = 1413755) B1413755
theorem B4841903 : Blo 940584 4841903 := bstep (se 1 (by rfl) ⟨3631427, by rfl⟩ : syracuseStep 4841903 = 7262855) B7262855
theorem B942587 : Blo 940584 942587 := bstep (se 1 (by rfl) ⟨706940, by rfl⟩ : syracuseStep 942587 = 1413881) B1413881
theorem B2122235 : Blo 940584 2122235 := bstep (se 1 (by rfl) ⟨1591676, by rfl⟩ : syracuseStep 2122235 = 3183353) B3183353
theorem B3400193 : Blo 940584 3400193 := bstep (se 2 (by rfl) ⟨1275072, by rfl⟩ : syracuseStep 3400193 = 2550145) B2550145
theorem B942655 : Blo 940584 942655 := bstep (se 1 (by rfl) ⟨706991, by rfl⟩ : syracuseStep 942655 = 1413983) B1413983
theorem B942663 : Blo 940584 942663 := bstep (se 1 (by rfl) ⟨706997, by rfl⟩ : syracuseStep 942663 = 1413995) B1413995
theorem B2122361 : Blo 940584 2122361 := bstep (se 2 (by rfl) ⟨795885, by rfl⟩ : syracuseStep 2122361 = 1591771) B1591771
theorem B4776569 : Blo 940584 4776569 := bstep (se 2 (by rfl) ⟨1791213, by rfl⟩ : syracuseStep 4776569 = 3582427) B3582427
theorem B4842155 : Blo 940584 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B2122415 : Blo 940584 2122415 := bstep (se 1 (by rfl) ⟨1591811, by rfl⟩ : syracuseStep 2122415 = 3183623) B3183623
theorem B942815 : Blo 940584 942815 := bstep (se 1 (by rfl) ⟨707111, by rfl⟩ : syracuseStep 942815 = 1414223) B1414223
theorem B2122487 : Blo 940584 2122487 := bstep (se 1 (by rfl) ⟨1591865, by rfl⟩ : syracuseStep 2122487 = 3183731) B3183731
theorem B4842233 : Blo 940584 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B942895 : Blo 940584 942895 := bstep (se 1 (by rfl) ⟨707171, by rfl⟩ : syracuseStep 942895 = 1414343) B1414343
theorem B9069407 : Blo 940584 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B943003 : Blo 940584 943003 := bstep (se 1 (by rfl) ⟨707252, by rfl⟩ : syracuseStep 943003 = 1414505) B1414505
theorem B5104549 : Blo 940584 5104549 := bstep (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) B957103
theorem B2122667 : Blo 940584 2122667 := bstep (se 1 (by rfl) ⟨1592000, by rfl⟩ : syracuseStep 2122667 = 3184001) B3184001
theorem B943055 : Blo 940584 943055 := bstep (se 1 (by rfl) ⟨707291, by rfl⟩ : syracuseStep 943055 = 1414583) B1414583
theorem B943079 : Blo 940584 943079 := bstep (se 1 (by rfl) ⟨707309, by rfl⟩ : syracuseStep 943079 = 1414619) B1414619
theorem B2385035 : Blo 940584 2385035 := bstep (se 1 (by rfl) ⟨1788776, by rfl⟩ : syracuseStep 2385035 = 3577553) B3577553
theorem B943391 : Blo 940584 943391 := bstep (se 1 (by rfl) ⟨707543, by rfl⟩ : syracuseStep 943391 = 1415087) B1415087
theorem B943451 : Blo 940584 943451 := bstep (se 1 (by rfl) ⟨707588, by rfl⟩ : syracuseStep 943451 = 1415177) B1415177
theorem B2385247 : Blo 940584 2385247 := bstep (se 1 (by rfl) ⟨1788935, by rfl⟩ : syracuseStep 2385247 = 3577871) B3577871
theorem B943471 : Blo 940584 943471 := bstep (se 1 (by rfl) ⟨707603, by rfl⟩ : syracuseStep 943471 = 1415207) B1415207
theorem B943527 : Blo 940584 943527 := bstep (se 1 (by rfl) ⟨707645, by rfl⟩ : syracuseStep 943527 = 1415291) B1415291
theorem B2123207 : Blo 940584 2123207 := bstep (se 1 (by rfl) ⟨1592405, by rfl⟩ : syracuseStep 2123207 = 3184811) B3184811
theorem B943611 : Blo 940584 943611 := bstep (se 1 (by rfl) ⟨707708, by rfl⟩ : syracuseStep 943611 = 1415417) B1415417
theorem B943679 : Blo 940584 943679 := bstep (se 1 (by rfl) ⟨707759, by rfl⟩ : syracuseStep 943679 = 1415519) B1415519
theorem B943687 : Blo 940584 943687 := bstep (se 1 (by rfl) ⟨707765, by rfl⟩ : syracuseStep 943687 = 1415531) B1415531
theorem B7628377 : Blo 940584 7628377 := bstep (se 2 (by rfl) ⟨2860641, by rfl⟩ : syracuseStep 7628377 = 5721283) B5721283
theorem B943839 : Blo 940584 943839 := bstep (se 1 (by rfl) ⟨707879, by rfl⟩ : syracuseStep 943839 = 1415759) B1415759
theorem B2123567 : Blo 940584 2123567 := bstep (se 1 (by rfl) ⟨1592675, by rfl⟩ : syracuseStep 2123567 = 3185351) B3185351
theorem B943919 : Blo 940584 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B4417361 : Blo 940584 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B9070481 : Blo 940584 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B944027 : Blo 940584 944027 := bstep (se 1 (by rfl) ⟨708020, by rfl⟩ : syracuseStep 944027 = 1416041) B1416041
theorem B944079 : Blo 940584 944079 := bstep (se 1 (by rfl) ⟨708059, by rfl⟩ : syracuseStep 944079 = 1416119) B1416119
theorem B944103 : Blo 940584 944103 := bstep (se 1 (by rfl) ⟨708077, by rfl⟩ : syracuseStep 944103 = 1416155) B1416155
theorem B16083197 : Blo 940584 16083197 := bstep (se 3 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 16083197 = 6031199) B6031199
theorem B2550025 : Blo 940584 2550025 := bstep (se 2 (by rfl) ⟨956259, by rfl⟩ : syracuseStep 2550025 = 1912519) B1912519
theorem B944415 : Blo 940584 944415 := bstep (se 1 (by rfl) ⟨708311, by rfl⟩ : syracuseStep 944415 = 1416623) B1416623
theorem B944475 : Blo 940584 944475 := bstep (se 1 (by rfl) ⟨708356, by rfl⟩ : syracuseStep 944475 = 1416713) B1416713
theorem B4778351 : Blo 940584 4778351 := bstep (se 1 (by rfl) ⟨3583763, by rfl⟩ : syracuseStep 4778351 = 7167527) B7167527
theorem B2124143 : Blo 940584 2124143 := bstep (se 1 (by rfl) ⟨1593107, by rfl⟩ : syracuseStep 2124143 = 3186215) B3186215
theorem B944495 : Blo 940584 944495 := bstep (se 1 (by rfl) ⟨708371, by rfl⟩ : syracuseStep 944495 = 1416743) B1416743
theorem B944551 : Blo 940584 944551 := bstep (se 1 (by rfl) ⟨708413, by rfl⟩ : syracuseStep 944551 = 1416827) B1416827
theorem B5237165 : Blo 940584 5237165 := bstep (se 3 (by rfl) ⟨981968, by rfl⟩ : syracuseStep 5237165 = 1963937) B1963937
theorem B20670893 : Blo 940584 20670893 := bstep (se 3 (by rfl) ⟨3875792, by rfl⟩ : syracuseStep 20670893 = 7751585) B7751585
theorem B2124215 : Blo 940584 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B2124359 : Blo 940584 2124359 := bstep (se 1 (by rfl) ⟨1593269, by rfl⟩ : syracuseStep 2124359 = 3186539) B3186539
theorem B2124395 : Blo 940584 2124395 := bstep (se 1 (by rfl) ⟨1593296, by rfl⟩ : syracuseStep 2124395 = 3186593) B3186593
theorem B2386655 : Blo 940584 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B25783193 : Blo 940584 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B2124791 : Blo 940584 2124791 := bstep (se 1 (by rfl) ⟨1593593, by rfl⟩ : syracuseStep 2124791 = 3187187) B3187187
theorem B4025483 : Blo 940584 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B2550923 : Blo 940584 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B3403075 : Blo 940584 3403075 := bstep (se 1 (by rfl) ⟨2552306, by rfl⟩ : syracuseStep 3403075 = 5104613) B5104613
theorem B2125151 : Blo 940584 2125151 := bstep (se 1 (by rfl) ⟨1593863, by rfl⟩ : syracuseStep 2125151 = 3187727) B3187727
theorem B3436445 : Blo 940584 3436445 := bstep (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) B1288667
theorem B1273807 : Blo 940584 1273807 := bstep (se 1 (by rfl) ⟨955355, by rfl⟩ : syracuseStep 1273807 = 1910711) B1910711
theorem B4026473 : Blo 940584 4026473 := bstep (se 2 (by rfl) ⟨1509927, by rfl⟩ : syracuseStep 4026473 = 3019855) B3019855
theorem B10186955 : Blo 940584 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B3174983 : Blo 940584 3174983 := bstep (se 1 (by rfl) ⟨2381237, by rfl⟩ : syracuseStep 3174983 = 4762475) B4762475
theorem B3175415 : Blo 940584 3175415 := bstep (se 1 (by rfl) ⟨2381561, by rfl⟩ : syracuseStep 3175415 = 4763123) B4763123
theorem B2389115 : Blo 940584 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B2389135 : Blo 940584 2389135 := bstep (se 1 (by rfl) ⟨1791851, by rfl⟩ : syracuseStep 2389135 = 3583703) B3583703
theorem B8058001 : Blo 940584 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B3732875 : Blo 940584 3732875 := bstep (se 1 (by rfl) ⟨2799656, by rfl⟩ : syracuseStep 3732875 = 5599313) B5599313
theorem B3634571 : Blo 940584 3634571 := bstep (se 1 (by rfl) ⟨2725928, by rfl⟩ : syracuseStep 3634571 = 5451857) B5451857
theorem B2389409 : Blo 940584 2389409 := bstep (se 2 (by rfl) ⟨896028, by rfl⟩ : syracuseStep 2389409 = 1792057) B1792057
theorem B173930165 : Blo 940584 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B4781753 : Blo 940584 4781753 := bstep (se 2 (by rfl) ⟨1793157, by rfl⟩ : syracuseStep 4781753 = 3586315) B3586315
theorem B3176279 : Blo 940584 3176279 := bstep (se 1 (by rfl) ⟨2382209, by rfl⟩ : syracuseStep 3176279 = 4764419) B4764419
theorem B8058959 : Blo 940584 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B5372183 : Blo 940584 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B1276327 : Blo 940584 1276327 := bstep (se 1 (by rfl) ⟨957245, by rfl⟩ : syracuseStep 1276327 = 1914491) B1914491
theorem B1341947 : Blo 940584 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B4291145 : Blo 940584 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B33094277 : Blo 940584 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B3177359 : Blo 940584 3177359 := bstep (se 1 (by rfl) ⟨2383019, by rfl⟩ : syracuseStep 3177359 = 4766039) B4766039
theorem B11467763 : Blo 940584 11467763 := bstep (se 1 (by rfl) ⟨8600822, by rfl⟩ : syracuseStep 11467763 = 17201645) B17201645
theorem B2587745 : Blo 940584 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B7634083 : Blo 940584 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B9043109 : Blo 940584 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B4357309 : Blo 940584 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B9666071 : Blo 940584 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B2686547 : Blo 940584 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B4292459 : Blo 940584 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B3178871 : Blo 940584 3178871 := bstep (se 1 (by rfl) ⟨2384153, by rfl⟩ : syracuseStep 3178871 = 4768307) B4768307
theorem B1344367 : Blo 940584 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B12911741 : Blo 940584 12911741 := bstep (se 3 (by rfl) ⟨2420951, by rfl⟩ : syracuseStep 12911741 = 4841903) B4841903
theorem B20382977 : Blo 940584 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B13600133 : Blo 940584 13600133 := bstep (se 4 (by rfl) ⟨1275012, by rfl⟩ : syracuseStep 13600133 = 2550025) B2550025
theorem B3179951 : Blo 940584 3179951 := bstep (se 1 (by rfl) ⟨2384963, by rfl⟩ : syracuseStep 3179951 = 4769927) B4769927
theorem B3180329 : Blo 940584 3180329 := bstep (se 2 (by rfl) ⟨1192623, by rfl⟩ : syracuseStep 3180329 = 2385247) B2385247
theorem B1410953 : Blo 940584 1410953 := bstep (se 2 (by rfl) ⟨529107, by rfl⟩ : syracuseStep 1410953 = 1058215) B1058215
theorem B1411055 : Blo 940584 1411055 := bstep (se 1 (by rfl) ⟨1058291, by rfl⟩ : syracuseStep 1411055 = 2116583) B2116583
theorem B1411307 : Blo 940584 1411307 := bstep (se 1 (by rfl) ⟨1058480, by rfl⟩ : syracuseStep 1411307 = 2116961) B2116961
theorem B1411367 : Blo 940584 1411367 := bstep (se 1 (by rfl) ⟨1058525, by rfl⟩ : syracuseStep 1411367 = 2117051) B2117051
theorem B1411451 : Blo 940584 1411451 := bstep (se 1 (by rfl) ⟨1058588, by rfl⟩ : syracuseStep 1411451 = 2117177) B2117177
theorem B1411721 : Blo 940584 1411721 := bstep (se 2 (by rfl) ⟨529395, by rfl⟩ : syracuseStep 1411721 = 1058791) B1058791
theorem B1411895 : Blo 940584 1411895 := bstep (se 1 (by rfl) ⟨1058921, by rfl⟩ : syracuseStep 1411895 = 2117843) B2117843
theorem B1411931 : Blo 940584 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B1412075 : Blo 940584 1412075 := bstep (se 1 (by rfl) ⟨1059056, by rfl⟩ : syracuseStep 1412075 = 2118113) B2118113
theorem B1412279 : Blo 940584 1412279 := bstep (se 1 (by rfl) ⟨1059209, by rfl⟩ : syracuseStep 1412279 = 2118419) B2118419
theorem B1412519 : Blo 940584 1412519 := bstep (se 1 (by rfl) ⟨1059389, by rfl⟩ : syracuseStep 1412519 = 2118779) B2118779
theorem B1412603 : Blo 940584 1412603 := bstep (se 1 (by rfl) ⟨1059452, by rfl⟩ : syracuseStep 1412603 = 2118905) B2118905
theorem B1412699 : Blo 940584 1412699 := bstep (se 1 (by rfl) ⟨1059524, by rfl⟩ : syracuseStep 1412699 = 2119049) B2119049
theorem B1412783 : Blo 940584 1412783 := bstep (se 1 (by rfl) ⟨1059587, by rfl⟩ : syracuseStep 1412783 = 2119175) B2119175
theorem B12914369 : Blo 940584 12914369 := bstep (se 2 (by rfl) ⟨4842888, by rfl⟩ : syracuseStep 12914369 = 9685777) B9685777
theorem B1412903 : Blo 940584 1412903 := bstep (se 1 (by rfl) ⟨1059677, by rfl⟩ : syracuseStep 1412903 = 2119355) B2119355
theorem B1412987 : Blo 940584 1412987 := bstep (se 1 (by rfl) ⟨1059740, by rfl⟩ : syracuseStep 1412987 = 2119481) B2119481
theorem B3182543 : Blo 940584 3182543 := bstep (se 1 (by rfl) ⟨2386907, by rfl⟩ : syracuseStep 3182543 = 4773815) B4773815
theorem B1413407 : Blo 940584 1413407 := bstep (se 1 (by rfl) ⟨1060055, by rfl⟩ : syracuseStep 1413407 = 2120111) B2120111
theorem B1413431 : Blo 940584 1413431 := bstep (se 1 (by rfl) ⟨1060073, by rfl⟩ : syracuseStep 1413431 = 2120147) B2120147
theorem B1413503 : Blo 940584 1413503 := bstep (se 1 (by rfl) ⟨1060127, by rfl⟩ : syracuseStep 1413503 = 2120255) B2120255
theorem B3182975 : Blo 940584 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B1413575 : Blo 940584 1413575 := bstep (se 1 (by rfl) ⟨1060181, by rfl⟩ : syracuseStep 1413575 = 2120363) B2120363
theorem B1413929 : Blo 940584 1413929 := bstep (se 2 (by rfl) ⟨530223, by rfl⟩ : syracuseStep 1413929 = 1060447) B1060447
theorem B1413935 : Blo 940584 1413935 := bstep (se 1 (by rfl) ⟨1060451, by rfl⟩ : syracuseStep 1413935 = 2120903) B2120903
theorem B1414055 : Blo 940584 1414055 := bstep (se 1 (by rfl) ⟨1060541, by rfl⟩ : syracuseStep 1414055 = 2121083) B2121083
theorem B1414139 : Blo 940584 1414139 := bstep (se 1 (by rfl) ⟨1060604, by rfl⟩ : syracuseStep 1414139 = 2121209) B2121209
theorem B6788099 : Blo 940584 6788099 := bstep (se 1 (by rfl) ⟨5091074, by rfl⟩ : syracuseStep 6788099 = 10182149) B10182149
theorem B1414199 : Blo 940584 1414199 := bstep (se 1 (by rfl) ⟨1060649, by rfl⟩ : syracuseStep 1414199 = 2121299) B2121299
theorem B1414319 : Blo 940584 1414319 := bstep (se 1 (by rfl) ⟨1060739, by rfl⟩ : syracuseStep 1414319 = 2121479) B2121479
theorem B4527323 : Blo 940584 4527323 := bstep (se 1 (by rfl) ⟨3395492, by rfl⟩ : syracuseStep 4527323 = 6790985) B6790985
theorem B10720673 : Blo 940584 10720673 := bstep (se 2 (by rfl) ⟨4020252, by rfl⟩ : syracuseStep 10720673 = 8040505) B8040505
theorem B1414727 : Blo 940584 1414727 := bstep (se 1 (by rfl) ⟨1061045, by rfl⟩ : syracuseStep 1414727 = 2122091) B2122091
theorem B2725447 : Blo 940584 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B1414823 : Blo 940584 1414823 := bstep (se 1 (by rfl) ⟨1061117, by rfl⟩ : syracuseStep 1414823 = 2122235) B2122235
theorem B2266795 : Blo 940584 2266795 := bstep (se 1 (by rfl) ⟨1700096, by rfl⟩ : syracuseStep 2266795 = 3400193) B3400193
theorem B8066749 : Blo 940584 8066749 := bstep (se 3 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 8066749 = 3025031) B3025031
theorem B1414907 : Blo 940584 1414907 := bstep (se 1 (by rfl) ⟨1061180, by rfl⟩ : syracuseStep 1414907 = 2122361) B2122361
theorem B3184379 : Blo 940584 3184379 := bstep (se 1 (by rfl) ⟨2388284, by rfl⟩ : syracuseStep 3184379 = 4776569) B4776569
theorem B21796613 : Blo 940584 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B1414943 : Blo 940584 1414943 := bstep (se 1 (by rfl) ⟨1061207, by rfl⟩ : syracuseStep 1414943 = 2122415) B2122415
theorem B1414991 : Blo 940584 1414991 := bstep (se 1 (by rfl) ⟨1061243, by rfl⟩ : syracuseStep 1414991 = 2122487) B2122487
theorem B3184541 : Blo 940584 3184541 := bstep (se 3 (by rfl) ⟨597101, by rfl⟩ : syracuseStep 3184541 = 1194203) B1194203
theorem B1415111 : Blo 940584 1415111 := bstep (se 1 (by rfl) ⟨1061333, by rfl⟩ : syracuseStep 1415111 = 2122667) B2122667
theorem B8067023 : Blo 940584 8067023 := bstep (se 1 (by rfl) ⟨6050267, by rfl⟩ : syracuseStep 8067023 = 12100535) B12100535
theorem B1415465 : Blo 940584 1415465 := bstep (se 2 (by rfl) ⟨530799, by rfl⟩ : syracuseStep 1415465 = 1061599) B1061599
theorem B1415471 : Blo 940584 1415471 := bstep (se 1 (by rfl) ⟨1061603, by rfl⟩ : syracuseStep 1415471 = 2123207) B2123207
theorem B1415711 : Blo 940584 1415711 := bstep (se 1 (by rfl) ⟨1061783, by rfl⟩ : syracuseStep 1415711 = 2123567) B2123567
theorem B3578525 : Blo 940584 3578525 := bstep (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) B1341947
theorem B10722131 : Blo 940584 10722131 := bstep (se 1 (by rfl) ⟨8041598, by rfl⟩ : syracuseStep 10722131 = 16083197) B16083197
theorem B5086057 : Blo 940584 5086057 := bstep (se 2 (by rfl) ⟨1907271, by rfl⟩ : syracuseStep 5086057 = 3814543) B3814543
theorem B3185513 : Blo 940584 3185513 := bstep (se 2 (by rfl) ⟨1194567, by rfl⟩ : syracuseStep 3185513 = 2389135) B2389135
theorem B3185567 : Blo 940584 3185567 := bstep (se 1 (by rfl) ⟨2389175, by rfl⟩ : syracuseStep 3185567 = 4778351) B4778351
theorem B1416095 : Blo 940584 1416095 := bstep (se 1 (by rfl) ⟨1062071, by rfl⟩ : syracuseStep 1416095 = 2124143) B2124143
theorem B1416143 : Blo 940584 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B1416233 : Blo 940584 1416233 := bstep (se 2 (by rfl) ⟨531087, by rfl⟩ : syracuseStep 1416233 = 1062175) B1062175
theorem B1416239 : Blo 940584 1416239 := bstep (se 1 (by rfl) ⟨1062179, by rfl⟩ : syracuseStep 1416239 = 2124359) B2124359
theorem B1416263 : Blo 940584 1416263 := bstep (se 1 (by rfl) ⟨1062197, by rfl⟩ : syracuseStep 1416263 = 2124395) B2124395
theorem B12917879 : Blo 940584 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B1416527 : Blo 940584 1416527 := bstep (se 1 (by rfl) ⟨1062395, by rfl⟩ : syracuseStep 1416527 = 2124791) B2124791
theorem B1416617 : Blo 940584 1416617 := bstep (se 2 (by rfl) ⟨531231, by rfl⟩ : syracuseStep 1416617 = 1062463) B1062463
theorem B1416767 : Blo 940584 1416767 := bstep (se 1 (by rfl) ⟨1062575, by rfl⟩ : syracuseStep 1416767 = 2125151) B2125151
theorem B6791303 : Blo 940584 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B6791789 : Blo 940584 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B29434681 : Blo 940584 29434681 := bstep (se 2 (by rfl) ⟨11038005, by rfl⟩ : syracuseStep 29434681 = 22076011) B22076011
theorem B10757123 : Blo 940584 10757123 := bstep (se 1 (by rfl) ⟨8067842, by rfl⟩ : syracuseStep 10757123 = 16135685) B16135685
theorem B3187835 : Blo 940584 3187835 := bstep (se 1 (by rfl) ⟨2390876, by rfl⟩ : syracuseStep 3187835 = 4781753) B4781753
theorem B3581455 : Blo 940584 3581455 := bstep (se 1 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 3581455 = 5372183) B5372183
theorem B5809745 : Blo 940584 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B9676421 : Blo 940584 9676421 := bstep (se 4 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 9676421 = 1814329) B1814329
theorem B2860763 : Blo 940584 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B22062851 : Blo 940584 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B6039299 : Blo 940584 6039299 := bstep (se 1 (by rfl) ⟨4529474, by rfl⟩ : syracuseStep 6039299 = 9058949) B9058949
theorem B7645175 : Blo 940584 7645175 := bstep (se 1 (by rfl) ⟨5733881, by rfl⟩ : syracuseStep 7645175 = 11467763) B11467763
theorem B1058971 : Blo 940584 1058971 := bstep (se 1 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 1058971 = 1588457) B1588457
theorem B1059007 : Blo 940584 1059007 := bstep (se 1 (by rfl) ⟨794255, by rfl⟩ : syracuseStep 1059007 = 1588511) B1588511
theorem B3222017 : Blo 940584 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B2861639 : Blo 940584 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B99167203 : Blo 940584 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B3222575 : Blo 940584 3222575 := bstep (se 1 (by rfl) ⟨2416931, by rfl⟩ : syracuseStep 3222575 = 4833863) B4833863
theorem B4598831 : Blo 940584 4598831 := bstep (se 1 (by rfl) ⟨3449123, by rfl⟩ : syracuseStep 4598831 = 6898247) B6898247
theorem B15313967 : Blo 940584 15313967 := bstep (se 1 (by rfl) ⟨11485475, by rfl⟩ : syracuseStep 15313967 = 22970951) B22970951
theorem B25800713 : Blo 940584 25800713 := bstep (se 2 (by rfl) ⟨9675267, by rfl⟩ : syracuseStep 25800713 = 19350535) B19350535
theorem B4763771 : Blo 940584 4763771 := bstep (se 1 (by rfl) ⟨3572828, by rfl⟩ : syracuseStep 4763771 = 7145657) B7145657
theorem B14495915 : Blo 940584 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B3584189 : Blo 940584 3584189 := bstep (se 3 (by rfl) ⟨672035, by rfl⟩ : syracuseStep 3584189 = 1344071) B1344071
theorem B1061095 : Blo 940584 1061095 := bstep (se 1 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 1061095 = 1591643) B1591643
theorem B4763933 : Blo 940584 4763933 := bstep (se 3 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 4763933 = 1786475) B1786475
theorem B12104225 : Blo 940584 12104225 := bstep (se 2 (by rfl) ⟨4539084, by rfl⟩ : syracuseStep 12104225 = 9078169) B9078169
theorem B10171169 : Blo 940584 10171169 := bstep (se 2 (by rfl) ⟨3814188, by rfl⟩ : syracuseStep 10171169 = 7628377) B7628377
theorem B1061743 : Blo 940584 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B1815547 : Blo 940584 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B2864339 : Blo 940584 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B1587343 : Blo 940584 1587343 := bstep (se 1 (by rfl) ⟨1190507, by rfl⟩ : syracuseStep 1587343 = 2381015) B2381015
theorem B1194527 : Blo 940584 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B13777447 : Blo 940584 13777447 := bstep (se 1 (by rfl) ⟨10333085, by rfl⟩ : syracuseStep 13777447 = 20666171) B20666171
theorem B1817225 : Blo 940584 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B2014159 : Blo 940584 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B1588295 : Blo 940584 1588295 := bstep (se 1 (by rfl) ⟨1191221, by rfl⟩ : syracuseStep 1588295 = 2382443) B2382443
theorem B4537433 : Blo 940584 4537433 := bstep (se 2 (by rfl) ⟨1701537, by rfl⟩ : syracuseStep 4537433 = 3403075) B3403075
theorem B4766849 : Blo 940584 4766849 := bstep (se 2 (by rfl) ⟨1787568, by rfl⟩ : syracuseStep 4766849 = 3575137) B3575137
theorem B1195231 : Blo 940584 1195231 := bstep (se 1 (by rfl) ⟨896423, by rfl⟩ : syracuseStep 1195231 = 1792847) B1792847
theorem B1588727 : Blo 940584 1588727 := bstep (se 1 (by rfl) ⟨1191545, by rfl⟩ : syracuseStep 1588727 = 2383091) B2383091
theorem B2015047 : Blo 940584 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B4767659 : Blo 940584 4767659 := bstep (se 1 (by rfl) ⟨3575744, by rfl⟩ : syracuseStep 4767659 = 7151489) B7151489
theorem B3228103 : Blo 940584 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B1589753 : Blo 940584 1589753 := bstep (se 2 (by rfl) ⟨596157, by rfl⟩ : syracuseStep 1589753 = 1192315) B1192315
theorem B3228155 : Blo 940584 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B6046271 : Blo 940584 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B1590023 : Blo 940584 1590023 := bstep (se 1 (by rfl) ⟨1192517, by rfl⟩ : syracuseStep 1590023 = 2385035) B2385035
theorem B4768631 : Blo 940584 4768631 := bstep (se 1 (by rfl) ⟨3576473, by rfl⟩ : syracuseStep 4768631 = 7152947) B7152947
theorem B6046987 : Blo 940584 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B3491443 : Blo 940584 3491443 := bstep (se 1 (by rfl) ⟨2618582, by rfl⟩ : syracuseStep 3491443 = 5237165) B5237165
theorem B13780595 : Blo 940584 13780595 := bstep (se 1 (by rfl) ⟨10335446, by rfl⟩ : syracuseStep 13780595 = 20670893) B20670893
theorem B5097113 : Blo 940584 5097113 := bstep (se 2 (by rfl) ⟨1911417, by rfl⟩ : syracuseStep 5097113 = 3822835) B3822835
theorem B4769441 : Blo 940584 4769441 := bstep (se 2 (by rfl) ⟨1788540, by rfl⟩ : syracuseStep 4769441 = 3577081) B3577081
theorem B1591103 : Blo 940584 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B3393359 : Blo 940584 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B1591177 : Blo 940584 1591177 := bstep (se 2 (by rfl) ⟨596691, by rfl⟩ : syracuseStep 1591177 = 1193383) B1193383
theorem B17188795 : Blo 940584 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B2148665 : Blo 940584 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B1591609 : Blo 940584 1591609 := bstep (se 2 (by rfl) ⟨596853, by rfl⟩ : syracuseStep 1591609 = 1193707) B1193707
theorem B5360201 : Blo 940584 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B1591913 : Blo 940584 1591913 := bstep (se 2 (by rfl) ⟨596967, by rfl⟩ : syracuseStep 1591913 = 1193935) B1193935
theorem B6900653 : Blo 940584 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B2116655 : Blo 940584 2116655 := bstep (se 1 (by rfl) ⟨1587491, by rfl⟩ : syracuseStep 2116655 = 3174983) B3174983
theorem B2116943 : Blo 940584 2116943 := bstep (se 1 (by rfl) ⟨1587707, by rfl⟩ : syracuseStep 2116943 = 3175415) B3175415
theorem B5360975 : Blo 940584 5360975 := bstep (se 1 (by rfl) ⟨4020731, by rfl⟩ : syracuseStep 5360975 = 8041463) B8041463
theorem B1592743 : Blo 940584 1592743 := bstep (se 1 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 1592743 = 2389115) B2389115
theorem B2117033 : Blo 940584 2117033 := bstep (se 2 (by rfl) ⟨793887, by rfl⟩ : syracuseStep 2117033 = 1587775) B1587775
theorem B1592905 : Blo 940584 1592905 := bstep (se 2 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 1592905 = 1194679) B1194679
theorem B1592939 : Blo 940584 1592939 := bstep (se 1 (by rfl) ⟨1194704, by rfl⟩ : syracuseStep 1592939 = 2389409) B2389409
theorem B115953443 : Blo 940584 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B1593209 : Blo 940584 1593209 := bstep (se 2 (by rfl) ⟨597453, by rfl⟩ : syracuseStep 1593209 = 1194907) B1194907
theorem B2117519 : Blo 940584 2117519 := bstep (se 1 (by rfl) ⟨1588139, by rfl⟩ : syracuseStep 2117519 = 3176279) B3176279
theorem B36720701 : Blo 940584 36720701 := bstep (se 3 (by rfl) ⟨6885131, by rfl⟩ : syracuseStep 36720701 = 13770263) B13770263
theorem B10178777 : Blo 940584 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B7164125 : Blo 940584 7164125 := bstep (se 3 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 7164125 = 2686547) B2686547
theorem B2118239 : Blo 940584 2118239 := bstep (se 1 (by rfl) ⟨1588679, by rfl⟩ : syracuseStep 2118239 = 3177359) B3177359
theorem B3396343 : Blo 940584 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B3396617 : Blo 940584 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B6444047 : Blo 940584 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B2380873 : Blo 940584 2380873 := bstep (se 2 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 2380873 = 1785655) B1785655
theorem B2381147 : Blo 940584 2381147 := bstep (se 1 (by rfl) ⟨1785860, by rfl⟩ : syracuseStep 2381147 = 3571721) B3571721
theorem B2119067 : Blo 940584 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B2119643 : Blo 940584 2119643 := bstep (se 1 (by rfl) ⟨1589732, by rfl⟩ : syracuseStep 2119643 = 3179465) B3179465
theorem B16078823 : Blo 940584 16078823 := bstep (se 1 (by rfl) ⟨12059117, by rfl⟩ : syracuseStep 16078823 = 24118235) B24118235
theorem B3397727 : Blo 940584 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B2119823 : Blo 940584 2119823 := bstep (se 1 (by rfl) ⟨1589867, by rfl⟩ : syracuseStep 2119823 = 3179735) B3179735
theorem B2119841 : Blo 940584 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B2119913 : Blo 940584 2119913 := bstep (se 2 (by rfl) ⟨794967, by rfl⟩ : syracuseStep 2119913 = 1589935) B1589935
theorem B8149355 : Blo 940584 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B8608123 : Blo 940584 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B5364143 : Blo 940584 5364143 := bstep (se 1 (by rfl) ⟨4023107, by rfl⟩ : syracuseStep 5364143 = 8046215) B8046215
theorem B43506197 : Blo 940584 43506197 := bstep (se 6 (by rfl) ⟨1019676, by rfl⟩ : syracuseStep 43506197 = 2039353) B2039353
theorem B6806065 : Blo 940584 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B2382473 : Blo 940584 2382473 := bstep (se 2 (by rfl) ⟨893427, by rfl⟩ : syracuseStep 2382473 = 1786855) B1786855
theorem B4021073 : Blo 940584 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B940891 : Blo 940584 940891 := bstep (se 1 (by rfl) ⟨705668, by rfl⟩ : syracuseStep 940891 = 1411337) B1411337
theorem B940959 : Blo 940584 940959 := bstep (se 1 (by rfl) ⟨705719, by rfl⟩ : syracuseStep 940959 = 1411439) B1411439
theorem B2382817 : Blo 940584 2382817 := bstep (se 2 (by rfl) ⟨893556, by rfl⟩ : syracuseStep 2382817 = 1787113) B1787113
theorem B941103 : Blo 940584 941103 := bstep (se 1 (by rfl) ⟨705827, by rfl⟩ : syracuseStep 941103 = 1411655) B1411655
theorem B941127 : Blo 940584 941127 := bstep (se 1 (by rfl) ⟨705845, by rfl⟩ : syracuseStep 941127 = 1411691) B1411691
theorem B941279 : Blo 940584 941279 := bstep (se 1 (by rfl) ⟨705959, by rfl⟩ : syracuseStep 941279 = 1411919) B1411919
theorem B941543 : Blo 940584 941543 := bstep (se 1 (by rfl) ⟨706157, by rfl⟩ : syracuseStep 941543 = 1412315) B1412315
theorem B2121191 : Blo 940584 2121191 := bstep (se 1 (by rfl) ⟨1590893, by rfl⟩ : syracuseStep 2121191 = 3181787) B3181787
theorem B941659 : Blo 940584 941659 := bstep (se 1 (by rfl) ⟨706244, by rfl⟩ : syracuseStep 941659 = 1412489) B1412489
theorem B2383607 : Blo 940584 2383607 := bstep (se 1 (by rfl) ⟨1787705, by rfl⟩ : syracuseStep 2383607 = 3575411) B3575411
theorem B941895 : Blo 940584 941895 := bstep (se 1 (by rfl) ⟨706421, by rfl⟩ : syracuseStep 941895 = 1412843) B1412843
theorem B2383739 : Blo 940584 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B942047 : Blo 940584 942047 := bstep (se 1 (by rfl) ⟨706535, by rfl⟩ : syracuseStep 942047 = 1413071) B1413071
theorem B2121767 : Blo 940584 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B2121947 : Blo 940584 2121947 := bstep (se 1 (by rfl) ⟨1591460, by rfl⟩ : syracuseStep 2121947 = 3182921) B3182921
theorem B942311 : Blo 940584 942311 := bstep (se 1 (by rfl) ⟨706733, by rfl⟩ : syracuseStep 942311 = 1413467) B1413467
theorem B2679065 : Blo 940584 2679065 := bstep (se 2 (by rfl) ⟨1004649, by rfl⟩ : syracuseStep 2679065 = 2009299) B2009299
theorem B2384225 : Blo 940584 2384225 := bstep (se 2 (by rfl) ⟨894084, by rfl⟩ : syracuseStep 2384225 = 1788169) B1788169
theorem B942463 : Blo 940584 942463 := bstep (se 1 (by rfl) ⟨706847, by rfl⟩ : syracuseStep 942463 = 1413695) B1413695
theorem B6807995 : Blo 940584 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B942543 : Blo 940584 942543 := bstep (se 1 (by rfl) ⟨706907, by rfl⟩ : syracuseStep 942543 = 1413815) B1413815
theorem B2122217 : Blo 940584 2122217 := bstep (se 2 (by rfl) ⟨795831, by rfl⟩ : syracuseStep 2122217 = 1591663) B1591663
theorem B942695 : Blo 940584 942695 := bstep (se 1 (by rfl) ⟨707021, by rfl⟩ : syracuseStep 942695 = 1414043) B1414043
theorem B2122505 : Blo 940584 2122505 := bstep (se 2 (by rfl) ⟨795939, by rfl⟩ : syracuseStep 2122505 = 1591879) B1591879
theorem B942959 : Blo 940584 942959 := bstep (se 1 (by rfl) ⟨707219, by rfl⟩ : syracuseStep 942959 = 1414439) B1414439
theorem B943015 : Blo 940584 943015 := bstep (se 1 (by rfl) ⟨707261, by rfl⟩ : syracuseStep 943015 = 1414523) B1414523
theorem B943099 : Blo 940584 943099 := bstep (se 1 (by rfl) ⟨707324, by rfl⟩ : syracuseStep 943099 = 1414649) B1414649
theorem B943167 : Blo 940584 943167 := bstep (se 1 (by rfl) ⟨707375, by rfl⟩ : syracuseStep 943167 = 1414751) B1414751
theorem B943311 : Blo 940584 943311 := bstep (se 1 (by rfl) ⟨707483, by rfl⟩ : syracuseStep 943311 = 1414967) B1414967
theorem B11461931 : Blo 940584 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B2123081 : Blo 940584 2123081 := bstep (se 2 (by rfl) ⟨796155, by rfl⟩ : syracuseStep 2123081 = 1592311) B1592311
theorem B943515 : Blo 940584 943515 := bstep (se 1 (by rfl) ⟨707636, by rfl⟩ : syracuseStep 943515 = 1415273) B1415273
theorem B25748941 : Blo 940584 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B943727 : Blo 940584 943727 := bstep (se 1 (by rfl) ⟨707795, by rfl⟩ : syracuseStep 943727 = 1415591) B1415591
theorem B943783 : Blo 940584 943783 := bstep (se 1 (by rfl) ⟨707837, by rfl⟩ : syracuseStep 943783 = 1415675) B1415675
theorem B943867 : Blo 940584 943867 := bstep (se 1 (by rfl) ⟨707900, by rfl⟩ : syracuseStep 943867 = 1415801) B1415801
theorem B943903 : Blo 940584 943903 := bstep (se 1 (by rfl) ⟨707927, by rfl⟩ : syracuseStep 943903 = 1415855) B1415855
theorem B943935 : Blo 940584 943935 := bstep (se 1 (by rfl) ⟨707951, by rfl⟩ : syracuseStep 943935 = 1415903) B1415903
theorem B944111 : Blo 940584 944111 := bstep (se 1 (by rfl) ⟨708083, by rfl⟩ : syracuseStep 944111 = 1416167) B1416167
theorem B1075295 : Blo 940584 1075295 := bstep (se 1 (by rfl) ⟨806471, by rfl⟩ : syracuseStep 1075295 = 1612943) B1612943
theorem B944283 : Blo 940584 944283 := bstep (se 1 (by rfl) ⟨708212, by rfl⟩ : syracuseStep 944283 = 1416425) B1416425
theorem B944319 : Blo 940584 944319 := bstep (se 1 (by rfl) ⟨708239, by rfl⟩ : syracuseStep 944319 = 1416479) B1416479
theorem B2386169 : Blo 940584 2386169 := bstep (se 2 (by rfl) ⟨894813, by rfl⟩ : syracuseStep 2386169 = 1789627) B1789627
theorem B2124071 : Blo 940584 2124071 := bstep (se 1 (by rfl) ⟨1593053, by rfl⟩ : syracuseStep 2124071 = 3186107) B3186107
theorem B944431 : Blo 940584 944431 := bstep (se 1 (by rfl) ⟨708323, by rfl⟩ : syracuseStep 944431 = 1416647) B1416647
theorem B2124089 : Blo 940584 2124089 := bstep (se 2 (by rfl) ⟨796533, by rfl⟩ : syracuseStep 2124089 = 1593067) B1593067
theorem B7629349 : Blo 940584 7629349 := bstep (se 4 (by rfl) ⟨715251, by rfl⟩ : syracuseStep 7629349 = 1430503) B1430503
theorem B1698409 : Blo 940584 1698409 := bstep (se 2 (by rfl) ⟨636903, by rfl⟩ : syracuseStep 1698409 = 1273807) B1273807
theorem B6974351 : Blo 940584 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B55799563 : Blo 940584 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B4026131 : Blo 940584 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B51572537 : Blo 940584 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B7171901 : Blo 940584 7171901 := bstep (se 3 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 7171901 = 2689463) B2689463
theorem B2944907 : Blo 940584 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B10744001 : Blo 940584 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B3174767 : Blo 940584 3174767 := bstep (se 1 (by rfl) ⟨2381075, by rfl⟩ : syracuseStep 3174767 = 4762151) B4762151
theorem B1339897 : Blo 940584 1339897 := bstep (se 2 (by rfl) ⟨502461, by rfl⟩ : syracuseStep 1339897 = 1004923) B1004923
theorem B2683655 : Blo 940584 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B1700615 : Blo 940584 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B2388761 : Blo 940584 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B2290963 : Blo 940584 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B2684315 : Blo 940584 2684315 := bstep (se 1 (by rfl) ⟨2013236, by rfl⟩ : syracuseStep 2684315 = 4026473) B4026473
theorem B3176171 : Blo 940584 3176171 := bstep (se 1 (by rfl) ⟨2382128, by rfl⟩ : syracuseStep 3176171 = 4764257) B4764257
theorem B10319633 : Blo 940584 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B13596497 : Blo 940584 13596497 := bstep (se 2 (by rfl) ⟨5098686, by rfl⟩ : syracuseStep 13596497 = 10197373) B10197373
theorem B1701769 : Blo 940584 1701769 := bstep (se 2 (by rfl) ⟨638163, by rfl⟩ : syracuseStep 1701769 = 1276327) B1276327
theorem B3176441 : Blo 940584 3176441 := bstep (se 2 (by rfl) ⟨1191165, by rfl⟩ : syracuseStep 3176441 = 2382331) B2382331
theorem B3176603 : Blo 940584 3176603 := bstep (se 1 (by rfl) ⟨2382452, by rfl⟩ : syracuseStep 3176603 = 4764905) B4764905
theorem B2685089 : Blo 940584 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B2390249 : Blo 940584 2390249 := bstep (se 2 (by rfl) ⟨896343, by rfl⟩ : syracuseStep 2390249 = 1792687) B1792687
theorem B3176711 : Blo 940584 3176711 := bstep (se 1 (by rfl) ⟨2382533, by rfl⟩ : syracuseStep 3176711 = 4765067) B4765067
theorem B2488583 : Blo 940584 2488583 := bstep (se 1 (by rfl) ⟨1866437, by rfl⟩ : syracuseStep 2488583 = 3732875) B3732875
theorem B2423047 : Blo 940584 2423047 := bstep (se 1 (by rfl) ⟨1817285, by rfl⟩ : syracuseStep 2423047 = 3634571) B3634571
theorem B6781295 : Blo 940584 6781295 := bstep (se 1 (by rfl) ⟨5085971, by rfl⟩ : syracuseStep 6781295 = 10171943) B10171943
theorem B16087571 : Blo 940584 16087571 := bstep (se 1 (by rfl) ⟨12065678, by rfl⟩ : syracuseStep 16087571 = 24131357) B24131357
theorem B5372639 : Blo 940584 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B2390867 : Blo 940584 2390867 := bstep (se 1 (by rfl) ⟨1793150, by rfl⟩ : syracuseStep 2390867 = 3586301) B3586301
theorem B1342585 : Blo 940584 1342585 := bstep (se 2 (by rfl) ⟨503469, by rfl⟩ : syracuseStep 1342585 = 1006939) B1006939
theorem B2686081 : Blo 940584 2686081 := bstep (se 2 (by rfl) ⟨1007280, by rfl⟩ : syracuseStep 2686081 = 2014561) B2014561
theorem B3177737 : Blo 940584 3177737 := bstep (se 2 (by rfl) ⟨1191651, by rfl⟩ : syracuseStep 3177737 = 2383303) B2383303
theorem B6454559 : Blo 940584 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B6028739 : Blo 940584 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B5799737 : Blo 940584 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B278822807 : Blo 940584 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B4030847 : Blo 940584 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B3179087 : Blo 940584 3179087 := bstep (se 1 (by rfl) ⟨2384315, by rfl⟩ : syracuseStep 3179087 = 4768631) B4768631
theorem B3179627 : Blo 940584 3179627 := bstep (se 1 (by rfl) ⟨2384720, by rfl⟩ : syracuseStep 3179627 = 4769441) B4769441
theorem B2262239 : Blo 940584 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B8062649 : Blo 940584 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B3573467 : Blo 940584 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B1411103 : Blo 940584 1411103 := bstep (se 1 (by rfl) ⟨1058327, by rfl⟩ : syracuseStep 1411103 = 2116655) B2116655
theorem B1411295 : Blo 940584 1411295 := bstep (se 1 (by rfl) ⟨1058471, by rfl⟩ : syracuseStep 1411295 = 2116943) B2116943
theorem B3573983 : Blo 940584 3573983 := bstep (se 1 (by rfl) ⟨2680487, by rfl⟩ : syracuseStep 3573983 = 5360975) B5360975
theorem B1411355 : Blo 940584 1411355 := bstep (se 1 (by rfl) ⟨1058516, by rfl⟩ : syracuseStep 1411355 = 2117033) B2117033
theorem B77302295 : Blo 940584 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B1411679 : Blo 940584 1411679 := bstep (se 1 (by rfl) ⟨1058759, by rfl⟩ : syracuseStep 1411679 = 2117519) B2117519
theorem B24480467 : Blo 940584 24480467 := bstep (se 1 (by rfl) ⟨18360350, by rfl⟩ : syracuseStep 24480467 = 36720701) B36720701
theorem B6785851 : Blo 940584 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B1411961 : Blo 940584 1411961 := bstep (se 2 (by rfl) ⟨529485, by rfl⟩ : syracuseStep 1411961 = 1058971) B1058971
theorem B1412009 : Blo 940584 1412009 := bstep (se 2 (by rfl) ⟨529503, by rfl⟩ : syracuseStep 1412009 = 1059007) B1059007
theorem B1412159 : Blo 940584 1412159 := bstep (se 1 (by rfl) ⟨1059119, by rfl⟩ : syracuseStep 1412159 = 2118239) B2118239
theorem B4525399 : Blo 940584 4525399 := bstep (se 1 (by rfl) ⟨3394049, by rfl⟩ : syracuseStep 4525399 = 6788099) B6788099
theorem B2264411 : Blo 940584 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B2264545 : Blo 940584 2264545 := bstep (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) B1698409
theorem B3018215 : Blo 940584 3018215 := bstep (se 1 (by rfl) ⟨2263661, by rfl⟩ : syracuseStep 3018215 = 4527323) B4527323
theorem B1412711 : Blo 940584 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B7147115 : Blo 940584 7147115 := bstep (se 1 (by rfl) ⟨5360336, by rfl⟩ : syracuseStep 7147115 = 10720673) B10720673
theorem B132222937 : Blo 940584 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B5378015 : Blo 940584 5378015 := bstep (se 1 (by rfl) ⟨4033511, by rfl⟩ : syracuseStep 5378015 = 8067023) B8067023
theorem B1413095 : Blo 940584 1413095 := bstep (se 1 (by rfl) ⟨1059821, by rfl⟩ : syracuseStep 1413095 = 2119643) B2119643
theorem B10719215 : Blo 940584 10719215 := bstep (se 1 (by rfl) ⟨8039411, by rfl⟩ : syracuseStep 10719215 = 16078823) B16078823
theorem B1413215 : Blo 940584 1413215 := bstep (se 1 (by rfl) ⟨1059911, by rfl⟩ : syracuseStep 1413215 = 2119823) B2119823
theorem B1413227 : Blo 940584 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B1413275 : Blo 940584 1413275 := bstep (se 1 (by rfl) ⟨1059956, by rfl⟩ : syracuseStep 1413275 = 2119913) B2119913
theorem B3576095 : Blo 940584 3576095 := bstep (se 1 (by rfl) ⟨2682071, by rfl⟩ : syracuseStep 3576095 = 5364143) B5364143
theorem B29004131 : Blo 940584 29004131 := bstep (se 1 (by rfl) ⟨21753098, by rfl⟩ : syracuseStep 29004131 = 43506197) B43506197
theorem B7148087 : Blo 940584 7148087 := bstep (se 1 (by rfl) ⟨5361065, by rfl⟩ : syracuseStep 7148087 = 10722131) B10722131
theorem B1414127 : Blo 940584 1414127 := bstep (se 1 (by rfl) ⟨1060595, by rfl⟩ : syracuseStep 1414127 = 2121191) B2121191
theorem B1414511 : Blo 940584 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B4527535 : Blo 940584 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B1414631 : Blo 940584 1414631 := bstep (se 1 (by rfl) ⟨1060973, by rfl⟩ : syracuseStep 1414631 = 2121947) B2121947
theorem B1414793 : Blo 940584 1414793 := bstep (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) B1061095
theorem B1414811 : Blo 940584 1414811 := bstep (se 1 (by rfl) ⟨1061108, by rfl⟩ : syracuseStep 1414811 = 2122217) B2122217
theorem B1415003 : Blo 940584 1415003 := bstep (se 1 (by rfl) ⟨1061252, by rfl⟩ : syracuseStep 1415003 = 2122505) B2122505
theorem B7641287 : Blo 940584 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B1415387 : Blo 940584 1415387 := bstep (se 1 (by rfl) ⟨1061540, by rfl⟩ : syracuseStep 1415387 = 2123081) B2123081
theorem B4528457 : Blo 940584 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B1415657 : Blo 940584 1415657 := bstep (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) B1061743
theorem B3185405 : Blo 940584 3185405 := bstep (se 3 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 3185405 = 1194527) B1194527
theorem B1416047 : Blo 940584 1416047 := bstep (se 1 (by rfl) ⟨1062035, by rfl⟩ : syracuseStep 1416047 = 2124071) B2124071
theorem B1416059 : Blo 940584 1416059 := bstep (se 1 (by rfl) ⟨1062044, by rfl⟩ : syracuseStep 1416059 = 2124089) B2124089
theorem B3054617 : Blo 940584 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B1907759 : Blo 940584 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B3022393 : Blo 940584 3022393 := bstep (se 2 (by rfl) ⟨1133397, by rfl⟩ : syracuseStep 3022393 = 2266795) B2266795
theorem B10755665 : Blo 940584 10755665 := bstep (se 2 (by rfl) ⟨4033374, by rfl⟩ : syracuseStep 10755665 = 8066749) B8066749
theorem B2269025 : Blo 940584 2269025 := bstep (se 2 (by rfl) ⟨850884, by rfl⟩ : syracuseStep 2269025 = 1701769) B1701769
theorem B34381691 : Blo 940584 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B8069483 : Blo 940584 8069483 := bstep (se 1 (by rfl) ⟨6052112, by rfl⟩ : syracuseStep 8069483 = 12104225) B12104225
theorem B11477497 : Blo 940584 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B18621029 : Blo 940584 18621029 := bstep (se 4 (by rfl) ⟨1745721, by rfl⟩ : syracuseStep 18621029 = 3491443) B3491443
theorem B1909559 : Blo 940584 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B3581441 : Blo 940584 3581441 := bstep (se 2 (by rfl) ⟨1343040, by rfl⟩ : syracuseStep 3581441 = 2686081) B2686081
theorem B10725047 : Blo 940584 10725047 := bstep (se 1 (by rfl) ⟨8043785, by rfl⟩ : syracuseStep 10725047 = 16087571) B16087571
theorem B3581759 : Blo 940584 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B1058863 : Blo 940584 1058863 := bstep (se 1 (by rfl) ⟨794147, by rfl⟩ : syracuseStep 1058863 = 1588295) B1588295
theorem B3024955 : Blo 940584 3024955 := bstep (se 1 (by rfl) ⟨2268716, by rfl⟩ : syracuseStep 3024955 = 4537433) B4537433
theorem B4303039 : Blo 940584 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B1059151 : Blo 940584 1059151 := bstep (se 1 (by rfl) ⟨794363, by rfl⟩ : syracuseStep 1059151 = 1588727) B1588727
theorem B1059835 : Blo 940584 1059835 := bstep (se 1 (by rfl) ⟨794876, by rfl⟩ : syracuseStep 1059835 = 1589753) B1589753
theorem B1060015 : Blo 940584 1060015 := bstep (se 1 (by rfl) ⟨795011, by rfl⟩ : syracuseStep 1060015 = 1590023) B1590023
theorem B4304137 : Blo 940584 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B9187063 : Blo 940584 9187063 := bstep (se 1 (by rfl) ⟨6890297, by rfl⟩ : syracuseStep 9187063 = 13780595) B13780595
theorem B1060735 : Blo 940584 1060735 := bstep (se 1 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 1060735 = 1591103) B1591103
theorem B1061275 : Blo 940584 1061275 := bstep (se 1 (by rfl) ⟨795956, by rfl⟩ : syracuseStep 1061275 = 1591913) B1591913
theorem B4600435 : Blo 940584 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B4534973 : Blo 940584 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B1061959 : Blo 940584 1061959 := bstep (se 1 (by rfl) ⟨796469, by rfl⟩ : syracuseStep 1061959 = 1592939) B1592939
theorem B22918393 : Blo 940584 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B1062139 : Blo 940584 1062139 := bstep (se 1 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 1062139 = 1593209) B1593209
theorem B17184125 : Blo 940584 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B10172465 : Blo 940584 10172465 := bstep (se 2 (by rfl) ⟨3814674, by rfl⟩ : syracuseStep 10172465 = 7629349) B7629349
theorem B1587431 : Blo 940584 1587431 := bstep (se 1 (by rfl) ⟨1190573, by rfl⟩ : syracuseStep 1587431 = 2381147) B2381147
theorem B14531075 : Blo 940584 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B1588315 : Blo 940584 1588315 := bstep (se 1 (by rfl) ⟨1191236, by rfl⟩ : syracuseStep 1588315 = 2382473) B2382473
theorem B74399417 : Blo 940584 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B1589071 : Blo 940584 1589071 := bstep (se 1 (by rfl) ⟨1191803, by rfl⟩ : syracuseStep 1589071 = 2383607) B2383607
theorem B1589159 : Blo 940584 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B1786043 : Blo 940584 1786043 := bstep (se 1 (by rfl) ⟨1339532, by rfl⟩ : syracuseStep 1786043 = 2679065) B2679065
theorem B1589483 : Blo 940584 1589483 := bstep (se 1 (by rfl) ⟨1192112, by rfl⟩ : syracuseStep 1589483 = 2384225) B2384225
theorem B9060605 : Blo 940584 9060605 := bstep (se 3 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 9060605 = 3397727) B3397727
theorem B2867453 : Blo 940584 2867453 := bstep (se 3 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 2867453 = 1075295) B1075295
theorem B4538663 : Blo 940584 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B7160237 : Blo 940584 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B1786529 : Blo 940584 1786529 := bstep (se 2 (by rfl) ⟨669948, by rfl⟩ : syracuseStep 1786529 = 1339897) B1339897
theorem B5096783 : Blo 940584 5096783 := bstep (se 1 (by rfl) ⟨3822587, by rfl⟩ : syracuseStep 5096783 = 7645175) B7645175
theorem B1590779 : Blo 940584 1590779 := bstep (se 1 (by rfl) ⟨1193084, by rfl⟩ : syracuseStep 1590779 = 2386169) B2386169
theorem B2148011 : Blo 940584 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B2148383 : Blo 940584 2148383 := bstep (se 1 (by rfl) ⟨1611287, by rfl⟩ : syracuseStep 2148383 = 3222575) B3222575
theorem B3065887 : Blo 940584 3065887 := bstep (se 1 (by rfl) ⟨2299415, by rfl⟩ : syracuseStep 3065887 = 4598831) B4598831
theorem B10209311 : Blo 940584 10209311 := bstep (se 1 (by rfl) ⟨7656983, by rfl⟩ : syracuseStep 10209311 = 15313967) B15313967
theorem B7162667 : Blo 940584 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B2116457 : Blo 940584 2116457 := bstep (se 2 (by rfl) ⟨793671, by rfl⟩ : syracuseStep 2116457 = 1587343) B1587343
theorem B2116511 : Blo 940584 2116511 := bstep (se 1 (by rfl) ⟨1587383, by rfl⟩ : syracuseStep 2116511 = 3174767) B3174767
theorem B3230729 : Blo 940584 3230729 := bstep (se 2 (by rfl) ⟨1211523, by rfl⟩ : syracuseStep 3230729 = 2423047) B2423047
theorem B1789103 : Blo 940584 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B1592507 : Blo 940584 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B18369929 : Blo 940584 18369929 := bstep (se 2 (by rfl) ⟨6888723, by rfl⟩ : syracuseStep 18369929 = 13777447) B13777447
theorem B1789543 : Blo 940584 1789543 := bstep (se 1 (by rfl) ⟨1342157, by rfl⟩ : syracuseStep 1789543 = 2684315) B2684315
theorem B2117447 : Blo 940584 2117447 := bstep (se 1 (by rfl) ⟨1588085, by rfl⟩ : syracuseStep 2117447 = 3176171) B3176171
theorem B9064331 : Blo 940584 9064331 := bstep (se 1 (by rfl) ⟨6798248, by rfl⟩ : syracuseStep 9064331 = 13596497) B13596497
theorem B2117627 : Blo 940584 2117627 := bstep (se 1 (by rfl) ⟨1588220, by rfl⟩ : syracuseStep 2117627 = 3176441) B3176441
theorem B2117735 : Blo 940584 2117735 := bstep (se 1 (by rfl) ⟨1588301, by rfl⟩ : syracuseStep 2117735 = 3176603) B3176603
theorem B1593499 : Blo 940584 1593499 := bstep (se 1 (by rfl) ⟨1195124, by rfl⟩ : syracuseStep 1593499 = 2390249) B2390249
theorem B1790113 : Blo 940584 1790113 := bstep (se 2 (by rfl) ⟨671292, by rfl⟩ : syracuseStep 1790113 = 1342585) B1342585
theorem B2117807 : Blo 940584 2117807 := bstep (se 1 (by rfl) ⟨1588355, by rfl⟩ : syracuseStep 2117807 = 3176711) B3176711
theorem B1659055 : Blo 940584 1659055 := bstep (se 1 (by rfl) ⟨1244291, by rfl⟩ : syracuseStep 1659055 = 2488583) B2488583
theorem B1593641 : Blo 940584 1593641 := bstep (se 2 (by rfl) ⟨597615, by rfl⟩ : syracuseStep 1593641 = 1195231) B1195231
theorem B1593911 : Blo 940584 1593911 := bstep (se 1 (by rfl) ⟨1195433, by rfl⟩ : syracuseStep 1593911 = 2390867) B2390867
theorem B2118491 : Blo 940584 2118491 := bstep (se 1 (by rfl) ⟨1588868, by rfl⟩ : syracuseStep 2118491 = 3177737) B3177737
theorem B4019159 : Blo 940584 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B185881871 : Blo 940584 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B2119247 : Blo 940584 2119247 := bstep (se 1 (by rfl) ⟨1589435, by rfl⟩ : syracuseStep 2119247 = 3178871) B3178871
theorem B2152103 : Blo 940584 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B8607827 : Blo 940584 8607827 := bstep (se 1 (by rfl) ⟨6455870, by rfl⟩ : syracuseStep 8607827 = 12911741) B12911741
theorem B13588651 : Blo 940584 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B9066755 : Blo 940584 9066755 := bstep (se 1 (by rfl) ⟨6800066, by rfl⟩ : syracuseStep 9066755 = 13600133) B13600133
theorem B2119967 : Blo 940584 2119967 := bstep (se 1 (by rfl) ⟨1589975, by rfl⟩ : syracuseStep 2119967 = 3179951) B3179951
theorem B3398075 : Blo 940584 3398075 := bstep (se 1 (by rfl) ⟨2548556, by rfl⟩ : syracuseStep 3398075 = 5097113) B5097113
theorem B2120219 : Blo 940584 2120219 := bstep (se 1 (by rfl) ⟨1590164, by rfl⟩ : syracuseStep 2120219 = 3180329) B3180329
theorem B940635 : Blo 940584 940635 := bstep (se 1 (by rfl) ⟨705476, by rfl⟩ : syracuseStep 940635 = 1410953) B1410953
theorem B940703 : Blo 940584 940703 := bstep (se 1 (by rfl) ⟨705527, by rfl⟩ : syracuseStep 940703 = 1411055) B1411055
theorem B940871 : Blo 940584 940871 := bstep (se 1 (by rfl) ⟨705653, by rfl⟩ : syracuseStep 940871 = 1411307) B1411307
theorem B940911 : Blo 940584 940911 := bstep (se 1 (by rfl) ⟨705683, by rfl⟩ : syracuseStep 940911 = 1411367) B1411367
theorem B940967 : Blo 940584 940967 := bstep (se 1 (by rfl) ⟨705725, by rfl⟩ : syracuseStep 940967 = 1411451) B1411451
theorem B18111437 : Blo 940584 18111437 := bstep (se 3 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 18111437 = 6791789) B6791789
theorem B941147 : Blo 940584 941147 := bstep (se 1 (by rfl) ⟨705860, by rfl⟩ : syracuseStep 941147 = 1411721) B1411721
theorem B941263 : Blo 940584 941263 := bstep (se 1 (by rfl) ⟨705947, by rfl⟩ : syracuseStep 941263 = 1411895) B1411895
theorem B941287 : Blo 940584 941287 := bstep (se 1 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 941287 = 1411931) B1411931
theorem B34331921 : Blo 940584 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B941383 : Blo 940584 941383 := bstep (se 1 (by rfl) ⟨706037, by rfl⟩ : syracuseStep 941383 = 1412075) B1412075
theorem B4775273 : Blo 940584 4775273 := bstep (se 2 (by rfl) ⟨1790727, by rfl⟩ : syracuseStep 4775273 = 3581455) B3581455
theorem B941519 : Blo 940584 941519 := bstep (se 1 (by rfl) ⟨706139, by rfl⟩ : syracuseStep 941519 = 1412279) B1412279
theorem B941679 : Blo 940584 941679 := bstep (se 1 (by rfl) ⟨706259, by rfl⟩ : syracuseStep 941679 = 1412519) B1412519
theorem B941735 : Blo 940584 941735 := bstep (se 1 (by rfl) ⟨706301, by rfl⟩ : syracuseStep 941735 = 1412603) B1412603
theorem B941799 : Blo 940584 941799 := bstep (se 1 (by rfl) ⟨706349, by rfl⟩ : syracuseStep 941799 = 1412699) B1412699
theorem B941855 : Blo 940584 941855 := bstep (se 1 (by rfl) ⟨706391, by rfl⟩ : syracuseStep 941855 = 1412783) B1412783
theorem B8609579 : Blo 940584 8609579 := bstep (se 1 (by rfl) ⟨6457184, by rfl⟩ : syracuseStep 8609579 = 12914369) B12914369
theorem B2121569 : Blo 940584 2121569 := bstep (se 2 (by rfl) ⟨795588, by rfl⟩ : syracuseStep 2121569 = 1591177) B1591177
theorem B941935 : Blo 940584 941935 := bstep (se 1 (by rfl) ⟨706451, by rfl⟩ : syracuseStep 941935 = 1412903) B1412903
theorem B941991 : Blo 940584 941991 := bstep (se 1 (by rfl) ⟨706493, by rfl⟩ : syracuseStep 941991 = 1412987) B1412987
theorem B2121695 : Blo 940584 2121695 := bstep (se 1 (by rfl) ⟨1591271, by rfl⟩ : syracuseStep 2121695 = 3182543) B3182543
theorem B4776083 : Blo 940584 4776083 := bstep (se 1 (by rfl) ⟨3582062, by rfl⟩ : syracuseStep 4776083 = 7164125) B7164125
theorem B942271 : Blo 940584 942271 := bstep (se 1 (by rfl) ⟨706703, by rfl⟩ : syracuseStep 942271 = 1413407) B1413407
theorem B942287 : Blo 940584 942287 := bstep (se 1 (by rfl) ⟨706715, by rfl⟩ : syracuseStep 942287 = 1413431) B1413431
theorem B942335 : Blo 940584 942335 := bstep (se 1 (by rfl) ⟨706751, by rfl⟩ : syracuseStep 942335 = 1413503) B1413503
theorem B2121983 : Blo 940584 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B942383 : Blo 940584 942383 := bstep (se 1 (by rfl) ⟨706787, by rfl⟩ : syracuseStep 942383 = 1413575) B1413575
theorem B2122145 : Blo 940584 2122145 := bstep (se 2 (by rfl) ⟨795804, by rfl⟩ : syracuseStep 2122145 = 1591609) B1591609
theorem B942619 : Blo 940584 942619 := bstep (se 1 (by rfl) ⟨706964, by rfl⟩ : syracuseStep 942619 = 1413929) B1413929
theorem B942623 : Blo 940584 942623 := bstep (se 1 (by rfl) ⟨706967, by rfl⟩ : syracuseStep 942623 = 1413935) B1413935
theorem B942703 : Blo 940584 942703 := bstep (se 1 (by rfl) ⟨707027, by rfl⟩ : syracuseStep 942703 = 1414055) B1414055
theorem B942759 : Blo 940584 942759 := bstep (se 1 (by rfl) ⟨707069, by rfl⟩ : syracuseStep 942759 = 1414139) B1414139
theorem B942799 : Blo 940584 942799 := bstep (se 1 (by rfl) ⟨707099, by rfl⟩ : syracuseStep 942799 = 1414199) B1414199
theorem B942879 : Blo 940584 942879 := bstep (se 1 (by rfl) ⟨707159, by rfl⟩ : syracuseStep 942879 = 1414319) B1414319
theorem B943151 : Blo 940584 943151 := bstep (se 1 (by rfl) ⟨707363, by rfl⟩ : syracuseStep 943151 = 1414727) B1414727
theorem B943215 : Blo 940584 943215 := bstep (se 1 (by rfl) ⟨707411, by rfl⟩ : syracuseStep 943215 = 1414823) B1414823
theorem B943271 : Blo 940584 943271 := bstep (se 1 (by rfl) ⟨707453, by rfl⟩ : syracuseStep 943271 = 1414907) B1414907
theorem B2122919 : Blo 940584 2122919 := bstep (se 1 (by rfl) ⟨1592189, by rfl⟩ : syracuseStep 2122919 = 3184379) B3184379
theorem B943295 : Blo 940584 943295 := bstep (se 1 (by rfl) ⟨707471, by rfl⟩ : syracuseStep 943295 = 1414943) B1414943
theorem B943327 : Blo 940584 943327 := bstep (se 1 (by rfl) ⟨707495, by rfl⟩ : syracuseStep 943327 = 1414991) B1414991
theorem B2123027 : Blo 940584 2123027 := bstep (se 1 (by rfl) ⟨1592270, by rfl⟩ : syracuseStep 2123027 = 3184541) B3184541
theorem B943407 : Blo 940584 943407 := bstep (se 1 (by rfl) ⟨707555, by rfl⟩ : syracuseStep 943407 = 1415111) B1415111
theorem B943643 : Blo 940584 943643 := bstep (se 1 (by rfl) ⟨707732, by rfl⟩ : syracuseStep 943643 = 1415465) B1415465
theorem B943647 : Blo 940584 943647 := bstep (se 1 (by rfl) ⟨707735, by rfl⟩ : syracuseStep 943647 = 1415471) B1415471
theorem B15492653 : Blo 940584 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B5432903 : Blo 940584 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B156984965 : Blo 940584 156984965 := bstep (se 4 (by rfl) ⟨14717340, by rfl⟩ : syracuseStep 156984965 = 29434681) B29434681
theorem B943807 : Blo 940584 943807 := bstep (se 1 (by rfl) ⟨707855, by rfl⟩ : syracuseStep 943807 = 1415711) B1415711
theorem B2385683 : Blo 940584 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B2680715 : Blo 940584 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B2123657 : Blo 940584 2123657 := bstep (se 2 (by rfl) ⟨796371, by rfl⟩ : syracuseStep 2123657 = 1592743) B1592743
theorem B2123675 : Blo 940584 2123675 := bstep (se 1 (by rfl) ⟨1592756, by rfl⟩ : syracuseStep 2123675 = 3185513) B3185513
theorem B7628701 : Blo 940584 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B7169957 : Blo 940584 7169957 := bstep (se 4 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 7169957 = 1344367) B1344367
theorem B2123711 : Blo 940584 2123711 := bstep (se 1 (by rfl) ⟨1592783, by rfl⟩ : syracuseStep 2123711 = 3185567) B3185567
theorem B944063 : Blo 940584 944063 := bstep (se 1 (by rfl) ⟨708047, by rfl⟩ : syracuseStep 944063 = 1416095) B1416095
theorem B944095 : Blo 940584 944095 := bstep (se 1 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 944095 = 1416143) B1416143
theorem B944155 : Blo 940584 944155 := bstep (se 1 (by rfl) ⟨708116, by rfl⟩ : syracuseStep 944155 = 1416233) B1416233
theorem B944159 : Blo 940584 944159 := bstep (se 1 (by rfl) ⟨708119, by rfl⟩ : syracuseStep 944159 = 1416239) B1416239
theorem B944175 : Blo 940584 944175 := bstep (se 1 (by rfl) ⟨708131, by rfl⟩ : syracuseStep 944175 = 1416263) B1416263
theorem B8611919 : Blo 940584 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B2123873 : Blo 940584 2123873 := bstep (se 2 (by rfl) ⟨796452, by rfl⟩ : syracuseStep 2123873 = 1592905) B1592905
theorem B944351 : Blo 940584 944351 := bstep (se 1 (by rfl) ⟨708263, by rfl⟩ : syracuseStep 944351 = 1416527) B1416527
theorem B944411 : Blo 940584 944411 := bstep (se 1 (by rfl) ⟨708308, by rfl⟩ : syracuseStep 944411 = 1416617) B1416617
theorem B944511 : Blo 940584 944511 := bstep (se 1 (by rfl) ⟨708383, by rfl⟩ : syracuseStep 944511 = 1416767) B1416767
theorem B7171415 : Blo 940584 7171415 := bstep (se 1 (by rfl) ⟨5378561, by rfl⟩ : syracuseStep 7171415 = 10757123) B10757123
theorem B2125223 : Blo 940584 2125223 := bstep (se 1 (by rfl) ⟨1593917, by rfl⟩ : syracuseStep 2125223 = 3187835) B3187835
theorem B5729773 : Blo 940584 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B6450947 : Blo 940584 6450947 := bstep (se 1 (by rfl) ⟨4838210, by rfl⟩ : syracuseStep 6450947 = 9676421) B9676421
theorem B14708567 : Blo 940584 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B4026199 : Blo 940584 4026199 := bstep (se 1 (by rfl) ⟨3019649, by rfl⟩ : syracuseStep 4026199 = 6039299) B6039299
theorem B2420729 : Blo 940584 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B3174497 : Blo 940584 3174497 := bstep (se 2 (by rfl) ⟨1190436, by rfl⟩ : syracuseStep 3174497 = 2380873) B2380873
theorem B4649567 : Blo 940584 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B3633929 : Blo 940584 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B2684087 : Blo 940584 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B4781267 : Blo 940584 4781267 := bstep (se 1 (by rfl) ⟨3585950, by rfl⟩ : syracuseStep 4781267 = 7171901) B7171901
theorem B1963271 : Blo 940584 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B17200475 : Blo 940584 17200475 := bstep (se 1 (by rfl) ⟨12900356, by rfl⟩ : syracuseStep 17200475 = 25800713) B25800713
theorem B3175847 : Blo 940584 3175847 := bstep (se 1 (by rfl) ⟨2381885, by rfl⟩ : syracuseStep 3175847 = 4763771) B4763771
theorem B9663943 : Blo 940584 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B2389459 : Blo 940584 2389459 := bstep (se 1 (by rfl) ⟨1792094, by rfl⟩ : syracuseStep 2389459 = 3584189) B3584189
theorem B3175955 : Blo 940584 3175955 := bstep (se 1 (by rfl) ⟨2381966, by rfl⟩ : syracuseStep 3175955 = 4763933) B4763933
theorem B6780779 : Blo 940584 6780779 := bstep (se 1 (by rfl) ⟨5085584, by rfl⟩ : syracuseStep 6780779 = 10171169) B10171169
theorem B9074753 : Blo 940584 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B6781409 : Blo 940584 6781409 := bstep (se 2 (by rfl) ⟨2543028, by rfl⟩ : syracuseStep 6781409 = 5086057) B5086057
theorem B6879755 : Blo 940584 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B2685545 : Blo 940584 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B3177089 : Blo 940584 3177089 := bstep (se 2 (by rfl) ⟨1191408, by rfl⟩ : syracuseStep 3177089 = 2382817) B2382817
theorem B4520863 : Blo 940584 4520863 := bstep (se 1 (by rfl) ⟨3390647, by rfl⟩ : syracuseStep 4520863 = 6781295) B6781295
theorem B10746917 : Blo 940584 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B1211483 : Blo 940584 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B3177899 : Blo 940584 3177899 := bstep (se 1 (by rfl) ⟨2383424, by rfl⟩ : syracuseStep 3177899 = 4766849) B4766849
theorem B3866491 : Blo 940584 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B3178439 : Blo 940584 3178439 := bstep (se 1 (by rfl) ⟨2383829, by rfl⟩ : syracuseStep 3178439 = 4767659) B4767659
theorem B2687231 : Blo 940584 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B15303329 : Blo 940584 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B1508159 : Blo 940584 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B5375099 : Blo 940584 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B16320311 : Blo 940584 16320311 := bstep (se 1 (by rfl) ⟨12240233, by rfl⟩ : syracuseStep 16320311 = 24480467) B24480467
theorem B1410971 : Blo 940584 1410971 := bstep (se 1 (by rfl) ⟨1058228, by rfl⟩ : syracuseStep 1410971 = 2116457) B2116457
theorem B1411007 : Blo 940584 1411007 := bstep (se 1 (by rfl) ⟨1058255, by rfl⟩ : syracuseStep 1411007 = 2116511) B2116511
theorem B1509607 : Blo 940584 1509607 := bstep (se 1 (by rfl) ⟨1132205, by rfl⟩ : syracuseStep 1509607 = 2264411) B2264411
theorem B1411631 : Blo 940584 1411631 := bstep (se 1 (by rfl) ⟨1058723, by rfl⟩ : syracuseStep 1411631 = 2117447) B2117447
theorem B10717757 : Blo 940584 10717757 := bstep (se 3 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 10717757 = 4019159) B4019159
theorem B7146143 : Blo 940584 7146143 := bstep (se 1 (by rfl) ⟨5359607, by rfl⟩ : syracuseStep 7146143 = 10719215) B10719215
theorem B1411751 : Blo 940584 1411751 := bstep (se 1 (by rfl) ⟨1058813, by rfl⟩ : syracuseStep 1411751 = 2117627) B2117627
theorem B1411817 : Blo 940584 1411817 := bstep (se 2 (by rfl) ⟨529431, by rfl⟩ : syracuseStep 1411817 = 1058863) B1058863
theorem B1411823 : Blo 940584 1411823 := bstep (se 1 (by rfl) ⟨1058867, by rfl⟩ : syracuseStep 1411823 = 2117735) B2117735
theorem B4033273 : Blo 940584 4033273 := bstep (se 2 (by rfl) ⟨1512477, by rfl⟩ : syracuseStep 4033273 = 3024955) B3024955
theorem B1411871 : Blo 940584 1411871 := bstep (se 1 (by rfl) ⟨1058903, by rfl⟩ : syracuseStep 1411871 = 2117807) B2117807
theorem B19336087 : Blo 940584 19336087 := bstep (se 1 (by rfl) ⟨14502065, by rfl⟩ : syracuseStep 19336087 = 29004131) B29004131
theorem B5737385 : Blo 940584 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B1412201 : Blo 940584 1412201 := bstep (se 2 (by rfl) ⟨529575, by rfl⟩ : syracuseStep 1412201 = 1059151) B1059151
theorem B1412327 : Blo 940584 1412327 := bstep (se 1 (by rfl) ⟨1059245, by rfl⟩ : syracuseStep 1412327 = 2118491) B2118491
theorem B1412831 : Blo 940584 1412831 := bstep (se 1 (by rfl) ⟨1059623, by rfl⟩ : syracuseStep 1412831 = 2119247) B2119247
theorem B9047801 : Blo 940584 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B1413113 : Blo 940584 1413113 := bstep (se 2 (by rfl) ⟨529917, by rfl⟩ : syracuseStep 1413113 = 1059835) B1059835
theorem B1413311 : Blo 940584 1413311 := bstep (se 1 (by rfl) ⟨1059983, by rfl⟩ : syracuseStep 1413311 = 2119967) B2119967
theorem B3018971 : Blo 940584 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B1413353 : Blo 940584 1413353 := bstep (se 2 (by rfl) ⟨530007, by rfl⟩ : syracuseStep 1413353 = 1060015) B1060015
theorem B2265383 : Blo 940584 2265383 := bstep (se 1 (by rfl) ⟨1699037, by rfl⟩ : syracuseStep 2265383 = 3398075) B3398075
theorem B5738849 : Blo 940584 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B1413479 : Blo 940584 1413479 := bstep (se 1 (by rfl) ⟨1060109, by rfl⟩ : syracuseStep 1413479 = 2120219) B2120219
theorem B5738941 : Blo 940584 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B6033865 : Blo 940584 6033865 := bstep (se 2 (by rfl) ⟨2262699, by rfl⟩ : syracuseStep 6033865 = 4525399) B4525399
theorem B3019393 : Blo 940584 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B7639697 : Blo 940584 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B2036411 : Blo 940584 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B3183515 : Blo 940584 3183515 := bstep (se 1 (by rfl) ⟨2387636, by rfl⟩ : syracuseStep 3183515 = 4775273) B4775273
theorem B7148573 : Blo 940584 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B1414313 : Blo 940584 1414313 := bstep (se 2 (by rfl) ⟨530367, by rfl⟩ : syracuseStep 1414313 = 1060735) B1060735
theorem B5739719 : Blo 940584 5739719 := bstep (se 1 (by rfl) ⟨4304789, by rfl⟩ : syracuseStep 5739719 = 8609579) B8609579
theorem B1414379 : Blo 940584 1414379 := bstep (se 1 (by rfl) ⟨1060784, by rfl⟩ : syracuseStep 1414379 = 2121569) B2121569
theorem B1512683 : Blo 940584 1512683 := bstep (se 1 (by rfl) ⟨1134512, by rfl⟩ : syracuseStep 1512683 = 2269025) B2269025
theorem B176297249 : Blo 940584 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B1414463 : Blo 940584 1414463 := bstep (se 1 (by rfl) ⟨1060847, by rfl⟩ : syracuseStep 1414463 = 2121695) B2121695
theorem B3184055 : Blo 940584 3184055 := bstep (se 1 (by rfl) ⟨2388041, by rfl⟩ : syracuseStep 3184055 = 4776083) B4776083
theorem B1414655 : Blo 940584 1414655 := bstep (se 1 (by rfl) ⟨1060991, by rfl⟩ : syracuseStep 1414655 = 2121983) B2121983
theorem B5379655 : Blo 940584 5379655 := bstep (se 1 (by rfl) ⟨4034741, by rfl⟩ : syracuseStep 5379655 = 8069483) B8069483
theorem B1414763 : Blo 940584 1414763 := bstep (se 1 (by rfl) ⟨1061072, by rfl⟩ : syracuseStep 1414763 = 2122145) B2122145
theorem B1415033 : Blo 940584 1415033 := bstep (se 2 (by rfl) ⟨530637, by rfl⟩ : syracuseStep 1415033 = 1061275) B1061275
theorem B1415279 : Blo 940584 1415279 := bstep (se 1 (by rfl) ⟨1061459, by rfl⟩ : syracuseStep 1415279 = 2122919) B2122919
theorem B6133913 : Blo 940584 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B1415351 : Blo 940584 1415351 := bstep (se 1 (by rfl) ⟨1061513, by rfl⟩ : syracuseStep 1415351 = 2123027) B2123027
theorem B10328435 : Blo 940584 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B7150031 : Blo 940584 7150031 := bstep (se 1 (by rfl) ⟨5362523, by rfl⟩ : syracuseStep 7150031 = 10725047) B10725047
theorem B1415771 : Blo 940584 1415771 := bstep (se 1 (by rfl) ⟨1061828, by rfl⟩ : syracuseStep 1415771 = 2123657) B2123657
theorem B1415783 : Blo 940584 1415783 := bstep (se 1 (by rfl) ⟨1061837, by rfl⟩ : syracuseStep 1415783 = 2123675) B2123675
theorem B1415807 : Blo 940584 1415807 := bstep (se 1 (by rfl) ⟨1061855, by rfl⟩ : syracuseStep 1415807 = 2123711) B2123711
theorem B122231429 : Blo 940584 122231429 := bstep (se 4 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 122231429 = 22918393) B22918393
theorem B5741279 : Blo 940584 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B1415915 : Blo 940584 1415915 := bstep (se 1 (by rfl) ⟨1061936, by rfl⟩ : syracuseStep 1415915 = 2123873) B2123873
theorem B1415945 : Blo 940584 1415945 := bstep (se 2 (by rfl) ⟨530979, by rfl⟩ : syracuseStep 1415945 = 1061959) B1061959
theorem B1416185 : Blo 940584 1416185 := bstep (se 2 (by rfl) ⟨531069, by rfl⟩ : syracuseStep 1416185 = 1062139) B1062139
theorem B6036713 : Blo 940584 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B12885257 : Blo 940584 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B3185945 : Blo 940584 3185945 := bstep (se 2 (by rfl) ⟨1194729, by rfl⟩ : syracuseStep 3185945 = 2389459) B2389459
theorem B1416815 : Blo 940584 1416815 := bstep (se 1 (by rfl) ⟨1062611, by rfl⟩ : syracuseStep 1416815 = 2125223) B2125223
theorem B4300631 : Blo 940584 4300631 := bstep (se 1 (by rfl) ⟨3225473, by rfl⟩ : syracuseStep 4300631 = 6450947) B6450947
theorem B9805711 : Blo 940584 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B1613819 : Blo 940584 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B5087357 : Blo 940584 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B3023315 : Blo 940584 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B3187511 : Blo 940584 3187511 := bstep (se 1 (by rfl) ⟨2390633, by rfl⟩ : syracuseStep 3187511 = 4781267) B4781267
theorem B48997669 : Blo 940584 48997669 := bstep (se 4 (by rfl) ⟨4593531, by rfl⟩ : syracuseStep 48997669 = 9187063) B9187063
theorem B1058287 : Blo 940584 1058287 := bstep (se 1 (by rfl) ⟨793715, by rfl⟩ : syracuseStep 1058287 = 1587431) B1587431
theorem B5155321 : Blo 940584 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B1059439 : Blo 940584 1059439 := bstep (se 1 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 1059439 = 1589159) B1589159
theorem B1190695 : Blo 940584 1190695 := bstep (se 1 (by rfl) ⟨893021, by rfl⟩ : syracuseStep 1190695 = 1786043) B1786043
theorem B1059655 : Blo 940584 1059655 := bstep (se 1 (by rfl) ⟨794741, by rfl⟩ : syracuseStep 1059655 = 1589483) B1589483
theorem B6040403 : Blo 940584 6040403 := bstep (se 1 (by rfl) ⟨4530302, by rfl⟩ : syracuseStep 6040403 = 9060605) B9060605
theorem B1911635 : Blo 940584 1911635 := bstep (se 1 (by rfl) ⟨1433726, by rfl⟩ : syracuseStep 1911635 = 2867453) B2867453
theorem B3025775 : Blo 940584 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B1191019 : Blo 940584 1191019 := bstep (se 1 (by rfl) ⟨893264, by rfl⟩ : syracuseStep 1191019 = 1786529) B1786529
theorem B1060519 : Blo 940584 1060519 := bstep (se 1 (by rfl) ⟨795389, by rfl⟩ : syracuseStep 1060519 = 1590779) B1590779
theorem B12398845 : Blo 940584 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B49656077 : Blo 940584 49656077 := bstep (se 3 (by rfl) ⟨9310514, by rfl⟩ : syracuseStep 49656077 = 18621029) B18621029
theorem B1192735 : Blo 940584 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B1061671 : Blo 940584 1061671 := bstep (se 1 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 1061671 = 1592507) B1592507
theorem B2012143 : Blo 940584 2012143 := bstep (se 1 (by rfl) ⟨1509107, by rfl⟩ : syracuseStep 2012143 = 3018215) B3018215
theorem B4764743 : Blo 940584 4764743 := bstep (se 1 (by rfl) ⟨3573557, by rfl⟩ : syracuseStep 4764743 = 7147115) B7147115
theorem B10171601 : Blo 940584 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B6042887 : Blo 940584 6042887 := bstep (se 1 (by rfl) ⟨4532165, by rfl⟩ : syracuseStep 6042887 = 9064331) B9064331
theorem B3585343 : Blo 940584 3585343 := bstep (se 1 (by rfl) ⟨2689007, by rfl⟩ : syracuseStep 3585343 = 5378015) B5378015
theorem B1062427 : Blo 940584 1062427 := bstep (se 1 (by rfl) ⟨796820, by rfl⟩ : syracuseStep 1062427 = 1593641) B1593641
theorem B4765391 : Blo 940584 4765391 := bstep (se 1 (by rfl) ⟨3574043, by rfl⟩ : syracuseStep 4765391 = 7148087) B7148087
theorem B1062607 : Blo 940584 1062607 := bstep (se 1 (by rfl) ⟨796955, by rfl⟩ : syracuseStep 1062607 = 1593911) B1593911
theorem B5094191 : Blo 940584 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B6044503 : Blo 940584 6044503 := bstep (se 1 (by rfl) ⟨4533377, by rfl⟩ : syracuseStep 6044503 = 9066755) B9066755
theorem B12074291 : Blo 940584 12074291 := bstep (se 1 (by rfl) ⟨9055718, by rfl⟩ : syracuseStep 12074291 = 18111437) B18111437
theorem B22887947 : Blo 940584 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B22921127 : Blo 940584 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B22954205 : Blo 940584 22954205 := bstep (se 3 (by rfl) ⟨4303913, by rfl⟩ : syracuseStep 22954205 = 8607827) B8607827
theorem B2212073 : Blo 940584 2212073 := bstep (se 2 (by rfl) ⟨829527, by rfl⟩ : syracuseStep 2212073 = 1659055) B1659055
theorem B3621935 : Blo 940584 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B1590455 : Blo 940584 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B2116331 : Blo 940584 2116331 := bstep (se 1 (by rfl) ⟨1587248, by rfl⟩ : syracuseStep 2116331 = 3174497) B3174497
theorem B3230621 : Blo 940584 3230621 := bstep (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) B1211483
theorem B1789391 : Blo 940584 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B11456083 : Blo 940584 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B2117231 : Blo 940584 2117231 := bstep (se 1 (by rfl) ⟨1587923, by rfl⟩ : syracuseStep 2117231 = 3175847) B3175847
theorem B2117303 : Blo 940584 2117303 := bstep (se 1 (by rfl) ⟨1587977, by rfl⟩ : syracuseStep 2117303 = 3175955) B3175955
theorem B6049835 : Blo 940584 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B2117753 : Blo 940584 2117753 := bstep (se 2 (by rfl) ⟨794157, by rfl⟩ : syracuseStep 2117753 = 1588315) B1588315
theorem B9687383 : Blo 940584 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B1790363 : Blo 940584 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B2118059 : Blo 940584 2118059 := bstep (se 1 (by rfl) ⟨1588544, by rfl⟩ : syracuseStep 2118059 = 3177089) B3177089
theorem B7164611 : Blo 940584 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B2118599 : Blo 940584 2118599 := bstep (se 1 (by rfl) ⟨1588949, by rfl⟩ : syracuseStep 2118599 = 3177899) B3177899
theorem B2118761 : Blo 940584 2118761 := bstep (se 2 (by rfl) ⟨794535, by rfl⟩ : syracuseStep 2118761 = 1589071) B1589071
theorem B49599611 : Blo 940584 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B2118959 : Blo 940584 2118959 := bstep (se 1 (by rfl) ⟨1589219, by rfl⟩ : syracuseStep 2118959 = 3178439) B3178439
theorem B4773491 : Blo 940584 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B2119391 : Blo 940584 2119391 := bstep (se 1 (by rfl) ⟨1589543, by rfl⟩ : syracuseStep 2119391 = 3179087) B3179087
theorem B2119751 : Blo 940584 2119751 := bstep (se 1 (by rfl) ⟨1589813, by rfl⟩ : syracuseStep 2119751 = 3179627) B3179627
theorem B1432007 : Blo 940584 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B2382311 : Blo 940584 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B940735 : Blo 940584 940735 := bstep (se 1 (by rfl) ⟨705551, by rfl⟩ : syracuseStep 940735 = 1411103) B1411103
theorem B1432255 : Blo 940584 1432255 := bstep (se 1 (by rfl) ⟨1074191, by rfl⟩ : syracuseStep 1432255 = 2148383) B2148383
theorem B6806207 : Blo 940584 6806207 := bstep (se 1 (by rfl) ⟨5104655, by rfl⟩ : syracuseStep 6806207 = 10209311) B10209311
theorem B940863 : Blo 940584 940863 := bstep (se 1 (by rfl) ⟨705647, by rfl⟩ : syracuseStep 940863 = 1411295) B1411295
theorem B2382655 : Blo 940584 2382655 := bstep (se 1 (by rfl) ⟨1786991, by rfl⟩ : syracuseStep 2382655 = 3573983) B3573983
theorem B940903 : Blo 940584 940903 := bstep (se 1 (by rfl) ⟨705677, by rfl⟩ : syracuseStep 940903 = 1411355) B1411355
theorem B51534863 : Blo 940584 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B941119 : Blo 940584 941119 := bstep (se 1 (by rfl) ⟨705839, by rfl⟩ : syracuseStep 941119 = 1411679) B1411679
theorem B4775111 : Blo 940584 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B941307 : Blo 940584 941307 := bstep (se 1 (by rfl) ⟨705980, by rfl⟩ : syracuseStep 941307 = 1411961) B1411961
theorem B941339 : Blo 940584 941339 := bstep (se 1 (by rfl) ⟨706004, by rfl⟩ : syracuseStep 941339 = 1412009) B1412009
theorem B2153819 : Blo 940584 2153819 := bstep (se 1 (by rfl) ⟨1615364, by rfl⟩ : syracuseStep 2153819 = 3230729) B3230729
theorem B941439 : Blo 940584 941439 := bstep (se 1 (by rfl) ⟨706079, by rfl⟩ : syracuseStep 941439 = 1412159) B1412159
theorem B941807 : Blo 940584 941807 := bstep (se 1 (by rfl) ⟨706355, by rfl⟩ : syracuseStep 941807 = 1412711) B1412711
theorem B942063 : Blo 940584 942063 := bstep (se 1 (by rfl) ⟨706547, by rfl⟩ : syracuseStep 942063 = 1413095) B1413095
theorem B4087849 : Blo 940584 4087849 := bstep (se 2 (by rfl) ⟨1532943, by rfl⟩ : syracuseStep 4087849 = 3065887) B3065887
theorem B942143 : Blo 940584 942143 := bstep (se 1 (by rfl) ⟨706607, by rfl⟩ : syracuseStep 942143 = 1413215) B1413215
theorem B942151 : Blo 940584 942151 := bstep (se 1 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 942151 = 1413227) B1413227
theorem B942183 : Blo 940584 942183 := bstep (se 1 (by rfl) ⟨706637, by rfl⟩ : syracuseStep 942183 = 1413275) B1413275
theorem B2384063 : Blo 940584 2384063 := bstep (se 1 (by rfl) ⟨1788047, by rfl⟩ : syracuseStep 2384063 = 3576095) B3576095
theorem B942751 : Blo 940584 942751 := bstep (se 1 (by rfl) ⟨707063, by rfl⟩ : syracuseStep 942751 = 1414127) B1414127
theorem B123921247 : Blo 940584 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B13591421 : Blo 940584 13591421 := bstep (se 3 (by rfl) ⟨2548391, by rfl⟩ : syracuseStep 13591421 = 5096783) B5096783
theorem B943007 : Blo 940584 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B943087 : Blo 940584 943087 := bstep (se 1 (by rfl) ⟨707315, by rfl⟩ : syracuseStep 943087 = 1414631) B1414631
theorem B943195 : Blo 940584 943195 := bstep (se 1 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 943195 = 1414793) B1414793
theorem B943207 : Blo 940584 943207 := bstep (se 1 (by rfl) ⟨707405, by rfl⟩ : syracuseStep 943207 = 1414811) B1414811
theorem B943335 : Blo 940584 943335 := bstep (se 1 (by rfl) ⟨707501, by rfl⟩ : syracuseStep 943335 = 1415003) B1415003
theorem B943591 : Blo 940584 943591 := bstep (se 1 (by rfl) ⟨707693, by rfl⟩ : syracuseStep 943591 = 1415387) B1415387
theorem B943771 : Blo 940584 943771 := bstep (se 1 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 943771 = 1415657) B1415657
theorem B2123603 : Blo 940584 2123603 := bstep (se 1 (by rfl) ⟨1592702, by rfl⟩ : syracuseStep 2123603 = 3185405) B3185405
theorem B944031 : Blo 940584 944031 := bstep (se 1 (by rfl) ⟨708023, by rfl⟩ : syracuseStep 944031 = 1416047) B1416047
theorem B944039 : Blo 940584 944039 := bstep (se 1 (by rfl) ⟨708029, by rfl⟩ : syracuseStep 944039 = 1416059) B1416059
theorem B2386057 : Blo 940584 2386057 := bstep (se 2 (by rfl) ⟨894771, by rfl⟩ : syracuseStep 2386057 = 1789543) B1789543
theorem B7170443 : Blo 940584 7170443 := bstep (se 1 (by rfl) ⟨5377832, by rfl⟩ : syracuseStep 7170443 = 10755665) B10755665
theorem B5368265 : Blo 940584 5368265 := bstep (se 2 (by rfl) ⟨2013099, by rfl⟩ : syracuseStep 5368265 = 4026199) B4026199
theorem B2124665 : Blo 940584 2124665 := bstep (se 2 (by rfl) ⟨796749, by rfl⟩ : syracuseStep 2124665 = 1593499) B1593499
theorem B2386817 : Blo 940584 2386817 := bstep (se 2 (by rfl) ⟨895056, by rfl⟩ : syracuseStep 2386817 = 1790113) B1790113
theorem B1273039 : Blo 940584 1273039 := bstep (se 1 (by rfl) ⟨954779, by rfl⟩ : syracuseStep 1273039 = 1909559) B1909559
theorem B2387627 : Blo 940584 2387627 := bstep (se 1 (by rfl) ⟨1790720, by rfl⟩ : syracuseStep 2387627 = 3581441) B3581441
theorem B104656643 : Blo 940584 104656643 := bstep (se 1 (by rfl) ⟨78492482, by rfl⟩ : syracuseStep 104656643 = 156984965) B156984965
theorem B2387839 : Blo 940584 2387839 := bstep (se 1 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 2387839 = 3581759) B3581759
theorem B4779971 : Blo 940584 4779971 := bstep (se 1 (by rfl) ⟨3584978, by rfl⟩ : syracuseStep 4779971 = 7169957) B7169957
theorem B18346013 : Blo 940584 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B4780943 : Blo 940584 4780943 := bstep (se 1 (by rfl) ⟨3585707, by rfl⟩ : syracuseStep 4780943 = 7171415) B7171415
theorem B18118201 : Blo 940584 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B2422619 : Blo 940584 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B1308847 : Blo 940584 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B11466983 : Blo 940584 11466983 := bstep (se 1 (by rfl) ⟨8600237, by rfl⟩ : syracuseStep 11466983 = 17200475) B17200475
theorem B48986477 : Blo 940584 48986477 := bstep (se 3 (by rfl) ⟨9184964, by rfl⟩ : syracuseStep 48986477 = 18369929) B18369929
theorem B6027817 : Blo 940584 6027817 := bstep (se 2 (by rfl) ⟨2260431, by rfl⟩ : syracuseStep 6027817 = 4520863) B4520863
theorem B4520519 : Blo 940584 4520519 := bstep (se 1 (by rfl) ⟨3390389, by rfl⟩ : syracuseStep 4520519 = 6780779) B6780779
theorem B6781643 : Blo 940584 6781643 := bstep (se 1 (by rfl) ⟨5086232, by rfl⟩ : syracuseStep 6781643 = 10172465) B10172465
theorem B4520939 : Blo 940584 4520939 := bstep (se 1 (by rfl) ⟨3390704, by rfl⟩ : syracuseStep 4520939 = 6781409) B6781409
theorem B4029857 : Blo 940584 4029857 := bstep (se 2 (by rfl) ⟨1511196, by rfl⟩ : syracuseStep 4029857 = 3022393) B3022393
theorem B1474715 : Blo 940584 1474715 := bstep (se 1 (by rfl) ⟨1106036, by rfl⟩ : syracuseStep 1474715 = 2212073) B2212073
theorem B61211213 : Blo 940584 61211213 := bstep (se 3 (by rfl) ⟨11477102, by rfl⟩ : syracuseStep 61211213 = 22954205) B22954205
theorem B10880207 : Blo 940584 10880207 := bstep (se 1 (by rfl) ⟨8160155, by rfl⟩ : syracuseStep 10880207 = 16320311) B16320311
theorem B7145171 : Blo 940584 7145171 := bstep (se 1 (by rfl) ⟨5358878, by rfl⟩ : syracuseStep 7145171 = 10717757) B10717757
theorem B1410887 : Blo 940584 1410887 := bstep (se 1 (by rfl) ⟨1058165, by rfl⟩ : syracuseStep 1410887 = 2116331) B2116331
theorem B1411049 : Blo 940584 1411049 := bstep (se 2 (by rfl) ⟨529143, by rfl⟩ : syracuseStep 1411049 = 1058287) B1058287
theorem B1411487 : Blo 940584 1411487 := bstep (se 1 (by rfl) ⟨1058615, by rfl⟩ : syracuseStep 1411487 = 2117231) B2117231
theorem B1411535 : Blo 940584 1411535 := bstep (se 1 (by rfl) ⟨1058651, by rfl⟩ : syracuseStep 1411535 = 2117303) B2117303
theorem B6031867 : Blo 940584 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B4033223 : Blo 940584 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B1411835 : Blo 940584 1411835 := bstep (se 1 (by rfl) ⟨1058876, by rfl⟩ : syracuseStep 1411835 = 2117753) B2117753
theorem B3181409 : Blo 940584 3181409 := bstep (se 2 (by rfl) ⟨1193028, by rfl⟩ : syracuseStep 3181409 = 2386057) B2386057
theorem B1510255 : Blo 940584 1510255 := bstep (se 1 (by rfl) ⟨1132691, by rfl⟩ : syracuseStep 1510255 = 2265383) B2265383
theorem B6458255 : Blo 940584 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B1412039 : Blo 940584 1412039 := bstep (se 1 (by rfl) ⟨1059029, by rfl⟩ : syracuseStep 1412039 = 2118059) B2118059
theorem B15305917 : Blo 940584 15305917 := bstep (se 3 (by rfl) ⟨2869859, by rfl⟩ : syracuseStep 15305917 = 5739719) B5739719
theorem B1412399 : Blo 940584 1412399 := bstep (se 1 (by rfl) ⟨1059299, by rfl⟩ : syracuseStep 1412399 = 2118599) B2118599
theorem B1412507 : Blo 940584 1412507 := bstep (se 1 (by rfl) ⟨1059380, by rfl⟩ : syracuseStep 1412507 = 2118761) B2118761
theorem B33066407 : Blo 940584 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B1412585 : Blo 940584 1412585 := bstep (se 2 (by rfl) ⟨529719, by rfl⟩ : syracuseStep 1412585 = 1059439) B1059439
theorem B1412639 : Blo 940584 1412639 := bstep (se 1 (by rfl) ⟨1059479, by rfl⟩ : syracuseStep 1412639 = 2118959) B2118959
theorem B5377697 : Blo 940584 5377697 := bstep (se 2 (by rfl) ⟨2016636, by rfl⟩ : syracuseStep 5377697 = 4033273) B4033273
theorem B3182327 : Blo 940584 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B1412873 : Blo 940584 1412873 := bstep (se 2 (by rfl) ⟨529827, by rfl⟩ : syracuseStep 1412873 = 1059655) B1059655
theorem B1412927 : Blo 940584 1412927 := bstep (se 1 (by rfl) ⟨1059695, by rfl⟩ : syracuseStep 1412927 = 2119391) B2119391
theorem B1413167 : Blo 940584 1413167 := bstep (se 1 (by rfl) ⟨1059875, by rfl⟩ : syracuseStep 1413167 = 2119751) B2119751
theorem B6885623 : Blo 940584 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B954671 : Blo 940584 954671 := bstep (se 1 (by rfl) ⟨716003, by rfl⟩ : syracuseStep 954671 = 1432007) B1432007
theorem B3183407 : Blo 940584 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B8590171 : Blo 940584 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B1414025 : Blo 940584 1414025 := bstep (se 2 (by rfl) ⟨530259, by rfl⟩ : syracuseStep 1414025 = 1060519) B1060519
theorem B3183785 : Blo 940584 3183785 := bstep (se 2 (by rfl) ⟨1193919, by rfl⟩ : syracuseStep 3183785 = 2387839) B2387839
theorem B1415561 : Blo 940584 1415561 := bstep (se 2 (by rfl) ⟨530835, by rfl⟩ : syracuseStep 1415561 = 1061671) B1061671
theorem B1415735 : Blo 940584 1415735 := bstep (se 1 (by rfl) ⟨1061801, by rfl⟩ : syracuseStep 1415735 = 2123603) B2123603
theorem B3578843 : Blo 940584 3578843 := bstep (se 1 (by rfl) ⟨2684132, by rfl⟩ : syracuseStep 3578843 = 5368265) B5368265
theorem B1416443 : Blo 940584 1416443 := bstep (se 1 (by rfl) ⟨1062332, by rfl⟩ : syracuseStep 1416443 = 2124665) B2124665
theorem B1416569 : Blo 940584 1416569 := bstep (se 2 (by rfl) ⟨531213, by rfl⟩ : syracuseStep 1416569 = 1062427) B1062427
theorem B24157601 : Blo 940584 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B1416809 : Blo 940584 1416809 := bstep (se 2 (by rfl) ⟨531303, by rfl⟩ : syracuseStep 1416809 = 1062607) B1062607
theorem B8068733 : Blo 940584 8068733 := bstep (se 3 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 8068733 = 3025775) B3025775
theorem B69771095 : Blo 940584 69771095 := bstep (se 1 (by rfl) ⟨52328321, by rfl⟩ : syracuseStep 69771095 = 104656643) B104656643
theorem B3186647 : Blo 940584 3186647 := bstep (se 1 (by rfl) ⟨2389985, by rfl⟩ : syracuseStep 3186647 = 4779971) B4779971
theorem B12230675 : Blo 940584 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B33104051 : Blo 940584 33104051 := bstep (se 1 (by rfl) ⟨24828038, by rfl⟩ : syracuseStep 33104051 = 49656077) B49656077
theorem B1745129 : Blo 940584 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B3187295 : Blo 940584 3187295 := bstep (se 1 (by rfl) ⟨2390471, by rfl⟩ : syracuseStep 3187295 = 4780943) B4780943
theorem B8037089 : Blo 940584 8037089 := bstep (se 2 (by rfl) ⟨3013908, by rfl⟩ : syracuseStep 8037089 = 6027817) B6027817
theorem B1909673 : Blo 940584 1909673 := bstep (se 2 (by rfl) ⟨716127, by rfl⟩ : syracuseStep 1909673 = 1432255) B1432255
theorem B1615079 : Blo 940584 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B7644655 : Blo 940584 7644655 := bstep (se 1 (by rfl) ⟨5733491, by rfl⟩ : syracuseStep 7644655 = 11466983) B11466983
theorem B15280751 : Blo 940584 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B10202219 : Blo 940584 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B3583399 : Blo 940584 3583399 := bstep (se 1 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 3583399 = 5375099) B5375099
theorem B1060303 : Blo 940584 1060303 := bstep (se 1 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 1060303 = 1590455) B1590455
theorem B87207445 : Blo 940584 87207445 := bstep (se 6 (by rfl) ⟨2043924, by rfl⟩ : syracuseStep 87207445 = 4087849) B4087849
theorem B165228329 : Blo 940584 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B4764095 : Blo 940584 4764095 := bstep (se 1 (by rfl) ⟨3573071, by rfl⟩ : syracuseStep 4764095 = 7146143) B7146143
theorem B5093131 : Blo 940584 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B1357607 : Blo 940584 1357607 := bstep (se 1 (by rfl) ⟨1018205, by rfl⟩ : syracuseStep 1357607 = 2036411) B2036411
theorem B4765715 : Blo 940584 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B1587593 : Blo 940584 1587593 := bstep (se 2 (by rfl) ⟨595347, by rfl⟩ : syracuseStep 1587593 = 1190695) B1190695
theorem B1588025 : Blo 940584 1588025 := bstep (se 2 (by rfl) ⟨595509, by rfl⟩ : syracuseStep 1588025 = 1191019) B1191019
theorem B4766687 : Blo 940584 4766687 := bstep (se 1 (by rfl) ⟨3575015, by rfl⟩ : syracuseStep 4766687 = 7150031) B7150031
theorem B1588207 : Blo 940584 1588207 := bstep (se 1 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 1588207 = 2382311) B2382311
theorem B4537471 : Blo 940584 4537471 := bstep (se 1 (by rfl) ⟨3403103, by rfl⟩ : syracuseStep 4537471 = 6806207) B6806207
theorem B34356575 : Blo 940584 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B2867087 : Blo 940584 2867087 := bstep (se 1 (by rfl) ⟨2150315, by rfl⟩ : syracuseStep 2867087 = 4300631) B4300631
theorem B3391571 : Blo 940584 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B1589375 : Blo 940584 1589375 := bstep (se 1 (by rfl) ⟨1192031, by rfl⟩ : syracuseStep 1589375 = 2384063) B2384063
theorem B2015543 : Blo 940584 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B16531793 : Blo 940584 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B7651921 : Blo 940584 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B9060947 : Blo 940584 9060947 := bstep (se 1 (by rfl) ⟨6795710, by rfl⟩ : syracuseStep 9060947 = 13591421) B13591421
theorem B8045153 : Blo 940584 8045153 := bstep (se 2 (by rfl) ⟨3016932, by rfl⟩ : syracuseStep 8045153 = 6033865) B6033865
theorem B1590313 : Blo 940584 1590313 := bstep (se 2 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 1590313 = 1192735) B1192735
theorem B1591211 : Blo 940584 1591211 := bstep (se 1 (by rfl) ⟨1193408, by rfl⟩ : syracuseStep 1591211 = 2386817) B2386817
theorem B1591751 : Blo 940584 1591751 := bstep (se 1 (by rfl) ⟨1193813, by rfl⟩ : syracuseStep 1591751 = 2387627) B2387627
theorem B61099109 : Blo 940584 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B4771709 : Blo 940584 4771709 := bstep (se 3 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 4771709 = 1789391) B1789391
theorem B32657651 : Blo 940584 32657651 := bstep (se 1 (by rfl) ⟨24493238, by rfl⟩ : syracuseStep 32657651 = 48986477) B48986477
theorem B3396127 : Blo 940584 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B8049527 : Blo 940584 8049527 := bstep (se 1 (by rfl) ⟨6037145, by rfl⟩ : syracuseStep 8049527 = 12074291) B12074291
theorem B15258631 : Blo 940584 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B1791487 : Blo 940584 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B8050589 : Blo 940584 8050589 := bstep (se 3 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 8050589 = 3018971) B3018971
theorem B2414623 : Blo 940584 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B4774301 : Blo 940584 4774301 := bstep (se 3 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 4774301 = 1790363) B1790363
theorem B8051237 : Blo 940584 8051237 := bstep (se 4 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 8051237 = 1509607) B1509607
theorem B940647 : Blo 940584 940647 := bstep (se 1 (by rfl) ⟨705485, by rfl⟩ : syracuseStep 940647 = 1410971) B1410971
theorem B940671 : Blo 940584 940671 := bstep (se 1 (by rfl) ⟨705503, by rfl⟩ : syracuseStep 940671 = 1411007) B1411007
theorem B941087 : Blo 940584 941087 := bstep (se 1 (by rfl) ⟨705815, by rfl⟩ : syracuseStep 941087 = 1411631) B1411631
theorem B65330225 : Blo 940584 65330225 := bstep (se 2 (by rfl) ⟨24498834, by rfl⟩ : syracuseStep 65330225 = 48997669) B48997669
theorem B941167 : Blo 940584 941167 := bstep (se 1 (by rfl) ⟨705875, by rfl⟩ : syracuseStep 941167 = 1411751) B1411751
theorem B941211 : Blo 940584 941211 := bstep (se 1 (by rfl) ⟨705908, by rfl⟩ : syracuseStep 941211 = 1411817) B1411817
theorem B941215 : Blo 940584 941215 := bstep (se 1 (by rfl) ⟨705911, by rfl⟩ : syracuseStep 941215 = 1411823) B1411823
theorem B941247 : Blo 940584 941247 := bstep (se 1 (by rfl) ⟨705935, by rfl⟩ : syracuseStep 941247 = 1411871) B1411871
theorem B2153747 : Blo 940584 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B3824923 : Blo 940584 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B941467 : Blo 940584 941467 := bstep (se 1 (by rfl) ⟨706100, by rfl⟩ : syracuseStep 941467 = 1412201) B1412201
theorem B941551 : Blo 940584 941551 := bstep (se 1 (by rfl) ⟨706163, by rfl⟩ : syracuseStep 941551 = 1412327) B1412327
theorem B4021757 : Blo 940584 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B941887 : Blo 940584 941887 := bstep (se 1 (by rfl) ⟨706415, by rfl⟩ : syracuseStep 941887 = 1412831) B1412831
theorem B942075 : Blo 940584 942075 := bstep (se 1 (by rfl) ⟨706556, by rfl⟩ : syracuseStep 942075 = 1413113) B1413113
theorem B942207 : Blo 940584 942207 := bstep (se 1 (by rfl) ⟨706655, by rfl⟩ : syracuseStep 942207 = 1413311) B1413311
theorem B942235 : Blo 940584 942235 := bstep (se 1 (by rfl) ⟨706676, by rfl⟩ : syracuseStep 942235 = 1413353) B1413353
theorem B3825899 : Blo 940584 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B942319 : Blo 940584 942319 := bstep (se 1 (by rfl) ⟨706739, by rfl⟩ : syracuseStep 942319 = 1413479) B1413479
theorem B4776407 : Blo 940584 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B2122343 : Blo 940584 2122343 := bstep (se 1 (by rfl) ⟨1591757, by rfl⟩ : syracuseStep 2122343 = 3183515) B3183515
theorem B6873761 : Blo 940584 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B942875 : Blo 940584 942875 := bstep (se 1 (by rfl) ⟨707156, by rfl⟩ : syracuseStep 942875 = 1414313) B1414313
theorem B942919 : Blo 940584 942919 := bstep (se 1 (by rfl) ⟨707189, by rfl⟩ : syracuseStep 942919 = 1414379) B1414379
theorem B1008455 : Blo 940584 1008455 := bstep (se 1 (by rfl) ⟨756341, by rfl⟩ : syracuseStep 1008455 = 1512683) B1512683
theorem B117531499 : Blo 940584 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B942975 : Blo 940584 942975 := bstep (se 1 (by rfl) ⟨707231, by rfl⟩ : syracuseStep 942975 = 1414463) B1414463
theorem B2122703 : Blo 940584 2122703 := bstep (se 1 (by rfl) ⟨1592027, by rfl⟩ : syracuseStep 2122703 = 3184055) B3184055
theorem B943103 : Blo 940584 943103 := bstep (se 1 (by rfl) ⟨707327, by rfl⟩ : syracuseStep 943103 = 1414655) B1414655
theorem B943175 : Blo 940584 943175 := bstep (se 1 (by rfl) ⟨707381, by rfl⟩ : syracuseStep 943175 = 1414763) B1414763
theorem B25781449 : Blo 940584 25781449 := bstep (se 2 (by rfl) ⟨9668043, by rfl⟩ : syracuseStep 25781449 = 19336087) B19336087
theorem B943355 : Blo 940584 943355 := bstep (se 1 (by rfl) ⟨707516, by rfl⟩ : syracuseStep 943355 = 1415033) B1415033
theorem B943519 : Blo 940584 943519 := bstep (se 1 (by rfl) ⟨707639, by rfl⟩ : syracuseStep 943519 = 1415279) B1415279
theorem B4089275 : Blo 940584 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B943567 : Blo 940584 943567 := bstep (se 1 (by rfl) ⟨707675, by rfl⟩ : syracuseStep 943567 = 1415351) B1415351
theorem B27158165 : Blo 940584 27158165 := bstep (se 6 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 27158165 = 1273039) B1273039
theorem B943847 : Blo 940584 943847 := bstep (se 1 (by rfl) ⟨707885, by rfl⟩ : syracuseStep 943847 = 1415771) B1415771
theorem B943855 : Blo 940584 943855 := bstep (se 1 (by rfl) ⟨707891, by rfl⟩ : syracuseStep 943855 = 1415783) B1415783
theorem B943871 : Blo 940584 943871 := bstep (se 1 (by rfl) ⟨707903, by rfl⟩ : syracuseStep 943871 = 1415807) B1415807
theorem B81487619 : Blo 940584 81487619 := bstep (se 1 (by rfl) ⟨61115714, by rfl⟩ : syracuseStep 81487619 = 122231429) B122231429
theorem B3827519 : Blo 940584 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B943943 : Blo 940584 943943 := bstep (se 1 (by rfl) ⟨707957, by rfl⟩ : syracuseStep 943943 = 1415915) B1415915
theorem B943963 : Blo 940584 943963 := bstep (se 1 (by rfl) ⟨707972, by rfl⟩ : syracuseStep 943963 = 1415945) B1415945
theorem B944123 : Blo 940584 944123 := bstep (se 1 (by rfl) ⟨708092, by rfl⟩ : syracuseStep 944123 = 1416185) B1416185
theorem B4024475 : Blo 940584 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B2123963 : Blo 940584 2123963 := bstep (se 1 (by rfl) ⟨1592972, by rfl⟩ : syracuseStep 2123963 = 3185945) B3185945
theorem B1435879 : Blo 940584 1435879 := bstep (se 1 (by rfl) ⟨1076909, by rfl⟩ : syracuseStep 1435879 = 2153819) B2153819
theorem B944543 : Blo 940584 944543 := bstep (se 1 (by rfl) ⟨708407, by rfl⟩ : syracuseStep 944543 = 1416815) B1416815
theorem B1075879 : Blo 940584 1075879 := bstep (se 1 (by rfl) ⟨806909, by rfl⟩ : syracuseStep 1075879 = 1613819) B1613819
theorem B2125007 : Blo 940584 2125007 := bstep (se 1 (by rfl) ⟨1593755, by rfl⟩ : syracuseStep 2125007 = 3187511) B3187511
theorem B4025857 : Blo 940584 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B2682857 : Blo 940584 2682857 := bstep (se 2 (by rfl) ⟨1006071, by rfl⟩ : syracuseStep 2682857 = 2012143) B2012143
theorem B4780295 : Blo 940584 4780295 := bstep (se 1 (by rfl) ⟨3585221, by rfl⟩ : syracuseStep 4780295 = 7170443) B7170443
theorem B4780457 : Blo 940584 4780457 := bstep (se 2 (by rfl) ⟨1792671, by rfl⟩ : syracuseStep 4780457 = 3585343) B3585343
theorem B4026935 : Blo 940584 4026935 := bstep (se 1 (by rfl) ⟨3020201, by rfl⟩ : syracuseStep 4026935 = 6040403) B6040403
theorem B1274423 : Blo 940584 1274423 := bstep (se 1 (by rfl) ⟨955817, by rfl⟩ : syracuseStep 1274423 = 1911635) B1911635
theorem B7172873 : Blo 940584 7172873 := bstep (se 2 (by rfl) ⟨2689827, by rfl⟩ : syracuseStep 7172873 = 5379655) B5379655
theorem B12055837 : Blo 940584 12055837 := bstep (se 3 (by rfl) ⟨2260469, by rfl⟩ : syracuseStep 12055837 = 4520939) B4520939
theorem B3176495 : Blo 940584 3176495 := bstep (se 1 (by rfl) ⟨2382371, by rfl⟩ : syracuseStep 3176495 = 4764743) B4764743
theorem B6781067 : Blo 940584 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B4028591 : Blo 940584 4028591 := bstep (se 1 (by rfl) ⟨3021443, by rfl⟩ : syracuseStep 4028591 = 6042887) B6042887
theorem B3176873 : Blo 940584 3176873 := bstep (se 2 (by rfl) ⟨1191327, by rfl⟩ : syracuseStep 3176873 = 2382655) B2382655
theorem B8059337 : Blo 940584 8059337 := bstep (se 2 (by rfl) ⟨3022251, by rfl⟩ : syracuseStep 8059337 = 6044503) B6044503
theorem B3176927 : Blo 940584 3176927 := bstep (se 1 (by rfl) ⟨2382695, by rfl⟩ : syracuseStep 3176927 = 4765391) B4765391
theorem B3013679 : Blo 940584 3013679 := bstep (se 1 (by rfl) ⟨2260259, by rfl⟩ : syracuseStep 3013679 = 4520519) B4520519
theorem B4521095 : Blo 940584 4521095 := bstep (se 1 (by rfl) ⟨3390821, by rfl⟩ : syracuseStep 4521095 = 6781643) B6781643
theorem B2686571 : Blo 940584 2686571 := bstep (se 1 (by rfl) ⟨2014928, by rfl⟩ : syracuseStep 2686571 = 4029857) B4029857
theorem B13074281 : Blo 940584 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B2261047 : Blo 940584 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B983143 : Blo 940584 983143 := bstep (se 1 (by rfl) ⟨737357, by rfl⟩ : syracuseStep 983143 = 1474715) B1474715
theorem B4653677 : Blo 940584 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B5374781 : Blo 940584 5374781 := bstep (se 3 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 5374781 = 2015543) B2015543
theorem B34375265 : Blo 940584 34375265 := bstep (se 2 (by rfl) ⟨12890724, by rfl⟩ : syracuseStep 34375265 = 25781449) B25781449
theorem B2688815 : Blo 940584 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B10192873 : Blo 940584 10192873 := bstep (se 2 (by rfl) ⟨3822327, by rfl⟩ : syracuseStep 10192873 = 7644655) B7644655
theorem B40732739 : Blo 940584 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B2689213 : Blo 940584 2689213 := bstep (se 3 (by rfl) ⟨504227, by rfl⟩ : syracuseStep 2689213 = 1008455) B1008455
theorem B3181139 : Blo 940584 3181139 := bstep (se 1 (by rfl) ⟨2385854, by rfl⟩ : syracuseStep 3181139 = 4771709) B4771709
theorem B4590415 : Blo 940584 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B3182867 : Blo 940584 3182867 := bstep (se 1 (by rfl) ⟨2387150, by rfl⟩ : syracuseStep 3182867 = 4774301) B4774301
theorem B1413737 : Blo 940584 1413737 := bstep (se 2 (by rfl) ⟨530151, by rfl⟩ : syracuseStep 1413737 = 1060303) B1060303
theorem B43553483 : Blo 940584 43553483 := bstep (se 1 (by rfl) ⟨32665112, by rfl⟩ : syracuseStep 43553483 = 65330225) B65330225
theorem B5379155 : Blo 940584 5379155 := bstep (se 1 (by rfl) ⟨4034366, by rfl⟩ : syracuseStep 5379155 = 8068733) B8068733
theorem B3184271 : Blo 940584 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B1414895 : Blo 940584 1414895 := bstep (se 1 (by rfl) ⟨1061171, by rfl⟩ : syracuseStep 1414895 = 2122343) B2122343
theorem B1415135 : Blo 940584 1415135 := bstep (se 1 (by rfl) ⟨1061351, by rfl⟩ : syracuseStep 1415135 = 2122703) B2122703
theorem B4528169 : Blo 940584 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B2726183 : Blo 940584 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B1415975 : Blo 940584 1415975 := bstep (se 1 (by rfl) ⟨1061981, by rfl⟩ : syracuseStep 1415975 = 2123963) B2123963
theorem B1416671 : Blo 940584 1416671 := bstep (se 1 (by rfl) ⟨1062503, by rfl⟩ : syracuseStep 1416671 = 2125007) B2125007
theorem B6790841 : Blo 940584 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B3219497 : Blo 940584 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B3186863 : Blo 940584 3186863 := bstep (se 1 (by rfl) ⟨2390147, by rfl⟩ : syracuseStep 3186863 = 4780295) B4780295
theorem B3186971 : Blo 940584 3186971 := bstep (se 1 (by rfl) ⟨2390228, by rfl⟩ : syracuseStep 3186971 = 4780457) B4780457
theorem B5743325 : Blo 940584 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B1058395 : Blo 940584 1058395 := bstep (se 1 (by rfl) ⟨793796, by rfl⟩ : syracuseStep 1058395 = 1587593) B1587593
theorem B1058683 : Blo 940584 1058683 := bstep (se 1 (by rfl) ⟨794012, by rfl⟩ : syracuseStep 1058683 = 1588025) B1588025
theorem B2009119 : Blo 940584 2009119 := bstep (se 1 (by rfl) ⟨1506839, by rfl⟩ : syracuseStep 2009119 = 3013679) B3013679
theorem B7645565 : Blo 940584 7645565 := bstep (se 3 (by rfl) ⟨1433543, by rfl⟩ : syracuseStep 7645565 = 2867087) B2867087
theorem B1059583 : Blo 940584 1059583 := bstep (se 1 (by rfl) ⟨794687, by rfl⟩ : syracuseStep 1059583 = 1589375) B1589375
theorem B11021195 : Blo 940584 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B40807475 : Blo 940584 40807475 := bstep (se 1 (by rfl) ⟨30605606, by rfl⟩ : syracuseStep 40807475 = 61211213) B61211213
theorem B6040631 : Blo 940584 6040631 := bstep (se 1 (by rfl) ⟨4530473, by rfl⟩ : syracuseStep 6040631 = 9060947) B9060947
theorem B10202561 : Blo 940584 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B7253471 : Blo 940584 7253471 := bstep (se 1 (by rfl) ⟨5440103, by rfl⟩ : syracuseStep 7253471 = 10880207) B10880207
theorem B4763447 : Blo 940584 4763447 := bstep (se 1 (by rfl) ⟨3572585, by rfl⟩ : syracuseStep 4763447 = 7145171) B7145171
theorem B156708665 : Blo 940584 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B1060807 : Blo 940584 1060807 := bstep (se 1 (by rfl) ⟨795605, by rfl⟩ : syracuseStep 1060807 = 1591211) B1591211
theorem B1061167 : Blo 940584 1061167 := bstep (se 1 (by rfl) ⟨795875, by rfl⟩ : syracuseStep 1061167 = 1591751) B1591751
theorem B4305503 : Blo 940584 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B3585131 : Blo 940584 3585131 := bstep (se 1 (by rfl) ⟨2688848, by rfl⟩ : syracuseStep 3585131 = 5377697) B5377697
theorem B21771767 : Blo 940584 21771767 := bstep (se 1 (by rfl) ⟨16328825, by rfl⟩ : syracuseStep 21771767 = 32657651) B32657651
theorem B1914505 : Blo 940584 1914505 := bstep (se 2 (by rfl) ⟨717939, by rfl⟩ : syracuseStep 1914505 = 1435879) B1435879
theorem B4306877 : Blo 940584 4306877 := bstep (se 3 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 4306877 = 1615079) B1615079
theorem B8042489 : Blo 940584 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B2013673 : Blo 940584 2013673 := bstep (se 2 (by rfl) ⟨755127, by rfl⟩ : syracuseStep 2013673 = 1510255) B1510255
theorem B3620285 : Blo 940584 3620285 := bstep (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) B1357607
theorem B16105067 : Blo 940584 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B46514063 : Blo 940584 46514063 := bstep (se 1 (by rfl) ⟨34885547, by rfl⟩ : syracuseStep 46514063 = 69771095) B69771095
theorem B22069367 : Blo 940584 22069367 := bstep (se 1 (by rfl) ⟨16552025, by rfl⟩ : syracuseStep 22069367 = 33104051) B33104051
theorem B5358059 : Blo 940584 5358059 := bstep (se 1 (by rfl) ⟨4018544, by rfl⟩ : syracuseStep 5358059 = 8037089) B8037089
theorem B18105443 : Blo 940584 18105443 := bstep (se 1 (by rfl) ⟨13579082, by rfl⟩ : syracuseStep 18105443 = 27158165) B27158165
theorem B11453561 : Blo 940584 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B16074449 : Blo 940584 16074449 := bstep (se 2 (by rfl) ⟨6027918, by rfl⟩ : syracuseStep 16074449 = 12055837) B12055837
theorem B6801479 : Blo 940584 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B110152219 : Blo 940584 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1788571 : Blo 940584 1788571 := bstep (se 1 (by rfl) ⟨1341428, by rfl⟩ : syracuseStep 1788571 = 2682857) B2682857
theorem B2117609 : Blo 940584 2117609 := bstep (se 2 (by rfl) ⟨794103, by rfl⟩ : syracuseStep 2117609 = 1588207) B1588207
theorem B2117663 : Blo 940584 2117663 := bstep (se 1 (by rfl) ⟨1588247, by rfl⟩ : syracuseStep 2117663 = 3176495) B3176495
theorem B6049961 : Blo 940584 6049961 := bstep (se 2 (by rfl) ⟨2268735, by rfl⟩ : syracuseStep 6049961 = 4537471) B4537471
theorem B2117915 : Blo 940584 2117915 := bstep (se 1 (by rfl) ⟨1588436, by rfl⟩ : syracuseStep 2117915 = 3176873) B3176873
theorem B2117951 : Blo 940584 2117951 := bstep (se 1 (by rfl) ⟨1588463, by rfl⟩ : syracuseStep 2117951 = 3176927) B3176927
theorem B5099897 : Blo 940584 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B1791047 : Blo 940584 1791047 := bstep (se 1 (by rfl) ⟨1343285, by rfl⟩ : syracuseStep 1791047 = 2686571) B2686571
theorem B5363435 : Blo 940584 5363435 := bstep (se 1 (by rfl) ⟨4022576, by rfl⟩ : syracuseStep 5363435 = 8045153) B8045153
theorem B2545789 : Blo 940584 2545789 := bstep (se 3 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 2545789 = 954671) B954671
theorem B940591 : Blo 940584 940591 := bstep (se 1 (by rfl) ⟨705443, by rfl⟩ : syracuseStep 940591 = 1410887) B1410887
theorem B940699 : Blo 940584 940699 := bstep (se 1 (by rfl) ⟨705524, by rfl⟩ : syracuseStep 940699 = 1411049) B1411049
theorem B2120417 : Blo 940584 2120417 := bstep (se 2 (by rfl) ⟨795156, by rfl⟩ : syracuseStep 2120417 = 1590313) B1590313
theorem B940991 : Blo 940584 940991 := bstep (se 1 (by rfl) ⟨705743, by rfl⟩ : syracuseStep 940991 = 1411487) B1411487
theorem B941023 : Blo 940584 941023 := bstep (se 1 (by rfl) ⟨705767, by rfl⟩ : syracuseStep 941023 = 1411535) B1411535
theorem B941223 : Blo 940584 941223 := bstep (se 1 (by rfl) ⟨705917, by rfl⟩ : syracuseStep 941223 = 1411835) B1411835
theorem B2120939 : Blo 940584 2120939 := bstep (se 1 (by rfl) ⟨1590704, by rfl⟩ : syracuseStep 2120939 = 3181409) B3181409
theorem B941359 : Blo 940584 941359 := bstep (se 1 (by rfl) ⟨706019, by rfl⟩ : syracuseStep 941359 = 1412039) B1412039
theorem B941599 : Blo 940584 941599 := bstep (se 1 (by rfl) ⟨706199, by rfl⟩ : syracuseStep 941599 = 1412399) B1412399
theorem B941671 : Blo 940584 941671 := bstep (se 1 (by rfl) ⟨706253, by rfl⟩ : syracuseStep 941671 = 1412507) B1412507
theorem B941723 : Blo 940584 941723 := bstep (se 1 (by rfl) ⟨706292, by rfl⟩ : syracuseStep 941723 = 1412585) B1412585
theorem B941759 : Blo 940584 941759 := bstep (se 1 (by rfl) ⟨706319, by rfl⟩ : syracuseStep 941759 = 1412639) B1412639
theorem B2121551 : Blo 940584 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B941915 : Blo 940584 941915 := bstep (se 1 (by rfl) ⟨706436, by rfl⟩ : syracuseStep 941915 = 1412873) B1412873
theorem B941951 : Blo 940584 941951 := bstep (se 1 (by rfl) ⟨706463, by rfl⟩ : syracuseStep 941951 = 1412927) B1412927
theorem B942111 : Blo 940584 942111 := bstep (se 1 (by rfl) ⟨706583, by rfl⟩ : syracuseStep 942111 = 1413167) B1413167
theorem B2122271 : Blo 940584 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B5366351 : Blo 940584 5366351 := bstep (se 1 (by rfl) ⟨4024763, by rfl⟩ : syracuseStep 5366351 = 8049527) B8049527
theorem B942683 : Blo 940584 942683 := bstep (se 1 (by rfl) ⟨707012, by rfl⟩ : syracuseStep 942683 = 1414025) B1414025
theorem B2122523 : Blo 940584 2122523 := bstep (se 1 (by rfl) ⟨1591892, by rfl⟩ : syracuseStep 2122523 = 3183785) B3183785
theorem B1434505 : Blo 940584 1434505 := bstep (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) B1075879
theorem B5367059 : Blo 940584 5367059 := bstep (se 1 (by rfl) ⟨4025294, by rfl⟩ : syracuseStep 5367059 = 8050589) B8050589
theorem B20407889 : Blo 940584 20407889 := bstep (se 2 (by rfl) ⟨7652958, by rfl⟩ : syracuseStep 20407889 = 15305917) B15305917
theorem B943707 : Blo 940584 943707 := bstep (se 1 (by rfl) ⟨707780, by rfl⟩ : syracuseStep 943707 = 1415561) B1415561
theorem B5367491 : Blo 940584 5367491 := bstep (se 1 (by rfl) ⟨4025618, by rfl⟩ : syracuseStep 5367491 = 8051237) B8051237
theorem B943823 : Blo 940584 943823 := bstep (se 1 (by rfl) ⟨707867, by rfl⟩ : syracuseStep 943823 = 1415735) B1415735
theorem B4777865 : Blo 940584 4777865 := bstep (se 2 (by rfl) ⟨1791699, by rfl⟩ : syracuseStep 4777865 = 3583399) B3583399
theorem B2385895 : Blo 940584 2385895 := bstep (se 1 (by rfl) ⟨1789421, by rfl⟩ : syracuseStep 2385895 = 3578843) B3578843
theorem B5367809 : Blo 940584 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B944295 : Blo 940584 944295 := bstep (se 1 (by rfl) ⟨708221, by rfl⟩ : syracuseStep 944295 = 1416443) B1416443
theorem B944379 : Blo 940584 944379 := bstep (se 1 (by rfl) ⟨708284, by rfl⟩ : syracuseStep 944379 = 1416569) B1416569
theorem B2681171 : Blo 940584 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B944539 : Blo 940584 944539 := bstep (se 1 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 944539 = 1416809) B1416809
theorem B2124431 : Blo 940584 2124431 := bstep (se 1 (by rfl) ⟨1593323, by rfl⟩ : syracuseStep 2124431 = 3186647) B3186647
theorem B8153783 : Blo 940584 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B2550599 : Blo 940584 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B2124863 : Blo 940584 2124863 := bstep (se 1 (by rfl) ⟨1593647, by rfl⟩ : syracuseStep 2124863 = 3187295) B3187295
theorem B4582507 : Blo 940584 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B13593845 : Blo 940584 13593845 := bstep (se 5 (by rfl) ⟨637211, by rfl⟩ : syracuseStep 13593845 = 1274423) B1274423
theorem B1273115 : Blo 940584 1273115 := bstep (se 1 (by rfl) ⟨954836, by rfl⟩ : syracuseStep 1273115 = 1909673) B1909673
theorem B54325079 : Blo 940584 54325079 := bstep (se 1 (by rfl) ⟨40743809, by rfl⟩ : syracuseStep 54325079 = 81487619) B81487619
theorem B2551679 : Blo 940584 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B20344841 : Blo 940584 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B2682983 : Blo 940584 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B10187167 : Blo 940584 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B2388649 : Blo 940584 2388649 := bstep (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) B1791487
theorem B465106373 : Blo 940584 465106373 := bstep (se 4 (by rfl) ⟨43603722, by rfl⟩ : syracuseStep 465106373 = 87207445) B87207445
theorem B3176063 : Blo 940584 3176063 := bstep (se 1 (by rfl) ⟨2382047, by rfl⟩ : syracuseStep 3176063 = 4764095) B4764095
theorem B2684623 : Blo 940584 2684623 := bstep (se 1 (by rfl) ⟨2013467, by rfl⟩ : syracuseStep 2684623 = 4026935) B4026935
theorem B4781915 : Blo 940584 4781915 := bstep (se 1 (by rfl) ⟨3586436, by rfl⟩ : syracuseStep 4781915 = 7172873) B7172873
theorem B88177085 : Blo 940584 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B3177143 : Blo 940584 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B4520711 : Blo 940584 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B2685727 : Blo 940584 2685727 := bstep (se 1 (by rfl) ⟨2014295, by rfl⟩ : syracuseStep 2685727 = 4028591) B4028591
theorem B5372891 : Blo 940584 5372891 := bstep (se 1 (by rfl) ⟨4029668, by rfl⟩ : syracuseStep 5372891 = 8059337) B8059337
theorem B3177791 : Blo 940584 3177791 := bstep (se 1 (by rfl) ⟨2383343, by rfl⟩ : syracuseStep 3177791 = 4766687) B4766687
theorem B3014063 : Blo 940584 3014063 := bstep (se 1 (by rfl) ⟨2260547, by rfl⟩ : syracuseStep 3014063 = 4521095) B4521095
theorem B22904383 : Blo 940584 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B8716187 : Blo 940584 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B3014729 : Blo 940584 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B14712911 : Blo 940584 14712911 := bstep (se 1 (by rfl) ⟨11034683, by rfl⟩ : syracuseStep 14712911 = 22069367) B22069367
theorem B1310857 : Blo 940584 1310857 := bstep (se 2 (by rfl) ⟨491571, by rfl⟩ : syracuseStep 1310857 = 983143) B983143
theorem B3572039 : Blo 940584 3572039 := bstep (se 1 (by rfl) ⟨2679029, by rfl⟩ : syracuseStep 3572039 = 5358059) B5358059
theorem B7635707 : Blo 940584 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B10716299 : Blo 940584 10716299 := bstep (se 1 (by rfl) ⟨8037224, by rfl⟩ : syracuseStep 10716299 = 16074449) B16074449
theorem B1411193 : Blo 940584 1411193 := bstep (se 2 (by rfl) ⟨529197, by rfl⟩ : syracuseStep 1411193 = 1058395) B1058395
theorem B1411577 : Blo 940584 1411577 := bstep (se 2 (by rfl) ⟨529341, by rfl⟩ : syracuseStep 1411577 = 1058683) B1058683
theorem B3181193 : Blo 940584 3181193 := bstep (se 2 (by rfl) ⟨1192947, by rfl⟩ : syracuseStep 3181193 = 2385895) B2385895
theorem B1411739 : Blo 940584 1411739 := bstep (se 1 (by rfl) ⟨1058804, by rfl⟩ : syracuseStep 1411739 = 2117609) B2117609
theorem B1411775 : Blo 940584 1411775 := bstep (se 1 (by rfl) ⟨1058831, by rfl⟩ : syracuseStep 1411775 = 2117663) B2117663
theorem B4033307 : Blo 940584 4033307 := bstep (se 1 (by rfl) ⟨3024980, by rfl⟩ : syracuseStep 4033307 = 6049961) B6049961
theorem B1411943 : Blo 940584 1411943 := bstep (se 1 (by rfl) ⟨1058957, by rfl⟩ : syracuseStep 1411943 = 2117915) B2117915
theorem B1411967 : Blo 940584 1411967 := bstep (se 1 (by rfl) ⟨1058975, by rfl⟩ : syracuseStep 1411967 = 2117951) B2117951
theorem B29035655 : Blo 940584 29035655 := bstep (se 1 (by rfl) ⟨21776741, by rfl⟩ : syracuseStep 29035655 = 43553483) B43553483
theorem B146869625 : Blo 940584 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B1412777 : Blo 940584 1412777 := bstep (se 2 (by rfl) ⟨529791, by rfl⟩ : syracuseStep 1412777 = 1059583) B1059583
theorem B3575623 : Blo 940584 3575623 := bstep (se 1 (by rfl) ⟨2681717, by rfl⟩ : syracuseStep 3575623 = 5363435) B5363435
theorem B3018779 : Blo 940584 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B24482213 : Blo 940584 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B1413611 : Blo 940584 1413611 := bstep (se 1 (by rfl) ⟨1060208, by rfl⟩ : syracuseStep 1413611 = 2120417) B2120417
theorem B1413959 : Blo 940584 1413959 := bstep (se 1 (by rfl) ⟨1060469, by rfl⟩ : syracuseStep 1413959 = 2120939) B2120939
theorem B4527227 : Blo 940584 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B1414367 : Blo 940584 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B1414409 : Blo 940584 1414409 := bstep (se 2 (by rfl) ⟨530403, by rfl⟩ : syracuseStep 1414409 = 1060807) B1060807
theorem B1414847 : Blo 940584 1414847 := bstep (se 1 (by rfl) ⟨1061135, by rfl⟩ : syracuseStep 1414847 = 2122271) B2122271
theorem B3577567 : Blo 940584 3577567 := bstep (se 1 (by rfl) ⟨2683175, by rfl⟩ : syracuseStep 3577567 = 5366351) B5366351
theorem B1414889 : Blo 940584 1414889 := bstep (se 2 (by rfl) ⟨530583, by rfl⟩ : syracuseStep 1414889 = 1061167) B1061167
theorem B1415015 : Blo 940584 1415015 := bstep (se 1 (by rfl) ⟨1061261, by rfl⟩ : syracuseStep 1415015 = 2122523) B2122523
theorem B3578039 : Blo 940584 3578039 := bstep (se 1 (by rfl) ⟨2683529, by rfl⟩ : syracuseStep 3578039 = 5367059) B5367059
theorem B3184865 : Blo 940584 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B13605259 : Blo 940584 13605259 := bstep (se 1 (by rfl) ⟨10203944, by rfl⟩ : syracuseStep 13605259 = 20407889) B20407889
theorem B3578327 : Blo 940584 3578327 := bstep (se 1 (by rfl) ⟨2683745, by rfl⟩ : syracuseStep 3578327 = 5367491) B5367491
theorem B3185243 : Blo 940584 3185243 := bstep (se 1 (by rfl) ⟨2388932, by rfl⟩ : syracuseStep 3185243 = 4777865) B4777865
theorem B3578539 : Blo 940584 3578539 := bstep (se 1 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 3578539 = 5367809) B5367809
theorem B1416287 : Blo 940584 1416287 := bstep (se 1 (by rfl) ⟨1062215, by rfl⟩ : syracuseStep 1416287 = 2124431) B2124431
theorem B27204983 : Blo 940584 27204983 := bstep (se 1 (by rfl) ⟨20403737, by rfl⟩ : syracuseStep 27204983 = 40807475) B40807475
theorem B1416575 : Blo 940584 1416575 := bstep (se 1 (by rfl) ⟨1062431, by rfl⟩ : syracuseStep 1416575 = 2124863) B2124863
theorem B3579497 : Blo 940584 3579497 := bstep (se 2 (by rfl) ⟨1342311, by rfl⟩ : syracuseStep 3579497 = 2684623) B2684623
theorem B104472443 : Blo 940584 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B36216719 : Blo 940584 36216719 := bstep (se 1 (by rfl) ⟨27162539, by rfl⟩ : syracuseStep 36216719 = 54325079) B54325079
theorem B3580969 : Blo 940584 3580969 := bstep (se 2 (by rfl) ⟨1342863, by rfl⟩ : syracuseStep 3580969 = 2685727) B2685727
theorem B3187943 : Blo 940584 3187943 := bstep (se 1 (by rfl) ⟨2390957, by rfl⟩ : syracuseStep 3187943 = 4781915) B4781915
theorem B3581927 : Blo 940584 3581927 := bstep (se 1 (by rfl) ⟨2686445, by rfl⟩ : syracuseStep 3581927 = 5372891) B5372891
theorem B2009375 : Blo 940584 2009375 := bstep (se 1 (by rfl) ⟨1507031, by rfl⟩ : syracuseStep 2009375 = 3014063) B3014063
theorem B31009375 : Blo 940584 31009375 := bstep (se 1 (by rfl) ⟨23257031, by rfl⟩ : syracuseStep 31009375 = 46514063) B46514063
theorem B5810791 : Blo 940584 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B3583187 : Blo 940584 3583187 := bstep (se 1 (by rfl) ⟨2687390, by rfl⟩ : syracuseStep 3583187 = 5374781) B5374781
theorem B12070295 : Blo 940584 12070295 := bstep (se 1 (by rfl) ⟨9052721, by rfl⟩ : syracuseStep 12070295 = 18105443) B18105443
theorem B22916843 : Blo 940584 22916843 := bstep (se 1 (by rfl) ⟨17187632, by rfl⟩ : syracuseStep 22916843 = 34375265) B34375265
theorem B1912673 : Blo 940584 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B4534319 : Blo 940584 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B3585617 : Blo 940584 3585617 := bstep (se 2 (by rfl) ⟨1344606, by rfl⟩ : syracuseStep 3585617 = 2689213) B2689213
theorem B1194031 : Blo 940584 1194031 := bstep (se 1 (by rfl) ⟨895523, by rfl⟩ : syracuseStep 1194031 = 1791047) B1791047
theorem B3586103 : Blo 940584 3586103 := bstep (se 1 (by rfl) ⟨2689577, by rfl⟩ : syracuseStep 3586103 = 5379155) B5379155
theorem B6110009 : Blo 940584 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B2146331 : Blo 940584 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B13582889 : Blo 940584 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B1787447 : Blo 940584 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B5097043 : Blo 940584 5097043 := bstep (se 1 (by rfl) ⟨3822782, by rfl⟩ : syracuseStep 5097043 = 7645565) B7645565
theorem B9062563 : Blo 940584 9062563 := bstep (se 1 (by rfl) ⟨6796922, by rfl⟩ : syracuseStep 9062563 = 13593845) B13593845
theorem B6801707 : Blo 940584 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B4835647 : Blo 940584 4835647 := bstep (se 1 (by rfl) ⟨3626735, by rfl⟩ : syracuseStep 4835647 = 7253471) B7253471
theorem B1788655 : Blo 940584 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B3394385 : Blo 940584 3394385 := bstep (se 2 (by rfl) ⟨1272894, by rfl⟩ : syracuseStep 3394385 = 2545789) B2545789
theorem B2870335 : Blo 940584 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B10210693 : Blo 940584 10210693 := bstep (se 4 (by rfl) ⟨957252, by rfl⟩ : syracuseStep 10210693 = 1914505) B1914505
theorem B3394973 : Blo 940584 3394973 := bstep (se 3 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 3394973 = 1273115) B1273115
theorem B310070915 : Blo 940584 310070915 := bstep (se 1 (by rfl) ⟨232553186, by rfl⟩ : syracuseStep 310070915 = 465106373) B465106373
theorem B2117375 : Blo 940584 2117375 := bstep (se 1 (by rfl) ⟨1588031, by rfl⟩ : syracuseStep 2117375 = 3176063) B3176063
theorem B2871251 : Blo 940584 2871251 := bstep (se 1 (by rfl) ⟨2153438, by rfl⟩ : syracuseStep 2871251 = 4306877) B4306877
theorem B5361659 : Blo 940584 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B2118095 : Blo 940584 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B2118527 : Blo 940584 2118527 := bstep (se 1 (by rfl) ⟨1588895, by rfl⟩ : syracuseStep 2118527 = 3177791) B3177791
theorem B2413523 : Blo 940584 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B10736711 : Blo 940584 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B1792543 : Blo 940584 1792543 := bstep (se 1 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 1792543 = 2688815) B2688815
theorem B27155159 : Blo 940584 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B12409805 : Blo 940584 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B2120759 : Blo 940584 2120759 := bstep (se 1 (by rfl) ⟨1590569, by rfl⟩ : syracuseStep 2120759 = 3181139) B3181139
theorem B13590497 : Blo 940584 13590497 := bstep (se 2 (by rfl) ⟨5096436, by rfl⟩ : syracuseStep 13590497 = 10192873) B10192873
theorem B2678825 : Blo 940584 2678825 := bstep (se 2 (by rfl) ⟨1004559, by rfl⟩ : syracuseStep 2678825 = 2009119) B2009119
theorem B2121911 : Blo 940584 2121911 := bstep (se 1 (by rfl) ⟨1591433, by rfl⟩ : syracuseStep 2121911 = 3182867) B3182867
theorem B3399931 : Blo 940584 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B942491 : Blo 940584 942491 := bstep (se 1 (by rfl) ⟨706868, by rfl⟩ : syracuseStep 942491 = 1413737) B1413737
theorem B2384761 : Blo 940584 2384761 := bstep (se 2 (by rfl) ⟨894285, by rfl⟩ : syracuseStep 2384761 = 1788571) B1788571
theorem B2122847 : Blo 940584 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B943263 : Blo 940584 943263 := bstep (se 1 (by rfl) ⟨707447, by rfl⟩ : syracuseStep 943263 = 1414895) B1414895
theorem B943423 : Blo 940584 943423 := bstep (se 1 (by rfl) ⟨707567, by rfl⟩ : syracuseStep 943423 = 1415135) B1415135
theorem B943983 : Blo 940584 943983 := bstep (se 1 (by rfl) ⟨707987, by rfl⟩ : syracuseStep 943983 = 1415975) B1415975
theorem B944447 : Blo 940584 944447 := bstep (se 1 (by rfl) ⟨708335, by rfl⟩ : syracuseStep 944447 = 1416671) B1416671
theorem B2124575 : Blo 940584 2124575 := bstep (se 1 (by rfl) ⟨1593431, by rfl⟩ : syracuseStep 2124575 = 3186863) B3186863
theorem B2124647 : Blo 940584 2124647 := bstep (se 1 (by rfl) ⟨1593485, by rfl⟩ : syracuseStep 2124647 = 3186971) B3186971
theorem B3828883 : Blo 940584 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B7269821 : Blo 940584 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B5435855 : Blo 940584 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B1700399 : Blo 940584 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B4027087 : Blo 940584 4027087 := bstep (se 1 (by rfl) ⟨3020315, by rfl⟩ : syracuseStep 4027087 = 6040631) B6040631
theorem B29389853 : Blo 940584 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B3175631 : Blo 940584 3175631 := bstep (se 1 (by rfl) ⟨2381723, by rfl⟩ : syracuseStep 3175631 = 4763447) B4763447
theorem B1701119 : Blo 940584 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B13563227 : Blo 940584 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B2684897 : Blo 940584 2684897 := bstep (se 2 (by rfl) ⟨1006836, by rfl⟩ : syracuseStep 2684897 = 2013673) B2013673
theorem B2390087 : Blo 940584 2390087 := bstep (se 1 (by rfl) ⟨1792565, by rfl⟩ : syracuseStep 2390087 = 3585131) B3585131
theorem B14514511 : Blo 940584 14514511 := bstep (se 1 (by rfl) ⟨10885883, by rfl⟩ : syracuseStep 14514511 = 21771767) B21771767
theorem B58784723 : Blo 940584 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B3013807 : Blo 940584 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B30539177 : Blo 940584 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B7144199 : Blo 940584 7144199 := bstep (se 1 (by rfl) ⟨5358149, by rfl⟩ : syracuseStep 7144199 = 10716299) B10716299
theorem B3179681 : Blo 940584 3179681 := bstep (se 2 (by rfl) ⟨1192380, by rfl⟩ : syracuseStep 3179681 = 2384761) B2384761
theorem B2688871 : Blo 940584 2688871 := bstep (se 1 (by rfl) ⟨2016653, by rfl⟩ : syracuseStep 2688871 = 4033307) B4033307
theorem B2262923 : Blo 940584 2262923 := bstep (se 1 (by rfl) ⟨1697192, by rfl⟩ : syracuseStep 2262923 = 3394385) B3394385
theorem B97913083 : Blo 940584 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B2263315 : Blo 940584 2263315 := bstep (se 1 (by rfl) ⟨1697486, by rfl⟩ : syracuseStep 2263315 = 3394973) B3394973
theorem B1411583 : Blo 940584 1411583 := bstep (se 1 (by rfl) ⟨1058687, by rfl⟩ : syracuseStep 1411583 = 2117375) B2117375
theorem B3574439 : Blo 940584 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B16321475 : Blo 940584 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B1412063 : Blo 940584 1412063 := bstep (se 1 (by rfl) ⟨1059047, by rfl⟩ : syracuseStep 1412063 = 2118095) B2118095
theorem B165383333 : Blo 940584 165383333 := bstep (se 4 (by rfl) ⟨15504687, by rfl⟩ : syracuseStep 165383333 = 31009375) B31009375
theorem B1412351 : Blo 940584 1412351 := bstep (se 1 (by rfl) ⟨1059263, by rfl⟩ : syracuseStep 1412351 = 2118527) B2118527
theorem B3018151 : Blo 940584 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B1413839 : Blo 940584 1413839 := bstep (se 1 (by rfl) ⟨1060379, by rfl⟩ : syracuseStep 1413839 = 2120759) B2120759
theorem B1414607 : Blo 940584 1414607 := bstep (se 1 (by rfl) ⟨1060955, by rfl⟩ : syracuseStep 1414607 = 2121911) B2121911
theorem B15308453 : Blo 940584 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B1415231 : Blo 940584 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B1416383 : Blo 940584 1416383 := bstep (se 1 (by rfl) ⟨1062287, by rfl⟩ : syracuseStep 1416383 = 2124575) B2124575
theorem B1416431 : Blo 940584 1416431 := bstep (se 1 (by rfl) ⟨1062323, by rfl⟩ : syracuseStep 1416431 = 2124647) B2124647
theorem B15277895 : Blo 940584 15277895 := bstep (se 1 (by rfl) ⟨11458421, by rfl⟩ : syracuseStep 15277895 = 22916843) B22916843
theorem B3022879 : Blo 940584 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B4073339 : Blo 940584 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B20359451 : Blo 940584 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B2009819 : Blo 940584 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B9808607 : Blo 940584 9808607 := bstep (se 1 (by rfl) ⟨7356455, by rfl⟩ : syracuseStep 9808607 = 14712911) B14712911
theorem B4533241 : Blo 940584 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B9055259 : Blo 940584 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B5090471 : Blo 940584 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B6991237 : Blo 940584 6991237 := bstep (se 4 (by rfl) ⟨655428, by rfl⟩ : syracuseStep 6991237 = 1310857) B1310857
theorem B4534471 : Blo 940584 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B6796057 : Blo 940584 6796057 := bstep (se 2 (by rfl) ⟨2548521, by rfl⟩ : syracuseStep 6796057 = 5097043) B5097043
theorem B206713943 : Blo 940584 206713943 := bstep (se 1 (by rfl) ⟨155035457, by rfl⟩ : syracuseStep 206713943 = 310070915) B310070915
theorem B6436061 : Blo 940584 6436061 := bstep (se 3 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 6436061 = 2413523) B2413523
theorem B1914167 : Blo 940584 1914167 := bstep (se 1 (by rfl) ⟨1435625, by rfl⟩ : syracuseStep 1914167 = 2871251) B2871251
theorem B2012519 : Blo 940584 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B4536317 : Blo 940584 4536317 := bstep (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) B1701119
theorem B7157807 : Blo 940584 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B7747721 : Blo 940584 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B4766525 : Blo 940584 4766525 := bstep (se 3 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 4766525 = 1787447) B1787447
theorem B18103439 : Blo 940584 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B13614257 : Blo 940584 13614257 := bstep (se 2 (by rfl) ⟨5105346, by rfl⟩ : syracuseStep 13614257 = 10210693) B10210693
theorem B18136655 : Blo 940584 18136655 := bstep (se 1 (by rfl) ⟨13602491, by rfl⟩ : syracuseStep 18136655 = 27204983) B27204983
theorem B4767497 : Blo 940584 4767497 := bstep (se 2 (by rfl) ⟨1787811, by rfl⟩ : syracuseStep 4767497 = 3575623) B3575623
theorem B9060331 : Blo 940584 9060331 := bstep (se 1 (by rfl) ⟨6795248, by rfl⟩ : syracuseStep 9060331 = 13590497) B13590497
theorem B1785883 : Blo 940584 1785883 := bstep (se 1 (by rfl) ⟨1339412, by rfl⟩ : syracuseStep 1785883 = 2678825) B2678825
theorem B8046863 : Blo 940584 8046863 := bstep (se 1 (by rfl) ⟨6035147, by rfl⟩ : syracuseStep 8046863 = 12070295) B12070295
theorem B4770089 : Blo 940584 4770089 := bstep (se 2 (by rfl) ⟨1788783, by rfl⟩ : syracuseStep 4770089 = 3577567) B3577567
theorem B1592041 : Blo 940584 1592041 := bstep (se 2 (by rfl) ⟨597015, by rfl⟩ : syracuseStep 1592041 = 1194031) B1194031
theorem B3623903 : Blo 940584 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B1133599 : Blo 940584 1133599 := bstep (se 1 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 1133599 = 1700399) B1700399
theorem B19352681 : Blo 940584 19352681 := bstep (se 2 (by rfl) ⟨7257255, by rfl⟩ : syracuseStep 19352681 = 14514511) B14514511
theorem B18140345 : Blo 940584 18140345 := bstep (se 2 (by rfl) ⟨6802629, by rfl⟩ : syracuseStep 18140345 = 13605259) B13605259
theorem B2117087 : Blo 940584 2117087 := bstep (se 1 (by rfl) ⟨1587815, by rfl⟩ : syracuseStep 2117087 = 3175631) B3175631
theorem B4771385 : Blo 940584 4771385 := bstep (se 2 (by rfl) ⟨1789269, by rfl⟩ : syracuseStep 4771385 = 3578539) B3578539
theorem B1789931 : Blo 940584 1789931 := bstep (se 1 (by rfl) ⟨1342448, by rfl⟩ : syracuseStep 1789931 = 2684897) B2684897
theorem B1593391 : Blo 940584 1593391 := bstep (se 1 (by rfl) ⟨1195043, by rfl⟩ : syracuseStep 1593391 = 2390087) B2390087
theorem B4018409 : Blo 940584 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B5100461 : Blo 940584 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B1430887 : Blo 940584 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B2381359 : Blo 940584 2381359 := bstep (se 1 (by rfl) ⟨1786019, by rfl⟩ : syracuseStep 2381359 = 3572039) B3572039
theorem B4774625 : Blo 940584 4774625 := bstep (se 2 (by rfl) ⟨1790484, by rfl⟩ : syracuseStep 4774625 = 3580969) B3580969
theorem B940795 : Blo 940584 940795 := bstep (se 1 (by rfl) ⟨705596, by rfl⟩ : syracuseStep 940795 = 1411193) B1411193
theorem B941051 : Blo 940584 941051 := bstep (se 1 (by rfl) ⟨705788, by rfl⟩ : syracuseStep 941051 = 1411577) B1411577
theorem B2120795 : Blo 940584 2120795 := bstep (se 1 (by rfl) ⟨1590596, by rfl⟩ : syracuseStep 2120795 = 3181193) B3181193
theorem B941159 : Blo 940584 941159 := bstep (se 1 (by rfl) ⟨705869, by rfl⟩ : syracuseStep 941159 = 1411739) B1411739
theorem B941183 : Blo 940584 941183 := bstep (se 1 (by rfl) ⟨705887, by rfl⟩ : syracuseStep 941183 = 1411775) B1411775
theorem B941295 : Blo 940584 941295 := bstep (se 1 (by rfl) ⟨705971, by rfl⟩ : syracuseStep 941295 = 1411943) B1411943
theorem B941311 : Blo 940584 941311 := bstep (se 1 (by rfl) ⟨705983, by rfl⟩ : syracuseStep 941311 = 1411967) B1411967
theorem B19357103 : Blo 940584 19357103 := bstep (se 1 (by rfl) ⟨14517827, by rfl⟩ : syracuseStep 19357103 = 29035655) B29035655
theorem B941851 : Blo 940584 941851 := bstep (se 1 (by rfl) ⟨706388, by rfl⟩ : syracuseStep 941851 = 1412777) B1412777
theorem B12083417 : Blo 940584 12083417 := bstep (se 2 (by rfl) ⟨4531281, by rfl⟩ : syracuseStep 12083417 = 9062563) B9062563
theorem B942407 : Blo 940584 942407 := bstep (se 1 (by rfl) ⟨706805, by rfl⟩ : syracuseStep 942407 = 1413611) B1413611
theorem B6447529 : Blo 940584 6447529 := bstep (se 2 (by rfl) ⟨2417823, by rfl⟩ : syracuseStep 6447529 = 4835647) B4835647
theorem B942639 : Blo 940584 942639 := bstep (se 1 (by rfl) ⟨706979, by rfl⟩ : syracuseStep 942639 = 1413959) B1413959
theorem B942911 : Blo 940584 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B942939 : Blo 940584 942939 := bstep (se 1 (by rfl) ⟨707204, by rfl⟩ : syracuseStep 942939 = 1414409) B1414409
theorem B2384873 : Blo 940584 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B943231 : Blo 940584 943231 := bstep (se 1 (by rfl) ⟨707423, by rfl⟩ : syracuseStep 943231 = 1414847) B1414847
theorem B943259 : Blo 940584 943259 := bstep (se 1 (by rfl) ⟨707444, by rfl⟩ : syracuseStep 943259 = 1414889) B1414889
theorem B943343 : Blo 940584 943343 := bstep (se 1 (by rfl) ⟨707507, by rfl⟩ : syracuseStep 943343 = 1415015) B1415015
theorem B2385359 : Blo 940584 2385359 := bstep (se 1 (by rfl) ⟨1789019, by rfl⟩ : syracuseStep 2385359 = 3578039) B3578039
theorem B2123243 : Blo 940584 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B5105177 : Blo 940584 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B2385551 : Blo 940584 2385551 := bstep (se 1 (by rfl) ⟨1789163, by rfl⟩ : syracuseStep 2385551 = 3578327) B3578327
theorem B2123495 : Blo 940584 2123495 := bstep (se 1 (by rfl) ⟨1592621, by rfl⟩ : syracuseStep 2123495 = 3185243) B3185243
theorem B944191 : Blo 940584 944191 := bstep (se 1 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 944191 = 1416287) B1416287
theorem B944383 : Blo 940584 944383 := bstep (se 1 (by rfl) ⟨708287, by rfl⟩ : syracuseStep 944383 = 1416575) B1416575
theorem B2386331 : Blo 940584 2386331 := bstep (se 1 (by rfl) ⟨1789748, by rfl⟩ : syracuseStep 2386331 = 3579497) B3579497
theorem B24144479 : Blo 940584 24144479 := bstep (se 1 (by rfl) ⟨18108359, by rfl⟩ : syracuseStep 24144479 = 36216719) B36216719
theorem B2125295 : Blo 940584 2125295 := bstep (se 1 (by rfl) ⟨1593971, by rfl⟩ : syracuseStep 2125295 = 3187943) B3187943
theorem B5369449 : Blo 940584 5369449 := bstep (se 2 (by rfl) ⟨2013543, by rfl⟩ : syracuseStep 5369449 = 4027087) B4027087
theorem B2387951 : Blo 940584 2387951 := bstep (se 1 (by rfl) ⟨1790963, by rfl⟩ : syracuseStep 2387951 = 3581927) B3581927
theorem B1339583 : Blo 940584 1339583 := bstep (se 1 (by rfl) ⟨1004687, by rfl⟩ : syracuseStep 1339583 = 2009375) B2009375
theorem B2388791 : Blo 940584 2388791 := bstep (se 1 (by rfl) ⟨1791593, by rfl⟩ : syracuseStep 2388791 = 3583187) B3583187
theorem B4846547 : Blo 940584 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B33092813 : Blo 940584 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B19593235 : Blo 940584 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B2390057 : Blo 940584 2390057 := bstep (se 2 (by rfl) ⟨896271, by rfl⟩ : syracuseStep 2390057 = 1792543) B1792543
theorem B9042151 : Blo 940584 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B2390411 : Blo 940584 2390411 := bstep (se 1 (by rfl) ⟨1792808, by rfl⟩ : syracuseStep 2390411 = 3585617) B3585617
theorem B2390735 : Blo 940584 2390735 := bstep (se 1 (by rfl) ⟨1793051, by rfl⟩ : syracuseStep 2390735 = 3586103) B3586103
theorem B39189815 : Blo 940584 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B278593181 : Blo 940584 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B4030505 : Blo 940584 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B104497253 : Blo 940584 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B3572221 : Blo 940584 3572221 := bstep (se 3 (by rfl) ⟨669791, by rfl⟩ : syracuseStep 3572221 = 1339583) B1339583
theorem B24183845 : Blo 940584 24183845 := bstep (se 4 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 24183845 = 4534471) B4534471
theorem B1508615 : Blo 940584 1508615 := bstep (se 1 (by rfl) ⟨1131461, by rfl⟩ : syracuseStep 1508615 = 2262923) B2262923
theorem B3180059 : Blo 940584 3180059 := bstep (se 1 (by rfl) ⟨2385044, by rfl⟩ : syracuseStep 3180059 = 4770089) B4770089
theorem B10880983 : Blo 940584 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B12093563 : Blo 940584 12093563 := bstep (se 1 (by rfl) ⟨9070172, by rfl⟩ : syracuseStep 12093563 = 18140345) B18140345
theorem B1411391 : Blo 940584 1411391 := bstep (se 1 (by rfl) ⟨1058543, by rfl⟩ : syracuseStep 1411391 = 2117087) B2117087
theorem B3180923 : Blo 940584 3180923 := bstep (se 1 (by rfl) ⟨2385692, by rfl⟩ : syracuseStep 3180923 = 4771385) B4771385
theorem B130550777 : Blo 940584 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B3017753 : Blo 940584 3017753 := bstep (se 2 (by rfl) ⟨1131657, by rfl⟩ : syracuseStep 3017753 = 2263315) B2263315
theorem B88247501 : Blo 940584 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B1511465 : Blo 940584 1511465 := bstep (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) B1133599
theorem B3183083 : Blo 940584 3183083 := bstep (se 1 (by rfl) ⟨2387312, by rfl⟩ : syracuseStep 3183083 = 4774625) B4774625
theorem B1413863 : Blo 940584 1413863 := bstep (se 1 (by rfl) ⟨1060397, by rfl⟩ : syracuseStep 1413863 = 2120795) B2120795
theorem B1415495 : Blo 940584 1415495 := bstep (se 1 (by rfl) ⟨1061621, by rfl⟩ : syracuseStep 1415495 = 2123243) B2123243
theorem B1415663 : Blo 940584 1415663 := bstep (se 1 (by rfl) ⟨1061747, by rfl⟩ : syracuseStep 1415663 = 2123495) B2123495
theorem B13572967 : Blo 940584 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B16096319 : Blo 940584 16096319 := bstep (se 1 (by rfl) ⟨12072239, by rfl⟩ : syracuseStep 16096319 = 24144479) B24144479
theorem B1907849 : Blo 940584 1907849 := bstep (se 2 (by rfl) ⟨715443, by rfl⟩ : syracuseStep 1907849 = 1430887) B1430887
theorem B6036839 : Blo 940584 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B1416863 : Blo 940584 1416863 := bstep (se 1 (by rfl) ⟨1062647, by rfl⟩ : syracuseStep 1416863 = 2125295) B2125295
theorem B51618941 : Blo 940584 51618941 := bstep (se 3 (by rfl) ⟨9678551, by rfl⟩ : syracuseStep 51618941 = 19357103) B19357103
theorem B3024211 : Blo 940584 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B12068959 : Blo 940584 12068959 := bstep (se 1 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 12068959 = 18103439) B18103439
theorem B26126543 : Blo 940584 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B4762799 : Blo 940584 4762799 := bstep (se 1 (by rfl) ⟨3572099, by rfl⟩ : syracuseStep 4762799 = 7144199) B7144199
theorem B8596705 : Blo 940584 8596705 := bstep (se 2 (by rfl) ⟨3223764, by rfl⟩ : syracuseStep 8596705 = 6447529) B6447529
theorem B3585161 : Blo 940584 3585161 := bstep (se 2 (by rfl) ⟨1344435, by rfl⟩ : syracuseStep 3585161 = 2688871) B2688871
theorem B1193287 : Blo 940584 1193287 := bstep (se 1 (by rfl) ⟨894965, by rfl⟩ : syracuseStep 1193287 = 1789931) B1789931
theorem B6044321 : Blo 940584 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B9321649 : Blo 940584 9321649 := bstep (se 2 (by rfl) ⟨3495618, by rfl⟩ : syracuseStep 9321649 = 6991237) B6991237
theorem B7159265 : Blo 940584 7159265 := bstep (se 2 (by rfl) ⟨2684724, by rfl⟩ : syracuseStep 7159265 = 5369449) B5369449
theorem B10862237 : Blo 940584 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B1589915 : Blo 940584 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B1590239 : Blo 940584 1590239 := bstep (se 1 (by rfl) ⟨1192679, by rfl⟩ : syracuseStep 1590239 = 2385359) B2385359
theorem B9061409 : Blo 940584 9061409 := bstep (se 2 (by rfl) ⟨3398028, by rfl⟩ : syracuseStep 9061409 = 6796057) B6796057
theorem B1590367 : Blo 940584 1590367 := bstep (se 1 (by rfl) ⟨1192775, by rfl⟩ : syracuseStep 1590367 = 2385551) B2385551
theorem B1590887 : Blo 940584 1590887 := bstep (se 1 (by rfl) ⟨1193165, by rfl⟩ : syracuseStep 1590887 = 2386331) B2386331
theorem B6539071 : Blo 940584 6539071 := bstep (se 1 (by rfl) ⟨4904303, by rfl⟩ : syracuseStep 6539071 = 9808607) B9808607
theorem B5359517 : Blo 940584 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B3393647 : Blo 940584 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B1591967 : Blo 940584 1591967 := bstep (se 1 (by rfl) ⟨1193975, by rfl⟩ : syracuseStep 1591967 = 2387951) B2387951
theorem B1592527 : Blo 940584 1592527 := bstep (se 1 (by rfl) ⟨1194395, by rfl⟩ : syracuseStep 1592527 = 2388791) B2388791
theorem B3231031 : Blo 940584 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B137809295 : Blo 940584 137809295 := bstep (se 1 (by rfl) ⟨103356971, by rfl⟩ : syracuseStep 137809295 = 206713943) B206713943
theorem B1593371 : Blo 940584 1593371 := bstep (se 1 (by rfl) ⟨1195028, by rfl⟩ : syracuseStep 1593371 = 2390057) B2390057
theorem B4771871 : Blo 940584 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B5165147 : Blo 940584 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B1593607 : Blo 940584 1593607 := bstep (se 1 (by rfl) ⟨1195205, by rfl⟩ : syracuseStep 1593607 = 2390411) B2390411
theorem B1593823 : Blo 940584 1593823 := bstep (se 1 (by rfl) ⟨1195367, by rfl⟩ : syracuseStep 1593823 = 2390735) B2390735
theorem B12080441 : Blo 940584 12080441 := bstep (se 2 (by rfl) ⟨4530165, by rfl⟩ : syracuseStep 12080441 = 9060331) B9060331
theorem B2381177 : Blo 940584 2381177 := bstep (se 2 (by rfl) ⟨892941, by rfl⟩ : syracuseStep 2381177 = 1785883) B1785883
theorem B2119787 : Blo 940584 2119787 := bstep (se 1 (by rfl) ⟨1589840, by rfl⟩ : syracuseStep 2119787 = 3179681) B3179681
theorem B5364575 : Blo 940584 5364575 := bstep (se 1 (by rfl) ⟨4023431, by rfl⟩ : syracuseStep 5364575 = 8046863) B8046863
theorem B941055 : Blo 940584 941055 := bstep (se 1 (by rfl) ⟨705791, by rfl⟩ : syracuseStep 941055 = 1411583) B1411583
theorem B2382959 : Blo 940584 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B941375 : Blo 940584 941375 := bstep (se 1 (by rfl) ⟨706031, by rfl⟩ : syracuseStep 941375 = 1412063) B1412063
theorem B2415935 : Blo 940584 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B12901787 : Blo 940584 12901787 := bstep (se 1 (by rfl) ⟨9676340, by rfl⟩ : syracuseStep 12901787 = 19352681) B19352681
theorem B110255555 : Blo 940584 110255555 := bstep (se 1 (by rfl) ⟨82691666, by rfl⟩ : syracuseStep 110255555 = 165383333) B165383333
theorem B941567 : Blo 940584 941567 := bstep (se 1 (by rfl) ⟨706175, by rfl⟩ : syracuseStep 941567 = 1412351) B1412351
theorem B2678939 : Blo 940584 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B942559 : Blo 940584 942559 := bstep (se 1 (by rfl) ⟨706919, by rfl⟩ : syracuseStep 942559 = 1413839) B1413839
theorem B3400307 : Blo 940584 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B943071 : Blo 940584 943071 := bstep (se 1 (by rfl) ⟨707303, by rfl⟩ : syracuseStep 943071 = 1414607) B1414607
theorem B2122721 : Blo 940584 2122721 := bstep (se 2 (by rfl) ⟨796020, by rfl⟩ : syracuseStep 2122721 = 1592041) B1592041
theorem B943487 : Blo 940584 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B40822541 : Blo 940584 40822541 := bstep (se 3 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 40822541 = 15308453) B15308453
theorem B4024201 : Blo 940584 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B944255 : Blo 940584 944255 := bstep (se 1 (by rfl) ⟨708191, by rfl⟩ : syracuseStep 944255 = 1416383) B1416383
theorem B944287 : Blo 940584 944287 := bstep (se 1 (by rfl) ⟨708215, by rfl⟩ : syracuseStep 944287 = 1416431) B1416431
theorem B10185263 : Blo 940584 10185263 := bstep (se 1 (by rfl) ⟨7638947, by rfl⟩ : syracuseStep 10185263 = 15277895) B15277895
theorem B2124521 : Blo 940584 2124521 := bstep (se 2 (by rfl) ⟨796695, by rfl⟩ : syracuseStep 2124521 = 1593391) B1593391
theorem B8055611 : Blo 940584 8055611 := bstep (se 1 (by rfl) ⟨6041708, by rfl⟩ : syracuseStep 8055611 = 12083417) B12083417
theorem B3403451 : Blo 940584 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B3175145 : Blo 940584 3175145 := bstep (se 2 (by rfl) ⟨1190679, by rfl⟩ : syracuseStep 3175145 = 2381359) B2381359
theorem B12056201 : Blo 940584 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B4290707 : Blo 940584 4290707 := bstep (se 1 (by rfl) ⟨3218030, by rfl⟩ : syracuseStep 4290707 = 6436061) B6436061
theorem B1276111 : Blo 940584 1276111 := bstep (se 1 (by rfl) ⟨957083, by rfl⟩ : syracuseStep 1276111 = 1914167) B1914167
theorem B1341679 : Blo 940584 1341679 := bstep (se 1 (by rfl) ⟨1006259, by rfl⟩ : syracuseStep 1341679 = 2012519) B2012519
theorem B3177683 : Blo 940584 3177683 := bstep (se 1 (by rfl) ⟨2383262, by rfl⟩ : syracuseStep 3177683 = 4766525) B4766525
theorem B9076171 : Blo 940584 9076171 := bstep (se 1 (by rfl) ⟨6807128, by rfl⟩ : syracuseStep 9076171 = 13614257) B13614257
theorem B12091103 : Blo 940584 12091103 := bstep (se 1 (by rfl) ⟨9068327, by rfl⟩ : syracuseStep 12091103 = 18136655) B18136655
theorem B185728787 : Blo 940584 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B3178331 : Blo 940584 3178331 := bstep (se 1 (by rfl) ⟨2383748, by rfl⟩ : syracuseStep 3178331 = 4767497) B4767497
theorem B2687003 : Blo 940584 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B69664835 : Blo 940584 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B4030573 : Blo 940584 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B16122563 : Blo 940584 16122563 := bstep (se 1 (by rfl) ⟨12091922, by rfl⟩ : syracuseStep 16122563 = 24183845) B24183845
theorem B3573011 : Blo 940584 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B2262431 : Blo 940584 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B8062375 : Blo 940584 8062375 := bstep (se 1 (by rfl) ⟨6046781, by rfl⟩ : syracuseStep 8062375 = 12093563) B12093563
theorem B4032281 : Blo 940584 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B87033851 : Blo 940584 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B8718761 : Blo 940584 8718761 := bstep (se 2 (by rfl) ⟨3269535, by rfl⟩ : syracuseStep 8718761 = 6539071) B6539071
theorem B3181247 : Blo 940584 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B16091945 : Blo 940584 16091945 := bstep (se 2 (by rfl) ⟨6034479, by rfl⟩ : syracuseStep 16091945 = 12068959) B12068959
theorem B1413191 : Blo 940584 1413191 := bstep (se 1 (by rfl) ⟨1059893, by rfl⟩ : syracuseStep 1413191 = 2119787) B2119787
theorem B3576383 : Blo 940584 3576383 := bstep (se 1 (by rfl) ⟨2682287, by rfl⟩ : syracuseStep 3576383 = 5364575) B5364575
theorem B1610623 : Blo 940584 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B73503703 : Blo 940584 73503703 := bstep (se 1 (by rfl) ⟨55127777, by rfl⟩ : syracuseStep 73503703 = 110255555) B110255555
theorem B2266871 : Blo 940584 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B69670781 : Blo 940584 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B1415147 : Blo 940584 1415147 := bstep (se 1 (by rfl) ⟨1061360, by rfl⟩ : syracuseStep 1415147 = 2122721) B2122721
theorem B34412627 : Blo 940584 34412627 := bstep (se 1 (by rfl) ⟨25809470, by rfl⟩ : syracuseStep 34412627 = 51618941) B51618941
theorem B49715461 : Blo 940584 49715461 := bstep (se 4 (by rfl) ⟨4660824, by rfl⟩ : syracuseStep 49715461 = 9321649) B9321649
theorem B6790175 : Blo 940584 6790175 := bstep (se 1 (by rfl) ⟨5092631, by rfl⟩ : syracuseStep 6790175 = 10185263) B10185263
theorem B1416347 : Blo 940584 1416347 := bstep (se 1 (by rfl) ⟨1062260, by rfl⟩ : syracuseStep 1416347 = 2124521) B2124521
theorem B2268967 : Blo 940584 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B8037467 : Blo 940584 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B18097289 : Blo 940584 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B2860471 : Blo 940584 2860471 := bstep (se 1 (by rfl) ⟨2145353, by rfl⟩ : syracuseStep 2860471 = 4290707) B4290707
theorem B12101561 : Blo 940584 12101561 := bstep (se 2 (by rfl) ⟨4538085, by rfl⟩ : syracuseStep 12101561 = 9076171) B9076171
theorem B13773725 : Blo 940584 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B1059943 : Blo 940584 1059943 := bstep (se 1 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 1059943 = 1589915) B1589915
theorem B1060159 : Blo 940584 1060159 := bstep (se 1 (by rfl) ⟨795119, by rfl⟩ : syracuseStep 1060159 = 1590239) B1590239
theorem B4762961 : Blo 940584 4762961 := bstep (se 2 (by rfl) ⟨1786110, by rfl⟩ : syracuseStep 4762961 = 3572221) B3572221
theorem B6040939 : Blo 940584 6040939 := bstep (se 1 (by rfl) ⟨4530704, by rfl⟩ : syracuseStep 6040939 = 9061409) B9061409
theorem B1060591 : Blo 940584 1060591 := bstep (se 1 (by rfl) ⟨795443, by rfl⟩ : syracuseStep 1060591 = 1590887) B1590887
theorem B1061311 : Blo 940584 1061311 := bstep (se 1 (by rfl) ⟨795983, by rfl⟩ : syracuseStep 1061311 = 1591967) B1591967
theorem B2011835 : Blo 940584 2011835 := bstep (se 1 (by rfl) ⟨1508876, by rfl⟩ : syracuseStep 2011835 = 3017753) B3017753
theorem B58831667 : Blo 940584 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B1062247 : Blo 940584 1062247 := bstep (se 1 (by rfl) ⟨796685, by rfl⟩ : syracuseStep 1062247 = 1593371) B1593371
theorem B1587451 : Blo 940584 1587451 := bstep (se 1 (by rfl) ⟨1190588, by rfl⟩ : syracuseStep 1587451 = 2381177) B2381177
theorem B4308041 : Blo 940584 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B10730879 : Blo 940584 10730879 := bstep (se 1 (by rfl) ⟨8048159, by rfl⟩ : syracuseStep 10730879 = 16096319) B16096319
theorem B1588639 : Blo 940584 1588639 := bstep (se 1 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 1588639 = 2382959) B2382959
theorem B8601191 : Blo 940584 8601191 := bstep (se 1 (by rfl) ⟨6450893, by rfl⟩ : syracuseStep 8601191 = 12901787) B12901787
theorem B1785959 : Blo 940584 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B27215027 : Blo 940584 27215027 := bstep (se 1 (by rfl) ⟨20411270, by rfl⟩ : syracuseStep 27215027 = 40822541) B40822541
theorem B1591049 : Blo 940584 1591049 := bstep (se 2 (by rfl) ⟨596643, by rfl⟩ : syracuseStep 1591049 = 1193287) B1193287
theorem B1788905 : Blo 940584 1788905 := bstep (se 2 (by rfl) ⟨670839, by rfl⟩ : syracuseStep 1788905 = 1341679) B1341679
theorem B2116763 : Blo 940584 2116763 := bstep (se 1 (by rfl) ⟨1587572, by rfl⟩ : syracuseStep 2116763 = 3175145) B3175145
theorem B2118455 : Blo 940584 2118455 := bstep (se 1 (by rfl) ⟨1588841, by rfl⟩ : syracuseStep 2118455 = 3177683) B3177683
theorem B4772843 : Blo 940584 4772843 := bstep (se 1 (by rfl) ⟨3579632, by rfl⟩ : syracuseStep 4772843 = 7159265) B7159265
theorem B123819191 : Blo 940584 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B2118887 : Blo 940584 2118887 := bstep (se 1 (by rfl) ⟨1589165, by rfl⟩ : syracuseStep 2118887 = 3178331) B3178331
theorem B1005743 : Blo 940584 1005743 := bstep (se 1 (by rfl) ⟨754307, by rfl⟩ : syracuseStep 1005743 = 1508615) B1508615
theorem B2120039 : Blo 940584 2120039 := bstep (se 1 (by rfl) ⟨1590029, by rfl⟩ : syracuseStep 2120039 = 3180059) B3180059
theorem B2120489 : Blo 940584 2120489 := bstep (se 2 (by rfl) ⟨795183, by rfl⟩ : syracuseStep 2120489 = 1590367) B1590367
theorem B940927 : Blo 940584 940927 := bstep (se 1 (by rfl) ⟨705695, by rfl⟩ : syracuseStep 940927 = 1411391) B1411391
theorem B2120615 : Blo 940584 2120615 := bstep (se 1 (by rfl) ⟨1590461, by rfl⟩ : syracuseStep 2120615 = 3180923) B3180923
theorem B91872863 : Blo 940584 91872863 := bstep (se 1 (by rfl) ⟨68904647, by rfl⟩ : syracuseStep 91872863 = 137809295) B137809295
theorem B5365601 : Blo 940584 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B2122055 : Blo 940584 2122055 := bstep (se 1 (by rfl) ⟨1591541, by rfl⟩ : syracuseStep 2122055 = 3183083) B3183083
theorem B942575 : Blo 940584 942575 := bstep (se 1 (by rfl) ⟨706931, by rfl⟩ : syracuseStep 942575 = 1413863) B1413863
theorem B8053627 : Blo 940584 8053627 := bstep (se 1 (by rfl) ⟨6040220, by rfl⟩ : syracuseStep 8053627 = 12080441) B12080441
theorem B943663 : Blo 940584 943663 := bstep (se 1 (by rfl) ⟨707747, by rfl⟩ : syracuseStep 943663 = 1415495) B1415495
theorem B2123369 : Blo 940584 2123369 := bstep (se 2 (by rfl) ⟨796263, by rfl⟩ : syracuseStep 2123369 = 1592527) B1592527
theorem B11462273 : Blo 940584 11462273 := bstep (se 2 (by rfl) ⟨4298352, by rfl⟩ : syracuseStep 11462273 = 8596705) B8596705
theorem B943775 : Blo 940584 943775 := bstep (se 1 (by rfl) ⟨707831, by rfl⟩ : syracuseStep 943775 = 1415663) B1415663
theorem B1271899 : Blo 940584 1271899 := bstep (se 1 (by rfl) ⟨953924, by rfl⟩ : syracuseStep 1271899 = 1907849) B1907849
theorem B4024559 : Blo 940584 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B944575 : Blo 940584 944575 := bstep (se 1 (by rfl) ⟨708431, by rfl⟩ : syracuseStep 944575 = 1416863) B1416863
theorem B2124809 : Blo 940584 2124809 := bstep (se 2 (by rfl) ⟨796803, by rfl⟩ : syracuseStep 2124809 = 1593607) B1593607
theorem B2125097 : Blo 940584 2125097 := bstep (se 2 (by rfl) ⟨796911, by rfl⟩ : syracuseStep 2125097 = 1593823) B1593823
theorem B16118189 : Blo 940584 16118189 := bstep (se 3 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 16118189 = 6044321) B6044321
theorem B5370407 : Blo 940584 5370407 := bstep (se 1 (by rfl) ⟨4027805, by rfl⟩ : syracuseStep 5370407 = 8055611) B8055611
theorem B3175199 : Blo 940584 3175199 := bstep (se 1 (by rfl) ⟨2381399, by rfl⟩ : syracuseStep 3175199 = 4762799) B4762799
theorem B1701481 : Blo 940584 1701481 := bstep (se 2 (by rfl) ⟨638055, by rfl⟩ : syracuseStep 1701481 = 1276111) B1276111
theorem B2390107 : Blo 940584 2390107 := bstep (se 1 (by rfl) ⟨1792580, by rfl⟩ : syracuseStep 2390107 = 3585161) B3585161
theorem B7241491 : Blo 940584 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B58031909 : Blo 940584 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B8060735 : Blo 940584 8060735 := bstep (se 1 (by rfl) ⟨6045551, by rfl⟩ : syracuseStep 8060735 = 12091103) B12091103
theorem B5374097 : Blo 940584 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B10748375 : Blo 940584 10748375 := bstep (se 1 (by rfl) ⟨8061281, by rfl⟩ : syracuseStep 10748375 = 16122563) B16122563
theorem B10749833 : Blo 940584 10749833 := bstep (se 2 (by rfl) ⟨4031187, by rfl⟩ : syracuseStep 10749833 = 8062375) B8062375
theorem B1411175 : Blo 940584 1411175 := bstep (se 1 (by rfl) ⟨1058381, by rfl⟩ : syracuseStep 1411175 = 2116763) B2116763
theorem B1412303 : Blo 940584 1412303 := bstep (se 1 (by rfl) ⟨1059227, by rfl⟩ : syracuseStep 1412303 = 2118455) B2118455
theorem B3181895 : Blo 940584 3181895 := bstep (se 1 (by rfl) ⟨2386421, by rfl⟩ : syracuseStep 3181895 = 4772843) B4772843
theorem B82546127 : Blo 940584 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B1412591 : Blo 940584 1412591 := bstep (se 1 (by rfl) ⟨1059443, by rfl⟩ : syracuseStep 1412591 = 2118887) B2118887
theorem B6033149 : Blo 940584 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B22941751 : Blo 940584 22941751 := bstep (se 1 (by rfl) ⟨17206313, by rfl⟩ : syracuseStep 22941751 = 34412627) B34412627
theorem B1413257 : Blo 940584 1413257 := bstep (se 2 (by rfl) ⟨529971, by rfl⟩ : syracuseStep 1413257 = 1059943) B1059943
theorem B1413359 : Blo 940584 1413359 := bstep (se 1 (by rfl) ⟨1060019, by rfl⟩ : syracuseStep 1413359 = 2120039) B2120039
theorem B1413545 : Blo 940584 1413545 := bstep (se 2 (by rfl) ⟨530079, by rfl⟩ : syracuseStep 1413545 = 1060159) B1060159
theorem B1413659 : Blo 940584 1413659 := bstep (se 1 (by rfl) ⟨1060244, by rfl⟩ : syracuseStep 1413659 = 2120489) B2120489
theorem B1413743 : Blo 940584 1413743 := bstep (se 1 (by rfl) ⟨1060307, by rfl⟩ : syracuseStep 1413743 = 2120615) B2120615
theorem B8589989 : Blo 940584 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B4526783 : Blo 940584 4526783 := bstep (se 1 (by rfl) ⟨3395087, by rfl⟩ : syracuseStep 4526783 = 6790175) B6790175
theorem B10752749 : Blo 940584 10752749 := bstep (se 3 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 10752749 = 4032281) B4032281
theorem B1414121 : Blo 940584 1414121 := bstep (se 2 (by rfl) ⟨530295, by rfl⟩ : syracuseStep 1414121 = 1060591) B1060591
theorem B61248575 : Blo 940584 61248575 := bstep (se 1 (by rfl) ⟨45936431, by rfl⟩ : syracuseStep 61248575 = 91872863) B91872863
theorem B3577067 : Blo 940584 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B1414703 : Blo 940584 1414703 := bstep (se 1 (by rfl) ⟨1061027, by rfl⟩ : syracuseStep 1414703 = 2122055) B2122055
theorem B1415081 : Blo 940584 1415081 := bstep (se 2 (by rfl) ⟨530655, by rfl⟩ : syracuseStep 1415081 = 1061311) B1061311
theorem B12064859 : Blo 940584 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B1415579 : Blo 940584 1415579 := bstep (se 1 (by rfl) ⟨1061684, by rfl⟩ : syracuseStep 1415579 = 2123369) B2123369
theorem B7641515 : Blo 940584 7641515 := bstep (se 1 (by rfl) ⟨5731136, by rfl⟩ : syracuseStep 7641515 = 11462273) B11462273
theorem B8067707 : Blo 940584 8067707 := bstep (se 1 (by rfl) ⟨6050780, by rfl⟩ : syracuseStep 8067707 = 12101561) B12101561
theorem B1416329 : Blo 940584 1416329 := bstep (se 2 (by rfl) ⟨531123, by rfl⟩ : syracuseStep 1416329 = 1062247) B1062247
theorem B9182483 : Blo 940584 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B1416539 : Blo 940584 1416539 := bstep (se 1 (by rfl) ⟨1062404, by rfl⟩ : syracuseStep 1416539 = 2124809) B2124809
theorem B2268641 : Blo 940584 2268641 := bstep (se 2 (by rfl) ⟨850740, by rfl⟩ : syracuseStep 2268641 = 1701481) B1701481
theorem B1416731 : Blo 940584 1416731 := bstep (se 1 (by rfl) ⟨1062548, by rfl⟩ : syracuseStep 1416731 = 2125097) B2125097
theorem B3186809 : Blo 940584 3186809 := bstep (se 2 (by rfl) ⟨1195053, by rfl⟩ : syracuseStep 3186809 = 2390107) B2390107
theorem B3580271 : Blo 940584 3580271 := bstep (se 1 (by rfl) ⟨2685203, by rfl⟩ : syracuseStep 3580271 = 5370407) B5370407
theorem B7153919 : Blo 940584 7153919 := bstep (se 1 (by rfl) ⟨5365439, by rfl⟩ : syracuseStep 7153919 = 10730879) B10730879
theorem B3025289 : Blo 940584 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B46443223 : Blo 940584 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B1190639 : Blo 940584 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B1060699 : Blo 940584 1060699 := bstep (se 1 (by rfl) ⟨795524, by rfl⟩ : syracuseStep 1060699 = 1591049) B1591049
theorem B5812507 : Blo 940584 5812507 := bstep (se 1 (by rfl) ⟨4359380, by rfl⟩ : syracuseStep 5812507 = 8718761) B8718761
theorem B10727963 : Blo 940584 10727963 := bstep (se 1 (by rfl) ⟨8045972, by rfl⟩ : syracuseStep 10727963 = 16091945) B16091945
theorem B3813961 : Blo 940584 3813961 := bstep (se 2 (by rfl) ⟨1430235, by rfl⟩ : syracuseStep 3813961 = 2860471) B2860471
theorem B46447187 : Blo 940584 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B6044989 : Blo 940584 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B392019749 : Blo 940584 392019749 := bstep (se 4 (by rfl) ⟨36751851, by rfl⟩ : syracuseStep 392019749 = 73503703) B73503703
theorem B5358311 : Blo 940584 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B4770413 : Blo 940584 4770413 := bstep (se 3 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 4770413 = 1788905) B1788905
theorem B2116601 : Blo 940584 2116601 := bstep (se 2 (by rfl) ⟨793725, by rfl⟩ : syracuseStep 2116601 = 1587451) B1587451
theorem B2116799 : Blo 940584 2116799 := bstep (se 1 (by rfl) ⟨1587599, by rfl⟩ : syracuseStep 2116799 = 3175199) B3175199
theorem B2118185 : Blo 940584 2118185 := bstep (se 2 (by rfl) ⟨794319, by rfl⟩ : syracuseStep 2118185 = 1588639) B1588639
theorem B2872027 : Blo 940584 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B9655321 : Blo 940584 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B38687939 : Blo 940584 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B1791335 : Blo 940584 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B18143351 : Blo 940584 18143351 := bstep (se 1 (by rfl) ⟨13607513, by rfl⟩ : syracuseStep 18143351 = 27215027) B27215027
theorem B2382007 : Blo 940584 2382007 := bstep (se 1 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 2382007 = 3573011) B3573011
theorem B10738169 : Blo 940584 10738169 := bstep (se 2 (by rfl) ⟨4026813, by rfl⟩ : syracuseStep 10738169 = 8053627) B8053627
theorem B58022567 : Blo 940584 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B265149125 : Blo 940584 265149125 := bstep (se 4 (by rfl) ⟨24857730, by rfl⟩ : syracuseStep 265149125 = 49715461) B49715461
theorem B2120831 : Blo 940584 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B5364893 : Blo 940584 5364893 := bstep (se 3 (by rfl) ⟨1005917, by rfl⟩ : syracuseStep 5364893 = 2011835) B2011835
theorem B942127 : Blo 940584 942127 := bstep (se 1 (by rfl) ⟨706595, by rfl⟩ : syracuseStep 942127 = 1413191) B1413191
theorem B1695865 : Blo 940584 1695865 := bstep (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) B1271899
theorem B2384255 : Blo 940584 2384255 := bstep (se 1 (by rfl) ⟨1788191, by rfl⟩ : syracuseStep 2384255 = 3576383) B3576383
theorem B943431 : Blo 940584 943431 := bstep (se 1 (by rfl) ⟨707573, by rfl⟩ : syracuseStep 943431 = 1415147) B1415147
theorem B8054585 : Blo 940584 8054585 := bstep (se 2 (by rfl) ⟨3020469, by rfl⟩ : syracuseStep 8054585 = 6040939) B6040939
theorem B944231 : Blo 940584 944231 := bstep (se 1 (by rfl) ⟨708173, by rfl⟩ : syracuseStep 944231 = 1416347) B1416347
theorem B2681981 : Blo 940584 2681981 := bstep (se 3 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 2681981 = 1005743) B1005743
theorem B2683039 : Blo 940584 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B3175307 : Blo 940584 3175307 := bstep (se 1 (by rfl) ⟨2381480, by rfl⟩ : syracuseStep 3175307 = 4762961) B4762961
theorem B10745459 : Blo 940584 10745459 := bstep (se 1 (by rfl) ⟨8059094, by rfl⟩ : syracuseStep 10745459 = 16118189) B16118189
theorem B39221111 : Blo 940584 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B5734127 : Blo 940584 5734127 := bstep (se 1 (by rfl) ⟨4300595, by rfl⟩ : syracuseStep 5734127 = 8601191) B8601191
theorem B5373823 : Blo 940584 5373823 := bstep (se 1 (by rfl) ⟨4030367, by rfl⟩ : syracuseStep 5373823 = 8060735) B8060735
theorem B2261153 : Blo 940584 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B3572207 : Blo 940584 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B3180275 : Blo 940584 3180275 := bstep (se 1 (by rfl) ⟨2385206, by rfl⟩ : syracuseStep 3180275 = 4770413) B4770413
theorem B22906637 : Blo 940584 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B1411067 : Blo 940584 1411067 := bstep (se 1 (by rfl) ⟨1058300, by rfl⟩ : syracuseStep 1411067 = 2116601) B2116601
theorem B1411199 : Blo 940584 1411199 := bstep (se 1 (by rfl) ⟨1058399, by rfl⟩ : syracuseStep 1411199 = 2116799) B2116799
theorem B1412123 : Blo 940584 1412123 := bstep (se 1 (by rfl) ⟨1059092, by rfl⟩ : syracuseStep 1412123 = 2118185) B2118185
theorem B3017855 : Blo 940584 3017855 := bstep (se 1 (by rfl) ⟨2263391, by rfl⟩ : syracuseStep 3017855 = 4526783) B4526783
theorem B40832383 : Blo 940584 40832383 := bstep (se 1 (by rfl) ⟨30624287, by rfl⟩ : syracuseStep 40832383 = 61248575) B61248575
theorem B25791959 : Blo 940584 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B12095567 : Blo 940584 12095567 := bstep (se 1 (by rfl) ⟨9071675, by rfl⟩ : syracuseStep 12095567 = 18143351) B18143351
theorem B5378471 : Blo 940584 5378471 := bstep (se 1 (by rfl) ⟨4033853, by rfl⟩ : syracuseStep 5378471 = 8067707) B8067707
theorem B1413887 : Blo 940584 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B3576595 : Blo 940584 3576595 := bstep (se 1 (by rfl) ⟨2682446, by rfl⟩ : syracuseStep 3576595 = 5364893) B5364893
theorem B1512427 : Blo 940584 1512427 := bstep (se 1 (by rfl) ⟨1134320, by rfl⟩ : syracuseStep 1512427 = 2268641) B2268641
theorem B1414265 : Blo 940584 1414265 := bstep (se 2 (by rfl) ⟨530349, by rfl⟩ : syracuseStep 1414265 = 1060699) B1060699
theorem B3577385 : Blo 940584 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B5085281 : Blo 940584 5085281 := bstep (se 2 (by rfl) ⟨1906980, by rfl⟩ : syracuseStep 5085281 = 3813961) B3813961
theorem B7151975 : Blo 940584 7151975 := bstep (se 1 (by rfl) ⟨5363981, by rfl⟩ : syracuseStep 7151975 = 10727963) B10727963
theorem B3582731 : Blo 940584 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B55030751 : Blo 940584 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B8043239 : Blo 940584 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B5094343 : Blo 940584 5094343 := bstep (se 1 (by rfl) ⟨3820757, by rfl⟩ : syracuseStep 5094343 = 7641515) B7641515
theorem B7158779 : Blo 940584 7158779 := bstep (se 1 (by rfl) ⟨5369084, by rfl⟩ : syracuseStep 7158779 = 10738169) B10738169
theorem B38681711 : Blo 940584 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B176766083 : Blo 940584 176766083 := bstep (se 1 (by rfl) ⟨132574562, by rfl⟩ : syracuseStep 176766083 = 265149125) B265149125
theorem B30589001 : Blo 940584 30589001 := bstep (se 2 (by rfl) ⟨11470875, by rfl⟩ : syracuseStep 30589001 = 22941751) B22941751
theorem B1589503 : Blo 940584 1589503 := bstep (se 1 (by rfl) ⟨1192127, by rfl⟩ : syracuseStep 1589503 = 2384255) B2384255
theorem B7750009 : Blo 940584 7750009 := bstep (se 2 (by rfl) ⟨2906253, by rfl⟩ : syracuseStep 7750009 = 5812507) B5812507
theorem B495436661 : Blo 940584 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B4769279 : Blo 940584 4769279 := bstep (se 1 (by rfl) ⟨3576959, by rfl⟩ : syracuseStep 4769279 = 7153919) B7153919
theorem B2016859 : Blo 940584 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B1787987 : Blo 940584 1787987 := bstep (se 1 (by rfl) ⟨1340990, by rfl⟩ : syracuseStep 1787987 = 2681981) B2681981
theorem B2116871 : Blo 940584 2116871 := bstep (se 1 (by rfl) ⟨1587653, by rfl⟩ : syracuseStep 2116871 = 3175307) B3175307
theorem B7163639 : Blo 940584 7163639 := bstep (se 1 (by rfl) ⟨5372729, by rfl⟩ : syracuseStep 7163639 = 10745459) B10745459
theorem B3822751 : Blo 940584 3822751 := bstep (se 1 (by rfl) ⟨2867063, by rfl⟩ : syracuseStep 3822751 = 5734127) B5734127
theorem B7165097 : Blo 940584 7165097 := bstep (se 2 (by rfl) ⟨2686911, by rfl⟩ : syracuseStep 7165097 = 5373823) B5373823
theorem B261346499 : Blo 940584 261346499 := bstep (se 1 (by rfl) ⟨196009874, by rfl⟩ : syracuseStep 261346499 = 392019749) B392019749
theorem B7165583 : Blo 940584 7165583 := bstep (se 1 (by rfl) ⟨5374187, by rfl⟩ : syracuseStep 7165583 = 10748375) B10748375
theorem B7166555 : Blo 940584 7166555 := bstep (se 1 (by rfl) ⟨5374916, by rfl⟩ : syracuseStep 7166555 = 10749833) B10749833
theorem B940783 : Blo 940584 940783 := bstep (se 1 (by rfl) ⟨705587, by rfl⟩ : syracuseStep 940783 = 1411175) B1411175
theorem B941535 : Blo 940584 941535 := bstep (se 1 (by rfl) ⟨706151, by rfl⟩ : syracuseStep 941535 = 1412303) B1412303
theorem B2121263 : Blo 940584 2121263 := bstep (se 1 (by rfl) ⟨1590947, by rfl⟩ : syracuseStep 2121263 = 3181895) B3181895
theorem B941727 : Blo 940584 941727 := bstep (se 1 (by rfl) ⟨706295, by rfl⟩ : syracuseStep 941727 = 1412591) B1412591
theorem B4022099 : Blo 940584 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B942171 : Blo 940584 942171 := bstep (se 1 (by rfl) ⟨706628, by rfl⟩ : syracuseStep 942171 = 1413257) B1413257
theorem B942239 : Blo 940584 942239 := bstep (se 1 (by rfl) ⟨706679, by rfl⟩ : syracuseStep 942239 = 1413359) B1413359
theorem B942363 : Blo 940584 942363 := bstep (se 1 (by rfl) ⟨706772, by rfl⟩ : syracuseStep 942363 = 1413545) B1413545
theorem B942439 : Blo 940584 942439 := bstep (se 1 (by rfl) ⟨706829, by rfl⟩ : syracuseStep 942439 = 1413659) B1413659
theorem B942495 : Blo 940584 942495 := bstep (se 1 (by rfl) ⟨706871, by rfl⟩ : syracuseStep 942495 = 1413743) B1413743
theorem B7168499 : Blo 940584 7168499 := bstep (se 1 (by rfl) ⟨5376374, by rfl⟩ : syracuseStep 7168499 = 10752749) B10752749
theorem B942747 : Blo 940584 942747 := bstep (se 1 (by rfl) ⟨707060, by rfl⟩ : syracuseStep 942747 = 1414121) B1414121
theorem B2384711 : Blo 940584 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B4776893 : Blo 940584 4776893 := bstep (se 3 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 4776893 = 1791335) B1791335
theorem B61924297 : Blo 940584 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B943135 : Blo 940584 943135 := bstep (se 1 (by rfl) ⟨707351, by rfl⟩ : syracuseStep 943135 = 1414703) B1414703
theorem B943387 : Blo 940584 943387 := bstep (se 1 (by rfl) ⟨707540, by rfl⟩ : syracuseStep 943387 = 1415081) B1415081
theorem B943719 : Blo 940584 943719 := bstep (se 1 (by rfl) ⟨707789, by rfl⟩ : syracuseStep 943719 = 1415579) B1415579
theorem B944219 : Blo 940584 944219 := bstep (se 1 (by rfl) ⟨708164, by rfl⟩ : syracuseStep 944219 = 1416329) B1416329
theorem B6121655 : Blo 940584 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B944359 : Blo 940584 944359 := bstep (se 1 (by rfl) ⟨708269, by rfl⟩ : syracuseStep 944359 = 1416539) B1416539
theorem B944487 : Blo 940584 944487 := bstep (se 1 (by rfl) ⟨708365, by rfl⟩ : syracuseStep 944487 = 1416731) B1416731
theorem B2124539 : Blo 940584 2124539 := bstep (se 1 (by rfl) ⟨1593404, by rfl⟩ : syracuseStep 2124539 = 3186809) B3186809
theorem B2386847 : Blo 940584 2386847 := bstep (se 1 (by rfl) ⟨1790135, by rfl⟩ : syracuseStep 2386847 = 3580271) B3580271
theorem B3829369 : Blo 940584 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B5369723 : Blo 940584 5369723 := bstep (se 1 (by rfl) ⟨4027292, by rfl⟩ : syracuseStep 5369723 = 8054585) B8054585
theorem B12873761 : Blo 940584 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B3175037 : Blo 940584 3175037 := bstep (se 3 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 3175037 = 1190639) B1190639
theorem B3176009 : Blo 940584 3176009 := bstep (se 2 (by rfl) ⟨1191003, by rfl⟩ : syracuseStep 3176009 = 2382007) B2382007
theorem B26147407 : Blo 940584 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B8059985 : Blo 940584 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B6029741 : Blo 940584 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B3179519 : Blo 940584 3179519 := bstep (se 1 (by rfl) ⟨2384639, by rfl⟩ : syracuseStep 3179519 = 4769279) B4769279
theorem B15271091 : Blo 940584 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B2689145 : Blo 940584 2689145 := bstep (se 2 (by rfl) ⟨1008429, by rfl⟩ : syracuseStep 2689145 = 2016859) B2016859
theorem B1411247 : Blo 940584 1411247 := bstep (se 1 (by rfl) ⟨1058435, by rfl⟩ : syracuseStep 1411247 = 2116871) B2116871
theorem B8063711 : Blo 940584 8063711 := bstep (se 1 (by rfl) ⟨6047783, by rfl⟩ : syracuseStep 8063711 = 12095567) B12095567
theorem B174230999 : Blo 940584 174230999 := bstep (se 1 (by rfl) ⟨130673249, by rfl⟩ : syracuseStep 174230999 = 261346499) B261346499
theorem B1414175 : Blo 940584 1414175 := bstep (se 1 (by rfl) ⟨1060631, by rfl⟩ : syracuseStep 1414175 = 2121263) B2121263
theorem B3184595 : Blo 940584 3184595 := bstep (se 1 (by rfl) ⟨2388446, by rfl⟩ : syracuseStep 3184595 = 4776893) B4776893
theorem B1416359 : Blo 940584 1416359 := bstep (se 1 (by rfl) ⟨1062269, by rfl⟩ : syracuseStep 1416359 = 2124539) B2124539
theorem B3579815 : Blo 940584 3579815 := bstep (se 1 (by rfl) ⟨2684861, by rfl⟩ : syracuseStep 3579815 = 5369723) B5369723
theorem B6792457 : Blo 940584 6792457 := bstep (se 2 (by rfl) ⟨2547171, by rfl⟩ : syracuseStep 6792457 = 5094343) B5094343
theorem B117844055 : Blo 940584 117844055 := bstep (se 1 (by rfl) ⟨88383041, by rfl⟩ : syracuseStep 117844055 = 176766083) B176766083
theorem B20392667 : Blo 940584 20392667 := bstep (se 1 (by rfl) ⟨15294500, by rfl⟩ : syracuseStep 20392667 = 30589001) B30589001
theorem B10333345 : Blo 940584 10333345 := bstep (se 2 (by rfl) ⟨3875004, by rfl⟩ : syracuseStep 10333345 = 7750009) B7750009
theorem B1191991 : Blo 940584 1191991 := bstep (se 1 (by rfl) ⟨893993, by rfl⟩ : syracuseStep 1191991 = 1787987) B1787987
theorem B3585647 : Blo 940584 3585647 := bstep (se 1 (by rfl) ⟨2689235, by rfl⟩ : syracuseStep 3585647 = 5378471) B5378471
theorem B3390187 : Blo 940584 3390187 := bstep (se 1 (by rfl) ⟨2542640, by rfl⟩ : syracuseStep 3390187 = 5085281) B5085281
theorem B54443177 : Blo 940584 54443177 := bstep (se 2 (by rfl) ⟨20416191, by rfl⟩ : syracuseStep 54443177 = 40832383) B40832383
theorem B4767983 : Blo 940584 4767983 := bstep (se 1 (by rfl) ⟨3575987, by rfl⟩ : syracuseStep 4767983 = 7151975) B7151975
theorem B1589807 : Blo 940584 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B4768793 : Blo 940584 4768793 := bstep (se 2 (by rfl) ⟨1788297, by rfl⟩ : syracuseStep 4768793 = 3576595) B3576595
theorem B2016569 : Blo 940584 2016569 := bstep (se 2 (by rfl) ⟨756213, by rfl⟩ : syracuseStep 2016569 = 1512427) B1512427
theorem B4081103 : Blo 940584 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B5097001 : Blo 940584 5097001 := bstep (se 2 (by rfl) ⟨1911375, by rfl⟩ : syracuseStep 5097001 = 3822751) B3822751
theorem B1591231 : Blo 940584 1591231 := bstep (se 1 (by rfl) ⟨1193423, by rfl⟩ : syracuseStep 1591231 = 2386847) B2386847
theorem B8047613 : Blo 940584 8047613 := bstep (se 3 (by rfl) ⟨1508927, by rfl⟩ : syracuseStep 8047613 = 3017855) B3017855
theorem B2116691 : Blo 940584 2116691 := bstep (se 1 (by rfl) ⟨1587518, by rfl⟩ : syracuseStep 2116691 = 3175037) B3175037
theorem B36687167 : Blo 940584 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B2117339 : Blo 940584 2117339 := bstep (se 1 (by rfl) ⟨1588004, by rfl⟩ : syracuseStep 2117339 = 3176009) B3176009
theorem B5362159 : Blo 940584 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B4772519 : Blo 940584 4772519 := bstep (se 1 (by rfl) ⟨3579389, by rfl⟩ : syracuseStep 4772519 = 7158779) B7158779
theorem B2381471 : Blo 940584 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B2119337 : Blo 940584 2119337 := bstep (se 2 (by rfl) ⟨794751, by rfl⟩ : syracuseStep 2119337 = 1589503) B1589503
theorem B330291107 : Blo 940584 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B2120183 : Blo 940584 2120183 := bstep (se 1 (by rfl) ⟨1590137, by rfl⟩ : syracuseStep 2120183 = 3180275) B3180275
theorem B82565729 : Blo 940584 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B940711 : Blo 940584 940711 := bstep (se 1 (by rfl) ⟨705533, by rfl⟩ : syracuseStep 940711 = 1411067) B1411067
theorem B940799 : Blo 940584 940799 := bstep (se 1 (by rfl) ⟨705599, by rfl⟩ : syracuseStep 940799 = 1411199) B1411199
theorem B941415 : Blo 940584 941415 := bstep (se 1 (by rfl) ⟨706061, by rfl⟩ : syracuseStep 941415 = 1412123) B1412123
theorem B17194639 : Blo 940584 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B4775759 : Blo 940584 4775759 := bstep (se 1 (by rfl) ⟨3581819, by rfl⟩ : syracuseStep 4775759 = 7163639) B7163639
theorem B942591 : Blo 940584 942591 := bstep (se 1 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 942591 = 1413887) B1413887
theorem B942843 : Blo 940584 942843 := bstep (se 1 (by rfl) ⟨707132, by rfl⟩ : syracuseStep 942843 = 1414265) B1414265
theorem B4776731 : Blo 940584 4776731 := bstep (se 1 (by rfl) ⟨3582548, by rfl⟩ : syracuseStep 4776731 = 7165097) B7165097
theorem B2384923 : Blo 940584 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B4777055 : Blo 940584 4777055 := bstep (se 1 (by rfl) ⟨3582791, by rfl⟩ : syracuseStep 4777055 = 7165583) B7165583
theorem B4777703 : Blo 940584 4777703 := bstep (se 1 (by rfl) ⟨3583277, by rfl⟩ : syracuseStep 4777703 = 7166555) B7166555
theorem B5105825 : Blo 940584 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B2681399 : Blo 940584 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B4778999 : Blo 940584 4778999 := bstep (se 1 (by rfl) ⟨3584249, by rfl⟩ : syracuseStep 4778999 = 7168499) B7168499
theorem B2388487 : Blo 940584 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B8582507 : Blo 940584 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B34863209 : Blo 940584 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B5373323 : Blo 940584 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B25787807 : Blo 940584 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B3178655 : Blo 940584 3178655 := bstep (se 1 (by rfl) ⟨2383991, by rfl⟩ : syracuseStep 3178655 = 4767983) B4767983
theorem B3179195 : Blo 940584 3179195 := bstep (se 1 (by rfl) ⟨2384396, by rfl⟩ : syracuseStep 3179195 = 4768793) B4768793
theorem B1344379 : Blo 940584 1344379 := bstep (se 1 (by rfl) ⟨1008284, by rfl⟩ : syracuseStep 1344379 = 2016569) B2016569
theorem B2720735 : Blo 940584 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B3179897 : Blo 940584 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B5375807 : Blo 940584 5375807 := bstep (se 1 (by rfl) ⟨4031855, by rfl⟩ : syracuseStep 5375807 = 8063711) B8063711
theorem B1411127 : Blo 940584 1411127 := bstep (se 1 (by rfl) ⟨1058345, by rfl⟩ : syracuseStep 1411127 = 2116691) B2116691
theorem B1411559 : Blo 940584 1411559 := bstep (se 1 (by rfl) ⟨1058669, by rfl⟩ : syracuseStep 1411559 = 2117339) B2117339
theorem B3181679 : Blo 940584 3181679 := bstep (se 1 (by rfl) ⟨2386259, by rfl⟩ : syracuseStep 3181679 = 4772519) B4772519
theorem B1412891 : Blo 940584 1412891 := bstep (se 1 (by rfl) ⟨1059668, by rfl⟩ : syracuseStep 1412891 = 2119337) B2119337
theorem B1413455 : Blo 940584 1413455 := bstep (se 1 (by rfl) ⟨1060091, by rfl⟩ : syracuseStep 1413455 = 2120183) B2120183
theorem B3183839 : Blo 940584 3183839 := bstep (se 1 (by rfl) ⟨2387879, by rfl⟩ : syracuseStep 3183839 = 4775759) B4775759
theorem B3184487 : Blo 940584 3184487 := bstep (se 1 (by rfl) ⟨2388365, by rfl⟩ : syracuseStep 3184487 = 4776731) B4776731
theorem B7149545 : Blo 940584 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B3184649 : Blo 940584 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B3184703 : Blo 940584 3184703 := bstep (se 1 (by rfl) ⟨2388527, by rfl⟩ : syracuseStep 3184703 = 4777055) B4777055
theorem B3185135 : Blo 940584 3185135 := bstep (se 1 (by rfl) ⟨2388851, by rfl⟩ : syracuseStep 3185135 = 4777703) B4777703
theorem B3185999 : Blo 940584 3185999 := bstep (se 1 (by rfl) ⟨2389499, by rfl⟩ : syracuseStep 3185999 = 4778999) B4778999
theorem B23242139 : Blo 940584 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B3582215 : Blo 940584 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B1059871 : Blo 940584 1059871 := bstep (se 1 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 1059871 = 1589807) B1589807
theorem B9056609 : Blo 940584 9056609 := bstep (se 2 (by rfl) ⟨3396228, by rfl⟩ : syracuseStep 9056609 = 6792457) B6792457
theorem B6796001 : Blo 940584 6796001 := bstep (se 2 (by rfl) ⟨2548500, by rfl⟩ : syracuseStep 6796001 = 5097001) B5097001
theorem B24458111 : Blo 940584 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B1587647 : Blo 940584 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B13777793 : Blo 940584 13777793 := bstep (se 2 (by rfl) ⟨5166672, by rfl⟩ : syracuseStep 13777793 = 10333345) B10333345
theorem B1589321 : Blo 940584 1589321 := bstep (se 2 (by rfl) ⟨595995, by rfl⟩ : syracuseStep 1589321 = 1191991) B1191991
theorem B78562703 : Blo 940584 78562703 := bstep (se 1 (by rfl) ⟨58922027, by rfl⟩ : syracuseStep 78562703 = 117844055) B117844055
theorem B1787599 : Blo 940584 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B5721671 : Blo 940584 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B36295451 : Blo 940584 36295451 := bstep (se 1 (by rfl) ⟨27221588, by rfl⟩ : syracuseStep 36295451 = 54443177) B54443177
theorem B22926185 : Blo 940584 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B17191871 : Blo 940584 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B4019827 : Blo 940584 4019827 := bstep (se 1 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 4019827 = 6029741) B6029741
theorem B2119679 : Blo 940584 2119679 := bstep (se 1 (by rfl) ⟨1589759, by rfl⟩ : syracuseStep 2119679 = 3179519) B3179519
theorem B10180727 : Blo 940584 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B1792763 : Blo 940584 1792763 := bstep (se 1 (by rfl) ⟨1344572, by rfl⟩ : syracuseStep 1792763 = 2689145) B2689145
theorem B940831 : Blo 940584 940831 := bstep (se 1 (by rfl) ⟨705623, by rfl⟩ : syracuseStep 940831 = 1411247) B1411247
theorem B5365075 : Blo 940584 5365075 := bstep (se 1 (by rfl) ⟨4023806, by rfl⟩ : syracuseStep 5365075 = 8047613) B8047613
theorem B116153999 : Blo 940584 116153999 := bstep (se 1 (by rfl) ⟨87115499, by rfl⟩ : syracuseStep 116153999 = 174230999) B174230999
theorem B2121641 : Blo 940584 2121641 := bstep (se 2 (by rfl) ⟨795615, by rfl⟩ : syracuseStep 2121641 = 1591231) B1591231
theorem B942783 : Blo 940584 942783 := bstep (se 1 (by rfl) ⟨707087, by rfl⟩ : syracuseStep 942783 = 1414175) B1414175
theorem B220194071 : Blo 940584 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B2123063 : Blo 940584 2123063 := bstep (se 1 (by rfl) ⟨1592297, by rfl⟩ : syracuseStep 2123063 = 3184595) B3184595
theorem B55043819 : Blo 940584 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B944239 : Blo 940584 944239 := bstep (se 1 (by rfl) ⟨708179, by rfl⟩ : syracuseStep 944239 = 1416359) B1416359
theorem B2386543 : Blo 940584 2386543 := bstep (se 1 (by rfl) ⟨1789907, by rfl⟩ : syracuseStep 2386543 = 3579815) B3579815
theorem B3403883 : Blo 940584 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B13595111 : Blo 940584 13595111 := bstep (se 1 (by rfl) ⟨10196333, by rfl⟩ : syracuseStep 13595111 = 20392667) B20392667
theorem B4520249 : Blo 940584 4520249 := bstep (se 2 (by rfl) ⟨1695093, by rfl⟩ : syracuseStep 4520249 = 3390187) B3390187
theorem B2390431 : Blo 940584 2390431 := bstep (se 1 (by rfl) ⟨1792823, by rfl⟩ : syracuseStep 2390431 = 3585647) B3585647
theorem B9077021 : Blo 940584 9077021 := bstep (se 3 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 9077021 = 3403883) B3403883
theorem B3182057 : Blo 940584 3182057 := bstep (se 2 (by rfl) ⟨1193271, by rfl⟩ : syracuseStep 3182057 = 2386543) B2386543
theorem B1413119 : Blo 940584 1413119 := bstep (se 1 (by rfl) ⟨1059839, by rfl⟩ : syracuseStep 1413119 = 2119679) B2119679
theorem B1413161 : Blo 940584 1413161 := bstep (se 2 (by rfl) ⟨529935, by rfl⟩ : syracuseStep 1413161 = 1059871) B1059871
theorem B6787151 : Blo 940584 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B77435999 : Blo 940584 77435999 := bstep (se 1 (by rfl) ⟨58076999, by rfl⟩ : syracuseStep 77435999 = 116153999) B116153999
theorem B1414427 : Blo 940584 1414427 := bstep (se 1 (by rfl) ⟨1060820, by rfl⟩ : syracuseStep 1414427 = 2121641) B2121641
theorem B1415375 : Blo 940584 1415375 := bstep (se 1 (by rfl) ⟨1061531, by rfl⟩ : syracuseStep 1415375 = 2123063) B2123063
theorem B6037739 : Blo 940584 6037739 := bstep (se 1 (by rfl) ⟨4528304, by rfl⟩ : syracuseStep 6037739 = 9056609) B9056609
theorem B4530667 : Blo 940584 4530667 := bstep (se 1 (by rfl) ⟨3398000, by rfl⟩ : syracuseStep 4530667 = 6796001) B6796001
theorem B3187241 : Blo 940584 3187241 := bstep (se 2 (by rfl) ⟨1195215, by rfl⟩ : syracuseStep 3187241 = 2390431) B2390431
theorem B1058431 : Blo 940584 1058431 := bstep (se 1 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 1058431 = 1587647) B1587647
theorem B7153433 : Blo 940584 7153433 := bstep (se 2 (by rfl) ⟨2682537, by rfl⟩ : syracuseStep 7153433 = 5365075) B5365075
theorem B9185195 : Blo 940584 9185195 := bstep (se 1 (by rfl) ⟨6888896, by rfl⟩ : syracuseStep 9185195 = 13777793) B13777793
theorem B1059547 : Blo 940584 1059547 := bstep (se 1 (by rfl) ⟨794660, by rfl⟩ : syracuseStep 1059547 = 1589321) B1589321
theorem B1813823 : Blo 940584 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B52375135 : Blo 940584 52375135 := bstep (se 1 (by rfl) ⟨39281351, by rfl⟩ : syracuseStep 52375135 = 78562703) B78562703
theorem B3583871 : Blo 940584 3583871 := bstep (se 1 (by rfl) ⟨2687903, by rfl⟩ : syracuseStep 3583871 = 5375807) B5375807
theorem B3814447 : Blo 940584 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B24196967 : Blo 940584 24196967 := bstep (se 1 (by rfl) ⟨18147725, by rfl⟩ : syracuseStep 24196967 = 36295451) B36295451
theorem B15284123 : Blo 940584 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B4766363 : Blo 940584 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B1195175 : Blo 940584 1195175 := bstep (se 1 (by rfl) ⟨896381, by rfl⟩ : syracuseStep 1195175 = 1792763) B1792763
theorem B5359769 : Blo 940584 5359769 := bstep (se 2 (by rfl) ⟨2009913, by rfl⟩ : syracuseStep 5359769 = 4019827) B4019827
theorem B9063407 : Blo 940584 9063407 := bstep (se 1 (by rfl) ⟨6797555, by rfl⟩ : syracuseStep 9063407 = 13595111) B13595111
theorem B16305407 : Blo 940584 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B2119103 : Blo 940584 2119103 := bstep (se 1 (by rfl) ⟨1589327, by rfl⟩ : syracuseStep 2119103 = 3178655) B3178655
theorem B2119463 : Blo 940584 2119463 := bstep (se 1 (by rfl) ⟨1589597, by rfl⟩ : syracuseStep 2119463 = 3179195) B3179195
theorem B2119931 : Blo 940584 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B1792505 : Blo 940584 1792505 := bstep (se 2 (by rfl) ⟨672189, by rfl⟩ : syracuseStep 1792505 = 1344379) B1344379
theorem B940751 : Blo 940584 940751 := bstep (se 1 (by rfl) ⟨705563, by rfl⟩ : syracuseStep 940751 = 1411127) B1411127
theorem B941039 : Blo 940584 941039 := bstep (se 1 (by rfl) ⟨705779, by rfl⟩ : syracuseStep 941039 = 1411559) B1411559
theorem B2121119 : Blo 940584 2121119 := bstep (se 1 (by rfl) ⟨1590839, by rfl⟩ : syracuseStep 2121119 = 3181679) B3181679
theorem B2383465 : Blo 940584 2383465 := bstep (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) B1787599
theorem B941927 : Blo 940584 941927 := bstep (se 1 (by rfl) ⟨706445, by rfl⟩ : syracuseStep 941927 = 1412891) B1412891
theorem B942303 : Blo 940584 942303 := bstep (se 1 (by rfl) ⟨706727, by rfl⟩ : syracuseStep 942303 = 1413455) B1413455
theorem B11461247 : Blo 940584 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B2122559 : Blo 940584 2122559 := bstep (se 1 (by rfl) ⟨1591919, by rfl⟩ : syracuseStep 2122559 = 3183839) B3183839
theorem B2122991 : Blo 940584 2122991 := bstep (se 1 (by rfl) ⟨1592243, by rfl⟩ : syracuseStep 2122991 = 3184487) B3184487
theorem B2123099 : Blo 940584 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B2123135 : Blo 940584 2123135 := bstep (se 1 (by rfl) ⟨1592351, by rfl⟩ : syracuseStep 2123135 = 3184703) B3184703
theorem B2123423 : Blo 940584 2123423 := bstep (se 1 (by rfl) ⟨1592567, by rfl⟩ : syracuseStep 2123423 = 3185135) B3185135
theorem B2123999 : Blo 940584 2123999 := bstep (se 1 (by rfl) ⟨1592999, by rfl⟩ : syracuseStep 2123999 = 3185999) B3185999
theorem B146796047 : Blo 940584 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B15494759 : Blo 940584 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B36695879 : Blo 940584 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B2388143 : Blo 940584 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B3013499 : Blo 940584 3013499 := bstep (se 1 (by rfl) ⟨2260124, by rfl⟩ : syracuseStep 3013499 = 4520249) B4520249
theorem B3573179 : Blo 940584 3573179 := bstep (se 1 (by rfl) ⟨2679884, by rfl⟩ : syracuseStep 3573179 = 5359769) B5359769
theorem B1411241 : Blo 940584 1411241 := bstep (se 2 (by rfl) ⟨529215, by rfl⟩ : syracuseStep 1411241 = 1058431) B1058431
theorem B4524767 : Blo 940584 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B1412729 : Blo 940584 1412729 := bstep (se 2 (by rfl) ⟨529773, by rfl⟩ : syracuseStep 1412729 = 1059547) B1059547
theorem B1412735 : Blo 940584 1412735 := bstep (se 1 (by rfl) ⟨1059551, by rfl⟩ : syracuseStep 1412735 = 2119103) B2119103
theorem B1412975 : Blo 940584 1412975 := bstep (se 1 (by rfl) ⟨1059731, by rfl⟩ : syracuseStep 1412975 = 2119463) B2119463
theorem B1413287 : Blo 940584 1413287 := bstep (se 1 (by rfl) ⟨1059965, by rfl⟩ : syracuseStep 1413287 = 2119931) B2119931
theorem B69833513 : Blo 940584 69833513 := bstep (se 2 (by rfl) ⟨26187567, by rfl⟩ : syracuseStep 69833513 = 52375135) B52375135
theorem B1414079 : Blo 940584 1414079 := bstep (se 1 (by rfl) ⟨1060559, by rfl⟩ : syracuseStep 1414079 = 2121119) B2121119
theorem B7640831 : Blo 940584 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B1415039 : Blo 940584 1415039 := bstep (se 1 (by rfl) ⟨1061279, by rfl⟩ : syracuseStep 1415039 = 2122559) B2122559
theorem B1415327 : Blo 940584 1415327 := bstep (se 1 (by rfl) ⟨1061495, by rfl⟩ : syracuseStep 1415327 = 2122991) B2122991
theorem B1415399 : Blo 940584 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B1415423 : Blo 940584 1415423 := bstep (se 1 (by rfl) ⟨1061567, by rfl⟩ : syracuseStep 1415423 = 2123135) B2123135
theorem B1415615 : Blo 940584 1415615 := bstep (se 1 (by rfl) ⟨1061711, by rfl⟩ : syracuseStep 1415615 = 2123423) B2123423
theorem B5085929 : Blo 940584 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B1415999 : Blo 940584 1415999 := bstep (se 1 (by rfl) ⟨1061999, by rfl⟩ : syracuseStep 1415999 = 2123999) B2123999
theorem B10329839 : Blo 940584 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B3187133 : Blo 940584 3187133 := bstep (se 3 (by rfl) ⟨597587, by rfl⟩ : syracuseStep 3187133 = 1195175) B1195175
theorem B16131311 : Blo 940584 16131311 := bstep (se 1 (by rfl) ⟨12098483, by rfl⟩ : syracuseStep 16131311 = 24196967) B24196967
theorem B2008999 : Blo 940584 2008999 := bstep (se 1 (by rfl) ⟨1506749, by rfl⟩ : syracuseStep 2008999 = 3013499) B3013499
theorem B6040889 : Blo 940584 6040889 := bstep (se 2 (by rfl) ⟨2265333, by rfl⟩ : syracuseStep 6040889 = 4530667) B4530667
theorem B6042271 : Blo 940584 6042271 := bstep (se 1 (by rfl) ⟨4531703, by rfl⟩ : syracuseStep 6042271 = 9063407) B9063407
theorem B51623999 : Blo 940584 51623999 := bstep (se 1 (by rfl) ⟨38717999, by rfl⟩ : syracuseStep 51623999 = 77435999) B77435999
theorem B1195003 : Blo 940584 1195003 := bstep (se 1 (by rfl) ⟨896252, by rfl⟩ : syracuseStep 1195003 = 1792505) B1792505
theorem B24493853 : Blo 940584 24493853 := bstep (se 3 (by rfl) ⟨4592597, by rfl⟩ : syracuseStep 24493853 = 9185195) B9185195
theorem B4768955 : Blo 940584 4768955 := bstep (se 1 (by rfl) ⟨3576716, by rfl⟩ : syracuseStep 4768955 = 7153433) B7153433
theorem B97864031 : Blo 940584 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B24463919 : Blo 940584 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B1592095 : Blo 940584 1592095 := bstep (se 1 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 1592095 = 2388143) B2388143
theorem B6051347 : Blo 940584 6051347 := bstep (se 1 (by rfl) ⟨4538510, by rfl⟩ : syracuseStep 6051347 = 9077021) B9077021
theorem B10870271 : Blo 940584 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B2121371 : Blo 940584 2121371 := bstep (se 1 (by rfl) ⟨1591028, by rfl⟩ : syracuseStep 2121371 = 3182057) B3182057
theorem B942079 : Blo 940584 942079 := bstep (se 1 (by rfl) ⟨706559, by rfl⟩ : syracuseStep 942079 = 1413119) B1413119
theorem B942107 : Blo 940584 942107 := bstep (se 1 (by rfl) ⟨706580, by rfl⟩ : syracuseStep 942107 = 1413161) B1413161
theorem B942951 : Blo 940584 942951 := bstep (se 1 (by rfl) ⟨707213, by rfl⟩ : syracuseStep 942951 = 1414427) B1414427
theorem B943583 : Blo 940584 943583 := bstep (se 1 (by rfl) ⟨707687, by rfl⟩ : syracuseStep 943583 = 1415375) B1415375
theorem B4025159 : Blo 940584 4025159 := bstep (se 1 (by rfl) ⟨3018869, by rfl⟩ : syracuseStep 4025159 = 6037739) B6037739
theorem B2124827 : Blo 940584 2124827 := bstep (se 1 (by rfl) ⟨1593620, by rfl⟩ : syracuseStep 2124827 = 3187241) B3187241
theorem B1209215 : Blo 940584 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B2389247 : Blo 940584 2389247 := bstep (se 1 (by rfl) ⟨1791935, by rfl⟩ : syracuseStep 2389247 = 3583871) B3583871
theorem B10189415 : Blo 940584 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B3177575 : Blo 940584 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B3177953 : Blo 940584 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B3179303 : Blo 940584 3179303 := bstep (se 1 (by rfl) ⟨2384477, by rfl⟩ : syracuseStep 3179303 = 4768955) B4768955
theorem B65242687 : Blo 940584 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B3016511 : Blo 940584 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B186222701 : Blo 940584 186222701 := bstep (se 3 (by rfl) ⟨34916756, by rfl⟩ : syracuseStep 186222701 = 69833513) B69833513
theorem B4034231 : Blo 940584 4034231 := bstep (se 1 (by rfl) ⟨3025673, by rfl⟩ : syracuseStep 4034231 = 6051347) B6051347
theorem B7246847 : Blo 940584 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B1414247 : Blo 940584 1414247 := bstep (se 1 (by rfl) ⟨1060685, by rfl⟩ : syracuseStep 1414247 = 2121371) B2121371
theorem B6886559 : Blo 940584 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B10754207 : Blo 940584 10754207 := bstep (se 1 (by rfl) ⟨8065655, by rfl⟩ : syracuseStep 10754207 = 16131311) B16131311
theorem B1416551 : Blo 940584 1416551 := bstep (se 1 (by rfl) ⟨1062413, by rfl⟩ : syracuseStep 1416551 = 2124827) B2124827
theorem B34415999 : Blo 940584 34415999 := bstep (se 1 (by rfl) ⟨25811999, by rfl⟩ : syracuseStep 34415999 = 51623999) B51623999
theorem B6792943 : Blo 940584 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B16329235 : Blo 940584 16329235 := bstep (se 1 (by rfl) ⟨12246926, by rfl⟩ : syracuseStep 16329235 = 24493853) B24493853
theorem B3224573 : Blo 940584 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B1592831 : Blo 940584 1592831 := bstep (se 1 (by rfl) ⟨1194623, by rfl⟩ : syracuseStep 1592831 = 2389247) B2389247
theorem B1593337 : Blo 940584 1593337 := bstep (se 2 (by rfl) ⟨597501, by rfl⟩ : syracuseStep 1593337 = 1195003) B1195003
theorem B2118383 : Blo 940584 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B2118635 : Blo 940584 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B2382119 : Blo 940584 2382119 := bstep (se 1 (by rfl) ⟨1786589, by rfl⟩ : syracuseStep 2382119 = 3573179) B3573179
theorem B940827 : Blo 940584 940827 := bstep (se 1 (by rfl) ⟨705620, by rfl⟩ : syracuseStep 940827 = 1411241) B1411241
theorem B16309279 : Blo 940584 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B941819 : Blo 940584 941819 := bstep (se 1 (by rfl) ⟨706364, by rfl⟩ : syracuseStep 941819 = 1412729) B1412729
theorem B941823 : Blo 940584 941823 := bstep (se 1 (by rfl) ⟨706367, by rfl⟩ : syracuseStep 941823 = 1412735) B1412735
theorem B2678665 : Blo 940584 2678665 := bstep (se 2 (by rfl) ⟨1004499, by rfl⟩ : syracuseStep 2678665 = 2008999) B2008999
theorem B941983 : Blo 940584 941983 := bstep (se 1 (by rfl) ⟨706487, by rfl⟩ : syracuseStep 941983 = 1412975) B1412975
theorem B942191 : Blo 940584 942191 := bstep (se 1 (by rfl) ⟨706643, by rfl⟩ : syracuseStep 942191 = 1413287) B1413287
theorem B942719 : Blo 940584 942719 := bstep (se 1 (by rfl) ⟨707039, by rfl⟩ : syracuseStep 942719 = 1414079) B1414079
theorem B2122793 : Blo 940584 2122793 := bstep (se 2 (by rfl) ⟨796047, by rfl⟩ : syracuseStep 2122793 = 1592095) B1592095
theorem B943359 : Blo 940584 943359 := bstep (se 1 (by rfl) ⟨707519, by rfl⟩ : syracuseStep 943359 = 1415039) B1415039
theorem B943551 : Blo 940584 943551 := bstep (se 1 (by rfl) ⟨707663, by rfl⟩ : syracuseStep 943551 = 1415327) B1415327
theorem B943599 : Blo 940584 943599 := bstep (se 1 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 943599 = 1415399) B1415399
theorem B943615 : Blo 940584 943615 := bstep (se 1 (by rfl) ⟨707711, by rfl⟩ : syracuseStep 943615 = 1415423) B1415423
theorem B943743 : Blo 940584 943743 := bstep (se 1 (by rfl) ⟨707807, by rfl⟩ : syracuseStep 943743 = 1415615) B1415615
theorem B943999 : Blo 940584 943999 := bstep (se 1 (by rfl) ⟨707999, by rfl⟩ : syracuseStep 943999 = 1415999) B1415999
theorem B20375549 : Blo 940584 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B2124755 : Blo 940584 2124755 := bstep (se 1 (by rfl) ⟨1593566, by rfl⟩ : syracuseStep 2124755 = 3187133) B3187133
theorem B8056361 : Blo 940584 8056361 := bstep (se 2 (by rfl) ⟨3021135, by rfl⟩ : syracuseStep 8056361 = 6042271) B6042271
theorem B2683439 : Blo 940584 2683439 := bstep (se 1 (by rfl) ⟨2012579, by rfl⟩ : syracuseStep 2683439 = 4025159) B4025159
theorem B13562477 : Blo 940584 13562477 := bstep (se 3 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 13562477 = 5085929) B5085929
theorem B4027259 : Blo 940584 4027259 := bstep (se 1 (by rfl) ⟨3020444, by rfl⟩ : syracuseStep 4027259 = 6040889) B6040889
theorem B2689487 : Blo 940584 2689487 := bstep (se 1 (by rfl) ⟨2017115, by rfl⟩ : syracuseStep 2689487 = 4034231) B4034231
theorem B1412255 : Blo 940584 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1412423 : Blo 940584 1412423 := bstep (se 1 (by rfl) ⟨1059317, by rfl⟩ : syracuseStep 1412423 = 2118635) B2118635
theorem B1415195 : Blo 940584 1415195 := bstep (se 1 (by rfl) ⟨1061396, by rfl⟩ : syracuseStep 1415195 = 2122793) B2122793
theorem B22943999 : Blo 940584 22943999 := bstep (se 1 (by rfl) ⟨17207999, by rfl⟩ : syracuseStep 22943999 = 34415999) B34415999
theorem B1416503 : Blo 940584 1416503 := bstep (se 1 (by rfl) ⟨1062377, by rfl⟩ : syracuseStep 1416503 = 2124755) B2124755
theorem B2011007 : Blo 940584 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B9057257 : Blo 940584 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B1061887 : Blo 940584 1061887 := bstep (se 1 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 1061887 = 1592831) B1592831
theorem B18364157 : Blo 940584 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B21772313 : Blo 940584 21772313 := bstep (se 2 (by rfl) ⟨8164617, by rfl⟩ : syracuseStep 21772313 = 16329235) B16329235
theorem B1588079 : Blo 940584 1588079 := bstep (se 1 (by rfl) ⟨1191059, by rfl⟩ : syracuseStep 1588079 = 2382119) B2382119
theorem B86982821 : Blo 940584 86982821 := bstep (se 4 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 86982821 = 16309279) B16309279
theorem B13583699 : Blo 940584 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B1788959 : Blo 940584 1788959 := bstep (se 1 (by rfl) ⟨1341719, by rfl⟩ : syracuseStep 1788959 = 2683439) B2683439
theorem B2149715 : Blo 940584 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B2119535 : Blo 940584 2119535 := bstep (se 1 (by rfl) ⟨1589651, by rfl⟩ : syracuseStep 2119535 = 3179303) B3179303
theorem B124148467 : Blo 940584 124148467 := bstep (se 1 (by rfl) ⟨93111350, by rfl⟩ : syracuseStep 124148467 = 186222701) B186222701
theorem B86990249 : Blo 940584 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B19324925 : Blo 940584 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B942831 : Blo 940584 942831 := bstep (se 1 (by rfl) ⟨707123, by rfl⟩ : syracuseStep 942831 = 1414247) B1414247
theorem B7169471 : Blo 940584 7169471 := bstep (se 1 (by rfl) ⟨5377103, by rfl⟩ : syracuseStep 7169471 = 10754207) B10754207
theorem B944367 : Blo 940584 944367 := bstep (se 1 (by rfl) ⟨708275, by rfl⟩ : syracuseStep 944367 = 1416551) B1416551
theorem B2124449 : Blo 940584 2124449 := bstep (se 2 (by rfl) ⟨796668, by rfl⟩ : syracuseStep 2124449 = 1593337) B1593337
theorem B5370907 : Blo 940584 5370907 := bstep (se 1 (by rfl) ⟨4028180, by rfl⟩ : syracuseStep 5370907 = 8056361) B8056361
theorem B9041651 : Blo 940584 9041651 := bstep (se 1 (by rfl) ⟨6781238, by rfl⟩ : syracuseStep 9041651 = 13562477) B13562477
theorem B2684839 : Blo 940584 2684839 := bstep (se 1 (by rfl) ⟨2013629, by rfl⟩ : syracuseStep 2684839 = 4027259) B4027259
theorem B3571553 : Blo 940584 3571553 := bstep (se 2 (by rfl) ⟨1339332, by rfl⟩ : syracuseStep 3571553 = 2678665) B2678665
theorem B1413023 : Blo 940584 1413023 := bstep (se 1 (by rfl) ⟨1059767, by rfl⟩ : syracuseStep 1413023 = 2119535) B2119535
theorem B12883283 : Blo 940584 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B1415849 : Blo 940584 1415849 := bstep (se 2 (by rfl) ⟨530943, by rfl⟩ : syracuseStep 1415849 = 1061887) B1061887
theorem B1416299 : Blo 940584 1416299 := bstep (se 1 (by rfl) ⟨1062224, by rfl⟩ : syracuseStep 1416299 = 2124449) B2124449
theorem B3579785 : Blo 940584 3579785 := bstep (se 2 (by rfl) ⟨1342419, by rfl⟩ : syracuseStep 3579785 = 2684839) B2684839
theorem B6038171 : Blo 940584 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B1058719 : Blo 940584 1058719 := bstep (se 1 (by rfl) ⟨794039, by rfl⟩ : syracuseStep 1058719 = 1588079) B1588079
theorem B9055799 : Blo 940584 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B1192639 : Blo 940584 1192639 := bstep (se 1 (by rfl) ⟨894479, by rfl⟩ : syracuseStep 1192639 = 1788959) B1788959
theorem B7161209 : Blo 940584 7161209 := bstep (se 2 (by rfl) ⟨2685453, by rfl⟩ : syracuseStep 7161209 = 5370907) B5370907
theorem B165531289 : Blo 940584 165531289 := bstep (se 2 (by rfl) ⟨62074233, by rfl⟩ : syracuseStep 165531289 = 124148467) B124148467
theorem B12242771 : Blo 940584 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B5362685 : Blo 940584 5362685 := bstep (se 3 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 5362685 = 2011007) B2011007
theorem B2381035 : Blo 940584 2381035 := bstep (se 1 (by rfl) ⟨1785776, by rfl⟩ : syracuseStep 2381035 = 3571553) B3571553
theorem B57988547 : Blo 940584 57988547 := bstep (se 1 (by rfl) ⟨43491410, by rfl⟩ : syracuseStep 57988547 = 86982821) B86982821
theorem B1792991 : Blo 940584 1792991 := bstep (se 1 (by rfl) ⟨1344743, by rfl⟩ : syracuseStep 1792991 = 2689487) B2689487
theorem B941503 : Blo 940584 941503 := bstep (se 1 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 941503 = 1412255) B1412255
theorem B941615 : Blo 940584 941615 := bstep (se 1 (by rfl) ⟨706211, by rfl⟩ : syracuseStep 941615 = 1412423) B1412423
theorem B1433143 : Blo 940584 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B943463 : Blo 940584 943463 := bstep (se 1 (by rfl) ⟨707597, by rfl⟩ : syracuseStep 943463 = 1415195) B1415195
theorem B15295999 : Blo 940584 15295999 := bstep (se 1 (by rfl) ⟨11471999, by rfl⟩ : syracuseStep 15295999 = 22943999) B22943999
theorem B944335 : Blo 940584 944335 := bstep (se 1 (by rfl) ⟨708251, by rfl⟩ : syracuseStep 944335 = 1416503) B1416503
theorem B57993499 : Blo 940584 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B4779647 : Blo 940584 4779647 := bstep (se 1 (by rfl) ⟨3584735, by rfl⟩ : syracuseStep 4779647 = 7169471) B7169471
theorem B6027767 : Blo 940584 6027767 := bstep (se 1 (by rfl) ⟨4520825, by rfl⟩ : syracuseStep 6027767 = 9041651) B9041651
theorem B14514875 : Blo 940584 14514875 := bstep (se 1 (by rfl) ⟨10886156, by rfl⟩ : syracuseStep 14514875 = 21772313) B21772313
theorem B1411625 : Blo 940584 1411625 := bstep (se 2 (by rfl) ⟨529359, by rfl⟩ : syracuseStep 1411625 = 1058719) B1058719
theorem B8161847 : Blo 940584 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B3575123 : Blo 940584 3575123 := bstep (se 1 (by rfl) ⟨2681342, by rfl⟩ : syracuseStep 3575123 = 5362685) B5362685
theorem B8588855 : Blo 940584 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B6037199 : Blo 940584 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B3186431 : Blo 940584 3186431 := bstep (se 1 (by rfl) ⟨2389823, by rfl⟩ : syracuseStep 3186431 = 4779647) B4779647
theorem B7643429 : Blo 940584 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B9676583 : Blo 940584 9676583 := bstep (se 1 (by rfl) ⟨7257437, by rfl⟩ : syracuseStep 9676583 = 14514875) B14514875
theorem B20394665 : Blo 940584 20394665 := bstep (se 2 (by rfl) ⟨7647999, by rfl⟩ : syracuseStep 20394665 = 15295999) B15295999
theorem B1195327 : Blo 940584 1195327 := bstep (se 1 (by rfl) ⟨896495, by rfl⟩ : syracuseStep 1195327 = 1792991) B1792991
theorem B220708385 : Blo 940584 220708385 := bstep (se 2 (by rfl) ⟨82765644, by rfl⟩ : syracuseStep 220708385 = 165531289) B165531289
theorem B1590185 : Blo 940584 1590185 := bstep (se 2 (by rfl) ⟨596319, by rfl⟩ : syracuseStep 1590185 = 1192639) B1192639
theorem B4018511 : Blo 940584 4018511 := bstep (se 1 (by rfl) ⟨3013883, by rfl⟩ : syracuseStep 4018511 = 6027767) B6027767
theorem B4774139 : Blo 940584 4774139 := bstep (se 1 (by rfl) ⟨3580604, by rfl⟩ : syracuseStep 4774139 = 7161209) B7161209
theorem B942015 : Blo 940584 942015 := bstep (se 1 (by rfl) ⟨706511, by rfl⟩ : syracuseStep 942015 = 1413023) B1413023
theorem B77324665 : Blo 940584 77324665 := bstep (se 2 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 77324665 = 57993499) B57993499
theorem B38659031 : Blo 940584 38659031 := bstep (se 1 (by rfl) ⟨28994273, by rfl⟩ : syracuseStep 38659031 = 57988547) B57988547
theorem B943899 : Blo 940584 943899 := bstep (se 1 (by rfl) ⟨707924, by rfl⟩ : syracuseStep 943899 = 1415849) B1415849
theorem B944199 : Blo 940584 944199 := bstep (se 1 (by rfl) ⟨708149, by rfl⟩ : syracuseStep 944199 = 1416299) B1416299
theorem B2386523 : Blo 940584 2386523 := bstep (se 1 (by rfl) ⟨1789892, by rfl⟩ : syracuseStep 2386523 = 3579785) B3579785
theorem B4025447 : Blo 940584 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B3174713 : Blo 940584 3174713 := bstep (se 2 (by rfl) ⟨1190517, by rfl⟩ : syracuseStep 3174713 = 2381035) B2381035
theorem B5441231 : Blo 940584 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B3182759 : Blo 940584 3182759 := bstep (se 1 (by rfl) ⟨2387069, by rfl⟩ : syracuseStep 3182759 = 4774139) B4774139
theorem B147138923 : Blo 940584 147138923 := bstep (se 1 (by rfl) ⟨110354192, by rfl⟩ : syracuseStep 147138923 = 220708385) B220708385
theorem B103099553 : Blo 940584 103099553 := bstep (se 2 (by rfl) ⟨38662332, by rfl⟩ : syracuseStep 103099553 = 77324665) B77324665
theorem B1060123 : Blo 940584 1060123 := bstep (se 1 (by rfl) ⟨795092, by rfl⟩ : syracuseStep 1060123 = 1590185) B1590185
theorem B5095619 : Blo 940584 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B25772687 : Blo 940584 25772687 := bstep (se 1 (by rfl) ⟨19329515, by rfl⟩ : syracuseStep 25772687 = 38659031) B38659031
theorem B1591015 : Blo 940584 1591015 := bstep (se 1 (by rfl) ⟨1193261, by rfl⟩ : syracuseStep 1591015 = 2386523) B2386523
theorem B2116475 : Blo 940584 2116475 := bstep (se 1 (by rfl) ⟨1587356, by rfl⟩ : syracuseStep 2116475 = 3174713) B3174713
theorem B1593769 : Blo 940584 1593769 := bstep (se 2 (by rfl) ⟨597663, by rfl⟩ : syracuseStep 1593769 = 1195327) B1195327
theorem B941083 : Blo 940584 941083 := bstep (se 1 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 941083 = 1411625) B1411625
theorem B2383415 : Blo 940584 2383415 := bstep (se 1 (by rfl) ⟨1787561, by rfl⟩ : syracuseStep 2383415 = 3575123) B3575123
theorem B5725903 : Blo 940584 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B2679007 : Blo 940584 2679007 := bstep (se 1 (by rfl) ⟨2009255, by rfl⟩ : syracuseStep 2679007 = 4018511) B4018511
theorem B4024799 : Blo 940584 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B2124287 : Blo 940584 2124287 := bstep (se 1 (by rfl) ⟨1593215, by rfl⟩ : syracuseStep 2124287 = 3186431) B3186431
theorem B6451055 : Blo 940584 6451055 := bstep (se 1 (by rfl) ⟨4838291, by rfl⟩ : syracuseStep 6451055 = 9676583) B9676583
theorem B2683631 : Blo 940584 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B13596443 : Blo 940584 13596443 := bstep (se 1 (by rfl) ⟨10197332, by rfl⟩ : syracuseStep 13596443 = 20394665) B20394665
theorem B3572009 : Blo 940584 3572009 := bstep (se 2 (by rfl) ⟨1339503, by rfl⟩ : syracuseStep 3572009 = 2679007) B2679007
theorem B1410983 : Blo 940584 1410983 := bstep (se 1 (by rfl) ⟨1058237, by rfl⟩ : syracuseStep 1410983 = 2116475) B2116475
theorem B1413497 : Blo 940584 1413497 := bstep (se 2 (by rfl) ⟨530061, by rfl⟩ : syracuseStep 1413497 = 1060123) B1060123
theorem B1416191 : Blo 940584 1416191 := bstep (se 1 (by rfl) ⟨1062143, by rfl⟩ : syracuseStep 1416191 = 2124287) B2124287
theorem B4300703 : Blo 940584 4300703 := bstep (se 1 (by rfl) ⟨3225527, by rfl⟩ : syracuseStep 4300703 = 6451055) B6451055
theorem B17181791 : Blo 940584 17181791 := bstep (se 1 (by rfl) ⟨12886343, by rfl⟩ : syracuseStep 17181791 = 25772687) B25772687
theorem B7156349 : Blo 940584 7156349 := bstep (se 3 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 7156349 = 2683631) B2683631
theorem B1588943 : Blo 940584 1588943 := bstep (se 1 (by rfl) ⟨1191707, by rfl⟩ : syracuseStep 1588943 = 2383415) B2383415
theorem B98092615 : Blo 940584 98092615 := bstep (se 1 (by rfl) ⟨73569461, by rfl⟩ : syracuseStep 98092615 = 147138923) B147138923
theorem B68733035 : Blo 940584 68733035 := bstep (se 1 (by rfl) ⟨51549776, by rfl⟩ : syracuseStep 68733035 = 103099553) B103099553
theorem B9064295 : Blo 940584 9064295 := bstep (se 1 (by rfl) ⟨6798221, by rfl⟩ : syracuseStep 9064295 = 13596443) B13596443
theorem B3397079 : Blo 940584 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B3627487 : Blo 940584 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B2121353 : Blo 940584 2121353 := bstep (se 2 (by rfl) ⟨795507, by rfl⟩ : syracuseStep 2121353 = 1591015) B1591015
theorem B2121839 : Blo 940584 2121839 := bstep (se 1 (by rfl) ⟨1591379, by rfl⟩ : syracuseStep 2121839 = 3182759) B3182759
theorem B2125025 : Blo 940584 2125025 := bstep (se 2 (by rfl) ⟨796884, by rfl⟩ : syracuseStep 2125025 = 1593769) B1593769
theorem B2683199 : Blo 940584 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B7634537 : Blo 940584 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B2264719 : Blo 940584 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B1414235 : Blo 940584 1414235 := bstep (se 1 (by rfl) ⟨1060676, by rfl⟩ : syracuseStep 1414235 = 2121353) B2121353
theorem B1414559 : Blo 940584 1414559 := bstep (se 1 (by rfl) ⟨1060919, by rfl⟩ : syracuseStep 1414559 = 2121839) B2121839
theorem B1416683 : Blo 940584 1416683 := bstep (se 1 (by rfl) ⟨1062512, by rfl⟩ : syracuseStep 1416683 = 2125025) B2125025
theorem B5089691 : Blo 940584 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B1059295 : Blo 940584 1059295 := bstep (se 1 (by rfl) ⟨794471, by rfl⟩ : syracuseStep 1059295 = 1588943) B1588943
theorem B45822023 : Blo 940584 45822023 := bstep (se 1 (by rfl) ⟨34366517, by rfl⟩ : syracuseStep 45822023 = 68733035) B68733035
theorem B130790153 : Blo 940584 130790153 := bstep (se 2 (by rfl) ⟨49046307, by rfl⟩ : syracuseStep 130790153 = 98092615) B98092615
theorem B19346597 : Blo 940584 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B6042863 : Blo 940584 6042863 := bstep (se 1 (by rfl) ⟨4532147, by rfl⟩ : syracuseStep 6042863 = 9064295) B9064295
theorem B2867135 : Blo 940584 2867135 := bstep (se 1 (by rfl) ⟨2150351, by rfl⟩ : syracuseStep 2867135 = 4300703) B4300703
theorem B11454527 : Blo 940584 11454527 := bstep (se 1 (by rfl) ⟨8590895, by rfl⟩ : syracuseStep 11454527 = 17181791) B17181791
theorem B1788799 : Blo 940584 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B4770899 : Blo 940584 4770899 := bstep (se 1 (by rfl) ⟨3578174, by rfl⟩ : syracuseStep 4770899 = 7156349) B7156349
theorem B2381339 : Blo 940584 2381339 := bstep (se 1 (by rfl) ⟨1786004, by rfl⟩ : syracuseStep 2381339 = 3572009) B3572009
theorem B940655 : Blo 940584 940655 := bstep (se 1 (by rfl) ⟨705491, by rfl⟩ : syracuseStep 940655 = 1410983) B1410983
theorem B942331 : Blo 940584 942331 := bstep (se 1 (by rfl) ⟨706748, by rfl⟩ : syracuseStep 942331 = 1413497) B1413497
theorem B944127 : Blo 940584 944127 := bstep (se 1 (by rfl) ⟨708095, by rfl⟩ : syracuseStep 944127 = 1416191) B1416191
theorem B7636351 : Blo 940584 7636351 := bstep (se 1 (by rfl) ⟨5727263, by rfl⟩ : syracuseStep 7636351 = 11454527) B11454527
theorem B3180599 : Blo 940584 3180599 := bstep (se 1 (by rfl) ⟨2385449, by rfl⟩ : syracuseStep 3180599 = 4770899) B4770899
theorem B1412393 : Blo 940584 1412393 := bstep (se 2 (by rfl) ⟨529647, by rfl⟩ : syracuseStep 1412393 = 1059295) B1059295
theorem B3019625 : Blo 940584 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B30548015 : Blo 940584 30548015 := bstep (se 1 (by rfl) ⟨22911011, by rfl⟩ : syracuseStep 30548015 = 45822023) B45822023
theorem B7645693 : Blo 940584 7645693 := bstep (se 3 (by rfl) ⟨1433567, by rfl⟩ : syracuseStep 7645693 = 2867135) B2867135
theorem B1587559 : Blo 940584 1587559 := bstep (se 1 (by rfl) ⟨1190669, by rfl⟩ : syracuseStep 1587559 = 2381339) B2381339
theorem B3393127 : Blo 940584 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B12897731 : Blo 940584 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B942823 : Blo 940584 942823 := bstep (se 1 (by rfl) ⟨707117, by rfl⟩ : syracuseStep 942823 = 1414235) B1414235
theorem B943039 : Blo 940584 943039 := bstep (se 1 (by rfl) ⟨707279, by rfl⟩ : syracuseStep 943039 = 1414559) B1414559
theorem B2385065 : Blo 940584 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B944455 : Blo 940584 944455 := bstep (se 1 (by rfl) ⟨708341, by rfl⟩ : syracuseStep 944455 = 1416683) B1416683
theorem B87193435 : Blo 940584 87193435 := bstep (se 1 (by rfl) ⟨65395076, by rfl⟩ : syracuseStep 87193435 = 130790153) B130790153
theorem B4028575 : Blo 940584 4028575 := bstep (se 1 (by rfl) ⟨3021431, by rfl⟩ : syracuseStep 4028575 = 6042863) B6042863
theorem B4524169 : Blo 940584 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B10194257 : Blo 940584 10194257 := bstep (se 2 (by rfl) ⟨3822846, by rfl⟩ : syracuseStep 10194257 = 7645693) B7645693
theorem B8598487 : Blo 940584 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B2013083 : Blo 940584 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B20365343 : Blo 940584 20365343 := bstep (se 1 (by rfl) ⟨15274007, by rfl⟩ : syracuseStep 20365343 = 30548015) B30548015
theorem B1590043 : Blo 940584 1590043 := bstep (se 1 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 1590043 = 2385065) B2385065
theorem B2116745 : Blo 940584 2116745 := bstep (se 2 (by rfl) ⟨793779, by rfl⟩ : syracuseStep 2116745 = 1587559) B1587559
theorem B2120399 : Blo 940584 2120399 := bstep (se 1 (by rfl) ⟨1590299, by rfl⟩ : syracuseStep 2120399 = 3180599) B3180599
theorem B10181801 : Blo 940584 10181801 := bstep (se 2 (by rfl) ⟨3818175, by rfl⟩ : syracuseStep 10181801 = 7636351) B7636351
theorem B941595 : Blo 940584 941595 := bstep (se 1 (by rfl) ⟨706196, by rfl⟩ : syracuseStep 941595 = 1412393) B1412393
theorem B116257913 : Blo 940584 116257913 := bstep (se 2 (by rfl) ⟨43596717, by rfl⟩ : syracuseStep 116257913 = 87193435) B87193435
theorem B5371433 : Blo 940584 5371433 := bstep (se 2 (by rfl) ⟨2014287, by rfl⟩ : syracuseStep 5371433 = 4028575) B4028575
theorem B1411163 : Blo 940584 1411163 := bstep (se 1 (by rfl) ⟨1058372, by rfl⟩ : syracuseStep 1411163 = 2116745) B2116745
theorem B6032225 : Blo 940584 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B1413599 : Blo 940584 1413599 := bstep (se 1 (by rfl) ⟨1060199, by rfl⟩ : syracuseStep 1413599 = 2120399) B2120399
theorem B77505275 : Blo 940584 77505275 := bstep (se 1 (by rfl) ⟨58128956, by rfl⟩ : syracuseStep 77505275 = 116257913) B116257913
theorem B3580955 : Blo 940584 3580955 := bstep (se 1 (by rfl) ⟨2685716, by rfl⟩ : syracuseStep 3580955 = 5371433) B5371433
theorem B13576895 : Blo 940584 13576895 := bstep (se 1 (by rfl) ⟨10182671, by rfl⟩ : syracuseStep 13576895 = 20365343) B20365343
theorem B6796171 : Blo 940584 6796171 := bstep (se 1 (by rfl) ⟨5097128, by rfl⟩ : syracuseStep 6796171 = 10194257) B10194257
theorem B27151469 : Blo 940584 27151469 := bstep (se 3 (by rfl) ⟨5090900, by rfl⟩ : syracuseStep 27151469 = 10181801) B10181801
theorem B2120057 : Blo 940584 2120057 := bstep (se 2 (by rfl) ⟨795021, by rfl⟩ : syracuseStep 2120057 = 1590043) B1590043
theorem B11464649 : Blo 940584 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B1342055 : Blo 940584 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B1413371 : Blo 940584 1413371 := bstep (se 1 (by rfl) ⟨1060028, by rfl⟩ : syracuseStep 1413371 = 2120057) B2120057
theorem B3578813 : Blo 940584 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B9051263 : Blo 940584 9051263 := bstep (se 1 (by rfl) ⟨6788447, by rfl⟩ : syracuseStep 9051263 = 13576895) B13576895
theorem B7643099 : Blo 940584 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B18100979 : Blo 940584 18100979 := bstep (se 1 (by rfl) ⟨13575734, by rfl⟩ : syracuseStep 18100979 = 27151469) B27151469
theorem B9061561 : Blo 940584 9061561 := bstep (se 2 (by rfl) ⟨3398085, by rfl⟩ : syracuseStep 9061561 = 6796171) B6796171
theorem B940775 : Blo 940584 940775 := bstep (se 1 (by rfl) ⟨705581, by rfl⟩ : syracuseStep 940775 = 1411163) B1411163
theorem B4021483 : Blo 940584 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B942399 : Blo 940584 942399 := bstep (se 1 (by rfl) ⟨706799, by rfl⟩ : syracuseStep 942399 = 1413599) B1413599
theorem B51670183 : Blo 940584 51670183 := bstep (se 1 (by rfl) ⟨38752637, by rfl⟩ : syracuseStep 51670183 = 77505275) B77505275
theorem B2387303 : Blo 940584 2387303 := bstep (se 1 (by rfl) ⟨1790477, by rfl⟩ : syracuseStep 2387303 = 3580955) B3580955
theorem B6034175 : Blo 940584 6034175 := bstep (se 1 (by rfl) ⟨4525631, by rfl⟩ : syracuseStep 6034175 = 9051263) B9051263
theorem B12067319 : Blo 940584 12067319 := bstep (se 1 (by rfl) ⟨9050489, by rfl⟩ : syracuseStep 12067319 = 18100979) B18100979
theorem B68893577 : Blo 940584 68893577 := bstep (se 2 (by rfl) ⟨25835091, by rfl⟩ : syracuseStep 68893577 = 51670183) B51670183
theorem B5095399 : Blo 940584 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B1591535 : Blo 940584 1591535 := bstep (se 1 (by rfl) ⟨1193651, by rfl⟩ : syracuseStep 1591535 = 2387303) B2387303
theorem B5361977 : Blo 940584 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B12082081 : Blo 940584 12082081 := bstep (se 2 (by rfl) ⟨4530780, by rfl⟩ : syracuseStep 12082081 = 9061561) B9061561
theorem B942247 : Blo 940584 942247 := bstep (se 1 (by rfl) ⟨706685, by rfl⟩ : syracuseStep 942247 = 1413371) B1413371
theorem B2385875 : Blo 940584 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B3574651 : Blo 940584 3574651 := bstep (se 1 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 3574651 = 5361977) B5361977
theorem B6793865 : Blo 940584 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B1061023 : Blo 940584 1061023 := bstep (se 1 (by rfl) ⟨795767, by rfl⟩ : syracuseStep 1061023 = 1591535) B1591535
theorem B8044879 : Blo 940584 8044879 := bstep (se 1 (by rfl) ⟨6033659, by rfl⟩ : syracuseStep 8044879 = 12067319) B12067319
theorem B1590583 : Blo 940584 1590583 := bstep (se 1 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 1590583 = 2385875) B2385875
theorem B16109441 : Blo 940584 16109441 := bstep (se 2 (by rfl) ⟨6041040, by rfl⟩ : syracuseStep 16109441 = 12082081) B12082081
theorem B45929051 : Blo 940584 45929051 := bstep (se 1 (by rfl) ⟨34446788, by rfl⟩ : syracuseStep 45929051 = 68893577) B68893577
theorem B4022783 : Blo 940584 4022783 := bstep (se 1 (by rfl) ⟨3017087, by rfl⟩ : syracuseStep 4022783 = 6034175) B6034175
theorem B1414697 : Blo 940584 1414697 := bstep (se 2 (by rfl) ⟨530511, by rfl⟩ : syracuseStep 1414697 = 1061023) B1061023
theorem B4529243 : Blo 940584 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B10726505 : Blo 940584 10726505 := bstep (se 2 (by rfl) ⟨4022439, by rfl⟩ : syracuseStep 10726505 = 8044879) B8044879
theorem B30619367 : Blo 940584 30619367 := bstep (se 1 (by rfl) ⟨22964525, by rfl⟩ : syracuseStep 30619367 = 45929051) B45929051
theorem B4766201 : Blo 940584 4766201 := bstep (se 2 (by rfl) ⟨1787325, by rfl⟩ : syracuseStep 4766201 = 3574651) B3574651
theorem B2120777 : Blo 940584 2120777 := bstep (se 2 (by rfl) ⟨795291, by rfl⟩ : syracuseStep 2120777 = 1590583) B1590583
theorem B10739627 : Blo 940584 10739627 := bstep (se 1 (by rfl) ⟨8054720, by rfl⟩ : syracuseStep 10739627 = 16109441) B16109441
theorem B2681855 : Blo 940584 2681855 := bstep (se 1 (by rfl) ⟨2011391, by rfl⟩ : syracuseStep 2681855 = 4022783) B4022783
theorem B1413851 : Blo 940584 1413851 := bstep (se 1 (by rfl) ⟨1060388, by rfl⟩ : syracuseStep 1413851 = 2120777) B2120777
theorem B7151003 : Blo 940584 7151003 := bstep (se 1 (by rfl) ⟨5363252, by rfl⟩ : syracuseStep 7151003 = 10726505) B10726505
theorem B7159751 : Blo 940584 7159751 := bstep (se 1 (by rfl) ⟨5369813, by rfl⟩ : syracuseStep 7159751 = 10739627) B10739627
theorem B1787903 : Blo 940584 1787903 := bstep (se 1 (by rfl) ⟨1340927, by rfl⟩ : syracuseStep 1787903 = 2681855) B2681855
theorem B12077981 : Blo 940584 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B943131 : Blo 940584 943131 := bstep (se 1 (by rfl) ⟨707348, by rfl⟩ : syracuseStep 943131 = 1414697) B1414697
theorem B20412911 : Blo 940584 20412911 := bstep (se 1 (by rfl) ⟨15309683, by rfl⟩ : syracuseStep 20412911 = 30619367) B30619367
theorem B3177467 : Blo 940584 3177467 := bstep (se 1 (by rfl) ⟨2383100, by rfl⟩ : syracuseStep 3177467 = 4766201) B4766201
theorem B13608607 : Blo 940584 13608607 := bstep (se 1 (by rfl) ⟨10206455, by rfl⟩ : syracuseStep 13608607 = 20412911) B20412911
theorem B1191935 : Blo 940584 1191935 := bstep (se 1 (by rfl) ⟨893951, by rfl⟩ : syracuseStep 1191935 = 1787903) B1787903
theorem B4767335 : Blo 940584 4767335 := bstep (se 1 (by rfl) ⟨3575501, by rfl⟩ : syracuseStep 4767335 = 7151003) B7151003
theorem B2118311 : Blo 940584 2118311 := bstep (se 1 (by rfl) ⟨1588733, by rfl⟩ : syracuseStep 2118311 = 3177467) B3177467
theorem B4773167 : Blo 940584 4773167 := bstep (se 1 (by rfl) ⟨3579875, by rfl⟩ : syracuseStep 4773167 = 7159751) B7159751
theorem B8051987 : Blo 940584 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B942567 : Blo 940584 942567 := bstep (se 1 (by rfl) ⟨706925, by rfl⟩ : syracuseStep 942567 = 1413851) B1413851
theorem B1412207 : Blo 940584 1412207 := bstep (se 1 (by rfl) ⟨1059155, by rfl⟩ : syracuseStep 1412207 = 2118311) B2118311
theorem B3182111 : Blo 940584 3182111 := bstep (se 1 (by rfl) ⟨2386583, by rfl⟩ : syracuseStep 3182111 = 4773167) B4773167
theorem B18144809 : Blo 940584 18144809 := bstep (se 2 (by rfl) ⟨6804303, by rfl⟩ : syracuseStep 18144809 = 13608607) B13608607
theorem B5367991 : Blo 940584 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B3178223 : Blo 940584 3178223 := bstep (se 1 (by rfl) ⟨2383667, by rfl⟩ : syracuseStep 3178223 = 4767335) B4767335
theorem B3178493 : Blo 940584 3178493 := bstep (se 3 (by rfl) ⟨595967, by rfl⟩ : syracuseStep 3178493 = 1191935) B1191935
theorem B12096539 : Blo 940584 12096539 := bstep (se 1 (by rfl) ⟨9072404, by rfl⟩ : syracuseStep 12096539 = 18144809) B18144809
theorem B7157321 : Blo 940584 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B2118815 : Blo 940584 2118815 := bstep (se 1 (by rfl) ⟨1589111, by rfl⟩ : syracuseStep 2118815 = 3178223) B3178223
theorem B2118995 : Blo 940584 2118995 := bstep (se 1 (by rfl) ⟨1589246, by rfl⟩ : syracuseStep 2118995 = 3178493) B3178493
theorem B941471 : Blo 940584 941471 := bstep (se 1 (by rfl) ⟨706103, by rfl⟩ : syracuseStep 941471 = 1412207) B1412207
theorem B2121407 : Blo 940584 2121407 := bstep (se 1 (by rfl) ⟨1591055, by rfl⟩ : syracuseStep 2121407 = 3182111) B3182111
theorem B8064359 : Blo 940584 8064359 := bstep (se 1 (by rfl) ⟨6048269, by rfl⟩ : syracuseStep 8064359 = 12096539) B12096539
theorem B1412543 : Blo 940584 1412543 := bstep (se 1 (by rfl) ⟨1059407, by rfl⟩ : syracuseStep 1412543 = 2118815) B2118815
theorem B1412663 : Blo 940584 1412663 := bstep (se 1 (by rfl) ⟨1059497, by rfl⟩ : syracuseStep 1412663 = 2118995) B2118995
theorem B1414271 : Blo 940584 1414271 := bstep (se 1 (by rfl) ⟨1060703, by rfl⟩ : syracuseStep 1414271 = 2121407) B2121407
theorem B4771547 : Blo 940584 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B5376239 : Blo 940584 5376239 := bstep (se 1 (by rfl) ⟨4032179, by rfl⟩ : syracuseStep 5376239 = 8064359) B8064359
theorem B3181031 : Blo 940584 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B941695 : Blo 940584 941695 := bstep (se 1 (by rfl) ⟨706271, by rfl⟩ : syracuseStep 941695 = 1412543) B1412543
theorem B941775 : Blo 940584 941775 := bstep (se 1 (by rfl) ⟨706331, by rfl⟩ : syracuseStep 941775 = 1412663) B1412663
theorem B942847 : Blo 940584 942847 := bstep (se 1 (by rfl) ⟨707135, by rfl⟩ : syracuseStep 942847 = 1414271) B1414271
theorem B3584159 : Blo 940584 3584159 := bstep (se 1 (by rfl) ⟨2688119, by rfl⟩ : syracuseStep 3584159 = 5376239) B5376239
theorem B2120687 : Blo 940584 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B1413791 : Blo 940584 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B2389439 : Blo 940584 2389439 := bstep (se 1 (by rfl) ⟨1792079, by rfl⟩ : syracuseStep 2389439 = 3584159) B3584159
theorem B1592959 : Blo 940584 1592959 := bstep (se 1 (by rfl) ⟨1194719, by rfl⟩ : syracuseStep 1592959 = 2389439) B2389439
theorem B942527 : Blo 940584 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B2123945 : Blo 940584 2123945 := bstep (se 2 (by rfl) ⟨796479, by rfl⟩ : syracuseStep 2123945 = 1592959) B1592959
theorem B1415963 : Blo 940584 1415963 := bstep (se 1 (by rfl) ⟨1061972, by rfl⟩ : syracuseStep 1415963 = 2123945) B2123945
theorem B943975 : Blo 940584 943975 := bstep (se 1 (by rfl) ⟨707981, by rfl⟩ : syracuseStep 943975 = 1415963) B1415963

theorem C0 (j : ℕ) (h1 : 235146 ≤ j) (h2 : j ≤ 235845) : Blo 940584 (4 * j + 3) := by
  interval_cases j
  · exact B940587
  · exact B940591
  · exact B940595
  · exact B940599
  · exact B940603
  · exact B940607
  · exact B940611
  · exact B940615
  · exact B940619
  · exact B940623
  · exact B940627
  · exact B940631
  · exact B940635
  · exact B940639
  · exact B940643
  · exact B940647
  · exact B940651
  · exact B940655
  · exact B940659
  · exact B940663
  · exact B940667
  · exact B940671
  · exact B940675
  · exact B940679
  · exact B940683
  · exact B940687
  · exact B940691
  · exact B940695
  · exact B940699
  · exact B940703
  · exact B940707
  · exact B940711
  · exact B940715
  · exact B940719
  · exact B940723
  · exact B940727
  · exact B940731
  · exact B940735
  · exact B940739
  · exact B940743
  · exact B940747
  · exact B940751
  · exact B940755
  · exact B940759
  · exact B940763
  · exact B940767
  · exact B940771
  · exact B940775
  · exact B940779
  · exact B940783
  · exact B940787
  · exact B940791
  · exact B940795
  · exact B940799
  · exact B940803
  · exact B940807
  · exact B940811
  · exact B940815
  · exact B940819
  · exact B940823
  · exact B940827
  · exact B940831
  · exact B940835
  · exact B940839
  · exact B940843
  · exact B940847
  · exact B940851
  · exact B940855
  · exact B940859
  · exact B940863
  · exact B940867
  · exact B940871
  · exact B940875
  · exact B940879
  · exact B940883
  · exact B940887
  · exact B940891
  · exact B940895
  · exact B940899
  · exact B940903
  · exact B940907
  · exact B940911
  · exact B940915
  · exact B940919
  · exact B940923
  · exact B940927
  · exact B940931
  · exact B940935
  · exact B940939
  · exact B940943
  · exact B940947
  · exact B940951
  · exact B940955
  · exact B940959
  · exact B940963
  · exact B940967
  · exact B940971
  · exact B940975
  · exact B940979
  · exact B940983
  · exact B940987
  · exact B940991
  · exact B940995
  · exact B940999
  · exact B941003
  · exact B941007
  · exact B941011
  · exact B941015
  · exact B941019
  · exact B941023
  · exact B941027
  · exact B941031
  · exact B941035
  · exact B941039
  · exact B941043
  · exact B941047
  · exact B941051
  · exact B941055
  · exact B941059
  · exact B941063
  · exact B941067
  · exact B941071
  · exact B941075
  · exact B941079
  · exact B941083
  · exact B941087
  · exact B941091
  · exact B941095
  · exact B941099
  · exact B941103
  · exact B941107
  · exact B941111
  · exact B941115
  · exact B941119
  · exact B941123
  · exact B941127
  · exact B941131
  · exact B941135
  · exact B941139
  · exact B941143
  · exact B941147
  · exact B941151
  · exact B941155
  · exact B941159
  · exact B941163
  · exact B941167
  · exact B941171
  · exact B941175
  · exact B941179
  · exact B941183
  · exact B941187
  · exact B941191
  · exact B941195
  · exact B941199
  · exact B941203
  · exact B941207
  · exact B941211
  · exact B941215
  · exact B941219
  · exact B941223
  · exact B941227
  · exact B941231
  · exact B941235
  · exact B941239
  · exact B941243
  · exact B941247
  · exact B941251
  · exact B941255
  · exact B941259
  · exact B941263
  · exact B941267
  · exact B941271
  · exact B941275
  · exact B941279
  · exact B941283
  · exact B941287
  · exact B941291
  · exact B941295
  · exact B941299
  · exact B941303
  · exact B941307
  · exact B941311
  · exact B941315
  · exact B941319
  · exact B941323
  · exact B941327
  · exact B941331
  · exact B941335
  · exact B941339
  · exact B941343
  · exact B941347
  · exact B941351
  · exact B941355
  · exact B941359
  · exact B941363
  · exact B941367
  · exact B941371
  · exact B941375
  · exact B941379
  · exact B941383
  · exact B941387
  · exact B941391
  · exact B941395
  · exact B941399
  · exact B941403
  · exact B941407
  · exact B941411
  · exact B941415
  · exact B941419
  · exact B941423
  · exact B941427
  · exact B941431
  · exact B941435
  · exact B941439
  · exact B941443
  · exact B941447
  · exact B941451
  · exact B941455
  · exact B941459
  · exact B941463
  · exact B941467
  · exact B941471
  · exact B941475
  · exact B941479
  · exact B941483
  · exact B941487
  · exact B941491
  · exact B941495
  · exact B941499
  · exact B941503
  · exact B941507
  · exact B941511
  · exact B941515
  · exact B941519
  · exact B941523
  · exact B941527
  · exact B941531
  · exact B941535
  · exact B941539
  · exact B941543
  · exact B941547
  · exact B941551
  · exact B941555
  · exact B941559
  · exact B941563
  · exact B941567
  · exact B941571
  · exact B941575
  · exact B941579
  · exact B941583
  · exact B941587
  · exact B941591
  · exact B941595
  · exact B941599
  · exact B941603
  · exact B941607
  · exact B941611
  · exact B941615
  · exact B941619
  · exact B941623
  · exact B941627
  · exact B941631
  · exact B941635
  · exact B941639
  · exact B941643
  · exact B941647
  · exact B941651
  · exact B941655
  · exact B941659
  · exact B941663
  · exact B941667
  · exact B941671
  · exact B941675
  · exact B941679
  · exact B941683
  · exact B941687
  · exact B941691
  · exact B941695
  · exact B941699
  · exact B941703
  · exact B941707
  · exact B941711
  · exact B941715
  · exact B941719
  · exact B941723
  · exact B941727
  · exact B941731
  · exact B941735
  · exact B941739
  · exact B941743
  · exact B941747
  · exact B941751
  · exact B941755
  · exact B941759
  · exact B941763
  · exact B941767
  · exact B941771
  · exact B941775
  · exact B941779
  · exact B941783
  · exact B941787
  · exact B941791
  · exact B941795
  · exact B941799
  · exact B941803
  · exact B941807
  · exact B941811
  · exact B941815
  · exact B941819
  · exact B941823
  · exact B941827
  · exact B941831
  · exact B941835
  · exact B941839
  · exact B941843
  · exact B941847
  · exact B941851
  · exact B941855
  · exact B941859
  · exact B941863
  · exact B941867
  · exact B941871
  · exact B941875
  · exact B941879
  · exact B941883
  · exact B941887
  · exact B941891
  · exact B941895
  · exact B941899
  · exact B941903
  · exact B941907
  · exact B941911
  · exact B941915
  · exact B941919
  · exact B941923
  · exact B941927
  · exact B941931
  · exact B941935
  · exact B941939
  · exact B941943
  · exact B941947
  · exact B941951
  · exact B941955
  · exact B941959
  · exact B941963
  · exact B941967
  · exact B941971
  · exact B941975
  · exact B941979
  · exact B941983
  · exact B941987
  · exact B941991
  · exact B941995
  · exact B941999
  · exact B942003
  · exact B942007
  · exact B942011
  · exact B942015
  · exact B942019
  · exact B942023
  · exact B942027
  · exact B942031
  · exact B942035
  · exact B942039
  · exact B942043
  · exact B942047
  · exact B942051
  · exact B942055
  · exact B942059
  · exact B942063
  · exact B942067
  · exact B942071
  · exact B942075
  · exact B942079
  · exact B942083
  · exact B942087
  · exact B942091
  · exact B942095
  · exact B942099
  · exact B942103
  · exact B942107
  · exact B942111
  · exact B942115
  · exact B942119
  · exact B942123
  · exact B942127
  · exact B942131
  · exact B942135
  · exact B942139
  · exact B942143
  · exact B942147
  · exact B942151
  · exact B942155
  · exact B942159
  · exact B942163
  · exact B942167
  · exact B942171
  · exact B942175
  · exact B942179
  · exact B942183
  · exact B942187
  · exact B942191
  · exact B942195
  · exact B942199
  · exact B942203
  · exact B942207
  · exact B942211
  · exact B942215
  · exact B942219
  · exact B942223
  · exact B942227
  · exact B942231
  · exact B942235
  · exact B942239
  · exact B942243
  · exact B942247
  · exact B942251
  · exact B942255
  · exact B942259
  · exact B942263
  · exact B942267
  · exact B942271
  · exact B942275
  · exact B942279
  · exact B942283
  · exact B942287
  · exact B942291
  · exact B942295
  · exact B942299
  · exact B942303
  · exact B942307
  · exact B942311
  · exact B942315
  · exact B942319
  · exact B942323
  · exact B942327
  · exact B942331
  · exact B942335
  · exact B942339
  · exact B942343
  · exact B942347
  · exact B942351
  · exact B942355
  · exact B942359
  · exact B942363
  · exact B942367
  · exact B942371
  · exact B942375
  · exact B942379
  · exact B942383
  · exact B942387
  · exact B942391
  · exact B942395
  · exact B942399
  · exact B942403
  · exact B942407
  · exact B942411
  · exact B942415
  · exact B942419
  · exact B942423
  · exact B942427
  · exact B942431
  · exact B942435
  · exact B942439
  · exact B942443
  · exact B942447
  · exact B942451
  · exact B942455
  · exact B942459
  · exact B942463
  · exact B942467
  · exact B942471
  · exact B942475
  · exact B942479
  · exact B942483
  · exact B942487
  · exact B942491
  · exact B942495
  · exact B942499
  · exact B942503
  · exact B942507
  · exact B942511
  · exact B942515
  · exact B942519
  · exact B942523
  · exact B942527
  · exact B942531
  · exact B942535
  · exact B942539
  · exact B942543
  · exact B942547
  · exact B942551
  · exact B942555
  · exact B942559
  · exact B942563
  · exact B942567
  · exact B942571
  · exact B942575
  · exact B942579
  · exact B942583
  · exact B942587
  · exact B942591
  · exact B942595
  · exact B942599
  · exact B942603
  · exact B942607
  · exact B942611
  · exact B942615
  · exact B942619
  · exact B942623
  · exact B942627
  · exact B942631
  · exact B942635
  · exact B942639
  · exact B942643
  · exact B942647
  · exact B942651
  · exact B942655
  · exact B942659
  · exact B942663
  · exact B942667
  · exact B942671
  · exact B942675
  · exact B942679
  · exact B942683
  · exact B942687
  · exact B942691
  · exact B942695
  · exact B942699
  · exact B942703
  · exact B942707
  · exact B942711
  · exact B942715
  · exact B942719
  · exact B942723
  · exact B942727
  · exact B942731
  · exact B942735
  · exact B942739
  · exact B942743
  · exact B942747
  · exact B942751
  · exact B942755
  · exact B942759
  · exact B942763
  · exact B942767
  · exact B942771
  · exact B942775
  · exact B942779
  · exact B942783
  · exact B942787
  · exact B942791
  · exact B942795
  · exact B942799
  · exact B942803
  · exact B942807
  · exact B942811
  · exact B942815
  · exact B942819
  · exact B942823
  · exact B942827
  · exact B942831
  · exact B942835
  · exact B942839
  · exact B942843
  · exact B942847
  · exact B942851
  · exact B942855
  · exact B942859
  · exact B942863
  · exact B942867
  · exact B942871
  · exact B942875
  · exact B942879
  · exact B942883
  · exact B942887
  · exact B942891
  · exact B942895
  · exact B942899
  · exact B942903
  · exact B942907
  · exact B942911
  · exact B942915
  · exact B942919
  · exact B942923
  · exact B942927
  · exact B942931
  · exact B942935
  · exact B942939
  · exact B942943
  · exact B942947
  · exact B942951
  · exact B942955
  · exact B942959
  · exact B942963
  · exact B942967
  · exact B942971
  · exact B942975
  · exact B942979
  · exact B942983
  · exact B942987
  · exact B942991
  · exact B942995
  · exact B942999
  · exact B943003
  · exact B943007
  · exact B943011
  · exact B943015
  · exact B943019
  · exact B943023
  · exact B943027
  · exact B943031
  · exact B943035
  · exact B943039
  · exact B943043
  · exact B943047
  · exact B943051
  · exact B943055
  · exact B943059
  · exact B943063
  · exact B943067
  · exact B943071
  · exact B943075
  · exact B943079
  · exact B943083
  · exact B943087
  · exact B943091
  · exact B943095
  · exact B943099
  · exact B943103
  · exact B943107
  · exact B943111
  · exact B943115
  · exact B943119
  · exact B943123
  · exact B943127
  · exact B943131
  · exact B943135
  · exact B943139
  · exact B943143
  · exact B943147
  · exact B943151
  · exact B943155
  · exact B943159
  · exact B943163
  · exact B943167
  · exact B943171
  · exact B943175
  · exact B943179
  · exact B943183
  · exact B943187
  · exact B943191
  · exact B943195
  · exact B943199
  · exact B943203
  · exact B943207
  · exact B943211
  · exact B943215
  · exact B943219
  · exact B943223
  · exact B943227
  · exact B943231
  · exact B943235
  · exact B943239
  · exact B943243
  · exact B943247
  · exact B943251
  · exact B943255
  · exact B943259
  · exact B943263
  · exact B943267
  · exact B943271
  · exact B943275
  · exact B943279
  · exact B943283
  · exact B943287
  · exact B943291
  · exact B943295
  · exact B943299
  · exact B943303
  · exact B943307
  · exact B943311
  · exact B943315
  · exact B943319
  · exact B943323
  · exact B943327
  · exact B943331
  · exact B943335
  · exact B943339
  · exact B943343
  · exact B943347
  · exact B943351
  · exact B943355
  · exact B943359
  · exact B943363
  · exact B943367
  · exact B943371
  · exact B943375
  · exact B943379
  · exact B943383

theorem C1 (j : ℕ) (h1 : 235846 ≤ j) (h2 : j ≤ 236145) : Blo 940584 (4 * j + 3) := by
  interval_cases j
  · exact B943387
  · exact B943391
  · exact B943395
  · exact B943399
  · exact B943403
  · exact B943407
  · exact B943411
  · exact B943415
  · exact B943419
  · exact B943423
  · exact B943427
  · exact B943431
  · exact B943435
  · exact B943439
  · exact B943443
  · exact B943447
  · exact B943451
  · exact B943455
  · exact B943459
  · exact B943463
  · exact B943467
  · exact B943471
  · exact B943475
  · exact B943479
  · exact B943483
  · exact B943487
  · exact B943491
  · exact B943495
  · exact B943499
  · exact B943503
  · exact B943507
  · exact B943511
  · exact B943515
  · exact B943519
  · exact B943523
  · exact B943527
  · exact B943531
  · exact B943535
  · exact B943539
  · exact B943543
  · exact B943547
  · exact B943551
  · exact B943555
  · exact B943559
  · exact B943563
  · exact B943567
  · exact B943571
  · exact B943575
  · exact B943579
  · exact B943583
  · exact B943587
  · exact B943591
  · exact B943595
  · exact B943599
  · exact B943603
  · exact B943607
  · exact B943611
  · exact B943615
  · exact B943619
  · exact B943623
  · exact B943627
  · exact B943631
  · exact B943635
  · exact B943639
  · exact B943643
  · exact B943647
  · exact B943651
  · exact B943655
  · exact B943659
  · exact B943663
  · exact B943667
  · exact B943671
  · exact B943675
  · exact B943679
  · exact B943683
  · exact B943687
  · exact B943691
  · exact B943695
  · exact B943699
  · exact B943703
  · exact B943707
  · exact B943711
  · exact B943715
  · exact B943719
  · exact B943723
  · exact B943727
  · exact B943731
  · exact B943735
  · exact B943739
  · exact B943743
  · exact B943747
  · exact B943751
  · exact B943755
  · exact B943759
  · exact B943763
  · exact B943767
  · exact B943771
  · exact B943775
  · exact B943779
  · exact B943783
  · exact B943787
  · exact B943791
  · exact B943795
  · exact B943799
  · exact B943803
  · exact B943807
  · exact B943811
  · exact B943815
  · exact B943819
  · exact B943823
  · exact B943827
  · exact B943831
  · exact B943835
  · exact B943839
  · exact B943843
  · exact B943847
  · exact B943851
  · exact B943855
  · exact B943859
  · exact B943863
  · exact B943867
  · exact B943871
  · exact B943875
  · exact B943879
  · exact B943883
  · exact B943887
  · exact B943891
  · exact B943895
  · exact B943899
  · exact B943903
  · exact B943907
  · exact B943911
  · exact B943915
  · exact B943919
  · exact B943923
  · exact B943927
  · exact B943931
  · exact B943935
  · exact B943939
  · exact B943943
  · exact B943947
  · exact B943951
  · exact B943955
  · exact B943959
  · exact B943963
  · exact B943967
  · exact B943971
  · exact B943975
  · exact B943979
  · exact B943983
  · exact B943987
  · exact B943991
  · exact B943995
  · exact B943999
  · exact B944003
  · exact B944007
  · exact B944011
  · exact B944015
  · exact B944019
  · exact B944023
  · exact B944027
  · exact B944031
  · exact B944035
  · exact B944039
  · exact B944043
  · exact B944047
  · exact B944051
  · exact B944055
  · exact B944059
  · exact B944063
  · exact B944067
  · exact B944071
  · exact B944075
  · exact B944079
  · exact B944083
  · exact B944087
  · exact B944091
  · exact B944095
  · exact B944099
  · exact B944103
  · exact B944107
  · exact B944111
  · exact B944115
  · exact B944119
  · exact B944123
  · exact B944127
  · exact B944131
  · exact B944135
  · exact B944139
  · exact B944143
  · exact B944147
  · exact B944151
  · exact B944155
  · exact B944159
  · exact B944163
  · exact B944167
  · exact B944171
  · exact B944175
  · exact B944179
  · exact B944183
  · exact B944187
  · exact B944191
  · exact B944195
  · exact B944199
  · exact B944203
  · exact B944207
  · exact B944211
  · exact B944215
  · exact B944219
  · exact B944223
  · exact B944227
  · exact B944231
  · exact B944235
  · exact B944239
  · exact B944243
  · exact B944247
  · exact B944251
  · exact B944255
  · exact B944259
  · exact B944263
  · exact B944267
  · exact B944271
  · exact B944275
  · exact B944279
  · exact B944283
  · exact B944287
  · exact B944291
  · exact B944295
  · exact B944299
  · exact B944303
  · exact B944307
  · exact B944311
  · exact B944315
  · exact B944319
  · exact B944323
  · exact B944327
  · exact B944331
  · exact B944335
  · exact B944339
  · exact B944343
  · exact B944347
  · exact B944351
  · exact B944355
  · exact B944359
  · exact B944363
  · exact B944367
  · exact B944371
  · exact B944375
  · exact B944379
  · exact B944383
  · exact B944387
  · exact B944391
  · exact B944395
  · exact B944399
  · exact B944403
  · exact B944407
  · exact B944411
  · exact B944415
  · exact B944419
  · exact B944423
  · exact B944427
  · exact B944431
  · exact B944435
  · exact B944439
  · exact B944443
  · exact B944447
  · exact B944451
  · exact B944455
  · exact B944459
  · exact B944463
  · exact B944467
  · exact B944471
  · exact B944475
  · exact B944479
  · exact B944483
  · exact B944487
  · exact B944491
  · exact B944495
  · exact B944499
  · exact B944503
  · exact B944507
  · exact B944511
  · exact B944515
  · exact B944519
  · exact B944523
  · exact B944527
  · exact B944531
  · exact B944535
  · exact B944539
  · exact B944543
  · exact B944547
  · exact B944551
  · exact B944555
  · exact B944559
  · exact B944563
  · exact B944567
  · exact B944571
  · exact B944575
  · exact B944579
  · exact B944583

theorem solution (m : ℕ) (hlo : 940584 ≤ m) (hhi : m ≤ 944584) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 235146 ≤ j := by omega
    have hj2 : j ≤ 236145 := by omega
    have hb : Blo 940584 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 235846 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
