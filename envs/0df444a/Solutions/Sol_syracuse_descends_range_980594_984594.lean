-- Prove2me | solution 1 for syracuse_descends_range_980594_984594
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:07.954117+00:00
-- url     : https://prove2.me/submissions/15a0ad49-fd63-4626-8653-118f7b70f150

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


theorem B1474565 : Blo 980594 1474565 := bbase (se 4 (by rfl) ⟨138240, by rfl⟩ : syracuseStep 1474565 = 276481) (by norm_num)
theorem B1867789 : Blo 980594 1867789 := bbase (se 3 (by rfl) ⟨350210, by rfl⟩ : syracuseStep 1867789 = 700421) (by norm_num)
theorem B1179673 : Blo 980594 1179673 := bbase (se 2 (by rfl) ⟨442377, by rfl⟩ : syracuseStep 1179673 = 884755) (by norm_num)
theorem B1474589 : Blo 980594 1474589 := bbase (se 3 (by rfl) ⟨276485, by rfl⟩ : syracuseStep 1474589 = 552971) (by norm_num)
theorem B3309605 : Blo 980594 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B1245233 : Blo 980594 1245233 := bbase (se 2 (by rfl) ⟨466962, by rfl⟩ : syracuseStep 1245233 = 933925) (by norm_num)
theorem B1474613 : Blo 980594 1474613 := bbase (se 5 (by rfl) ⟨69122, by rfl⟩ : syracuseStep 1474613 = 138245) (by norm_num)
theorem B1474637 : Blo 980594 1474637 := bbase (se 3 (by rfl) ⟨276494, by rfl⟩ : syracuseStep 1474637 = 552989) (by norm_num)
theorem B1572949 : Blo 980594 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1474661 : Blo 980594 1474661 := bbase (se 4 (by rfl) ⟨138249, by rfl⟩ : syracuseStep 1474661 = 276499) (by norm_num)
theorem B1245289 : Blo 980594 1245289 := bbase (se 2 (by rfl) ⟨466983, by rfl⟩ : syracuseStep 1245289 = 933967) (by norm_num)
theorem B1769597 : Blo 980594 1769597 := bbase (se 3 (by rfl) ⟨331799, by rfl⟩ : syracuseStep 1769597 = 663599) (by norm_num)
theorem B1474685 : Blo 980594 1474685 := bbase (se 3 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 1474685 = 553007) (by norm_num)
theorem B1474709 : Blo 980594 1474709 := bbase (se 6 (by rfl) ⟨34563, by rfl⟩ : syracuseStep 1474709 = 69127) (by norm_num)
theorem B1474733 : Blo 980594 1474733 := bbase (se 3 (by rfl) ⟨276512, by rfl⟩ : syracuseStep 1474733 = 553025) (by norm_num)
theorem B2359493 : Blo 980594 2359493 := bbase (se 4 (by rfl) ⟨221202, by rfl⟩ : syracuseStep 2359493 = 442405) (by norm_num)
theorem B1474757 : Blo 980594 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B1245385 : Blo 980594 1245385 := bbase (se 2 (by rfl) ⟨467019, by rfl⟩ : syracuseStep 1245385 = 934039) (by norm_num)
theorem B1474781 : Blo 980594 1474781 := bbase (se 3 (by rfl) ⟨276521, by rfl⟩ : syracuseStep 1474781 = 553043) (by norm_num)
theorem B1474805 : Blo 980594 1474805 := bbase (se 5 (by rfl) ⟨69131, by rfl⟩ : syracuseStep 1474805 = 138263) (by norm_num)
theorem B1474829 : Blo 980594 1474829 := bbase (se 3 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 1474829 = 553061) (by norm_num)
theorem B4981013 : Blo 980594 4981013 := bbase (se 6 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 4981013 = 233485) (by norm_num)
theorem B1474853 : Blo 980594 1474853 := bbase (se 4 (by rfl) ⟨138267, by rfl⟩ : syracuseStep 1474853 = 276535) (by norm_num)
theorem B1048889 : Blo 980594 1048889 := bbase (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) (by norm_num)
theorem B1474877 : Blo 980594 1474877 := bbase (se 3 (by rfl) ⟨276539, by rfl⟩ : syracuseStep 1474877 = 553079) (by norm_num)
theorem B1868093 : Blo 980594 1868093 := bbase (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) (by norm_num)
theorem B1474901 : Blo 980594 1474901 := bbase (se 10 (by rfl) ⟨2160, by rfl⟩ : syracuseStep 1474901 = 4321) (by norm_num)
theorem B2490709 : Blo 980594 2490709 := bbase (se 10 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 2490709 = 7297) (by norm_num)
theorem B1474925 : Blo 980594 1474925 := bbase (se 3 (by rfl) ⟨276548, by rfl⟩ : syracuseStep 1474925 = 553097) (by norm_num)
theorem B1245557 : Blo 980594 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1474949 : Blo 980594 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B1474973 : Blo 980594 1474973 := bbase (se 3 (by rfl) ⟨276557, by rfl⟩ : syracuseStep 1474973 = 553115) (by norm_num)
theorem B2130349 : Blo 980594 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B1245613 : Blo 980594 1245613 := bbase (se 3 (by rfl) ⟨233552, by rfl⟩ : syracuseStep 1245613 = 467105) (by norm_num)
theorem B1474997 : Blo 980594 1474997 := bbase (se 5 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 1474997 = 138281) (by norm_num)
theorem B3735989 : Blo 980594 3735989 := bbase (se 5 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 3735989 = 350249) (by norm_num)
theorem B2490821 : Blo 980594 2490821 := bbase (se 4 (by rfl) ⟨233514, by rfl⟩ : syracuseStep 2490821 = 467029) (by norm_num)
theorem B1475021 : Blo 980594 1475021 := bbase (se 3 (by rfl) ⟨276566, by rfl⟩ : syracuseStep 1475021 = 553133) (by norm_num)
theorem B3310037 : Blo 980594 3310037 := bbase (se 7 (by rfl) ⟨38789, by rfl⟩ : syracuseStep 3310037 = 77579) (by norm_num)
theorem B1475045 : Blo 980594 1475045 := bbase (se 4 (by rfl) ⟨138285, by rfl⟩ : syracuseStep 1475045 = 276571) (by norm_num)
theorem B1475069 : Blo 980594 1475069 := bbase (se 3 (by rfl) ⟨276575, by rfl⟩ : syracuseStep 1475069 = 553151) (by norm_num)
theorem B1245709 : Blo 980594 1245709 := bbase (se 3 (by rfl) ⟨233570, by rfl⟩ : syracuseStep 1245709 = 467141) (by norm_num)
theorem B2654741 : Blo 980594 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B1475093 : Blo 980594 1475093 := bbase (se 6 (by rfl) ⟨34572, by rfl⟩ : syracuseStep 1475093 = 69145) (by norm_num)
theorem B2982437 : Blo 980594 2982437 := bbase (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) (by norm_num)
theorem B1475117 : Blo 980594 1475117 := bbase (se 3 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 1475117 = 553169) (by norm_num)
theorem B1475141 : Blo 980594 1475141 := bbase (se 4 (by rfl) ⟨138294, by rfl⟩ : syracuseStep 1475141 = 276589) (by norm_num)
theorem B1475165 : Blo 980594 1475165 := bbase (se 3 (by rfl) ⟨276593, by rfl⟩ : syracuseStep 1475165 = 553187) (by norm_num)
theorem B1475189 : Blo 980594 1475189 := bbase (se 5 (by rfl) ⟨69149, by rfl⟩ : syracuseStep 1475189 = 138299) (by norm_num)
theorem B2491013 : Blo 980594 2491013 := bbase (se 4 (by rfl) ⟨233532, by rfl⟩ : syracuseStep 2491013 = 467065) (by norm_num)
theorem B1475213 : Blo 980594 1475213 := bbase (se 3 (by rfl) ⟨276602, by rfl⟩ : syracuseStep 1475213 = 553205) (by norm_num)
theorem B2097829 : Blo 980594 2097829 := bbase (se 4 (by rfl) ⟨196671, by rfl⟩ : syracuseStep 2097829 = 393343) (by norm_num)
theorem B1475237 : Blo 980594 1475237 := bbase (se 4 (by rfl) ⟨138303, by rfl⟩ : syracuseStep 1475237 = 276607) (by norm_num)
theorem B1245881 : Blo 980594 1245881 := bbase (se 2 (by rfl) ⟨467205, by rfl⟩ : syracuseStep 1245881 = 934411) (by norm_num)
theorem B1475261 : Blo 980594 1475261 := bbase (se 3 (by rfl) ⟨276611, by rfl⟩ : syracuseStep 1475261 = 553223) (by norm_num)
theorem B6292181 : Blo 980594 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B1475285 : Blo 980594 1475285 := bbase (se 7 (by rfl) ⟨17288, by rfl⟩ : syracuseStep 1475285 = 34577) (by norm_num)
theorem B3736277 : Blo 980594 3736277 := bbase (se 7 (by rfl) ⟨43784, by rfl⟩ : syracuseStep 3736277 = 87569) (by norm_num)
theorem B1475309 : Blo 980594 1475309 := bbase (se 3 (by rfl) ⟨276620, by rfl⟩ : syracuseStep 1475309 = 553241) (by norm_num)
theorem B4195061 : Blo 980594 4195061 := bbase (se 5 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 4195061 = 393287) (by norm_num)
theorem B2425589 : Blo 980594 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B1049333 : Blo 980594 1049333 := bbase (se 5 (by rfl) ⟨49187, by rfl⟩ : syracuseStep 1049333 = 98375) (by norm_num)
theorem B3146501 : Blo 980594 3146501 := bbase (se 4 (by rfl) ⟨294984, by rfl⟩ : syracuseStep 3146501 = 589969) (by norm_num)
theorem B1475333 : Blo 980594 1475333 := bbase (se 4 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 1475333 = 276625) (by norm_num)
theorem B1573661 : Blo 980594 1573661 := bbase (se 3 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 1573661 = 590123) (by norm_num)
theorem B1475357 : Blo 980594 1475357 := bbase (se 3 (by rfl) ⟨276629, by rfl⟩ : syracuseStep 1475357 = 553259) (by norm_num)
theorem B1049393 : Blo 980594 1049393 := bbase (se 2 (by rfl) ⟨393522, by rfl⟩ : syracuseStep 1049393 = 787045) (by norm_num)
theorem B1475381 : Blo 980594 1475381 := bbase (se 5 (by rfl) ⟨69158, by rfl⟩ : syracuseStep 1475381 = 138317) (by norm_num)
theorem B1475405 : Blo 980594 1475405 := bbase (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) (by norm_num)
theorem B1246033 : Blo 980594 1246033 := bbase (se 2 (by rfl) ⟨467262, by rfl⟩ : syracuseStep 1246033 = 934525) (by norm_num)
theorem B1475429 : Blo 980594 1475429 := bbase (se 4 (by rfl) ⟨138321, by rfl⟩ : syracuseStep 1475429 = 276643) (by norm_num)
theorem B1475453 : Blo 980594 1475453 := bbase (se 3 (by rfl) ⟨276647, by rfl⟩ : syracuseStep 1475453 = 553295) (by norm_num)
theorem B3310469 : Blo 980594 3310469 := bbase (se 4 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 3310469 = 620713) (by norm_num)
theorem B1180553 : Blo 980594 1180553 := bbase (se 2 (by rfl) ⟨442707, by rfl⟩ : syracuseStep 1180553 = 885415) (by norm_num)
theorem B1475477 : Blo 980594 1475477 := bbase (se 6 (by rfl) ⟨34581, by rfl⟩ : syracuseStep 1475477 = 69163) (by norm_num)
theorem B1475501 : Blo 980594 1475501 := bbase (se 3 (by rfl) ⟨276656, by rfl⟩ : syracuseStep 1475501 = 553313) (by norm_num)
theorem B1049521 : Blo 980594 1049521 := bbase (se 2 (by rfl) ⟨393570, by rfl⟩ : syracuseStep 1049521 = 787141) (by norm_num)
theorem B1475525 : Blo 980594 1475525 := bbase (se 4 (by rfl) ⟨138330, by rfl⟩ : syracuseStep 1475525 = 276661) (by norm_num)
theorem B2360269 : Blo 980594 2360269 := bbase (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) (by norm_num)
theorem B1475549 : Blo 980594 1475549 := bbase (se 3 (by rfl) ⟨276665, by rfl⟩ : syracuseStep 1475549 = 553331) (by norm_num)
theorem B2491357 : Blo 980594 2491357 := bbase (se 3 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 2491357 = 934259) (by norm_num)
theorem B1475573 : Blo 980594 1475573 := bbase (se 5 (by rfl) ⟨69167, by rfl⟩ : syracuseStep 1475573 = 138335) (by norm_num)
theorem B1180669 : Blo 980594 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B1475597 : Blo 980594 1475597 := bbase (se 3 (by rfl) ⟨276674, by rfl⟩ : syracuseStep 1475597 = 553349) (by norm_num)
theorem B1475621 : Blo 980594 1475621 := bbase (se 4 (by rfl) ⟨138339, by rfl⟩ : syracuseStep 1475621 = 276679) (by norm_num)
theorem B1868845 : Blo 980594 1868845 := bbase (se 3 (by rfl) ⟨350408, by rfl⟩ : syracuseStep 1868845 = 700817) (by norm_num)
theorem B1475645 : Blo 980594 1475645 := bbase (se 3 (by rfl) ⟨276683, by rfl⟩ : syracuseStep 1475645 = 553367) (by norm_num)
theorem B2491469 : Blo 980594 2491469 := bbase (se 3 (by rfl) ⟨467150, by rfl⟩ : syracuseStep 2491469 = 934301) (by norm_num)
theorem B1475669 : Blo 980594 1475669 := bbase (se 8 (by rfl) ⟨8646, by rfl⟩ : syracuseStep 1475669 = 17293) (by norm_num)
theorem B1475693 : Blo 980594 1475693 := bbase (se 3 (by rfl) ⟨276692, by rfl⟩ : syracuseStep 1475693 = 553385) (by norm_num)
theorem B1475717 : Blo 980594 1475717 := bbase (se 4 (by rfl) ⟨138348, by rfl⟩ : syracuseStep 1475717 = 276697) (by norm_num)
theorem B2098325 : Blo 980594 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B1475741 : Blo 980594 1475741 := bbase (se 3 (by rfl) ⟨276701, by rfl⟩ : syracuseStep 1475741 = 553403) (by norm_num)
theorem B1475765 : Blo 980594 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B1868989 : Blo 980594 1868989 := bbase (se 3 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 1868989 = 700871) (by norm_num)
theorem B1180865 : Blo 980594 1180865 := bbase (se 2 (by rfl) ⟨442824, by rfl⟩ : syracuseStep 1180865 = 885649) (by norm_num)
theorem B1475789 : Blo 980594 1475789 := bbase (se 3 (by rfl) ⟨276710, by rfl⟩ : syracuseStep 1475789 = 553421) (by norm_num)
theorem B1475813 : Blo 980594 1475813 := bbase (se 4 (by rfl) ⟨138357, by rfl⟩ : syracuseStep 1475813 = 276715) (by norm_num)
theorem B1475837 : Blo 980594 1475837 := bbase (se 3 (by rfl) ⟨276719, by rfl⟩ : syracuseStep 1475837 = 553439) (by norm_num)
theorem B2491661 : Blo 980594 2491661 := bbase (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) (by norm_num)
theorem B1475861 : Blo 980594 1475861 := bbase (se 6 (by rfl) ⟨34590, by rfl⟩ : syracuseStep 1475861 = 69181) (by norm_num)
theorem B1475885 : Blo 980594 1475885 := bbase (se 3 (by rfl) ⟨276728, by rfl⟩ : syracuseStep 1475885 = 553457) (by norm_num)
theorem B3310901 : Blo 980594 3310901 := bbase (se 5 (by rfl) ⟨155198, by rfl⟩ : syracuseStep 3310901 = 310397) (by norm_num)
theorem B1475909 : Blo 980594 1475909 := bbase (se 4 (by rfl) ⟨138366, by rfl⟩ : syracuseStep 1475909 = 276733) (by norm_num)
theorem B1475933 : Blo 980594 1475933 := bbase (se 3 (by rfl) ⟨276737, by rfl⟩ : syracuseStep 1475933 = 553475) (by norm_num)
theorem B1869149 : Blo 980594 1869149 := bbase (se 3 (by rfl) ⟨350465, by rfl⟩ : syracuseStep 1869149 = 700931) (by norm_num)
theorem B1049965 : Blo 980594 1049965 := bbase (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) (by norm_num)
theorem B1475957 : Blo 980594 1475957 := bbase (se 5 (by rfl) ⟨69185, by rfl⟩ : syracuseStep 1475957 = 138371) (by norm_num)
theorem B1475981 : Blo 980594 1475981 := bbase (se 3 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 1475981 = 553493) (by norm_num)
theorem B1476005 : Blo 980594 1476005 := bbase (se 4 (by rfl) ⟨138375, by rfl⟩ : syracuseStep 1476005 = 276751) (by norm_num)
theorem B1574333 : Blo 980594 1574333 := bbase (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) (by norm_num)
theorem B1476029 : Blo 980594 1476029 := bbase (se 3 (by rfl) ⟨276755, by rfl⟩ : syracuseStep 1476029 = 553511) (by norm_num)
theorem B1476053 : Blo 980594 1476053 := bbase (se 7 (by rfl) ⟨17297, by rfl⟩ : syracuseStep 1476053 = 34595) (by norm_num)
theorem B1050085 : Blo 980594 1050085 := bbase (se 4 (by rfl) ⟨98445, by rfl⟩ : syracuseStep 1050085 = 196891) (by norm_num)
theorem B1476077 : Blo 980594 1476077 := bbase (se 3 (by rfl) ⟨276764, by rfl⟩ : syracuseStep 1476077 = 553529) (by norm_num)
theorem B1476101 : Blo 980594 1476101 := bbase (se 4 (by rfl) ⟨138384, by rfl⟩ : syracuseStep 1476101 = 276769) (by norm_num)
theorem B1476125 : Blo 980594 1476125 := bbase (se 3 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 1476125 = 553547) (by norm_num)
theorem B4982309 : Blo 980594 4982309 := bbase (se 4 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 4982309 = 934183) (by norm_num)
theorem B1476149 : Blo 980594 1476149 := bbase (se 5 (by rfl) ⟨69194, by rfl⟩ : syracuseStep 1476149 = 138389) (by norm_num)
theorem B1476173 : Blo 980594 1476173 := bbase (se 3 (by rfl) ⟨276782, by rfl⟩ : syracuseStep 1476173 = 553565) (by norm_num)
theorem B1476197 : Blo 980594 1476197 := bbase (se 4 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 1476197 = 276787) (by norm_num)
theorem B2492005 : Blo 980594 2492005 := bbase (se 4 (by rfl) ⟨233625, by rfl⟩ : syracuseStep 2492005 = 467251) (by norm_num)
theorem B1476221 : Blo 980594 1476221 := bbase (se 3 (by rfl) ⟨276791, by rfl⟩ : syracuseStep 1476221 = 553583) (by norm_num)
theorem B2360981 : Blo 980594 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B1476245 : Blo 980594 1476245 := bbase (se 6 (by rfl) ⟨34599, by rfl⟩ : syracuseStep 1476245 = 69199) (by norm_num)
theorem B1476269 : Blo 980594 1476269 := bbase (se 3 (by rfl) ⟨276800, by rfl⟩ : syracuseStep 1476269 = 553601) (by norm_num)
theorem B1476293 : Blo 980594 1476293 := bbase (se 4 (by rfl) ⟨138402, by rfl⟩ : syracuseStep 1476293 = 276805) (by norm_num)
theorem B2492117 : Blo 980594 2492117 := bbase (se 7 (by rfl) ⟨29204, by rfl⟩ : syracuseStep 2492117 = 58409) (by norm_num)
theorem B1476317 : Blo 980594 1476317 := bbase (se 3 (by rfl) ⟨276809, by rfl⟩ : syracuseStep 1476317 = 553619) (by norm_num)
theorem B1050337 : Blo 980594 1050337 := bbase (se 2 (by rfl) ⟨393876, by rfl⟩ : syracuseStep 1050337 = 787753) (by norm_num)
theorem B3311333 : Blo 980594 3311333 := bbase (se 4 (by rfl) ⟨310437, by rfl⟩ : syracuseStep 3311333 = 620875) (by norm_num)
theorem B4196069 : Blo 980594 4196069 := bbase (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) (by norm_num)
theorem B1181413 : Blo 980594 1181413 := bbase (se 4 (by rfl) ⟨110757, by rfl⟩ : syracuseStep 1181413 = 221515) (by norm_num)
theorem B1050341 : Blo 980594 1050341 := bbase (se 4 (by rfl) ⟨98469, by rfl⟩ : syracuseStep 1050341 = 196939) (by norm_num)
theorem B1476341 : Blo 980594 1476341 := bbase (se 5 (by rfl) ⟨69203, by rfl⟩ : syracuseStep 1476341 = 138407) (by norm_num)
theorem B1476365 : Blo 980594 1476365 := bbase (se 3 (by rfl) ⟨276818, by rfl⟩ : syracuseStep 1476365 = 553637) (by norm_num)
theorem B1476389 : Blo 980594 1476389 := bbase (se 4 (by rfl) ⟨138411, by rfl⟩ : syracuseStep 1476389 = 276823) (by norm_num)
theorem B1476413 : Blo 980594 1476413 := bbase (se 3 (by rfl) ⟨276827, by rfl⟩ : syracuseStep 1476413 = 553655) (by norm_num)
theorem B3147589 : Blo 980594 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B1476437 : Blo 980594 1476437 := bbase (se 9 (by rfl) ⟨4325, by rfl⟩ : syracuseStep 1476437 = 8651) (by norm_num)
theorem B1476461 : Blo 980594 1476461 := bbase (se 3 (by rfl) ⟨276836, by rfl⟩ : syracuseStep 1476461 = 553673) (by norm_num)
theorem B4786037 : Blo 980594 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B1181557 : Blo 980594 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B3737461 : Blo 980594 3737461 := bbase (se 5 (by rfl) ⟨175193, by rfl⟩ : syracuseStep 3737461 = 350387) (by norm_num)
theorem B1476485 : Blo 980594 1476485 := bbase (se 4 (by rfl) ⟨138420, by rfl⟩ : syracuseStep 1476485 = 276841) (by norm_num)
theorem B1476509 : Blo 980594 1476509 := bbase (se 3 (by rfl) ⟨276845, by rfl⟩ : syracuseStep 1476509 = 553691) (by norm_num)
theorem B1476533 : Blo 980594 1476533 := bbase (se 5 (by rfl) ⟨69212, by rfl⟩ : syracuseStep 1476533 = 138425) (by norm_num)
theorem B1574845 : Blo 980594 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B1476557 : Blo 980594 1476557 := bbase (se 3 (by rfl) ⟨276854, by rfl⟩ : syracuseStep 1476557 = 553709) (by norm_num)
theorem B1476581 : Blo 980594 1476581 := bbase (se 4 (by rfl) ⟨138429, by rfl⟩ : syracuseStep 1476581 = 276859) (by norm_num)
theorem B1476605 : Blo 980594 1476605 := bbase (se 3 (by rfl) ⟨276863, by rfl⟩ : syracuseStep 1476605 = 553727) (by norm_num)
theorem B2099213 : Blo 980594 2099213 := bbase (se 3 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 2099213 = 787205) (by norm_num)
theorem B1476629 : Blo 980594 1476629 := bbase (se 6 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 1476629 = 69217) (by norm_num)
theorem B1476653 : Blo 980594 1476653 := bbase (se 3 (by rfl) ⟨276872, by rfl⟩ : syracuseStep 1476653 = 553745) (by norm_num)
theorem B1476677 : Blo 980594 1476677 := bbase (se 4 (by rfl) ⟨138438, by rfl⟩ : syracuseStep 1476677 = 276877) (by norm_num)
theorem B1476701 : Blo 980594 1476701 := bbase (se 3 (by rfl) ⟨276881, by rfl⟩ : syracuseStep 1476701 = 553763) (by norm_num)
theorem B1771637 : Blo 980594 1771637 := bbase (se 5 (by rfl) ⟨83045, by rfl⟩ : syracuseStep 1771637 = 166091) (by norm_num)
theorem B1476725 : Blo 980594 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B2099333 : Blo 980594 2099333 := bbase (se 4 (by rfl) ⟨196812, by rfl⟩ : syracuseStep 2099333 = 393625) (by norm_num)
theorem B1476749 : Blo 980594 1476749 := bbase (se 3 (by rfl) ⟨276890, by rfl⟩ : syracuseStep 1476749 = 553781) (by norm_num)
theorem B3311765 : Blo 980594 3311765 := bbase (se 6 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 3311765 = 155239) (by norm_num)
theorem B3737765 : Blo 980594 3737765 := bbase (se 4 (by rfl) ⟨350415, by rfl⟩ : syracuseStep 3737765 = 700831) (by norm_num)
theorem B1476773 : Blo 980594 1476773 := bbase (se 4 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 1476773 = 276895) (by norm_num)
theorem B1476797 : Blo 980594 1476797 := bbase (se 3 (by rfl) ⟨276899, by rfl⟩ : syracuseStep 1476797 = 553799) (by norm_num)
theorem B1476821 : Blo 980594 1476821 := bbase (se 7 (by rfl) ⟨17306, by rfl⟩ : syracuseStep 1476821 = 34613) (by norm_num)
theorem B1476845 : Blo 980594 1476845 := bbase (se 3 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 1476845 = 553817) (by norm_num)
theorem B1476869 : Blo 980594 1476869 := bbase (se 4 (by rfl) ⟨138456, by rfl⟩ : syracuseStep 1476869 = 276913) (by norm_num)
theorem B1050905 : Blo 980594 1050905 := bbase (se 2 (by rfl) ⟨394089, by rfl⟩ : syracuseStep 1050905 = 788179) (by norm_num)
theorem B2361653 : Blo 980594 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B2394461 : Blo 980594 2394461 := bbase (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) (by norm_num)
theorem B1575301 : Blo 980594 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B2591165 : Blo 980594 2591165 := bbase (se 3 (by rfl) ⟨485843, by rfl⟩ : syracuseStep 2591165 = 971687) (by norm_num)
theorem B1051093 : Blo 980594 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B3312197 : Blo 980594 3312197 := bbase (se 4 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 3312197 = 621037) (by norm_num)
theorem B2099965 : Blo 980594 2099965 := bbase (se 3 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 2099965 = 787487) (by norm_num)
theorem B4983605 : Blo 980594 4983605 := bbase (se 5 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 4983605 = 467213) (by norm_num)
theorem B24218453 : Blo 980594 24218453 := bbase (se 9 (by rfl) ⟨70952, by rfl⟩ : syracuseStep 24218453 = 141905) (by norm_num)
theorem B1182605 : Blo 980594 1182605 := bbase (se 3 (by rfl) ⟨221738, by rfl⟩ : syracuseStep 1182605 = 443477) (by norm_num)
theorem B3148757 : Blo 980594 3148757 := bbase (se 7 (by rfl) ⟨36899, by rfl⟩ : syracuseStep 3148757 = 73799) (by norm_num)
theorem B3312629 : Blo 980594 3312629 := bbase (se 5 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 3312629 = 310559) (by norm_num)
theorem B1575973 : Blo 980594 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B3313061 : Blo 980594 3313061 := bbase (se 4 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 3313061 = 621199) (by norm_num)
theorem B1576397 : Blo 980594 1576397 := bbase (se 3 (by rfl) ⟨295574, by rfl⟩ : syracuseStep 1576397 = 591149) (by norm_num)
theorem B4197845 : Blo 980594 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B1773085 : Blo 980594 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B4722229 : Blo 980594 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B2100853 : Blo 980594 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B2100973 : Blo 980594 2100973 := bbase (se 3 (by rfl) ⟨393932, by rfl⟩ : syracuseStep 2100973 = 787865) (by norm_num)
theorem B1576685 : Blo 980594 1576685 := bbase (se 3 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 1576685 = 591257) (by norm_num)
theorem B3313493 : Blo 980594 3313493 := bbase (se 9 (by rfl) ⟨9707, by rfl⟩ : syracuseStep 3313493 = 19415) (by norm_num)
theorem B3542885 : Blo 980594 3542885 := bbase (se 4 (by rfl) ⟨332145, by rfl⟩ : syracuseStep 3542885 = 664291) (by norm_num)
theorem B2592749 : Blo 980594 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B2101229 : Blo 980594 2101229 := bbase (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) (by norm_num)
theorem B2363413 : Blo 980594 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B5967989 : Blo 980594 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B3543173 : Blo 980594 3543173 := bbase (se 4 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 3543173 = 664345) (by norm_num)
theorem B9441461 : Blo 980594 9441461 := bbase (se 5 (by rfl) ⟨442568, by rfl⟩ : syracuseStep 9441461 = 885137) (by norm_num)
theorem B8523989 : Blo 980594 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B3313925 : Blo 980594 3313925 := bbase (se 4 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 3313925 = 621361) (by norm_num)
theorem B3543317 : Blo 980594 3543317 := bbase (se 6 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 3543317 = 166093) (by norm_num)
theorem B1773893 : Blo 980594 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B1347925 : Blo 980594 1347925 := bbase (se 10 (by rfl) ⟨1974, by rfl⟩ : syracuseStep 1347925 = 3949) (by norm_num)
theorem B1773965 : Blo 980594 1773965 := bbase (se 3 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 1773965 = 665237) (by norm_num)
theorem B1348045 : Blo 980594 1348045 := bbase (se 3 (by rfl) ⟨252758, by rfl⟩ : syracuseStep 1348045 = 505517) (by norm_num)
theorem B1774181 : Blo 980594 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B2364029 : Blo 980594 2364029 := bbase (se 3 (by rfl) ⟨443255, by rfl⟩ : syracuseStep 2364029 = 886511) (by norm_num)
theorem B3314357 : Blo 980594 3314357 := bbase (se 5 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 3314357 = 310721) (by norm_num)
theorem B3150613 : Blo 980594 3150613 := bbase (se 6 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 3150613 = 147685) (by norm_num)
theorem B2102117 : Blo 980594 2102117 := bbase (se 4 (by rfl) ⟨197073, by rfl⟩ : syracuseStep 2102117 = 394147) (by norm_num)
theorem B5968981 : Blo 980594 5968981 := bbase (se 8 (by rfl) ⟨34974, by rfl⟩ : syracuseStep 5968981 = 69949) (by norm_num)
theorem B2102357 : Blo 980594 2102357 := bbase (se 8 (by rfl) ⟨12318, by rfl⟩ : syracuseStep 2102357 = 24637) (by norm_num)
theorem B3314789 : Blo 980594 3314789 := bbase (se 4 (by rfl) ⟨310761, by rfl⟩ : syracuseStep 3314789 = 621523) (by norm_num)
theorem B1119377 : Blo 980594 1119377 := bbase (se 2 (by rfl) ⟨419766, by rfl⟩ : syracuseStep 1119377 = 839533) (by norm_num)
theorem B5051765 : Blo 980594 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B2364797 : Blo 980594 2364797 := bbase (se 3 (by rfl) ⟨443399, by rfl⟩ : syracuseStep 2364797 = 886799) (by norm_num)
theorem B2364805 : Blo 980594 2364805 := bbase (se 4 (by rfl) ⟨221700, by rfl⟩ : syracuseStep 2364805 = 443401) (by norm_num)
theorem B3315221 : Blo 980594 3315221 := bbase (se 6 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 3315221 = 155401) (by norm_num)
theorem B15963733 : Blo 980594 15963733 := bbase (se 8 (by rfl) ⟨93537, by rfl⟩ : syracuseStep 15963733 = 187075) (by norm_num)
theorem B2659973 : Blo 980594 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B10753685 : Blo 980594 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B3774293 : Blo 980594 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B1120133 : Blo 980594 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B3315653 : Blo 980594 3315653 := bbase (se 4 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 3315653 = 621685) (by norm_num)
theorem B3151973 : Blo 980594 3151973 := bbase (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) (by norm_num)
theorem B2365613 : Blo 980594 2365613 := bbase (se 3 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 2365613 = 887105) (by norm_num)
theorem B5314805 : Blo 980594 5314805 := bbase (se 5 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 5314805 = 498263) (by norm_num)
theorem B3316085 : Blo 980594 3316085 := bbase (se 5 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 3316085 = 310883) (by norm_num)
theorem B3316517 : Blo 980594 3316517 := bbase (se 4 (by rfl) ⟨310923, by rfl⟩ : syracuseStep 3316517 = 621847) (by norm_num)
theorem B1121297 : Blo 980594 1121297 := bbase (se 2 (by rfl) ⟨420486, by rfl⟩ : syracuseStep 1121297 = 840973) (by norm_num)
theorem B1121333 : Blo 980594 1121333 := bbase (se 5 (by rfl) ⟨52562, by rfl⟩ : syracuseStep 1121333 = 105125) (by norm_num)
theorem B1678421 : Blo 980594 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B2792549 : Blo 980594 2792549 := bbase (se 4 (by rfl) ⟨261801, by rfl⟩ : syracuseStep 2792549 = 523603) (by norm_num)
theorem B3316949 : Blo 980594 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B2989349 : Blo 980594 2989349 := bbase (se 4 (by rfl) ⟨280251, by rfl⟩ : syracuseStep 2989349 = 560503) (by norm_num)
theorem B1121593 : Blo 980594 1121593 := bbase (se 2 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 1121593 = 841195) (by norm_num)
theorem B2792789 : Blo 980594 2792789 := bbase (se 11 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2792789 = 4091) (by norm_num)
theorem B3546517 : Blo 980594 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B2792981 : Blo 980594 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B3317381 : Blo 980594 3317381 := bbase (se 4 (by rfl) ⟨311004, by rfl⟩ : syracuseStep 3317381 = 622009) (by norm_num)
theorem B4202117 : Blo 980594 4202117 := bbase (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) (by norm_num)
theorem B4726613 : Blo 980594 4726613 := bbase (se 9 (by rfl) ⟨13847, by rfl⟩ : syracuseStep 4726613 = 27695) (by norm_num)
theorem B3546965 : Blo 980594 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B3317813 : Blo 980594 3317813 := bbase (se 5 (by rfl) ⟨155522, by rfl⟩ : syracuseStep 3317813 = 311045) (by norm_num)
theorem B3318245 : Blo 980594 3318245 := bbase (se 4 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 3318245 = 622171) (by norm_num)
theorem B2793973 : Blo 980594 2793973 := bbase (se 5 (by rfl) ⟨130967, by rfl⟩ : syracuseStep 2793973 = 261935) (by norm_num)
theorem B2237021 : Blo 980594 2237021 := bbase (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) (by norm_num)
theorem B1680173 : Blo 980594 1680173 := bbase (se 3 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 1680173 = 630065) (by norm_num)
theorem B3318677 : Blo 980594 3318677 := bbase (se 6 (by rfl) ⟨77781, by rfl⟩ : syracuseStep 3318677 = 155563) (by norm_num)
theorem B3319109 : Blo 980594 3319109 := bbase (se 4 (by rfl) ⟨311166, by rfl⟩ : syracuseStep 3319109 = 622333) (by norm_num)
theorem B4203893 : Blo 980594 4203893 := bbase (se 5 (by rfl) ⟨197057, by rfl⟩ : syracuseStep 4203893 = 394115) (by norm_num)
theorem B2795077 : Blo 980594 2795077 := bbase (se 4 (by rfl) ⟨262038, by rfl⟩ : syracuseStep 2795077 = 524077) (by norm_num)
theorem B4204133 : Blo 980594 4204133 := bbase (se 4 (by rfl) ⟨394137, by rfl⟩ : syracuseStep 4204133 = 788275) (by norm_num)
theorem B2238077 : Blo 980594 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B1245937 : Blo 980594 1245937 := bbase (se 2 (by rfl) ⟨467226, by rfl⟩ : syracuseStep 1245937 = 934453) (by norm_num)
theorem B7186133 : Blo 980594 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B3319541 : Blo 980594 3319541 := bbase (se 5 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 3319541 = 311207) (by norm_num)
theorem B3319973 : Blo 980594 3319973 := bbase (se 4 (by rfl) ⟨311247, by rfl⟩ : syracuseStep 3319973 = 622495) (by norm_num)
theorem B3320405 : Blo 980594 3320405 := bbase (se 8 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 3320405 = 38911) (by norm_num)
theorem B2206349 : Blo 980594 2206349 := bbase (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) (by norm_num)
theorem B2206421 : Blo 980594 2206421 := bbase (se 7 (by rfl) ⟨25856, by rfl⟩ : syracuseStep 2206421 = 51713) (by norm_num)
theorem B994069 : Blo 980594 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B2206493 : Blo 980594 2206493 := bbase (se 3 (by rfl) ⟨413717, by rfl⟩ : syracuseStep 2206493 = 827435) (by norm_num)
theorem B2206565 : Blo 980594 2206565 := bbase (se 4 (by rfl) ⟨206865, by rfl⟩ : syracuseStep 2206565 = 413731) (by norm_num)
theorem B2206637 : Blo 980594 2206637 := bbase (se 3 (by rfl) ⟨413744, by rfl⟩ : syracuseStep 2206637 = 827489) (by norm_num)
theorem B2206709 : Blo 980594 2206709 := bbase (se 5 (by rfl) ⟨103439, by rfl⟩ : syracuseStep 2206709 = 206879) (by norm_num)
theorem B3320837 : Blo 980594 3320837 := bbase (se 4 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 3320837 = 622657) (by norm_num)
theorem B2796581 : Blo 980594 2796581 := bbase (se 4 (by rfl) ⟨262179, by rfl⟩ : syracuseStep 2796581 = 524359) (by norm_num)
theorem B2206781 : Blo 980594 2206781 := bbase (se 3 (by rfl) ⟨413771, by rfl⟩ : syracuseStep 2206781 = 827543) (by norm_num)
theorem B2206853 : Blo 980594 2206853 := bbase (se 4 (by rfl) ⟨206892, by rfl⟩ : syracuseStep 2206853 = 413785) (by norm_num)
theorem B2206925 : Blo 980594 2206925 := bbase (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) (by norm_num)
theorem B2239757 : Blo 980594 2239757 := bbase (se 3 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 2239757 = 839909) (by norm_num)
theorem B2206997 : Blo 980594 2206997 := bbase (se 6 (by rfl) ⟨51726, by rfl⟩ : syracuseStep 2206997 = 103453) (by norm_num)
theorem B5680469 : Blo 980594 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B2207069 : Blo 980594 2207069 := bbase (se 3 (by rfl) ⟨413825, by rfl⟩ : syracuseStep 2207069 = 827651) (by norm_num)
theorem B2207141 : Blo 980594 2207141 := bbase (se 4 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 2207141 = 413839) (by norm_num)
theorem B3321269 : Blo 980594 3321269 := bbase (se 5 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 3321269 = 311369) (by norm_num)
theorem B2207213 : Blo 980594 2207213 := bbase (se 3 (by rfl) ⟨413852, by rfl⟩ : syracuseStep 2207213 = 827705) (by norm_num)
theorem B2043389 : Blo 980594 2043389 := bbase (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) (by norm_num)
theorem B18853397 : Blo 980594 18853397 := bbase (se 6 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 18853397 = 883753) (by norm_num)
theorem B2207285 : Blo 980594 2207285 := bbase (se 5 (by rfl) ⟨103466, by rfl⟩ : syracuseStep 2207285 = 206933) (by norm_num)
theorem B2207357 : Blo 980594 2207357 := bbase (se 3 (by rfl) ⟨413879, by rfl⟩ : syracuseStep 2207357 = 827759) (by norm_num)
theorem B995009 : Blo 980594 995009 := bbase (se 2 (by rfl) ⟨373128, by rfl⟩ : syracuseStep 995009 = 746257) (by norm_num)
theorem B2207429 : Blo 980594 2207429 := bbase (se 4 (by rfl) ⟨206946, by rfl⟩ : syracuseStep 2207429 = 413893) (by norm_num)
theorem B2207501 : Blo 980594 2207501 := bbase (se 3 (by rfl) ⟨413906, by rfl⟩ : syracuseStep 2207501 = 827813) (by norm_num)
theorem B2207573 : Blo 980594 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B3321701 : Blo 980594 3321701 := bbase (se 4 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 3321701 = 622819) (by norm_num)
theorem B2207645 : Blo 980594 2207645 := bbase (se 3 (by rfl) ⟨413933, by rfl⟩ : syracuseStep 2207645 = 827867) (by norm_num)
theorem B2207717 : Blo 980594 2207717 := bbase (se 4 (by rfl) ⟨206973, by rfl⟩ : syracuseStep 2207717 = 413947) (by norm_num)
theorem B2207789 : Blo 980594 2207789 := bbase (se 3 (by rfl) ⟨413960, by rfl⟩ : syracuseStep 2207789 = 827921) (by norm_num)
theorem B2207861 : Blo 980594 2207861 := bbase (se 5 (by rfl) ⟨103493, by rfl⟩ : syracuseStep 2207861 = 206987) (by norm_num)
theorem B2207933 : Blo 980594 2207933 := bbase (se 3 (by rfl) ⟨413987, by rfl⟩ : syracuseStep 2207933 = 827975) (by norm_num)
theorem B995585 : Blo 980594 995585 := bbase (se 2 (by rfl) ⟨373344, by rfl⟩ : syracuseStep 995585 = 746689) (by norm_num)
theorem B2208005 : Blo 980594 2208005 := bbase (se 4 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 2208005 = 414001) (by norm_num)
theorem B3322133 : Blo 980594 3322133 := bbase (se 6 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 3322133 = 155725) (by norm_num)
theorem B995609 : Blo 980594 995609 := bbase (se 2 (by rfl) ⟨373353, by rfl⟩ : syracuseStep 995609 = 746707) (by norm_num)
theorem B2208077 : Blo 980594 2208077 := bbase (se 3 (by rfl) ⟨414014, by rfl⟩ : syracuseStep 2208077 = 828029) (by norm_num)
theorem B2208149 : Blo 980594 2208149 := bbase (se 6 (by rfl) ⟨51753, by rfl⟩ : syracuseStep 2208149 = 103507) (by norm_num)
theorem B4731301 : Blo 980594 4731301 := bbase (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) (by norm_num)
theorem B5681621 : Blo 980594 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B2208221 : Blo 980594 2208221 := bbase (se 3 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 2208221 = 828083) (by norm_num)
theorem B2208293 : Blo 980594 2208293 := bbase (se 4 (by rfl) ⟨207027, by rfl⟩ : syracuseStep 2208293 = 414055) (by norm_num)
theorem B2798165 : Blo 980594 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B1684061 : Blo 980594 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B2208365 : Blo 980594 2208365 := bbase (se 3 (by rfl) ⟨414068, by rfl⟩ : syracuseStep 2208365 = 828137) (by norm_num)
theorem B2208437 : Blo 980594 2208437 := bbase (se 5 (by rfl) ⟨103520, by rfl⟩ : syracuseStep 2208437 = 207041) (by norm_num)
theorem B3322565 : Blo 980594 3322565 := bbase (se 4 (by rfl) ⟨311490, by rfl⟩ : syracuseStep 3322565 = 622981) (by norm_num)
theorem B2208509 : Blo 980594 2208509 := bbase (se 3 (by rfl) ⟨414095, by rfl⟩ : syracuseStep 2208509 = 828191) (by norm_num)
theorem B2241325 : Blo 980594 2241325 := bbase (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) (by norm_num)
theorem B2208581 : Blo 980594 2208581 := bbase (se 4 (by rfl) ⟨207054, by rfl⟩ : syracuseStep 2208581 = 414109) (by norm_num)
theorem B2208653 : Blo 980594 2208653 := bbase (se 3 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 2208653 = 828245) (by norm_num)
theorem B2208725 : Blo 980594 2208725 := bbase (se 7 (by rfl) ⟨25883, by rfl⟩ : syracuseStep 2208725 = 51767) (by norm_num)
theorem B2208797 : Blo 980594 2208797 := bbase (se 3 (by rfl) ⟨414149, by rfl⟩ : syracuseStep 2208797 = 828299) (by norm_num)
theorem B2208869 : Blo 980594 2208869 := bbase (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) (by norm_num)
theorem B3322997 : Blo 980594 3322997 := bbase (se 5 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 3322997 = 311531) (by norm_num)
theorem B996481 : Blo 980594 996481 := bbase (se 2 (by rfl) ⟨373680, by rfl⟩ : syracuseStep 996481 = 747361) (by norm_num)
theorem B2208941 : Blo 980594 2208941 := bbase (se 3 (by rfl) ⟨414176, by rfl⟩ : syracuseStep 2208941 = 828353) (by norm_num)
theorem B2209013 : Blo 980594 2209013 := bbase (se 5 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 2209013 = 207095) (by norm_num)
theorem B2798837 : Blo 980594 2798837 := bbase (se 5 (by rfl) ⟨131195, by rfl⟩ : syracuseStep 2798837 = 262391) (by norm_num)
theorem B2209085 : Blo 980594 2209085 := bbase (se 3 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 2209085 = 828407) (by norm_num)
theorem B2209157 : Blo 980594 2209157 := bbase (se 4 (by rfl) ⟨207108, by rfl⟩ : syracuseStep 2209157 = 414217) (by norm_num)
theorem B2209229 : Blo 980594 2209229 := bbase (se 3 (by rfl) ⟨414230, by rfl⟩ : syracuseStep 2209229 = 828461) (by norm_num)
theorem B2209301 : Blo 980594 2209301 := bbase (se 6 (by rfl) ⟨51780, by rfl⟩ : syracuseStep 2209301 = 103561) (by norm_num)
theorem B2209373 : Blo 980594 2209373 := bbase (se 3 (by rfl) ⟨414257, by rfl⟩ : syracuseStep 2209373 = 828515) (by norm_num)
theorem B2209445 : Blo 980594 2209445 := bbase (se 4 (by rfl) ⟨207135, by rfl⟩ : syracuseStep 2209445 = 414271) (by norm_num)
theorem B2799269 : Blo 980594 2799269 := bbase (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) (by norm_num)
theorem B2209517 : Blo 980594 2209517 := bbase (se 3 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 2209517 = 828569) (by norm_num)
theorem B2209589 : Blo 980594 2209589 := bbase (se 5 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 2209589 = 207149) (by norm_num)
theorem B2209661 : Blo 980594 2209661 := bbase (se 3 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 2209661 = 828623) (by norm_num)
theorem B2209733 : Blo 980594 2209733 := bbase (se 4 (by rfl) ⟨207162, by rfl⟩ : syracuseStep 2209733 = 414325) (by norm_num)
theorem B1259473 : Blo 980594 1259473 := bbase (se 2 (by rfl) ⟨472302, by rfl⟩ : syracuseStep 1259473 = 944605) (by norm_num)
theorem B2209805 : Blo 980594 2209805 := bbase (se 3 (by rfl) ⟨414338, by rfl⟩ : syracuseStep 2209805 = 828677) (by norm_num)
theorem B2209877 : Blo 980594 2209877 := bbase (se 8 (by rfl) ⟨12948, by rfl⟩ : syracuseStep 2209877 = 25897) (by norm_num)
theorem B6305941 : Blo 980594 6305941 := bbase (se 6 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 6305941 = 295591) (by norm_num)
theorem B2209949 : Blo 980594 2209949 := bbase (se 3 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 2209949 = 828731) (by norm_num)
theorem B2210021 : Blo 980594 2210021 := bbase (se 4 (by rfl) ⟨207189, by rfl⟩ : syracuseStep 2210021 = 414379) (by norm_num)
theorem B2210093 : Blo 980594 2210093 := bbase (se 3 (by rfl) ⟨414392, by rfl⟩ : syracuseStep 2210093 = 828785) (by norm_num)
theorem B2210165 : Blo 980594 2210165 := bbase (se 5 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 2210165 = 207203) (by norm_num)
theorem B2800021 : Blo 980594 2800021 := bbase (se 6 (by rfl) ⟨65625, by rfl⟩ : syracuseStep 2800021 = 131251) (by norm_num)
theorem B2210237 : Blo 980594 2210237 := bbase (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) (by norm_num)
theorem B2210309 : Blo 980594 2210309 := bbase (se 4 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 2210309 = 414433) (by norm_num)
theorem B2210381 : Blo 980594 2210381 := bbase (se 3 (by rfl) ⟨414446, by rfl⟩ : syracuseStep 2210381 = 828893) (by norm_num)
theorem B2210453 : Blo 980594 2210453 := bbase (se 6 (by rfl) ⟨51807, by rfl⟩ : syracuseStep 2210453 = 103615) (by norm_num)
theorem B7977653 : Blo 980594 7977653 := bbase (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) (by norm_num)
theorem B1325749 : Blo 980594 1325749 := bbase (se 5 (by rfl) ⟨62144, by rfl⟩ : syracuseStep 1325749 = 124289) (by norm_num)
theorem B2210525 : Blo 980594 2210525 := bbase (se 3 (by rfl) ⟨414473, by rfl⟩ : syracuseStep 2210525 = 828947) (by norm_num)
theorem B2210597 : Blo 980594 2210597 := bbase (se 4 (by rfl) ⟨207243, by rfl⟩ : syracuseStep 2210597 = 414487) (by norm_num)
theorem B2210669 : Blo 980594 2210669 := bbase (se 3 (by rfl) ⟨414500, by rfl⟩ : syracuseStep 2210669 = 829001) (by norm_num)
theorem B2210741 : Blo 980594 2210741 := bbase (se 5 (by rfl) ⟨103628, by rfl⟩ : syracuseStep 2210741 = 207257) (by norm_num)
theorem B2210813 : Blo 980594 2210813 := bbase (se 3 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 2210813 = 829055) (by norm_num)
theorem B2210885 : Blo 980594 2210885 := bbase (se 4 (by rfl) ⟨207270, by rfl⟩ : syracuseStep 2210885 = 414541) (by norm_num)
theorem B7453781 : Blo 980594 7453781 := bbase (se 8 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 7453781 = 87349) (by norm_num)
theorem B1326181 : Blo 980594 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B2210957 : Blo 980594 2210957 := bbase (se 3 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 2210957 = 829109) (by norm_num)
theorem B11943125 : Blo 980594 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B2211029 : Blo 980594 2211029 := bbase (se 7 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 2211029 = 51821) (by norm_num)
theorem B2211101 : Blo 980594 2211101 := bbase (se 3 (by rfl) ⟨414581, by rfl⟩ : syracuseStep 2211101 = 829163) (by norm_num)
theorem B2211173 : Blo 980594 2211173 := bbase (se 4 (by rfl) ⟨207297, by rfl⟩ : syracuseStep 2211173 = 414595) (by norm_num)
theorem B2211245 : Blo 980594 2211245 := bbase (se 3 (by rfl) ⟨414608, by rfl⟩ : syracuseStep 2211245 = 829217) (by norm_num)
theorem B1916389 : Blo 980594 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B2211317 : Blo 980594 2211317 := bbase (se 5 (by rfl) ⟨103655, by rfl⟩ : syracuseStep 2211317 = 207311) (by norm_num)
theorem B2211389 : Blo 980594 2211389 := bbase (se 3 (by rfl) ⟨414635, by rfl⟩ : syracuseStep 2211389 = 829271) (by norm_num)
theorem B2211461 : Blo 980594 2211461 := bbase (se 4 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 2211461 = 414649) (by norm_num)
theorem B1064621 : Blo 980594 1064621 := bbase (se 3 (by rfl) ⟨199616, by rfl⟩ : syracuseStep 1064621 = 399233) (by norm_num)
theorem B2211533 : Blo 980594 2211533 := bbase (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) (by norm_num)
theorem B2211605 : Blo 980594 2211605 := bbase (se 6 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 2211605 = 103669) (by norm_num)
theorem B1261337 : Blo 980594 1261337 := bbase (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) (by norm_num)
theorem B2211677 : Blo 980594 2211677 := bbase (se 3 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 2211677 = 829379) (by norm_num)
theorem B1064845 : Blo 980594 1064845 := bbase (se 3 (by rfl) ⟨199658, by rfl⟩ : syracuseStep 1064845 = 399317) (by norm_num)
theorem B2211749 : Blo 980594 2211749 := bbase (se 4 (by rfl) ⟨207351, by rfl⟩ : syracuseStep 2211749 = 414703) (by norm_num)
theorem B2211821 : Blo 980594 2211821 := bbase (se 3 (by rfl) ⟨414716, by rfl⟩ : syracuseStep 2211821 = 829433) (by norm_num)
theorem B1654789 : Blo 980594 1654789 := bbase (se 4 (by rfl) ⟨155136, by rfl⟩ : syracuseStep 1654789 = 310273) (by norm_num)
theorem B5586965 : Blo 980594 5586965 := bbase (se 6 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 5586965 = 261889) (by norm_num)
theorem B2211893 : Blo 980594 2211893 := bbase (se 5 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 2211893 = 207365) (by norm_num)
theorem B1491029 : Blo 980594 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B1654877 : Blo 980594 1654877 := bbase (se 3 (by rfl) ⟨310289, by rfl⟩ : syracuseStep 1654877 = 620579) (by norm_num)
theorem B2211965 : Blo 980594 2211965 := bbase (se 3 (by rfl) ⟨414743, by rfl⟩ : syracuseStep 2211965 = 829487) (by norm_num)
theorem B2834597 : Blo 980594 2834597 := bbase (se 4 (by rfl) ⟨265743, by rfl⟩ : syracuseStep 2834597 = 531487) (by norm_num)
theorem B2212037 : Blo 980594 2212037 := bbase (se 4 (by rfl) ⟨207378, by rfl⟩ : syracuseStep 2212037 = 414757) (by norm_num)
theorem B1655005 : Blo 980594 1655005 := bbase (se 3 (by rfl) ⟨310313, by rfl⟩ : syracuseStep 1655005 = 620627) (by norm_num)
theorem B2212109 : Blo 980594 2212109 := bbase (se 3 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 2212109 = 829541) (by norm_num)
theorem B1655093 : Blo 980594 1655093 := bbase (se 5 (by rfl) ⟨77582, by rfl⟩ : syracuseStep 1655093 = 155165) (by norm_num)
theorem B1196353 : Blo 980594 1196353 := bbase (se 2 (by rfl) ⟨448632, by rfl⟩ : syracuseStep 1196353 = 897265) (by norm_num)
theorem B2212181 : Blo 980594 2212181 := bbase (se 10 (by rfl) ⟨3240, by rfl⟩ : syracuseStep 2212181 = 6481) (by norm_num)
theorem B2212253 : Blo 980594 2212253 := bbase (se 3 (by rfl) ⟨414797, by rfl⟩ : syracuseStep 2212253 = 829595) (by norm_num)
theorem B1261993 : Blo 980594 1261993 := bbase (se 2 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 1261993 = 946495) (by norm_num)
theorem B1655221 : Blo 980594 1655221 := bbase (se 5 (by rfl) ⟨77588, by rfl⟩ : syracuseStep 1655221 = 155177) (by norm_num)
theorem B2212325 : Blo 980594 2212325 := bbase (se 4 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 2212325 = 414811) (by norm_num)
theorem B5980661 : Blo 980594 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B1065469 : Blo 980594 1065469 := bbase (se 3 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 1065469 = 399551) (by norm_num)
theorem B1655309 : Blo 980594 1655309 := bbase (se 3 (by rfl) ⟨310370, by rfl⟩ : syracuseStep 1655309 = 620741) (by norm_num)
theorem B2212397 : Blo 980594 2212397 := bbase (se 3 (by rfl) ⟨414824, by rfl⟩ : syracuseStep 2212397 = 829649) (by norm_num)
theorem B2212469 : Blo 980594 2212469 := bbase (se 5 (by rfl) ⟨103709, by rfl⟩ : syracuseStep 2212469 = 207419) (by norm_num)
theorem B1655437 : Blo 980594 1655437 := bbase (se 3 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 1655437 = 620789) (by norm_num)
theorem B2212541 : Blo 980594 2212541 := bbase (se 3 (by rfl) ⟨414851, by rfl⟩ : syracuseStep 2212541 = 829703) (by norm_num)
theorem B1655525 : Blo 980594 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B2212613 : Blo 980594 2212613 := bbase (se 4 (by rfl) ⟨207432, by rfl⟩ : syracuseStep 2212613 = 414865) (by norm_num)
theorem B2212685 : Blo 980594 2212685 := bbase (se 3 (by rfl) ⟨414878, by rfl⟩ : syracuseStep 2212685 = 829757) (by norm_num)
theorem B1655653 : Blo 980594 1655653 := bbase (se 4 (by rfl) ⟨155217, by rfl⟩ : syracuseStep 1655653 = 310435) (by norm_num)
theorem B2212757 : Blo 980594 2212757 := bbase (se 6 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 2212757 = 103723) (by norm_num)
theorem B1655741 : Blo 980594 1655741 := bbase (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) (by norm_num)
theorem B2212829 : Blo 980594 2212829 := bbase (se 3 (by rfl) ⟨414905, by rfl⟩ : syracuseStep 2212829 = 829811) (by norm_num)
theorem B1491949 : Blo 980594 1491949 := bbase (se 3 (by rfl) ⟨279740, by rfl⟩ : syracuseStep 1491949 = 559481) (by norm_num)
theorem B2212901 : Blo 980594 2212901 := bbase (se 4 (by rfl) ⟨207459, by rfl⟩ : syracuseStep 2212901 = 414919) (by norm_num)
theorem B3032117 : Blo 980594 3032117 := bbase (se 5 (by rfl) ⟨142130, by rfl⟩ : syracuseStep 3032117 = 284261) (by norm_num)
theorem B1655869 : Blo 980594 1655869 := bbase (se 3 (by rfl) ⟨310475, by rfl⟩ : syracuseStep 1655869 = 620951) (by norm_num)
theorem B4965461 : Blo 980594 4965461 := bbase (se 8 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 4965461 = 58189) (by norm_num)
theorem B2212973 : Blo 980594 2212973 := bbase (se 3 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 2212973 = 829865) (by norm_num)
theorem B1655957 : Blo 980594 1655957 := bbase (se 6 (by rfl) ⟨38811, by rfl⟩ : syracuseStep 1655957 = 77623) (by norm_num)
theorem B5588149 : Blo 980594 5588149 := bbase (se 5 (by rfl) ⟨261944, by rfl⟩ : syracuseStep 5588149 = 523889) (by norm_num)
theorem B2213045 : Blo 980594 2213045 := bbase (se 5 (by rfl) ⟨103736, by rfl⟩ : syracuseStep 2213045 = 207473) (by norm_num)
theorem B2802869 : Blo 980594 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B2213117 : Blo 980594 2213117 := bbase (se 3 (by rfl) ⟨414959, by rfl⟩ : syracuseStep 2213117 = 829919) (by norm_num)
theorem B1656085 : Blo 980594 1656085 := bbase (se 6 (by rfl) ⟨38814, by rfl⟩ : syracuseStep 1656085 = 77629) (by norm_num)
theorem B2213189 : Blo 980594 2213189 := bbase (se 4 (by rfl) ⟨207486, by rfl⟩ : syracuseStep 2213189 = 414973) (by norm_num)
theorem B1656173 : Blo 980594 1656173 := bbase (se 3 (by rfl) ⟨310532, by rfl⟩ : syracuseStep 1656173 = 621065) (by norm_num)
theorem B2213261 : Blo 980594 2213261 := bbase (se 3 (by rfl) ⟨414986, by rfl⟩ : syracuseStep 2213261 = 829973) (by norm_num)
theorem B2213333 : Blo 980594 2213333 := bbase (se 7 (by rfl) ⟨25937, by rfl⟩ : syracuseStep 2213333 = 51875) (by norm_num)
theorem B1656301 : Blo 980594 1656301 := bbase (se 3 (by rfl) ⟨310556, by rfl⟩ : syracuseStep 1656301 = 621113) (by norm_num)
theorem B2213405 : Blo 980594 2213405 := bbase (se 3 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 2213405 = 830027) (by norm_num)
theorem B1656389 : Blo 980594 1656389 := bbase (se 4 (by rfl) ⟨155286, by rfl⟩ : syracuseStep 1656389 = 310573) (by norm_num)
theorem B2213477 : Blo 980594 2213477 := bbase (se 4 (by rfl) ⟨207513, by rfl⟩ : syracuseStep 2213477 = 415027) (by norm_num)
theorem B9455221 : Blo 980594 9455221 := bbase (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) (by norm_num)
theorem B2213549 : Blo 980594 2213549 := bbase (se 3 (by rfl) ⟨415040, by rfl⟩ : syracuseStep 2213549 = 830081) (by norm_num)
theorem B1656517 : Blo 980594 1656517 := bbase (se 4 (by rfl) ⟨155298, by rfl⟩ : syracuseStep 1656517 = 310597) (by norm_num)
theorem B2213621 : Blo 980594 2213621 := bbase (se 5 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 2213621 = 207527) (by norm_num)
theorem B1656605 : Blo 980594 1656605 := bbase (se 3 (by rfl) ⟨310613, by rfl⟩ : syracuseStep 1656605 = 621227) (by norm_num)
theorem B3360565 : Blo 980594 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B2213693 : Blo 980594 2213693 := bbase (se 3 (by rfl) ⟨415067, by rfl⟩ : syracuseStep 2213693 = 830135) (by norm_num)
theorem B2213765 : Blo 980594 2213765 := bbase (se 4 (by rfl) ⟨207540, by rfl⟩ : syracuseStep 2213765 = 415081) (by norm_num)
theorem B1656733 : Blo 980594 1656733 := bbase (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) (by norm_num)
theorem B2869157 : Blo 980594 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B2213837 : Blo 980594 2213837 := bbase (se 3 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 2213837 = 830189) (by norm_num)
theorem B1656821 : Blo 980594 1656821 := bbase (se 5 (by rfl) ⟨77663, by rfl⟩ : syracuseStep 1656821 = 155327) (by norm_num)
theorem B2213909 : Blo 980594 2213909 := bbase (se 6 (by rfl) ⟨51888, by rfl⟩ : syracuseStep 2213909 = 103777) (by norm_num)
theorem B2213981 : Blo 980594 2213981 := bbase (se 3 (by rfl) ⟨415121, by rfl⟩ : syracuseStep 2213981 = 830243) (by norm_num)
theorem B3197029 : Blo 980594 3197029 := bbase (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) (by norm_num)
theorem B1656949 : Blo 980594 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B2214053 : Blo 980594 2214053 := bbase (se 4 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 2214053 = 415135) (by norm_num)
theorem B1657037 : Blo 980594 1657037 := bbase (se 3 (by rfl) ⟨310694, by rfl⟩ : syracuseStep 1657037 = 621389) (by norm_num)
theorem B2214125 : Blo 980594 2214125 := bbase (se 3 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 2214125 = 830297) (by norm_num)
theorem B3688741 : Blo 980594 3688741 := bbase (se 4 (by rfl) ⟨345819, by rfl⟩ : syracuseStep 3688741 = 691639) (by norm_num)
theorem B2214197 : Blo 980594 2214197 := bbase (se 5 (by rfl) ⟨103790, by rfl⟩ : syracuseStep 2214197 = 207581) (by norm_num)
theorem B1657165 : Blo 980594 1657165 := bbase (se 3 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 1657165 = 621437) (by norm_num)
theorem B4966757 : Blo 980594 4966757 := bbase (se 4 (by rfl) ⟨465633, by rfl⟩ : syracuseStep 4966757 = 931267) (by norm_num)
theorem B1493365 : Blo 980594 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B2214269 : Blo 980594 2214269 := bbase (se 3 (by rfl) ⟨415175, by rfl⟩ : syracuseStep 2214269 = 830351) (by norm_num)
theorem B1657253 : Blo 980594 1657253 := bbase (se 4 (by rfl) ⟨155367, by rfl⟩ : syracuseStep 1657253 = 310735) (by norm_num)
theorem B2214341 : Blo 980594 2214341 := bbase (se 4 (by rfl) ⟨207594, by rfl⟩ : syracuseStep 2214341 = 415189) (by norm_num)
theorem B1329637 : Blo 980594 1329637 := bbase (se 4 (by rfl) ⟨124653, by rfl⟩ : syracuseStep 1329637 = 249307) (by norm_num)
theorem B2214413 : Blo 980594 2214413 := bbase (se 3 (by rfl) ⟨415202, by rfl⟩ : syracuseStep 2214413 = 830405) (by norm_num)
theorem B6736405 : Blo 980594 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B1657381 : Blo 980594 1657381 := bbase (se 4 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 1657381 = 310759) (by norm_num)
theorem B2214485 : Blo 980594 2214485 := bbase (se 8 (by rfl) ⟨12975, by rfl⟩ : syracuseStep 2214485 = 25951) (by norm_num)
theorem B1657469 : Blo 980594 1657469 := bbase (se 3 (by rfl) ⟨310775, by rfl⟩ : syracuseStep 1657469 = 621551) (by norm_num)
theorem B2214557 : Blo 980594 2214557 := bbase (se 3 (by rfl) ⟨415229, by rfl⟩ : syracuseStep 2214557 = 830459) (by norm_num)
theorem B2214629 : Blo 980594 2214629 := bbase (se 4 (by rfl) ⟨207621, by rfl⟩ : syracuseStep 2214629 = 415243) (by norm_num)
theorem B1657597 : Blo 980594 1657597 := bbase (se 3 (by rfl) ⟨310799, by rfl⟩ : syracuseStep 1657597 = 621599) (by norm_num)
theorem B2214701 : Blo 980594 2214701 := bbase (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) (by norm_num)
theorem B2018125 : Blo 980594 2018125 := bbase (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) (by norm_num)
theorem B4246357 : Blo 980594 4246357 := bbase (se 9 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 4246357 = 24881) (by norm_num)
theorem B135940949 : Blo 980594 135940949 := bbase (se 9 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 135940949 = 796529) (by norm_num)
theorem B1657685 : Blo 980594 1657685 := bbase (se 9 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 1657685 = 9713) (by norm_num)
theorem B2214773 : Blo 980594 2214773 := bbase (se 5 (by rfl) ⟨103817, by rfl⟩ : syracuseStep 2214773 = 207635) (by norm_num)
theorem B2214845 : Blo 980594 2214845 := bbase (se 3 (by rfl) ⟨415283, by rfl⟩ : syracuseStep 2214845 = 830567) (by norm_num)
theorem B1657813 : Blo 980594 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B2214917 : Blo 980594 2214917 := bbase (se 4 (by rfl) ⟨207648, by rfl⟩ : syracuseStep 2214917 = 415297) (by norm_num)
theorem B1657901 : Blo 980594 1657901 := bbase (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) (by norm_num)
theorem B2214989 : Blo 980594 2214989 := bbase (se 3 (by rfl) ⟨415310, by rfl⟩ : syracuseStep 2214989 = 830621) (by norm_num)
theorem B5590133 : Blo 980594 5590133 := bbase (se 5 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 5590133 = 524075) (by norm_num)
theorem B1330301 : Blo 980594 1330301 := bbase (se 3 (by rfl) ⟨249431, by rfl⟩ : syracuseStep 1330301 = 498863) (by norm_num)
theorem B2215061 : Blo 980594 2215061 := bbase (se 6 (by rfl) ⟨51915, by rfl⟩ : syracuseStep 2215061 = 103831) (by norm_num)
theorem B1658029 : Blo 980594 1658029 := bbase (se 3 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 1658029 = 621761) (by norm_num)
theorem B2215133 : Blo 980594 2215133 := bbase (se 3 (by rfl) ⟨415337, by rfl⟩ : syracuseStep 2215133 = 830675) (by norm_num)
theorem B1658117 : Blo 980594 1658117 := bbase (se 4 (by rfl) ⟨155448, by rfl⟩ : syracuseStep 1658117 = 310897) (by norm_num)
theorem B2870549 : Blo 980594 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B2215205 : Blo 980594 2215205 := bbase (se 4 (by rfl) ⟨207675, by rfl⟩ : syracuseStep 2215205 = 415351) (by norm_num)
theorem B2215277 : Blo 980594 2215277 := bbase (se 3 (by rfl) ⟨415364, by rfl⟩ : syracuseStep 2215277 = 830729) (by norm_num)
theorem B1330549 : Blo 980594 1330549 := bbase (se 5 (by rfl) ⟨62369, by rfl⟩ : syracuseStep 1330549 = 124739) (by norm_num)
theorem B1658245 : Blo 980594 1658245 := bbase (se 4 (by rfl) ⟨155460, by rfl⟩ : syracuseStep 1658245 = 310921) (by norm_num)
theorem B1658333 : Blo 980594 1658333 := bbase (se 3 (by rfl) ⟨310937, by rfl⟩ : syracuseStep 1658333 = 621875) (by norm_num)
theorem B1658461 : Blo 980594 1658461 := bbase (se 3 (by rfl) ⟨310961, by rfl⟩ : syracuseStep 1658461 = 621923) (by norm_num)
theorem B4968053 : Blo 980594 4968053 := bbase (se 5 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 4968053 = 465755) (by norm_num)
theorem B1658549 : Blo 980594 1658549 := bbase (se 5 (by rfl) ⟨77744, by rfl⟩ : syracuseStep 1658549 = 155489) (by norm_num)
theorem B1396445 : Blo 980594 1396445 := bbase (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) (by norm_num)
theorem B1658677 : Blo 980594 1658677 := bbase (se 5 (by rfl) ⟨77750, by rfl⟩ : syracuseStep 1658677 = 155501) (by norm_num)
theorem B1658765 : Blo 980594 1658765 := bbase (se 3 (by rfl) ⟨311018, by rfl⟩ : syracuseStep 1658765 = 622037) (by norm_num)
theorem B1658893 : Blo 980594 1658893 := bbase (se 3 (by rfl) ⟨311042, by rfl⟩ : syracuseStep 1658893 = 622085) (by norm_num)
theorem B1658981 : Blo 980594 1658981 := bbase (se 4 (by rfl) ⟨155529, by rfl⟩ : syracuseStep 1658981 = 311059) (by norm_num)
theorem B1659109 : Blo 980594 1659109 := bbase (se 4 (by rfl) ⟨155541, by rfl⟩ : syracuseStep 1659109 = 311083) (by norm_num)
theorem B1659197 : Blo 980594 1659197 := bbase (se 3 (by rfl) ⟨311099, by rfl⟩ : syracuseStep 1659197 = 622199) (by norm_num)
theorem B1659325 : Blo 980594 1659325 := bbase (se 3 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 1659325 = 622247) (by norm_num)
theorem B1397197 : Blo 980594 1397197 := bbase (se 3 (by rfl) ⟨261974, by rfl⟩ : syracuseStep 1397197 = 523949) (by norm_num)
theorem B1888717 : Blo 980594 1888717 := bbase (se 3 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 1888717 = 708269) (by norm_num)
theorem B1659413 : Blo 980594 1659413 := bbase (se 6 (by rfl) ⟨38892, by rfl⟩ : syracuseStep 1659413 = 77785) (by norm_num)
theorem B3986005 : Blo 980594 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B1659541 : Blo 980594 1659541 := bbase (se 6 (by rfl) ⟨38895, by rfl⟩ : syracuseStep 1659541 = 77791) (by norm_num)
theorem B1594093 : Blo 980594 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1659629 : Blo 980594 1659629 := bbase (se 3 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 1659629 = 622361) (by norm_num)
theorem B67982165 : Blo 980594 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B1659757 : Blo 980594 1659757 := bbase (se 3 (by rfl) ⟨311204, by rfl⟩ : syracuseStep 1659757 = 622409) (by norm_num)
theorem B4969349 : Blo 980594 4969349 := bbase (se 4 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 4969349 = 931753) (by norm_num)
theorem B1659845 : Blo 980594 1659845 := bbase (se 4 (by rfl) ⟨155610, by rfl⟩ : syracuseStep 1659845 = 311221) (by norm_num)
theorem B3724325 : Blo 980594 3724325 := bbase (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) (by norm_num)
theorem B1659973 : Blo 980594 1659973 := bbase (se 4 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 1659973 = 311245) (by norm_num)
theorem B1135745 : Blo 980594 1135745 := bbase (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) (by norm_num)
theorem B1660061 : Blo 980594 1660061 := bbase (se 3 (by rfl) ⟨311261, by rfl⟩ : syracuseStep 1660061 = 622523) (by norm_num)
theorem B1397989 : Blo 980594 1397989 := bbase (se 4 (by rfl) ⟨131061, by rfl⟩ : syracuseStep 1397989 = 262123) (by norm_num)
theorem B5592341 : Blo 980594 5592341 := bbase (se 6 (by rfl) ⟨131070, by rfl⟩ : syracuseStep 5592341 = 262141) (by norm_num)
theorem B1660189 : Blo 980594 1660189 := bbase (se 3 (by rfl) ⟨311285, by rfl⟩ : syracuseStep 1660189 = 622571) (by norm_num)
theorem B1594669 : Blo 980594 1594669 := bbase (se 3 (by rfl) ⟨299000, by rfl⟩ : syracuseStep 1594669 = 598001) (by norm_num)
theorem B3724613 : Blo 980594 3724613 := bbase (se 4 (by rfl) ⟨349182, by rfl⟩ : syracuseStep 3724613 = 698365) (by norm_num)
theorem B1103197 : Blo 980594 1103197 := bbase (se 3 (by rfl) ⟨206849, by rfl⟩ : syracuseStep 1103197 = 413699) (by norm_num)
theorem B1660277 : Blo 980594 1660277 := bbase (se 5 (by rfl) ⟨77825, by rfl⟩ : syracuseStep 1660277 = 155651) (by norm_num)
theorem B1103233 : Blo 980594 1103233 := bbase (se 2 (by rfl) ⟨413712, by rfl⟩ : syracuseStep 1103233 = 827425) (by norm_num)
theorem B1791389 : Blo 980594 1791389 := bbase (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) (by norm_num)
theorem B1103269 : Blo 980594 1103269 := bbase (se 4 (by rfl) ⟨103431, by rfl⟩ : syracuseStep 1103269 = 206863) (by norm_num)
theorem B1103305 : Blo 980594 1103305 := bbase (se 2 (by rfl) ⟨413739, by rfl⟩ : syracuseStep 1103305 = 827479) (by norm_num)
theorem B1103341 : Blo 980594 1103341 := bbase (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) (by norm_num)
theorem B1660405 : Blo 980594 1660405 := bbase (se 5 (by rfl) ⟨77831, by rfl⟩ : syracuseStep 1660405 = 155663) (by norm_num)
theorem B1103377 : Blo 980594 1103377 := bbase (se 2 (by rfl) ⟨413766, by rfl⟩ : syracuseStep 1103377 = 827533) (by norm_num)
theorem B1103413 : Blo 980594 1103413 := bbase (se 5 (by rfl) ⟨51722, by rfl⟩ : syracuseStep 1103413 = 103445) (by norm_num)
theorem B1398325 : Blo 980594 1398325 := bbase (se 5 (by rfl) ⟨65546, by rfl⟩ : syracuseStep 1398325 = 131093) (by norm_num)
theorem B1660493 : Blo 980594 1660493 := bbase (se 3 (by rfl) ⟨311342, by rfl⟩ : syracuseStep 1660493 = 622685) (by norm_num)
theorem B1103449 : Blo 980594 1103449 := bbase (se 2 (by rfl) ⟨413793, by rfl⟩ : syracuseStep 1103449 = 827587) (by norm_num)
theorem B1103485 : Blo 980594 1103485 := bbase (se 3 (by rfl) ⟨206903, by rfl⟩ : syracuseStep 1103485 = 413807) (by norm_num)
theorem B1103521 : Blo 980594 1103521 := bbase (se 2 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 1103521 = 827641) (by norm_num)
theorem B1103557 : Blo 980594 1103557 := bbase (se 4 (by rfl) ⟨103458, by rfl⟩ : syracuseStep 1103557 = 206917) (by norm_num)
theorem B1660621 : Blo 980594 1660621 := bbase (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) (by norm_num)
theorem B1103593 : Blo 980594 1103593 := bbase (se 2 (by rfl) ⟨413847, by rfl⟩ : syracuseStep 1103593 = 827695) (by norm_num)
theorem B1103629 : Blo 980594 1103629 := bbase (se 3 (by rfl) ⟨206930, by rfl⟩ : syracuseStep 1103629 = 413861) (by norm_num)
theorem B1398541 : Blo 980594 1398541 := bbase (se 3 (by rfl) ⟨262226, by rfl⟩ : syracuseStep 1398541 = 524453) (by norm_num)
theorem B1660709 : Blo 980594 1660709 := bbase (se 4 (by rfl) ⟨155691, by rfl⟩ : syracuseStep 1660709 = 311383) (by norm_num)
theorem B1103665 : Blo 980594 1103665 := bbase (se 2 (by rfl) ⟨413874, by rfl⟩ : syracuseStep 1103665 = 827749) (by norm_num)
theorem B1103701 : Blo 980594 1103701 := bbase (se 9 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 1103701 = 6467) (by norm_num)
theorem B1103737 : Blo 980594 1103737 := bbase (se 2 (by rfl) ⟨413901, by rfl⟩ : syracuseStep 1103737 = 827803) (by norm_num)
theorem B8378261 : Blo 980594 8378261 := bbase (se 6 (by rfl) ⟨196365, by rfl⟩ : syracuseStep 8378261 = 392731) (by norm_num)
theorem B1103773 : Blo 980594 1103773 := bbase (se 3 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 1103773 = 413915) (by norm_num)
theorem B1660837 : Blo 980594 1660837 := bbase (se 4 (by rfl) ⟨155703, by rfl⟩ : syracuseStep 1660837 = 311407) (by norm_num)
theorem B1103809 : Blo 980594 1103809 := bbase (se 2 (by rfl) ⟨413928, by rfl⟩ : syracuseStep 1103809 = 827857) (by norm_num)
theorem B1103845 : Blo 980594 1103845 := bbase (se 4 (by rfl) ⟨103485, by rfl⟩ : syracuseStep 1103845 = 206971) (by norm_num)
theorem B1660925 : Blo 980594 1660925 := bbase (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) (by norm_num)
theorem B1103881 : Blo 980594 1103881 := bbase (se 2 (by rfl) ⟨413955, by rfl⟩ : syracuseStep 1103881 = 827911) (by norm_num)
theorem B1103917 : Blo 980594 1103917 := bbase (se 3 (by rfl) ⟨206984, by rfl⟩ : syracuseStep 1103917 = 413969) (by norm_num)
theorem B1103953 : Blo 980594 1103953 := bbase (se 2 (by rfl) ⟨413982, by rfl⟩ : syracuseStep 1103953 = 827965) (by norm_num)
theorem B1103989 : Blo 980594 1103989 := bbase (se 5 (by rfl) ⟨51749, by rfl⟩ : syracuseStep 1103989 = 103499) (by norm_num)
theorem B1661053 : Blo 980594 1661053 := bbase (se 3 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 1661053 = 622895) (by norm_num)
theorem B1398917 : Blo 980594 1398917 := bbase (se 4 (by rfl) ⟨131148, by rfl⟩ : syracuseStep 1398917 = 262297) (by norm_num)
theorem B4970645 : Blo 980594 4970645 := bbase (se 6 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 4970645 = 232999) (by norm_num)
theorem B1104025 : Blo 980594 1104025 := bbase (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) (by norm_num)
theorem B1104061 : Blo 980594 1104061 := bbase (se 3 (by rfl) ⟨207011, by rfl⟩ : syracuseStep 1104061 = 414023) (by norm_num)
theorem B1661141 : Blo 980594 1661141 := bbase (se 7 (by rfl) ⟨19466, by rfl⟩ : syracuseStep 1661141 = 38933) (by norm_num)
theorem B1104097 : Blo 980594 1104097 := bbase (se 2 (by rfl) ⟨414036, by rfl⟩ : syracuseStep 1104097 = 828073) (by norm_num)
theorem B1104133 : Blo 980594 1104133 := bbase (se 4 (by rfl) ⟨103512, by rfl⟩ : syracuseStep 1104133 = 207025) (by norm_num)
theorem B1104169 : Blo 980594 1104169 := bbase (se 2 (by rfl) ⟨414063, by rfl⟩ : syracuseStep 1104169 = 828127) (by norm_num)
theorem B1104205 : Blo 980594 1104205 := bbase (se 3 (by rfl) ⟨207038, by rfl⟩ : syracuseStep 1104205 = 414077) (by norm_num)
theorem B1661269 : Blo 980594 1661269 := bbase (se 10 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 1661269 = 4867) (by norm_num)
theorem B1104241 : Blo 980594 1104241 := bbase (se 2 (by rfl) ⟨414090, by rfl⟩ : syracuseStep 1104241 = 828181) (by norm_num)
theorem B1104277 : Blo 980594 1104277 := bbase (se 6 (by rfl) ⟨25881, by rfl⟩ : syracuseStep 1104277 = 51763) (by norm_num)
theorem B1661357 : Blo 980594 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B1104313 : Blo 980594 1104313 := bbase (se 2 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 1104313 = 828235) (by norm_num)
theorem B1104349 : Blo 980594 1104349 := bbase (se 3 (by rfl) ⟨207065, by rfl⟩ : syracuseStep 1104349 = 414131) (by norm_num)
theorem B3725797 : Blo 980594 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B1104385 : Blo 980594 1104385 := bbase (se 2 (by rfl) ⟨414144, by rfl⟩ : syracuseStep 1104385 = 828289) (by norm_num)
theorem B1104421 : Blo 980594 1104421 := bbase (se 4 (by rfl) ⟨103539, by rfl⟩ : syracuseStep 1104421 = 207079) (by norm_num)
theorem B1661485 : Blo 980594 1661485 := bbase (se 3 (by rfl) ⟨311528, by rfl⟩ : syracuseStep 1661485 = 623057) (by norm_num)
theorem B1104457 : Blo 980594 1104457 := bbase (se 2 (by rfl) ⟨414171, by rfl⟩ : syracuseStep 1104457 = 828343) (by norm_num)
theorem B1104493 : Blo 980594 1104493 := bbase (se 3 (by rfl) ⟨207092, by rfl⟩ : syracuseStep 1104493 = 414185) (by norm_num)
theorem B1104529 : Blo 980594 1104529 := bbase (se 2 (by rfl) ⟨414198, by rfl⟩ : syracuseStep 1104529 = 828397) (by norm_num)
theorem B1104565 : Blo 980594 1104565 := bbase (se 5 (by rfl) ⟨51776, by rfl⟩ : syracuseStep 1104565 = 103553) (by norm_num)
theorem B7461557 : Blo 980594 7461557 := bbase (se 5 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 7461557 = 699521) (by norm_num)
theorem B1104601 : Blo 980594 1104601 := bbase (se 2 (by rfl) ⟨414225, by rfl⟩ : syracuseStep 1104601 = 828451) (by norm_num)
theorem B1104637 : Blo 980594 1104637 := bbase (se 3 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 1104637 = 414239) (by norm_num)
theorem B3726101 : Blo 980594 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B16800533 : Blo 980594 16800533 := bbase (se 6 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 16800533 = 787525) (by norm_num)
theorem B1104673 : Blo 980594 1104673 := bbase (se 2 (by rfl) ⟨414252, by rfl⟩ : syracuseStep 1104673 = 828505) (by norm_num)
theorem B1104709 : Blo 980594 1104709 := bbase (se 4 (by rfl) ⟨103566, by rfl⟩ : syracuseStep 1104709 = 207133) (by norm_num)
theorem B1104745 : Blo 980594 1104745 := bbase (se 2 (by rfl) ⟨414279, by rfl⟩ : syracuseStep 1104745 = 828559) (by norm_num)
theorem B1891181 : Blo 980594 1891181 := bbase (se 3 (by rfl) ⟨354596, by rfl⟩ : syracuseStep 1891181 = 709193) (by norm_num)
theorem B1104781 : Blo 980594 1104781 := bbase (se 3 (by rfl) ⟨207146, by rfl⟩ : syracuseStep 1104781 = 414293) (by norm_num)
theorem B1104817 : Blo 980594 1104817 := bbase (se 2 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 1104817 = 828613) (by norm_num)
theorem B1104853 : Blo 980594 1104853 := bbase (se 7 (by rfl) ⟨12947, by rfl⟩ : syracuseStep 1104853 = 25895) (by norm_num)
theorem B1104889 : Blo 980594 1104889 := bbase (se 2 (by rfl) ⟨414333, by rfl⟩ : syracuseStep 1104889 = 828667) (by norm_num)
theorem B1104925 : Blo 980594 1104925 := bbase (se 3 (by rfl) ⟨207173, by rfl⟩ : syracuseStep 1104925 = 414347) (by norm_num)
theorem B1104961 : Blo 980594 1104961 := bbase (se 2 (by rfl) ⟨414360, by rfl⟩ : syracuseStep 1104961 = 828721) (by norm_num)
theorem B1104997 : Blo 980594 1104997 := bbase (se 4 (by rfl) ⟨103593, by rfl⟩ : syracuseStep 1104997 = 207187) (by norm_num)
theorem B1105033 : Blo 980594 1105033 := bbase (se 2 (by rfl) ⟨414387, by rfl⟩ : syracuseStep 1105033 = 828775) (by norm_num)
theorem B1105069 : Blo 980594 1105069 := bbase (se 3 (by rfl) ⟨207200, by rfl⟩ : syracuseStep 1105069 = 414401) (by norm_num)
theorem B1105105 : Blo 980594 1105105 := bbase (se 2 (by rfl) ⟨414414, by rfl⟩ : syracuseStep 1105105 = 828829) (by norm_num)
theorem B1105141 : Blo 980594 1105141 := bbase (se 5 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 1105141 = 103607) (by norm_num)
theorem B1105177 : Blo 980594 1105177 := bbase (se 2 (by rfl) ⟨414441, by rfl⟩ : syracuseStep 1105177 = 828883) (by norm_num)
theorem B1105213 : Blo 980594 1105213 := bbase (se 3 (by rfl) ⟨207227, by rfl⟩ : syracuseStep 1105213 = 414455) (by norm_num)
theorem B1105249 : Blo 980594 1105249 := bbase (se 2 (by rfl) ⟨414468, by rfl⟩ : syracuseStep 1105249 = 828937) (by norm_num)
theorem B1105285 : Blo 980594 1105285 := bbase (se 4 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 1105285 = 207241) (by norm_num)
theorem B5037461 : Blo 980594 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B4971941 : Blo 980594 4971941 := bbase (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) (by norm_num)
theorem B1105321 : Blo 980594 1105321 := bbase (se 2 (by rfl) ⟨414495, by rfl⟩ : syracuseStep 1105321 = 828991) (by norm_num)
theorem B1891765 : Blo 980594 1891765 := bbase (se 5 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 1891765 = 177353) (by norm_num)
theorem B1105357 : Blo 980594 1105357 := bbase (se 3 (by rfl) ⟨207254, by rfl⟩ : syracuseStep 1105357 = 414509) (by norm_num)
theorem B1105393 : Blo 980594 1105393 := bbase (se 2 (by rfl) ⟨414522, by rfl⟩ : syracuseStep 1105393 = 829045) (by norm_num)
theorem B1105429 : Blo 980594 1105429 := bbase (se 6 (by rfl) ⟨25908, by rfl⟩ : syracuseStep 1105429 = 51817) (by norm_num)
theorem B1400341 : Blo 980594 1400341 := bbase (se 6 (by rfl) ⟨32820, by rfl⟩ : syracuseStep 1400341 = 65641) (by norm_num)
theorem B1105465 : Blo 980594 1105465 := bbase (se 2 (by rfl) ⟨414549, by rfl⟩ : syracuseStep 1105465 = 829099) (by norm_num)
theorem B1105501 : Blo 980594 1105501 := bbase (se 3 (by rfl) ⟨207281, by rfl⟩ : syracuseStep 1105501 = 414563) (by norm_num)
theorem B1105537 : Blo 980594 1105537 := bbase (se 2 (by rfl) ⟨414576, by rfl⟩ : syracuseStep 1105537 = 829153) (by norm_num)
theorem B1105573 : Blo 980594 1105573 := bbase (se 4 (by rfl) ⟨103647, by rfl⟩ : syracuseStep 1105573 = 207295) (by norm_num)
theorem B1105609 : Blo 980594 1105609 := bbase (se 2 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 1105609 = 829207) (by norm_num)
theorem B3366629 : Blo 980594 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B1105645 : Blo 980594 1105645 := bbase (se 3 (by rfl) ⟨207308, by rfl⟩ : syracuseStep 1105645 = 414617) (by norm_num)
theorem B1105681 : Blo 980594 1105681 := bbase (se 2 (by rfl) ⟨414630, by rfl⟩ : syracuseStep 1105681 = 829261) (by norm_num)
theorem B1105717 : Blo 980594 1105717 := bbase (se 5 (by rfl) ⟨51830, by rfl⟩ : syracuseStep 1105717 = 103661) (by norm_num)
theorem B1892165 : Blo 980594 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1105753 : Blo 980594 1105753 := bbase (se 2 (by rfl) ⟨414657, by rfl⟩ : syracuseStep 1105753 = 829315) (by norm_num)
theorem B1105789 : Blo 980594 1105789 := bbase (se 3 (by rfl) ⟨207335, by rfl⟩ : syracuseStep 1105789 = 414671) (by norm_num)
theorem B1105825 : Blo 980594 1105825 := bbase (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) (by norm_num)
theorem B1105861 : Blo 980594 1105861 := bbase (se 4 (by rfl) ⟨103674, by rfl⟩ : syracuseStep 1105861 = 207349) (by norm_num)
theorem B1105897 : Blo 980594 1105897 := bbase (se 2 (by rfl) ⟨414711, by rfl⟩ : syracuseStep 1105897 = 829423) (by norm_num)
theorem B1105933 : Blo 980594 1105933 := bbase (se 3 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 1105933 = 414725) (by norm_num)
theorem B2154533 : Blo 980594 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B1105969 : Blo 980594 1105969 := bbase (se 2 (by rfl) ⟨414738, by rfl⟩ : syracuseStep 1105969 = 829477) (by norm_num)
theorem B1106005 : Blo 980594 1106005 := bbase (se 8 (by rfl) ⟨6480, by rfl⟩ : syracuseStep 1106005 = 12961) (by norm_num)
theorem B1400933 : Blo 980594 1400933 := bbase (se 4 (by rfl) ⟨131337, by rfl⟩ : syracuseStep 1400933 = 262675) (by norm_num)
theorem B2482285 : Blo 980594 2482285 := bbase (se 3 (by rfl) ⟨465428, by rfl⟩ : syracuseStep 2482285 = 930857) (by norm_num)
theorem B1106041 : Blo 980594 1106041 := bbase (se 2 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 1106041 = 829531) (by norm_num)
theorem B1106077 : Blo 980594 1106077 := bbase (se 3 (by rfl) ⟨207389, by rfl⟩ : syracuseStep 1106077 = 414779) (by norm_num)
theorem B1401013 : Blo 980594 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B1106113 : Blo 980594 1106113 := bbase (se 2 (by rfl) ⟨414792, by rfl⟩ : syracuseStep 1106113 = 829585) (by norm_num)
theorem B2482397 : Blo 980594 2482397 := bbase (se 3 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 2482397 = 930899) (by norm_num)
theorem B1106149 : Blo 980594 1106149 := bbase (se 4 (by rfl) ⟨103701, by rfl⟩ : syracuseStep 1106149 = 207403) (by norm_num)
theorem B1106185 : Blo 980594 1106185 := bbase (se 2 (by rfl) ⟨414819, by rfl⟩ : syracuseStep 1106185 = 829639) (by norm_num)
theorem B1106221 : Blo 980594 1106221 := bbase (se 3 (by rfl) ⟨207416, by rfl⟩ : syracuseStep 1106221 = 414833) (by norm_num)
theorem B1401133 : Blo 980594 1401133 := bbase (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) (by norm_num)
theorem B1106257 : Blo 980594 1106257 := bbase (se 2 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 1106257 = 829693) (by norm_num)
theorem B1106293 : Blo 980594 1106293 := bbase (se 5 (by rfl) ⟨51857, by rfl⟩ : syracuseStep 1106293 = 103715) (by norm_num)
theorem B1401229 : Blo 980594 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B1106329 : Blo 980594 1106329 := bbase (se 2 (by rfl) ⟨414873, by rfl⟩ : syracuseStep 1106329 = 829747) (by norm_num)
theorem B2482589 : Blo 980594 2482589 := bbase (se 3 (by rfl) ⟨465485, by rfl⟩ : syracuseStep 2482589 = 930971) (by norm_num)
theorem B1106365 : Blo 980594 1106365 := bbase (se 3 (by rfl) ⟨207443, by rfl⟩ : syracuseStep 1106365 = 414887) (by norm_num)
theorem B1106401 : Blo 980594 1106401 := bbase (se 2 (by rfl) ⟨414900, by rfl⟩ : syracuseStep 1106401 = 829801) (by norm_num)
theorem B1106437 : Blo 980594 1106437 := bbase (se 4 (by rfl) ⟨103728, by rfl⟩ : syracuseStep 1106437 = 207457) (by norm_num)
theorem B1106473 : Blo 980594 1106473 := bbase (se 2 (by rfl) ⟨414927, by rfl⟩ : syracuseStep 1106473 = 829855) (by norm_num)
theorem B1106509 : Blo 980594 1106509 := bbase (se 3 (by rfl) ⟨207470, by rfl⟩ : syracuseStep 1106509 = 414941) (by norm_num)
theorem B1106545 : Blo 980594 1106545 := bbase (se 2 (by rfl) ⟨414954, by rfl⟩ : syracuseStep 1106545 = 829909) (by norm_num)
theorem B1106581 : Blo 980594 1106581 := bbase (se 6 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 1106581 = 51871) (by norm_num)
theorem B1991341 : Blo 980594 1991341 := bbase (se 3 (by rfl) ⟨373376, by rfl⟩ : syracuseStep 1991341 = 746753) (by norm_num)
theorem B4973237 : Blo 980594 4973237 := bbase (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) (by norm_num)
theorem B1106617 : Blo 980594 1106617 := bbase (se 2 (by rfl) ⟨414981, by rfl⟩ : syracuseStep 1106617 = 829963) (by norm_num)
theorem B1106653 : Blo 980594 1106653 := bbase (se 3 (by rfl) ⟨207497, by rfl⟩ : syracuseStep 1106653 = 414995) (by norm_num)
theorem B1991405 : Blo 980594 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B2482933 : Blo 980594 2482933 := bbase (se 5 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 2482933 = 232775) (by norm_num)
theorem B1106689 : Blo 980594 1106689 := bbase (se 2 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 1106689 = 830017) (by norm_num)
theorem B1106725 : Blo 980594 1106725 := bbase (se 4 (by rfl) ⟨103755, by rfl⟩ : syracuseStep 1106725 = 207511) (by norm_num)
theorem B1106761 : Blo 980594 1106761 := bbase (se 2 (by rfl) ⟨415035, by rfl⟩ : syracuseStep 1106761 = 830071) (by norm_num)
theorem B3728213 : Blo 980594 3728213 := bbase (se 9 (by rfl) ⟨10922, by rfl⟩ : syracuseStep 3728213 = 21845) (by norm_num)
theorem B2483045 : Blo 980594 2483045 := bbase (se 4 (by rfl) ⟨232785, by rfl⟩ : syracuseStep 2483045 = 465571) (by norm_num)
theorem B1106797 : Blo 980594 1106797 := bbase (se 3 (by rfl) ⟨207524, by rfl⟩ : syracuseStep 1106797 = 415049) (by norm_num)
theorem B1401725 : Blo 980594 1401725 := bbase (se 3 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 1401725 = 525647) (by norm_num)
theorem B1106833 : Blo 980594 1106833 := bbase (se 2 (by rfl) ⟨415062, by rfl⟩ : syracuseStep 1106833 = 830125) (by norm_num)
theorem B1106869 : Blo 980594 1106869 := bbase (se 5 (by rfl) ⟨51884, by rfl⟩ : syracuseStep 1106869 = 103769) (by norm_num)
theorem B1106905 : Blo 980594 1106905 := bbase (se 2 (by rfl) ⟨415089, by rfl⟩ : syracuseStep 1106905 = 830179) (by norm_num)
theorem B1106941 : Blo 980594 1106941 := bbase (se 3 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 1106941 = 415103) (by norm_num)
theorem B1106977 : Blo 980594 1106977 := bbase (se 2 (by rfl) ⟨415116, by rfl⟩ : syracuseStep 1106977 = 830233) (by norm_num)
theorem B2483237 : Blo 980594 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B1107013 : Blo 980594 1107013 := bbase (se 4 (by rfl) ⟨103782, by rfl⟩ : syracuseStep 1107013 = 207565) (by norm_num)
theorem B1107049 : Blo 980594 1107049 := bbase (se 2 (by rfl) ⟨415143, by rfl⟩ : syracuseStep 1107049 = 830287) (by norm_num)
theorem B3728501 : Blo 980594 3728501 := bbase (se 5 (by rfl) ⟨174773, by rfl⟩ : syracuseStep 3728501 = 349547) (by norm_num)
theorem B1107085 : Blo 980594 1107085 := bbase (se 3 (by rfl) ⟨207578, by rfl⟩ : syracuseStep 1107085 = 415157) (by norm_num)
theorem B1107121 : Blo 980594 1107121 := bbase (se 2 (by rfl) ⟨415170, by rfl⟩ : syracuseStep 1107121 = 830341) (by norm_num)
theorem B1107157 : Blo 980594 1107157 := bbase (se 7 (by rfl) ⟨12974, by rfl⟩ : syracuseStep 1107157 = 25949) (by norm_num)
theorem B1008865 : Blo 980594 1008865 := bbase (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) (by norm_num)
theorem B1107193 : Blo 980594 1107193 := bbase (se 2 (by rfl) ⟨415197, by rfl⟩ : syracuseStep 1107193 = 830395) (by norm_num)
theorem B1991965 : Blo 980594 1991965 := bbase (se 3 (by rfl) ⟨373493, by rfl⟩ : syracuseStep 1991965 = 746987) (by norm_num)
theorem B1107229 : Blo 980594 1107229 := bbase (se 3 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 1107229 = 415211) (by norm_num)
theorem B1107265 : Blo 980594 1107265 := bbase (se 2 (by rfl) ⟨415224, by rfl⟩ : syracuseStep 1107265 = 830449) (by norm_num)
theorem B1107301 : Blo 980594 1107301 := bbase (se 4 (by rfl) ⟨103809, by rfl⟩ : syracuseStep 1107301 = 207619) (by norm_num)
theorem B2483581 : Blo 980594 2483581 := bbase (se 3 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 2483581 = 931343) (by norm_num)
theorem B1107337 : Blo 980594 1107337 := bbase (se 2 (by rfl) ⟨415251, by rfl⟩ : syracuseStep 1107337 = 830503) (by norm_num)
theorem B1107373 : Blo 980594 1107373 := bbase (se 3 (by rfl) ⟨207632, by rfl⟩ : syracuseStep 1107373 = 415265) (by norm_num)
theorem B1107409 : Blo 980594 1107409 := bbase (se 2 (by rfl) ⟨415278, by rfl⟩ : syracuseStep 1107409 = 830557) (by norm_num)
theorem B2483693 : Blo 980594 2483693 := bbase (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) (by norm_num)
theorem B1107445 : Blo 980594 1107445 := bbase (se 5 (by rfl) ⟨51911, by rfl⟩ : syracuseStep 1107445 = 103823) (by norm_num)
theorem B1107481 : Blo 980594 1107481 := bbase (se 2 (by rfl) ⟨415305, by rfl⟩ : syracuseStep 1107481 = 830611) (by norm_num)
theorem B1107517 : Blo 980594 1107517 := bbase (se 3 (by rfl) ⟨207659, by rfl⟩ : syracuseStep 1107517 = 415319) (by norm_num)
theorem B1107553 : Blo 980594 1107553 := bbase (se 2 (by rfl) ⟨415332, by rfl⟩ : syracuseStep 1107553 = 830665) (by norm_num)
theorem B1107589 : Blo 980594 1107589 := bbase (se 4 (by rfl) ⟨103836, by rfl⟩ : syracuseStep 1107589 = 207673) (by norm_num)
theorem B1107625 : Blo 980594 1107625 := bbase (se 2 (by rfl) ⟨415359, by rfl⟩ : syracuseStep 1107625 = 830719) (by norm_num)
theorem B2483885 : Blo 980594 2483885 := bbase (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) (by norm_num)
theorem B1107661 : Blo 980594 1107661 := bbase (se 3 (by rfl) ⟨207686, by rfl⟩ : syracuseStep 1107661 = 415373) (by norm_num)
theorem B4548325 : Blo 980594 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B1795949 : Blo 980594 1795949 := bbase (se 3 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 1795949 = 673481) (by norm_num)
theorem B4974533 : Blo 980594 4974533 := bbase (se 4 (by rfl) ⟨466362, by rfl⟩ : syracuseStep 4974533 = 932725) (by norm_num)
theorem B4777973 : Blo 980594 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B2484229 : Blo 980594 2484229 := bbase (se 4 (by rfl) ⟨232896, by rfl⟩ : syracuseStep 2484229 = 465793) (by norm_num)
theorem B2484341 : Blo 980594 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B1009813 : Blo 980594 1009813 := bbase (se 6 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 1009813 = 47335) (by norm_num)
theorem B1861805 : Blo 980594 1861805 := bbase (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) (by norm_num)
theorem B3729685 : Blo 980594 3729685 := bbase (se 6 (by rfl) ⟨87414, by rfl⟩ : syracuseStep 3729685 = 174829) (by norm_num)
theorem B2484533 : Blo 980594 2484533 := bbase (se 5 (by rfl) ⟨116462, by rfl⟩ : syracuseStep 2484533 = 232925) (by norm_num)
theorem B1861957 : Blo 980594 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B1993229 : Blo 980594 1993229 := bbase (se 3 (by rfl) ⟨373730, by rfl⟩ : syracuseStep 1993229 = 747461) (by norm_num)
theorem B3729989 : Blo 980594 3729989 := bbase (se 4 (by rfl) ⟨349686, by rfl⟩ : syracuseStep 3729989 = 699373) (by norm_num)
theorem B4188773 : Blo 980594 4188773 := bbase (se 4 (by rfl) ⟨392697, by rfl⟩ : syracuseStep 4188773 = 785395) (by norm_num)
theorem B1862261 : Blo 980594 1862261 := bbase (se 5 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 1862261 = 174587) (by norm_num)
theorem B2484877 : Blo 980594 2484877 := bbase (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) (by norm_num)
theorem B2484989 : Blo 980594 2484989 := bbase (se 3 (by rfl) ⟨465935, by rfl⟩ : syracuseStep 2484989 = 931871) (by norm_num)
theorem B7269173 : Blo 980594 7269173 := bbase (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) (by norm_num)
theorem B2485181 : Blo 980594 2485181 := bbase (se 3 (by rfl) ⟨465971, by rfl⟩ : syracuseStep 2485181 = 931943) (by norm_num)
theorem B6286517 : Blo 980594 6286517 := bbase (se 5 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 6286517 = 589361) (by norm_num)
theorem B4975829 : Blo 980594 4975829 := bbase (se 7 (by rfl) ⟨58310, by rfl⟩ : syracuseStep 4975829 = 116621) (by norm_num)
theorem B2485525 : Blo 980594 2485525 := bbase (se 6 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 2485525 = 116509) (by norm_num)
theorem B11201813 : Blo 980594 11201813 := bbase (se 6 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 11201813 = 525085) (by norm_num)
theorem B1863013 : Blo 980594 1863013 := bbase (se 4 (by rfl) ⟨174657, by rfl⟩ : syracuseStep 1863013 = 349315) (by norm_num)
theorem B2485637 : Blo 980594 2485637 := bbase (se 4 (by rfl) ⟨233028, by rfl⟩ : syracuseStep 2485637 = 466057) (by norm_num)
theorem B1011133 : Blo 980594 1011133 := bbase (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) (by norm_num)
theorem B1863157 : Blo 980594 1863157 := bbase (se 5 (by rfl) ⟨87335, by rfl⟩ : syracuseStep 1863157 = 174671) (by norm_num)
theorem B2485829 : Blo 980594 2485829 := bbase (se 4 (by rfl) ⟨233046, by rfl⟩ : syracuseStep 2485829 = 466093) (by norm_num)
theorem B1863317 : Blo 980594 1863317 := bbase (se 6 (by rfl) ⟨43671, by rfl⟩ : syracuseStep 1863317 = 87343) (by norm_num)
theorem B1535645 : Blo 980594 1535645 := bbase (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) (by norm_num)
theorem B1994429 : Blo 980594 1994429 := bbase (se 3 (by rfl) ⟨373955, by rfl⟩ : syracuseStep 1994429 = 747911) (by norm_num)
theorem B1863461 : Blo 980594 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B7958357 : Blo 980594 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B2486173 : Blo 980594 2486173 := bbase (se 3 (by rfl) ⟨466157, by rfl⟩ : syracuseStep 2486173 = 932315) (by norm_num)
theorem B1241077 : Blo 980594 1241077 := bbase (se 5 (by rfl) ⟨58175, by rfl⟩ : syracuseStep 1241077 = 116351) (by norm_num)
theorem B2486285 : Blo 980594 2486285 := bbase (se 3 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 2486285 = 932357) (by norm_num)
theorem B1863749 : Blo 980594 1863749 := bbase (se 4 (by rfl) ⟨174726, by rfl⟩ : syracuseStep 1863749 = 349453) (by norm_num)
theorem B1241173 : Blo 980594 1241173 := bbase (se 8 (by rfl) ⟨7272, by rfl⟩ : syracuseStep 1241173 = 14545) (by norm_num)
theorem B2486477 : Blo 980594 2486477 := bbase (se 3 (by rfl) ⟨466214, by rfl⟩ : syracuseStep 2486477 = 932429) (by norm_num)
theorem B1863901 : Blo 980594 1863901 := bbase (se 3 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 1863901 = 698963) (by norm_num)
theorem B1241345 : Blo 980594 1241345 := bbase (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) (by norm_num)
theorem B1241401 : Blo 980594 1241401 := bbase (se 2 (by rfl) ⟨465525, by rfl⟩ : syracuseStep 1241401 = 931051) (by norm_num)
theorem B1241497 : Blo 980594 1241497 := bbase (se 2 (by rfl) ⟨465561, by rfl⟩ : syracuseStep 1241497 = 931123) (by norm_num)
theorem B1470893 : Blo 980594 1470893 := bbase (se 3 (by rfl) ⟨275792, by rfl⟩ : syracuseStep 1470893 = 551585) (by norm_num)
theorem B1438133 : Blo 980594 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B1470917 : Blo 980594 1470917 := bbase (se 4 (by rfl) ⟨137898, by rfl⟩ : syracuseStep 1470917 = 275797) (by norm_num)
theorem B1470941 : Blo 980594 1470941 := bbase (se 3 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 1470941 = 551603) (by norm_num)
theorem B4977125 : Blo 980594 4977125 := bbase (se 4 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 4977125 = 933211) (by norm_num)
theorem B1470965 : Blo 980594 1470965 := bbase (se 5 (by rfl) ⟨68951, by rfl⟩ : syracuseStep 1470965 = 137903) (by norm_num)
theorem B1470989 : Blo 980594 1470989 := bbase (se 3 (by rfl) ⟨275810, by rfl⟩ : syracuseStep 1470989 = 551621) (by norm_num)
theorem B1864205 : Blo 980594 1864205 := bbase (se 3 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 1864205 = 699077) (by norm_num)
theorem B1471013 : Blo 980594 1471013 := bbase (se 4 (by rfl) ⟨137907, by rfl⟩ : syracuseStep 1471013 = 275815) (by norm_num)
theorem B2486821 : Blo 980594 2486821 := bbase (se 4 (by rfl) ⟨233139, by rfl⟩ : syracuseStep 2486821 = 466279) (by norm_num)
theorem B1471037 : Blo 980594 1471037 := bbase (se 3 (by rfl) ⟨275819, by rfl⟩ : syracuseStep 1471037 = 551639) (by norm_num)
theorem B1241669 : Blo 980594 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B1471061 : Blo 980594 1471061 := bbase (se 8 (by rfl) ⟨8619, by rfl⟩ : syracuseStep 1471061 = 17239) (by norm_num)
theorem B1471085 : Blo 980594 1471085 := bbase (se 3 (by rfl) ⟨275828, by rfl⟩ : syracuseStep 1471085 = 551657) (by norm_num)
theorem B1241725 : Blo 980594 1241725 := bbase (se 3 (by rfl) ⟨232823, by rfl⟩ : syracuseStep 1241725 = 465647) (by norm_num)
theorem B1471109 : Blo 980594 1471109 := bbase (se 4 (by rfl) ⟨137916, by rfl⟩ : syracuseStep 1471109 = 275833) (by norm_num)
theorem B3732101 : Blo 980594 3732101 := bbase (se 4 (by rfl) ⟨349884, by rfl⟩ : syracuseStep 3732101 = 699769) (by norm_num)
theorem B2486933 : Blo 980594 2486933 := bbase (se 6 (by rfl) ⟨58287, by rfl⟩ : syracuseStep 2486933 = 116575) (by norm_num)
theorem B1471133 : Blo 980594 1471133 := bbase (se 3 (by rfl) ⟨275837, by rfl⟩ : syracuseStep 1471133 = 551675) (by norm_num)
theorem B3142309 : Blo 980594 3142309 := bbase (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) (by norm_num)
theorem B1471157 : Blo 980594 1471157 := bbase (se 5 (by rfl) ⟨68960, by rfl⟩ : syracuseStep 1471157 = 137921) (by norm_num)
theorem B1471181 : Blo 980594 1471181 := bbase (se 3 (by rfl) ⟨275846, by rfl⟩ : syracuseStep 1471181 = 551693) (by norm_num)
theorem B1241821 : Blo 980594 1241821 := bbase (se 3 (by rfl) ⟨232841, by rfl⟩ : syracuseStep 1241821 = 465683) (by norm_num)
theorem B1471205 : Blo 980594 1471205 := bbase (se 4 (by rfl) ⟨137925, by rfl⟩ : syracuseStep 1471205 = 275851) (by norm_num)
theorem B1471229 : Blo 980594 1471229 := bbase (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) (by norm_num)
theorem B1471253 : Blo 980594 1471253 := bbase (se 6 (by rfl) ⟨34482, by rfl⟩ : syracuseStep 1471253 = 68965) (by norm_num)
theorem B1471277 : Blo 980594 1471277 := bbase (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) (by norm_num)
theorem B1471301 : Blo 980594 1471301 := bbase (se 4 (by rfl) ⟨137934, by rfl⟩ : syracuseStep 1471301 = 275869) (by norm_num)
theorem B2487125 : Blo 980594 2487125 := bbase (se 9 (by rfl) ⟨7286, by rfl⟩ : syracuseStep 2487125 = 14573) (by norm_num)
theorem B1471325 : Blo 980594 1471325 := bbase (se 3 (by rfl) ⟨275873, by rfl⟩ : syracuseStep 1471325 = 551747) (by norm_num)
theorem B1471349 : Blo 980594 1471349 := bbase (se 5 (by rfl) ⟨68969, by rfl⟩ : syracuseStep 1471349 = 137939) (by norm_num)
theorem B1241993 : Blo 980594 1241993 := bbase (se 2 (by rfl) ⟨465747, by rfl⟩ : syracuseStep 1241993 = 931495) (by norm_num)
theorem B1471373 : Blo 980594 1471373 := bbase (se 3 (by rfl) ⟨275882, by rfl⟩ : syracuseStep 1471373 = 551765) (by norm_num)
theorem B1471397 : Blo 980594 1471397 := bbase (se 4 (by rfl) ⟨137943, by rfl⟩ : syracuseStep 1471397 = 275887) (by norm_num)
theorem B3732389 : Blo 980594 3732389 := bbase (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) (by norm_num)
theorem B1471421 : Blo 980594 1471421 := bbase (se 3 (by rfl) ⟨275891, by rfl⟩ : syracuseStep 1471421 = 551783) (by norm_num)
theorem B1242049 : Blo 980594 1242049 := bbase (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) (by norm_num)
theorem B1471445 : Blo 980594 1471445 := bbase (se 7 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 1471445 = 34487) (by norm_num)
theorem B1471469 : Blo 980594 1471469 := bbase (se 3 (by rfl) ⟨275900, by rfl⟩ : syracuseStep 1471469 = 551801) (by norm_num)
theorem B1471493 : Blo 980594 1471493 := bbase (se 4 (by rfl) ⟨137952, by rfl⟩ : syracuseStep 1471493 = 275905) (by norm_num)
theorem B1471517 : Blo 980594 1471517 := bbase (se 3 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 1471517 = 551819) (by norm_num)
theorem B1242145 : Blo 980594 1242145 := bbase (se 2 (by rfl) ⟨465804, by rfl⟩ : syracuseStep 1242145 = 931609) (by norm_num)
theorem B3142709 : Blo 980594 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B1471541 : Blo 980594 1471541 := bbase (se 5 (by rfl) ⟨68978, by rfl⟩ : syracuseStep 1471541 = 137957) (by norm_num)
theorem B1471565 : Blo 980594 1471565 := bbase (se 3 (by rfl) ⟨275918, by rfl⟩ : syracuseStep 1471565 = 551837) (by norm_num)
theorem B1471589 : Blo 980594 1471589 := bbase (se 4 (by rfl) ⟨137961, by rfl⟩ : syracuseStep 1471589 = 275923) (by norm_num)
theorem B1471613 : Blo 980594 1471613 := bbase (se 3 (by rfl) ⟨275927, by rfl⟩ : syracuseStep 1471613 = 551855) (by norm_num)
theorem B1471637 : Blo 980594 1471637 := bbase (se 6 (by rfl) ⟨34491, by rfl⟩ : syracuseStep 1471637 = 68983) (by norm_num)
theorem B3536021 : Blo 980594 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B1471661 : Blo 980594 1471661 := bbase (se 3 (by rfl) ⟨275936, by rfl⟩ : syracuseStep 1471661 = 551873) (by norm_num)
theorem B2487469 : Blo 980594 2487469 := bbase (se 3 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 2487469 = 932801) (by norm_num)
theorem B1471685 : Blo 980594 1471685 := bbase (se 4 (by rfl) ⟨137970, by rfl⟩ : syracuseStep 1471685 = 275941) (by norm_num)
theorem B1242317 : Blo 980594 1242317 := bbase (se 3 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 1242317 = 465869) (by norm_num)
theorem B1471709 : Blo 980594 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B1471733 : Blo 980594 1471733 := bbase (se 5 (by rfl) ⟨68987, by rfl⟩ : syracuseStep 1471733 = 137975) (by norm_num)
theorem B1864957 : Blo 980594 1864957 := bbase (se 3 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 1864957 = 699359) (by norm_num)
theorem B1242373 : Blo 980594 1242373 := bbase (se 4 (by rfl) ⟨116472, by rfl⟩ : syracuseStep 1242373 = 232945) (by norm_num)
theorem B1471757 : Blo 980594 1471757 := bbase (se 3 (by rfl) ⟨275954, by rfl⟩ : syracuseStep 1471757 = 551909) (by norm_num)
theorem B2487581 : Blo 980594 2487581 := bbase (se 3 (by rfl) ⟨466421, by rfl⟩ : syracuseStep 2487581 = 932843) (by norm_num)
theorem B1471781 : Blo 980594 1471781 := bbase (se 4 (by rfl) ⟨137979, by rfl⟩ : syracuseStep 1471781 = 275959) (by norm_num)
theorem B1471805 : Blo 980594 1471805 := bbase (se 3 (by rfl) ⟨275963, by rfl⟩ : syracuseStep 1471805 = 551927) (by norm_num)
theorem B1471829 : Blo 980594 1471829 := bbase (se 13 (by rfl) ⟨269, by rfl⟩ : syracuseStep 1471829 = 539) (by norm_num)
theorem B1242469 : Blo 980594 1242469 := bbase (se 4 (by rfl) ⟨116481, by rfl⟩ : syracuseStep 1242469 = 232963) (by norm_num)
theorem B1471853 : Blo 980594 1471853 := bbase (se 3 (by rfl) ⟨275972, by rfl⟩ : syracuseStep 1471853 = 551945) (by norm_num)
theorem B1471877 : Blo 980594 1471877 := bbase (se 4 (by rfl) ⟨137988, by rfl⟩ : syracuseStep 1471877 = 275977) (by norm_num)
theorem B1865101 : Blo 980594 1865101 := bbase (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) (by norm_num)
theorem B1471901 : Blo 980594 1471901 := bbase (se 3 (by rfl) ⟨275981, by rfl⟩ : syracuseStep 1471901 = 551963) (by norm_num)
theorem B1471925 : Blo 980594 1471925 := bbase (se 5 (by rfl) ⟨68996, by rfl⟩ : syracuseStep 1471925 = 137993) (by norm_num)
theorem B1471949 : Blo 980594 1471949 := bbase (se 3 (by rfl) ⟨275990, by rfl⟩ : syracuseStep 1471949 = 551981) (by norm_num)
theorem B2553293 : Blo 980594 2553293 := bbase (se 3 (by rfl) ⟨478742, by rfl⟩ : syracuseStep 2553293 = 957485) (by norm_num)
theorem B2487773 : Blo 980594 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B1471973 : Blo 980594 1471973 := bbase (se 4 (by rfl) ⟨137997, by rfl⟩ : syracuseStep 1471973 = 275995) (by norm_num)
theorem B1471997 : Blo 980594 1471997 := bbase (se 3 (by rfl) ⟨275999, by rfl⟩ : syracuseStep 1471997 = 551999) (by norm_num)
theorem B1242641 : Blo 980594 1242641 := bbase (se 2 (by rfl) ⟨465990, by rfl⟩ : syracuseStep 1242641 = 931981) (by norm_num)
theorem B1472021 : Blo 980594 1472021 := bbase (se 6 (by rfl) ⟨34500, by rfl⟩ : syracuseStep 1472021 = 69001) (by norm_num)
theorem B1472045 : Blo 980594 1472045 := bbase (se 3 (by rfl) ⟨276008, by rfl⟩ : syracuseStep 1472045 = 552017) (by norm_num)
theorem B1865261 : Blo 980594 1865261 := bbase (se 3 (by rfl) ⟨349736, by rfl⟩ : syracuseStep 1865261 = 699473) (by norm_num)
theorem B1078849 : Blo 980594 1078849 := bbase (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) (by norm_num)
theorem B1472069 : Blo 980594 1472069 := bbase (se 4 (by rfl) ⟨138006, by rfl⟩ : syracuseStep 1472069 = 276013) (by norm_num)
theorem B1242697 : Blo 980594 1242697 := bbase (se 2 (by rfl) ⟨466011, by rfl⟩ : syracuseStep 1242697 = 932023) (by norm_num)
theorem B1472093 : Blo 980594 1472093 := bbase (se 3 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 1472093 = 552035) (by norm_num)
theorem B1472117 : Blo 980594 1472117 := bbase (se 5 (by rfl) ⟨69005, by rfl⟩ : syracuseStep 1472117 = 138011) (by norm_num)
theorem B1472141 : Blo 980594 1472141 := bbase (se 3 (by rfl) ⟨276026, by rfl⟩ : syracuseStep 1472141 = 552053) (by norm_num)
theorem B1472165 : Blo 980594 1472165 := bbase (se 4 (by rfl) ⟨138015, by rfl⟩ : syracuseStep 1472165 = 276031) (by norm_num)
theorem B1242793 : Blo 980594 1242793 := bbase (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) (by norm_num)
theorem B1472189 : Blo 980594 1472189 := bbase (se 3 (by rfl) ⟨276035, by rfl⟩ : syracuseStep 1472189 = 552071) (by norm_num)
theorem B1865405 : Blo 980594 1865405 := bbase (se 3 (by rfl) ⟨349763, by rfl⟩ : syracuseStep 1865405 = 699527) (by norm_num)
theorem B2094797 : Blo 980594 2094797 := bbase (se 3 (by rfl) ⟨392774, by rfl⟩ : syracuseStep 2094797 = 785549) (by norm_num)
theorem B1472213 : Blo 980594 1472213 := bbase (se 7 (by rfl) ⟨17252, by rfl⟩ : syracuseStep 1472213 = 34505) (by norm_num)
theorem B1472237 : Blo 980594 1472237 := bbase (se 3 (by rfl) ⟨276044, by rfl⟩ : syracuseStep 1472237 = 552089) (by norm_num)
theorem B4978421 : Blo 980594 4978421 := bbase (se 5 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 4978421 = 466727) (by norm_num)
theorem B1472261 : Blo 980594 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B8386325 : Blo 980594 8386325 := bbase (se 6 (by rfl) ⟨196554, by rfl⟩ : syracuseStep 8386325 = 393109) (by norm_num)
theorem B1472285 : Blo 980594 1472285 := bbase (se 3 (by rfl) ⟨276053, by rfl⟩ : syracuseStep 1472285 = 552107) (by norm_num)
theorem B2520877 : Blo 980594 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B1472309 : Blo 980594 1472309 := bbase (se 5 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 1472309 = 138029) (by norm_num)
theorem B2488117 : Blo 980594 2488117 := bbase (se 5 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 2488117 = 233261) (by norm_num)
theorem B4192069 : Blo 980594 4192069 := bbase (se 4 (by rfl) ⟨393006, by rfl⟩ : syracuseStep 4192069 = 786013) (by norm_num)
theorem B1472333 : Blo 980594 1472333 := bbase (se 3 (by rfl) ⟨276062, by rfl⟩ : syracuseStep 1472333 = 552125) (by norm_num)
theorem B1242965 : Blo 980594 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B2094941 : Blo 980594 2094941 := bbase (se 3 (by rfl) ⟨392801, by rfl⟩ : syracuseStep 2094941 = 785603) (by norm_num)
theorem B1472357 : Blo 980594 1472357 := bbase (se 4 (by rfl) ⟨138033, by rfl⟩ : syracuseStep 1472357 = 276067) (by norm_num)
theorem B2357117 : Blo 980594 2357117 := bbase (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) (by norm_num)
theorem B1472381 : Blo 980594 1472381 := bbase (se 3 (by rfl) ⟨276071, by rfl⟩ : syracuseStep 1472381 = 552143) (by norm_num)
theorem B1243021 : Blo 980594 1243021 := bbase (se 3 (by rfl) ⟨233066, by rfl⟩ : syracuseStep 1243021 = 466133) (by norm_num)
theorem B1472405 : Blo 980594 1472405 := bbase (se 6 (by rfl) ⟨34509, by rfl⟩ : syracuseStep 1472405 = 69019) (by norm_num)
theorem B2488229 : Blo 980594 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B1472429 : Blo 980594 1472429 := bbase (se 3 (by rfl) ⟨276080, by rfl⟩ : syracuseStep 1472429 = 552161) (by norm_num)
theorem B1472453 : Blo 980594 1472453 := bbase (se 4 (by rfl) ⟨138042, by rfl⟩ : syracuseStep 1472453 = 276085) (by norm_num)
theorem B1472477 : Blo 980594 1472477 := bbase (se 3 (by rfl) ⟨276089, by rfl⟩ : syracuseStep 1472477 = 552179) (by norm_num)
theorem B1865693 : Blo 980594 1865693 := bbase (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) (by norm_num)
theorem B1243117 : Blo 980594 1243117 := bbase (se 3 (by rfl) ⟨233084, by rfl⟩ : syracuseStep 1243117 = 466169) (by norm_num)
theorem B1472501 : Blo 980594 1472501 := bbase (se 5 (by rfl) ⟨69023, by rfl⟩ : syracuseStep 1472501 = 138047) (by norm_num)
theorem B1472525 : Blo 980594 1472525 := bbase (se 3 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 1472525 = 552197) (by norm_num)
theorem B1472549 : Blo 980594 1472549 := bbase (se 4 (by rfl) ⟨138051, by rfl⟩ : syracuseStep 1472549 = 276103) (by norm_num)
theorem B2357309 : Blo 980594 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B1472573 : Blo 980594 1472573 := bbase (se 3 (by rfl) ⟨276107, by rfl⟩ : syracuseStep 1472573 = 552215) (by norm_num)
theorem B3733573 : Blo 980594 3733573 := bbase (se 4 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 3733573 = 700045) (by norm_num)
theorem B1472597 : Blo 980594 1472597 := bbase (se 8 (by rfl) ⟨8628, by rfl⟩ : syracuseStep 1472597 = 17257) (by norm_num)
theorem B2488421 : Blo 980594 2488421 := bbase (se 4 (by rfl) ⟨233289, by rfl⟩ : syracuseStep 2488421 = 466579) (by norm_num)
theorem B1472621 : Blo 980594 1472621 := bbase (se 3 (by rfl) ⟨276116, by rfl⟩ : syracuseStep 1472621 = 552233) (by norm_num)
theorem B2652277 : Blo 980594 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B1865845 : Blo 980594 1865845 := bbase (se 5 (by rfl) ⟨87461, by rfl⟩ : syracuseStep 1865845 = 174923) (by norm_num)
theorem B1472645 : Blo 980594 1472645 := bbase (se 4 (by rfl) ⟨138060, by rfl⟩ : syracuseStep 1472645 = 276121) (by norm_num)
theorem B1243289 : Blo 980594 1243289 := bbase (se 2 (by rfl) ⟨466233, by rfl⟩ : syracuseStep 1243289 = 932467) (by norm_num)
theorem B1472669 : Blo 980594 1472669 := bbase (se 3 (by rfl) ⟨276125, by rfl⟩ : syracuseStep 1472669 = 552251) (by norm_num)
theorem B1472693 : Blo 980594 1472693 := bbase (se 5 (by rfl) ⟨69032, by rfl⟩ : syracuseStep 1472693 = 138065) (by norm_num)
theorem B2095301 : Blo 980594 2095301 := bbase (se 4 (by rfl) ⟨196434, by rfl⟩ : syracuseStep 2095301 = 392869) (by norm_num)
theorem B1472717 : Blo 980594 1472717 := bbase (se 3 (by rfl) ⟨276134, by rfl⟩ : syracuseStep 1472717 = 552269) (by norm_num)
theorem B1243345 : Blo 980594 1243345 := bbase (se 2 (by rfl) ⟨466254, by rfl⟩ : syracuseStep 1243345 = 932509) (by norm_num)
theorem B1472741 : Blo 980594 1472741 := bbase (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) (by norm_num)
theorem B1472765 : Blo 980594 1472765 := bbase (se 3 (by rfl) ⟨276143, by rfl⟩ : syracuseStep 1472765 = 552287) (by norm_num)
theorem B7469333 : Blo 980594 7469333 := bbase (se 6 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 7469333 = 350125) (by norm_num)
theorem B1472789 : Blo 980594 1472789 := bbase (se 6 (by rfl) ⟨34518, by rfl⟩ : syracuseStep 1472789 = 69037) (by norm_num)
theorem B1472813 : Blo 980594 1472813 := bbase (se 3 (by rfl) ⟨276152, by rfl⟩ : syracuseStep 1472813 = 552305) (by norm_num)
theorem B1243441 : Blo 980594 1243441 := bbase (se 2 (by rfl) ⟨466290, by rfl⟩ : syracuseStep 1243441 = 932581) (by norm_num)
theorem B1472837 : Blo 980594 1472837 := bbase (se 4 (by rfl) ⟨138078, by rfl⟩ : syracuseStep 1472837 = 276157) (by norm_num)
theorem B1472861 : Blo 980594 1472861 := bbase (se 3 (by rfl) ⟨276161, by rfl⟩ : syracuseStep 1472861 = 552323) (by norm_num)
theorem B1472885 : Blo 980594 1472885 := bbase (se 5 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 1472885 = 138083) (by norm_num)
theorem B3733877 : Blo 980594 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B1472909 : Blo 980594 1472909 := bbase (se 3 (by rfl) ⟨276170, by rfl⟩ : syracuseStep 1472909 = 552341) (by norm_num)
theorem B1472933 : Blo 980594 1472933 := bbase (se 4 (by rfl) ⟨138087, by rfl⟩ : syracuseStep 1472933 = 276175) (by norm_num)
theorem B1866149 : Blo 980594 1866149 := bbase (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) (by norm_num)
theorem B1472957 : Blo 980594 1472957 := bbase (se 3 (by rfl) ⟨276179, by rfl⟩ : syracuseStep 1472957 = 552359) (by norm_num)
theorem B2488765 : Blo 980594 2488765 := bbase (se 3 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 2488765 = 933287) (by norm_num)
theorem B1472981 : Blo 980594 1472981 := bbase (se 7 (by rfl) ⟨17261, by rfl⟩ : syracuseStep 1472981 = 34523) (by norm_num)
theorem B1243613 : Blo 980594 1243613 := bbase (se 3 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 1243613 = 466355) (by norm_num)
theorem B1571309 : Blo 980594 1571309 := bbase (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) (by norm_num)
theorem B1473005 : Blo 980594 1473005 := bbase (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) (by norm_num)
theorem B4487669 : Blo 980594 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B1473029 : Blo 980594 1473029 := bbase (se 4 (by rfl) ⟨138096, by rfl⟩ : syracuseStep 1473029 = 276193) (by norm_num)
theorem B2521613 : Blo 980594 2521613 := bbase (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) (by norm_num)
theorem B1243669 : Blo 980594 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B1473053 : Blo 980594 1473053 := bbase (se 3 (by rfl) ⟨276197, by rfl⟩ : syracuseStep 1473053 = 552395) (by norm_num)
theorem B2652709 : Blo 980594 2652709 := bbase (se 4 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 2652709 = 497383) (by norm_num)
theorem B2488877 : Blo 980594 2488877 := bbase (se 3 (by rfl) ⟨466664, by rfl⟩ : syracuseStep 2488877 = 933329) (by norm_num)
theorem B1473077 : Blo 980594 1473077 := bbase (se 5 (by rfl) ⟨69050, by rfl⟩ : syracuseStep 1473077 = 138101) (by norm_num)
theorem B1571405 : Blo 980594 1571405 := bbase (se 3 (by rfl) ⟨294638, by rfl⟩ : syracuseStep 1571405 = 589277) (by norm_num)
theorem B1473101 : Blo 980594 1473101 := bbase (se 3 (by rfl) ⟨276206, by rfl⟩ : syracuseStep 1473101 = 552413) (by norm_num)
theorem B1473125 : Blo 980594 1473125 := bbase (se 4 (by rfl) ⟨138105, by rfl⟩ : syracuseStep 1473125 = 276211) (by norm_num)
theorem B1571437 : Blo 980594 1571437 := bbase (se 3 (by rfl) ⟨294644, by rfl⟩ : syracuseStep 1571437 = 589289) (by norm_num)
theorem B1243765 : Blo 980594 1243765 := bbase (se 5 (by rfl) ⟨58301, by rfl⟩ : syracuseStep 1243765 = 116603) (by norm_num)
theorem B1473149 : Blo 980594 1473149 := bbase (se 3 (by rfl) ⟨276215, by rfl⟩ : syracuseStep 1473149 = 552431) (by norm_num)
theorem B7961237 : Blo 980594 7961237 := bbase (se 6 (by rfl) ⟨186591, by rfl⟩ : syracuseStep 7961237 = 373183) (by norm_num)
theorem B1473173 : Blo 980594 1473173 := bbase (se 6 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 1473173 = 69055) (by norm_num)
theorem B1473197 : Blo 980594 1473197 := bbase (se 3 (by rfl) ⟨276224, by rfl⟩ : syracuseStep 1473197 = 552449) (by norm_num)
theorem B1473221 : Blo 980594 1473221 := bbase (se 4 (by rfl) ⟨138114, by rfl⟩ : syracuseStep 1473221 = 276229) (by norm_num)
theorem B1473245 : Blo 980594 1473245 := bbase (se 3 (by rfl) ⟨276233, by rfl⟩ : syracuseStep 1473245 = 552467) (by norm_num)
theorem B2489069 : Blo 980594 2489069 := bbase (se 3 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 2489069 = 933401) (by norm_num)
theorem B1473269 : Blo 980594 1473269 := bbase (se 5 (by rfl) ⟨69059, by rfl⟩ : syracuseStep 1473269 = 138119) (by norm_num)
theorem B1473293 : Blo 980594 1473293 := bbase (se 3 (by rfl) ⟨276242, by rfl⟩ : syracuseStep 1473293 = 552485) (by norm_num)
theorem B1243937 : Blo 980594 1243937 := bbase (se 2 (by rfl) ⟨466476, by rfl⟩ : syracuseStep 1243937 = 932953) (by norm_num)
theorem B4717349 : Blo 980594 4717349 := bbase (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) (by norm_num)
theorem B1473317 : Blo 980594 1473317 := bbase (se 4 (by rfl) ⟨138123, by rfl⟩ : syracuseStep 1473317 = 276247) (by norm_num)
theorem B1473341 : Blo 980594 1473341 := bbase (se 3 (by rfl) ⟨276251, by rfl⟩ : syracuseStep 1473341 = 552503) (by norm_num)
theorem B1047377 : Blo 980594 1047377 := bbase (se 2 (by rfl) ⟨392766, by rfl⟩ : syracuseStep 1047377 = 785533) (by norm_num)
theorem B1473365 : Blo 980594 1473365 := bbase (se 9 (by rfl) ⟨4316, by rfl⟩ : syracuseStep 1473365 = 8633) (by norm_num)
theorem B1243993 : Blo 980594 1243993 := bbase (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) (by norm_num)
theorem B3406693 : Blo 980594 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B1473389 : Blo 980594 1473389 := bbase (se 3 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 1473389 = 552521) (by norm_num)
theorem B1473413 : Blo 980594 1473413 := bbase (se 4 (by rfl) ⟨138132, by rfl⟩ : syracuseStep 1473413 = 276265) (by norm_num)
theorem B1473437 : Blo 980594 1473437 := bbase (se 3 (by rfl) ⟨276269, by rfl⟩ : syracuseStep 1473437 = 552539) (by norm_num)
theorem B1473461 : Blo 980594 1473461 := bbase (se 5 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 1473461 = 138137) (by norm_num)
theorem B5602229 : Blo 980594 5602229 := bbase (se 5 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 5602229 = 525209) (by norm_num)
theorem B1244089 : Blo 980594 1244089 := bbase (se 2 (by rfl) ⟨466533, by rfl⟩ : syracuseStep 1244089 = 933067) (by norm_num)
theorem B1473485 : Blo 980594 1473485 := bbase (se 3 (by rfl) ⟨276278, by rfl⟩ : syracuseStep 1473485 = 552557) (by norm_num)
theorem B1178597 : Blo 980594 1178597 := bbase (se 4 (by rfl) ⟨110493, by rfl⟩ : syracuseStep 1178597 = 220987) (by norm_num)
theorem B4717541 : Blo 980594 4717541 := bbase (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) (by norm_num)
theorem B1473509 : Blo 980594 1473509 := bbase (se 4 (by rfl) ⟨138141, by rfl⟩ : syracuseStep 1473509 = 276283) (by norm_num)
theorem B1768429 : Blo 980594 1768429 := bbase (se 3 (by rfl) ⟨331580, by rfl⟩ : syracuseStep 1768429 = 663161) (by norm_num)
theorem B2128877 : Blo 980594 2128877 := bbase (se 3 (by rfl) ⟨399164, by rfl⟩ : syracuseStep 2128877 = 798329) (by norm_num)
theorem B1473533 : Blo 980594 1473533 := bbase (se 3 (by rfl) ⟨276287, by rfl⟩ : syracuseStep 1473533 = 552575) (by norm_num)
theorem B4979717 : Blo 980594 4979717 := bbase (se 4 (by rfl) ⟨466848, by rfl⟩ : syracuseStep 4979717 = 933697) (by norm_num)
theorem B1178645 : Blo 980594 1178645 := bbase (se 6 (by rfl) ⟨27624, by rfl⟩ : syracuseStep 1178645 = 55249) (by norm_num)
theorem B1473557 : Blo 980594 1473557 := bbase (se 6 (by rfl) ⟨34536, by rfl⟩ : syracuseStep 1473557 = 69073) (by norm_num)
theorem B1473581 : Blo 980594 1473581 := bbase (se 3 (by rfl) ⟨276296, by rfl⟩ : syracuseStep 1473581 = 552593) (by norm_num)
theorem B2096189 : Blo 980594 2096189 := bbase (se 3 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 2096189 = 786071) (by norm_num)
theorem B1473605 : Blo 980594 1473605 := bbase (se 4 (by rfl) ⟨138150, by rfl⟩ : syracuseStep 1473605 = 276301) (by norm_num)
theorem B2489413 : Blo 980594 2489413 := bbase (se 4 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 2489413 = 466765) (by norm_num)
theorem B1473629 : Blo 980594 1473629 := bbase (se 3 (by rfl) ⟨276305, by rfl⟩ : syracuseStep 1473629 = 552611) (by norm_num)
theorem B1244261 : Blo 980594 1244261 := bbase (se 4 (by rfl) ⟨116649, by rfl⟩ : syracuseStep 1244261 = 233299) (by norm_num)
theorem B1473653 : Blo 980594 1473653 := bbase (se 5 (by rfl) ⟨69077, by rfl⟩ : syracuseStep 1473653 = 138155) (by norm_num)
theorem B1473677 : Blo 980594 1473677 := bbase (se 3 (by rfl) ⟨276314, by rfl⟩ : syracuseStep 1473677 = 552629) (by norm_num)
theorem B1866901 : Blo 980594 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B1244317 : Blo 980594 1244317 := bbase (se 3 (by rfl) ⟨233309, by rfl⟩ : syracuseStep 1244317 = 466619) (by norm_num)
theorem B1473701 : Blo 980594 1473701 := bbase (se 4 (by rfl) ⟨138159, by rfl⟩ : syracuseStep 1473701 = 276319) (by norm_num)
theorem B2489525 : Blo 980594 2489525 := bbase (se 5 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 2489525 = 233393) (by norm_num)
theorem B1473725 : Blo 980594 1473725 := bbase (se 3 (by rfl) ⟨276323, by rfl⟩ : syracuseStep 1473725 = 552647) (by norm_num)
theorem B1768645 : Blo 980594 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B1473749 : Blo 980594 1473749 := bbase (se 7 (by rfl) ⟨17270, by rfl⟩ : syracuseStep 1473749 = 34541) (by norm_num)
theorem B1473773 : Blo 980594 1473773 := bbase (se 3 (by rfl) ⟨276332, by rfl⟩ : syracuseStep 1473773 = 552665) (by norm_num)
theorem B1244413 : Blo 980594 1244413 := bbase (se 3 (by rfl) ⟨233327, by rfl⟩ : syracuseStep 1244413 = 466655) (by norm_num)
theorem B1473797 : Blo 980594 1473797 := bbase (se 4 (by rfl) ⟨138168, by rfl⟩ : syracuseStep 1473797 = 276337) (by norm_num)
theorem B1047821 : Blo 980594 1047821 := bbase (se 3 (by rfl) ⟨196466, by rfl⟩ : syracuseStep 1047821 = 392933) (by norm_num)
theorem B1473821 : Blo 980594 1473821 := bbase (se 3 (by rfl) ⟨276341, by rfl⟩ : syracuseStep 1473821 = 552683) (by norm_num)
theorem B1867045 : Blo 980594 1867045 := bbase (se 4 (by rfl) ⟨175035, by rfl⟩ : syracuseStep 1867045 = 350071) (by norm_num)
theorem B2096437 : Blo 980594 2096437 := bbase (se 5 (by rfl) ⟨98270, by rfl⟩ : syracuseStep 2096437 = 196541) (by norm_num)
theorem B1473845 : Blo 980594 1473845 := bbase (se 5 (by rfl) ⟨69086, by rfl⟩ : syracuseStep 1473845 = 138173) (by norm_num)
theorem B1473869 : Blo 980594 1473869 := bbase (se 3 (by rfl) ⟨276350, by rfl⟩ : syracuseStep 1473869 = 552701) (by norm_num)
theorem B4717925 : Blo 980594 4717925 := bbase (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) (by norm_num)
theorem B1473893 : Blo 980594 1473893 := bbase (se 4 (by rfl) ⟨138177, by rfl⟩ : syracuseStep 1473893 = 276355) (by norm_num)
theorem B2489717 : Blo 980594 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B1473917 : Blo 980594 1473917 := bbase (se 3 (by rfl) ⟨276359, by rfl⟩ : syracuseStep 1473917 = 552719) (by norm_num)
theorem B2653573 : Blo 980594 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B1473941 : Blo 980594 1473941 := bbase (se 6 (by rfl) ⟨34545, by rfl⟩ : syracuseStep 1473941 = 69091) (by norm_num)
theorem B1244585 : Blo 980594 1244585 := bbase (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) (by norm_num)
theorem B1473965 : Blo 980594 1473965 := bbase (se 3 (by rfl) ⟨276368, by rfl⟩ : syracuseStep 1473965 = 552737) (by norm_num)
theorem B1473989 : Blo 980594 1473989 := bbase (se 4 (by rfl) ⟨138186, by rfl⟩ : syracuseStep 1473989 = 276373) (by norm_num)
theorem B1867205 : Blo 980594 1867205 := bbase (se 4 (by rfl) ⟨175050, by rfl⟩ : syracuseStep 1867205 = 350101) (by norm_num)
theorem B1474013 : Blo 980594 1474013 := bbase (se 3 (by rfl) ⟨276377, by rfl⟩ : syracuseStep 1474013 = 552755) (by norm_num)
theorem B1244641 : Blo 980594 1244641 := bbase (se 2 (by rfl) ⟨466740, by rfl⟩ : syracuseStep 1244641 = 933481) (by norm_num)
theorem B1768933 : Blo 980594 1768933 := bbase (se 4 (by rfl) ⟨165837, by rfl⟩ : syracuseStep 1768933 = 331675) (by norm_num)
theorem B1474037 : Blo 980594 1474037 := bbase (se 5 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 1474037 = 138191) (by norm_num)
theorem B1048069 : Blo 980594 1048069 := bbase (se 4 (by rfl) ⟨98256, by rfl⟩ : syracuseStep 1048069 = 196513) (by norm_num)
theorem B1474061 : Blo 980594 1474061 := bbase (se 3 (by rfl) ⟨276386, by rfl⟩ : syracuseStep 1474061 = 552773) (by norm_num)
theorem B1474085 : Blo 980594 1474085 := bbase (se 4 (by rfl) ⟨138195, by rfl⟩ : syracuseStep 1474085 = 276391) (by norm_num)
theorem B1179193 : Blo 980594 1179193 := bbase (se 2 (by rfl) ⟨442197, by rfl⟩ : syracuseStep 1179193 = 884395) (by norm_num)
theorem B1474109 : Blo 980594 1474109 := bbase (se 3 (by rfl) ⟨276395, by rfl⟩ : syracuseStep 1474109 = 552791) (by norm_num)
theorem B1244737 : Blo 980594 1244737 := bbase (se 2 (by rfl) ⟨466776, by rfl⟩ : syracuseStep 1244737 = 933553) (by norm_num)
theorem B1474133 : Blo 980594 1474133 := bbase (se 8 (by rfl) ⟨8637, by rfl⟩ : syracuseStep 1474133 = 17275) (by norm_num)
theorem B1867349 : Blo 980594 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B2358877 : Blo 980594 2358877 := bbase (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) (by norm_num)
theorem B1474157 : Blo 980594 1474157 := bbase (se 3 (by rfl) ⟨276404, by rfl⟩ : syracuseStep 1474157 = 552809) (by norm_num)
theorem B1474181 : Blo 980594 1474181 := bbase (se 4 (by rfl) ⟨138204, by rfl⟩ : syracuseStep 1474181 = 276409) (by norm_num)
theorem B1474205 : Blo 980594 1474205 := bbase (se 3 (by rfl) ⟨276413, by rfl⟩ : syracuseStep 1474205 = 552827) (by norm_num)
theorem B1474229 : Blo 980594 1474229 := bbase (se 5 (by rfl) ⟨69104, by rfl⟩ : syracuseStep 1474229 = 138209) (by norm_num)
theorem B1474253 : Blo 980594 1474253 := bbase (se 3 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 1474253 = 552845) (by norm_num)
theorem B2490061 : Blo 980594 2490061 := bbase (se 3 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 2490061 = 933773) (by norm_num)
theorem B1474277 : Blo 980594 1474277 := bbase (se 4 (by rfl) ⟨138213, by rfl⟩ : syracuseStep 1474277 = 276427) (by norm_num)
theorem B1244909 : Blo 980594 1244909 := bbase (se 3 (by rfl) ⟨233420, by rfl⟩ : syracuseStep 1244909 = 466841) (by norm_num)
theorem B1474301 : Blo 980594 1474301 := bbase (se 3 (by rfl) ⟨276431, by rfl⟩ : syracuseStep 1474301 = 552863) (by norm_num)
theorem B1474325 : Blo 980594 1474325 := bbase (se 6 (by rfl) ⟨34554, by rfl⟩ : syracuseStep 1474325 = 69109) (by norm_num)
theorem B1244965 : Blo 980594 1244965 := bbase (se 4 (by rfl) ⟨116715, by rfl⟩ : syracuseStep 1244965 = 233431) (by norm_num)
theorem B2096941 : Blo 980594 2096941 := bbase (se 3 (by rfl) ⟨393176, by rfl⟩ : syracuseStep 2096941 = 786353) (by norm_num)
theorem B1474349 : Blo 980594 1474349 := bbase (se 3 (by rfl) ⟨276440, by rfl⟩ : syracuseStep 1474349 = 552881) (by norm_num)
theorem B2490173 : Blo 980594 2490173 := bbase (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) (by norm_num)
theorem B1474373 : Blo 980594 1474373 := bbase (se 4 (by rfl) ⟨138222, by rfl⟩ : syracuseStep 1474373 = 276445) (by norm_num)
theorem B1474397 : Blo 980594 1474397 := bbase (se 3 (by rfl) ⟨276449, by rfl⟩ : syracuseStep 1474397 = 552899) (by norm_num)
theorem B1703789 : Blo 980594 1703789 := bbase (se 3 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 1703789 = 638921) (by norm_num)
theorem B1474421 : Blo 980594 1474421 := bbase (se 5 (by rfl) ⟨69113, by rfl⟩ : syracuseStep 1474421 = 138227) (by norm_num)
theorem B1867637 : Blo 980594 1867637 := bbase (se 5 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 1867637 = 175091) (by norm_num)
theorem B1245061 : Blo 980594 1245061 := bbase (se 4 (by rfl) ⟨116724, by rfl⟩ : syracuseStep 1245061 = 233449) (by norm_num)
theorem B1474445 : Blo 980594 1474445 := bbase (se 3 (by rfl) ⟨276458, by rfl⟩ : syracuseStep 1474445 = 552917) (by norm_num)
theorem B1474469 : Blo 980594 1474469 := bbase (se 4 (by rfl) ⟨138231, by rfl⟩ : syracuseStep 1474469 = 276463) (by norm_num)
theorem B1474493 : Blo 980594 1474493 := bbase (se 3 (by rfl) ⟨276467, by rfl⟩ : syracuseStep 1474493 = 552935) (by norm_num)
theorem B1048513 : Blo 980594 1048513 := bbase (se 2 (by rfl) ⟨393192, by rfl⟩ : syracuseStep 1048513 = 786385) (by norm_num)
theorem B1474517 : Blo 980594 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B1474541 : Blo 980594 1474541 := bbase (se 3 (by rfl) ⟨276476, by rfl⟩ : syracuseStep 1474541 = 552953) (by norm_num)
theorem B1048573 : Blo 980594 1048573 := bbase (se 3 (by rfl) ⟨196607, by rfl⟩ : syracuseStep 1048573 = 393215) (by norm_num)
theorem B2490365 : Blo 980594 2490365 := bbase (se 3 (by rfl) ⟨466943, by rfl⟩ : syracuseStep 2490365 = 933887) (by norm_num)
theorem B983043 : Blo 980594 983043 := bstep (se 1 (by rfl) ⟨737282, by rfl⟩ : syracuseStep 983043 = 1474565) B1474565
theorem B1474577 : Blo 980594 1474577 := bstep (se 2 (by rfl) ⟨552966, by rfl⟩ : syracuseStep 1474577 = 1105933) B1105933
theorem B2490385 : Blo 980594 2490385 := bstep (se 2 (by rfl) ⟨933894, by rfl⟩ : syracuseStep 2490385 = 1867789) B1867789
theorem B983059 : Blo 980594 983059 := bstep (se 1 (by rfl) ⟨737294, by rfl⟩ : syracuseStep 983059 = 1474589) B1474589
theorem B1474595 : Blo 980594 1474595 := bstep (se 1 (by rfl) ⟨1105946, by rfl⟩ : syracuseStep 1474595 = 2211893) B2211893
theorem B983075 : Blo 980594 983075 := bstep (se 1 (by rfl) ⟨737306, by rfl⟩ : syracuseStep 983075 = 1474613) B1474613
theorem B983091 : Blo 980594 983091 := bstep (se 1 (by rfl) ⟨737318, by rfl⟩ : syracuseStep 983091 = 1474637) B1474637
theorem B1474625 : Blo 980594 1474625 := bstep (se 2 (by rfl) ⟨552984, by rfl⟩ : syracuseStep 1474625 = 1105969) B1105969
theorem B983107 : Blo 980594 983107 := bstep (se 1 (by rfl) ⟨737330, by rfl⟩ : syracuseStep 983107 = 1474661) B1474661
theorem B1179731 : Blo 980594 1179731 := bstep (se 1 (by rfl) ⟨884798, by rfl⟩ : syracuseStep 1179731 = 1769597) B1769597
theorem B1474643 : Blo 980594 1474643 := bstep (se 1 (by rfl) ⟨1105982, by rfl⟩ : syracuseStep 1474643 = 2211965) B2211965
theorem B983123 : Blo 980594 983123 := bstep (se 1 (by rfl) ⟨737342, by rfl⟩ : syracuseStep 983123 = 1474685) B1474685
theorem B983139 : Blo 980594 983139 := bstep (se 1 (by rfl) ⟨737354, by rfl⟩ : syracuseStep 983139 = 1474709) B1474709
theorem B2097265 : Blo 980594 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1474673 : Blo 980594 1474673 := bstep (se 2 (by rfl) ⟨553002, by rfl⟩ : syracuseStep 1474673 = 1106005) B1106005
theorem B983155 : Blo 980594 983155 := bstep (se 1 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 983155 = 1474733) B1474733
theorem B1572995 : Blo 980594 1572995 := bstep (se 1 (by rfl) ⟨1179746, by rfl⟩ : syracuseStep 1572995 = 2359493) B2359493
theorem B1474691 : Blo 980594 1474691 := bstep (se 1 (by rfl) ⟨1106018, by rfl⟩ : syracuseStep 1474691 = 2212037) B2212037
theorem B6291589 : Blo 980594 6291589 := bstep (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) B1179673
theorem B983171 : Blo 980594 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B3309713 : Blo 980594 3309713 := bstep (se 2 (by rfl) ⟨1241142, by rfl⟩ : syracuseStep 3309713 = 2482285) B2482285
theorem B983187 : Blo 980594 983187 := bstep (se 1 (by rfl) ⟨737390, by rfl⟩ : syracuseStep 983187 = 1474781) B1474781
theorem B1474721 : Blo 980594 1474721 := bstep (se 2 (by rfl) ⟨553020, by rfl⟩ : syracuseStep 1474721 = 1106041) B1106041
theorem B983203 : Blo 980594 983203 := bstep (se 1 (by rfl) ⟨737402, by rfl⟩ : syracuseStep 983203 = 1474805) B1474805
theorem B1474739 : Blo 980594 1474739 := bstep (se 1 (by rfl) ⟨1106054, by rfl⟩ : syracuseStep 1474739 = 2212109) B2212109
theorem B983219 : Blo 980594 983219 := bstep (se 1 (by rfl) ⟨737414, by rfl⟩ : syracuseStep 983219 = 1474829) B1474829
theorem B983235 : Blo 980594 983235 := bstep (se 1 (by rfl) ⟨737426, by rfl⟩ : syracuseStep 983235 = 1474853) B1474853
theorem B1474769 : Blo 980594 1474769 := bstep (se 2 (by rfl) ⟨553038, by rfl⟩ : syracuseStep 1474769 = 1106077) B1106077
theorem B983251 : Blo 980594 983251 := bstep (se 1 (by rfl) ⟨737438, by rfl⟩ : syracuseStep 983251 = 1474877) B1474877
theorem B1245395 : Blo 980594 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B1474787 : Blo 980594 1474787 := bstep (se 1 (by rfl) ⟨1106090, by rfl⟩ : syracuseStep 1474787 = 2212181) B2212181
theorem B983267 : Blo 980594 983267 := bstep (se 1 (by rfl) ⟨737450, by rfl⟩ : syracuseStep 983267 = 1474901) B1474901
theorem B983283 : Blo 980594 983283 := bstep (se 1 (by rfl) ⟨737462, by rfl⟩ : syracuseStep 983283 = 1474925) B1474925
theorem B1868017 : Blo 980594 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B1474817 : Blo 980594 1474817 := bstep (se 2 (by rfl) ⟨553056, by rfl⟩ : syracuseStep 1474817 = 1106113) B1106113
theorem B983299 : Blo 980594 983299 := bstep (se 1 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 983299 = 1474949) B1474949
theorem B3735821 : Blo 980594 3735821 := bstep (se 3 (by rfl) ⟨700466, by rfl⟩ : syracuseStep 3735821 = 1400933) B1400933
theorem B1474835 : Blo 980594 1474835 := bstep (se 1 (by rfl) ⟨1106126, by rfl⟩ : syracuseStep 1474835 = 2212253) B2212253
theorem B983315 : Blo 980594 983315 := bstep (se 1 (by rfl) ⟨737486, by rfl⟩ : syracuseStep 983315 = 1474973) B1474973
theorem B983331 : Blo 980594 983331 := bstep (se 1 (by rfl) ⟨737498, by rfl⟩ : syracuseStep 983331 = 1474997) B1474997
theorem B2490659 : Blo 980594 2490659 := bstep (se 1 (by rfl) ⟨1867994, by rfl⟩ : syracuseStep 2490659 = 3735989) B3735989
theorem B1474865 : Blo 980594 1474865 := bstep (se 2 (by rfl) ⟨553074, by rfl⟩ : syracuseStep 1474865 = 1106149) B1106149
theorem B983347 : Blo 980594 983347 := bstep (se 1 (by rfl) ⟨737510, by rfl⟩ : syracuseStep 983347 = 1475021) B1475021
theorem B1474883 : Blo 980594 1474883 := bstep (se 1 (by rfl) ⟨1106162, by rfl⟩ : syracuseStep 1474883 = 2212325) B2212325
theorem B983363 : Blo 980594 983363 := bstep (se 1 (by rfl) ⟨737522, by rfl⟩ : syracuseStep 983363 = 1475045) B1475045
theorem B983379 : Blo 980594 983379 := bstep (se 1 (by rfl) ⟨737534, by rfl⟩ : syracuseStep 983379 = 1475069) B1475069
theorem B1474913 : Blo 980594 1474913 := bstep (se 2 (by rfl) ⟨553092, by rfl⟩ : syracuseStep 1474913 = 1106185) B1106185
theorem B983395 : Blo 980594 983395 := bstep (se 1 (by rfl) ⟨737546, by rfl⟩ : syracuseStep 983395 = 1475093) B1475093
theorem B1474931 : Blo 980594 1474931 := bstep (se 1 (by rfl) ⟨1106198, by rfl⟩ : syracuseStep 1474931 = 2212397) B2212397
theorem B983411 : Blo 980594 983411 := bstep (se 1 (by rfl) ⟨737558, by rfl⟩ : syracuseStep 983411 = 1475117) B1475117
theorem B983427 : Blo 980594 983427 := bstep (se 1 (by rfl) ⟨737570, by rfl⟩ : syracuseStep 983427 = 1475141) B1475141
theorem B1474961 : Blo 980594 1474961 := bstep (se 2 (by rfl) ⟨553110, by rfl⟩ : syracuseStep 1474961 = 1106221) B1106221
theorem B983443 : Blo 980594 983443 := bstep (se 1 (by rfl) ⟨737582, by rfl⟩ : syracuseStep 983443 = 1475165) B1475165
theorem B1868177 : Blo 980594 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B1474979 : Blo 980594 1474979 := bstep (se 1 (by rfl) ⟨1106234, by rfl⟩ : syracuseStep 1474979 = 2212469) B2212469
theorem B983459 : Blo 980594 983459 := bstep (se 1 (by rfl) ⟨737594, by rfl⟩ : syracuseStep 983459 = 1475189) B1475189
theorem B983475 : Blo 980594 983475 := bstep (se 1 (by rfl) ⟨737606, by rfl⟩ : syracuseStep 983475 = 1475213) B1475213
theorem B1475009 : Blo 980594 1475009 := bstep (se 2 (by rfl) ⟨553128, by rfl⟩ : syracuseStep 1475009 = 1106257) B1106257
theorem B983491 : Blo 980594 983491 := bstep (se 1 (by rfl) ⟨737618, by rfl⟩ : syracuseStep 983491 = 1475237) B1475237
theorem B1475027 : Blo 980594 1475027 := bstep (se 1 (by rfl) ⟨1106270, by rfl⟩ : syracuseStep 1475027 = 2212541) B2212541
theorem B983507 : Blo 980594 983507 := bstep (se 1 (by rfl) ⟨737630, by rfl⟩ : syracuseStep 983507 = 1475261) B1475261
theorem B4194787 : Blo 980594 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B983523 : Blo 980594 983523 := bstep (se 1 (by rfl) ⟨737642, by rfl⟩ : syracuseStep 983523 = 1475285) B1475285
theorem B2490851 : Blo 980594 2490851 := bstep (se 1 (by rfl) ⟨1868138, by rfl⟩ : syracuseStep 2490851 = 3736277) B3736277
theorem B1475057 : Blo 980594 1475057 := bstep (se 2 (by rfl) ⟨553146, by rfl⟩ : syracuseStep 1475057 = 1106293) B1106293
theorem B983539 : Blo 980594 983539 := bstep (se 1 (by rfl) ⟨737654, by rfl⟩ : syracuseStep 983539 = 1475309) B1475309
theorem B2097667 : Blo 980594 2097667 := bstep (se 1 (by rfl) ⟨1573250, by rfl⟩ : syracuseStep 2097667 = 3146501) B3146501
theorem B1475075 : Blo 980594 1475075 := bstep (se 1 (by rfl) ⟨1106306, by rfl⟩ : syracuseStep 1475075 = 2212613) B2212613
theorem B983555 : Blo 980594 983555 := bstep (se 1 (by rfl) ⟨737666, by rfl⟩ : syracuseStep 983555 = 1475333) B1475333
theorem B1049107 : Blo 980594 1049107 := bstep (se 1 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 1049107 = 1573661) B1573661
theorem B983571 : Blo 980594 983571 := bstep (se 1 (by rfl) ⟨737678, by rfl⟩ : syracuseStep 983571 = 1475357) B1475357
theorem B1475105 : Blo 980594 1475105 := bstep (se 2 (by rfl) ⟨553164, by rfl⟩ : syracuseStep 1475105 = 1106329) B1106329
theorem B983587 : Blo 980594 983587 := bstep (se 1 (by rfl) ⟨737690, by rfl⟩ : syracuseStep 983587 = 1475381) B1475381
theorem B1475123 : Blo 980594 1475123 := bstep (se 1 (by rfl) ⟨1106342, by rfl⟩ : syracuseStep 1475123 = 2212685) B2212685
theorem B983603 : Blo 980594 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B11960885 : Blo 980594 11960885 := bstep (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) B1121333
theorem B983619 : Blo 980594 983619 := bstep (se 1 (by rfl) ⟨737714, by rfl⟩ : syracuseStep 983619 = 1475429) B1475429
theorem B1475153 : Blo 980594 1475153 := bstep (se 2 (by rfl) ⟨553182, by rfl⟩ : syracuseStep 1475153 = 1106365) B1106365
theorem B983635 : Blo 980594 983635 := bstep (se 1 (by rfl) ⟨737726, by rfl⟩ : syracuseStep 983635 = 1475453) B1475453
theorem B1475171 : Blo 980594 1475171 := bstep (se 1 (by rfl) ⟨1106378, by rfl⟩ : syracuseStep 1475171 = 2212757) B2212757
theorem B983651 : Blo 980594 983651 := bstep (se 1 (by rfl) ⟨737738, by rfl⟩ : syracuseStep 983651 = 1475477) B1475477
theorem B983667 : Blo 980594 983667 := bstep (se 1 (by rfl) ⟨737750, by rfl⟩ : syracuseStep 983667 = 1475501) B1475501
theorem B1475201 : Blo 980594 1475201 := bstep (se 2 (by rfl) ⟨553200, by rfl⟩ : syracuseStep 1475201 = 1106401) B1106401
theorem B983683 : Blo 980594 983683 := bstep (se 1 (by rfl) ⟨737762, by rfl⟩ : syracuseStep 983683 = 1475525) B1475525
theorem B1475219 : Blo 980594 1475219 := bstep (se 1 (by rfl) ⟨1106414, by rfl⟩ : syracuseStep 1475219 = 2212829) B2212829
theorem B983699 : Blo 980594 983699 := bstep (se 1 (by rfl) ⟨737774, by rfl⟩ : syracuseStep 983699 = 1475549) B1475549
theorem B983715 : Blo 980594 983715 := bstep (se 1 (by rfl) ⟨737786, by rfl⟩ : syracuseStep 983715 = 1475573) B1475573
theorem B3310253 : Blo 980594 3310253 := bstep (se 3 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 3310253 = 1241345) B1241345
theorem B2654893 : Blo 980594 2654893 := bstep (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) B995585
theorem B1475249 : Blo 980594 1475249 := bstep (se 2 (by rfl) ⟨553218, by rfl⟩ : syracuseStep 1475249 = 1106437) B1106437
theorem B983731 : Blo 980594 983731 := bstep (se 1 (by rfl) ⟨737798, by rfl⟩ : syracuseStep 983731 = 1475597) B1475597
theorem B1475267 : Blo 980594 1475267 := bstep (se 1 (by rfl) ⟨1106450, by rfl⟩ : syracuseStep 1475267 = 2212901) B2212901
theorem B983747 : Blo 980594 983747 := bstep (se 1 (by rfl) ⟨737810, by rfl⟩ : syracuseStep 983747 = 1475621) B1475621
theorem B983763 : Blo 980594 983763 := bstep (se 1 (by rfl) ⟨737822, by rfl⟩ : syracuseStep 983763 = 1475645) B1475645
theorem B1475297 : Blo 980594 1475297 := bstep (se 2 (by rfl) ⟨553236, by rfl⟩ : syracuseStep 1475297 = 1106473) B1106473
theorem B3310307 : Blo 980594 3310307 := bstep (se 1 (by rfl) ⟨2482730, by rfl⟩ : syracuseStep 3310307 = 4965461) B4965461
theorem B983779 : Blo 980594 983779 := bstep (se 1 (by rfl) ⟨737834, by rfl⟩ : syracuseStep 983779 = 1475669) B1475669
theorem B2654957 : Blo 980594 2654957 := bstep (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) B995609
theorem B1475315 : Blo 980594 1475315 := bstep (se 1 (by rfl) ⟨1106486, by rfl⟩ : syracuseStep 1475315 = 2212973) B2212973
theorem B983795 : Blo 980594 983795 := bstep (se 1 (by rfl) ⟨737846, by rfl⟩ : syracuseStep 983795 = 1475693) B1475693
theorem B983811 : Blo 980594 983811 := bstep (se 1 (by rfl) ⟨737858, by rfl⟩ : syracuseStep 983811 = 1475717) B1475717
theorem B1475345 : Blo 980594 1475345 := bstep (se 2 (by rfl) ⟨553254, by rfl⟩ : syracuseStep 1475345 = 1106509) B1106509
theorem B983827 : Blo 980594 983827 := bstep (se 1 (by rfl) ⟨737870, by rfl⟩ : syracuseStep 983827 = 1475741) B1475741
theorem B1475363 : Blo 980594 1475363 := bstep (se 1 (by rfl) ⟨1106522, by rfl⟩ : syracuseStep 1475363 = 2213045) B2213045
theorem B983843 : Blo 980594 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B1868579 : Blo 980594 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B983859 : Blo 980594 983859 := bstep (se 1 (by rfl) ⟨737894, by rfl⟩ : syracuseStep 983859 = 1475789) B1475789
theorem B1475393 : Blo 980594 1475393 := bstep (se 2 (by rfl) ⟨553272, by rfl⟩ : syracuseStep 1475393 = 1106545) B1106545
theorem B983875 : Blo 980594 983875 := bstep (se 1 (by rfl) ⟨737906, by rfl⟩ : syracuseStep 983875 = 1475813) B1475813
theorem B1475411 : Blo 980594 1475411 := bstep (se 1 (by rfl) ⟨1106558, by rfl⟩ : syracuseStep 1475411 = 2213117) B2213117
theorem B983891 : Blo 980594 983891 := bstep (se 1 (by rfl) ⟨737918, by rfl⟩ : syracuseStep 983891 = 1475837) B1475837
theorem B983907 : Blo 980594 983907 := bstep (se 1 (by rfl) ⟨737930, by rfl⟩ : syracuseStep 983907 = 1475861) B1475861
theorem B1475441 : Blo 980594 1475441 := bstep (se 2 (by rfl) ⟨553290, by rfl⟩ : syracuseStep 1475441 = 1106581) B1106581
theorem B983923 : Blo 980594 983923 := bstep (se 1 (by rfl) ⟨737942, by rfl⟩ : syracuseStep 983923 = 1475885) B1475885
theorem B1475459 : Blo 980594 1475459 := bstep (se 1 (by rfl) ⟨1106594, by rfl⟩ : syracuseStep 1475459 = 2213189) B2213189
theorem B983939 : Blo 980594 983939 := bstep (se 1 (by rfl) ⟨737954, by rfl⟩ : syracuseStep 983939 = 1475909) B1475909
theorem B2655121 : Blo 980594 2655121 := bstep (se 2 (by rfl) ⟨995670, by rfl⟩ : syracuseStep 2655121 = 1991341) B1991341
theorem B983955 : Blo 980594 983955 := bstep (se 1 (by rfl) ⟨737966, by rfl⟩ : syracuseStep 983955 = 1475933) B1475933
theorem B1246099 : Blo 980594 1246099 := bstep (se 1 (by rfl) ⟨934574, by rfl⟩ : syracuseStep 1246099 = 1869149) B1869149
theorem B1475489 : Blo 980594 1475489 := bstep (se 2 (by rfl) ⟨553308, by rfl⟩ : syracuseStep 1475489 = 1106617) B1106617
theorem B983971 : Blo 980594 983971 := bstep (se 1 (by rfl) ⟨737978, by rfl⟩ : syracuseStep 983971 = 1475957) B1475957
theorem B1475507 : Blo 980594 1475507 := bstep (se 1 (by rfl) ⟨1106630, by rfl⟩ : syracuseStep 1475507 = 2213261) B2213261
theorem B983987 : Blo 980594 983987 := bstep (se 1 (by rfl) ⟨737990, by rfl⟩ : syracuseStep 983987 = 1475981) B1475981
theorem B984003 : Blo 980594 984003 := bstep (se 1 (by rfl) ⟨738002, by rfl⟩ : syracuseStep 984003 = 1476005) B1476005
theorem B1475537 : Blo 980594 1475537 := bstep (se 2 (by rfl) ⟨553326, by rfl⟩ : syracuseStep 1475537 = 1106653) B1106653
theorem B1049555 : Blo 980594 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B984019 : Blo 980594 984019 := bstep (se 1 (by rfl) ⟨738014, by rfl⟩ : syracuseStep 984019 = 1476029) B1476029
theorem B1475555 : Blo 980594 1475555 := bstep (se 1 (by rfl) ⟨1106666, by rfl⟩ : syracuseStep 1475555 = 2213333) B2213333
theorem B984035 : Blo 980594 984035 := bstep (se 1 (by rfl) ⟨738026, by rfl⟩ : syracuseStep 984035 = 1476053) B1476053
theorem B3310577 : Blo 980594 3310577 := bstep (se 2 (by rfl) ⟨1241466, by rfl⟩ : syracuseStep 3310577 = 2482933) B2482933
theorem B984051 : Blo 980594 984051 := bstep (se 1 (by rfl) ⟨738038, by rfl⟩ : syracuseStep 984051 = 1476077) B1476077
theorem B1475585 : Blo 980594 1475585 := bstep (se 2 (by rfl) ⟨553344, by rfl⟩ : syracuseStep 1475585 = 1106689) B1106689
theorem B984067 : Blo 980594 984067 := bstep (se 1 (by rfl) ⟨738050, by rfl⟩ : syracuseStep 984067 = 1476101) B1476101
theorem B1475603 : Blo 980594 1475603 := bstep (se 1 (by rfl) ⟨1106702, by rfl⟩ : syracuseStep 1475603 = 2213405) B2213405
theorem B984083 : Blo 980594 984083 := bstep (se 1 (by rfl) ⟨738062, by rfl⟩ : syracuseStep 984083 = 1476125) B1476125
theorem B984099 : Blo 980594 984099 := bstep (se 1 (by rfl) ⟨738074, by rfl⟩ : syracuseStep 984099 = 1476149) B1476149
theorem B1475633 : Blo 980594 1475633 := bstep (se 2 (by rfl) ⟨553362, by rfl⟩ : syracuseStep 1475633 = 1106725) B1106725
theorem B984115 : Blo 980594 984115 := bstep (se 1 (by rfl) ⟨738086, by rfl⟩ : syracuseStep 984115 = 1476173) B1476173
theorem B1475651 : Blo 980594 1475651 := bstep (se 1 (by rfl) ⟨1106738, by rfl⟩ : syracuseStep 1475651 = 2213477) B2213477
theorem B984131 : Blo 980594 984131 := bstep (se 1 (by rfl) ⟨738098, by rfl⟩ : syracuseStep 984131 = 1476197) B1476197
theorem B984147 : Blo 980594 984147 := bstep (se 1 (by rfl) ⟨738110, by rfl⟩ : syracuseStep 984147 = 1476221) B1476221
theorem B1475681 : Blo 980594 1475681 := bstep (se 2 (by rfl) ⟨553380, by rfl⟩ : syracuseStep 1475681 = 1106761) B1106761
theorem B1573987 : Blo 980594 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B984163 : Blo 980594 984163 := bstep (se 1 (by rfl) ⟨738122, by rfl⟩ : syracuseStep 984163 = 1476245) B1476245
theorem B1475699 : Blo 980594 1475699 := bstep (se 1 (by rfl) ⟨1106774, by rfl⟩ : syracuseStep 1475699 = 2213549) B2213549
theorem B984179 : Blo 980594 984179 := bstep (se 1 (by rfl) ⟨738134, by rfl⟩ : syracuseStep 984179 = 1476269) B1476269
theorem B984195 : Blo 980594 984195 := bstep (se 1 (by rfl) ⟨738146, by rfl⟩ : syracuseStep 984195 = 1476293) B1476293
theorem B1475729 : Blo 980594 1475729 := bstep (se 2 (by rfl) ⟨553398, by rfl⟩ : syracuseStep 1475729 = 1106797) B1106797
theorem B984211 : Blo 980594 984211 := bstep (se 1 (by rfl) ⟨738158, by rfl⟩ : syracuseStep 984211 = 1476317) B1476317
theorem B1475747 : Blo 980594 1475747 := bstep (se 1 (by rfl) ⟨1106810, by rfl⟩ : syracuseStep 1475747 = 2213621) B2213621
theorem B984227 : Blo 980594 984227 := bstep (se 1 (by rfl) ⟨738170, by rfl⟩ : syracuseStep 984227 = 1476341) B1476341
theorem B984243 : Blo 980594 984243 := bstep (se 1 (by rfl) ⟨738182, by rfl⟩ : syracuseStep 984243 = 1476365) B1476365
theorem B1475777 : Blo 980594 1475777 := bstep (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) B1106833
theorem B984259 : Blo 980594 984259 := bstep (se 1 (by rfl) ⟨738194, by rfl⟩ : syracuseStep 984259 = 1476389) B1476389
theorem B1475795 : Blo 980594 1475795 := bstep (se 1 (by rfl) ⟨1106846, by rfl⟩ : syracuseStep 1475795 = 2213693) B2213693
theorem B984275 : Blo 980594 984275 := bstep (se 1 (by rfl) ⟨738206, by rfl⟩ : syracuseStep 984275 = 1476413) B1476413
theorem B984291 : Blo 980594 984291 := bstep (se 1 (by rfl) ⟨738218, by rfl⟩ : syracuseStep 984291 = 1476437) B1476437
theorem B1475825 : Blo 980594 1475825 := bstep (se 2 (by rfl) ⟨553434, by rfl⟩ : syracuseStep 1475825 = 1106869) B1106869
theorem B984307 : Blo 980594 984307 := bstep (se 1 (by rfl) ⟨738230, by rfl⟩ : syracuseStep 984307 = 1476461) B1476461
theorem B1475843 : Blo 980594 1475843 := bstep (se 1 (by rfl) ⟨1106882, by rfl⟩ : syracuseStep 1475843 = 2213765) B2213765
theorem B984323 : Blo 980594 984323 := bstep (se 1 (by rfl) ⟨738242, by rfl⟩ : syracuseStep 984323 = 1476485) B1476485
theorem B3147025 : Blo 980594 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B984339 : Blo 980594 984339 := bstep (se 1 (by rfl) ⟨738254, by rfl⟩ : syracuseStep 984339 = 1476509) B1476509
theorem B1475873 : Blo 980594 1475873 := bstep (se 2 (by rfl) ⟨553452, by rfl⟩ : syracuseStep 1475873 = 1106905) B1106905
theorem B984355 : Blo 980594 984355 := bstep (se 1 (by rfl) ⟨738266, by rfl⟩ : syracuseStep 984355 = 1476533) B1476533
theorem B1475891 : Blo 980594 1475891 := bstep (se 1 (by rfl) ⟨1106918, by rfl⟩ : syracuseStep 1475891 = 2213837) B2213837
theorem B984371 : Blo 980594 984371 := bstep (se 1 (by rfl) ⟨738278, by rfl⟩ : syracuseStep 984371 = 1476557) B1476557
theorem B984387 : Blo 980594 984387 := bstep (se 1 (by rfl) ⟨738290, by rfl⟩ : syracuseStep 984387 = 1476581) B1476581
theorem B1574225 : Blo 980594 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B1475921 : Blo 980594 1475921 := bstep (se 2 (by rfl) ⟨553470, by rfl⟩ : syracuseStep 1475921 = 1106941) B1106941
theorem B984403 : Blo 980594 984403 := bstep (se 1 (by rfl) ⟨738302, by rfl⟩ : syracuseStep 984403 = 1476605) B1476605
theorem B1475939 : Blo 980594 1475939 := bstep (se 1 (by rfl) ⟨1106954, by rfl⟩ : syracuseStep 1475939 = 2213909) B2213909
theorem B984419 : Blo 980594 984419 := bstep (se 1 (by rfl) ⟨738314, by rfl⟩ : syracuseStep 984419 = 1476629) B1476629
theorem B984435 : Blo 980594 984435 := bstep (se 1 (by rfl) ⟨738326, by rfl⟩ : syracuseStep 984435 = 1476653) B1476653
theorem B1475969 : Blo 980594 1475969 := bstep (se 2 (by rfl) ⟨553488, by rfl⟩ : syracuseStep 1475969 = 1106977) B1106977
theorem B984451 : Blo 980594 984451 := bstep (se 1 (by rfl) ⟨738338, by rfl⟩ : syracuseStep 984451 = 1476677) B1476677
theorem B7079309 : Blo 980594 7079309 := bstep (se 3 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 7079309 = 2654741) B2654741
theorem B2491793 : Blo 980594 2491793 := bstep (se 2 (by rfl) ⟨934422, by rfl⟩ : syracuseStep 2491793 = 1868845) B1868845
theorem B1475987 : Blo 980594 1475987 := bstep (se 1 (by rfl) ⟨1106990, by rfl⟩ : syracuseStep 1475987 = 2213981) B2213981
theorem B984467 : Blo 980594 984467 := bstep (se 1 (by rfl) ⟨738350, by rfl⟩ : syracuseStep 984467 = 1476701) B1476701
theorem B984483 : Blo 980594 984483 := bstep (se 1 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 984483 = 1476725) B1476725
theorem B1476017 : Blo 980594 1476017 := bstep (se 2 (by rfl) ⟨553506, by rfl⟩ : syracuseStep 1476017 = 1107013) B1107013
theorem B984499 : Blo 980594 984499 := bstep (se 1 (by rfl) ⟨738374, by rfl⟩ : syracuseStep 984499 = 1476749) B1476749
theorem B1476035 : Blo 980594 1476035 := bstep (se 1 (by rfl) ⟨1107026, by rfl⟩ : syracuseStep 1476035 = 2214053) B2214053
theorem B2491843 : Blo 980594 2491843 := bstep (se 1 (by rfl) ⟨1868882, by rfl⟩ : syracuseStep 2491843 = 3737765) B3737765
theorem B984515 : Blo 980594 984515 := bstep (se 1 (by rfl) ⟨738386, by rfl⟩ : syracuseStep 984515 = 1476773) B1476773
theorem B984531 : Blo 980594 984531 := bstep (se 1 (by rfl) ⟨738398, by rfl⟩ : syracuseStep 984531 = 1476797) B1476797
theorem B1476065 : Blo 980594 1476065 := bstep (se 2 (by rfl) ⟨553524, by rfl⟩ : syracuseStep 1476065 = 1107049) B1107049
theorem B984547 : Blo 980594 984547 := bstep (se 1 (by rfl) ⟨738410, by rfl⟩ : syracuseStep 984547 = 1476821) B1476821
theorem B1476083 : Blo 980594 1476083 := bstep (se 1 (by rfl) ⟨1107062, by rfl⟩ : syracuseStep 1476083 = 2214125) B2214125
theorem B984563 : Blo 980594 984563 := bstep (se 1 (by rfl) ⟨738422, by rfl⟩ : syracuseStep 984563 = 1476845) B1476845
theorem B984579 : Blo 980594 984579 := bstep (se 1 (by rfl) ⟨738434, by rfl⟩ : syracuseStep 984579 = 1476869) B1476869
theorem B3311117 : Blo 980594 3311117 := bstep (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) B1241669
theorem B1476113 : Blo 980594 1476113 := bstep (se 2 (by rfl) ⟨553542, by rfl⟩ : syracuseStep 1476113 = 1107085) B1107085
theorem B1574435 : Blo 980594 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B1476131 : Blo 980594 1476131 := bstep (se 1 (by rfl) ⟨1107098, by rfl⟩ : syracuseStep 1476131 = 2214197) B2214197
theorem B1476161 : Blo 980594 1476161 := bstep (se 2 (by rfl) ⟨553560, by rfl⟩ : syracuseStep 1476161 = 1107121) B1107121
theorem B3311171 : Blo 980594 3311171 := bstep (se 1 (by rfl) ⟨2483378, by rfl⟩ : syracuseStep 3311171 = 4966757) B4966757
theorem B2491985 : Blo 980594 2491985 := bstep (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) B1868989
theorem B1476179 : Blo 980594 1476179 := bstep (se 1 (by rfl) ⟨1107134, by rfl⟩ : syracuseStep 1476179 = 2214269) B2214269
theorem B1476209 : Blo 980594 1476209 := bstep (se 2 (by rfl) ⟨553578, by rfl⟩ : syracuseStep 1476209 = 1107157) B1107157
theorem B1476227 : Blo 980594 1476227 := bstep (se 1 (by rfl) ⟨1107170, by rfl⟩ : syracuseStep 1476227 = 2214341) B2214341
theorem B1476257 : Blo 980594 1476257 := bstep (se 2 (by rfl) ⟨553596, by rfl⟩ : syracuseStep 1476257 = 1107193) B1107193
theorem B1476275 : Blo 980594 1476275 := bstep (se 1 (by rfl) ⟨1107206, by rfl⟩ : syracuseStep 1476275 = 2214413) B2214413
theorem B2655953 : Blo 980594 2655953 := bstep (se 2 (by rfl) ⟨995982, by rfl⟩ : syracuseStep 2655953 = 1991965) B1991965
theorem B1476305 : Blo 980594 1476305 := bstep (se 2 (by rfl) ⟨553614, by rfl⟩ : syracuseStep 1476305 = 1107229) B1107229
theorem B1476323 : Blo 980594 1476323 := bstep (se 1 (by rfl) ⟨1107242, by rfl⟩ : syracuseStep 1476323 = 2214485) B2214485
theorem B1476353 : Blo 980594 1476353 := bstep (se 2 (by rfl) ⟨553632, by rfl⟩ : syracuseStep 1476353 = 1107265) B1107265
theorem B1476371 : Blo 980594 1476371 := bstep (se 1 (by rfl) ⟨1107278, by rfl⟩ : syracuseStep 1476371 = 2214557) B2214557
theorem B1476401 : Blo 980594 1476401 := bstep (se 2 (by rfl) ⟨553650, by rfl⟩ : syracuseStep 1476401 = 1107301) B1107301
theorem B1476419 : Blo 980594 1476419 := bstep (se 1 (by rfl) ⟨1107314, by rfl⟩ : syracuseStep 1476419 = 2214629) B2214629
theorem B3311441 : Blo 980594 3311441 := bstep (se 2 (by rfl) ⟨1241790, by rfl⟩ : syracuseStep 3311441 = 2483581) B2483581
theorem B1476449 : Blo 980594 1476449 := bstep (se 2 (by rfl) ⟨553668, by rfl⟩ : syracuseStep 1476449 = 1107337) B1107337
theorem B1476467 : Blo 980594 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B1476497 : Blo 980594 1476497 := bstep (se 2 (by rfl) ⟨553686, by rfl⟩ : syracuseStep 1476497 = 1107373) B1107373
theorem B1476515 : Blo 980594 1476515 := bstep (se 1 (by rfl) ⟨1107386, by rfl⟩ : syracuseStep 1476515 = 2214773) B2214773
theorem B1476545 : Blo 980594 1476545 := bstep (se 2 (by rfl) ⟨553704, by rfl⟩ : syracuseStep 1476545 = 1107409) B1107409
theorem B5310413 : Blo 980594 5310413 := bstep (se 3 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 5310413 = 1991405) B1991405
theorem B1476563 : Blo 980594 1476563 := bstep (se 1 (by rfl) ⟨1107422, by rfl⟩ : syracuseStep 1476563 = 2214845) B2214845
theorem B2099171 : Blo 980594 2099171 := bstep (se 1 (by rfl) ⟨1574378, by rfl⟩ : syracuseStep 2099171 = 3148757) B3148757
theorem B1476593 : Blo 980594 1476593 := bstep (se 2 (by rfl) ⟨553722, by rfl⟩ : syracuseStep 1476593 = 1107445) B1107445
theorem B1476611 : Blo 980594 1476611 := bstep (se 1 (by rfl) ⟨1107458, by rfl⟩ : syracuseStep 1476611 = 2214917) B2214917
theorem B1476641 : Blo 980594 1476641 := bstep (se 2 (by rfl) ⟨553740, by rfl⟩ : syracuseStep 1476641 = 1107481) B1107481
theorem B1476659 : Blo 980594 1476659 := bstep (se 1 (by rfl) ⟨1107494, by rfl⟩ : syracuseStep 1476659 = 2214989) B2214989
theorem B7473221 : Blo 980594 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1476689 : Blo 980594 1476689 := bstep (se 2 (by rfl) ⟨553758, by rfl⟩ : syracuseStep 1476689 = 1107517) B1107517
theorem B1476707 : Blo 980594 1476707 := bstep (se 1 (by rfl) ⟨1107530, by rfl⟩ : syracuseStep 1476707 = 2215061) B2215061
theorem B1476737 : Blo 980594 1476737 := bstep (se 2 (by rfl) ⟨553776, by rfl⟩ : syracuseStep 1476737 = 1107553) B1107553
theorem B1476755 : Blo 980594 1476755 := bstep (se 1 (by rfl) ⟨1107566, by rfl⟩ : syracuseStep 1476755 = 2215133) B2215133
theorem B1476785 : Blo 980594 1476785 := bstep (se 2 (by rfl) ⟨553794, by rfl⟩ : syracuseStep 1476785 = 1107589) B1107589
theorem B1476803 : Blo 980594 1476803 := bstep (se 1 (by rfl) ⟨1107602, by rfl⟩ : syracuseStep 1476803 = 2215205) B2215205
theorem B25233605 : Blo 980594 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B1476833 : Blo 980594 1476833 := bstep (se 2 (by rfl) ⟨553812, by rfl⟩ : syracuseStep 1476833 = 1107625) B1107625
theorem B1476851 : Blo 980594 1476851 := bstep (se 1 (by rfl) ⟨1107638, by rfl⟩ : syracuseStep 1476851 = 2215277) B2215277
theorem B5605645 : Blo 980594 5605645 := bstep (se 3 (by rfl) ⟨1051058, by rfl⟩ : syracuseStep 5605645 = 2102117) B2102117
theorem B1476881 : Blo 980594 1476881 := bstep (se 2 (by rfl) ⟨553830, by rfl⟩ : syracuseStep 1476881 = 1107661) B1107661
theorem B1575217 : Blo 980594 1575217 := bstep (se 2 (by rfl) ⟨590706, by rfl⟩ : syracuseStep 1575217 = 1181413) B1181413
theorem B6064433 : Blo 980594 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B1050931 : Blo 980594 1050931 := bstep (se 1 (by rfl) ⟨788198, by rfl⟩ : syracuseStep 1050931 = 1576397) B1576397
theorem B3737933 : Blo 980594 3737933 := bstep (se 3 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 3737933 = 1401725) B1401725
theorem B3311981 : Blo 980594 3311981 := bstep (se 3 (by rfl) ⟨620996, by rfl⟩ : syracuseStep 3311981 = 1241993) B1241993
theorem B3148141 : Blo 980594 3148141 := bstep (se 3 (by rfl) ⟨590276, by rfl⟩ : syracuseStep 3148141 = 1180553) B1180553
theorem B3312035 : Blo 980594 3312035 := bstep (se 1 (by rfl) ⟨2484026, by rfl⟩ : syracuseStep 3312035 = 4968053) B4968053
theorem B4196785 : Blo 980594 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B4983281 : Blo 980594 4983281 := bstep (se 2 (by rfl) ⟨1868730, by rfl⟩ : syracuseStep 4983281 = 3737461) B3737461
theorem B2361923 : Blo 980594 2361923 := bstep (se 1 (by rfl) ⟨1771442, by rfl⟩ : syracuseStep 2361923 = 3542885) B3542885
theorem B3312305 : Blo 980594 3312305 := bstep (se 2 (by rfl) ⟨1242114, by rfl⟩ : syracuseStep 3312305 = 2484229) B2484229
theorem B2362115 : Blo 980594 2362115 := bstep (se 1 (by rfl) ⟨1771586, by rfl⟩ : syracuseStep 2362115 = 3543173) B3543173
theorem B6294307 : Blo 980594 6294307 := bstep (se 1 (by rfl) ⟨4720730, by rfl⟩ : syracuseStep 6294307 = 9441461) B9441461
theorem B4262705 : Blo 980594 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B2362211 : Blo 980594 2362211 := bstep (se 1 (by rfl) ⟨1771658, by rfl⟩ : syracuseStep 2362211 = 3543317) B3543317
theorem B1182595 : Blo 980594 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B1182643 : Blo 980594 1182643 := bstep (se 1 (by rfl) ⟨886982, by rfl⟩ : syracuseStep 1182643 = 1773965) B1773965
theorem B2985005 : Blo 980594 2985005 := bstep (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) B1119377
theorem B4918321 : Blo 980594 4918321 := bstep (se 2 (by rfl) ⟨1844370, by rfl⟩ : syracuseStep 4918321 = 3688741) B3688741
theorem B1576019 : Blo 980594 1576019 := bstep (se 1 (by rfl) ⟨1182014, by rfl⟩ : syracuseStep 1576019 = 2364029) B2364029
theorem B3148973 : Blo 980594 3148973 := bstep (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) B1180865
theorem B2100401 : Blo 980594 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B3312845 : Blo 980594 3312845 := bstep (se 3 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 3312845 = 1242317) B1242317
theorem B45321443 : Blo 980594 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B3312899 : Blo 980594 3312899 := bstep (se 1 (by rfl) ⟨2484674, by rfl⟩ : syracuseStep 3312899 = 4969349) B4969349
theorem B1772849 : Blo 980594 1772849 := bstep (se 2 (by rfl) ⟨664818, by rfl⟩ : syracuseStep 1772849 = 1329637) B1329637
theorem B8981873 : Blo 980594 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B3313169 : Blo 980594 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B1576531 : Blo 980594 1576531 := bstep (se 1 (by rfl) ⟨1182398, by rfl⟩ : syracuseStep 1576531 = 2364797) B2364797
theorem B13471373 : Blo 980594 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B2690833 : Blo 980594 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B3313709 : Blo 980594 3313709 := bstep (se 3 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 3313709 = 1242641) B1242641
theorem B2101297 : Blo 980594 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B2101315 : Blo 980594 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B3313763 : Blo 980594 3313763 := bstep (se 1 (by rfl) ⟨2485322, by rfl⟩ : syracuseStep 3313763 = 4970645) B4970645
theorem B1577075 : Blo 980594 1577075 := bstep (se 1 (by rfl) ⟨1182806, by rfl⟩ : syracuseStep 1577075 = 2365613) B2365613
theorem B3543203 : Blo 980594 3543203 := bstep (se 1 (by rfl) ⟨2657402, by rfl⟩ : syracuseStep 3543203 = 5314805) B5314805
theorem B5968205 : Blo 980594 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B3314033 : Blo 980594 3314033 := bstep (se 2 (by rfl) ⟨1242762, by rfl⟩ : syracuseStep 3314033 = 2485525) B2485525
theorem B15340085 : Blo 980594 15340085 := bstep (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) B1438133
theorem B1348177 : Blo 980594 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B2364113 : Blo 980594 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B6296305 : Blo 980594 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B3314573 : Blo 980594 3314573 := bstep (se 3 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 3314573 = 1242965) B1242965
theorem B3314627 : Blo 980594 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B2987021 : Blo 980594 2987021 := bstep (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) B1120133
theorem B3314897 : Blo 980594 3314897 := bstep (se 2 (by rfl) ⟨1243086, by rfl⟩ : syracuseStep 3314897 = 2486173) B2486173
theorem B3151075 : Blo 980594 3151075 := bstep (se 1 (by rfl) ⟨2363306, by rfl⟩ : syracuseStep 3151075 = 4726613) B4726613
theorem B2364643 : Blo 980594 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B3151217 : Blo 980594 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B4724365 : Blo 980594 4724365 := bstep (se 3 (by rfl) ⟨885818, by rfl⟩ : syracuseStep 4724365 = 1771637) B1771637
theorem B3315437 : Blo 980594 3315437 := bstep (se 3 (by rfl) ⟨621644, by rfl⟩ : syracuseStep 3315437 = 1243289) B1243289
theorem B3315491 : Blo 980594 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B1120115 : Blo 980594 1120115 := bstep (se 1 (by rfl) ⟨840086, by rfl⟩ : syracuseStep 1120115 = 1680173) B1680173
theorem B5314565 : Blo 980594 5314565 := bstep (se 4 (by rfl) ⟨498240, by rfl⟩ : syracuseStep 5314565 = 996481) B996481
theorem B3315761 : Blo 980594 3315761 := bstep (se 2 (by rfl) ⟨1243410, by rfl⟩ : syracuseStep 3315761 = 2486821) B2486821
theorem B5314673 : Blo 980594 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B34019605 : Blo 980594 34019605 := bstep (se 6 (by rfl) ⟨797334, by rfl⟩ : syracuseStep 34019605 = 1594669) B1594669
theorem B4200817 : Blo 980594 4200817 := bstep (se 2 (by rfl) ⟨1575306, by rfl⟩ : syracuseStep 4200817 = 3150613) B3150613
theorem B2988433 : Blo 980594 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B4790755 : Blo 980594 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B5380613 : Blo 980594 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B3316301 : Blo 980594 3316301 := bstep (se 3 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 3316301 = 1243613) B1243613
theorem B3316355 : Blo 980594 3316355 := bstep (se 1 (by rfl) ⟨2487266, by rfl⟩ : syracuseStep 3316355 = 4974533) B4974533
theorem B3185315 : Blo 980594 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B3316625 : Blo 980594 3316625 := bstep (se 2 (by rfl) ⟨1243734, by rfl⟩ : syracuseStep 3316625 = 2487469) B2487469
theorem B2792515 : Blo 980594 2792515 := bstep (se 1 (by rfl) ⟨2094386, by rfl⟩ : syracuseStep 2792515 = 4188773) B4188773
theorem B3317165 : Blo 980594 3317165 := bstep (se 3 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 3317165 = 1243937) B1243937
theorem B3317219 : Blo 980594 3317219 := bstep (se 1 (by rfl) ⟨2487914, by rfl⟩ : syracuseStep 3317219 = 4975829) B4975829
theorem B2793005 : Blo 980594 2793005 := bstep (se 3 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 2793005 = 1047377) B1047377
theorem B3153613 : Blo 980594 3153613 := bstep (se 3 (by rfl) ⟨591302, by rfl⟩ : syracuseStep 3153613 = 1182605) B1182605
theorem B3317489 : Blo 980594 3317489 := bstep (se 2 (by rfl) ⟨1244058, by rfl⟩ : syracuseStep 3317489 = 2488117) B2488117
theorem B1023763 : Blo 980594 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B1679297 : Blo 980594 1679297 := bstep (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) B1259473
theorem B2990125 : Blo 980594 2990125 := bstep (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) B1121297
theorem B3318029 : Blo 980594 3318029 := bstep (se 3 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 3318029 = 1244261) B1244261
theorem B3318083 : Blo 980594 3318083 := bstep (se 1 (by rfl) ⟨2488562, by rfl⟩ : syracuseStep 3318083 = 4977125) B4977125
theorem B3547469 : Blo 980594 3547469 := bstep (se 3 (by rfl) ⟨665150, by rfl⟩ : syracuseStep 3547469 = 1330301) B1330301
theorem B1122707 : Blo 980594 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B77537845 : Blo 980594 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B3318353 : Blo 980594 3318353 := bstep (se 2 (by rfl) ⟨1244382, by rfl⟩ : syracuseStep 3318353 = 2488765) B2488765
theorem B2794189 : Blo 980594 2794189 := bstep (se 3 (by rfl) ⟨523910, by rfl⟩ : syracuseStep 2794189 = 1047821) B1047821
theorem B3318893 : Blo 980594 3318893 := bstep (se 3 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 3318893 = 1244585) B1244585
theorem B3318947 : Blo 980594 3318947 := bstep (se 1 (by rfl) ⟨2489210, by rfl⟩ : syracuseStep 3318947 = 4978421) B4978421
theorem B5449037 : Blo 980594 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B7447949 : Blo 980594 7447949 := bstep (se 3 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 7447949 = 2792981) B2792981
theorem B3319217 : Blo 980594 3319217 := bstep (se 2 (by rfl) ⟨1244706, by rfl⟩ : syracuseStep 3319217 = 2489413) B2489413
theorem B2991779 : Blo 980594 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B1681075 : Blo 980594 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B2795249 : Blo 980594 2795249 := bstep (se 2 (by rfl) ⟨1048218, by rfl⟩ : syracuseStep 2795249 = 2096437) B2096437
theorem B5318435 : Blo 980594 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B5318477 : Blo 980594 5318477 := bstep (se 3 (by rfl) ⟨997214, by rfl⟩ : syracuseStep 5318477 = 1994429) B1994429
theorem B4728689 : Blo 980594 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B6301637 : Blo 980594 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B3319757 : Blo 980594 3319757 := bstep (se 3 (by rfl) ⟨622454, by rfl⟩ : syracuseStep 3319757 = 1244909) B1244909
theorem B4204493 : Blo 980594 4204493 := bstep (se 3 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 4204493 = 1576685) B1576685
theorem B1419251 : Blo 980594 1419251 := bstep (se 1 (by rfl) ⟨1064438, by rfl⟩ : syracuseStep 1419251 = 2128877) B2128877
theorem B3319811 : Blo 980594 3319811 := bstep (se 1 (by rfl) ⟨2489858, by rfl⟩ : syracuseStep 3319811 = 4979717) B4979717
theorem B5679173 : Blo 980594 5679173 := bstep (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) B1064845
theorem B3320081 : Blo 980594 3320081 := bstep (se 2 (by rfl) ⟨1245030, by rfl⟩ : syracuseStep 3320081 = 2490061) B2490061
theorem B8399173 : Blo 980594 8399173 := bstep (se 4 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 8399173 = 1574845) B1574845
theorem B2795921 : Blo 980594 2795921 := bstep (se 2 (by rfl) ⟨1048470, by rfl⟩ : syracuseStep 2795921 = 2096941) B2096941
theorem B2206385 : Blo 980594 2206385 := bstep (se 2 (by rfl) ⟨827394, by rfl⟩ : syracuseStep 2206385 = 1654789) B1654789
theorem B2206403 : Blo 980594 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B5745421 : Blo 980594 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B3320621 : Blo 980594 3320621 := bstep (se 3 (by rfl) ⟨622616, by rfl⟩ : syracuseStep 3320621 = 1245233) B1245233
theorem B3320675 : Blo 980594 3320675 := bstep (se 1 (by rfl) ⟨2490506, by rfl⟩ : syracuseStep 3320675 = 4981013) B4981013
theorem B2206673 : Blo 980594 2206673 := bstep (se 2 (by rfl) ⟨827502, by rfl⟩ : syracuseStep 2206673 = 1655005) B1655005
theorem B2206691 : Blo 980594 2206691 := bstep (se 1 (by rfl) ⟨1655018, by rfl⟩ : syracuseStep 2206691 = 3310037) B3310037
theorem B3320945 : Blo 980594 3320945 := bstep (se 2 (by rfl) ⟨1245354, by rfl⟩ : syracuseStep 3320945 = 2490709) B2490709
theorem B2796707 : Blo 980594 2796707 := bstep (se 1 (by rfl) ⟨2097530, by rfl⟩ : syracuseStep 2796707 = 4195061) B4195061
theorem B1617059 : Blo 980594 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B1682657 : Blo 980594 1682657 := bstep (se 2 (by rfl) ⟨630996, by rfl⟩ : syracuseStep 1682657 = 1261993) B1261993
theorem B2206961 : Blo 980594 2206961 := bstep (se 2 (by rfl) ⟨827610, by rfl⟩ : syracuseStep 2206961 = 1655221) B1655221
theorem B2206979 : Blo 980594 2206979 := bstep (se 1 (by rfl) ⟨1655234, by rfl⟩ : syracuseStep 2206979 = 3310469) B3310469
theorem B1420625 : Blo 980594 1420625 := bstep (se 2 (by rfl) ⟨532734, by rfl⟩ : syracuseStep 1420625 = 1065469) B1065469
theorem B2797037 : Blo 980594 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B2207249 : Blo 980594 2207249 := bstep (se 2 (by rfl) ⟨827718, by rfl⟩ : syracuseStep 2207249 = 1655437) B1655437
theorem B2207267 : Blo 980594 2207267 := bstep (se 1 (by rfl) ⟨1655450, by rfl⟩ : syracuseStep 2207267 = 3310901) B3310901
theorem B2797105 : Blo 980594 2797105 := bstep (se 2 (by rfl) ⟨1048914, by rfl⟩ : syracuseStep 2797105 = 2097829) B2097829
theorem B15904309 : Blo 980594 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B3321485 : Blo 980594 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B3321539 : Blo 980594 3321539 := bstep (se 1 (by rfl) ⟨2491154, by rfl⟩ : syracuseStep 3321539 = 4982309) B4982309
theorem B2207537 : Blo 980594 2207537 := bstep (se 2 (by rfl) ⟨827826, by rfl⟩ : syracuseStep 2207537 = 1655653) B1655653
theorem B2207555 : Blo 980594 2207555 := bstep (se 1 (by rfl) ⟨1655666, by rfl⟩ : syracuseStep 2207555 = 3311333) B3311333
theorem B2797379 : Blo 980594 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B15150989 : Blo 980594 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B3190691 : Blo 980594 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B1912771 : Blo 980594 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B3321809 : Blo 980594 3321809 := bstep (se 2 (by rfl) ⟨1245678, by rfl⟩ : syracuseStep 3321809 = 2491357) B2491357
theorem B2207825 : Blo 980594 2207825 := bstep (se 2 (by rfl) ⟨827934, by rfl⟩ : syracuseStep 2207825 = 1655869) B1655869
theorem B2207843 : Blo 980594 2207843 := bstep (se 1 (by rfl) ⟨1655882, by rfl⟩ : syracuseStep 2207843 = 3311765) B3311765
theorem B7450865 : Blo 980594 7450865 := bstep (se 2 (by rfl) ⟨2794074, by rfl⟩ : syracuseStep 7450865 = 5588149) B5588149
theorem B4731149 : Blo 980594 4731149 := bstep (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) B1774181
theorem B2208113 : Blo 980594 2208113 := bstep (se 2 (by rfl) ⟨828042, by rfl⟩ : syracuseStep 2208113 = 1656085) B1656085
theorem B2208131 : Blo 980594 2208131 := bstep (se 1 (by rfl) ⟨1656098, by rfl⟩ : syracuseStep 2208131 = 3312197) B3312197
theorem B3322349 : Blo 980594 3322349 := bstep (se 3 (by rfl) ⟨622940, by rfl⟩ : syracuseStep 3322349 = 1245881) B1245881
theorem B3322403 : Blo 980594 3322403 := bstep (se 1 (by rfl) ⟨2491802, by rfl⟩ : syracuseStep 3322403 = 4983605) B4983605
theorem B2798221 : Blo 980594 2798221 := bstep (se 3 (by rfl) ⟨524666, by rfl⟩ : syracuseStep 2798221 = 1049333) B1049333
theorem B2208401 : Blo 980594 2208401 := bstep (se 2 (by rfl) ⟨828150, by rfl⟩ : syracuseStep 2208401 = 1656301) B1656301
theorem B2208419 : Blo 980594 2208419 := bstep (se 1 (by rfl) ⟨1656314, by rfl⟩ : syracuseStep 2208419 = 3312629) B3312629
theorem B2798381 : Blo 980594 2798381 := bstep (se 3 (by rfl) ⟨524696, by rfl⟩ : syracuseStep 2798381 = 1049393) B1049393
theorem B3322673 : Blo 980594 3322673 := bstep (se 2 (by rfl) ⟨1246002, by rfl⟩ : syracuseStep 3322673 = 2492005) B2492005
theorem B1913699 : Blo 980594 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B2208689 : Blo 980594 2208689 := bstep (se 2 (by rfl) ⟨828258, by rfl⟩ : syracuseStep 2208689 = 1656517) B1656517
theorem B2208707 : Blo 980594 2208707 := bstep (se 1 (by rfl) ⟨1656530, by rfl⟩ : syracuseStep 2208707 = 3313061) B3313061
theorem B2798563 : Blo 980594 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B7189573 : Blo 980594 7189573 := bstep (se 4 (by rfl) ⟨674022, by rfl⟩ : syracuseStep 7189573 = 1348045) B1348045
theorem B2208977 : Blo 980594 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B2208995 : Blo 980594 2208995 := bstep (se 1 (by rfl) ⟨1656746, by rfl⟩ : syracuseStep 2208995 = 3313493) B3313493
theorem B3978659 : Blo 980594 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B5682659 : Blo 980594 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B2209265 : Blo 980594 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B2209283 : Blo 980594 2209283 := bstep (se 1 (by rfl) ⟨1656962, by rfl⟩ : syracuseStep 2209283 = 3313925) B3313925
theorem B2209553 : Blo 980594 2209553 := bstep (se 2 (by rfl) ⟨828582, by rfl⟩ : syracuseStep 2209553 = 1657165) B1657165
theorem B2209571 : Blo 980594 2209571 := bstep (se 1 (by rfl) ⟨1657178, by rfl⟩ : syracuseStep 2209571 = 3314357) B3314357
theorem B2209841 : Blo 980594 2209841 := bstep (se 2 (by rfl) ⟨828690, by rfl⟩ : syracuseStep 2209841 = 1657381) B1657381
theorem B2209859 : Blo 980594 2209859 := bstep (se 1 (by rfl) ⟨1657394, by rfl⟩ : syracuseStep 2209859 = 3314789) B3314789
theorem B1194259 : Blo 980594 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B2210129 : Blo 980594 2210129 := bstep (se 2 (by rfl) ⟨828798, by rfl⟩ : syracuseStep 2210129 = 1657597) B1657597
theorem B2799953 : Blo 980594 2799953 := bstep (se 2 (by rfl) ⟨1049982, by rfl⟩ : syracuseStep 2799953 = 2099965) B2099965
theorem B2210147 : Blo 980594 2210147 := bstep (se 1 (by rfl) ⟨1657610, by rfl⟩ : syracuseStep 2210147 = 3315221) B3315221
theorem B1325425 : Blo 980594 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B5585507 : Blo 980594 5585507 := bstep (se 1 (by rfl) ⟨4189130, by rfl⟩ : syracuseStep 5585507 = 8378261) B8378261
theorem B2210417 : Blo 980594 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B2210435 : Blo 980594 2210435 := bstep (se 1 (by rfl) ⟨1657826, by rfl⟩ : syracuseStep 2210435 = 3315653) B3315653
theorem B2210705 : Blo 980594 2210705 := bstep (se 2 (by rfl) ⟨829014, by rfl⟩ : syracuseStep 2210705 = 1658029) B1658029
theorem B2210723 : Blo 980594 2210723 := bstep (se 1 (by rfl) ⟨1658042, by rfl⟩ : syracuseStep 2210723 = 3316085) B3316085
theorem B7093261 : Blo 980594 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B2210993 : Blo 980594 2210993 := bstep (se 2 (by rfl) ⟨829122, by rfl⟩ : syracuseStep 2210993 = 1658245) B1658245
theorem B2211011 : Blo 980594 2211011 := bstep (se 1 (by rfl) ⟨1658258, by rfl⟩ : syracuseStep 2211011 = 3316517) B3316517
theorem B1260787 : Blo 980594 1260787 := bstep (se 1 (by rfl) ⟨945590, by rfl⟩ : syracuseStep 1260787 = 1891181) B1891181
theorem B2800909 : Blo 980594 2800909 := bstep (se 3 (by rfl) ⟨525170, by rfl⟩ : syracuseStep 2800909 = 1050341) B1050341
theorem B2211281 : Blo 980594 2211281 := bstep (se 2 (by rfl) ⟨829230, by rfl⟩ : syracuseStep 2211281 = 1658461) B1658461
theorem B2211299 : Blo 980594 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B2801137 : Blo 980594 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B5586509 : Blo 980594 5586509 := bstep (se 3 (by rfl) ⟨1047470, by rfl⟩ : syracuseStep 5586509 = 2094941) B2094941
theorem B3358307 : Blo 980594 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B2801297 : Blo 980594 2801297 := bstep (se 2 (by rfl) ⟨1050486, by rfl⟩ : syracuseStep 2801297 = 2100973) B2100973
theorem B2211569 : Blo 980594 2211569 := bstep (se 2 (by rfl) ⟨829338, by rfl⟩ : syracuseStep 2211569 = 1658677) B1658677
theorem B2211587 : Blo 980594 2211587 := bstep (se 1 (by rfl) ⟨1658690, by rfl⟩ : syracuseStep 2211587 = 3317381) B3317381
theorem B2801411 : Blo 980594 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B2244419 : Blo 980594 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B1654769 : Blo 980594 1654769 := bstep (se 2 (by rfl) ⟨620538, by rfl⟩ : syracuseStep 1654769 = 1241077) B1241077
theorem B2211857 : Blo 980594 2211857 := bstep (se 2 (by rfl) ⟨829446, by rfl⟩ : syracuseStep 2211857 = 1658893) B1658893
theorem B2211875 : Blo 980594 2211875 := bstep (se 1 (by rfl) ⟨1658906, by rfl⟩ : syracuseStep 2211875 = 3317813) B3317813
theorem B1654897 : Blo 980594 1654897 := bstep (se 2 (by rfl) ⟨620586, by rfl⟩ : syracuseStep 1654897 = 1241173) B1241173
theorem B1654931 : Blo 980594 1654931 := bstep (se 1 (by rfl) ⟨1241198, by rfl⟩ : syracuseStep 1654931 = 2482397) B2482397
theorem B1655059 : Blo 980594 1655059 := bstep (se 1 (by rfl) ⟨1241294, by rfl⟩ : syracuseStep 1655059 = 2482589) B2482589
theorem B2212145 : Blo 980594 2212145 := bstep (se 2 (by rfl) ⟨829554, by rfl⟩ : syracuseStep 2212145 = 1659109) B1659109
theorem B2212163 : Blo 980594 2212163 := bstep (se 1 (by rfl) ⟨1659122, by rfl⟩ : syracuseStep 2212163 = 3318245) B3318245
theorem B1491347 : Blo 980594 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B1655201 : Blo 980594 1655201 := bstep (se 2 (by rfl) ⟨620700, by rfl⟩ : syracuseStep 1655201 = 1241401) B1241401
theorem B31834565 : Blo 980594 31834565 := bstep (se 4 (by rfl) ⟨2984490, by rfl⟩ : syracuseStep 31834565 = 5968981) B5968981
theorem B4964813 : Blo 980594 4964813 := bstep (se 3 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 4964813 = 1861805) B1861805
theorem B1655329 : Blo 980594 1655329 := bstep (se 2 (by rfl) ⟨620748, by rfl⟩ : syracuseStep 1655329 = 1241497) B1241497
theorem B1655363 : Blo 980594 1655363 := bstep (se 1 (by rfl) ⟨1241522, by rfl⟩ : syracuseStep 1655363 = 2483045) B2483045
theorem B2212433 : Blo 980594 2212433 := bstep (se 2 (by rfl) ⟨829662, by rfl⟩ : syracuseStep 2212433 = 1659325) B1659325
theorem B2212451 : Blo 980594 2212451 := bstep (se 1 (by rfl) ⟨1659338, by rfl⟩ : syracuseStep 2212451 = 3318677) B3318677
theorem B1655491 : Blo 980594 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B2802413 : Blo 980594 2802413 := bstep (se 3 (by rfl) ⟨525452, by rfl⟩ : syracuseStep 2802413 = 1050905) B1050905
theorem B1655633 : Blo 980594 1655633 := bstep (se 2 (by rfl) ⟨620862, by rfl⟩ : syracuseStep 1655633 = 1241725) B1241725
theorem B2212721 : Blo 980594 2212721 := bstep (se 2 (by rfl) ⟨829770, by rfl⟩ : syracuseStep 2212721 = 1659541) B1659541
theorem B2212739 : Blo 980594 2212739 := bstep (se 1 (by rfl) ⟨1659554, by rfl⟩ : syracuseStep 2212739 = 3319109) B3319109
theorem B2802595 : Blo 980594 2802595 := bstep (se 1 (by rfl) ⟨2101946, by rfl⟩ : syracuseStep 2802595 = 4203893) B4203893
theorem B1655761 : Blo 980594 1655761 := bstep (se 2 (by rfl) ⟨620910, by rfl⟩ : syracuseStep 1655761 = 1241821) B1241821
theorem B1655795 : Blo 980594 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B2802755 : Blo 980594 2802755 := bstep (se 1 (by rfl) ⟨2102066, by rfl⟩ : syracuseStep 2802755 = 4204133) B4204133
theorem B1655923 : Blo 980594 1655923 := bstep (se 1 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 1655923 = 2483885) B2483885
theorem B2213009 : Blo 980594 2213009 := bstep (se 2 (by rfl) ⟨829878, by rfl⟩ : syracuseStep 2213009 = 1659757) B1659757
theorem B2213027 : Blo 980594 2213027 := bstep (se 1 (by rfl) ⟨1659770, by rfl⟩ : syracuseStep 2213027 = 3319541) B3319541
theorem B1197299 : Blo 980594 1197299 := bstep (se 1 (by rfl) ⟨897974, by rfl⟩ : syracuseStep 1197299 = 1795949) B1795949
theorem B1656065 : Blo 980594 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B1656193 : Blo 980594 1656193 := bstep (se 2 (by rfl) ⟨621072, by rfl⟩ : syracuseStep 1656193 = 1242145) B1242145
theorem B1656227 : Blo 980594 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B2213297 : Blo 980594 2213297 := bstep (se 2 (by rfl) ⟨829986, by rfl⟩ : syracuseStep 2213297 = 1659973) B1659973
theorem B2213315 : Blo 980594 2213315 := bstep (se 1 (by rfl) ⟨1659986, by rfl⟩ : syracuseStep 2213315 = 3319973) B3319973
theorem B1656355 : Blo 980594 1656355 := bstep (se 1 (by rfl) ⟨1242266, by rfl⟩ : syracuseStep 1656355 = 2484533) B2484533
theorem B1656497 : Blo 980594 1656497 := bstep (se 2 (by rfl) ⟨621186, by rfl⟩ : syracuseStep 1656497 = 1242373) B1242373
theorem B1328819 : Blo 980594 1328819 := bstep (se 1 (by rfl) ⟨996614, by rfl⟩ : syracuseStep 1328819 = 1993229) B1993229
theorem B2213585 : Blo 980594 2213585 := bstep (se 2 (by rfl) ⟨830094, by rfl⟩ : syracuseStep 2213585 = 1660189) B1660189
theorem B2213603 : Blo 980594 2213603 := bstep (se 1 (by rfl) ⟨1660202, by rfl⟩ : syracuseStep 2213603 = 3320405) B3320405
theorem B1656625 : Blo 980594 1656625 := bstep (se 2 (by rfl) ⟨621234, by rfl⟩ : syracuseStep 1656625 = 1242469) B1242469
theorem B1656659 : Blo 980594 1656659 := bstep (se 1 (by rfl) ⟨1242494, by rfl⟩ : syracuseStep 1656659 = 2484989) B2484989
theorem B7096261 : Blo 980594 7096261 := bstep (se 4 (by rfl) ⟨665274, by rfl⟩ : syracuseStep 7096261 = 1330549) B1330549
theorem B1656787 : Blo 980594 1656787 := bstep (se 1 (by rfl) ⟨1242590, by rfl⟩ : syracuseStep 1656787 = 2485181) B2485181
theorem B2213873 : Blo 980594 2213873 := bstep (se 2 (by rfl) ⟨830202, by rfl⟩ : syracuseStep 2213873 = 1660405) B1660405
theorem B2213891 : Blo 980594 2213891 := bstep (se 1 (by rfl) ⟨1660418, by rfl⟩ : syracuseStep 2213891 = 3320837) B3320837
theorem B1656929 : Blo 980594 1656929 := bstep (se 2 (by rfl) ⟨621348, by rfl⟩ : syracuseStep 1656929 = 1242697) B1242697
theorem B21284977 : Blo 980594 21284977 := bstep (se 2 (by rfl) ⟨7981866, by rfl⟩ : syracuseStep 21284977 = 15963733) B15963733
theorem B1493171 : Blo 980594 1493171 := bstep (se 1 (by rfl) ⟨1119878, by rfl⟩ : syracuseStep 1493171 = 2239757) B2239757
theorem B1657057 : Blo 980594 1657057 := bstep (se 2 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 1657057 = 1242793) B1242793
theorem B3786979 : Blo 980594 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B1657091 : Blo 980594 1657091 := bstep (se 1 (by rfl) ⟨1242818, by rfl⟩ : syracuseStep 1657091 = 2485637) B2485637
theorem B2214161 : Blo 980594 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B2214179 : Blo 980594 2214179 := bstep (se 1 (by rfl) ⟨1660634, by rfl⟩ : syracuseStep 2214179 = 3321269) B3321269
theorem B12568931 : Blo 980594 12568931 := bstep (se 1 (by rfl) ⟨9426698, by rfl⟩ : syracuseStep 12568931 = 18853397) B18853397
theorem B1657219 : Blo 980594 1657219 := bstep (se 1 (by rfl) ⟨1242914, by rfl⟩ : syracuseStep 1657219 = 2485829) B2485829
theorem B3361169 : Blo 980594 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B5589425 : Blo 980594 5589425 := bstep (se 2 (by rfl) ⟨2096034, by rfl⟩ : syracuseStep 5589425 = 4192069) B4192069
theorem B1657361 : Blo 980594 1657361 := bstep (se 2 (by rfl) ⟨621510, by rfl⟩ : syracuseStep 1657361 = 1243021) B1243021
theorem B2214449 : Blo 980594 2214449 := bstep (se 2 (by rfl) ⟨830418, by rfl⟩ : syracuseStep 2214449 = 1660837) B1660837
theorem B2214467 : Blo 980594 2214467 := bstep (se 1 (by rfl) ⟨1660850, by rfl⟩ : syracuseStep 2214467 = 3321701) B3321701
theorem B1657489 : Blo 980594 1657489 := bstep (se 2 (by rfl) ⟨621558, by rfl⟩ : syracuseStep 1657489 = 1243117) B1243117
theorem B1657523 : Blo 980594 1657523 := bstep (se 1 (by rfl) ⟨1243142, by rfl⟩ : syracuseStep 1657523 = 2486285) B2486285
theorem B1657651 : Blo 980594 1657651 := bstep (se 1 (by rfl) ⟨1243238, by rfl⟩ : syracuseStep 1657651 = 2486477) B2486477
theorem B2214737 : Blo 980594 2214737 := bstep (se 2 (by rfl) ⟨830526, by rfl⟩ : syracuseStep 2214737 = 1661053) B1661053
theorem B2214755 : Blo 980594 2214755 := bstep (se 1 (by rfl) ⟨1661066, by rfl⟩ : syracuseStep 2214755 = 3322133) B3322133
theorem B8407921 : Blo 980594 8407921 := bstep (se 2 (by rfl) ⟨3152970, by rfl⟩ : syracuseStep 8407921 = 6305941) B6305941
theorem B4475789 : Blo 980594 4475789 := bstep (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) B1678421
theorem B1657793 : Blo 980594 1657793 := bstep (se 2 (by rfl) ⟨621672, by rfl⟩ : syracuseStep 1657793 = 1243345) B1243345
theorem B5753861 : Blo 980594 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B1657921 : Blo 980594 1657921 := bstep (se 2 (by rfl) ⟨621720, by rfl⟩ : syracuseStep 1657921 = 1243441) B1243441
theorem B1657955 : Blo 980594 1657955 := bstep (se 1 (by rfl) ⟨1243466, by rfl⟩ : syracuseStep 1657955 = 2486933) B2486933
theorem B2215025 : Blo 980594 2215025 := bstep (se 2 (by rfl) ⟨830634, by rfl⟩ : syracuseStep 2215025 = 1661269) B1661269
theorem B2215043 : Blo 980594 2215043 := bstep (se 1 (by rfl) ⟨1661282, by rfl⟩ : syracuseStep 2215043 = 3322565) B3322565
theorem B1658083 : Blo 980594 1658083 := bstep (se 1 (by rfl) ⟨1243562, by rfl⟩ : syracuseStep 1658083 = 2487125) B2487125
theorem B4967729 : Blo 980594 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B1658225 : Blo 980594 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B2215313 : Blo 980594 2215313 := bstep (se 2 (by rfl) ⟨830742, by rfl⟩ : syracuseStep 2215313 = 1661485) B1661485
theorem B2215331 : Blo 980594 2215331 := bstep (se 1 (by rfl) ⟨1661498, by rfl⟩ : syracuseStep 2215331 = 3322997) B3322997
theorem B1658353 : Blo 980594 1658353 := bstep (se 2 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 1658353 = 1243765) B1243765
theorem B1658387 : Blo 980594 1658387 := bstep (se 1 (by rfl) ⟨1243790, by rfl⟩ : syracuseStep 1658387 = 2487581) B2487581
theorem B1658515 : Blo 980594 1658515 := bstep (se 1 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 1658515 = 2487773) B2487773
theorem B1658657 : Blo 980594 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B4542257 : Blo 980594 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B1396531 : Blo 980594 1396531 := bstep (se 1 (by rfl) ⟨1047398, by rfl⟩ : syracuseStep 1396531 = 2094797) B2094797
theorem B5590883 : Blo 980594 5590883 := bstep (se 1 (by rfl) ⟨4193162, by rfl⟩ : syracuseStep 5590883 = 8386325) B8386325
theorem B1658785 : Blo 980594 1658785 := bstep (se 2 (by rfl) ⟨622044, by rfl⟩ : syracuseStep 1658785 = 1244089) B1244089
theorem B1658819 : Blo 980594 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B1658947 : Blo 980594 1658947 := bstep (se 1 (by rfl) ⟨1244210, by rfl⟩ : syracuseStep 1658947 = 2488421) B2488421
theorem B1396867 : Blo 980594 1396867 := bstep (se 1 (by rfl) ⟨1047650, by rfl⟩ : syracuseStep 1396867 = 2095301) B2095301
theorem B1659089 : Blo 980594 1659089 := bstep (se 2 (by rfl) ⟨622158, by rfl⟩ : syracuseStep 1659089 = 1244317) B1244317
theorem B1659217 : Blo 980594 1659217 := bstep (se 2 (by rfl) ⟨622206, by rfl⟩ : syracuseStep 1659217 = 1244413) B1244413
theorem B1659251 : Blo 980594 1659251 := bstep (se 1 (by rfl) ⟨1244438, by rfl⟩ : syracuseStep 1659251 = 2488877) B2488877
theorem B1495457 : Blo 980594 1495457 := bstep (se 2 (by rfl) ⟨560796, by rfl⟩ : syracuseStep 1495457 = 1121593) B1121593
theorem B2838989 : Blo 980594 2838989 := bstep (se 3 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 2838989 = 1064621) B1064621
theorem B1659379 : Blo 980594 1659379 := bstep (se 1 (by rfl) ⟨1244534, by rfl⟩ : syracuseStep 1659379 = 2489069) B2489069
theorem B3723853 : Blo 980594 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B1659521 : Blo 980594 1659521 := bstep (se 2 (by rfl) ⟨622320, by rfl⟩ : syracuseStep 1659521 = 1244641) B1244641
theorem B1397425 : Blo 980594 1397425 := bstep (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) B1048069
theorem B1397459 : Blo 980594 1397459 := bstep (se 1 (by rfl) ⟨1048094, by rfl⟩ : syracuseStep 1397459 = 2096189) B2096189
theorem B4969187 : Blo 980594 4969187 := bstep (se 1 (by rfl) ⟨3726890, by rfl⟩ : syracuseStep 4969187 = 7453781) B7453781
theorem B3363565 : Blo 980594 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B1659649 : Blo 980594 1659649 := bstep (se 2 (by rfl) ⟨622368, by rfl⟩ : syracuseStep 1659649 = 1244737) B1244737
theorem B1659683 : Blo 980594 1659683 := bstep (se 1 (by rfl) ⟨1244762, by rfl⟩ : syracuseStep 1659683 = 2489525) B2489525
theorem B1659811 : Blo 980594 1659811 := bstep (se 1 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 1659811 = 2489717) B2489717
theorem B1659953 : Blo 980594 1659953 := bstep (se 2 (by rfl) ⟨622482, by rfl⟩ : syracuseStep 1659953 = 1244965) B1244965
theorem B1660081 : Blo 980594 1660081 := bstep (se 2 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 1660081 = 1245061) B1245061
theorem B1660115 : Blo 980594 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B1135859 : Blo 980594 1135859 := bstep (se 1 (by rfl) ⟨851894, by rfl⟩ : syracuseStep 1135859 = 1703789) B1703789
theorem B1398017 : Blo 980594 1398017 := bstep (se 2 (by rfl) ⟨524256, by rfl⟩ : syracuseStep 1398017 = 1048513) B1048513
theorem B1398097 : Blo 980594 1398097 := bstep (se 2 (by rfl) ⟨524286, by rfl⟩ : syracuseStep 1398097 = 1048573) B1048573
theorem B1660243 : Blo 980594 1660243 := bstep (se 1 (by rfl) ⟨1245182, by rfl⟩ : syracuseStep 1660243 = 2490365) B2490365
theorem B3724643 : Blo 980594 3724643 := bstep (se 1 (by rfl) ⟨2793482, by rfl⟩ : syracuseStep 3724643 = 5586965) B5586965
theorem B1103251 : Blo 980594 1103251 := bstep (se 1 (by rfl) ⟨827438, by rfl⟩ : syracuseStep 1103251 = 1654877) B1654877
theorem B1660385 : Blo 980594 1660385 := bstep (se 2 (by rfl) ⟨622644, by rfl⟩ : syracuseStep 1660385 = 1245289) B1245289
theorem B4969997 : Blo 980594 4969997 := bstep (se 3 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 4969997 = 1863749) B1863749
theorem B1103395 : Blo 980594 1103395 := bstep (se 1 (by rfl) ⟨827546, by rfl⟩ : syracuseStep 1103395 = 1655093) B1655093
theorem B1660513 : Blo 980594 1660513 := bstep (se 2 (by rfl) ⟨622692, by rfl⟩ : syracuseStep 1660513 = 1245385) B1245385
theorem B1660547 : Blo 980594 1660547 := bstep (se 1 (by rfl) ⟨1245410, by rfl⟩ : syracuseStep 1660547 = 2490821) B2490821
theorem B3987107 : Blo 980594 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B1103539 : Blo 980594 1103539 := bstep (se 1 (by rfl) ⟨827654, by rfl⟩ : syracuseStep 1103539 = 1655309) B1655309
theorem B1988291 : Blo 980594 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B1595137 : Blo 980594 1595137 := bstep (se 2 (by rfl) ⟨598176, by rfl⟩ : syracuseStep 1595137 = 1196353) B1196353
theorem B1660675 : Blo 980594 1660675 := bstep (se 1 (by rfl) ⟨1245506, by rfl⟩ : syracuseStep 1660675 = 2491013) B2491013
theorem B7558925 : Blo 980594 7558925 := bstep (se 3 (by rfl) ⟨1417298, by rfl⟩ : syracuseStep 7558925 = 2834597) B2834597
theorem B1103683 : Blo 980594 1103683 := bstep (se 1 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 1103683 = 1655525) B1655525
theorem B2840465 : Blo 980594 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1660817 : Blo 980594 1660817 := bstep (se 2 (by rfl) ⟨622806, by rfl⟩ : syracuseStep 1660817 = 1245613) B1245613
theorem B1103827 : Blo 980594 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B3725297 : Blo 980594 3725297 := bstep (se 2 (by rfl) ⟨1396986, by rfl⟩ : syracuseStep 3725297 = 2793973) B2793973
theorem B1660945 : Blo 980594 1660945 := bstep (se 2 (by rfl) ⟨622854, by rfl⟩ : syracuseStep 1660945 = 1245709) B1245709
theorem B2021411 : Blo 980594 2021411 := bstep (se 1 (by rfl) ⟨1516058, by rfl⟩ : syracuseStep 2021411 = 3032117) B3032117
theorem B1660979 : Blo 980594 1660979 := bstep (se 1 (by rfl) ⟨1245734, by rfl⟩ : syracuseStep 1660979 = 2491469) B2491469
theorem B1398883 : Blo 980594 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B1103971 : Blo 980594 1103971 := bstep (se 1 (by rfl) ⟨827978, by rfl⟩ : syracuseStep 1103971 = 1655957) B1655957
theorem B1661107 : Blo 980594 1661107 := bstep (se 1 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 1661107 = 2491661) B2491661
theorem B1104115 : Blo 980594 1104115 := bstep (se 1 (by rfl) ⟨828086, by rfl⟩ : syracuseStep 1104115 = 1656173) B1656173
theorem B1661249 : Blo 980594 1661249 := bstep (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) B1245937
theorem B1104259 : Blo 980594 1104259 := bstep (se 1 (by rfl) ⟨828194, by rfl⟩ : syracuseStep 1104259 = 1656389) B1656389
theorem B1661377 : Blo 980594 1661377 := bstep (se 2 (by rfl) ⟨623016, by rfl⟩ : syracuseStep 1661377 = 1246033) B1246033
theorem B1661411 : Blo 980594 1661411 := bstep (se 1 (by rfl) ⟨1246058, by rfl⟩ : syracuseStep 1661411 = 2492117) B2492117
theorem B1104403 : Blo 980594 1104403 := bstep (se 1 (by rfl) ⟨828302, by rfl⟩ : syracuseStep 1104403 = 1656605) B1656605
theorem B1399361 : Blo 980594 1399361 := bstep (se 2 (by rfl) ⟨524760, by rfl⟩ : syracuseStep 1399361 = 1049521) B1049521
theorem B1989265 : Blo 980594 1989265 := bstep (se 2 (by rfl) ⟨745974, by rfl⟩ : syracuseStep 1989265 = 1491949) B1491949
theorem B1104547 : Blo 980594 1104547 := bstep (se 1 (by rfl) ⟨828410, by rfl⟩ : syracuseStep 1104547 = 1656821) B1656821
theorem B1399475 : Blo 980594 1399475 := bstep (se 1 (by rfl) ⟨1049606, by rfl⟩ : syracuseStep 1399475 = 2099213) B2099213
theorem B12114613 : Blo 980594 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B1399555 : Blo 980594 1399555 := bstep (se 1 (by rfl) ⟨1049666, by rfl⟩ : syracuseStep 1399555 = 2099333) B2099333
theorem B1104691 : Blo 980594 1104691 := bstep (se 1 (by rfl) ⟨828518, by rfl⟩ : syracuseStep 1104691 = 1657037) B1657037
theorem B1104835 : Blo 980594 1104835 := bstep (se 1 (by rfl) ⟨828626, by rfl⟩ : syracuseStep 1104835 = 1657253) B1657253
theorem B1727443 : Blo 980594 1727443 := bstep (se 1 (by rfl) ⟨1295582, by rfl⟩ : syracuseStep 1727443 = 2591165) B2591165
theorem B1104979 : Blo 980594 1104979 := bstep (se 1 (by rfl) ⟨828734, by rfl⟩ : syracuseStep 1104979 = 1657469) B1657469
theorem B86170709 : Blo 980594 86170709 := bstep (se 8 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 86170709 = 1009813) B1009813
theorem B90627299 : Blo 980594 90627299 := bstep (se 1 (by rfl) ⟨67970474, by rfl⟩ : syracuseStep 90627299 = 135940949) B135940949
theorem B16145635 : Blo 980594 16145635 := bstep (se 1 (by rfl) ⟨12109226, by rfl⟩ : syracuseStep 16145635 = 24218453) B24218453
theorem B1105123 : Blo 980594 1105123 := bstep (se 1 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 1105123 = 1657685) B1657685
theorem B1400113 : Blo 980594 1400113 := bstep (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) B1050085
theorem B1105267 : Blo 980594 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B3726755 : Blo 980594 3726755 := bstep (se 1 (by rfl) ⟨2795066, by rfl⟩ : syracuseStep 3726755 = 5590133) B5590133
theorem B3726769 : Blo 980594 3726769 := bstep (se 2 (by rfl) ⟨1397538, by rfl⟩ : syracuseStep 3726769 = 2795077) B2795077
theorem B12606961 : Blo 980594 12606961 := bstep (se 2 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 12606961 = 9455221) B9455221
theorem B1105411 : Blo 980594 1105411 := bstep (se 1 (by rfl) ⟨829058, by rfl⟩ : syracuseStep 1105411 = 1658117) B1658117
theorem B1105555 : Blo 980594 1105555 := bstep (se 1 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 1105555 = 1658333) B1658333
theorem B4480753 : Blo 980594 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B1105699 : Blo 980594 1105699 := bstep (se 1 (by rfl) ⟨829274, by rfl⟩ : syracuseStep 1105699 = 1658549) B1658549
theorem B1105843 : Blo 980594 1105843 := bstep (se 1 (by rfl) ⟨829382, by rfl⟩ : syracuseStep 1105843 = 1658765) B1658765
theorem B1400819 : Blo 980594 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B1105987 : Blo 980594 1105987 := bstep (se 1 (by rfl) ⟨829490, by rfl⟩ : syracuseStep 1105987 = 1658981) B1658981
theorem B1106131 : Blo 980594 1106131 := bstep (se 1 (by rfl) ⟨829598, by rfl⟩ : syracuseStep 1106131 = 1659197) B1659197
theorem B1106275 : Blo 980594 1106275 := bstep (se 1 (by rfl) ⟨829706, by rfl⟩ : syracuseStep 1106275 = 1659413) B1659413
theorem B4972913 : Blo 980594 4972913 := bstep (se 2 (by rfl) ⟨1864842, by rfl⟩ : syracuseStep 4972913 = 3729685) B3729685
theorem B2482609 : Blo 980594 2482609 := bstep (se 2 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 2482609 = 1861957) B1861957
theorem B1991153 : Blo 980594 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B1106419 : Blo 980594 1106419 := bstep (se 1 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 1106419 = 1659629) B1659629
theorem B1401457 : Blo 980594 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B1106563 : Blo 980594 1106563 := bstep (se 1 (by rfl) ⟨829922, by rfl⟩ : syracuseStep 1106563 = 1659845) B1659845
theorem B2482883 : Blo 980594 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B1401571 : Blo 980594 1401571 := bstep (se 1 (by rfl) ⟨1051178, by rfl⟩ : syracuseStep 1401571 = 2102357) B2102357
theorem B1106707 : Blo 980594 1106707 := bstep (se 1 (by rfl) ⟨830030, by rfl⟩ : syracuseStep 1106707 = 1660061) B1660061
theorem B3728227 : Blo 980594 3728227 := bstep (se 1 (by rfl) ⟨2796170, by rfl⟩ : syracuseStep 3728227 = 5592341) B5592341
theorem B2483075 : Blo 980594 2483075 := bstep (se 1 (by rfl) ⟨1862306, by rfl⟩ : syracuseStep 2483075 = 3724613) B3724613
theorem B1106851 : Blo 980594 1106851 := bstep (se 1 (by rfl) ⟨830138, by rfl⟩ : syracuseStep 1106851 = 1660277) B1660277
theorem B1106995 : Blo 980594 1106995 := bstep (se 1 (by rfl) ⟨830246, by rfl⟩ : syracuseStep 1106995 = 1660493) B1660493
theorem B7169123 : Blo 980594 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B5661809 : Blo 980594 5661809 := bstep (se 2 (by rfl) ⟨2123178, by rfl⟩ : syracuseStep 5661809 = 4246357) B4246357
theorem B1107139 : Blo 980594 1107139 := bstep (se 1 (by rfl) ⟨830354, by rfl⟩ : syracuseStep 1107139 = 1660709) B1660709
theorem B6808781 : Blo 980594 6808781 := bstep (se 3 (by rfl) ⟨1276646, by rfl⟩ : syracuseStep 6808781 = 2553293) B2553293
theorem B2516195 : Blo 980594 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B1107283 : Blo 980594 1107283 := bstep (se 1 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 1107283 = 1660925) B1660925
theorem B1107427 : Blo 980594 1107427 := bstep (se 1 (by rfl) ⟨830570, by rfl⟩ : syracuseStep 1107427 = 1661141) B1661141
theorem B1107571 : Blo 980594 1107571 := bstep (se 1 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 1107571 = 1661357) B1661357
theorem B4974371 : Blo 980594 4974371 := bstep (se 1 (by rfl) ⟨3730778, by rfl⟩ : syracuseStep 4974371 = 7461557) B7461557
theorem B2484017 : Blo 980594 2484017 := bstep (se 2 (by rfl) ⟨931506, by rfl⟩ : syracuseStep 2484017 = 1863013) B1863013
theorem B2484067 : Blo 980594 2484067 := bstep (se 1 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 2484067 = 3726101) B3726101
theorem B11200355 : Blo 980594 11200355 := bstep (se 1 (by rfl) ⟨8400266, by rfl⟩ : syracuseStep 11200355 = 16800533) B16800533
theorem B2484209 : Blo 980594 2484209 := bstep (se 2 (by rfl) ⟨931578, by rfl⟩ : syracuseStep 2484209 = 1863157) B1863157
theorem B1861699 : Blo 980594 1861699 := bstep (se 1 (by rfl) ⟨1396274, by rfl⟩ : syracuseStep 1861699 = 2792549) B2792549
theorem B1992899 : Blo 980594 1992899 := bstep (se 1 (by rfl) ⟨1494674, by rfl⟩ : syracuseStep 1992899 = 2989349) B2989349
theorem B1861859 : Blo 980594 1861859 := bstep (se 1 (by rfl) ⟨1396394, by rfl⟩ : syracuseStep 1861859 = 2792789) B2792789
theorem B4975181 : Blo 980594 4975181 := bstep (se 3 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 4975181 = 1865693) B1865693
theorem B6286157 : Blo 980594 6286157 := bstep (se 3 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 6286157 = 2357309) B2357309
theorem B2485201 : Blo 980594 2485201 := bstep (se 2 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 2485201 = 1863901) B1863901
theorem B3730445 : Blo 980594 3730445 := bstep (se 3 (by rfl) ⟨699458, by rfl⟩ : syracuseStep 3730445 = 1398917) B1398917
theorem B1797233 : Blo 980594 1797233 := bstep (se 2 (by rfl) ⟨673962, by rfl⟩ : syracuseStep 1797233 = 1347925) B1347925
theorem B2485475 : Blo 980594 2485475 := bstep (se 1 (by rfl) ⟨1864106, by rfl⟩ : syracuseStep 2485475 = 3728213) B3728213
theorem B1862929 : Blo 980594 1862929 := bstep (se 2 (by rfl) ⟨698598, by rfl⟩ : syracuseStep 1862929 = 1397197) B1397197
theorem B2518289 : Blo 980594 2518289 := bstep (se 2 (by rfl) ⟨944358, by rfl⟩ : syracuseStep 2518289 = 1888717) B1888717
theorem B2485667 : Blo 980594 2485667 := bstep (se 1 (by rfl) ⟨1864250, by rfl⟩ : syracuseStep 2485667 = 3728501) B3728501
theorem B4189745 : Blo 980594 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B6385229 : Blo 980594 6385229 := bstep (se 3 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 6385229 = 2394461) B2394461
theorem B2125457 : Blo 980594 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B9432773 : Blo 980594 9432773 := bstep (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) B1768645
theorem B4190413 : Blo 980594 4190413 := bstep (se 3 (by rfl) ⟨785702, by rfl⟩ : syracuseStep 4190413 = 1571405) B1571405
theorem B1863985 : Blo 980594 1863985 := bstep (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) B1397989
theorem B2486609 : Blo 980594 2486609 := bstep (se 2 (by rfl) ⟨932478, by rfl⟩ : syracuseStep 2486609 = 1864957) B1864957
theorem B2486659 : Blo 980594 2486659 := bstep (se 1 (by rfl) ⟨1864994, by rfl⟩ : syracuseStep 2486659 = 3729989) B3729989
theorem B1241507 : Blo 980594 1241507 := bstep (se 1 (by rfl) ⟨931130, by rfl⟩ : syracuseStep 1241507 = 1862261) B1862261
theorem B1470899 : Blo 980594 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B1470929 : Blo 980594 1470929 := bstep (se 2 (by rfl) ⟨551598, by rfl⟩ : syracuseStep 1470929 = 1103197) B1103197
theorem B1470947 : Blo 980594 1470947 := bstep (se 1 (by rfl) ⟨1103210, by rfl⟩ : syracuseStep 1470947 = 2206421) B2206421
theorem B1470977 : Blo 980594 1470977 := bstep (se 2 (by rfl) ⟨551616, by rfl⟩ : syracuseStep 1470977 = 1103233) B1103233
theorem B2486801 : Blo 980594 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B1470995 : Blo 980594 1470995 := bstep (se 1 (by rfl) ⟨1103246, by rfl⟩ : syracuseStep 1470995 = 2206493) B2206493
theorem B1471025 : Blo 980594 1471025 := bstep (se 2 (by rfl) ⟨551634, by rfl⟩ : syracuseStep 1471025 = 1103269) B1103269
theorem B1471043 : Blo 980594 1471043 := bstep (se 1 (by rfl) ⟨1103282, by rfl⟩ : syracuseStep 1471043 = 2206565) B2206565
theorem B5599813 : Blo 980594 5599813 := bstep (se 4 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 5599813 = 1049965) B1049965
theorem B1471073 : Blo 980594 1471073 := bstep (se 2 (by rfl) ⟨551652, by rfl⟩ : syracuseStep 1471073 = 1103305) B1103305
theorem B1471091 : Blo 980594 1471091 := bstep (se 1 (by rfl) ⟨1103318, by rfl⟩ : syracuseStep 1471091 = 2206637) B2206637
theorem B1471121 : Blo 980594 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B1471139 : Blo 980594 1471139 := bstep (se 1 (by rfl) ⟨1103354, by rfl⟩ : syracuseStep 1471139 = 2206709) B2206709
theorem B10613429 : Blo 980594 10613429 := bstep (se 5 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 10613429 = 995009) B995009
theorem B1471169 : Blo 980594 1471169 := bstep (se 2 (by rfl) ⟨551688, by rfl⟩ : syracuseStep 1471169 = 1103377) B1103377
theorem B1864387 : Blo 980594 1864387 := bstep (se 1 (by rfl) ⟨1398290, by rfl⟩ : syracuseStep 1864387 = 2796581) B2796581
theorem B12612293 : Blo 980594 12612293 := bstep (se 4 (by rfl) ⟨1182402, by rfl⟩ : syracuseStep 12612293 = 2364805) B2364805
theorem B1471187 : Blo 980594 1471187 := bstep (se 1 (by rfl) ⟨1103390, by rfl⟩ : syracuseStep 1471187 = 2206781) B2206781
theorem B1471217 : Blo 980594 1471217 := bstep (se 2 (by rfl) ⟨551706, by rfl⟩ : syracuseStep 1471217 = 1103413) B1103413
theorem B1864433 : Blo 980594 1864433 := bstep (se 2 (by rfl) ⟨699162, by rfl⟩ : syracuseStep 1864433 = 1398325) B1398325
theorem B1471235 : Blo 980594 1471235 := bstep (se 1 (by rfl) ⟨1103426, by rfl⟩ : syracuseStep 1471235 = 2206853) B2206853
theorem B1471265 : Blo 980594 1471265 := bstep (se 2 (by rfl) ⟨551724, by rfl⟩ : syracuseStep 1471265 = 1103449) B1103449
theorem B4191011 : Blo 980594 4191011 := bstep (se 1 (by rfl) ⟨3143258, by rfl⟩ : syracuseStep 4191011 = 6286517) B6286517
theorem B1471283 : Blo 980594 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B1471313 : Blo 980594 1471313 := bstep (se 2 (by rfl) ⟨551742, by rfl⟩ : syracuseStep 1471313 = 1103485) B1103485
theorem B1471331 : Blo 980594 1471331 := bstep (se 1 (by rfl) ⟨1103498, by rfl⟩ : syracuseStep 1471331 = 2206997) B2206997
theorem B7467875 : Blo 980594 7467875 := bstep (se 1 (by rfl) ⟨5600906, by rfl⟩ : syracuseStep 7467875 = 11201813) B11201813
theorem B1471361 : Blo 980594 1471361 := bstep (se 2 (by rfl) ⟨551760, by rfl⟩ : syracuseStep 1471361 = 1103521) B1103521
theorem B1471379 : Blo 980594 1471379 := bstep (se 1 (by rfl) ⟨1103534, by rfl⟩ : syracuseStep 1471379 = 2207069) B2207069
theorem B1471409 : Blo 980594 1471409 := bstep (se 2 (by rfl) ⟨551778, by rfl⟩ : syracuseStep 1471409 = 1103557) B1103557
theorem B1471427 : Blo 980594 1471427 := bstep (se 1 (by rfl) ⟨1103570, by rfl⟩ : syracuseStep 1471427 = 2207141) B2207141
theorem B1471457 : Blo 980594 1471457 := bstep (se 2 (by rfl) ⟨551796, by rfl⟩ : syracuseStep 1471457 = 1103593) B1103593
theorem B1471475 : Blo 980594 1471475 := bstep (se 1 (by rfl) ⟨1103606, by rfl⟩ : syracuseStep 1471475 = 2207213) B2207213
theorem B1471505 : Blo 980594 1471505 := bstep (se 2 (by rfl) ⟨551814, by rfl⟩ : syracuseStep 1471505 = 1103629) B1103629
theorem B1864721 : Blo 980594 1864721 := bstep (se 2 (by rfl) ⟨699270, by rfl⟩ : syracuseStep 1864721 = 1398541) B1398541
theorem B1471523 : Blo 980594 1471523 := bstep (se 1 (by rfl) ⟨1103642, by rfl⟩ : syracuseStep 1471523 = 2207285) B2207285
theorem B1471553 : Blo 980594 1471553 := bstep (se 2 (by rfl) ⟨551832, by rfl⟩ : syracuseStep 1471553 = 1103665) B1103665
theorem B1471571 : Blo 980594 1471571 := bstep (se 1 (by rfl) ⟨1103678, by rfl⟩ : syracuseStep 1471571 = 2207357) B2207357
theorem B1242211 : Blo 980594 1242211 := bstep (se 1 (by rfl) ⟨931658, by rfl⟩ : syracuseStep 1242211 = 1863317) B1863317
theorem B1471601 : Blo 980594 1471601 := bstep (se 2 (by rfl) ⟨551850, by rfl⟩ : syracuseStep 1471601 = 1103701) B1103701
theorem B1471619 : Blo 980594 1471619 := bstep (se 1 (by rfl) ⟨1103714, by rfl⟩ : syracuseStep 1471619 = 2207429) B2207429
theorem B1471649 : Blo 980594 1471649 := bstep (se 2 (by rfl) ⟨551868, by rfl⟩ : syracuseStep 1471649 = 1103737) B1103737
theorem B1471667 : Blo 980594 1471667 := bstep (se 1 (by rfl) ⟨1103750, by rfl⟩ : syracuseStep 1471667 = 2207501) B2207501
theorem B1242307 : Blo 980594 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B10220741 : Blo 980594 10220741 := bstep (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) B1916389
theorem B1471697 : Blo 980594 1471697 := bstep (se 2 (by rfl) ⟨551886, by rfl⟩ : syracuseStep 1471697 = 1103773) B1103773
theorem B1471715 : Blo 980594 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B5305571 : Blo 980594 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B1471745 : Blo 980594 1471745 := bstep (se 2 (by rfl) ⟨551904, by rfl⟩ : syracuseStep 1471745 = 1103809) B1103809
theorem B3142925 : Blo 980594 3142925 := bstep (se 3 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 3142925 = 1178597) B1178597
theorem B1471763 : Blo 980594 1471763 := bstep (se 1 (by rfl) ⟨1103822, by rfl⟩ : syracuseStep 1471763 = 2207645) B2207645
theorem B1471793 : Blo 980594 1471793 := bstep (se 2 (by rfl) ⟨551922, by rfl⟩ : syracuseStep 1471793 = 1103845) B1103845
theorem B1471811 : Blo 980594 1471811 := bstep (se 1 (by rfl) ⟨1103858, by rfl⟩ : syracuseStep 1471811 = 2207717) B2207717
theorem B1471841 : Blo 980594 1471841 := bstep (se 2 (by rfl) ⟨551940, by rfl⟩ : syracuseStep 1471841 = 1103881) B1103881
theorem B1471859 : Blo 980594 1471859 := bstep (se 1 (by rfl) ⟨1103894, by rfl⟩ : syracuseStep 1471859 = 2207789) B2207789
theorem B3143053 : Blo 980594 3143053 := bstep (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) B1178645
theorem B1471889 : Blo 980594 1471889 := bstep (se 2 (by rfl) ⟨551958, by rfl⟩ : syracuseStep 1471889 = 1103917) B1103917
theorem B1471907 : Blo 980594 1471907 := bstep (se 1 (by rfl) ⟨1103930, by rfl⟩ : syracuseStep 1471907 = 2207861) B2207861
theorem B4978097 : Blo 980594 4978097 := bstep (se 2 (by rfl) ⟨1866786, by rfl⟩ : syracuseStep 4978097 = 3733573) B3733573
theorem B1471937 : Blo 980594 1471937 := bstep (se 2 (by rfl) ⟨551976, by rfl⟩ : syracuseStep 1471937 = 1103953) B1103953
theorem B1471955 : Blo 980594 1471955 := bstep (se 1 (by rfl) ⟨1103966, by rfl⟩ : syracuseStep 1471955 = 2207933) B2207933
theorem B3536369 : Blo 980594 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B1471985 : Blo 980594 1471985 := bstep (se 2 (by rfl) ⟨551994, by rfl⟩ : syracuseStep 1471985 = 1103989) B1103989
theorem B2487793 : Blo 980594 2487793 := bstep (se 2 (by rfl) ⟨932922, by rfl⟩ : syracuseStep 2487793 = 1865845) B1865845
theorem B1472003 : Blo 980594 1472003 := bstep (se 1 (by rfl) ⟨1104002, by rfl⟩ : syracuseStep 1472003 = 2208005) B2208005
theorem B1472033 : Blo 980594 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B1472051 : Blo 980594 1472051 := bstep (se 1 (by rfl) ⟨1104038, by rfl⟩ : syracuseStep 1472051 = 2208077) B2208077
theorem B1472081 : Blo 980594 1472081 := bstep (se 2 (by rfl) ⟨552030, by rfl⟩ : syracuseStep 1472081 = 1104061) B1104061
theorem B1472099 : Blo 980594 1472099 := bstep (se 1 (by rfl) ⟨1104074, by rfl⟩ : syracuseStep 1472099 = 2208149) B2208149
theorem B980595 : Blo 980594 980595 := bstep (se 1 (by rfl) ⟨735446, by rfl⟩ : syracuseStep 980595 = 1470893) B1470893
theorem B1472129 : Blo 980594 1472129 := bstep (se 2 (by rfl) ⟨552048, by rfl⟩ : syracuseStep 1472129 = 1104097) B1104097
theorem B980611 : Blo 980594 980611 := bstep (se 1 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 980611 = 1470917) B1470917
theorem B980627 : Blo 980594 980627 := bstep (se 1 (by rfl) ⟨735470, by rfl⟩ : syracuseStep 980627 = 1470941) B1470941
theorem B1472147 : Blo 980594 1472147 := bstep (se 1 (by rfl) ⟨1104110, by rfl⟩ : syracuseStep 1472147 = 2208221) B2208221
theorem B980643 : Blo 980594 980643 := bstep (se 1 (by rfl) ⟨735482, by rfl⟩ : syracuseStep 980643 = 1470965) B1470965
theorem B1472177 : Blo 980594 1472177 := bstep (se 2 (by rfl) ⟨552066, by rfl⟩ : syracuseStep 1472177 = 1104133) B1104133
theorem B980659 : Blo 980594 980659 := bstep (se 1 (by rfl) ⟨735494, by rfl⟩ : syracuseStep 980659 = 1470989) B1470989
theorem B1242803 : Blo 980594 1242803 := bstep (se 1 (by rfl) ⟨932102, by rfl⟩ : syracuseStep 1242803 = 1864205) B1864205
theorem B980675 : Blo 980594 980675 := bstep (se 1 (by rfl) ⟨735506, by rfl⟩ : syracuseStep 980675 = 1471013) B1471013
theorem B1472195 : Blo 980594 1472195 := bstep (se 1 (by rfl) ⟨1104146, by rfl⟩ : syracuseStep 1472195 = 2208293) B2208293
theorem B980691 : Blo 980594 980691 := bstep (se 1 (by rfl) ⟨735518, by rfl⟩ : syracuseStep 980691 = 1471037) B1471037
theorem B1472225 : Blo 980594 1472225 := bstep (se 2 (by rfl) ⟨552084, by rfl⟩ : syracuseStep 1472225 = 1104169) B1104169
theorem B980707 : Blo 980594 980707 := bstep (se 1 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 980707 = 1471061) B1471061
theorem B1865443 : Blo 980594 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B980723 : Blo 980594 980723 := bstep (se 1 (by rfl) ⟨735542, by rfl⟩ : syracuseStep 980723 = 1471085) B1471085
theorem B1472243 : Blo 980594 1472243 := bstep (se 1 (by rfl) ⟨1104182, by rfl⟩ : syracuseStep 1472243 = 2208365) B2208365
theorem B980739 : Blo 980594 980739 := bstep (se 1 (by rfl) ⟨735554, by rfl⟩ : syracuseStep 980739 = 1471109) B1471109
theorem B2488067 : Blo 980594 2488067 := bstep (se 1 (by rfl) ⟨1866050, by rfl⟩ : syracuseStep 2488067 = 3732101) B3732101
theorem B1472273 : Blo 980594 1472273 := bstep (se 2 (by rfl) ⟨552102, by rfl⟩ : syracuseStep 1472273 = 1104205) B1104205
theorem B980755 : Blo 980594 980755 := bstep (se 1 (by rfl) ⟨735566, by rfl⟩ : syracuseStep 980755 = 1471133) B1471133
theorem B980771 : Blo 980594 980771 := bstep (se 1 (by rfl) ⟨735578, by rfl⟩ : syracuseStep 980771 = 1471157) B1471157
theorem B1472291 : Blo 980594 1472291 := bstep (se 1 (by rfl) ⟨1104218, by rfl⟩ : syracuseStep 1472291 = 2208437) B2208437
theorem B980787 : Blo 980594 980787 := bstep (se 1 (by rfl) ⟨735590, by rfl⟩ : syracuseStep 980787 = 1471181) B1471181
theorem B1472321 : Blo 980594 1472321 := bstep (se 2 (by rfl) ⟨552120, by rfl⟩ : syracuseStep 1472321 = 1104241) B1104241
theorem B980803 : Blo 980594 980803 := bstep (se 1 (by rfl) ⟨735602, by rfl⟩ : syracuseStep 980803 = 1471205) B1471205
theorem B980819 : Blo 980594 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B1472339 : Blo 980594 1472339 := bstep (se 1 (by rfl) ⟨1104254, by rfl⟩ : syracuseStep 1472339 = 2208509) B2208509
theorem B980835 : Blo 980594 980835 := bstep (se 1 (by rfl) ⟨735626, by rfl⟩ : syracuseStep 980835 = 1471253) B1471253
theorem B1472369 : Blo 980594 1472369 := bstep (se 2 (by rfl) ⟨552138, by rfl⟩ : syracuseStep 1472369 = 1104277) B1104277
theorem B3733361 : Blo 980594 3733361 := bstep (se 2 (by rfl) ⟨1400010, by rfl⟩ : syracuseStep 3733361 = 2800021) B2800021
theorem B980851 : Blo 980594 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B980867 : Blo 980594 980867 := bstep (se 1 (by rfl) ⟨735650, by rfl⟩ : syracuseStep 980867 = 1471301) B1471301
theorem B1472387 : Blo 980594 1472387 := bstep (se 1 (by rfl) ⟨1104290, by rfl⟩ : syracuseStep 1472387 = 2208581) B2208581
theorem B980883 : Blo 980594 980883 := bstep (se 1 (by rfl) ⟨735662, by rfl⟩ : syracuseStep 980883 = 1471325) B1471325
theorem B1472417 : Blo 980594 1472417 := bstep (se 2 (by rfl) ⟨552156, by rfl⟩ : syracuseStep 1472417 = 1104313) B1104313
theorem B980899 : Blo 980594 980899 := bstep (se 1 (by rfl) ⟨735674, by rfl⟩ : syracuseStep 980899 = 1471349) B1471349
theorem B980915 : Blo 980594 980915 := bstep (se 1 (by rfl) ⟨735686, by rfl⟩ : syracuseStep 980915 = 1471373) B1471373
theorem B1472435 : Blo 980594 1472435 := bstep (se 1 (by rfl) ⟨1104326, by rfl⟩ : syracuseStep 1472435 = 2208653) B2208653
theorem B980931 : Blo 980594 980931 := bstep (se 1 (by rfl) ⟨735698, by rfl⟩ : syracuseStep 980931 = 1471397) B1471397
theorem B2488259 : Blo 980594 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B1472465 : Blo 980594 1472465 := bstep (se 2 (by rfl) ⟨552174, by rfl⟩ : syracuseStep 1472465 = 1104349) B1104349
theorem B980947 : Blo 980594 980947 := bstep (se 1 (by rfl) ⟨735710, by rfl⟩ : syracuseStep 980947 = 1471421) B1471421
theorem B980963 : Blo 980594 980963 := bstep (se 1 (by rfl) ⟨735722, by rfl⟩ : syracuseStep 980963 = 1471445) B1471445
theorem B1472483 : Blo 980594 1472483 := bstep (se 1 (by rfl) ⟨1104362, by rfl⟩ : syracuseStep 1472483 = 2208725) B2208725
theorem B980979 : Blo 980594 980979 := bstep (se 1 (by rfl) ⟨735734, by rfl⟩ : syracuseStep 980979 = 1471469) B1471469
theorem B1472513 : Blo 980594 1472513 := bstep (se 2 (by rfl) ⟨552192, by rfl⟩ : syracuseStep 1472513 = 1104385) B1104385
theorem B980995 : Blo 980594 980995 := bstep (se 1 (by rfl) ⟨735746, by rfl⟩ : syracuseStep 980995 = 1471493) B1471493
theorem B981011 : Blo 980594 981011 := bstep (se 1 (by rfl) ⟨735758, by rfl⟩ : syracuseStep 981011 = 1471517) B1471517
theorem B1472531 : Blo 980594 1472531 := bstep (se 1 (by rfl) ⟨1104398, by rfl⟩ : syracuseStep 1472531 = 2208797) B2208797
theorem B2095139 : Blo 980594 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B981027 : Blo 980594 981027 := bstep (se 1 (by rfl) ⟨735770, by rfl⟩ : syracuseStep 981027 = 1471541) B1471541
theorem B3536945 : Blo 980594 3536945 := bstep (se 2 (by rfl) ⟨1326354, by rfl⟩ : syracuseStep 3536945 = 2652709) B2652709
theorem B1472561 : Blo 980594 1472561 := bstep (se 2 (by rfl) ⟨552210, by rfl⟩ : syracuseStep 1472561 = 1104421) B1104421
theorem B981043 : Blo 980594 981043 := bstep (se 1 (by rfl) ⟨735782, by rfl⟩ : syracuseStep 981043 = 1471565) B1471565
theorem B20183093 : Blo 980594 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B981059 : Blo 980594 981059 := bstep (se 1 (by rfl) ⟨735794, by rfl⟩ : syracuseStep 981059 = 1471589) B1471589
theorem B1472579 : Blo 980594 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B981075 : Blo 980594 981075 := bstep (se 1 (by rfl) ⟨735806, by rfl⟩ : syracuseStep 981075 = 1471613) B1471613
theorem B981091 : Blo 980594 981091 := bstep (se 1 (by rfl) ⟨735818, by rfl⟩ : syracuseStep 981091 = 1471637) B1471637
theorem B2357347 : Blo 980594 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B1472609 : Blo 980594 1472609 := bstep (se 2 (by rfl) ⟨552228, by rfl⟩ : syracuseStep 1472609 = 1104457) B1104457
theorem B981107 : Blo 980594 981107 := bstep (se 1 (by rfl) ⟨735830, by rfl⟩ : syracuseStep 981107 = 1471661) B1471661
theorem B1472627 : Blo 980594 1472627 := bstep (se 1 (by rfl) ⟨1104470, by rfl⟩ : syracuseStep 1472627 = 2208941) B2208941
theorem B981123 : Blo 980594 981123 := bstep (se 1 (by rfl) ⟨735842, by rfl⟩ : syracuseStep 981123 = 1471685) B1471685
theorem B2095249 : Blo 980594 2095249 := bstep (se 2 (by rfl) ⟨785718, by rfl⟩ : syracuseStep 2095249 = 1571437) B1571437
theorem B1472657 : Blo 980594 1472657 := bstep (se 2 (by rfl) ⟨552246, by rfl⟩ : syracuseStep 1472657 = 1104493) B1104493
theorem B981139 : Blo 980594 981139 := bstep (se 1 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 981139 = 1471709) B1471709
theorem B981155 : Blo 980594 981155 := bstep (se 1 (by rfl) ⟨735866, by rfl⟩ : syracuseStep 981155 = 1471733) B1471733
theorem B1472675 : Blo 980594 1472675 := bstep (se 1 (by rfl) ⟨1104506, by rfl⟩ : syracuseStep 1472675 = 2209013) B2209013
theorem B1865891 : Blo 980594 1865891 := bstep (se 1 (by rfl) ⟨1399418, by rfl⟩ : syracuseStep 1865891 = 2798837) B2798837
theorem B981171 : Blo 980594 981171 := bstep (se 1 (by rfl) ⟨735878, by rfl⟩ : syracuseStep 981171 = 1471757) B1471757
theorem B981187 : Blo 980594 981187 := bstep (se 1 (by rfl) ⟨735890, by rfl⟩ : syracuseStep 981187 = 1471781) B1471781
theorem B1472705 : Blo 980594 1472705 := bstep (se 2 (by rfl) ⟨552264, by rfl⟩ : syracuseStep 1472705 = 1104529) B1104529
theorem B981203 : Blo 980594 981203 := bstep (se 1 (by rfl) ⟨735902, by rfl⟩ : syracuseStep 981203 = 1471805) B1471805
theorem B1472723 : Blo 980594 1472723 := bstep (se 1 (by rfl) ⟨1104542, by rfl⟩ : syracuseStep 1472723 = 2209085) B2209085
theorem B981219 : Blo 980594 981219 := bstep (se 1 (by rfl) ⟨735914, by rfl⟩ : syracuseStep 981219 = 1471829) B1471829
theorem B1767665 : Blo 980594 1767665 := bstep (se 2 (by rfl) ⟨662874, by rfl⟩ : syracuseStep 1767665 = 1325749) B1325749
theorem B1472753 : Blo 980594 1472753 := bstep (se 2 (by rfl) ⟨552282, by rfl⟩ : syracuseStep 1472753 = 1104565) B1104565
theorem B981235 : Blo 980594 981235 := bstep (se 1 (by rfl) ⟨735926, by rfl⟩ : syracuseStep 981235 = 1471853) B1471853
theorem B981251 : Blo 980594 981251 := bstep (se 1 (by rfl) ⟨735938, by rfl⟩ : syracuseStep 981251 = 1471877) B1471877
theorem B1472771 : Blo 980594 1472771 := bstep (se 1 (by rfl) ⟨1104578, by rfl⟩ : syracuseStep 1472771 = 2209157) B2209157
theorem B981267 : Blo 980594 981267 := bstep (se 1 (by rfl) ⟨735950, by rfl⟩ : syracuseStep 981267 = 1471901) B1471901
theorem B1472801 : Blo 980594 1472801 := bstep (se 2 (by rfl) ⟨552300, by rfl⟩ : syracuseStep 1472801 = 1104601) B1104601
theorem B981283 : Blo 980594 981283 := bstep (se 1 (by rfl) ⟨735962, by rfl⟩ : syracuseStep 981283 = 1471925) B1471925
theorem B981299 : Blo 980594 981299 := bstep (se 1 (by rfl) ⟨735974, by rfl⟩ : syracuseStep 981299 = 1471949) B1471949
theorem B1472819 : Blo 980594 1472819 := bstep (se 1 (by rfl) ⟨1104614, by rfl⟩ : syracuseStep 1472819 = 2209229) B2209229
theorem B981315 : Blo 980594 981315 := bstep (se 1 (by rfl) ⟨735986, by rfl⟩ : syracuseStep 981315 = 1471973) B1471973
theorem B1472849 : Blo 980594 1472849 := bstep (se 2 (by rfl) ⟨552318, by rfl⟩ : syracuseStep 1472849 = 1104637) B1104637
theorem B981331 : Blo 980594 981331 := bstep (se 1 (by rfl) ⟨735998, by rfl⟩ : syracuseStep 981331 = 1471997) B1471997
theorem B981347 : Blo 980594 981347 := bstep (se 1 (by rfl) ⟨736010, by rfl⟩ : syracuseStep 981347 = 1472021) B1472021
theorem B1472867 : Blo 980594 1472867 := bstep (se 1 (by rfl) ⟨1104650, by rfl⟩ : syracuseStep 1472867 = 2209301) B2209301
theorem B981363 : Blo 980594 981363 := bstep (se 1 (by rfl) ⟨736022, by rfl⟩ : syracuseStep 981363 = 1472045) B1472045
theorem B1243507 : Blo 980594 1243507 := bstep (se 1 (by rfl) ⟨932630, by rfl⟩ : syracuseStep 1243507 = 1865261) B1865261
theorem B1472897 : Blo 980594 1472897 := bstep (se 2 (by rfl) ⟨552336, by rfl⟩ : syracuseStep 1472897 = 1104673) B1104673
theorem B981379 : Blo 980594 981379 := bstep (se 1 (by rfl) ⟨736034, by rfl⟩ : syracuseStep 981379 = 1472069) B1472069
theorem B981395 : Blo 980594 981395 := bstep (se 1 (by rfl) ⟨736046, by rfl⟩ : syracuseStep 981395 = 1472093) B1472093
theorem B1472915 : Blo 980594 1472915 := bstep (se 1 (by rfl) ⟨1104686, by rfl⟩ : syracuseStep 1472915 = 2209373) B2209373
theorem B981411 : Blo 980594 981411 := bstep (se 1 (by rfl) ⟨736058, by rfl⟩ : syracuseStep 981411 = 1472117) B1472117
theorem B1472945 : Blo 980594 1472945 := bstep (se 2 (by rfl) ⟨552354, by rfl⟩ : syracuseStep 1472945 = 1104709) B1104709
theorem B981427 : Blo 980594 981427 := bstep (se 1 (by rfl) ⟨736070, by rfl⟩ : syracuseStep 981427 = 1472141) B1472141
theorem B981443 : Blo 980594 981443 := bstep (se 1 (by rfl) ⟨736082, by rfl⟩ : syracuseStep 981443 = 1472165) B1472165
theorem B1472963 : Blo 980594 1472963 := bstep (se 1 (by rfl) ⟨1104722, by rfl⟩ : syracuseStep 1472963 = 2209445) B2209445
theorem B1866179 : Blo 980594 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1243603 : Blo 980594 1243603 := bstep (se 1 (by rfl) ⟨932702, by rfl⟩ : syracuseStep 1243603 = 1865405) B1865405
theorem B981459 : Blo 980594 981459 := bstep (se 1 (by rfl) ⟨736094, by rfl⟩ : syracuseStep 981459 = 1472189) B1472189
theorem B1472993 : Blo 980594 1472993 := bstep (se 2 (by rfl) ⟨552372, by rfl⟩ : syracuseStep 1472993 = 1104745) B1104745
theorem B981475 : Blo 980594 981475 := bstep (se 1 (by rfl) ⟨736106, by rfl⟩ : syracuseStep 981475 = 1472213) B1472213
theorem B981491 : Blo 980594 981491 := bstep (se 1 (by rfl) ⟨736118, by rfl⟩ : syracuseStep 981491 = 1472237) B1472237
theorem B1473011 : Blo 980594 1473011 := bstep (se 1 (by rfl) ⟨1104758, by rfl⟩ : syracuseStep 1473011 = 2209517) B2209517
theorem B981507 : Blo 980594 981507 := bstep (se 1 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 981507 = 1472261) B1472261
theorem B5601797 : Blo 980594 5601797 := bstep (se 4 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 5601797 = 1050337) B1050337
theorem B1473041 : Blo 980594 1473041 := bstep (se 2 (by rfl) ⟨552390, by rfl⟩ : syracuseStep 1473041 = 1104781) B1104781
theorem B981523 : Blo 980594 981523 := bstep (se 1 (by rfl) ⟨736142, by rfl⟩ : syracuseStep 981523 = 1472285) B1472285
theorem B981539 : Blo 980594 981539 := bstep (se 1 (by rfl) ⟨736154, by rfl⟩ : syracuseStep 981539 = 1472309) B1472309
theorem B1473059 : Blo 980594 1473059 := bstep (se 1 (by rfl) ⟨1104794, by rfl⟩ : syracuseStep 1473059 = 2209589) B2209589
theorem B981555 : Blo 980594 981555 := bstep (se 1 (by rfl) ⟨736166, by rfl⟩ : syracuseStep 981555 = 1472333) B1472333
theorem B1473089 : Blo 980594 1473089 := bstep (se 2 (by rfl) ⟨552408, by rfl⟩ : syracuseStep 1473089 = 1104817) B1104817
theorem B981571 : Blo 980594 981571 := bstep (se 1 (by rfl) ⟨736178, by rfl⟩ : syracuseStep 981571 = 1472357) B1472357
theorem B1571411 : Blo 980594 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B981587 : Blo 980594 981587 := bstep (se 1 (by rfl) ⟨736190, by rfl⟩ : syracuseStep 981587 = 1472381) B1472381
theorem B1473107 : Blo 980594 1473107 := bstep (se 1 (by rfl) ⟨1104830, by rfl⟩ : syracuseStep 1473107 = 2209661) B2209661
theorem B981603 : Blo 980594 981603 := bstep (se 1 (by rfl) ⟨736202, by rfl⟩ : syracuseStep 981603 = 1472405) B1472405
theorem B1473137 : Blo 980594 1473137 := bstep (se 2 (by rfl) ⟨552426, by rfl⟩ : syracuseStep 1473137 = 1104853) B1104853
theorem B981619 : Blo 980594 981619 := bstep (se 1 (by rfl) ⟨736214, by rfl⟩ : syracuseStep 981619 = 1472429) B1472429
theorem B981635 : Blo 980594 981635 := bstep (se 1 (by rfl) ⟨736226, by rfl⟩ : syracuseStep 981635 = 1472453) B1472453
theorem B1473155 : Blo 980594 1473155 := bstep (se 1 (by rfl) ⟨1104866, by rfl⟩ : syracuseStep 1473155 = 2209733) B2209733
theorem B2357905 : Blo 980594 2357905 := bstep (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) B1768429
theorem B981651 : Blo 980594 981651 := bstep (se 1 (by rfl) ⟨736238, by rfl⟩ : syracuseStep 981651 = 1472477) B1472477
theorem B1473185 : Blo 980594 1473185 := bstep (se 2 (by rfl) ⟨552444, by rfl⟩ : syracuseStep 1473185 = 1104889) B1104889
theorem B981667 : Blo 980594 981667 := bstep (se 1 (by rfl) ⟨736250, by rfl⟩ : syracuseStep 981667 = 1472501) B1472501
theorem B981683 : Blo 980594 981683 := bstep (se 1 (by rfl) ⟨736262, by rfl⟩ : syracuseStep 981683 = 1472525) B1472525
theorem B1473203 : Blo 980594 1473203 := bstep (se 1 (by rfl) ⟨1104902, by rfl⟩ : syracuseStep 1473203 = 2209805) B2209805
theorem B981699 : Blo 980594 981699 := bstep (se 1 (by rfl) ⟨736274, by rfl⟩ : syracuseStep 981699 = 1472549) B1472549
theorem B1473233 : Blo 980594 1473233 := bstep (se 2 (by rfl) ⟨552462, by rfl⟩ : syracuseStep 1473233 = 1104925) B1104925
theorem B981715 : Blo 980594 981715 := bstep (se 1 (by rfl) ⟨736286, by rfl⟩ : syracuseStep 981715 = 1472573) B1472573
theorem B981731 : Blo 980594 981731 := bstep (se 1 (by rfl) ⟨736298, by rfl⟩ : syracuseStep 981731 = 1472597) B1472597
theorem B1473251 : Blo 980594 1473251 := bstep (se 1 (by rfl) ⟨1104938, by rfl⟩ : syracuseStep 1473251 = 2209877) B2209877
theorem B981747 : Blo 980594 981747 := bstep (se 1 (by rfl) ⟨736310, by rfl⟩ : syracuseStep 981747 = 1472621) B1472621
theorem B1473281 : Blo 980594 1473281 := bstep (se 2 (by rfl) ⟨552480, by rfl⟩ : syracuseStep 1473281 = 1104961) B1104961
theorem B981763 : Blo 980594 981763 := bstep (se 1 (by rfl) ⟨736322, by rfl⟩ : syracuseStep 981763 = 1472645) B1472645
theorem B981779 : Blo 980594 981779 := bstep (se 1 (by rfl) ⟨736334, by rfl⟩ : syracuseStep 981779 = 1472669) B1472669
theorem B1473299 : Blo 980594 1473299 := bstep (se 1 (by rfl) ⟨1104974, by rfl⟩ : syracuseStep 1473299 = 2209949) B2209949
theorem B981795 : Blo 980594 981795 := bstep (se 1 (by rfl) ⟨736346, by rfl⟩ : syracuseStep 981795 = 1472693) B1472693
theorem B1768241 : Blo 980594 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B1473329 : Blo 980594 1473329 := bstep (se 2 (by rfl) ⟨552498, by rfl⟩ : syracuseStep 1473329 = 1104997) B1104997
theorem B981811 : Blo 980594 981811 := bstep (se 1 (by rfl) ⟨736358, by rfl⟩ : syracuseStep 981811 = 1472717) B1472717
theorem B981827 : Blo 980594 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B1473347 : Blo 980594 1473347 := bstep (se 1 (by rfl) ⟨1105010, by rfl⟩ : syracuseStep 1473347 = 2210021) B2210021
theorem B981843 : Blo 980594 981843 := bstep (se 1 (by rfl) ⟨736382, by rfl⟩ : syracuseStep 981843 = 1472765) B1472765
theorem B1473377 : Blo 980594 1473377 := bstep (se 2 (by rfl) ⟨552516, by rfl⟩ : syracuseStep 1473377 = 1105033) B1105033
theorem B981859 : Blo 980594 981859 := bstep (se 1 (by rfl) ⟨736394, by rfl⟩ : syracuseStep 981859 = 1472789) B1472789
theorem B4979555 : Blo 980594 4979555 := bstep (se 1 (by rfl) ⟨3734666, by rfl⟩ : syracuseStep 4979555 = 7469333) B7469333
theorem B2489201 : Blo 980594 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B981875 : Blo 980594 981875 := bstep (se 1 (by rfl) ⟨736406, by rfl⟩ : syracuseStep 981875 = 1472813) B1472813
theorem B1473395 : Blo 980594 1473395 := bstep (se 1 (by rfl) ⟨1105046, by rfl⟩ : syracuseStep 1473395 = 2210093) B2210093
theorem B981891 : Blo 980594 981891 := bstep (se 1 (by rfl) ⟨736418, by rfl⟩ : syracuseStep 981891 = 1472837) B1472837
theorem B1473425 : Blo 980594 1473425 := bstep (se 2 (by rfl) ⟨552534, by rfl⟩ : syracuseStep 1473425 = 1105069) B1105069
theorem B981907 : Blo 980594 981907 := bstep (se 1 (by rfl) ⟨736430, by rfl⟩ : syracuseStep 981907 = 1472861) B1472861
theorem B981923 : Blo 980594 981923 := bstep (se 1 (by rfl) ⟨736442, by rfl⟩ : syracuseStep 981923 = 1472885) B1472885
theorem B1473443 : Blo 980594 1473443 := bstep (se 1 (by rfl) ⟨1105082, by rfl⟩ : syracuseStep 1473443 = 2210165) B2210165
theorem B2489251 : Blo 980594 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B981939 : Blo 980594 981939 := bstep (se 1 (by rfl) ⟨736454, by rfl⟩ : syracuseStep 981939 = 1472909) B1472909
theorem B1473473 : Blo 980594 1473473 := bstep (se 2 (by rfl) ⟨552552, by rfl⟩ : syracuseStep 1473473 = 1105105) B1105105
theorem B981955 : Blo 980594 981955 := bstep (se 1 (by rfl) ⟨736466, by rfl⟩ : syracuseStep 981955 = 1472933) B1472933
theorem B1244099 : Blo 980594 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B981971 : Blo 980594 981971 := bstep (se 1 (by rfl) ⟨736478, by rfl⟩ : syracuseStep 981971 = 1472957) B1472957
theorem B1473491 : Blo 980594 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B981987 : Blo 980594 981987 := bstep (se 1 (by rfl) ⟨736490, by rfl⟩ : syracuseStep 981987 = 1472981) B1472981
theorem B1473521 : Blo 980594 1473521 := bstep (se 2 (by rfl) ⟨552570, by rfl⟩ : syracuseStep 1473521 = 1105141) B1105141
theorem B1047539 : Blo 980594 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B982003 : Blo 980594 982003 := bstep (se 1 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 982003 = 1473005) B1473005
theorem B982019 : Blo 980594 982019 := bstep (se 1 (by rfl) ⟨736514, by rfl⟩ : syracuseStep 982019 = 1473029) B1473029
theorem B1473539 : Blo 980594 1473539 := bstep (se 1 (by rfl) ⟨1105154, by rfl⟩ : syracuseStep 1473539 = 2210309) B2210309
theorem B982035 : Blo 980594 982035 := bstep (se 1 (by rfl) ⟨736526, by rfl⟩ : syracuseStep 982035 = 1473053) B1473053
theorem B1473569 : Blo 980594 1473569 := bstep (se 2 (by rfl) ⟨552588, by rfl⟩ : syracuseStep 1473569 = 1105177) B1105177
theorem B982051 : Blo 980594 982051 := bstep (se 1 (by rfl) ⟨736538, by rfl⟩ : syracuseStep 982051 = 1473077) B1473077
theorem B2489393 : Blo 980594 2489393 := bstep (se 2 (by rfl) ⟨933522, by rfl⟩ : syracuseStep 2489393 = 1867045) B1867045
theorem B982067 : Blo 980594 982067 := bstep (se 1 (by rfl) ⟨736550, by rfl⟩ : syracuseStep 982067 = 1473101) B1473101
theorem B1473587 : Blo 980594 1473587 := bstep (se 1 (by rfl) ⟨1105190, by rfl⟩ : syracuseStep 1473587 = 2210381) B2210381
theorem B982083 : Blo 980594 982083 := bstep (se 1 (by rfl) ⟨736562, by rfl⟩ : syracuseStep 982083 = 1473125) B1473125
theorem B1473617 : Blo 980594 1473617 := bstep (se 2 (by rfl) ⟨552606, by rfl⟩ : syracuseStep 1473617 = 1105213) B1105213
theorem B982099 : Blo 980594 982099 := bstep (se 1 (by rfl) ⟨736574, by rfl⟩ : syracuseStep 982099 = 1473149) B1473149
theorem B5307491 : Blo 980594 5307491 := bstep (se 1 (by rfl) ⟨3980618, by rfl⟩ : syracuseStep 5307491 = 7961237) B7961237
theorem B982115 : Blo 980594 982115 := bstep (se 1 (by rfl) ⟨736586, by rfl⟩ : syracuseStep 982115 = 1473173) B1473173
theorem B1473635 : Blo 980594 1473635 := bstep (se 1 (by rfl) ⟨1105226, by rfl⟩ : syracuseStep 1473635 = 2210453) B2210453
theorem B982131 : Blo 980594 982131 := bstep (se 1 (by rfl) ⟨736598, by rfl⟩ : syracuseStep 982131 = 1473197) B1473197
theorem B1473665 : Blo 980594 1473665 := bstep (se 2 (by rfl) ⟨552624, by rfl⟩ : syracuseStep 1473665 = 1105249) B1105249
theorem B982147 : Blo 980594 982147 := bstep (se 1 (by rfl) ⟨736610, by rfl⟩ : syracuseStep 982147 = 1473221) B1473221
theorem B982163 : Blo 980594 982163 := bstep (se 1 (by rfl) ⟨736622, by rfl⟩ : syracuseStep 982163 = 1473245) B1473245
theorem B1473683 : Blo 980594 1473683 := bstep (se 1 (by rfl) ⟨1105262, by rfl⟩ : syracuseStep 1473683 = 2210525) B2210525
theorem B982179 : Blo 980594 982179 := bstep (se 1 (by rfl) ⟨736634, by rfl⟩ : syracuseStep 982179 = 1473269) B1473269
theorem B3538097 : Blo 980594 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B1473713 : Blo 980594 1473713 := bstep (se 2 (by rfl) ⟨552642, by rfl⟩ : syracuseStep 1473713 = 1105285) B1105285
theorem B982195 : Blo 980594 982195 := bstep (se 1 (by rfl) ⟨736646, by rfl⟩ : syracuseStep 982195 = 1473293) B1473293
theorem B3144899 : Blo 980594 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B982211 : Blo 980594 982211 := bstep (se 1 (by rfl) ⟨736658, by rfl⟩ : syracuseStep 982211 = 1473317) B1473317
theorem B1473731 : Blo 980594 1473731 := bstep (se 1 (by rfl) ⟨1105298, by rfl⟩ : syracuseStep 1473731 = 2210597) B2210597
theorem B982227 : Blo 980594 982227 := bstep (se 1 (by rfl) ⟨736670, by rfl⟩ : syracuseStep 982227 = 1473341) B1473341
theorem B1473761 : Blo 980594 1473761 := bstep (se 2 (by rfl) ⟨552660, by rfl⟩ : syracuseStep 1473761 = 1105321) B1105321
theorem B982243 : Blo 980594 982243 := bstep (se 1 (by rfl) ⟨736682, by rfl⟩ : syracuseStep 982243 = 1473365) B1473365
theorem B2522353 : Blo 980594 2522353 := bstep (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) B1891765
theorem B982259 : Blo 980594 982259 := bstep (se 1 (by rfl) ⟨736694, by rfl⟩ : syracuseStep 982259 = 1473389) B1473389
theorem B1473779 : Blo 980594 1473779 := bstep (se 1 (by rfl) ⟨1105334, by rfl⟩ : syracuseStep 1473779 = 2210669) B2210669
theorem B982275 : Blo 980594 982275 := bstep (se 1 (by rfl) ⟨736706, by rfl⟩ : syracuseStep 982275 = 1473413) B1473413
theorem B1473809 : Blo 980594 1473809 := bstep (se 2 (by rfl) ⟨552678, by rfl⟩ : syracuseStep 1473809 = 1105357) B1105357
theorem B982291 : Blo 980594 982291 := bstep (se 1 (by rfl) ⟨736718, by rfl⟩ : syracuseStep 982291 = 1473437) B1473437
theorem B3734819 : Blo 980594 3734819 := bstep (se 1 (by rfl) ⟨2801114, by rfl⟩ : syracuseStep 3734819 = 5602229) B5602229
theorem B982307 : Blo 980594 982307 := bstep (se 1 (by rfl) ⟨736730, by rfl⟩ : syracuseStep 982307 = 1473461) B1473461
theorem B1473827 : Blo 980594 1473827 := bstep (se 1 (by rfl) ⟨1105370, by rfl⟩ : syracuseStep 1473827 = 2210741) B2210741
theorem B2358577 : Blo 980594 2358577 := bstep (se 2 (by rfl) ⟨884466, by rfl⟩ : syracuseStep 2358577 = 1768933) B1768933
theorem B982323 : Blo 980594 982323 := bstep (se 1 (by rfl) ⟨736742, by rfl⟩ : syracuseStep 982323 = 1473485) B1473485
theorem B1473857 : Blo 980594 1473857 := bstep (se 2 (by rfl) ⟨552696, by rfl⟩ : syracuseStep 1473857 = 1105393) B1105393
theorem B3145027 : Blo 980594 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B982339 : Blo 980594 982339 := bstep (se 1 (by rfl) ⟨736754, by rfl⟩ : syracuseStep 982339 = 1473509) B1473509
theorem B982355 : Blo 980594 982355 := bstep (se 1 (by rfl) ⟨736766, by rfl⟩ : syracuseStep 982355 = 1473533) B1473533
theorem B1473875 : Blo 980594 1473875 := bstep (se 1 (by rfl) ⟨1105406, by rfl⟩ : syracuseStep 1473875 = 2210813) B2210813
theorem B982371 : Blo 980594 982371 := bstep (se 1 (by rfl) ⟨736778, by rfl⟩ : syracuseStep 982371 = 1473557) B1473557
theorem B1473905 : Blo 980594 1473905 := bstep (se 2 (by rfl) ⟨552714, by rfl⟩ : syracuseStep 1473905 = 1105429) B1105429
theorem B1867121 : Blo 980594 1867121 := bstep (se 2 (by rfl) ⟨700170, by rfl⟩ : syracuseStep 1867121 = 1400341) B1400341
theorem B982387 : Blo 980594 982387 := bstep (se 1 (by rfl) ⟨736790, by rfl⟩ : syracuseStep 982387 = 1473581) B1473581
theorem B982403 : Blo 980594 982403 := bstep (se 1 (by rfl) ⟨736802, by rfl⟩ : syracuseStep 982403 = 1473605) B1473605
theorem B1473923 : Blo 980594 1473923 := bstep (se 1 (by rfl) ⟨1105442, by rfl⟩ : syracuseStep 1473923 = 2210885) B2210885
theorem B982419 : Blo 980594 982419 := bstep (se 1 (by rfl) ⟨736814, by rfl⟩ : syracuseStep 982419 = 1473629) B1473629
theorem B1572257 : Blo 980594 1572257 := bstep (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) B1179193
theorem B1473953 : Blo 980594 1473953 := bstep (se 2 (by rfl) ⟨552732, by rfl⟩ : syracuseStep 1473953 = 1105465) B1105465
theorem B982435 : Blo 980594 982435 := bstep (se 1 (by rfl) ⟨736826, by rfl⟩ : syracuseStep 982435 = 1473653) B1473653
theorem B982451 : Blo 980594 982451 := bstep (se 1 (by rfl) ⟨736838, by rfl⟩ : syracuseStep 982451 = 1473677) B1473677
theorem B1473971 : Blo 980594 1473971 := bstep (se 1 (by rfl) ⟨1105478, by rfl⟩ : syracuseStep 1473971 = 2210957) B2210957
theorem B982467 : Blo 980594 982467 := bstep (se 1 (by rfl) ⟨736850, by rfl⟩ : syracuseStep 982467 = 1473701) B1473701
theorem B3145169 : Blo 980594 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B1474001 : Blo 980594 1474001 := bstep (se 2 (by rfl) ⟨552750, by rfl⟩ : syracuseStep 1474001 = 1105501) B1105501
theorem B982483 : Blo 980594 982483 := bstep (se 1 (by rfl) ⟨736862, by rfl⟩ : syracuseStep 982483 = 1473725) B1473725
theorem B7962083 : Blo 980594 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B982499 : Blo 980594 982499 := bstep (se 1 (by rfl) ⟨736874, by rfl⟩ : syracuseStep 982499 = 1473749) B1473749
theorem B1474019 : Blo 980594 1474019 := bstep (se 1 (by rfl) ⟨1105514, by rfl⟩ : syracuseStep 1474019 = 2211029) B2211029
theorem B982515 : Blo 980594 982515 := bstep (se 1 (by rfl) ⟨736886, by rfl⟩ : syracuseStep 982515 = 1473773) B1473773
theorem B1474049 : Blo 980594 1474049 := bstep (se 2 (by rfl) ⟨552768, by rfl⟩ : syracuseStep 1474049 = 1105537) B1105537
theorem B982531 : Blo 980594 982531 := bstep (se 1 (by rfl) ⟨736898, by rfl⟩ : syracuseStep 982531 = 1473797) B1473797
theorem B982547 : Blo 980594 982547 := bstep (se 1 (by rfl) ⟨736910, by rfl⟩ : syracuseStep 982547 = 1473821) B1473821
theorem B1474067 : Blo 980594 1474067 := bstep (se 1 (by rfl) ⟨1105550, by rfl⟩ : syracuseStep 1474067 = 2211101) B2211101
theorem B982563 : Blo 980594 982563 := bstep (se 1 (by rfl) ⟨736922, by rfl⟩ : syracuseStep 982563 = 1473845) B1473845
theorem B1474097 : Blo 980594 1474097 := bstep (se 2 (by rfl) ⟨552786, by rfl⟩ : syracuseStep 1474097 = 1105573) B1105573
theorem B982579 : Blo 980594 982579 := bstep (se 1 (by rfl) ⟨736934, by rfl⟩ : syracuseStep 982579 = 1473869) B1473869
theorem B3145283 : Blo 980594 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B982595 : Blo 980594 982595 := bstep (se 1 (by rfl) ⟨736946, by rfl⟩ : syracuseStep 982595 = 1473893) B1473893
theorem B1474115 : Blo 980594 1474115 := bstep (se 1 (by rfl) ⟨1105586, by rfl⟩ : syracuseStep 1474115 = 2211173) B2211173
theorem B982611 : Blo 980594 982611 := bstep (se 1 (by rfl) ⟨736958, by rfl⟩ : syracuseStep 982611 = 1473917) B1473917
theorem B1474145 : Blo 980594 1474145 := bstep (se 2 (by rfl) ⟨552804, by rfl⟩ : syracuseStep 1474145 = 1105609) B1105609
theorem B982627 : Blo 980594 982627 := bstep (se 1 (by rfl) ⟨736970, by rfl⟩ : syracuseStep 982627 = 1473941) B1473941
theorem B982643 : Blo 980594 982643 := bstep (se 1 (by rfl) ⟨736982, by rfl⟩ : syracuseStep 982643 = 1473965) B1473965
theorem B1474163 : Blo 980594 1474163 := bstep (se 1 (by rfl) ⟨1105622, by rfl⟩ : syracuseStep 1474163 = 2211245) B2211245
theorem B982659 : Blo 980594 982659 := bstep (se 1 (by rfl) ⟨736994, by rfl⟩ : syracuseStep 982659 = 1473989) B1473989
theorem B1244803 : Blo 980594 1244803 := bstep (se 1 (by rfl) ⟨933602, by rfl⟩ : syracuseStep 1244803 = 1867205) B1867205
theorem B4980365 : Blo 980594 4980365 := bstep (se 3 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 4980365 = 1867637) B1867637
theorem B1474193 : Blo 980594 1474193 := bstep (se 2 (by rfl) ⟨552822, by rfl⟩ : syracuseStep 1474193 = 1105645) B1105645
theorem B982675 : Blo 980594 982675 := bstep (se 1 (by rfl) ⟨737006, by rfl⟩ : syracuseStep 982675 = 1474013) B1474013
theorem B982691 : Blo 980594 982691 := bstep (se 1 (by rfl) ⟨737018, by rfl⟩ : syracuseStep 982691 = 1474037) B1474037
theorem B1474211 : Blo 980594 1474211 := bstep (se 1 (by rfl) ⟨1105658, by rfl⟩ : syracuseStep 1474211 = 2211317) B2211317
theorem B982707 : Blo 980594 982707 := bstep (se 1 (by rfl) ⟨737030, by rfl⟩ : syracuseStep 982707 = 1474061) B1474061
theorem B1474241 : Blo 980594 1474241 := bstep (se 2 (by rfl) ⟨552840, by rfl⟩ : syracuseStep 1474241 = 1105681) B1105681
theorem B982723 : Blo 980594 982723 := bstep (se 1 (by rfl) ⟨737042, by rfl⟩ : syracuseStep 982723 = 1474085) B1474085
theorem B982739 : Blo 980594 982739 := bstep (se 1 (by rfl) ⟨737054, by rfl⟩ : syracuseStep 982739 = 1474109) B1474109
theorem B1474259 : Blo 980594 1474259 := bstep (se 1 (by rfl) ⟨1105694, by rfl⟩ : syracuseStep 1474259 = 2211389) B2211389
theorem B982755 : Blo 980594 982755 := bstep (se 1 (by rfl) ⟨737066, by rfl⟩ : syracuseStep 982755 = 1474133) B1474133
theorem B1244899 : Blo 980594 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B1474289 : Blo 980594 1474289 := bstep (se 2 (by rfl) ⟨552858, by rfl⟩ : syracuseStep 1474289 = 1105717) B1105717
theorem B982771 : Blo 980594 982771 := bstep (se 1 (by rfl) ⟨737078, by rfl⟩ : syracuseStep 982771 = 1474157) B1474157
theorem B982787 : Blo 980594 982787 := bstep (se 1 (by rfl) ⟨737090, by rfl⟩ : syracuseStep 982787 = 1474181) B1474181
theorem B1474307 : Blo 980594 1474307 := bstep (se 1 (by rfl) ⟨1105730, by rfl⟩ : syracuseStep 1474307 = 2211461) B2211461
theorem B982803 : Blo 980594 982803 := bstep (se 1 (by rfl) ⟨737102, by rfl⟩ : syracuseStep 982803 = 1474205) B1474205
theorem B1474337 : Blo 980594 1474337 := bstep (se 2 (by rfl) ⟨552876, by rfl⟩ : syracuseStep 1474337 = 1105753) B1105753
theorem B982819 : Blo 980594 982819 := bstep (se 1 (by rfl) ⟨737114, by rfl⟩ : syracuseStep 982819 = 1474229) B1474229
theorem B982835 : Blo 980594 982835 := bstep (se 1 (by rfl) ⟨737126, by rfl⟩ : syracuseStep 982835 = 1474253) B1474253
theorem B1474355 : Blo 980594 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B982851 : Blo 980594 982851 := bstep (se 1 (by rfl) ⟨737138, by rfl⟩ : syracuseStep 982851 = 1474277) B1474277
theorem B1474385 : Blo 980594 1474385 := bstep (se 2 (by rfl) ⟨552894, by rfl⟩ : syracuseStep 1474385 = 1105789) B1105789
theorem B982867 : Blo 980594 982867 := bstep (se 1 (by rfl) ⟨737150, by rfl⟩ : syracuseStep 982867 = 1474301) B1474301
theorem B982883 : Blo 980594 982883 := bstep (se 1 (by rfl) ⟨737162, by rfl⟩ : syracuseStep 982883 = 1474325) B1474325
theorem B1474403 : Blo 980594 1474403 := bstep (se 1 (by rfl) ⟨1105802, by rfl⟩ : syracuseStep 1474403 = 2211605) B2211605
theorem B982899 : Blo 980594 982899 := bstep (se 1 (by rfl) ⟨737174, by rfl⟩ : syracuseStep 982899 = 1474349) B1474349
theorem B1474433 : Blo 980594 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B982915 : Blo 980594 982915 := bstep (se 1 (by rfl) ⟨737186, by rfl⟩ : syracuseStep 982915 = 1474373) B1474373
theorem B982931 : Blo 980594 982931 := bstep (se 1 (by rfl) ⟨737198, by rfl⟩ : syracuseStep 982931 = 1474397) B1474397
theorem B1474451 : Blo 980594 1474451 := bstep (se 1 (by rfl) ⟨1105838, by rfl⟩ : syracuseStep 1474451 = 2211677) B2211677
theorem B982947 : Blo 980594 982947 := bstep (se 1 (by rfl) ⟨737210, by rfl⟩ : syracuseStep 982947 = 1474421) B1474421
theorem B1474481 : Blo 980594 1474481 := bstep (se 2 (by rfl) ⟨552930, by rfl⟩ : syracuseStep 1474481 = 1105861) B1105861
theorem B982963 : Blo 980594 982963 := bstep (se 1 (by rfl) ⟨737222, by rfl⟩ : syracuseStep 982963 = 1474445) B1474445
theorem B982979 : Blo 980594 982979 := bstep (se 1 (by rfl) ⟨737234, by rfl⟩ : syracuseStep 982979 = 1474469) B1474469
theorem B1474499 : Blo 980594 1474499 := bstep (se 1 (by rfl) ⟨1105874, by rfl⟩ : syracuseStep 1474499 = 2211749) B2211749
theorem B6913997 : Blo 980594 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B982995 : Blo 980594 982995 := bstep (se 1 (by rfl) ⟨737246, by rfl⟩ : syracuseStep 982995 = 1474493) B1474493
theorem B1474529 : Blo 980594 1474529 := bstep (se 2 (by rfl) ⟨552948, by rfl⟩ : syracuseStep 1474529 = 1105897) B1105897
theorem B983011 : Blo 980594 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B983027 : Blo 980594 983027 := bstep (se 1 (by rfl) ⟨737270, by rfl⟩ : syracuseStep 983027 = 1474541) B1474541
theorem B1474547 : Blo 980594 1474547 := bstep (se 1 (by rfl) ⟨1105910, by rfl⟩ : syracuseStep 1474547 = 2211821) B2211821
theorem B1474571 : Blo 980594 1474571 := bstep (se 1 (by rfl) ⟨1105928, by rfl⟩ : syracuseStep 1474571 = 2211857) B2211857
theorem B983051 : Blo 980594 983051 := bstep (se 1 (by rfl) ⟨737288, by rfl⟩ : syracuseStep 983051 = 1474577) B1474577
theorem B1474583 : Blo 980594 1474583 := bstep (se 1 (by rfl) ⟨1105937, by rfl⟩ : syracuseStep 1474583 = 2211875) B2211875
theorem B983063 : Blo 980594 983063 := bstep (se 1 (by rfl) ⟨737297, by rfl⟩ : syracuseStep 983063 = 1474595) B1474595
theorem B983083 : Blo 980594 983083 := bstep (se 1 (by rfl) ⟨737312, by rfl⟩ : syracuseStep 983083 = 1474625) B1474625
theorem B983095 : Blo 980594 983095 := bstep (se 1 (by rfl) ⟨737321, by rfl⟩ : syracuseStep 983095 = 1474643) B1474643
theorem B983115 : Blo 980594 983115 := bstep (se 1 (by rfl) ⟨737336, by rfl⟩ : syracuseStep 983115 = 1474673) B1474673
theorem B1048663 : Blo 980594 1048663 := bstep (se 1 (by rfl) ⟨786497, by rfl⟩ : syracuseStep 1048663 = 1572995) B1572995
theorem B983127 : Blo 980594 983127 := bstep (se 1 (by rfl) ⟨737345, by rfl⟩ : syracuseStep 983127 = 1474691) B1474691
theorem B1474649 : Blo 980594 1474649 := bstep (se 2 (by rfl) ⟨552993, by rfl⟩ : syracuseStep 1474649 = 1105987) B1105987
theorem B983147 : Blo 980594 983147 := bstep (se 1 (by rfl) ⟨737360, by rfl⟩ : syracuseStep 983147 = 1474721) B1474721
theorem B983159 : Blo 980594 983159 := bstep (se 1 (by rfl) ⟨737369, by rfl⟩ : syracuseStep 983159 = 1474739) B1474739
theorem B983179 : Blo 980594 983179 := bstep (se 1 (by rfl) ⟨737384, by rfl⟩ : syracuseStep 983179 = 1474769) B1474769
theorem B983191 : Blo 980594 983191 := bstep (se 1 (by rfl) ⟨737393, by rfl⟩ : syracuseStep 983191 = 1474787) B1474787
theorem B983211 : Blo 980594 983211 := bstep (se 1 (by rfl) ⟨737408, by rfl⟩ : syracuseStep 983211 = 1474817) B1474817
theorem B8388785 : Blo 980594 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B2490547 : Blo 980594 2490547 := bstep (se 1 (by rfl) ⟨1867910, by rfl⟩ : syracuseStep 2490547 = 3735821) B3735821
theorem B983223 : Blo 980594 983223 := bstep (se 1 (by rfl) ⟨737417, by rfl⟩ : syracuseStep 983223 = 1474835) B1474835
theorem B1474763 : Blo 980594 1474763 := bstep (se 1 (by rfl) ⟨1106072, by rfl⟩ : syracuseStep 1474763 = 2212145) B2212145
theorem B983243 : Blo 980594 983243 := bstep (se 1 (by rfl) ⟨737432, by rfl⟩ : syracuseStep 983243 = 1474865) B1474865
theorem B1474775 : Blo 980594 1474775 := bstep (se 1 (by rfl) ⟨1106081, by rfl⟩ : syracuseStep 1474775 = 2212163) B2212163
theorem B983255 : Blo 980594 983255 := bstep (se 1 (by rfl) ⟨737441, by rfl⟩ : syracuseStep 983255 = 1474883) B1474883
theorem B3145949 : Blo 980594 3145949 := bstep (se 3 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 3145949 = 1179731) B1179731
theorem B983275 : Blo 980594 983275 := bstep (se 1 (by rfl) ⟨737456, by rfl⟩ : syracuseStep 983275 = 1474913) B1474913
theorem B983287 : Blo 980594 983287 := bstep (se 1 (by rfl) ⟨737465, by rfl⟩ : syracuseStep 983287 = 1474931) B1474931
theorem B983307 : Blo 980594 983307 := bstep (se 1 (by rfl) ⟨737480, by rfl⟩ : syracuseStep 983307 = 1474961) B1474961
theorem B1245451 : Blo 980594 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B983319 : Blo 980594 983319 := bstep (se 1 (by rfl) ⟨737489, by rfl⟩ : syracuseStep 983319 = 1474979) B1474979
theorem B1474841 : Blo 980594 1474841 := bstep (se 2 (by rfl) ⟨553065, by rfl⟩ : syracuseStep 1474841 = 1106131) B1106131
theorem B983339 : Blo 980594 983339 := bstep (se 1 (by rfl) ⟨737504, by rfl⟩ : syracuseStep 983339 = 1475009) B1475009
theorem B3309875 : Blo 980594 3309875 := bstep (se 1 (by rfl) ⟨2482406, by rfl⟩ : syracuseStep 3309875 = 4964813) B4964813
theorem B983351 : Blo 980594 983351 := bstep (se 1 (by rfl) ⟨737513, by rfl⟩ : syracuseStep 983351 = 1475027) B1475027
theorem B2490689 : Blo 980594 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B983371 : Blo 980594 983371 := bstep (se 1 (by rfl) ⟨737528, by rfl⟩ : syracuseStep 983371 = 1475057) B1475057
theorem B983383 : Blo 980594 983383 := bstep (se 1 (by rfl) ⟨737537, by rfl⟩ : syracuseStep 983383 = 1475075) B1475075
theorem B983403 : Blo 980594 983403 := bstep (se 1 (by rfl) ⟨737552, by rfl⟩ : syracuseStep 983403 = 1475105) B1475105
theorem B983415 : Blo 980594 983415 := bstep (se 1 (by rfl) ⟨737561, by rfl⟩ : syracuseStep 983415 = 1475123) B1475123
theorem B1474955 : Blo 980594 1474955 := bstep (se 1 (by rfl) ⟨1106216, by rfl⟩ : syracuseStep 1474955 = 2212433) B2212433
theorem B983435 : Blo 980594 983435 := bstep (se 1 (by rfl) ⟨737576, by rfl⟩ : syracuseStep 983435 = 1475153) B1475153
theorem B1474967 : Blo 980594 1474967 := bstep (se 1 (by rfl) ⟨1106225, by rfl⟩ : syracuseStep 1474967 = 2212451) B2212451
theorem B983447 : Blo 980594 983447 := bstep (se 1 (by rfl) ⟨737585, by rfl⟩ : syracuseStep 983447 = 1475171) B1475171
theorem B983467 : Blo 980594 983467 := bstep (se 1 (by rfl) ⟨737600, by rfl⟩ : syracuseStep 983467 = 1475201) B1475201
theorem B983479 : Blo 980594 983479 := bstep (se 1 (by rfl) ⟨737609, by rfl⟩ : syracuseStep 983479 = 1475219) B1475219
theorem B983499 : Blo 980594 983499 := bstep (se 1 (by rfl) ⟨737624, by rfl⟩ : syracuseStep 983499 = 1475249) B1475249
theorem B983511 : Blo 980594 983511 := bstep (se 1 (by rfl) ⟨737633, by rfl⟩ : syracuseStep 983511 = 1475267) B1475267
theorem B1475033 : Blo 980594 1475033 := bstep (se 2 (by rfl) ⟨553137, by rfl⟩ : syracuseStep 1475033 = 1106275) B1106275
theorem B983531 : Blo 980594 983531 := bstep (se 1 (by rfl) ⟨737648, by rfl⟩ : syracuseStep 983531 = 1475297) B1475297
theorem B1868275 : Blo 980594 1868275 := bstep (se 1 (by rfl) ⟨1401206, by rfl⟩ : syracuseStep 1868275 = 2802413) B2802413
theorem B983543 : Blo 980594 983543 := bstep (se 1 (by rfl) ⟨737657, by rfl⟩ : syracuseStep 983543 = 1475315) B1475315
theorem B983563 : Blo 980594 983563 := bstep (se 1 (by rfl) ⟨737672, by rfl⟩ : syracuseStep 983563 = 1475345) B1475345
theorem B983575 : Blo 980594 983575 := bstep (se 1 (by rfl) ⟨737681, by rfl⟩ : syracuseStep 983575 = 1475363) B1475363
theorem B1245719 : Blo 980594 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B983595 : Blo 980594 983595 := bstep (se 1 (by rfl) ⟨737696, by rfl⟩ : syracuseStep 983595 = 1475393) B1475393
theorem B983607 : Blo 980594 983607 := bstep (se 1 (by rfl) ⟨737705, by rfl⟩ : syracuseStep 983607 = 1475411) B1475411
theorem B3310145 : Blo 980594 3310145 := bstep (se 2 (by rfl) ⟨1241304, by rfl⟩ : syracuseStep 3310145 = 2482609) B2482609
theorem B1475147 : Blo 980594 1475147 := bstep (se 1 (by rfl) ⟨1106360, by rfl⟩ : syracuseStep 1475147 = 2212721) B2212721
theorem B983627 : Blo 980594 983627 := bstep (se 1 (by rfl) ⟨737720, by rfl⟩ : syracuseStep 983627 = 1475441) B1475441
theorem B1475159 : Blo 980594 1475159 := bstep (se 1 (by rfl) ⟨1106369, by rfl⟩ : syracuseStep 1475159 = 2212739) B2212739
theorem B983639 : Blo 980594 983639 := bstep (se 1 (by rfl) ⟨737729, by rfl⟩ : syracuseStep 983639 = 1475459) B1475459
theorem B983659 : Blo 980594 983659 := bstep (se 1 (by rfl) ⟨737744, by rfl⟩ : syracuseStep 983659 = 1475489) B1475489
theorem B983671 : Blo 980594 983671 := bstep (se 1 (by rfl) ⟨737753, by rfl⟩ : syracuseStep 983671 = 1475507) B1475507
theorem B983691 : Blo 980594 983691 := bstep (se 1 (by rfl) ⟨737768, by rfl⟩ : syracuseStep 983691 = 1475537) B1475537
theorem B983703 : Blo 980594 983703 := bstep (se 1 (by rfl) ⟨737777, by rfl⟩ : syracuseStep 983703 = 1475555) B1475555
theorem B1475225 : Blo 980594 1475225 := bstep (se 2 (by rfl) ⟨553209, by rfl⟩ : syracuseStep 1475225 = 1106419) B1106419
theorem B983723 : Blo 980594 983723 := bstep (se 1 (by rfl) ⟨737792, by rfl⟩ : syracuseStep 983723 = 1475585) B1475585
theorem B983735 : Blo 980594 983735 := bstep (se 1 (by rfl) ⟨737801, by rfl⟩ : syracuseStep 983735 = 1475603) B1475603
theorem B983755 : Blo 980594 983755 := bstep (se 1 (by rfl) ⟨737816, by rfl⟩ : syracuseStep 983755 = 1475633) B1475633
theorem B983767 : Blo 980594 983767 := bstep (se 1 (by rfl) ⟨737825, by rfl⟩ : syracuseStep 983767 = 1475651) B1475651
theorem B1868503 : Blo 980594 1868503 := bstep (se 1 (by rfl) ⟨1401377, by rfl⟩ : syracuseStep 1868503 = 2802755) B2802755
theorem B983787 : Blo 980594 983787 := bstep (se 1 (by rfl) ⟨737840, by rfl⟩ : syracuseStep 983787 = 1475681) B1475681
theorem B103383793 : Blo 980594 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B983799 : Blo 980594 983799 := bstep (se 1 (by rfl) ⟨737849, by rfl⟩ : syracuseStep 983799 = 1475699) B1475699
theorem B1475339 : Blo 980594 1475339 := bstep (se 1 (by rfl) ⟨1106504, by rfl⟩ : syracuseStep 1475339 = 2213009) B2213009
theorem B983819 : Blo 980594 983819 := bstep (se 1 (by rfl) ⟨737864, by rfl⟩ : syracuseStep 983819 = 1475729) B1475729
theorem B1475351 : Blo 980594 1475351 := bstep (se 1 (by rfl) ⟨1106513, by rfl⟩ : syracuseStep 1475351 = 2213027) B2213027
theorem B983831 : Blo 980594 983831 := bstep (se 1 (by rfl) ⟨737873, by rfl⟩ : syracuseStep 983831 = 1475747) B1475747
theorem B983851 : Blo 980594 983851 := bstep (se 1 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 983851 = 1475777) B1475777
theorem B983863 : Blo 980594 983863 := bstep (se 1 (by rfl) ⟨737897, by rfl⟩ : syracuseStep 983863 = 1475795) B1475795
theorem B1868609 : Blo 980594 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B983883 : Blo 980594 983883 := bstep (se 1 (by rfl) ⟨737912, by rfl⟩ : syracuseStep 983883 = 1475825) B1475825
theorem B983895 : Blo 980594 983895 := bstep (se 1 (by rfl) ⟨737921, by rfl⟩ : syracuseStep 983895 = 1475843) B1475843
theorem B1475417 : Blo 980594 1475417 := bstep (se 2 (by rfl) ⟨553281, by rfl⟩ : syracuseStep 1475417 = 1106563) B1106563
theorem B983915 : Blo 980594 983915 := bstep (se 1 (by rfl) ⟨737936, by rfl⟩ : syracuseStep 983915 = 1475873) B1475873
theorem B983927 : Blo 980594 983927 := bstep (se 1 (by rfl) ⟨737945, by rfl⟩ : syracuseStep 983927 = 1475891) B1475891
theorem B1049483 : Blo 980594 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B983947 : Blo 980594 983947 := bstep (se 1 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 983947 = 1475921) B1475921
theorem B3539857 : Blo 980594 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B983959 : Blo 980594 983959 := bstep (se 1 (by rfl) ⟨737969, by rfl⟩ : syracuseStep 983959 = 1475939) B1475939
theorem B983979 : Blo 980594 983979 := bstep (se 1 (by rfl) ⟨737984, by rfl⟩ : syracuseStep 983979 = 1475969) B1475969
theorem B4719539 : Blo 980594 4719539 := bstep (se 1 (by rfl) ⟨3539654, by rfl⟩ : syracuseStep 4719539 = 7079309) B7079309
theorem B983991 : Blo 980594 983991 := bstep (se 1 (by rfl) ⟨737993, by rfl⟩ : syracuseStep 983991 = 1475987) B1475987
theorem B1475531 : Blo 980594 1475531 := bstep (se 1 (by rfl) ⟨1106648, by rfl⟩ : syracuseStep 1475531 = 2213297) B2213297
theorem B984011 : Blo 980594 984011 := bstep (se 1 (by rfl) ⟨738008, by rfl⟩ : syracuseStep 984011 = 1476017) B1476017
theorem B1475543 : Blo 980594 1475543 := bstep (se 1 (by rfl) ⟨1106657, by rfl⟩ : syracuseStep 1475543 = 2213315) B2213315
theorem B984023 : Blo 980594 984023 := bstep (se 1 (by rfl) ⟨738017, by rfl⟩ : syracuseStep 984023 = 1476035) B1476035
theorem B1868761 : Blo 980594 1868761 := bstep (se 2 (by rfl) ⟨700785, by rfl⟩ : syracuseStep 1868761 = 1401571) B1401571
theorem B984043 : Blo 980594 984043 := bstep (se 1 (by rfl) ⟨738032, by rfl⟩ : syracuseStep 984043 = 1476065) B1476065
theorem B984055 : Blo 980594 984055 := bstep (se 1 (by rfl) ⟨738041, by rfl⟩ : syracuseStep 984055 = 1476083) B1476083
theorem B984075 : Blo 980594 984075 := bstep (se 1 (by rfl) ⟨738056, by rfl⟩ : syracuseStep 984075 = 1476113) B1476113
theorem B984087 : Blo 980594 984087 := bstep (se 1 (by rfl) ⟨738065, by rfl⟩ : syracuseStep 984087 = 1476131) B1476131
theorem B1475609 : Blo 980594 1475609 := bstep (se 2 (by rfl) ⟨553353, by rfl⟩ : syracuseStep 1475609 = 1106707) B1106707
theorem B984107 : Blo 980594 984107 := bstep (se 1 (by rfl) ⟨738080, by rfl⟩ : syracuseStep 984107 = 1476161) B1476161
theorem B984119 : Blo 980594 984119 := bstep (se 1 (by rfl) ⟨738089, by rfl⟩ : syracuseStep 984119 = 1476179) B1476179
theorem B984139 : Blo 980594 984139 := bstep (se 1 (by rfl) ⟨738104, by rfl⟩ : syracuseStep 984139 = 1476209) B1476209
theorem B984151 : Blo 980594 984151 := bstep (se 1 (by rfl) ⟨738113, by rfl⟩ : syracuseStep 984151 = 1476227) B1476227
theorem B3310685 : Blo 980594 3310685 := bstep (se 3 (by rfl) ⟨620753, by rfl⟩ : syracuseStep 3310685 = 1241507) B1241507
theorem B984171 : Blo 980594 984171 := bstep (se 1 (by rfl) ⟨738128, by rfl⟩ : syracuseStep 984171 = 1476257) B1476257
theorem B984183 : Blo 980594 984183 := bstep (se 1 (by rfl) ⟨738137, by rfl⟩ : syracuseStep 984183 = 1476275) B1476275
theorem B1770635 : Blo 980594 1770635 := bstep (se 1 (by rfl) ⟨1327976, by rfl⟩ : syracuseStep 1770635 = 2655953) B2655953
theorem B1475723 : Blo 980594 1475723 := bstep (se 1 (by rfl) ⟨1106792, by rfl⟩ : syracuseStep 1475723 = 2213585) B2213585
theorem B984203 : Blo 980594 984203 := bstep (se 1 (by rfl) ⟨738152, by rfl⟩ : syracuseStep 984203 = 1476305) B1476305
theorem B1475735 : Blo 980594 1475735 := bstep (se 1 (by rfl) ⟨1106801, by rfl⟩ : syracuseStep 1475735 = 2213603) B2213603
theorem B984215 : Blo 980594 984215 := bstep (se 1 (by rfl) ⟨738161, by rfl⟩ : syracuseStep 984215 = 1476323) B1476323
theorem B984235 : Blo 980594 984235 := bstep (se 1 (by rfl) ⟨738176, by rfl⟩ : syracuseStep 984235 = 1476353) B1476353
theorem B984247 : Blo 980594 984247 := bstep (se 1 (by rfl) ⟨738185, by rfl⟩ : syracuseStep 984247 = 1476371) B1476371
theorem B3540161 : Blo 980594 3540161 := bstep (se 2 (by rfl) ⟨1327560, by rfl⟩ : syracuseStep 3540161 = 2655121) B2655121
theorem B984267 : Blo 980594 984267 := bstep (se 1 (by rfl) ⟨738200, by rfl⟩ : syracuseStep 984267 = 1476401) B1476401
theorem B984279 : Blo 980594 984279 := bstep (se 1 (by rfl) ⟨738209, by rfl⟩ : syracuseStep 984279 = 1476419) B1476419
theorem B1475801 : Blo 980594 1475801 := bstep (se 2 (by rfl) ⟨553425, by rfl⟩ : syracuseStep 1475801 = 1106851) B1106851
theorem B3736793 : Blo 980594 3736793 := bstep (se 2 (by rfl) ⟨1401297, by rfl⟩ : syracuseStep 3736793 = 2802595) B2802595
theorem B984299 : Blo 980594 984299 := bstep (se 1 (by rfl) ⟨738224, by rfl⟩ : syracuseStep 984299 = 1476449) B1476449
theorem B984311 : Blo 980594 984311 := bstep (se 1 (by rfl) ⟨738233, by rfl⟩ : syracuseStep 984311 = 1476467) B1476467
theorem B984331 : Blo 980594 984331 := bstep (se 1 (by rfl) ⟨738248, by rfl⟩ : syracuseStep 984331 = 1476497) B1476497
theorem B984343 : Blo 980594 984343 := bstep (se 1 (by rfl) ⟨738257, by rfl⟩ : syracuseStep 984343 = 1476515) B1476515
theorem B984363 : Blo 980594 984363 := bstep (se 1 (by rfl) ⟨738272, by rfl⟩ : syracuseStep 984363 = 1476545) B1476545
theorem B3540275 : Blo 980594 3540275 := bstep (se 1 (by rfl) ⟨2655206, by rfl⟩ : syracuseStep 3540275 = 5310413) B5310413
theorem B984375 : Blo 980594 984375 := bstep (se 1 (by rfl) ⟨738281, by rfl⟩ : syracuseStep 984375 = 1476563) B1476563
theorem B1475915 : Blo 980594 1475915 := bstep (se 1 (by rfl) ⟨1106936, by rfl⟩ : syracuseStep 1475915 = 2213873) B2213873
theorem B984395 : Blo 980594 984395 := bstep (se 1 (by rfl) ⟨738296, by rfl⟩ : syracuseStep 984395 = 1476593) B1476593
theorem B1475927 : Blo 980594 1475927 := bstep (se 1 (by rfl) ⟨1106945, by rfl⟩ : syracuseStep 1475927 = 2213891) B2213891
theorem B984407 : Blo 980594 984407 := bstep (se 1 (by rfl) ⟨738305, by rfl⟩ : syracuseStep 984407 = 1476611) B1476611
theorem B984427 : Blo 980594 984427 := bstep (se 1 (by rfl) ⟨738320, by rfl⟩ : syracuseStep 984427 = 1476641) B1476641
theorem B984439 : Blo 980594 984439 := bstep (se 1 (by rfl) ⟨738329, by rfl⟩ : syracuseStep 984439 = 1476659) B1476659
theorem B4982147 : Blo 980594 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B984459 : Blo 980594 984459 := bstep (se 1 (by rfl) ⟨738344, by rfl⟩ : syracuseStep 984459 = 1476689) B1476689
theorem B984471 : Blo 980594 984471 := bstep (se 1 (by rfl) ⟨738353, by rfl⟩ : syracuseStep 984471 = 1476707) B1476707
theorem B1475993 : Blo 980594 1475993 := bstep (se 2 (by rfl) ⟨553497, by rfl⟩ : syracuseStep 1475993 = 1106995) B1106995
theorem B984491 : Blo 980594 984491 := bstep (se 1 (by rfl) ⟨738368, by rfl⟩ : syracuseStep 984491 = 1476737) B1476737
theorem B984503 : Blo 980594 984503 := bstep (se 1 (by rfl) ⟨738377, by rfl⟩ : syracuseStep 984503 = 1476755) B1476755
theorem B984523 : Blo 980594 984523 := bstep (se 1 (by rfl) ⟨738392, by rfl⟩ : syracuseStep 984523 = 1476785) B1476785
theorem B984535 : Blo 980594 984535 := bstep (se 1 (by rfl) ⟨738401, by rfl⟩ : syracuseStep 984535 = 1476803) B1476803
theorem B2098649 : Blo 980594 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B984555 : Blo 980594 984555 := bstep (se 1 (by rfl) ⟨738416, by rfl⟩ : syracuseStep 984555 = 1476833) B1476833
theorem B984567 : Blo 980594 984567 := bstep (se 1 (by rfl) ⟨738425, by rfl⟩ : syracuseStep 984567 = 1476851) B1476851
theorem B1476107 : Blo 980594 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B984587 : Blo 980594 984587 := bstep (se 1 (by rfl) ⟨738440, by rfl⟩ : syracuseStep 984587 = 1476881) B1476881
theorem B1476119 : Blo 980594 1476119 := bstep (se 1 (by rfl) ⟨1107089, by rfl⟩ : syracuseStep 1476119 = 2214179) B2214179
theorem B2491955 : Blo 980594 2491955 := bstep (se 1 (by rfl) ⟨1868966, by rfl⟩ : syracuseStep 2491955 = 3737933) B3737933
theorem B1476185 : Blo 980594 1476185 := bstep (se 2 (by rfl) ⟨553569, by rfl⟩ : syracuseStep 1476185 = 1107139) B1107139
theorem B4196033 : Blo 980594 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B1476299 : Blo 980594 1476299 := bstep (se 1 (by rfl) ⟨1107224, by rfl⟩ : syracuseStep 1476299 = 2214449) B2214449
theorem B1574615 : Blo 980594 1574615 := bstep (se 1 (by rfl) ⟨1180961, by rfl⟩ : syracuseStep 1574615 = 2361923) B2361923
theorem B1476311 : Blo 980594 1476311 := bstep (se 1 (by rfl) ⟨1107233, by rfl⟩ : syracuseStep 1476311 = 2214467) B2214467
theorem B1476377 : Blo 980594 1476377 := bstep (se 2 (by rfl) ⟨553641, by rfl⟩ : syracuseStep 1476377 = 1107283) B1107283
theorem B1574743 : Blo 980594 1574743 := bstep (se 1 (by rfl) ⟨1181057, by rfl⟩ : syracuseStep 1574743 = 2362115) B2362115
theorem B1476491 : Blo 980594 1476491 := bstep (se 1 (by rfl) ⟨1107368, by rfl⟩ : syracuseStep 1476491 = 2214737) B2214737
theorem B1574807 : Blo 980594 1574807 := bstep (se 1 (by rfl) ⟨1181105, by rfl⟩ : syracuseStep 1574807 = 2362211) B2362211
theorem B1476503 : Blo 980594 1476503 := bstep (se 1 (by rfl) ⟨1107377, by rfl⟩ : syracuseStep 1476503 = 2214755) B2214755
theorem B2983859 : Blo 980594 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B7079885 : Blo 980594 7079885 := bstep (se 3 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 7079885 = 2654957) B2654957
theorem B1476569 : Blo 980594 1476569 := bstep (se 2 (by rfl) ⟨553713, by rfl⟩ : syracuseStep 1476569 = 1107427) B1107427
theorem B3835907 : Blo 980594 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B1050679 : Blo 980594 1050679 := bstep (se 1 (by rfl) ⟨788009, by rfl⟩ : syracuseStep 1050679 = 1576019) B1576019
theorem B1476683 : Blo 980594 1476683 := bstep (se 1 (by rfl) ⟨1107512, by rfl⟩ : syracuseStep 1476683 = 2215025) B2215025
theorem B1476695 : Blo 980594 1476695 := bstep (se 1 (by rfl) ⟨1107521, by rfl⟩ : syracuseStep 1476695 = 2215043) B2215043
theorem B2099315 : Blo 980594 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B30214295 : Blo 980594 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B1476761 : Blo 980594 1476761 := bstep (se 2 (by rfl) ⟨553785, by rfl⟩ : syracuseStep 1476761 = 1107571) B1107571
theorem B3311819 : Blo 980594 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B1181899 : Blo 980594 1181899 := bstep (se 1 (by rfl) ⟨886424, by rfl⟩ : syracuseStep 1181899 = 1772849) B1772849
theorem B1476875 : Blo 980594 1476875 := bstep (se 1 (by rfl) ⟨1107656, by rfl⟩ : syracuseStep 1476875 = 2215313) B2215313
theorem B1476887 : Blo 980594 1476887 := bstep (se 1 (by rfl) ⟨1107665, by rfl⟩ : syracuseStep 1476887 = 2215331) B2215331
theorem B3312089 : Blo 980594 3312089 := bstep (se 2 (by rfl) ⟨1242033, by rfl⟩ : syracuseStep 3312089 = 2484067) B2484067
theorem B2362135 : Blo 980594 2362135 := bstep (se 1 (by rfl) ⟨1771601, by rfl⟩ : syracuseStep 2362135 = 3543203) B3543203
theorem B28379969 : Blo 980594 28379969 := bstep (se 2 (by rfl) ⟨10642488, by rfl⟩ : syracuseStep 28379969 = 21284977) B21284977
theorem B5049305 : Blo 980594 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B7474193 : Blo 980594 7474193 := bstep (se 2 (by rfl) ⟨2802822, by rfl⟩ : syracuseStep 7474193 = 5605645) B5605645
theorem B4197521 : Blo 980594 4197521 := bstep (se 2 (by rfl) ⟨1574070, by rfl⟩ : syracuseStep 4197521 = 3148141) B3148141
theorem B3312791 : Blo 980594 3312791 := bstep (se 1 (by rfl) ⟨2484593, by rfl⟩ : syracuseStep 3312791 = 4969187) B4969187
theorem B2100811 : Blo 980594 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B3313331 : Blo 980594 3313331 := bstep (se 1 (by rfl) ⟨2484998, by rfl⟩ : syracuseStep 3313331 = 4969997) B4969997
theorem B8392409 : Blo 980594 8392409 := bstep (se 2 (by rfl) ⟨3147153, by rfl⟩ : syracuseStep 8392409 = 6294307) B6294307
theorem B2658071 : Blo 980594 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B11210561 : Blo 980594 11210561 := bstep (se 2 (by rfl) ⟨4203960, by rfl⟩ : syracuseStep 11210561 = 8407921) B8407921
theorem B1576793 : Blo 980594 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B3313601 : Blo 980594 3313601 := bstep (se 2 (by rfl) ⟨1242600, by rfl⟩ : syracuseStep 3313601 = 2485201) B2485201
theorem B3543043 : Blo 980594 3543043 := bstep (se 1 (by rfl) ⟨2657282, by rfl⟩ : syracuseStep 3543043 = 5314565) B5314565
theorem B1347607 : Blo 980594 1347607 := bstep (se 1 (by rfl) ⟨1010705, by rfl⟩ : syracuseStep 1347607 = 2021411) B2021411
theorem B6557761 : Blo 980594 6557761 := bstep (se 2 (by rfl) ⟨2459160, by rfl⟩ : syracuseStep 6557761 = 4918321) B4918321
theorem B30642245 : Blo 980594 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B3543115 : Blo 980594 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B4198493 : Blo 980594 4198493 := bstep (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) B1574435
theorem B3314141 : Blo 980594 3314141 := bstep (se 3 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 3314141 = 1242803) B1242803
theorem B3543517 : Blo 980594 3543517 := bstep (se 3 (by rfl) ⟨664409, by rfl⟩ : syracuseStep 3543517 = 1328819) B1328819
theorem B20157133 : Blo 980594 20157133 := bstep (se 3 (by rfl) ⟨3779462, by rfl⟩ : syracuseStep 20157133 = 7558925) B7558925
theorem B57447139 : Blo 980594 57447139 := bstep (se 1 (by rfl) ⟨43085354, by rfl⟩ : syracuseStep 57447139 = 86170709) B86170709
theorem B21205745 : Blo 980594 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B2102041 : Blo 980594 2102041 := bstep (se 2 (by rfl) ⟨788265, by rfl⟩ : syracuseStep 2102041 = 1576531) B1576531
theorem B2986973 : Blo 980594 2986973 := bstep (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) B1120115
theorem B7574573 : Blo 980594 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B2364979 : Blo 980594 2364979 := bstep (se 1 (by rfl) ⟨1773734, by rfl⟩ : syracuseStep 2364979 = 3547469) B3547469
theorem B3315275 : Blo 980594 3315275 := bstep (se 1 (by rfl) ⟨2486456, by rfl⟩ : syracuseStep 3315275 = 4972913) B4972913
theorem B3315545 : Blo 980594 3315545 := bstep (se 2 (by rfl) ⟨1243329, by rfl⟩ : syracuseStep 3315545 = 2486659) B2486659
theorem B3774539 : Blo 980594 3774539 := bstep (se 1 (by rfl) ⟨2830904, by rfl⟩ : syracuseStep 3774539 = 5661809) B5661809
theorem B8395073 : Blo 980594 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B3545623 : Blo 980594 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B3316247 : Blo 980594 3316247 := bstep (se 1 (by rfl) ⟨2487185, by rfl⟩ : syracuseStep 3316247 = 4974371) B4974371
theorem B3545651 : Blo 980594 3545651 := bstep (se 1 (by rfl) ⟨2659238, by rfl⟩ : syracuseStep 3545651 = 5318477) B5318477
theorem B3152459 : Blo 980594 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B4201091 : Blo 980594 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B4201433 : Blo 980594 4201433 := bstep (se 2 (by rfl) ⟨1575537, by rfl⟩ : syracuseStep 4201433 = 3151075) B3151075
theorem B3152857 : Blo 980594 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B3316787 : Blo 980594 3316787 := bstep (se 1 (by rfl) ⟨2487590, by rfl⟩ : syracuseStep 3316787 = 4975181) B4975181
theorem B3317057 : Blo 980594 3317057 := bstep (se 2 (by rfl) ⟨1243896, by rfl⟩ : syracuseStep 3317057 = 2487793) B2487793
theorem B1121771 : Blo 980594 1121771 := bstep (se 1 (by rfl) ⟨841328, by rfl⟩ : syracuseStep 1121771 = 1682657) B1682657
theorem B1678859 : Blo 980594 1678859 := bstep (se 1 (by rfl) ⟨1259144, by rfl⟩ : syracuseStep 1678859 = 2518289) B2518289
theorem B6299153 : Blo 980594 6299153 := bstep (se 2 (by rfl) ⟨2362182, by rfl⟩ : syracuseStep 6299153 = 4724365) B4724365
theorem B1416971 : Blo 980594 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B3317597 : Blo 980594 3317597 := bstep (se 3 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 3317597 = 1244099) B1244099
theorem B2793437 : Blo 980594 2793437 := bstep (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) B1047539
theorem B3154099 : Blo 980594 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B2793665 : Blo 980594 2793665 := bstep (se 2 (by rfl) ⟨1047624, by rfl⟩ : syracuseStep 2793665 = 2095249) B2095249
theorem B4792621 : Blo 980594 4792621 := bstep (se 3 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 4792621 = 1797233) B1797233
theorem B45359473 : Blo 980594 45359473 := bstep (se 2 (by rfl) ⟨17009802, by rfl⟩ : syracuseStep 45359473 = 34019605) B34019605
theorem B2794007 : Blo 980594 2794007 := bstep (se 1 (by rfl) ⟨2095505, by rfl⟩ : syracuseStep 2794007 = 4191011) B4191011
theorem B3318731 : Blo 980594 3318731 := bstep (se 1 (by rfl) ⟨2489048, by rfl⟩ : syracuseStep 3318731 = 4978097) B4978097
theorem B3319001 : Blo 980594 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B2303257 : Blo 980594 2303257 := bstep (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) B1727443
theorem B8955485 : Blo 980594 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B1681049 : Blo 980594 1681049 := bstep (se 2 (by rfl) ⟨630393, by rfl⟩ : syracuseStep 1681049 = 1260787) B1260787
theorem B35923661 : Blo 980594 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B3319703 : Blo 980594 3319703 := bstep (se 1 (by rfl) ⟨2489777, by rfl⟩ : syracuseStep 3319703 = 4979555) B4979555
theorem B4204817 : Blo 980594 4204817 := bstep (se 2 (by rfl) ⟨1576806, by rfl⟩ : syracuseStep 4204817 = 3153613) B3153613
theorem B5974337 : Blo 980594 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B3320243 : Blo 980594 3320243 := bstep (se 1 (by rfl) ⟨2490182, by rfl⟩ : syracuseStep 3320243 = 4980365) B4980365
theorem B3320513 : Blo 980594 3320513 := bstep (se 2 (by rfl) ⟨1245192, by rfl⟩ : syracuseStep 3320513 = 2490385) B2490385
theorem B2206475 : Blo 980594 2206475 := bstep (se 1 (by rfl) ⟨1654856, by rfl⟩ : syracuseStep 2206475 = 3309713) B3309713
theorem B2206529 : Blo 980594 2206529 := bstep (se 2 (by rfl) ⟨827448, by rfl⟩ : syracuseStep 2206529 = 1654897) B1654897
theorem B2796353 : Blo 980594 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B994231 : Blo 980594 994231 := bstep (se 1 (by rfl) ⟨745673, by rfl⟩ : syracuseStep 994231 = 1491347) B1491347
theorem B4205533 : Blo 980594 4205533 := bstep (se 3 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 4205533 = 1577075) B1577075
theorem B2206745 : Blo 980594 2206745 := bstep (se 2 (by rfl) ⟨827529, by rfl⟩ : syracuseStep 2206745 = 1655059) B1655059
theorem B7973923 : Blo 980594 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B2206835 : Blo 980594 2206835 := bstep (se 1 (by rfl) ⟨1655126, by rfl⟩ : syracuseStep 2206835 = 3310253) B3310253
theorem B2206871 : Blo 980594 2206871 := bstep (se 1 (by rfl) ⟨1655153, by rfl⟩ : syracuseStep 2206871 = 3310307) B3310307
theorem B3321053 : Blo 980594 3321053 := bstep (se 3 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 3321053 = 1245395) B1245395
theorem B2207051 : Blo 980594 2207051 := bstep (se 1 (by rfl) ⟨1655288, by rfl⟩ : syracuseStep 2207051 = 3310577) B3310577
theorem B2796889 : Blo 980594 2796889 := bstep (se 2 (by rfl) ⟨1048833, by rfl⟩ : syracuseStep 2796889 = 2097667) B2097667
theorem B2207105 : Blo 980594 2207105 := bstep (se 2 (by rfl) ⟨827664, by rfl⟩ : syracuseStep 2207105 = 1655329) B1655329
theorem B2207321 : Blo 980594 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B2207411 : Blo 980594 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B2207447 : Blo 980594 2207447 := bstep (se 1 (by rfl) ⟨1655585, by rfl⟩ : syracuseStep 2207447 = 3311171) B3311171
theorem B2993885 : Blo 980594 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B2207627 : Blo 980594 2207627 := bstep (se 1 (by rfl) ⟨1655720, by rfl⟩ : syracuseStep 2207627 = 3311441) B3311441
theorem B2207681 : Blo 980594 2207681 := bstep (se 2 (by rfl) ⟨827880, by rfl⟩ : syracuseStep 2207681 = 1655761) B1655761
theorem B995447 : Blo 980594 995447 := bstep (se 1 (by rfl) ⟨746585, by rfl⟩ : syracuseStep 995447 = 1493171) B1493171
theorem B16822403 : Blo 980594 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B2207897 : Blo 980594 2207897 := bstep (se 2 (by rfl) ⟨827961, by rfl⟩ : syracuseStep 2207897 = 1655923) B1655923
theorem B4042955 : Blo 980594 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B2207987 : Blo 980594 2207987 := bstep (se 1 (by rfl) ⟨1655990, by rfl⟩ : syracuseStep 2207987 = 3311981) B3311981
theorem B8401157 : Blo 980594 8401157 := bstep (se 4 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 8401157 = 1575217) B1575217
theorem B2240779 : Blo 980594 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B2208023 : Blo 980594 2208023 := bstep (se 1 (by rfl) ⟨1656017, by rfl⟩ : syracuseStep 2208023 = 3312035) B3312035
theorem B3322187 : Blo 980594 3322187 := bstep (se 1 (by rfl) ⟨2491640, by rfl⟩ : syracuseStep 3322187 = 4983281) B4983281
theorem B2208203 : Blo 980594 2208203 := bstep (se 1 (by rfl) ⟨1656152, by rfl⟩ : syracuseStep 2208203 = 3312305) B3312305
theorem B2208257 : Blo 980594 2208257 := bstep (se 2 (by rfl) ⟨828096, by rfl⟩ : syracuseStep 2208257 = 1656193) B1656193
theorem B6304301 : Blo 980594 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B3322457 : Blo 980594 3322457 := bstep (se 2 (by rfl) ⟨1245921, by rfl⟩ : syracuseStep 3322457 = 2491843) B2491843
theorem B2208473 : Blo 980594 2208473 := bstep (se 2 (by rfl) ⟨828177, by rfl⟩ : syracuseStep 2208473 = 1656355) B1656355
theorem B15938309 : Blo 980594 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B2208563 : Blo 980594 2208563 := bstep (se 1 (by rfl) ⟨1656422, by rfl⟩ : syracuseStep 2208563 = 3312845) B3312845
theorem B2208599 : Blo 980594 2208599 := bstep (se 1 (by rfl) ⟨1656449, by rfl⟩ : syracuseStep 2208599 = 3312899) B3312899
theorem B2241433 : Blo 980594 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B2208779 : Blo 980594 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B2208833 : Blo 980594 2208833 := bstep (se 2 (by rfl) ⟨828312, by rfl⟩ : syracuseStep 2208833 = 1656625) B1656625
theorem B2798813 : Blo 980594 2798813 := bstep (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) B1049555
theorem B2209049 : Blo 980594 2209049 := bstep (se 2 (by rfl) ⟨828393, by rfl⟩ : syracuseStep 2209049 = 1656787) B1656787
theorem B2209139 : Blo 980594 2209139 := bstep (se 1 (by rfl) ⟨1656854, by rfl⟩ : syracuseStep 2209139 = 3313709) B3313709
theorem B2209175 : Blo 980594 2209175 := bstep (se 1 (by rfl) ⟨1656881, by rfl⟩ : syracuseStep 2209175 = 3313763) B3313763
theorem B3978803 : Blo 980594 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B2209355 : Blo 980594 2209355 := bstep (se 1 (by rfl) ⟨1657016, by rfl⟩ : syracuseStep 2209355 = 3314033) B3314033
theorem B996971 : Blo 980594 996971 := bstep (se 1 (by rfl) ⟨747728, by rfl⟩ : syracuseStep 996971 = 1495457) B1495457
theorem B2209409 : Blo 980594 2209409 := bstep (se 2 (by rfl) ⟨828528, by rfl⟩ : syracuseStep 2209409 = 1657057) B1657057
theorem B2209625 : Blo 980594 2209625 := bstep (se 2 (by rfl) ⟨828609, by rfl⟩ : syracuseStep 2209625 = 1657219) B1657219
theorem B2209715 : Blo 980594 2209715 := bstep (se 1 (by rfl) ⟨1657286, by rfl⟩ : syracuseStep 2209715 = 3314573) B3314573
theorem B2209751 : Blo 980594 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B3192797 : Blo 980594 3192797 := bstep (se 3 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 3192797 = 1197299) B1197299
theorem B2209931 : Blo 980594 2209931 := bstep (se 1 (by rfl) ⟨1657448, by rfl⟩ : syracuseStep 2209931 = 3314897) B3314897
theorem B2209985 : Blo 980594 2209985 := bstep (se 2 (by rfl) ⟨828744, by rfl⟩ : syracuseStep 2209985 = 1657489) B1657489
theorem B14530765 : Blo 980594 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B2210201 : Blo 980594 2210201 := bstep (se 2 (by rfl) ⟨828825, by rfl⟩ : syracuseStep 2210201 = 1657651) B1657651
theorem B1325527 : Blo 980594 1325527 := bstep (se 1 (by rfl) ⟨994145, by rfl⟩ : syracuseStep 1325527 = 1988291) B1988291
theorem B2210291 : Blo 980594 2210291 := bstep (se 1 (by rfl) ⟨1657718, by rfl⟩ : syracuseStep 2210291 = 3315437) B3315437
theorem B2210327 : Blo 980594 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B2210507 : Blo 980594 2210507 := bstep (se 1 (by rfl) ⟨1657880, by rfl⟩ : syracuseStep 2210507 = 3315761) B3315761
theorem B2210561 : Blo 980594 2210561 := bstep (se 2 (by rfl) ⟨828960, by rfl⟩ : syracuseStep 2210561 = 1657921) B1657921
theorem B2210777 : Blo 980594 2210777 := bstep (se 2 (by rfl) ⟨829041, by rfl⟩ : syracuseStep 2210777 = 1658083) B1658083
theorem B3587075 : Blo 980594 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B2210867 : Blo 980594 2210867 := bstep (se 1 (by rfl) ⟨1658150, by rfl⟩ : syracuseStep 2210867 = 3316301) B3316301
theorem B2210903 : Blo 980594 2210903 := bstep (se 1 (by rfl) ⟨1658177, by rfl⟩ : syracuseStep 2210903 = 3316355) B3316355
theorem B2211083 : Blo 980594 2211083 := bstep (se 1 (by rfl) ⟨1658312, by rfl⟩ : syracuseStep 2211083 = 3316625) B3316625
theorem B2211137 : Blo 980594 2211137 := bstep (se 2 (by rfl) ⟨829176, by rfl⟩ : syracuseStep 2211137 = 1658353) B1658353
theorem B2211353 : Blo 980594 2211353 := bstep (se 2 (by rfl) ⟨829257, by rfl⟩ : syracuseStep 2211353 = 1658515) B1658515
theorem B6307429 : Blo 980594 6307429 := bstep (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) B1182643
theorem B2211443 : Blo 980594 2211443 := bstep (se 1 (by rfl) ⟨1658582, by rfl⟩ : syracuseStep 2211443 = 3317165) B3317165
theorem B2211479 : Blo 980594 2211479 := bstep (se 1 (by rfl) ⟨1658609, by rfl⟩ : syracuseStep 2211479 = 3317219) B3317219
theorem B3587777 : Blo 980594 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B2211659 : Blo 980594 2211659 := bstep (se 1 (by rfl) ⟨1658744, by rfl⟩ : syracuseStep 2211659 = 3317489) B3317489
theorem B2211713 : Blo 980594 2211713 := bstep (se 2 (by rfl) ⟨829392, by rfl⟩ : syracuseStep 2211713 = 1658785) B1658785
theorem B2801729 : Blo 980594 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B37830725 : Blo 980594 37830725 := bstep (se 4 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 37830725 = 7093261) B7093261
theorem B2211929 : Blo 980594 2211929 := bstep (se 2 (by rfl) ⟨829473, by rfl⟩ : syracuseStep 2211929 = 1658947) B1658947
theorem B2801753 : Blo 980594 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B2212019 : Blo 980594 2212019 := bstep (se 1 (by rfl) ⟨1659014, by rfl⟩ : syracuseStep 2212019 = 3318029) B3318029
theorem B2212055 : Blo 980594 2212055 := bstep (se 1 (by rfl) ⟨1659041, by rfl⟩ : syracuseStep 2212055 = 3318083) B3318083
theorem B5587217 : Blo 980594 5587217 := bstep (se 2 (by rfl) ⟨2095206, by rfl⟩ : syracuseStep 5587217 = 4190413) B4190413
theorem B1327435 : Blo 980594 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B2212235 : Blo 980594 2212235 := bstep (se 1 (by rfl) ⟨1659176, by rfl⟩ : syracuseStep 2212235 = 3318353) B3318353
theorem B2212289 : Blo 980594 2212289 := bstep (se 2 (by rfl) ⟨829608, by rfl⟩ : syracuseStep 2212289 = 1659217) B1659217
theorem B1655255 : Blo 980594 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B163627573 : Blo 980594 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B1655383 : Blo 980594 1655383 := bstep (se 1 (by rfl) ⟨1241537, by rfl⟩ : syracuseStep 1655383 = 2483075) B2483075
theorem B2212505 : Blo 980594 2212505 := bstep (se 2 (by rfl) ⟨829689, by rfl⟩ : syracuseStep 2212505 = 1659379) B1659379
theorem B2212595 : Blo 980594 2212595 := bstep (se 1 (by rfl) ⟨1659446, by rfl⟩ : syracuseStep 2212595 = 3318893) B3318893
theorem B4965137 : Blo 980594 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B2212631 : Blo 980594 2212631 := bstep (se 1 (by rfl) ⟨1659473, by rfl⟩ : syracuseStep 2212631 = 3318947) B3318947
theorem B4539187 : Blo 980594 4539187 := bstep (se 1 (by rfl) ⟨3404390, by rfl⟩ : syracuseStep 4539187 = 6808781) B6808781
theorem B4965299 : Blo 980594 4965299 := bstep (se 1 (by rfl) ⟨3723974, by rfl⟩ : syracuseStep 4965299 = 7447949) B7447949
theorem B2212811 : Blo 980594 2212811 := bstep (se 1 (by rfl) ⟨1659608, by rfl⟩ : syracuseStep 2212811 = 3319217) B3319217
theorem B2212865 : Blo 980594 2212865 := bstep (se 2 (by rfl) ⟨829824, by rfl⟩ : syracuseStep 2212865 = 1659649) B1659649
theorem B1656011 : Blo 980594 1656011 := bstep (se 1 (by rfl) ⟨1242008, by rfl⟩ : syracuseStep 1656011 = 2484017) B2484017
theorem B2213081 : Blo 980594 2213081 := bstep (se 2 (by rfl) ⟨829905, by rfl⟩ : syracuseStep 2213081 = 1659811) B1659811
theorem B2213171 : Blo 980594 2213171 := bstep (se 1 (by rfl) ⟨1659878, by rfl⟩ : syracuseStep 2213171 = 3319757) B3319757
theorem B2802995 : Blo 980594 2802995 := bstep (se 1 (by rfl) ⟨2102246, by rfl⟩ : syracuseStep 2802995 = 4204493) B4204493
theorem B1656139 : Blo 980594 1656139 := bstep (se 1 (by rfl) ⟨1242104, by rfl⟩ : syracuseStep 1656139 = 2484209) B2484209
theorem B2213207 : Blo 980594 2213207 := bstep (se 1 (by rfl) ⟨1659905, by rfl⟩ : syracuseStep 2213207 = 3319811) B3319811
theorem B3786115 : Blo 980594 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B9586097 : Blo 980594 9586097 := bstep (se 2 (by rfl) ⟨3594786, by rfl⟩ : syracuseStep 9586097 = 7189573) B7189573
theorem B1328599 : Blo 980594 1328599 := bstep (se 1 (by rfl) ⟨996449, by rfl⟩ : syracuseStep 1328599 = 1992899) B1992899
theorem B1656281 : Blo 980594 1656281 := bstep (se 2 (by rfl) ⟨621105, by rfl⟩ : syracuseStep 1656281 = 1242211) B1242211
theorem B2213387 : Blo 980594 2213387 := bstep (se 1 (by rfl) ⟨1660040, by rfl⟩ : syracuseStep 2213387 = 3320081) B3320081
theorem B2213441 : Blo 980594 2213441 := bstep (se 2 (by rfl) ⟨830040, by rfl⟩ : syracuseStep 2213441 = 1660081) B1660081
theorem B1656409 : Blo 980594 1656409 := bstep (se 2 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 1656409 = 1242307) B1242307
theorem B2213657 : Blo 980594 2213657 := bstep (se 2 (by rfl) ⟨830121, by rfl⟩ : syracuseStep 2213657 = 1660243) B1660243
theorem B2213747 : Blo 980594 2213747 := bstep (se 1 (by rfl) ⟨1660310, by rfl⟩ : syracuseStep 2213747 = 3320621) B3320621
theorem B2213783 : Blo 980594 2213783 := bstep (se 1 (by rfl) ⟨1660337, by rfl⟩ : syracuseStep 2213783 = 3320675) B3320675
theorem B2213963 : Blo 980594 2213963 := bstep (se 1 (by rfl) ⟨1660472, by rfl⟩ : syracuseStep 2213963 = 3320945) B3320945
theorem B2214017 : Blo 980594 2214017 := bstep (se 2 (by rfl) ⟨830256, by rfl⟩ : syracuseStep 2214017 = 1660513) B1660513
theorem B1656983 : Blo 980594 1656983 := bstep (se 1 (by rfl) ⟨1242737, by rfl⟩ : syracuseStep 1656983 = 2485475) B2485475
theorem B1657111 : Blo 980594 1657111 := bstep (se 1 (by rfl) ⟨1242833, by rfl⟩ : syracuseStep 1657111 = 2485667) B2485667
theorem B2214233 : Blo 980594 2214233 := bstep (se 2 (by rfl) ⟨830337, by rfl⟩ : syracuseStep 2214233 = 1660675) B1660675
theorem B2214323 : Blo 980594 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B2214359 : Blo 980594 2214359 := bstep (se 1 (by rfl) ⟨1660769, by rfl⟩ : syracuseStep 2214359 = 3321539) B3321539
theorem B2214539 : Blo 980594 2214539 := bstep (se 1 (by rfl) ⟨1660904, by rfl⟩ : syracuseStep 2214539 = 3321809) B3321809
theorem B2214593 : Blo 980594 2214593 := bstep (se 2 (by rfl) ⟨830472, by rfl⟩ : syracuseStep 2214593 = 1660945) B1660945
theorem B4967243 : Blo 980594 4967243 := bstep (se 1 (by rfl) ⟨3725432, by rfl⟩ : syracuseStep 4967243 = 7450865) B7450865
theorem B1657739 : Blo 980594 1657739 := bstep (se 1 (by rfl) ⟨1243304, by rfl⟩ : syracuseStep 1657739 = 2486609) B2486609
theorem B2214809 : Blo 980594 2214809 := bstep (se 2 (by rfl) ⟨830553, by rfl⟩ : syracuseStep 2214809 = 1661107) B1661107
theorem B2214899 : Blo 980594 2214899 := bstep (se 1 (by rfl) ⟨1661174, by rfl⟩ : syracuseStep 2214899 = 3322349) B3322349
theorem B1657867 : Blo 980594 1657867 := bstep (se 1 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 1657867 = 2486801) B2486801
theorem B2214935 : Blo 980594 2214935 := bstep (se 1 (by rfl) ⟨1661201, by rfl⟩ : syracuseStep 2214935 = 3322403) B3322403
theorem B1592345 : Blo 980594 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B8408195 : Blo 980594 8408195 := bstep (se 1 (by rfl) ⟨6306146, by rfl⟩ : syracuseStep 8408195 = 12612293) B12612293
theorem B1658009 : Blo 980594 1658009 := bstep (se 2 (by rfl) ⟨621753, by rfl⟩ : syracuseStep 1658009 = 1243507) B1243507
theorem B2215115 : Blo 980594 2215115 := bstep (se 1 (by rfl) ⟨1661336, by rfl⟩ : syracuseStep 2215115 = 3322673) B3322673
theorem B2215169 : Blo 980594 2215169 := bstep (se 2 (by rfl) ⟨830688, by rfl⟩ : syracuseStep 2215169 = 1661377) B1661377
theorem B1658137 : Blo 980594 1658137 := bstep (se 2 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 1658137 = 1243603) B1243603
theorem B3788333 : Blo 980594 3788333 := bstep (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) B1420625
theorem B1658711 : Blo 980594 1658711 := bstep (se 1 (by rfl) ⟨1244033, by rfl⟩ : syracuseStep 1658711 = 2488067) B2488067
theorem B1658839 : Blo 980594 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B1396759 : Blo 980594 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B13455395 : Blo 980594 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B3723353 : Blo 980594 3723353 := bstep (se 2 (by rfl) ⟨1396257, by rfl⟩ : syracuseStep 3723353 = 2792515) B2792515
theorem B3363137 : Blo 980594 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B3723671 : Blo 980594 3723671 := bstep (se 1 (by rfl) ⟨2792753, by rfl⟩ : syracuseStep 3723671 = 5585507) B5585507
theorem B4969025 : Blo 980594 4969025 := bstep (se 2 (by rfl) ⟨1863384, by rfl⟩ : syracuseStep 4969025 = 3726769) B3726769
theorem B1659467 : Blo 980594 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B1659595 : Blo 980594 1659595 := bstep (se 1 (by rfl) ⟨1244696, by rfl⟩ : syracuseStep 1659595 = 2489393) B2489393
theorem B12112685 : Blo 980594 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B1659737 : Blo 980594 1659737 := bstep (se 2 (by rfl) ⟨622401, by rfl⟩ : syracuseStep 1659737 = 1244803) B1244803
theorem B1659865 : Blo 980594 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B1365017 : Blo 980594 1365017 := bstep (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) B1023763
theorem B3724339 : Blo 980594 3724339 := bstep (se 1 (by rfl) ⟨2793254, by rfl⟩ : syracuseStep 3724339 = 5586509) B5586509
theorem B8508509 : Blo 980594 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B4478125 : Blo 980594 4478125 := bstep (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) B1679297
theorem B1496279 : Blo 980594 1496279 := bstep (se 1 (by rfl) ⟨1122209, by rfl⟩ : syracuseStep 1496279 = 2244419) B2244419
theorem B4609331 : Blo 980594 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B1103179 : Blo 980594 1103179 := bstep (se 1 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 1103179 = 1654769) B1654769
theorem B3986833 : Blo 980594 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B1103287 : Blo 980594 1103287 := bstep (se 1 (by rfl) ⟨827465, by rfl⟩ : syracuseStep 1103287 = 1654931) B1654931
theorem B1660439 : Blo 980594 1660439 := bstep (se 1 (by rfl) ⟨1245329, by rfl⟩ : syracuseStep 1660439 = 2490659) B2490659
theorem B1103467 : Blo 980594 1103467 := bstep (se 1 (by rfl) ⟨827600, by rfl⟩ : syracuseStep 1103467 = 1655201) B1655201
theorem B21223043 : Blo 980594 21223043 := bstep (se 1 (by rfl) ⟨15917282, by rfl⟩ : syracuseStep 21223043 = 31834565) B31834565
theorem B1660567 : Blo 980594 1660567 := bstep (se 1 (by rfl) ⟨1245425, by rfl⟩ : syracuseStep 1660567 = 2490851) B2490851
theorem B1103575 : Blo 980594 1103575 := bstep (se 1 (by rfl) ⟨827681, by rfl⟩ : syracuseStep 1103575 = 1655363) B1655363
theorem B1103755 : Blo 980594 1103755 := bstep (se 1 (by rfl) ⟨827816, by rfl⟩ : syracuseStep 1103755 = 1655633) B1655633
theorem B5593049 : Blo 980594 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B1103863 : Blo 980594 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B1398809 : Blo 980594 1398809 := bstep (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) B1049107
theorem B1104043 : Blo 980594 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B1661195 : Blo 980594 1661195 := bstep (se 1 (by rfl) ⟨1245896, by rfl⟩ : syracuseStep 1661195 = 2491793) B2491793
theorem B3725585 : Blo 980594 3725585 := bstep (se 2 (by rfl) ⟨1397094, by rfl⟩ : syracuseStep 3725585 = 2794189) B2794189
theorem B1104151 : Blo 980594 1104151 := bstep (se 1 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 1104151 = 1656227) B1656227
theorem B1661323 : Blo 980594 1661323 := bstep (se 1 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 1661323 = 2491985) B2491985
theorem B1104331 : Blo 980594 1104331 := bstep (se 1 (by rfl) ⟨828248, by rfl⟩ : syracuseStep 1104331 = 1656497) B1656497
theorem B4970969 : Blo 980594 4970969 := bstep (se 2 (by rfl) ⟨1864113, by rfl⟩ : syracuseStep 4970969 = 3728227) B3728227
theorem B1661465 : Blo 980594 1661465 := bstep (se 2 (by rfl) ⟨623049, by rfl⟩ : syracuseStep 1661465 = 1246099) B1246099
theorem B1104439 : Blo 980594 1104439 := bstep (se 1 (by rfl) ⟨828329, by rfl⟩ : syracuseStep 1104439 = 1656659) B1656659
theorem B1399447 : Blo 980594 1399447 := bstep (se 1 (by rfl) ⟨1049585, by rfl⟩ : syracuseStep 1399447 = 2099171) B2099171
theorem B1104619 : Blo 980594 1104619 := bstep (se 1 (by rfl) ⟨828464, by rfl⟩ : syracuseStep 1104619 = 1656929) B1656929
theorem B1104727 : Blo 980594 1104727 := bstep (se 1 (by rfl) ⟨828545, by rfl⟩ : syracuseStep 1104727 = 1657091) B1657091
theorem B8379287 : Blo 980594 8379287 := bstep (se 1 (by rfl) ⟨6284465, by rfl⟩ : syracuseStep 8379287 = 12568931) B12568931
theorem B3726283 : Blo 980594 3726283 := bstep (se 1 (by rfl) ⟨2794712, by rfl⟩ : syracuseStep 3726283 = 5589425) B5589425
theorem B1104907 : Blo 980594 1104907 := bstep (se 1 (by rfl) ⟨828680, by rfl⟩ : syracuseStep 1104907 = 1657361) B1657361
theorem B1105015 : Blo 980594 1105015 := bstep (se 1 (by rfl) ⟨828761, by rfl⟩ : syracuseStep 1105015 = 1657523) B1657523
theorem B2841803 : Blo 980594 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B3726557 : Blo 980594 3726557 := bstep (se 3 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 3726557 = 1397459) B1397459
theorem B1105195 : Blo 980594 1105195 := bstep (se 1 (by rfl) ⟨828896, by rfl⟩ : syracuseStep 1105195 = 1657793) B1657793
theorem B1990003 : Blo 980594 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B1105303 : Blo 980594 1105303 := bstep (se 1 (by rfl) ⟨828977, by rfl⟩ : syracuseStep 1105303 = 1657955) B1657955
theorem B1400267 : Blo 980594 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B1105483 : Blo 980594 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B5987915 : Blo 980594 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B1105591 : Blo 980594 1105591 := bstep (se 1 (by rfl) ⟨829193, by rfl⟩ : syracuseStep 1105591 = 1658387) B1658387
theorem B1105771 : Blo 980594 1105771 := bstep (se 1 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 1105771 = 1658657) B1658657
theorem B12115829 : Blo 980594 12115829 := bstep (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) B1135859
theorem B3727255 : Blo 980594 3727255 := bstep (se 1 (by rfl) ⟨2795441, by rfl⟩ : syracuseStep 3727255 = 5590883) B5590883
theorem B9461681 : Blo 980594 9461681 := bstep (se 2 (by rfl) ⟨3548130, by rfl⟩ : syracuseStep 9461681 = 7096261) B7096261
theorem B1105879 : Blo 980594 1105879 := bstep (se 1 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 1105879 = 1658819) B1658819
theorem B4972589 : Blo 980594 4972589 := bstep (se 3 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 4972589 = 1864721) B1864721
theorem B2482265 : Blo 980594 2482265 := bstep (se 2 (by rfl) ⟨930849, by rfl⟩ : syracuseStep 2482265 = 1861699) B1861699
theorem B1106059 : Blo 980594 1106059 := bstep (se 1 (by rfl) ⟨829544, by rfl⟩ : syracuseStep 1106059 = 1659089) B1659089
theorem B1106167 : Blo 980594 1106167 := bstep (se 1 (by rfl) ⟨829625, by rfl⟩ : syracuseStep 1106167 = 1659251) B1659251
theorem B1892659 : Blo 980594 1892659 := bstep (se 1 (by rfl) ⟨1419494, by rfl⟩ : syracuseStep 1892659 = 2838989) B2838989
theorem B1401241 : Blo 980594 1401241 := bstep (se 2 (by rfl) ⟨525465, by rfl⟩ : syracuseStep 1401241 = 1050931) B1050931
theorem B1106347 : Blo 980594 1106347 := bstep (se 1 (by rfl) ⟨829760, by rfl⟩ : syracuseStep 1106347 = 1659521) B1659521
theorem B11198897 : Blo 980594 11198897 := bstep (se 2 (by rfl) ⟨4199586, by rfl⟩ : syracuseStep 11198897 = 8399173) B8399173
theorem B1106455 : Blo 980594 1106455 := bstep (se 1 (by rfl) ⟨829841, by rfl⟩ : syracuseStep 1106455 = 1659683) B1659683
theorem B5595713 : Blo 980594 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B6709853 : Blo 980594 6709853 := bstep (se 3 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 6709853 = 2516195) B2516195
theorem B3728045 : Blo 980594 3728045 := bstep (se 3 (by rfl) ⟨699008, by rfl⟩ : syracuseStep 3728045 = 1398017) B1398017
theorem B1991347 : Blo 980594 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B1106635 : Blo 980594 1106635 := bstep (se 1 (by rfl) ⟨829976, by rfl⟩ : syracuseStep 1106635 = 1659953) B1659953
theorem B1106743 : Blo 980594 1106743 := bstep (se 1 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 1106743 = 1660115) B1660115
theorem B2483095 : Blo 980594 2483095 := bstep (se 1 (by rfl) ⟨1862321, by rfl⟩ : syracuseStep 2483095 = 3724643) B3724643
theorem B1106923 : Blo 980594 1106923 := bstep (se 1 (by rfl) ⟨830192, by rfl⟩ : syracuseStep 1106923 = 1660385) B1660385
theorem B1107031 : Blo 980594 1107031 := bstep (se 1 (by rfl) ⟨830273, by rfl⟩ : syracuseStep 1107031 = 1660547) B1660547
theorem B1107211 : Blo 980594 1107211 := bstep (se 1 (by rfl) ⟨830408, by rfl⟩ : syracuseStep 1107211 = 1660817) B1660817
theorem B2483531 : Blo 980594 2483531 := bstep (se 1 (by rfl) ⟨1862648, by rfl⟩ : syracuseStep 2483531 = 3725297) B3725297
theorem B1107319 : Blo 980594 1107319 := bstep (se 1 (by rfl) ⟨830489, by rfl⟩ : syracuseStep 1107319 = 1660979) B1660979
theorem B1107499 : Blo 980594 1107499 := bstep (se 1 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 1107499 = 1661249) B1661249
theorem B1107607 : Blo 980594 1107607 := bstep (se 1 (by rfl) ⟨830705, by rfl⟩ : syracuseStep 1107607 = 1661411) B1661411
theorem B2483905 : Blo 980594 2483905 := bstep (se 2 (by rfl) ⟨931464, by rfl⟩ : syracuseStep 2483905 = 1862929) B1862929
theorem B2123543 : Blo 980594 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B3729473 : Blo 980594 3729473 := bstep (se 2 (by rfl) ⟨1398552, by rfl⟩ : syracuseStep 3729473 = 2797105) B2797105
theorem B60418199 : Blo 980594 60418199 := bstep (se 1 (by rfl) ⟨45313649, by rfl⟩ : syracuseStep 60418199 = 90627299) B90627299
theorem B2484503 : Blo 980594 2484503 := bstep (se 1 (by rfl) ⟨1863377, by rfl⟩ : syracuseStep 2484503 = 3726755) B3726755
theorem B1862003 : Blo 980594 1862003 := bstep (se 1 (by rfl) ⟨1396502, by rfl⟩ : syracuseStep 1862003 = 2793005) B2793005
theorem B60615029 : Blo 980594 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B1862041 : Blo 980594 1862041 := bstep (se 2 (by rfl) ⟨698265, by rfl⟩ : syracuseStep 1862041 = 1396531) B1396531
theorem B2550361 : Blo 980594 2550361 := bstep (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) B1912771
theorem B1862489 : Blo 980594 1862489 := bstep (se 2 (by rfl) ⟨698433, by rfl⟩ : syracuseStep 1862489 = 1396867) B1396867
theorem B2485313 : Blo 980594 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B4779415 : Blo 980594 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B7466417 : Blo 980594 7466417 := bstep (se 2 (by rfl) ⟨2799906, by rfl⟩ : syracuseStep 7466417 = 5599813) B5599813
theorem B1797569 : Blo 980594 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B3730961 : Blo 980594 3730961 := bstep (se 2 (by rfl) ⟨1399110, by rfl⟩ : syracuseStep 3730961 = 2798221) B2798221
theorem B1863233 : Blo 980594 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B2485849 : Blo 980594 2485849 := bstep (se 2 (by rfl) ⟨932193, by rfl⟩ : syracuseStep 2485849 = 1864387) B1864387
theorem B4484753 : Blo 980594 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B1994519 : Blo 980594 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B1863499 : Blo 980594 1863499 := bstep (se 1 (by rfl) ⟨1397624, by rfl⟩ : syracuseStep 1863499 = 2795249) B2795249
theorem B4976477 : Blo 980594 4976477 := bstep (se 3 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 4976477 = 1866179) B1866179
theorem B7466903 : Blo 980594 7466903 := bstep (se 1 (by rfl) ⟨5600177, by rfl⟩ : syracuseStep 7466903 = 11200355) B11200355
theorem B3731417 : Blo 980594 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B1241239 : Blo 980594 1241239 := bstep (se 1 (by rfl) ⟨930929, by rfl⟩ : syracuseStep 1241239 = 1861859) B1861859
theorem B3731629 : Blo 980594 3731629 := bstep (se 3 (by rfl) ⟨699680, by rfl⟩ : syracuseStep 3731629 = 1399361) B1399361
theorem B4190429 : Blo 980594 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B12579077 : Blo 980594 12579077 := bstep (se 4 (by rfl) ⟨1179288, by rfl⟩ : syracuseStep 12579077 = 2358577) B2358577
theorem B1863947 : Blo 980594 1863947 := bstep (se 1 (by rfl) ⟨1397960, by rfl⟩ : syracuseStep 1863947 = 2795921) B2795921
theorem B1864129 : Blo 980594 1864129 := bstep (se 2 (by rfl) ⟨699048, by rfl⟩ : syracuseStep 1864129 = 1398097) B1398097
theorem B1470923 : Blo 980594 1470923 := bstep (se 1 (by rfl) ⟨1103192, by rfl⟩ : syracuseStep 1470923 = 2206385) B2206385
theorem B1470935 : Blo 980594 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B3731933 : Blo 980594 3731933 := bstep (se 3 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 3731933 = 1399475) B1399475
theorem B4190737 : Blo 980594 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B1471001 : Blo 980594 1471001 := bstep (se 2 (by rfl) ⟨551625, by rfl⟩ : syracuseStep 1471001 = 1103251) B1103251
theorem B4190771 : Blo 980594 4190771 := bstep (se 1 (by rfl) ⟨3143078, by rfl⟩ : syracuseStep 4190771 = 6286157) B6286157
theorem B1471115 : Blo 980594 1471115 := bstep (se 1 (by rfl) ⟨1103336, by rfl⟩ : syracuseStep 1471115 = 2206673) B2206673
theorem B1471127 : Blo 980594 1471127 := bstep (se 1 (by rfl) ⟨1103345, by rfl⟩ : syracuseStep 1471127 = 2206691) B2206691
theorem B2486963 : Blo 980594 2486963 := bstep (se 1 (by rfl) ⟨1865222, by rfl⟩ : syracuseStep 2486963 = 3730445) B3730445
theorem B1471193 : Blo 980594 1471193 := bstep (se 2 (by rfl) ⟨551697, by rfl⟩ : syracuseStep 1471193 = 1103395) B1103395
theorem B1864471 : Blo 980594 1864471 := bstep (se 1 (by rfl) ⟨1398353, by rfl⟩ : syracuseStep 1864471 = 2796707) B2796707
theorem B1078039 : Blo 980594 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B4715309 : Blo 980594 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B1471307 : Blo 980594 1471307 := bstep (se 1 (by rfl) ⟨1103480, by rfl⟩ : syracuseStep 1471307 = 2206961) B2206961
theorem B1471319 : Blo 980594 1471319 := bstep (se 1 (by rfl) ⟨1103489, by rfl⟩ : syracuseStep 1471319 = 2206979) B2206979
theorem B1471385 : Blo 980594 1471385 := bstep (se 2 (by rfl) ⟨551769, by rfl⟩ : syracuseStep 1471385 = 1103539) B1103539
theorem B2487257 : Blo 980594 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B1864691 : Blo 980594 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B2126849 : Blo 980594 2126849 := bstep (se 2 (by rfl) ⟨797568, by rfl⟩ : syracuseStep 2126849 = 1595137) B1595137
theorem B1471499 : Blo 980594 1471499 := bstep (se 1 (by rfl) ⟨1103624, by rfl⟩ : syracuseStep 1471499 = 2207249) B2207249
theorem B1471511 : Blo 980594 1471511 := bstep (se 1 (by rfl) ⟨1103633, by rfl⟩ : syracuseStep 1471511 = 2207267) B2207267
theorem B4256819 : Blo 980594 4256819 := bstep (se 1 (by rfl) ⟨3192614, by rfl⟩ : syracuseStep 4256819 = 6385229) B6385229
theorem B1471577 : Blo 980594 1471577 := bstep (se 2 (by rfl) ⟨551841, by rfl⟩ : syracuseStep 1471577 = 1103683) B1103683
theorem B6288515 : Blo 980594 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B1471691 : Blo 980594 1471691 := bstep (se 1 (by rfl) ⟨1103768, by rfl⟩ : syracuseStep 1471691 = 2207537) B2207537
theorem B1471703 : Blo 980594 1471703 := bstep (se 1 (by rfl) ⟨1103777, by rfl⟩ : syracuseStep 1471703 = 2207555) B2207555
theorem B1864919 : Blo 980594 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B1471769 : Blo 980594 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B1471883 : Blo 980594 1471883 := bstep (se 1 (by rfl) ⟨1103912, by rfl⟩ : syracuseStep 1471883 = 2207825) B2207825
theorem B1471895 : Blo 980594 1471895 := bstep (se 1 (by rfl) ⟨1103921, by rfl⟩ : syracuseStep 1471895 = 2207843) B2207843
theorem B3143129 : Blo 980594 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B1471961 : Blo 980594 1471961 := bstep (se 2 (by rfl) ⟨551985, by rfl⟩ : syracuseStep 1471961 = 1103971) B1103971
theorem B1865177 : Blo 980594 1865177 := bstep (se 2 (by rfl) ⟨699441, by rfl⟩ : syracuseStep 1865177 = 1398883) B1398883
theorem B1472075 : Blo 980594 1472075 := bstep (se 1 (by rfl) ⟨1104056, by rfl⟩ : syracuseStep 1472075 = 2208113) B2208113
theorem B1472087 : Blo 980594 1472087 := bstep (se 1 (by rfl) ⟨1104065, by rfl⟩ : syracuseStep 1472087 = 2208131) B2208131
theorem B980599 : Blo 980594 980599 := bstep (se 1 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 980599 = 1470899) B1470899
theorem B980619 : Blo 980594 980619 := bstep (se 1 (by rfl) ⟨735464, by rfl⟩ : syracuseStep 980619 = 1470929) B1470929
theorem B980631 : Blo 980594 980631 := bstep (se 1 (by rfl) ⟨735473, by rfl⟩ : syracuseStep 980631 = 1470947) B1470947
theorem B1472153 : Blo 980594 1472153 := bstep (se 2 (by rfl) ⟨552057, by rfl⟩ : syracuseStep 1472153 = 1104115) B1104115
theorem B980651 : Blo 980594 980651 := bstep (se 1 (by rfl) ⟨735488, by rfl⟩ : syracuseStep 980651 = 1470977) B1470977
theorem B980663 : Blo 980594 980663 := bstep (se 1 (by rfl) ⟨735497, by rfl⟩ : syracuseStep 980663 = 1470995) B1470995
theorem B980683 : Blo 980594 980683 := bstep (se 1 (by rfl) ⟨735512, by rfl⟩ : syracuseStep 980683 = 1471025) B1471025
theorem B980695 : Blo 980594 980695 := bstep (se 1 (by rfl) ⟨735521, by rfl⟩ : syracuseStep 980695 = 1471043) B1471043
theorem B980715 : Blo 980594 980715 := bstep (se 1 (by rfl) ⟨735536, by rfl⟩ : syracuseStep 980715 = 1471073) B1471073
theorem B980727 : Blo 980594 980727 := bstep (se 1 (by rfl) ⟨735545, by rfl⟩ : syracuseStep 980727 = 1471091) B1471091
theorem B980747 : Blo 980594 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B1472267 : Blo 980594 1472267 := bstep (se 1 (by rfl) ⟨1104200, by rfl⟩ : syracuseStep 1472267 = 2208401) B2208401
theorem B980759 : Blo 980594 980759 := bstep (se 1 (by rfl) ⟨735569, by rfl⟩ : syracuseStep 980759 = 1471139) B1471139
theorem B1472279 : Blo 980594 1472279 := bstep (se 1 (by rfl) ⟨1104209, by rfl⟩ : syracuseStep 1472279 = 2208419) B2208419
theorem B7075619 : Blo 980594 7075619 := bstep (se 1 (by rfl) ⟨5306714, by rfl⟩ : syracuseStep 7075619 = 10613429) B10613429
theorem B980779 : Blo 980594 980779 := bstep (se 1 (by rfl) ⟨735584, by rfl⟩ : syracuseStep 980779 = 1471169) B1471169
theorem B980791 : Blo 980594 980791 := bstep (se 1 (by rfl) ⟨735593, by rfl⟩ : syracuseStep 980791 = 1471187) B1471187
theorem B5601089 : Blo 980594 5601089 := bstep (se 2 (by rfl) ⟨2100408, by rfl⟩ : syracuseStep 5601089 = 4200817) B4200817
theorem B1767233 : Blo 980594 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B980811 : Blo 980594 980811 := bstep (se 1 (by rfl) ⟨735608, by rfl⟩ : syracuseStep 980811 = 1471217) B1471217
theorem B1242955 : Blo 980594 1242955 := bstep (se 1 (by rfl) ⟨932216, by rfl⟩ : syracuseStep 1242955 = 1864433) B1864433
theorem B980823 : Blo 980594 980823 := bstep (se 1 (by rfl) ⟨735617, by rfl⟩ : syracuseStep 980823 = 1471235) B1471235
theorem B1472345 : Blo 980594 1472345 := bstep (se 2 (by rfl) ⟨552129, by rfl⟩ : syracuseStep 1472345 = 1104259) B1104259
theorem B980843 : Blo 980594 980843 := bstep (se 1 (by rfl) ⟨735632, by rfl⟩ : syracuseStep 980843 = 1471265) B1471265
theorem B1865587 : Blo 980594 1865587 := bstep (se 1 (by rfl) ⟨1399190, by rfl⟩ : syracuseStep 1865587 = 2798381) B2798381
theorem B980855 : Blo 980594 980855 := bstep (se 1 (by rfl) ⟨735641, by rfl⟩ : syracuseStep 980855 = 1471283) B1471283
theorem B980875 : Blo 980594 980875 := bstep (se 1 (by rfl) ⟨735656, by rfl⟩ : syracuseStep 980875 = 1471313) B1471313
theorem B980887 : Blo 980594 980887 := bstep (se 1 (by rfl) ⟨735665, by rfl⟩ : syracuseStep 980887 = 1471331) B1471331
theorem B1275799 : Blo 980594 1275799 := bstep (se 1 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 1275799 = 1913699) B1913699
theorem B4978583 : Blo 980594 4978583 := bstep (se 1 (by rfl) ⟨3733937, by rfl⟩ : syracuseStep 4978583 = 7467875) B7467875
theorem B980907 : Blo 980594 980907 := bstep (se 1 (by rfl) ⟨735680, by rfl⟩ : syracuseStep 980907 = 1471361) B1471361
theorem B980919 : Blo 980594 980919 := bstep (se 1 (by rfl) ⟨735689, by rfl⟩ : syracuseStep 980919 = 1471379) B1471379
theorem B980939 : Blo 980594 980939 := bstep (se 1 (by rfl) ⟨735704, by rfl⟩ : syracuseStep 980939 = 1471409) B1471409
theorem B1472459 : Blo 980594 1472459 := bstep (se 1 (by rfl) ⟨1104344, by rfl⟩ : syracuseStep 1472459 = 2208689) B2208689
theorem B980951 : Blo 980594 980951 := bstep (se 1 (by rfl) ⟨735713, by rfl⟩ : syracuseStep 980951 = 1471427) B1471427
theorem B1472471 : Blo 980594 1472471 := bstep (se 1 (by rfl) ⟨1104353, by rfl⟩ : syracuseStep 1472471 = 2208707) B2208707
theorem B6387673 : Blo 980594 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B980971 : Blo 980594 980971 := bstep (se 1 (by rfl) ⟨735728, by rfl⟩ : syracuseStep 980971 = 1471457) B1471457
theorem B980983 : Blo 980594 980983 := bstep (se 1 (by rfl) ⟨735737, by rfl⟩ : syracuseStep 980983 = 1471475) B1471475
theorem B981003 : Blo 980594 981003 := bstep (se 1 (by rfl) ⟨735752, by rfl⟩ : syracuseStep 981003 = 1471505) B1471505
theorem B981015 : Blo 980594 981015 := bstep (se 1 (by rfl) ⟨735761, by rfl⟩ : syracuseStep 981015 = 1471523) B1471523
theorem B1472537 : Blo 980594 1472537 := bstep (se 2 (by rfl) ⟨552201, by rfl⟩ : syracuseStep 1472537 = 1104403) B1104403
theorem B981035 : Blo 980594 981035 := bstep (se 1 (by rfl) ⟨735776, by rfl⟩ : syracuseStep 981035 = 1471553) B1471553
theorem B981047 : Blo 980594 981047 := bstep (se 1 (by rfl) ⟨735785, by rfl⟩ : syracuseStep 981047 = 1471571) B1471571
theorem B981067 : Blo 980594 981067 := bstep (se 1 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 981067 = 1471601) B1471601
theorem B981079 : Blo 980594 981079 := bstep (se 1 (by rfl) ⟨735809, by rfl⟩ : syracuseStep 981079 = 1471619) B1471619
theorem B981099 : Blo 980594 981099 := bstep (se 1 (by rfl) ⟨735824, by rfl⟩ : syracuseStep 981099 = 1471649) B1471649
theorem B981111 : Blo 980594 981111 := bstep (se 1 (by rfl) ⟨735833, by rfl⟩ : syracuseStep 981111 = 1471667) B1471667
theorem B6813827 : Blo 980594 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B981131 : Blo 980594 981131 := bstep (se 1 (by rfl) ⟨735848, by rfl⟩ : syracuseStep 981131 = 1471697) B1471697
theorem B1472651 : Blo 980594 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B981143 : Blo 980594 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B3537047 : Blo 980594 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B1472663 : Blo 980594 1472663 := bstep (se 1 (by rfl) ⟨1104497, by rfl⟩ : syracuseStep 1472663 = 2208995) B2208995
theorem B981163 : Blo 980594 981163 := bstep (se 1 (by rfl) ⟨735872, by rfl⟩ : syracuseStep 981163 = 1471745) B1471745
theorem B2095283 : Blo 980594 2095283 := bstep (se 1 (by rfl) ⟨1571462, by rfl⟩ : syracuseStep 2095283 = 3142925) B3142925
theorem B981175 : Blo 980594 981175 := bstep (se 1 (by rfl) ⟨735881, by rfl⟩ : syracuseStep 981175 = 1471763) B1471763
theorem B2652353 : Blo 980594 2652353 := bstep (se 2 (by rfl) ⟨994632, by rfl⟩ : syracuseStep 2652353 = 1989265) B1989265
theorem B3143873 : Blo 980594 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B981195 : Blo 980594 981195 := bstep (se 1 (by rfl) ⟨735896, by rfl⟩ : syracuseStep 981195 = 1471793) B1471793
theorem B981207 : Blo 980594 981207 := bstep (se 1 (by rfl) ⟨735905, by rfl⟩ : syracuseStep 981207 = 1471811) B1471811
theorem B1472729 : Blo 980594 1472729 := bstep (se 2 (by rfl) ⟨552273, by rfl⟩ : syracuseStep 1472729 = 1104547) B1104547
theorem B981227 : Blo 980594 981227 := bstep (se 1 (by rfl) ⟨735920, by rfl⟩ : syracuseStep 981227 = 1471841) B1471841
theorem B16152817 : Blo 980594 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B981239 : Blo 980594 981239 := bstep (se 1 (by rfl) ⟨735929, by rfl⟩ : syracuseStep 981239 = 1471859) B1471859
theorem B981259 : Blo 980594 981259 := bstep (se 1 (by rfl) ⟨735944, by rfl⟩ : syracuseStep 981259 = 1471889) B1471889
theorem B981271 : Blo 980594 981271 := bstep (se 1 (by rfl) ⟨735953, by rfl⟩ : syracuseStep 981271 = 1471907) B1471907
theorem B2652439 : Blo 980594 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B981291 : Blo 980594 981291 := bstep (se 1 (by rfl) ⟨735968, by rfl⟩ : syracuseStep 981291 = 1471937) B1471937
theorem B981303 : Blo 980594 981303 := bstep (se 1 (by rfl) ⟨735977, by rfl⟩ : syracuseStep 981303 = 1471955) B1471955
theorem B2357579 : Blo 980594 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B981323 : Blo 980594 981323 := bstep (se 1 (by rfl) ⟨735992, by rfl⟩ : syracuseStep 981323 = 1471985) B1471985
theorem B1472843 : Blo 980594 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B981335 : Blo 980594 981335 := bstep (se 1 (by rfl) ⟨736001, by rfl⟩ : syracuseStep 981335 = 1472003) B1472003
theorem B1472855 : Blo 980594 1472855 := bstep (se 1 (by rfl) ⟨1104641, by rfl⟩ : syracuseStep 1472855 = 2209283) B2209283
theorem B1866073 : Blo 980594 1866073 := bstep (se 2 (by rfl) ⟨699777, by rfl⟩ : syracuseStep 1866073 = 1399555) B1399555
theorem B981355 : Blo 980594 981355 := bstep (se 1 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 981355 = 1472033) B1472033
theorem B981367 : Blo 980594 981367 := bstep (se 1 (by rfl) ⟨736025, by rfl⟩ : syracuseStep 981367 = 1472051) B1472051
theorem B981387 : Blo 980594 981387 := bstep (se 1 (by rfl) ⟨736040, by rfl⟩ : syracuseStep 981387 = 1472081) B1472081
theorem B981399 : Blo 980594 981399 := bstep (se 1 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 981399 = 1472099) B1472099
theorem B1472921 : Blo 980594 1472921 := bstep (se 2 (by rfl) ⟨552345, by rfl⟩ : syracuseStep 1472921 = 1104691) B1104691
theorem B981419 : Blo 980594 981419 := bstep (se 1 (by rfl) ⟨736064, by rfl⟩ : syracuseStep 981419 = 1472129) B1472129
theorem B4192685 : Blo 980594 4192685 := bstep (se 3 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 4192685 = 1572257) B1572257
theorem B981431 : Blo 980594 981431 := bstep (se 1 (by rfl) ⟨736073, by rfl⟩ : syracuseStep 981431 = 1472147) B1472147
theorem B981451 : Blo 980594 981451 := bstep (se 1 (by rfl) ⟨736088, by rfl⟩ : syracuseStep 981451 = 1472177) B1472177
theorem B981463 : Blo 980594 981463 := bstep (se 1 (by rfl) ⟨736097, by rfl⟩ : syracuseStep 981463 = 1472195) B1472195
theorem B981483 : Blo 980594 981483 := bstep (se 1 (by rfl) ⟨736112, by rfl⟩ : syracuseStep 981483 = 1472225) B1472225
theorem B981495 : Blo 980594 981495 := bstep (se 1 (by rfl) ⟨736121, by rfl⟩ : syracuseStep 981495 = 1472243) B1472243
theorem B981515 : Blo 980594 981515 := bstep (se 1 (by rfl) ⟨736136, by rfl⟩ : syracuseStep 981515 = 1472273) B1472273
theorem B1473035 : Blo 980594 1473035 := bstep (se 1 (by rfl) ⟨1104776, by rfl⟩ : syracuseStep 1473035 = 2209553) B2209553
theorem B981527 : Blo 980594 981527 := bstep (se 1 (by rfl) ⟨736145, by rfl⟩ : syracuseStep 981527 = 1472291) B1472291
theorem B1473047 : Blo 980594 1473047 := bstep (se 1 (by rfl) ⟨1104785, by rfl⟩ : syracuseStep 1473047 = 2209571) B2209571
theorem B981547 : Blo 980594 981547 := bstep (se 1 (by rfl) ⟨736160, by rfl⟩ : syracuseStep 981547 = 1472321) B1472321
theorem B981559 : Blo 980594 981559 := bstep (se 1 (by rfl) ⟨736169, by rfl⟩ : syracuseStep 981559 = 1472339) B1472339
theorem B981579 : Blo 980594 981579 := bstep (se 1 (by rfl) ⟨736184, by rfl⟩ : syracuseStep 981579 = 1472369) B1472369
theorem B2488907 : Blo 980594 2488907 := bstep (se 1 (by rfl) ⟨1866680, by rfl⟩ : syracuseStep 2488907 = 3733361) B3733361
theorem B981591 : Blo 980594 981591 := bstep (se 1 (by rfl) ⟨736193, by rfl⟩ : syracuseStep 981591 = 1472387) B1472387
theorem B1473113 : Blo 980594 1473113 := bstep (se 2 (by rfl) ⟨552417, by rfl⟩ : syracuseStep 1473113 = 1104835) B1104835
theorem B981611 : Blo 980594 981611 := bstep (se 1 (by rfl) ⟨736208, by rfl⟩ : syracuseStep 981611 = 1472417) B1472417
theorem B981623 : Blo 980594 981623 := bstep (se 1 (by rfl) ⟨736217, by rfl⟩ : syracuseStep 981623 = 1472435) B1472435
theorem B981643 : Blo 980594 981643 := bstep (se 1 (by rfl) ⟨736232, by rfl⟩ : syracuseStep 981643 = 1472465) B1472465
theorem B981655 : Blo 980594 981655 := bstep (se 1 (by rfl) ⟨736241, by rfl⟩ : syracuseStep 981655 = 1472483) B1472483
theorem B981675 : Blo 980594 981675 := bstep (se 1 (by rfl) ⟨736256, by rfl⟩ : syracuseStep 981675 = 1472513) B1472513
theorem B981687 : Blo 980594 981687 := bstep (se 1 (by rfl) ⟨736265, by rfl⟩ : syracuseStep 981687 = 1472531) B1472531
theorem B2357963 : Blo 980594 2357963 := bstep (se 1 (by rfl) ⟨1768472, by rfl⟩ : syracuseStep 2357963 = 3536945) B3536945
theorem B981707 : Blo 980594 981707 := bstep (se 1 (by rfl) ⟨736280, by rfl⟩ : syracuseStep 981707 = 1472561) B1472561
theorem B1473227 : Blo 980594 1473227 := bstep (se 1 (by rfl) ⟨1104920, by rfl⟩ : syracuseStep 1473227 = 2209841) B2209841
theorem B981719 : Blo 980594 981719 := bstep (se 1 (by rfl) ⟨736289, by rfl⟩ : syracuseStep 981719 = 1472579) B1472579
theorem B1473239 : Blo 980594 1473239 := bstep (se 1 (by rfl) ⟨1104929, by rfl⟩ : syracuseStep 1473239 = 2209859) B2209859
theorem B981739 : Blo 980594 981739 := bstep (se 1 (by rfl) ⟨736304, by rfl⟩ : syracuseStep 981739 = 1472609) B1472609
theorem B981751 : Blo 980594 981751 := bstep (se 1 (by rfl) ⟨736313, by rfl⟩ : syracuseStep 981751 = 1472627) B1472627
theorem B981771 : Blo 980594 981771 := bstep (se 1 (by rfl) ⟨736328, by rfl⟩ : syracuseStep 981771 = 1472657) B1472657
theorem B981783 : Blo 980594 981783 := bstep (se 1 (by rfl) ⟨736337, by rfl⟩ : syracuseStep 981783 = 1472675) B1472675
theorem B1243927 : Blo 980594 1243927 := bstep (se 1 (by rfl) ⟨932945, by rfl⟩ : syracuseStep 1243927 = 1865891) B1865891
theorem B1473305 : Blo 980594 1473305 := bstep (se 2 (by rfl) ⟨552489, by rfl⟩ : syracuseStep 1473305 = 1104979) B1104979
theorem B981803 : Blo 980594 981803 := bstep (se 1 (by rfl) ⟨736352, by rfl⟩ : syracuseStep 981803 = 1472705) B1472705
theorem B11172653 : Blo 980594 11172653 := bstep (se 3 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 11172653 = 4189745) B4189745
theorem B981815 : Blo 980594 981815 := bstep (se 1 (by rfl) ⟨736361, by rfl⟩ : syracuseStep 981815 = 1472723) B1472723
theorem B1178443 : Blo 980594 1178443 := bstep (se 1 (by rfl) ⟨883832, by rfl⟩ : syracuseStep 1178443 = 1767665) B1767665
theorem B981835 : Blo 980594 981835 := bstep (se 1 (by rfl) ⟨736376, by rfl⟩ : syracuseStep 981835 = 1472753) B1472753
theorem B981847 : Blo 980594 981847 := bstep (se 1 (by rfl) ⟨736385, by rfl⟩ : syracuseStep 981847 = 1472771) B1472771
theorem B981867 : Blo 980594 981867 := bstep (se 1 (by rfl) ⟨736400, by rfl⟩ : syracuseStep 981867 = 1472801) B1472801
theorem B981879 : Blo 980594 981879 := bstep (se 1 (by rfl) ⟨736409, by rfl⟩ : syracuseStep 981879 = 1472819) B1472819
theorem B981899 : Blo 980594 981899 := bstep (se 1 (by rfl) ⟨736424, by rfl⟩ : syracuseStep 981899 = 1472849) B1472849
theorem B1473419 : Blo 980594 1473419 := bstep (se 1 (by rfl) ⟨1105064, by rfl⟩ : syracuseStep 1473419 = 2210129) B2210129
theorem B1866635 : Blo 980594 1866635 := bstep (se 1 (by rfl) ⟨1399976, by rfl⟩ : syracuseStep 1866635 = 2799953) B2799953
theorem B981911 : Blo 980594 981911 := bstep (se 1 (by rfl) ⟨736433, by rfl⟩ : syracuseStep 981911 = 1472867) B1472867
theorem B1473431 : Blo 980594 1473431 := bstep (se 1 (by rfl) ⟨1105073, by rfl⟩ : syracuseStep 1473431 = 2210147) B2210147
theorem B981931 : Blo 980594 981931 := bstep (se 1 (by rfl) ⟨736448, by rfl⟩ : syracuseStep 981931 = 1472897) B1472897
theorem B981943 : Blo 980594 981943 := bstep (se 1 (by rfl) ⟨736457, by rfl⟩ : syracuseStep 981943 = 1472915) B1472915
theorem B981963 : Blo 980594 981963 := bstep (se 1 (by rfl) ⟨736472, by rfl⟩ : syracuseStep 981963 = 1472945) B1472945
theorem B981975 : Blo 980594 981975 := bstep (se 1 (by rfl) ⟨736481, by rfl⟩ : syracuseStep 981975 = 1472963) B1472963
theorem B21527513 : Blo 980594 21527513 := bstep (se 2 (by rfl) ⟨8072817, by rfl⟩ : syracuseStep 21527513 = 16145635) B16145635
theorem B1473497 : Blo 980594 1473497 := bstep (se 2 (by rfl) ⟨552561, by rfl⟩ : syracuseStep 1473497 = 1105123) B1105123
theorem B981995 : Blo 980594 981995 := bstep (se 1 (by rfl) ⟨736496, by rfl⟩ : syracuseStep 981995 = 1472993) B1472993
theorem B982007 : Blo 980594 982007 := bstep (se 1 (by rfl) ⟨736505, by rfl⟩ : syracuseStep 982007 = 1473011) B1473011
theorem B3734531 : Blo 980594 3734531 := bstep (se 1 (by rfl) ⟨2800898, by rfl⟩ : syracuseStep 3734531 = 5601797) B5601797
theorem B982027 : Blo 980594 982027 := bstep (se 1 (by rfl) ⟨736520, by rfl⟩ : syracuseStep 982027 = 1473041) B1473041
theorem B3734545 : Blo 980594 3734545 := bstep (se 2 (by rfl) ⟨1400454, by rfl⟩ : syracuseStep 3734545 = 2800909) B2800909
theorem B982039 : Blo 980594 982039 := bstep (se 1 (by rfl) ⟨736529, by rfl⟩ : syracuseStep 982039 = 1473059) B1473059
theorem B982059 : Blo 980594 982059 := bstep (se 1 (by rfl) ⟨736544, by rfl⟩ : syracuseStep 982059 = 1473089) B1473089
theorem B982071 : Blo 980594 982071 := bstep (se 1 (by rfl) ⟨736553, by rfl⟩ : syracuseStep 982071 = 1473107) B1473107
theorem B1866817 : Blo 980594 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B982091 : Blo 980594 982091 := bstep (se 1 (by rfl) ⟨736568, by rfl⟩ : syracuseStep 982091 = 1473137) B1473137
theorem B1473611 : Blo 980594 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B982103 : Blo 980594 982103 := bstep (se 1 (by rfl) ⟨736577, by rfl⟩ : syracuseStep 982103 = 1473155) B1473155
theorem B1473623 : Blo 980594 1473623 := bstep (se 1 (by rfl) ⟨1105217, by rfl⟩ : syracuseStep 1473623 = 2210435) B2210435
theorem B4193369 : Blo 980594 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B982123 : Blo 980594 982123 := bstep (se 1 (by rfl) ⟨736592, by rfl⟩ : syracuseStep 982123 = 1473185) B1473185
theorem B982135 : Blo 980594 982135 := bstep (se 1 (by rfl) ⟨736601, by rfl⟩ : syracuseStep 982135 = 1473203) B1473203
theorem B982155 : Blo 980594 982155 := bstep (se 1 (by rfl) ⟨736616, by rfl⟩ : syracuseStep 982155 = 1473233) B1473233
theorem B982167 : Blo 980594 982167 := bstep (se 1 (by rfl) ⟨736625, by rfl⟩ : syracuseStep 982167 = 1473251) B1473251
theorem B1473689 : Blo 980594 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B982187 : Blo 980594 982187 := bstep (se 1 (by rfl) ⟨736640, by rfl⟩ : syracuseStep 982187 = 1473281) B1473281
theorem B982199 : Blo 980594 982199 := bstep (se 1 (by rfl) ⟨736649, by rfl⟩ : syracuseStep 982199 = 1473299) B1473299
theorem B982219 : Blo 980594 982219 := bstep (se 1 (by rfl) ⟨736664, by rfl⟩ : syracuseStep 982219 = 1473329) B1473329
theorem B982231 : Blo 980594 982231 := bstep (se 1 (by rfl) ⟨736673, by rfl⟩ : syracuseStep 982231 = 1473347) B1473347
theorem B982251 : Blo 980594 982251 := bstep (se 1 (by rfl) ⟨736688, by rfl⟩ : syracuseStep 982251 = 1473377) B1473377
theorem B982263 : Blo 980594 982263 := bstep (se 1 (by rfl) ⟨736697, by rfl⟩ : syracuseStep 982263 = 1473395) B1473395
theorem B982283 : Blo 980594 982283 := bstep (se 1 (by rfl) ⟨736712, by rfl⟩ : syracuseStep 982283 = 1473425) B1473425
theorem B1473803 : Blo 980594 1473803 := bstep (se 1 (by rfl) ⟨1105352, by rfl⟩ : syracuseStep 1473803 = 2210705) B2210705
theorem B982295 : Blo 980594 982295 := bstep (se 1 (by rfl) ⟨736721, by rfl⟩ : syracuseStep 982295 = 1473443) B1473443
theorem B1473815 : Blo 980594 1473815 := bstep (se 1 (by rfl) ⟨1105361, by rfl⟩ : syracuseStep 1473815 = 2210723) B2210723
theorem B982315 : Blo 980594 982315 := bstep (se 1 (by rfl) ⟨736736, by rfl⟩ : syracuseStep 982315 = 1473473) B1473473
theorem B982327 : Blo 980594 982327 := bstep (se 1 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 982327 = 1473491) B1473491
theorem B16809281 : Blo 980594 16809281 := bstep (se 2 (by rfl) ⟨6303480, by rfl⟩ : syracuseStep 16809281 = 12606961) B12606961
theorem B3734849 : Blo 980594 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B982347 : Blo 980594 982347 := bstep (se 1 (by rfl) ⟨736760, by rfl⟩ : syracuseStep 982347 = 1473521) B1473521
theorem B982359 : Blo 980594 982359 := bstep (se 1 (by rfl) ⟨736769, by rfl⟩ : syracuseStep 982359 = 1473539) B1473539
theorem B1473881 : Blo 980594 1473881 := bstep (se 2 (by rfl) ⟨552705, by rfl⟩ : syracuseStep 1473881 = 1105411) B1105411
theorem B982379 : Blo 980594 982379 := bstep (se 1 (by rfl) ⟨736784, by rfl⟩ : syracuseStep 982379 = 1473569) B1473569
theorem B982391 : Blo 980594 982391 := bstep (se 1 (by rfl) ⟨736793, by rfl⟩ : syracuseStep 982391 = 1473587) B1473587
theorem B982411 : Blo 980594 982411 := bstep (se 1 (by rfl) ⟨736808, by rfl⟩ : syracuseStep 982411 = 1473617) B1473617
theorem B3538327 : Blo 980594 3538327 := bstep (se 1 (by rfl) ⟨2653745, by rfl⟩ : syracuseStep 3538327 = 5307491) B5307491
theorem B982423 : Blo 980594 982423 := bstep (se 1 (by rfl) ⟨736817, by rfl⟩ : syracuseStep 982423 = 1473635) B1473635
theorem B982443 : Blo 980594 982443 := bstep (se 1 (by rfl) ⟨736832, by rfl⟩ : syracuseStep 982443 = 1473665) B1473665
theorem B982455 : Blo 980594 982455 := bstep (se 1 (by rfl) ⟨736841, by rfl⟩ : syracuseStep 982455 = 1473683) B1473683
theorem B2358731 : Blo 980594 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B982475 : Blo 980594 982475 := bstep (se 1 (by rfl) ⟨736856, by rfl⟩ : syracuseStep 982475 = 1473713) B1473713
theorem B1473995 : Blo 980594 1473995 := bstep (se 1 (by rfl) ⟨1105496, by rfl⟩ : syracuseStep 1473995 = 2210993) B2210993
theorem B2096599 : Blo 980594 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B982487 : Blo 980594 982487 := bstep (se 1 (by rfl) ⟨736865, by rfl⟩ : syracuseStep 982487 = 1473731) B1473731
theorem B1474007 : Blo 980594 1474007 := bstep (se 1 (by rfl) ⟨1105505, by rfl⟩ : syracuseStep 1474007 = 2211011) B2211011
theorem B982507 : Blo 980594 982507 := bstep (se 1 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 982507 = 1473761) B1473761
theorem B982519 : Blo 980594 982519 := bstep (se 1 (by rfl) ⟨736889, by rfl⟩ : syracuseStep 982519 = 1473779) B1473779
theorem B982539 : Blo 980594 982539 := bstep (se 1 (by rfl) ⟨736904, by rfl⟩ : syracuseStep 982539 = 1473809) B1473809
theorem B982551 : Blo 980594 982551 := bstep (se 1 (by rfl) ⟨736913, by rfl⟩ : syracuseStep 982551 = 1473827) B1473827
theorem B2489879 : Blo 980594 2489879 := bstep (se 1 (by rfl) ⟨1867409, by rfl⟩ : syracuseStep 2489879 = 3734819) B3734819
theorem B1474073 : Blo 980594 1474073 := bstep (se 2 (by rfl) ⟨552777, by rfl⟩ : syracuseStep 1474073 = 1105555) B1105555
theorem B982571 : Blo 980594 982571 := bstep (se 1 (by rfl) ⟨736928, by rfl⟩ : syracuseStep 982571 = 1473857) B1473857
theorem B982583 : Blo 980594 982583 := bstep (se 1 (by rfl) ⟨736937, by rfl⟩ : syracuseStep 982583 = 1473875) B1473875
theorem B982603 : Blo 980594 982603 := bstep (se 1 (by rfl) ⟨736952, by rfl⟩ : syracuseStep 982603 = 1473905) B1473905
theorem B1244747 : Blo 980594 1244747 := bstep (se 1 (by rfl) ⟨933560, by rfl⟩ : syracuseStep 1244747 = 1867121) B1867121
theorem B982615 : Blo 980594 982615 := bstep (se 1 (by rfl) ⟨736961, by rfl⟩ : syracuseStep 982615 = 1473923) B1473923
theorem B982635 : Blo 980594 982635 := bstep (se 1 (by rfl) ⟨736976, by rfl⟩ : syracuseStep 982635 = 1473953) B1473953
theorem B982647 : Blo 980594 982647 := bstep (se 1 (by rfl) ⟨736985, by rfl⟩ : syracuseStep 982647 = 1473971) B1473971
theorem B2096779 : Blo 980594 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B982667 : Blo 980594 982667 := bstep (se 1 (by rfl) ⟨737000, by rfl⟩ : syracuseStep 982667 = 1474001) B1474001
theorem B1474187 : Blo 980594 1474187 := bstep (se 1 (by rfl) ⟨1105640, by rfl⟩ : syracuseStep 1474187 = 2211281) B2211281
theorem B5308055 : Blo 980594 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B982679 : Blo 980594 982679 := bstep (se 1 (by rfl) ⟨737009, by rfl⟩ : syracuseStep 982679 = 1474019) B1474019
theorem B1474199 : Blo 980594 1474199 := bstep (se 1 (by rfl) ⟨1105649, by rfl⟩ : syracuseStep 1474199 = 2211299) B2211299
theorem B982699 : Blo 980594 982699 := bstep (se 1 (by rfl) ⟨737024, by rfl⟩ : syracuseStep 982699 = 1474049) B1474049
theorem B982711 : Blo 980594 982711 := bstep (se 1 (by rfl) ⟨737033, by rfl⟩ : syracuseStep 982711 = 1474067) B1474067
theorem B982731 : Blo 980594 982731 := bstep (se 1 (by rfl) ⟨737048, by rfl⟩ : syracuseStep 982731 = 1474097) B1474097
theorem B40402637 : Blo 980594 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B2096855 : Blo 980594 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B982743 : Blo 980594 982743 := bstep (se 1 (by rfl) ⟨737057, by rfl⟩ : syracuseStep 982743 = 1474115) B1474115
theorem B1474265 : Blo 980594 1474265 := bstep (se 2 (by rfl) ⟨552849, by rfl⟩ : syracuseStep 1474265 = 1105699) B1105699
theorem B982763 : Blo 980594 982763 := bstep (se 1 (by rfl) ⟨737072, by rfl⟩ : syracuseStep 982763 = 1474145) B1474145
theorem B982775 : Blo 980594 982775 := bstep (se 1 (by rfl) ⟨737081, by rfl⟩ : syracuseStep 982775 = 1474163) B1474163
theorem B982795 : Blo 980594 982795 := bstep (se 1 (by rfl) ⟨737096, by rfl⟩ : syracuseStep 982795 = 1474193) B1474193
theorem B1867531 : Blo 980594 1867531 := bstep (se 1 (by rfl) ⟨1400648, by rfl⟩ : syracuseStep 1867531 = 2801297) B2801297
theorem B982807 : Blo 980594 982807 := bstep (se 1 (by rfl) ⟨737105, by rfl⟩ : syracuseStep 982807 = 1474211) B1474211
theorem B982827 : Blo 980594 982827 := bstep (se 1 (by rfl) ⟨737120, by rfl⟩ : syracuseStep 982827 = 1474241) B1474241
theorem B982839 : Blo 980594 982839 := bstep (se 1 (by rfl) ⟨737129, by rfl⟩ : syracuseStep 982839 = 1474259) B1474259
theorem B982859 : Blo 980594 982859 := bstep (se 1 (by rfl) ⟨737144, by rfl⟩ : syracuseStep 982859 = 1474289) B1474289
theorem B1474379 : Blo 980594 1474379 := bstep (se 1 (by rfl) ⟨1105784, by rfl⟩ : syracuseStep 1474379 = 2211569) B2211569
theorem B982871 : Blo 980594 982871 := bstep (se 1 (by rfl) ⟨737153, by rfl⟩ : syracuseStep 982871 = 1474307) B1474307
theorem B1474391 : Blo 980594 1474391 := bstep (se 1 (by rfl) ⟨1105793, by rfl⟩ : syracuseStep 1474391 = 2211587) B2211587
theorem B1867607 : Blo 980594 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B982891 : Blo 980594 982891 := bstep (se 1 (by rfl) ⟨737168, by rfl⟩ : syracuseStep 982891 = 1474337) B1474337
theorem B15138677 : Blo 980594 15138677 := bstep (se 5 (by rfl) ⟨709625, by rfl⟩ : syracuseStep 15138677 = 1419251) B1419251
theorem B982903 : Blo 980594 982903 := bstep (se 1 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 982903 = 1474355) B1474355
theorem B982923 : Blo 980594 982923 := bstep (se 1 (by rfl) ⟨737192, by rfl⟩ : syracuseStep 982923 = 1474385) B1474385
theorem B982935 : Blo 980594 982935 := bstep (se 1 (by rfl) ⟨737201, by rfl⟩ : syracuseStep 982935 = 1474403) B1474403
theorem B1474457 : Blo 980594 1474457 := bstep (se 2 (by rfl) ⟨552921, by rfl⟩ : syracuseStep 1474457 = 1105843) B1105843
theorem B982955 : Blo 980594 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B982967 : Blo 980594 982967 := bstep (se 1 (by rfl) ⟨737225, by rfl⟩ : syracuseStep 982967 = 1474451) B1474451
theorem B982987 : Blo 980594 982987 := bstep (se 1 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 982987 = 1474481) B1474481
theorem B982999 : Blo 980594 982999 := bstep (se 1 (by rfl) ⟨737249, by rfl⟩ : syracuseStep 982999 = 1474499) B1474499
theorem B3735517 : Blo 980594 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B983019 : Blo 980594 983019 := bstep (se 1 (by rfl) ⟨737264, by rfl⟩ : syracuseStep 983019 = 1474529) B1474529
theorem B983031 : Blo 980594 983031 := bstep (se 1 (by rfl) ⟨737273, by rfl⟩ : syracuseStep 983031 = 1474547) B1474547
theorem B983047 : Blo 980594 983047 := bstep (se 1 (by rfl) ⟨737285, by rfl⟩ : syracuseStep 983047 = 1474571) B1474571
theorem B983055 : Blo 980594 983055 := bstep (se 1 (by rfl) ⟨737291, by rfl⟩ : syracuseStep 983055 = 1474583) B1474583
theorem B1474619 : Blo 980594 1474619 := bstep (se 1 (by rfl) ⟨1105964, by rfl⟩ : syracuseStep 1474619 = 2211929) B2211929
theorem B983099 : Blo 980594 983099 := bstep (se 1 (by rfl) ⟨737324, by rfl⟩ : syracuseStep 983099 = 1474649) B1474649
theorem B1867835 : Blo 980594 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B1474679 : Blo 980594 1474679 := bstep (se 1 (by rfl) ⟨1106009, by rfl⟩ : syracuseStep 1474679 = 2212019) B2212019
theorem B983175 : Blo 980594 983175 := bstep (se 1 (by rfl) ⟨737381, by rfl⟩ : syracuseStep 983175 = 1474763) B1474763
theorem B1474703 : Blo 980594 1474703 := bstep (se 1 (by rfl) ⟨1106027, by rfl⟩ : syracuseStep 1474703 = 2212055) B2212055
theorem B983183 : Blo 980594 983183 := bstep (se 1 (by rfl) ⟨737387, by rfl⟩ : syracuseStep 983183 = 1474775) B1474775
theorem B2097299 : Blo 980594 2097299 := bstep (se 1 (by rfl) ⟨1572974, by rfl⟩ : syracuseStep 2097299 = 3145949) B3145949
theorem B7471277 : Blo 980594 7471277 := bstep (se 3 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 7471277 = 2801729) B2801729
theorem B1474745 : Blo 980594 1474745 := bstep (se 2 (by rfl) ⟨553029, by rfl⟩ : syracuseStep 1474745 = 1106059) B1106059
theorem B983227 : Blo 980594 983227 := bstep (se 1 (by rfl) ⟨737420, by rfl⟩ : syracuseStep 983227 = 1474841) B1474841
theorem B1474823 : Blo 980594 1474823 := bstep (se 1 (by rfl) ⟨1106117, by rfl⟩ : syracuseStep 1474823 = 2212235) B2212235
theorem B983303 : Blo 980594 983303 := bstep (se 1 (by rfl) ⟨737477, by rfl⟩ : syracuseStep 983303 = 1474955) B1474955
theorem B983311 : Blo 980594 983311 := bstep (se 1 (by rfl) ⟨737483, by rfl⟩ : syracuseStep 983311 = 1474967) B1474967
theorem B1474859 : Blo 980594 1474859 := bstep (se 1 (by rfl) ⟨1106144, by rfl⟩ : syracuseStep 1474859 = 2212289) B2212289
theorem B983355 : Blo 980594 983355 := bstep (se 1 (by rfl) ⟨737516, by rfl⟩ : syracuseStep 983355 = 1475033) B1475033
theorem B2654525 : Blo 980594 2654525 := bstep (se 3 (by rfl) ⟨497723, by rfl⟩ : syracuseStep 2654525 = 995447) B995447
theorem B1474889 : Blo 980594 1474889 := bstep (se 2 (by rfl) ⟨553083, by rfl⟩ : syracuseStep 1474889 = 1106167) B1106167
theorem B983431 : Blo 980594 983431 := bstep (se 1 (by rfl) ⟨737573, by rfl⟩ : syracuseStep 983431 = 1475147) B1475147
theorem B983439 : Blo 980594 983439 := bstep (se 1 (by rfl) ⟨737579, by rfl⟩ : syracuseStep 983439 = 1475159) B1475159
theorem B6390161 : Blo 980594 6390161 := bstep (se 2 (by rfl) ⟨2396310, by rfl⟩ : syracuseStep 6390161 = 4792621) B4792621
theorem B2523545 : Blo 980594 2523545 := bstep (se 2 (by rfl) ⟨946329, by rfl⟩ : syracuseStep 2523545 = 1892659) B1892659
theorem B1475003 : Blo 980594 1475003 := bstep (se 1 (by rfl) ⟨1106252, by rfl⟩ : syracuseStep 1475003 = 2212505) B2212505
theorem B983483 : Blo 980594 983483 := bstep (se 1 (by rfl) ⟨737612, by rfl⟩ : syracuseStep 983483 = 1475225) B1475225
theorem B1475063 : Blo 980594 1475063 := bstep (se 1 (by rfl) ⟨1106297, by rfl⟩ : syracuseStep 1475063 = 2212595) B2212595
theorem B983559 : Blo 980594 983559 := bstep (se 1 (by rfl) ⟨737669, by rfl⟩ : syracuseStep 983559 = 1475339) B1475339
theorem B3310091 : Blo 980594 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B1475087 : Blo 980594 1475087 := bstep (se 1 (by rfl) ⟨1106315, by rfl⟩ : syracuseStep 1475087 = 2212631) B2212631
theorem B983567 : Blo 980594 983567 := bstep (se 1 (by rfl) ⟨737675, by rfl⟩ : syracuseStep 983567 = 1475351) B1475351
theorem B1868321 : Blo 980594 1868321 := bstep (se 2 (by rfl) ⟨700620, by rfl⟩ : syracuseStep 1868321 = 1401241) B1401241
theorem B1475129 : Blo 980594 1475129 := bstep (se 2 (by rfl) ⟨553173, by rfl⟩ : syracuseStep 1475129 = 1106347) B1106347
theorem B983611 : Blo 980594 983611 := bstep (se 1 (by rfl) ⟨737708, by rfl⟩ : syracuseStep 983611 = 1475417) B1475417
theorem B3310199 : Blo 980594 3310199 := bstep (se 1 (by rfl) ⟨2482649, by rfl⟩ : syracuseStep 3310199 = 4965299) B4965299
theorem B3146359 : Blo 980594 3146359 := bstep (se 1 (by rfl) ⟨2359769, by rfl⟩ : syracuseStep 3146359 = 4719539) B4719539
theorem B1475207 : Blo 980594 1475207 := bstep (se 1 (by rfl) ⟨1106405, by rfl⟩ : syracuseStep 1475207 = 2212811) B2212811
theorem B983687 : Blo 980594 983687 := bstep (se 1 (by rfl) ⟨737765, by rfl⟩ : syracuseStep 983687 = 1475531) B1475531
theorem B983695 : Blo 980594 983695 := bstep (se 1 (by rfl) ⟨737771, by rfl⟩ : syracuseStep 983695 = 1475543) B1475543
theorem B2491033 : Blo 980594 2491033 := bstep (se 2 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 2491033 = 1868275) B1868275
theorem B1475243 : Blo 980594 1475243 := bstep (se 1 (by rfl) ⟨1106432, by rfl⟩ : syracuseStep 1475243 = 2212865) B2212865
theorem B983739 : Blo 980594 983739 := bstep (se 1 (by rfl) ⟨737804, by rfl⟩ : syracuseStep 983739 = 1475609) B1475609
theorem B1475273 : Blo 980594 1475273 := bstep (se 2 (by rfl) ⟨553227, by rfl⟩ : syracuseStep 1475273 = 1106455) B1106455
theorem B218170097 : Blo 980594 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B1180423 : Blo 980594 1180423 := bstep (se 1 (by rfl) ⟨885317, by rfl⟩ : syracuseStep 1180423 = 1770635) B1770635
theorem B983815 : Blo 980594 983815 := bstep (se 1 (by rfl) ⟨737861, by rfl⟩ : syracuseStep 983815 = 1475723) B1475723
theorem B983823 : Blo 980594 983823 := bstep (se 1 (by rfl) ⟨737867, by rfl⟩ : syracuseStep 983823 = 1475735) B1475735
theorem B2360107 : Blo 980594 2360107 := bstep (se 1 (by rfl) ⟨1770080, by rfl⟩ : syracuseStep 2360107 = 3540161) B3540161
theorem B1475387 : Blo 980594 1475387 := bstep (se 1 (by rfl) ⟨1106540, by rfl⟩ : syracuseStep 1475387 = 2213081) B2213081
theorem B983867 : Blo 980594 983867 := bstep (se 1 (by rfl) ⟨737900, by rfl⟩ : syracuseStep 983867 = 1475801) B1475801
theorem B2491195 : Blo 980594 2491195 := bstep (se 1 (by rfl) ⟨1868396, by rfl⟩ : syracuseStep 2491195 = 3736793) B3736793
theorem B2360183 : Blo 980594 2360183 := bstep (se 1 (by rfl) ⟨1770137, by rfl⟩ : syracuseStep 2360183 = 3540275) B3540275
theorem B1475447 : Blo 980594 1475447 := bstep (se 1 (by rfl) ⟨1106585, by rfl⟩ : syracuseStep 1475447 = 2213171) B2213171
theorem B1868663 : Blo 980594 1868663 := bstep (se 1 (by rfl) ⟨1401497, by rfl⟩ : syracuseStep 1868663 = 2802995) B2802995
theorem B983943 : Blo 980594 983943 := bstep (se 1 (by rfl) ⟨737957, by rfl⟩ : syracuseStep 983943 = 1475915) B1475915
theorem B1475471 : Blo 980594 1475471 := bstep (se 1 (by rfl) ⟨1106603, by rfl⟩ : syracuseStep 1475471 = 2213207) B2213207
theorem B983951 : Blo 980594 983951 := bstep (se 1 (by rfl) ⟨737963, by rfl⟩ : syracuseStep 983951 = 1475927) B1475927
theorem B1475513 : Blo 980594 1475513 := bstep (se 2 (by rfl) ⟨553317, by rfl⟩ : syracuseStep 1475513 = 1106635) B1106635
theorem B983995 : Blo 980594 983995 := bstep (se 1 (by rfl) ⟨737996, by rfl⟩ : syracuseStep 983995 = 1475993) B1475993
theorem B2491337 : Blo 980594 2491337 := bstep (se 2 (by rfl) ⟨934251, by rfl⟩ : syracuseStep 2491337 = 1868503) B1868503
theorem B6390731 : Blo 980594 6390731 := bstep (se 1 (by rfl) ⟨4793048, by rfl⟩ : syracuseStep 6390731 = 9586097) B9586097
theorem B1475591 : Blo 980594 1475591 := bstep (se 1 (by rfl) ⟨1106693, by rfl⟩ : syracuseStep 1475591 = 2213387) B2213387
theorem B984071 : Blo 980594 984071 := bstep (se 1 (by rfl) ⟨738053, by rfl⟩ : syracuseStep 984071 = 1476107) B1476107
theorem B984079 : Blo 980594 984079 := bstep (se 1 (by rfl) ⟨738059, by rfl⟩ : syracuseStep 984079 = 1476119) B1476119
theorem B1475627 : Blo 980594 1475627 := bstep (se 1 (by rfl) ⟨1106720, by rfl⟩ : syracuseStep 1475627 = 2213441) B2213441
theorem B984123 : Blo 980594 984123 := bstep (se 1 (by rfl) ⟨738092, by rfl⟩ : syracuseStep 984123 = 1476185) B1476185
theorem B1475657 : Blo 980594 1475657 := bstep (se 2 (by rfl) ⟨553371, by rfl⟩ : syracuseStep 1475657 = 1106743) B1106743
theorem B984199 : Blo 980594 984199 := bstep (se 1 (by rfl) ⟨738149, by rfl⟩ : syracuseStep 984199 = 1476299) B1476299
theorem B1049743 : Blo 980594 1049743 := bstep (se 1 (by rfl) ⟨787307, by rfl⟩ : syracuseStep 1049743 = 1574615) B1574615
theorem B984207 : Blo 980594 984207 := bstep (se 1 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 984207 = 1476311) B1476311
theorem B1475771 : Blo 980594 1475771 := bstep (se 1 (by rfl) ⟨1106828, by rfl⟩ : syracuseStep 1475771 = 2213657) B2213657
theorem B984251 : Blo 980594 984251 := bstep (se 1 (by rfl) ⟨738188, by rfl⟩ : syracuseStep 984251 = 1476377) B1476377
theorem B4719809 : Blo 980594 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B3310793 : Blo 980594 3310793 := bstep (se 2 (by rfl) ⟨1241547, by rfl⟩ : syracuseStep 3310793 = 2483095) B2483095
theorem B1475831 : Blo 980594 1475831 := bstep (se 1 (by rfl) ⟨1106873, by rfl⟩ : syracuseStep 1475831 = 2213747) B2213747
theorem B984327 : Blo 980594 984327 := bstep (se 1 (by rfl) ⟨738245, by rfl⟩ : syracuseStep 984327 = 1476491) B1476491
theorem B1475855 : Blo 980594 1475855 := bstep (se 1 (by rfl) ⟨1106891, by rfl⟩ : syracuseStep 1475855 = 2213783) B2213783
theorem B984335 : Blo 980594 984335 := bstep (se 1 (by rfl) ⟨738251, by rfl⟩ : syracuseStep 984335 = 1476503) B1476503
theorem B2491681 : Blo 980594 2491681 := bstep (se 2 (by rfl) ⟨934380, by rfl⟩ : syracuseStep 2491681 = 1868761) B1868761
theorem B4719923 : Blo 980594 4719923 := bstep (se 1 (by rfl) ⟨3539942, by rfl⟩ : syracuseStep 4719923 = 7079885) B7079885
theorem B1475897 : Blo 980594 1475897 := bstep (se 2 (by rfl) ⟨553461, by rfl⟩ : syracuseStep 1475897 = 1106923) B1106923
theorem B984379 : Blo 980594 984379 := bstep (se 1 (by rfl) ⟨738284, by rfl⟩ : syracuseStep 984379 = 1476569) B1476569
theorem B2557271 : Blo 980594 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1475975 : Blo 980594 1475975 := bstep (se 1 (by rfl) ⟨1106981, by rfl⟩ : syracuseStep 1475975 = 2213963) B2213963
theorem B984455 : Blo 980594 984455 := bstep (se 1 (by rfl) ⟨738341, by rfl⟩ : syracuseStep 984455 = 1476683) B1476683
theorem B984463 : Blo 980594 984463 := bstep (se 1 (by rfl) ⟨738347, by rfl⟩ : syracuseStep 984463 = 1476695) B1476695
theorem B1476011 : Blo 980594 1476011 := bstep (se 1 (by rfl) ⟨1107008, by rfl⟩ : syracuseStep 1476011 = 2214017) B2214017
theorem B984507 : Blo 980594 984507 := bstep (se 1 (by rfl) ⟨738380, by rfl⟩ : syracuseStep 984507 = 1476761) B1476761
theorem B1476041 : Blo 980594 1476041 := bstep (se 2 (by rfl) ⟨553515, by rfl⟩ : syracuseStep 1476041 = 1107031) B1107031
theorem B984583 : Blo 980594 984583 := bstep (se 1 (by rfl) ⟨738437, by rfl⟩ : syracuseStep 984583 = 1476875) B1476875
theorem B984591 : Blo 980594 984591 := bstep (se 1 (by rfl) ⟨738443, by rfl⟩ : syracuseStep 984591 = 1476887) B1476887
theorem B1476155 : Blo 980594 1476155 := bstep (se 1 (by rfl) ⟨1107116, by rfl⟩ : syracuseStep 1476155 = 2214233) B2214233
theorem B1476215 : Blo 980594 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B1476239 : Blo 980594 1476239 := bstep (se 1 (by rfl) ⟨1107179, by rfl⟩ : syracuseStep 1476239 = 2214359) B2214359
theorem B1476281 : Blo 980594 1476281 := bstep (se 2 (by rfl) ⟨553605, by rfl⟩ : syracuseStep 1476281 = 1107211) B1107211
theorem B7079653 : Blo 980594 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B1476359 : Blo 980594 1476359 := bstep (se 1 (by rfl) ⟨1107269, by rfl⟩ : syracuseStep 1476359 = 2214539) B2214539
theorem B1476395 : Blo 980594 1476395 := bstep (se 1 (by rfl) ⟨1107296, by rfl⟩ : syracuseStep 1476395 = 2214593) B2214593
theorem B1476425 : Blo 980594 1476425 := bstep (se 2 (by rfl) ⟨553659, by rfl⟩ : syracuseStep 1476425 = 1107319) B1107319
theorem B5048153 : Blo 980594 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3311495 : Blo 980594 3311495 := bstep (se 1 (by rfl) ⟨2483621, by rfl⟩ : syracuseStep 3311495 = 4967243) B4967243
theorem B1476539 : Blo 980594 1476539 := bstep (se 1 (by rfl) ⟨1107404, by rfl⟩ : syracuseStep 1476539 = 2214809) B2214809
theorem B1771465 : Blo 980594 1771465 := bstep (se 2 (by rfl) ⟨664299, by rfl⟩ : syracuseStep 1771465 = 1328599) B1328599
theorem B1476599 : Blo 980594 1476599 := bstep (se 1 (by rfl) ⟨1107449, by rfl⟩ : syracuseStep 1476599 = 2214899) B2214899
theorem B4982795 : Blo 980594 4982795 := bstep (se 1 (by rfl) ⟨3737096, by rfl⟩ : syracuseStep 4982795 = 7474193) B7474193
theorem B1476623 : Blo 980594 1476623 := bstep (se 1 (by rfl) ⟨1107467, by rfl⟩ : syracuseStep 1476623 = 2214935) B2214935
theorem B1476665 : Blo 980594 1476665 := bstep (se 2 (by rfl) ⟨553749, by rfl⟩ : syracuseStep 1476665 = 1107499) B1107499
theorem B5605463 : Blo 980594 5605463 := bstep (se 1 (by rfl) ⟨4204097, by rfl⟩ : syracuseStep 5605463 = 8408195) B8408195
theorem B1476743 : Blo 980594 1476743 := bstep (se 1 (by rfl) ⟨1107557, by rfl⟩ : syracuseStep 1476743 = 2215115) B2215115
theorem B1476779 : Blo 980594 1476779 := bstep (se 1 (by rfl) ⟨1107584, by rfl⟩ : syracuseStep 1476779 = 2215169) B2215169
theorem B4982957 : Blo 980594 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B1476809 : Blo 980594 1476809 := bstep (se 2 (by rfl) ⟨553803, by rfl⟩ : syracuseStep 1476809 = 1107607) B1107607
theorem B3311873 : Blo 980594 3311873 := bstep (se 2 (by rfl) ⟨1241952, by rfl⟩ : syracuseStep 3311873 = 2483905) B2483905
theorem B2525555 : Blo 980594 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B2099657 : Blo 980594 2099657 := bstep (se 2 (by rfl) ⟨787371, by rfl⟩ : syracuseStep 2099657 = 1574743) B1574743
theorem B1772047 : Blo 980594 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B7473707 : Blo 980594 7473707 := bstep (se 1 (by rfl) ⟨5605280, by rfl⟩ : syracuseStep 7473707 = 11210561) B11210561
theorem B1575865 : Blo 980594 1575865 := bstep (se 2 (by rfl) ⟨590949, by rfl⟩ : syracuseStep 1575865 = 1181899) B1181899
theorem B3312683 : Blo 980594 3312683 := bstep (se 1 (by rfl) ⟨2484512, by rfl⟩ : syracuseStep 3312683 = 4969025) B4969025
theorem B5049715 : Blo 980594 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B5672339 : Blo 980594 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B10620517 : Blo 980594 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B3149513 : Blo 980594 3149513 := bstep (se 2 (by rfl) ⟨1181067, by rfl⟩ : syracuseStep 3149513 = 2362135) B2362135
theorem B5607377 : Blo 980594 5607377 := bstep (se 2 (by rfl) ⟨2102766, by rfl⟩ : syracuseStep 5607377 = 4205533) B4205533
theorem B2658589 : Blo 980594 2658589 := bstep (se 3 (by rfl) ⟨498485, by rfl⟩ : syracuseStep 2658589 = 996971) B996971
theorem B3313979 : Blo 980594 3313979 := bstep (se 1 (by rfl) ⟨2485484, by rfl⟩ : syracuseStep 3313979 = 4970969) B4970969
theorem B2101639 : Blo 980594 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B3314465 : Blo 980594 3314465 := bstep (se 2 (by rfl) ⟨1242924, by rfl⟩ : syracuseStep 3314465 = 2485849) B2485849
theorem B1119239 : Blo 980594 1119239 := bstep (se 1 (by rfl) ⟨839429, by rfl⟩ : syracuseStep 1119239 = 1678859) B1678859
theorem B4199435 : Blo 980594 4199435 := bstep (se 1 (by rfl) ⟨3149576, by rfl⟩ : syracuseStep 4199435 = 6299153) B6299153
theorem B4199485 : Blo 980594 4199485 := bstep (se 3 (by rfl) ⟨787403, by rfl⟩ : syracuseStep 4199485 = 1574807) B1574807
theorem B4724057 : Blo 980594 4724057 := bstep (se 2 (by rfl) ⟨1771521, by rfl⟩ : syracuseStep 4724057 = 3543043) B3543043
theorem B3315059 : Blo 980594 3315059 := bstep (se 1 (by rfl) ⟨2486294, by rfl⟩ : syracuseStep 3315059 = 4972589) B4972589
theorem B4724153 : Blo 980594 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B2987705 : Blo 980594 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B15931565 : Blo 980594 15931565 := bstep (se 3 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 15931565 = 5974337) B5974337
theorem B26876177 : Blo 980594 26876177 := bstep (se 2 (by rfl) ⟨10078566, by rfl⟩ : syracuseStep 26876177 = 20157133) B20157133
theorem B5970323 : Blo 980594 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B1120699 : Blo 980594 1120699 := bstep (se 1 (by rfl) ⟨840524, by rfl⟩ : syracuseStep 1120699 = 1681049) B1681049
theorem B40278799 : Blo 980594 40278799 := bstep (se 1 (by rfl) ⟨30209099, by rfl⟩ : syracuseStep 40278799 = 60418199) B60418199
theorem B5970833 : Blo 980594 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B40410019 : Blo 980594 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B5315777 : Blo 980594 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B3153305 : Blo 980594 3153305 := bstep (se 2 (by rfl) ⟨1182489, by rfl⟩ : syracuseStep 3153305 = 2364979) B2364979
theorem B2989835 : Blo 980594 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B3317651 : Blo 980594 3317651 := bstep (se 1 (by rfl) ⟨2488238, by rfl⟩ : syracuseStep 3317651 = 4976477) B4976477
theorem B11214935 : Blo 980594 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B2695303 : Blo 980594 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B2793619 : Blo 980594 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B19374353 : Blo 980594 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B21537089 : Blo 980594 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B4202867 : Blo 980594 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B2793847 : Blo 980594 2793847 := bstep (se 1 (by rfl) ⟨2095385, by rfl⟩ : syracuseStep 2793847 = 4190771) B4190771
theorem B10625539 : Blo 980594 10625539 := bstep (se 1 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 10625539 = 15938309) B15938309
theorem B4727497 : Blo 980594 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B3319055 : Blo 980594 3319055 := bstep (se 1 (by rfl) ⟨2489291, by rfl⟩ : syracuseStep 3319055 = 4978583) B4978583
theorem B2991389 : Blo 980594 2991389 := bstep (se 3 (by rfl) ⟨560885, by rfl⟩ : syracuseStep 2991389 = 1121771) B1121771
theorem B4203809 : Blo 980594 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B3319325 : Blo 980594 3319325 := bstep (se 3 (by rfl) ⟨622373, by rfl⟩ : syracuseStep 3319325 = 1244747) B1244747
theorem B2795123 : Blo 980594 2795123 := bstep (se 1 (by rfl) ⟨2096342, by rfl⟩ : syracuseStep 2795123 = 4192685) B4192685
theorem B7448435 : Blo 980594 7448435 := bstep (se 1 (by rfl) ⟨5586326, by rfl⟩ : syracuseStep 7448435 = 11172653) B11172653
theorem B2795465 : Blo 980594 2795465 := bstep (se 2 (by rfl) ⟨1048299, by rfl⟩ : syracuseStep 2795465 = 2096599) B2096599
theorem B3778589 : Blo 980594 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B2795579 : Blo 980594 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B2795705 : Blo 980594 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B4204781 : Blo 980594 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B22686389 : Blo 980594 22686389 := bstep (se 5 (by rfl) ⟨1063424, by rfl⟩ : syracuseStep 22686389 = 2126849) B2126849
theorem B2206583 : Blo 980594 2206583 := bstep (se 1 (by rfl) ⟨1654937, by rfl⟩ : syracuseStep 2206583 = 3309875) B3309875
theorem B3320729 : Blo 980594 3320729 := bstep (se 2 (by rfl) ⟨1245273, by rfl⟩ : syracuseStep 3320729 = 2490547) B2490547
theorem B4205465 : Blo 980594 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B14560181 : Blo 980594 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B2206763 : Blo 980594 2206763 := bstep (se 1 (by rfl) ⟨1655072, by rfl⟩ : syracuseStep 2206763 = 3310145) B3310145
theorem B2207123 : Blo 980594 2207123 := bstep (se 1 (by rfl) ⟨1655342, by rfl⟩ : syracuseStep 2207123 = 3310685) B3310685
theorem B2207177 : Blo 980594 2207177 := bstep (se 2 (by rfl) ⟨827691, by rfl⟩ : syracuseStep 2207177 = 1655383) B1655383
theorem B3321431 : Blo 980594 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B2797355 : Blo 980594 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B3321917 : Blo 980594 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B2207879 : Blo 980594 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B2208059 : Blo 980594 2208059 := bstep (se 1 (by rfl) ⟨1656044, by rfl⟩ : syracuseStep 2208059 = 3312089) B3312089
theorem B2208185 : Blo 980594 2208185 := bstep (se 2 (by rfl) ⟨828069, by rfl⟩ : syracuseStep 2208185 = 1656139) B1656139
theorem B18919979 : Blo 980594 18919979 := bstep (se 1 (by rfl) ⟨14189984, by rfl⟩ : syracuseStep 18919979 = 28379969) B28379969
theorem B2798347 : Blo 980594 2798347 := bstep (se 1 (by rfl) ⟨2098760, by rfl⟩ : syracuseStep 2798347 = 4197521) B4197521
theorem B2208527 : Blo 980594 2208527 := bstep (se 1 (by rfl) ⟨1656395, by rfl⟩ : syracuseStep 2208527 = 3312791) B3312791
theorem B2208545 : Blo 980594 2208545 := bstep (se 2 (by rfl) ⟨828204, by rfl⟩ : syracuseStep 2208545 = 1656409) B1656409
theorem B2798621 : Blo 980594 2798621 := bstep (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) B1049483
theorem B2208887 : Blo 980594 2208887 := bstep (se 1 (by rfl) ⟨1656665, by rfl⟩ : syracuseStep 2208887 = 3313331) B3313331
theorem B2209067 : Blo 980594 2209067 := bstep (se 1 (by rfl) ⟨1656800, by rfl⟩ : syracuseStep 2209067 = 3313601) B3313601
theorem B20428163 : Blo 980594 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B2242091 : Blo 980594 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B2209427 : Blo 980594 2209427 := bstep (se 1 (by rfl) ⟨1657070, by rfl⟩ : syracuseStep 2209427 = 3314141) B3314141
theorem B2209481 : Blo 980594 2209481 := bstep (se 2 (by rfl) ⟨828555, by rfl⟩ : syracuseStep 2209481 = 1657111) B1657111
theorem B14137163 : Blo 980594 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B8075123 : Blo 980594 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B997519 : Blo 980594 997519 := bstep (se 1 (by rfl) ⟨748139, by rfl⟩ : syracuseStep 997519 = 1496279) B1496279
theorem B2210183 : Blo 980594 2210183 := bstep (se 1 (by rfl) ⟨1657637, by rfl⟩ : syracuseStep 2210183 = 3315275) B3315275
theorem B2210363 : Blo 980594 2210363 := bstep (se 1 (by rfl) ⟨1657772, by rfl⟩ : syracuseStep 2210363 = 3315545) B3315545
theorem B1325641 : Blo 980594 1325641 := bstep (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) B994231
theorem B2210489 : Blo 980594 2210489 := bstep (se 2 (by rfl) ⟨828933, by rfl⟩ : syracuseStep 2210489 = 1657867) B1657867
theorem B10631897 : Blo 980594 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B2210831 : Blo 980594 2210831 := bstep (se 1 (by rfl) ⟨1658123, by rfl⟩ : syracuseStep 2210831 = 3316247) B3316247
theorem B2210849 : Blo 980594 2210849 := bstep (se 2 (by rfl) ⟨829068, by rfl⟩ : syracuseStep 2210849 = 1658137) B1658137
theorem B2800727 : Blo 980594 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B6372553 : Blo 980594 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B5586191 : Blo 980594 5586191 := bstep (se 1 (by rfl) ⟨4189643, by rfl⟩ : syracuseStep 5586191 = 8379287) B8379287
theorem B2800955 : Blo 980594 2800955 := bstep (se 1 (by rfl) ⟨2100716, by rfl⟩ : syracuseStep 2800955 = 4201433) B4201433
theorem B2211191 : Blo 980594 2211191 := bstep (se 1 (by rfl) ⟨1658393, by rfl⟩ : syracuseStep 2211191 = 3316787) B3316787
theorem B2801081 : Blo 980594 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B2211371 : Blo 980594 2211371 := bstep (se 1 (by rfl) ⟨1658528, by rfl⟩ : syracuseStep 2211371 = 3317057) B3317057
theorem B2211731 : Blo 980594 2211731 := bstep (se 1 (by rfl) ⟨1658798, by rfl⟩ : syracuseStep 2211731 = 3317597) B3317597
theorem B8077219 : Blo 980594 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B2211785 : Blo 980594 2211785 := bstep (se 2 (by rfl) ⟨829419, by rfl⟩ : syracuseStep 2211785 = 1658839) B1658839
theorem B6307787 : Blo 980594 6307787 := bstep (se 1 (by rfl) ⟨4730840, by rfl⟩ : syracuseStep 6307787 = 9461681) B9461681
theorem B1654843 : Blo 980594 1654843 := bstep (se 1 (by rfl) ⟨1241132, by rfl⟩ : syracuseStep 1654843 = 2482265) B2482265
theorem B1654985 : Blo 980594 1654985 := bstep (se 2 (by rfl) ⟨620619, by rfl⟩ : syracuseStep 1654985 = 1241239) B1241239
theorem B4473235 : Blo 980594 4473235 := bstep (se 1 (by rfl) ⟨3354926, by rfl⟩ : syracuseStep 4473235 = 6709853) B6709853
theorem B49136149 : Blo 980594 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B2212487 : Blo 980594 2212487 := bstep (se 1 (by rfl) ⟨1659365, by rfl⟩ : syracuseStep 2212487 = 3318731) B3318731
theorem B5587649 : Blo 980594 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B2212667 : Blo 980594 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B1655687 : Blo 980594 1655687 := bstep (se 1 (by rfl) ⟨1241765, by rfl⟩ : syracuseStep 1655687 = 2483531) B2483531
theorem B2212793 : Blo 980594 2212793 := bstep (se 2 (by rfl) ⟨829797, by rfl⟩ : syracuseStep 2212793 = 1659595) B1659595
theorem B76596185 : Blo 980594 76596185 := bstep (se 2 (by rfl) ⟨28723569, by rfl⟩ : syracuseStep 76596185 = 57447139) B57447139
theorem B2802721 : Blo 980594 2802721 := bstep (se 2 (by rfl) ⟨1051020, by rfl⟩ : syracuseStep 2802721 = 2102041) B2102041
theorem B2213135 : Blo 980594 2213135 := bstep (se 1 (by rfl) ⟨1659851, by rfl⟩ : syracuseStep 2213135 = 3319703) B3319703
theorem B2213153 : Blo 980594 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B4965785 : Blo 980594 4965785 := bstep (se 2 (by rfl) ⟨1862169, by rfl⟩ : syracuseStep 4965785 = 3724339) B3724339
theorem B9455069 : Blo 980594 9455069 := bstep (se 3 (by rfl) ⟨1772825, by rfl⟩ : syracuseStep 9455069 = 3545651) B3545651
theorem B2803211 : Blo 980594 2803211 := bstep (se 1 (by rfl) ⟨2102408, by rfl⟩ : syracuseStep 2803211 = 4204817) B4204817
theorem B1656335 : Blo 980594 1656335 := bstep (se 1 (by rfl) ⟨1242251, by rfl⟩ : syracuseStep 1656335 = 2484503) B2484503
theorem B2213495 : Blo 980594 2213495 := bstep (se 1 (by rfl) ⟨1660121, by rfl⟩ : syracuseStep 2213495 = 3320243) B3320243
theorem B2213675 : Blo 980594 2213675 := bstep (se 1 (by rfl) ⟨1660256, by rfl⟩ : syracuseStep 2213675 = 3320513) B3320513
theorem B1656875 : Blo 980594 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B2214035 : Blo 980594 2214035 := bstep (se 1 (by rfl) ⟨1660526, by rfl⟩ : syracuseStep 2214035 = 3321053) B3321053
theorem B2214089 : Blo 980594 2214089 := bstep (se 2 (by rfl) ⟨830283, by rfl⟩ : syracuseStep 2214089 = 1660567) B1660567
theorem B1198379 : Blo 980594 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B1657273 : Blo 980594 1657273 := bstep (se 2 (by rfl) ⟨621477, by rfl⟩ : syracuseStep 1657273 = 1242955) B1242955
theorem B1329679 : Blo 980594 1329679 := bstep (se 1 (by rfl) ⟨997259, by rfl⟩ : syracuseStep 1329679 = 1994519) B1994519
theorem B4246253 : Blo 980594 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B2214791 : Blo 980594 2214791 := bstep (se 1 (by rfl) ⟨1661093, by rfl⟩ : syracuseStep 2214791 = 3322187) B3322187
theorem B2214971 : Blo 980594 2214971 := bstep (se 1 (by rfl) ⟨1661228, by rfl⟩ : syracuseStep 2214971 = 3322457) B3322457
theorem B1657975 : Blo 980594 1657975 := bstep (se 1 (by rfl) ⟨1243481, by rfl⟩ : syracuseStep 1657975 = 2486963) B2486963
theorem B2215097 : Blo 980594 2215097 := bstep (se 2 (by rfl) ⟨830661, by rfl⟩ : syracuseStep 2215097 = 1661323) B1661323
theorem B1658171 : Blo 980594 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B2837879 : Blo 980594 2837879 := bstep (se 1 (by rfl) ⟨2128409, by rfl⟩ : syracuseStep 2837879 = 4256819) B4256819
theorem B1658569 : Blo 980594 1658569 := bstep (se 2 (by rfl) ⟨621963, by rfl⟩ : syracuseStep 1658569 = 1243927) B1243927
theorem B4968377 : Blo 980594 4968377 := bstep (se 2 (by rfl) ⟨1863141, by rfl⟩ : syracuseStep 4968377 = 3726283) B3726283
theorem B4542551 : Blo 980594 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B1396855 : Blo 980594 1396855 := bstep (se 1 (by rfl) ⟨1047641, by rfl⟩ : syracuseStep 1396855 = 2095283) B2095283
theorem B1659271 : Blo 980594 1659271 := bstep (se 1 (by rfl) ⟨1244453, by rfl⟩ : syracuseStep 1659271 = 2488907) B2488907
theorem B8409905 : Blo 980594 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B1659919 : Blo 980594 1659919 := bstep (se 1 (by rfl) ⟨1244939, by rfl⟩ : syracuseStep 1659919 = 2489879) B2489879
theorem B1397903 : Blo 980594 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B4969673 : Blo 980594 4969673 := bstep (se 2 (by rfl) ⟨1863627, by rfl⟩ : syracuseStep 4969673 = 3727255) B3727255
theorem B25220483 : Blo 980594 25220483 := bstep (se 1 (by rfl) ⟨18915362, by rfl⟩ : syracuseStep 25220483 = 37830725) B37830725
theorem B1398217 : Blo 980594 1398217 := bstep (se 2 (by rfl) ⟨524331, by rfl⟩ : syracuseStep 1398217 = 1048663) B1048663
theorem B5592523 : Blo 980594 5592523 := bstep (se 1 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 5592523 = 8388785) B8388785
theorem B3724811 : Blo 980594 3724811 := bstep (se 1 (by rfl) ⟨2793608, by rfl⟩ : syracuseStep 3724811 = 5587217) B5587217
theorem B1660459 : Blo 980594 1660459 := bstep (se 1 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 1660459 = 2490689) B2490689
theorem B11195981 : Blo 980594 11195981 := bstep (se 3 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 11195981 = 4198493) B4198493
theorem B1103503 : Blo 980594 1103503 := bstep (se 1 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 1103503 = 1655255) B1655255
theorem B1660601 : Blo 980594 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B60479297 : Blo 980594 60479297 := bstep (se 2 (by rfl) ⟨22679736, by rfl⟩ : syracuseStep 60479297 = 45359473) B45359473
theorem B1104007 : Blo 980594 1104007 := bstep (se 1 (by rfl) ⟨828005, by rfl⟩ : syracuseStep 1104007 = 1656011) B1656011
theorem B1104187 : Blo 980594 1104187 := bstep (se 1 (by rfl) ⟨828140, by rfl⟩ : syracuseStep 1104187 = 1656281) B1656281
theorem B1661303 : Blo 980594 1661303 := bstep (se 1 (by rfl) ⟨1245977, by rfl⟩ : syracuseStep 1661303 = 2491955) B2491955
theorem B6052249 : Blo 980594 6052249 := bstep (se 2 (by rfl) ⟨2269593, by rfl⟩ : syracuseStep 6052249 = 4539187) B4539187
theorem B1989239 : Blo 980594 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B20142863 : Blo 980594 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B1104655 : Blo 980594 1104655 := bstep (se 1 (by rfl) ⟨828491, by rfl⟩ : syracuseStep 1104655 = 1656983) B1656983
theorem B1105159 : Blo 980594 1105159 := bstep (se 1 (by rfl) ⟨828869, by rfl⟩ : syracuseStep 1105159 = 1657739) B1657739
theorem B3366203 : Blo 980594 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B1105339 : Blo 980594 1105339 := bstep (se 1 (by rfl) ⟨829004, by rfl⟩ : syracuseStep 1105339 = 1658009) B1658009
theorem B5594939 : Blo 980594 5594939 := bstep (se 1 (by rfl) ⟨4196204, by rfl⟩ : syracuseStep 5594939 = 8392409) B8392409
theorem B18898757 : Blo 980594 18898757 := bstep (se 4 (by rfl) ⟨1771758, by rfl⟩ : syracuseStep 18898757 = 3543517) B3543517
theorem B1105807 : Blo 980594 1105807 := bstep (se 1 (by rfl) ⟨829355, by rfl⟩ : syracuseStep 1105807 = 1658711) B1658711
theorem B8970263 : Blo 980594 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B2482235 : Blo 980594 2482235 := bstep (se 1 (by rfl) ⟨1861676, by rfl⟩ : syracuseStep 2482235 = 3723353) B3723353
theorem B1400905 : Blo 980594 1400905 := bstep (se 2 (by rfl) ⟨525339, by rfl⟩ : syracuseStep 1400905 = 1050679) B1050679
theorem B2482447 : Blo 980594 2482447 := bstep (se 1 (by rfl) ⟨1861835, by rfl⟩ : syracuseStep 2482447 = 3723671) B3723671
theorem B1106311 : Blo 980594 1106311 := bstep (se 1 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 1106311 = 1659467) B1659467
theorem B2482721 : Blo 980594 2482721 := bstep (se 2 (by rfl) ⟨931020, by rfl⟩ : syracuseStep 2482721 = 1862041) B1862041
theorem B1106491 : Blo 980594 1106491 := bstep (se 1 (by rfl) ⟨829868, by rfl⟩ : syracuseStep 1106491 = 1659737) B1659737
theorem B7463501 : Blo 980594 7463501 := bstep (se 3 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 7463501 = 2798813) B2798813
theorem B1991315 : Blo 980594 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B3400481 : Blo 980594 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B3072887 : Blo 980594 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B1106959 : Blo 980594 1106959 := bstep (se 1 (by rfl) ⟨830219, by rfl⟩ : syracuseStep 1106959 = 1660439) B1660439
theorem B14148695 : Blo 980594 14148695 := bstep (se 1 (by rfl) ⟨10611521, by rfl⟩ : syracuseStep 14148695 = 21223043) B21223043
theorem B8381677 : Blo 980594 8381677 := bstep (se 3 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 8381677 = 3143129) B3143129
theorem B5596397 : Blo 980594 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B551380229 : Blo 980594 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B3728699 : Blo 980594 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B2516359 : Blo 980594 2516359 := bstep (se 1 (by rfl) ⟨1887269, by rfl⟩ : syracuseStep 2516359 = 3774539) B3774539
theorem B1107463 : Blo 980594 1107463 := bstep (se 1 (by rfl) ⟨830597, by rfl⟩ : syracuseStep 1107463 = 1661195) B1661195
theorem B2483723 : Blo 980594 2483723 := bstep (se 1 (by rfl) ⟨1862792, by rfl⟩ : syracuseStep 2483723 = 3725585) B3725585
theorem B5596715 : Blo 980594 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B1107643 : Blo 980594 1107643 := bstep (se 1 (by rfl) ⟨830732, by rfl⟩ : syracuseStep 1107643 = 1661465) B1661465
theorem B3729185 : Blo 980594 3729185 := bstep (se 2 (by rfl) ⟨1398444, by rfl⟩ : syracuseStep 3729185 = 2796889) B2796889
theorem B5662781 : Blo 980594 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B11954309 : Blo 980594 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B1894535 : Blo 980594 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B2484371 : Blo 980594 2484371 := bstep (se 1 (by rfl) ⟨1863278, by rfl⟩ : syracuseStep 2484371 = 3726557) B3726557
theorem B3991943 : Blo 980594 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B2484665 : Blo 980594 2484665 := bstep (se 2 (by rfl) ⟨931749, by rfl⟩ : syracuseStep 2484665 = 1863499) B1863499
theorem B1862291 : Blo 980594 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B1862345 : Blo 980594 1862345 := bstep (se 2 (by rfl) ⟨698379, by rfl⟩ : syracuseStep 1862345 = 1396759) B1396759
theorem B1796809 : Blo 980594 1796809 := bstep (se 2 (by rfl) ⟨673803, by rfl⟩ : syracuseStep 1796809 = 1347607) B1347607
theorem B3730157 : Blo 980594 3730157 := bstep (se 3 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 3730157 = 1398809) B1398809
theorem B8743681 : Blo 980594 8743681 := bstep (se 2 (by rfl) ⟨3278880, by rfl⟩ : syracuseStep 8743681 = 6557761) B6557761
theorem B1862443 : Blo 980594 1862443 := bstep (se 1 (by rfl) ⟨1396832, by rfl⟩ : syracuseStep 1862443 = 2793665) B2793665
theorem B4975505 : Blo 980594 4975505 := bstep (se 2 (by rfl) ⟨1865814, by rfl⟩ : syracuseStep 4975505 = 3731629) B3731629
theorem B7465931 : Blo 980594 7465931 := bstep (se 1 (by rfl) ⟨5599448, by rfl⟩ : syracuseStep 7465931 = 11198897) B11198897
theorem B5598173 : Blo 980594 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B1862671 : Blo 980594 1862671 := bstep (se 1 (by rfl) ⟨1397003, by rfl⟩ : syracuseStep 1862671 = 2794007) B2794007
theorem B3730475 : Blo 980594 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B2485363 : Blo 980594 2485363 := bstep (se 1 (by rfl) ⟨1864022, by rfl⟩ : syracuseStep 2485363 = 3728045) B3728045
theorem B8383661 : Blo 980594 8383661 := bstep (se 3 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 8383661 = 3143873) B3143873
theorem B2485505 : Blo 980594 2485505 := bstep (se 2 (by rfl) ⟨932064, by rfl⟩ : syracuseStep 2485505 = 1864129) B1864129
theorem B2485961 : Blo 980594 2485961 := bstep (se 2 (by rfl) ⟨932235, by rfl⟩ : syracuseStep 2485961 = 1864471) B1864471
theorem B1437385 : Blo 980594 1437385 := bstep (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) B1078039
theorem B23949107 : Blo 980594 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B2486315 : Blo 980594 2486315 := bstep (se 1 (by rfl) ⟨1864736, by rfl⟩ : syracuseStep 2486315 = 3729473) B3729473
theorem B1241335 : Blo 980594 1241335 := bstep (se 1 (by rfl) ⟨931001, by rfl⟩ : syracuseStep 1241335 = 1862003) B1862003
theorem B1470905 : Blo 980594 1470905 := bstep (se 2 (by rfl) ⟨551589, by rfl⟩ : syracuseStep 1470905 = 1103179) B1103179
theorem B1470983 : Blo 980594 1470983 := bstep (se 1 (by rfl) ⟨1103237, by rfl⟩ : syracuseStep 1470983 = 2206475) B2206475
theorem B1471019 : Blo 980594 1471019 := bstep (se 1 (by rfl) ⟨1103264, by rfl⟩ : syracuseStep 1471019 = 2206529) B2206529
theorem B1864235 : Blo 980594 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B1241659 : Blo 980594 1241659 := bstep (se 1 (by rfl) ⟨931244, by rfl⟩ : syracuseStep 1241659 = 1862489) B1862489
theorem B1471049 : Blo 980594 1471049 := bstep (se 2 (by rfl) ⟨551643, by rfl⟩ : syracuseStep 1471049 = 1103287) B1103287
theorem B1471163 : Blo 980594 1471163 := bstep (se 1 (by rfl) ⟨1103372, by rfl⟩ : syracuseStep 1471163 = 2206745) B2206745
theorem B1471223 : Blo 980594 1471223 := bstep (se 1 (by rfl) ⟨1103417, by rfl⟩ : syracuseStep 1471223 = 2206835) B2206835
theorem B1471247 : Blo 980594 1471247 := bstep (se 1 (by rfl) ⟨1103435, by rfl⟩ : syracuseStep 1471247 = 2206871) B2206871
theorem B1471289 : Blo 980594 1471289 := bstep (se 2 (by rfl) ⟨551733, by rfl⟩ : syracuseStep 1471289 = 1103467) B1103467
theorem B1471367 : Blo 980594 1471367 := bstep (se 1 (by rfl) ⟨1103525, by rfl⟩ : syracuseStep 1471367 = 2207051) B2207051
theorem B1471403 : Blo 980594 1471403 := bstep (se 1 (by rfl) ⟨1103552, by rfl⟩ : syracuseStep 1471403 = 2207105) B2207105
theorem B1471433 : Blo 980594 1471433 := bstep (se 2 (by rfl) ⟨551787, by rfl⟩ : syracuseStep 1471433 = 1103575) B1103575
theorem B4977611 : Blo 980594 4977611 := bstep (se 1 (by rfl) ⟨3733208, by rfl⟩ : syracuseStep 4977611 = 7466417) B7466417
theorem B2487307 : Blo 980594 2487307 := bstep (se 1 (by rfl) ⟨1865480, by rfl⟩ : syracuseStep 2487307 = 3730961) B3730961
theorem B1242155 : Blo 980594 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B1471547 : Blo 980594 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B1471607 : Blo 980594 1471607 := bstep (se 1 (by rfl) ⟨1103705, by rfl⟩ : syracuseStep 1471607 = 2207411) B2207411
theorem B1471631 : Blo 980594 1471631 := bstep (se 1 (by rfl) ⟨1103723, by rfl⟩ : syracuseStep 1471631 = 2207447) B2207447
theorem B1995923 : Blo 980594 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B2487449 : Blo 980594 2487449 := bstep (se 2 (by rfl) ⟨932793, by rfl⟩ : syracuseStep 2487449 = 1865587) B1865587
theorem B1471673 : Blo 980594 1471673 := bstep (se 2 (by rfl) ⟨551877, by rfl⟩ : syracuseStep 1471673 = 1103755) B1103755
theorem B1701065 : Blo 980594 1701065 := bstep (se 2 (by rfl) ⟨637899, by rfl⟩ : syracuseStep 1701065 = 1275799) B1275799
theorem B1471751 : Blo 980594 1471751 := bstep (se 1 (by rfl) ⟨1103813, by rfl⟩ : syracuseStep 1471751 = 2207627) B2207627
theorem B4977935 : Blo 980594 4977935 := bstep (se 1 (by rfl) ⟨3733451, by rfl⟩ : syracuseStep 4977935 = 7466903) B7466903
theorem B8516897 : Blo 980594 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1471787 : Blo 980594 1471787 := bstep (se 1 (by rfl) ⟨1103840, by rfl⟩ : syracuseStep 1471787 = 2207681) B2207681
theorem B2487611 : Blo 980594 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B1471817 : Blo 980594 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B1471931 : Blo 980594 1471931 := bstep (se 1 (by rfl) ⟨1103948, by rfl⟩ : syracuseStep 1471931 = 2207897) B2207897
theorem B1471991 : Blo 980594 1471991 := bstep (se 1 (by rfl) ⟨1103993, by rfl⟩ : syracuseStep 1471991 = 2207987) B2207987
theorem B8386051 : Blo 980594 8386051 := bstep (se 1 (by rfl) ⟨6289538, by rfl⟩ : syracuseStep 8386051 = 12579077) B12579077
theorem B5600771 : Blo 980594 5600771 := bstep (se 1 (by rfl) ⟨4200578, by rfl⟩ : syracuseStep 5600771 = 8401157) B8401157
theorem B1242631 : Blo 980594 1242631 := bstep (se 1 (by rfl) ⟨931973, by rfl⟩ : syracuseStep 1242631 = 1863947) B1863947
theorem B1472015 : Blo 980594 1472015 := bstep (se 1 (by rfl) ⟨1104011, by rfl⟩ : syracuseStep 1472015 = 2208023) B2208023
theorem B1472057 : Blo 980594 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B980615 : Blo 980594 980615 := bstep (se 1 (by rfl) ⟨735461, by rfl⟩ : syracuseStep 980615 = 1470923) B1470923
theorem B1472135 : Blo 980594 1472135 := bstep (se 1 (by rfl) ⟨1104101, by rfl⟩ : syracuseStep 1472135 = 2208203) B2208203
theorem B980623 : Blo 980594 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B2487955 : Blo 980594 2487955 := bstep (se 1 (by rfl) ⟨1865966, by rfl⟩ : syracuseStep 2487955 = 3731933) B3731933
theorem B1472171 : Blo 980594 1472171 := bstep (se 1 (by rfl) ⟨1104128, by rfl⟩ : syracuseStep 1472171 = 2208257) B2208257
theorem B980667 : Blo 980594 980667 := bstep (se 1 (by rfl) ⟨735500, by rfl⟩ : syracuseStep 980667 = 1471001) B1471001
theorem B3536585 : Blo 980594 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B1472201 : Blo 980594 1472201 := bstep (se 2 (by rfl) ⟨552075, by rfl⟩ : syracuseStep 1472201 = 1104151) B1104151
theorem B980743 : Blo 980594 980743 := bstep (se 1 (by rfl) ⟨735557, by rfl⟩ : syracuseStep 980743 = 1471115) B1471115
theorem B980751 : Blo 980594 980751 := bstep (se 1 (by rfl) ⟨735563, by rfl⟩ : syracuseStep 980751 = 1471127) B1471127
theorem B2488097 : Blo 980594 2488097 := bstep (se 2 (by rfl) ⟨933036, by rfl⟩ : syracuseStep 2488097 = 1866073) B1866073
theorem B980795 : Blo 980594 980795 := bstep (se 1 (by rfl) ⟨735596, by rfl⟩ : syracuseStep 980795 = 1471193) B1471193
theorem B1472315 : Blo 980594 1472315 := bstep (se 1 (by rfl) ⟨1104236, by rfl⟩ : syracuseStep 1472315 = 2208473) B2208473
theorem B3143539 : Blo 980594 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B1472375 : Blo 980594 1472375 := bstep (se 1 (by rfl) ⟨1104281, by rfl⟩ : syracuseStep 1472375 = 2208563) B2208563
theorem B980871 : Blo 980594 980871 := bstep (se 1 (by rfl) ⟨735653, by rfl⟩ : syracuseStep 980871 = 1471307) B1471307
theorem B980879 : Blo 980594 980879 := bstep (se 1 (by rfl) ⟨735659, by rfl⟩ : syracuseStep 980879 = 1471319) B1471319
theorem B1472399 : Blo 980594 1472399 := bstep (se 1 (by rfl) ⟨1104299, by rfl⟩ : syracuseStep 1472399 = 2208599) B2208599
theorem B1472441 : Blo 980594 1472441 := bstep (se 2 (by rfl) ⟨552165, by rfl⟩ : syracuseStep 1472441 = 1104331) B1104331
theorem B980923 : Blo 980594 980923 := bstep (se 1 (by rfl) ⟨735692, by rfl⟩ : syracuseStep 980923 = 1471385) B1471385
theorem B1243127 : Blo 980594 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B980999 : Blo 980594 980999 := bstep (se 1 (by rfl) ⟨735749, by rfl⟩ : syracuseStep 980999 = 1471499) B1471499
theorem B1472519 : Blo 980594 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B981007 : Blo 980594 981007 := bstep (se 1 (by rfl) ⟨735755, by rfl⟩ : syracuseStep 981007 = 1471511) B1471511
theorem B1472555 : Blo 980594 1472555 := bstep (se 1 (by rfl) ⟨1104416, by rfl⟩ : syracuseStep 1472555 = 2208833) B2208833
theorem B981051 : Blo 980594 981051 := bstep (se 1 (by rfl) ⟨735788, by rfl⟩ : syracuseStep 981051 = 1471577) B1471577
theorem B1472585 : Blo 980594 1472585 := bstep (se 2 (by rfl) ⟨552219, by rfl⟩ : syracuseStep 1472585 = 1104439) B1104439
theorem B4192343 : Blo 980594 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B981127 : Blo 980594 981127 := bstep (se 1 (by rfl) ⟨735845, by rfl⟩ : syracuseStep 981127 = 1471691) B1471691
theorem B981135 : Blo 980594 981135 := bstep (se 1 (by rfl) ⟨735851, by rfl⟩ : syracuseStep 981135 = 1471703) B1471703
theorem B1243279 : Blo 980594 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B981179 : Blo 980594 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B1472699 : Blo 980594 1472699 := bstep (se 1 (by rfl) ⟨1104524, by rfl⟩ : syracuseStep 1472699 = 2209049) B2209049
theorem B1865929 : Blo 980594 1865929 := bstep (se 2 (by rfl) ⟨699723, by rfl⟩ : syracuseStep 1865929 = 1399447) B1399447
theorem B1472759 : Blo 980594 1472759 := bstep (se 1 (by rfl) ⟨1104569, by rfl⟩ : syracuseStep 1472759 = 2209139) B2209139
theorem B981255 : Blo 980594 981255 := bstep (se 1 (by rfl) ⟨735941, by rfl⟩ : syracuseStep 981255 = 1471883) B1471883
theorem B981263 : Blo 980594 981263 := bstep (se 1 (by rfl) ⟨735947, by rfl⟩ : syracuseStep 981263 = 1471895) B1471895
theorem B1472783 : Blo 980594 1472783 := bstep (se 1 (by rfl) ⟨1104587, by rfl⟩ : syracuseStep 1472783 = 2209175) B2209175
theorem B1472825 : Blo 980594 1472825 := bstep (se 2 (by rfl) ⟨552309, by rfl⟩ : syracuseStep 1472825 = 1104619) B1104619
theorem B981307 : Blo 980594 981307 := bstep (se 1 (by rfl) ⟨735980, by rfl⟩ : syracuseStep 981307 = 1471961) B1471961
theorem B1243451 : Blo 980594 1243451 := bstep (se 1 (by rfl) ⟨932588, by rfl⟩ : syracuseStep 1243451 = 1865177) B1865177
theorem B2652535 : Blo 980594 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B981383 : Blo 980594 981383 := bstep (se 1 (by rfl) ⟨736037, by rfl⟩ : syracuseStep 981383 = 1472075) B1472075
theorem B1472903 : Blo 980594 1472903 := bstep (se 1 (by rfl) ⟨1104677, by rfl⟩ : syracuseStep 1472903 = 2209355) B2209355
theorem B981391 : Blo 980594 981391 := bstep (se 1 (by rfl) ⟨736043, by rfl⟩ : syracuseStep 981391 = 1472087) B1472087
theorem B1472939 : Blo 980594 1472939 := bstep (se 1 (by rfl) ⟨1104704, by rfl⟩ : syracuseStep 1472939 = 2209409) B2209409
theorem B1571257 : Blo 980594 1571257 := bstep (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) B1178443
theorem B981435 : Blo 980594 981435 := bstep (se 1 (by rfl) ⟨736076, by rfl⟩ : syracuseStep 981435 = 1472153) B1472153
theorem B1472969 : Blo 980594 1472969 := bstep (se 2 (by rfl) ⟨552363, by rfl⟩ : syracuseStep 1472969 = 1104727) B1104727
theorem B981511 : Blo 980594 981511 := bstep (se 1 (by rfl) ⟨736133, by rfl⟩ : syracuseStep 981511 = 1472267) B1472267
theorem B981519 : Blo 980594 981519 := bstep (se 1 (by rfl) ⟨736139, by rfl⟩ : syracuseStep 981519 = 1472279) B1472279
theorem B4717079 : Blo 980594 4717079 := bstep (se 1 (by rfl) ⟨3537809, by rfl⟩ : syracuseStep 4717079 = 7075619) B7075619
theorem B6289949 : Blo 980594 6289949 := bstep (se 3 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 6289949 = 2358731) B2358731
theorem B3734045 : Blo 980594 3734045 := bstep (se 3 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 3734045 = 1400267) B1400267
theorem B1178155 : Blo 980594 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B3734059 : Blo 980594 3734059 := bstep (se 1 (by rfl) ⟨2800544, by rfl⟩ : syracuseStep 3734059 = 5601089) B5601089
theorem B981563 : Blo 980594 981563 := bstep (se 1 (by rfl) ⟨736172, by rfl⟩ : syracuseStep 981563 = 1472345) B1472345
theorem B1473083 : Blo 980594 1473083 := bstep (se 1 (by rfl) ⟨1104812, by rfl⟩ : syracuseStep 1473083 = 2209625) B2209625
theorem B1473143 : Blo 980594 1473143 := bstep (se 1 (by rfl) ⟨1104857, by rfl⟩ : syracuseStep 1473143 = 2209715) B2209715
theorem B981639 : Blo 980594 981639 := bstep (se 1 (by rfl) ⟨736229, by rfl⟩ : syracuseStep 981639 = 1472459) B1472459
theorem B981647 : Blo 980594 981647 := bstep (se 1 (by rfl) ⟨736235, by rfl⟩ : syracuseStep 981647 = 1472471) B1472471
theorem B1473167 : Blo 980594 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B2128531 : Blo 980594 2128531 := bstep (se 1 (by rfl) ⟨1596398, by rfl⟩ : syracuseStep 2128531 = 3192797) B3192797
theorem B1473209 : Blo 980594 1473209 := bstep (se 2 (by rfl) ⟨552453, by rfl⟩ : syracuseStep 1473209 = 1104907) B1104907
theorem B981691 : Blo 980594 981691 := bstep (se 1 (by rfl) ⟨736268, by rfl⟩ : syracuseStep 981691 = 1472537) B1472537
theorem B4979393 : Blo 980594 4979393 := bstep (se 2 (by rfl) ⟨1867272, by rfl⟩ : syracuseStep 4979393 = 3734545) B3734545
theorem B2489089 : Blo 980594 2489089 := bstep (se 2 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 2489089 = 1866817) B1866817
theorem B981767 : Blo 980594 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B1473287 : Blo 980594 1473287 := bstep (se 1 (by rfl) ⟨1104965, by rfl⟩ : syracuseStep 1473287 = 2209931) B2209931
theorem B2358031 : Blo 980594 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B981775 : Blo 980594 981775 := bstep (se 1 (by rfl) ⟨736331, by rfl⟩ : syracuseStep 981775 = 1472663) B1472663
theorem B1768235 : Blo 980594 1768235 := bstep (se 1 (by rfl) ⟨1326176, by rfl⟩ : syracuseStep 1768235 = 2652353) B2652353
theorem B1473323 : Blo 980594 1473323 := bstep (se 1 (by rfl) ⟨1104992, by rfl⟩ : syracuseStep 1473323 = 2209985) B2209985
theorem B981819 : Blo 980594 981819 := bstep (se 1 (by rfl) ⟨736364, by rfl⟩ : syracuseStep 981819 = 1472729) B1472729
theorem B1473353 : Blo 980594 1473353 := bstep (se 2 (by rfl) ⟨552507, by rfl⟩ : syracuseStep 1473353 = 1105015) B1105015
theorem B1571719 : Blo 980594 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B981895 : Blo 980594 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B981903 : Blo 980594 981903 := bstep (se 1 (by rfl) ⟨736427, by rfl⟩ : syracuseStep 981903 = 1472855) B1472855
theorem B981947 : Blo 980594 981947 := bstep (se 1 (by rfl) ⟨736460, by rfl⟩ : syracuseStep 981947 = 1472921) B1472921
theorem B1473467 : Blo 980594 1473467 := bstep (se 1 (by rfl) ⟨1105100, by rfl⟩ : syracuseStep 1473467 = 2210201) B2210201
theorem B1473527 : Blo 980594 1473527 := bstep (se 1 (by rfl) ⟨1105145, by rfl⟩ : syracuseStep 1473527 = 2210291) B2210291
theorem B982023 : Blo 980594 982023 := bstep (se 1 (by rfl) ⟨736517, by rfl⟩ : syracuseStep 982023 = 1473035) B1473035
theorem B982031 : Blo 980594 982031 := bstep (se 1 (by rfl) ⟨736523, by rfl⟩ : syracuseStep 982031 = 1473047) B1473047
theorem B1473551 : Blo 980594 1473551 := bstep (se 1 (by rfl) ⟨1105163, by rfl⟩ : syracuseStep 1473551 = 2210327) B2210327
theorem B1473593 : Blo 980594 1473593 := bstep (se 2 (by rfl) ⟨552597, by rfl⟩ : syracuseStep 1473593 = 1105195) B1105195
theorem B982075 : Blo 980594 982075 := bstep (se 1 (by rfl) ⟨736556, by rfl⟩ : syracuseStep 982075 = 1473113) B1473113
theorem B1571975 : Blo 980594 1571975 := bstep (se 1 (by rfl) ⟨1178981, by rfl⟩ : syracuseStep 1571975 = 2357963) B2357963
theorem B982151 : Blo 980594 982151 := bstep (se 1 (by rfl) ⟨736613, by rfl⟩ : syracuseStep 982151 = 1473227) B1473227
theorem B1473671 : Blo 980594 1473671 := bstep (se 1 (by rfl) ⟨1105253, by rfl⟩ : syracuseStep 1473671 = 2210507) B2210507
theorem B982159 : Blo 980594 982159 := bstep (se 1 (by rfl) ⟨736619, by rfl⟩ : syracuseStep 982159 = 1473239) B1473239
theorem B28277909 : Blo 980594 28277909 := bstep (se 6 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 28277909 = 1325527) B1325527
theorem B2653337 : Blo 980594 2653337 := bstep (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) B1990003
theorem B1473707 : Blo 980594 1473707 := bstep (se 1 (by rfl) ⟨1105280, by rfl⟩ : syracuseStep 1473707 = 2210561) B2210561
theorem B982203 : Blo 980594 982203 := bstep (se 1 (by rfl) ⟨736652, by rfl⟩ : syracuseStep 982203 = 1473305) B1473305
theorem B4717769 : Blo 980594 4717769 := bstep (se 2 (by rfl) ⟨1769163, by rfl⟩ : syracuseStep 4717769 = 3538327) B3538327
theorem B1473737 : Blo 980594 1473737 := bstep (se 2 (by rfl) ⟨552651, by rfl⟩ : syracuseStep 1473737 = 1105303) B1105303
theorem B982279 : Blo 980594 982279 := bstep (se 1 (by rfl) ⟨736709, by rfl⟩ : syracuseStep 982279 = 1473419) B1473419
theorem B1244423 : Blo 980594 1244423 := bstep (se 1 (by rfl) ⟨933317, by rfl⟩ : syracuseStep 1244423 = 1866635) B1866635
theorem B982287 : Blo 980594 982287 := bstep (se 1 (by rfl) ⟨736715, by rfl⟩ : syracuseStep 982287 = 1473431) B1473431
theorem B14351675 : Blo 980594 14351675 := bstep (se 1 (by rfl) ⟨10763756, by rfl⟩ : syracuseStep 14351675 = 21527513) B21527513
theorem B982331 : Blo 980594 982331 := bstep (se 1 (by rfl) ⟨736748, by rfl⟩ : syracuseStep 982331 = 1473497) B1473497
theorem B1473851 : Blo 980594 1473851 := bstep (se 1 (by rfl) ⟨1105388, by rfl⟩ : syracuseStep 1473851 = 2210777) B2210777
theorem B2391383 : Blo 980594 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B2489687 : Blo 980594 2489687 := bstep (se 1 (by rfl) ⟨1867265, by rfl⟩ : syracuseStep 2489687 = 3734531) B3734531
theorem B1473911 : Blo 980594 1473911 := bstep (se 1 (by rfl) ⟨1105433, by rfl⟩ : syracuseStep 1473911 = 2210867) B2210867
theorem B982407 : Blo 980594 982407 := bstep (se 1 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 982407 = 1473611) B1473611
theorem B982415 : Blo 980594 982415 := bstep (se 1 (by rfl) ⟨736811, by rfl⟩ : syracuseStep 982415 = 1473623) B1473623
theorem B1473935 : Blo 980594 1473935 := bstep (se 1 (by rfl) ⟨1105451, by rfl⟩ : syracuseStep 1473935 = 2210903) B2210903
theorem B1473977 : Blo 980594 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B982459 : Blo 980594 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B982535 : Blo 980594 982535 := bstep (se 1 (by rfl) ⟨736901, by rfl⟩ : syracuseStep 982535 = 1473803) B1473803
theorem B1474055 : Blo 980594 1474055 := bstep (se 1 (by rfl) ⟨1105541, by rfl⟩ : syracuseStep 1474055 = 2211083) B2211083
theorem B982543 : Blo 980594 982543 := bstep (se 1 (by rfl) ⟨736907, by rfl⟩ : syracuseStep 982543 = 1473815) B1473815
theorem B1474091 : Blo 980594 1474091 := bstep (se 1 (by rfl) ⟨1105568, by rfl⟩ : syracuseStep 1474091 = 2211137) B2211137
theorem B2489899 : Blo 980594 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B11206187 : Blo 980594 11206187 := bstep (se 1 (by rfl) ⟨8404640, by rfl⟩ : syracuseStep 11206187 = 16809281) B16809281
theorem B982587 : Blo 980594 982587 := bstep (se 1 (by rfl) ⟨736940, by rfl⟩ : syracuseStep 982587 = 1473881) B1473881
theorem B1474121 : Blo 980594 1474121 := bstep (se 2 (by rfl) ⟨552795, by rfl⟩ : syracuseStep 1474121 = 1105591) B1105591
theorem B982663 : Blo 980594 982663 := bstep (se 1 (by rfl) ⟨736997, by rfl⟩ : syracuseStep 982663 = 1473995) B1473995
theorem B982671 : Blo 980594 982671 := bstep (se 1 (by rfl) ⟨737003, by rfl⟩ : syracuseStep 982671 = 1474007) B1474007
theorem B2490041 : Blo 980594 2490041 := bstep (se 2 (by rfl) ⟨933765, by rfl⟩ : syracuseStep 2490041 = 1867531) B1867531
theorem B982715 : Blo 980594 982715 := bstep (se 1 (by rfl) ⟨737036, by rfl⟩ : syracuseStep 982715 = 1474073) B1474073
theorem B1474235 : Blo 980594 1474235 := bstep (se 1 (by rfl) ⟨1105676, by rfl⟩ : syracuseStep 1474235 = 2211353) B2211353
theorem B1474295 : Blo 980594 1474295 := bstep (se 1 (by rfl) ⟨1105721, by rfl⟩ : syracuseStep 1474295 = 2211443) B2211443
theorem B982791 : Blo 980594 982791 := bstep (se 1 (by rfl) ⟨737093, by rfl⟩ : syracuseStep 982791 = 1474187) B1474187
theorem B3538703 : Blo 980594 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B982799 : Blo 980594 982799 := bstep (se 1 (by rfl) ⟨737099, by rfl⟩ : syracuseStep 982799 = 1474199) B1474199
theorem B1474319 : Blo 980594 1474319 := bstep (se 1 (by rfl) ⟨1105739, by rfl⟩ : syracuseStep 1474319 = 2211479) B2211479
theorem B2391851 : Blo 980594 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B26935091 : Blo 980594 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B1474361 : Blo 980594 1474361 := bstep (se 2 (by rfl) ⟨552885, by rfl⟩ : syracuseStep 1474361 = 1105771) B1105771
theorem B982843 : Blo 980594 982843 := bstep (se 1 (by rfl) ⟨737132, by rfl⟩ : syracuseStep 982843 = 1474265) B1474265
theorem B982919 : Blo 980594 982919 := bstep (se 1 (by rfl) ⟨737189, by rfl⟩ : syracuseStep 982919 = 1474379) B1474379
theorem B1474439 : Blo 980594 1474439 := bstep (se 1 (by rfl) ⟨1105829, by rfl⟩ : syracuseStep 1474439 = 2211659) B2211659
theorem B982927 : Blo 980594 982927 := bstep (se 1 (by rfl) ⟨737195, by rfl⟩ : syracuseStep 982927 = 1474391) B1474391
theorem B1245071 : Blo 980594 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B10092451 : Blo 980594 10092451 := bstep (se 1 (by rfl) ⟨7569338, by rfl⟩ : syracuseStep 10092451 = 15138677) B15138677
theorem B1474475 : Blo 980594 1474475 := bstep (se 1 (by rfl) ⟨1105856, by rfl⟩ : syracuseStep 1474475 = 2211713) B2211713
theorem B982971 : Blo 980594 982971 := bstep (se 1 (by rfl) ⟨737228, by rfl⟩ : syracuseStep 982971 = 1474457) B1474457
theorem B1474505 : Blo 980594 1474505 := bstep (se 2 (by rfl) ⟨552939, by rfl⟩ : syracuseStep 1474505 = 1105879) B1105879
theorem B4980689 : Blo 980594 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B983079 : Blo 980594 983079 := bstep (se 1 (by rfl) ⟨737309, by rfl⟩ : syracuseStep 983079 = 1474619) B1474619
theorem B1245223 : Blo 980594 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B983119 : Blo 980594 983119 := bstep (se 1 (by rfl) ⟨737339, by rfl⟩ : syracuseStep 983119 = 1474679) B1474679
theorem B983135 : Blo 980594 983135 := bstep (se 1 (by rfl) ⟨737351, by rfl⟩ : syracuseStep 983135 = 1474703) B1474703
theorem B1867873 : Blo 980594 1867873 := bstep (se 2 (by rfl) ⟨700452, by rfl⟩ : syracuseStep 1867873 = 1400905) B1400905
theorem B4980851 : Blo 980594 4980851 := bstep (se 1 (by rfl) ⟨3735638, by rfl⟩ : syracuseStep 4980851 = 7471277) B7471277
theorem B983163 : Blo 980594 983163 := bstep (se 1 (by rfl) ⟨737372, by rfl⟩ : syracuseStep 983163 = 1474745) B1474745
theorem B983215 : Blo 980594 983215 := bstep (se 1 (by rfl) ⟨737411, by rfl⟩ : syracuseStep 983215 = 1474823) B1474823
theorem B983239 : Blo 980594 983239 := bstep (se 1 (by rfl) ⟨737429, by rfl⟩ : syracuseStep 983239 = 1474859) B1474859
theorem B1769683 : Blo 980594 1769683 := bstep (se 1 (by rfl) ⟨1327262, by rfl⟩ : syracuseStep 1769683 = 2654525) B2654525
theorem B983259 : Blo 980594 983259 := bstep (se 1 (by rfl) ⟨737444, by rfl⟩ : syracuseStep 983259 = 1474889) B1474889
theorem B4260107 : Blo 980594 4260107 := bstep (se 1 (by rfl) ⟨3195080, by rfl⟩ : syracuseStep 4260107 = 6390161) B6390161
theorem B983335 : Blo 980594 983335 := bstep (se 1 (by rfl) ⟨737501, by rfl⟩ : syracuseStep 983335 = 1475003) B1475003
theorem B983375 : Blo 980594 983375 := bstep (se 1 (by rfl) ⟨737531, by rfl⟩ : syracuseStep 983375 = 1475063) B1475063
theorem B983391 : Blo 980594 983391 := bstep (se 1 (by rfl) ⟨737543, by rfl⟩ : syracuseStep 983391 = 1475087) B1475087
theorem B3309929 : Blo 980594 3309929 := bstep (se 2 (by rfl) ⟨1241223, by rfl⟩ : syracuseStep 3309929 = 2482447) B2482447
theorem B1245547 : Blo 980594 1245547 := bstep (se 1 (by rfl) ⟨934160, by rfl⟩ : syracuseStep 1245547 = 1868321) B1868321
theorem B983419 : Blo 980594 983419 := bstep (se 1 (by rfl) ⟨737564, by rfl⟩ : syracuseStep 983419 = 1475129) B1475129
theorem B1474991 : Blo 980594 1474991 := bstep (se 1 (by rfl) ⟨1106243, by rfl⟩ : syracuseStep 1474991 = 2212487) B2212487
theorem B983471 : Blo 980594 983471 := bstep (se 1 (by rfl) ⟨737603, by rfl⟩ : syracuseStep 983471 = 1475207) B1475207
theorem B983495 : Blo 980594 983495 := bstep (se 1 (by rfl) ⟨737621, by rfl⟩ : syracuseStep 983495 = 1475243) B1475243
theorem B983515 : Blo 980594 983515 := bstep (se 1 (by rfl) ⟨737636, by rfl⟩ : syracuseStep 983515 = 1475273) B1475273
theorem B1475081 : Blo 980594 1475081 := bstep (se 2 (by rfl) ⟨553155, by rfl⟩ : syracuseStep 1475081 = 1106311) B1106311
theorem B5964313 : Blo 980594 5964313 := bstep (se 2 (by rfl) ⟨2236617, by rfl⟩ : syracuseStep 5964313 = 4473235) B4473235
theorem B1475111 : Blo 980594 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B983591 : Blo 980594 983591 := bstep (se 1 (by rfl) ⟨737693, by rfl⟩ : syracuseStep 983591 = 1475387) B1475387
theorem B983631 : Blo 980594 983631 := bstep (se 1 (by rfl) ⟨737723, by rfl⟩ : syracuseStep 983631 = 1475447) B1475447
theorem B1245775 : Blo 980594 1245775 := bstep (se 1 (by rfl) ⟨934331, by rfl⟩ : syracuseStep 1245775 = 1868663) B1868663
theorem B983647 : Blo 980594 983647 := bstep (se 1 (by rfl) ⟨737735, by rfl⟩ : syracuseStep 983647 = 1475471) B1475471
theorem B1475195 : Blo 980594 1475195 := bstep (se 1 (by rfl) ⟨1106396, by rfl⟩ : syracuseStep 1475195 = 2212793) B2212793
theorem B983675 : Blo 980594 983675 := bstep (se 1 (by rfl) ⟨737756, by rfl⟩ : syracuseStep 983675 = 1475513) B1475513
theorem B4260487 : Blo 980594 4260487 := bstep (se 1 (by rfl) ⟨3195365, by rfl⟩ : syracuseStep 4260487 = 6390731) B6390731
theorem B983727 : Blo 980594 983727 := bstep (se 1 (by rfl) ⟨737795, by rfl⟩ : syracuseStep 983727 = 1475591) B1475591
theorem B983751 : Blo 980594 983751 := bstep (se 1 (by rfl) ⟨737813, by rfl⟩ : syracuseStep 983751 = 1475627) B1475627
theorem B983771 : Blo 980594 983771 := bstep (se 1 (by rfl) ⟨737828, by rfl⟩ : syracuseStep 983771 = 1475657) B1475657
theorem B1475321 : Blo 980594 1475321 := bstep (se 2 (by rfl) ⟨553245, by rfl⟩ : syracuseStep 1475321 = 1106491) B1106491
theorem B983847 : Blo 980594 983847 := bstep (se 1 (by rfl) ⟨737885, by rfl⟩ : syracuseStep 983847 = 1475771) B1475771
theorem B3146539 : Blo 980594 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B4195145 : Blo 980594 4195145 := bstep (se 2 (by rfl) ⟨1573179, by rfl⟩ : syracuseStep 4195145 = 3146359) B3146359
theorem B983887 : Blo 980594 983887 := bstep (se 1 (by rfl) ⟨737915, by rfl⟩ : syracuseStep 983887 = 1475831) B1475831
theorem B1475423 : Blo 980594 1475423 := bstep (se 1 (by rfl) ⟨1106567, by rfl⟩ : syracuseStep 1475423 = 2213135) B2213135
theorem B983903 : Blo 980594 983903 := bstep (se 1 (by rfl) ⟨737927, by rfl⟩ : syracuseStep 983903 = 1475855) B1475855
theorem B1475435 : Blo 980594 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B3146615 : Blo 980594 3146615 := bstep (se 1 (by rfl) ⟨2359961, by rfl⟩ : syracuseStep 3146615 = 4719923) B4719923
theorem B983931 : Blo 980594 983931 := bstep (se 1 (by rfl) ⟨737948, by rfl⟩ : syracuseStep 983931 = 1475897) B1475897
theorem B1704847 : Blo 980594 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B983983 : Blo 980594 983983 := bstep (se 1 (by rfl) ⟨737987, by rfl⟩ : syracuseStep 983983 = 1475975) B1475975
theorem B3310523 : Blo 980594 3310523 := bstep (se 1 (by rfl) ⟨2482892, by rfl⟩ : syracuseStep 3310523 = 4965785) B4965785
theorem B984007 : Blo 980594 984007 := bstep (se 1 (by rfl) ⟨738005, by rfl⟩ : syracuseStep 984007 = 1476011) B1476011
theorem B984027 : Blo 980594 984027 := bstep (se 1 (by rfl) ⟨738020, by rfl⟩ : syracuseStep 984027 = 1476041) B1476041
theorem B11207645 : Blo 980594 11207645 := bstep (se 3 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 11207645 = 4202867) B4202867
theorem B1868807 : Blo 980594 1868807 := bstep (se 1 (by rfl) ⟨1401605, by rfl⟩ : syracuseStep 1868807 = 2803211) B2803211
theorem B984103 : Blo 980594 984103 := bstep (se 1 (by rfl) ⟨738077, by rfl⟩ : syracuseStep 984103 = 1476155) B1476155
theorem B3146809 : Blo 980594 3146809 := bstep (se 2 (by rfl) ⟨1180053, by rfl⟩ : syracuseStep 3146809 = 2360107) B2360107
theorem B1475663 : Blo 980594 1475663 := bstep (se 1 (by rfl) ⟨1106747, by rfl⟩ : syracuseStep 1475663 = 2213495) B2213495
theorem B984143 : Blo 980594 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B984159 : Blo 980594 984159 := bstep (se 1 (by rfl) ⟨738119, by rfl⟩ : syracuseStep 984159 = 1476239) B1476239
theorem B984187 : Blo 980594 984187 := bstep (se 1 (by rfl) ⟨738140, by rfl⟩ : syracuseStep 984187 = 1476281) B1476281
theorem B984239 : Blo 980594 984239 := bstep (se 1 (by rfl) ⟨738179, by rfl⟩ : syracuseStep 984239 = 1476359) B1476359
theorem B1475783 : Blo 980594 1475783 := bstep (se 1 (by rfl) ⟨1106837, by rfl⟩ : syracuseStep 1475783 = 2213675) B2213675
theorem B984263 : Blo 980594 984263 := bstep (se 1 (by rfl) ⟨738197, by rfl⟩ : syracuseStep 984263 = 1476395) B1476395
theorem B984283 : Blo 980594 984283 := bstep (se 1 (by rfl) ⟨738212, by rfl⟩ : syracuseStep 984283 = 1476425) B1476425
theorem B984359 : Blo 980594 984359 := bstep (se 1 (by rfl) ⟨738269, by rfl⟩ : syracuseStep 984359 = 1476539) B1476539
theorem B984399 : Blo 980594 984399 := bstep (se 1 (by rfl) ⟨738299, by rfl⟩ : syracuseStep 984399 = 1476599) B1476599
theorem B984415 : Blo 980594 984415 := bstep (se 1 (by rfl) ⟨738311, by rfl⟩ : syracuseStep 984415 = 1476623) B1476623
theorem B1475945 : Blo 980594 1475945 := bstep (se 2 (by rfl) ⟨553479, by rfl⟩ : syracuseStep 1475945 = 1106959) B1106959
theorem B984443 : Blo 980594 984443 := bstep (se 1 (by rfl) ⟨738332, by rfl⟩ : syracuseStep 984443 = 1476665) B1476665
theorem B3736961 : Blo 980594 3736961 := bstep (se 2 (by rfl) ⟨1401360, by rfl⟩ : syracuseStep 3736961 = 2802721) B2802721
theorem B3736975 : Blo 980594 3736975 := bstep (se 1 (by rfl) ⟨2802731, by rfl⟩ : syracuseStep 3736975 = 5605463) B5605463
theorem B984495 : Blo 980594 984495 := bstep (se 1 (by rfl) ⟨738371, by rfl⟩ : syracuseStep 984495 = 1476743) B1476743
theorem B1476023 : Blo 980594 1476023 := bstep (se 1 (by rfl) ⟨1107017, by rfl⟩ : syracuseStep 1476023 = 2214035) B2214035
theorem B984519 : Blo 980594 984519 := bstep (se 1 (by rfl) ⟨738389, by rfl⟩ : syracuseStep 984519 = 1476779) B1476779
theorem B1476059 : Blo 980594 1476059 := bstep (se 1 (by rfl) ⟨1107044, by rfl⟩ : syracuseStep 1476059 = 2214089) B2214089
theorem B984539 : Blo 980594 984539 := bstep (se 1 (by rfl) ⟨738404, by rfl⟩ : syracuseStep 984539 = 1476809) B1476809
theorem B11175569 : Blo 980594 11175569 := bstep (se 2 (by rfl) ⟨4190838, by rfl⟩ : syracuseStep 11175569 = 8381677) B8381677
theorem B4982471 : Blo 980594 4982471 := bstep (se 1 (by rfl) ⟨3736853, by rfl⟩ : syracuseStep 4982471 = 7473707) B7473707
theorem B5310173 : Blo 980594 5310173 := bstep (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) B1991315
theorem B1476527 : Blo 980594 1476527 := bstep (se 1 (by rfl) ⟨1107395, by rfl⟩ : syracuseStep 1476527 = 2214791) B2214791
theorem B1476617 : Blo 980594 1476617 := bstep (se 2 (by rfl) ⟨553731, by rfl⟩ : syracuseStep 1476617 = 1107463) B1107463
theorem B1476647 : Blo 980594 1476647 := bstep (se 1 (by rfl) ⟨1107485, by rfl⟩ : syracuseStep 1476647 = 2214971) B2214971
theorem B1476731 : Blo 980594 1476731 := bstep (se 1 (by rfl) ⟨1107548, by rfl⟩ : syracuseStep 1476731 = 2215097) B2215097
theorem B1476857 : Blo 980594 1476857 := bstep (se 2 (by rfl) ⟨553821, by rfl⟩ : syracuseStep 1476857 = 1107643) B1107643
theorem B9439537 : Blo 980594 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B6293821 : Blo 980594 6293821 := bstep (se 3 (by rfl) ⟨1180091, by rfl⟩ : syracuseStep 6293821 = 2360183) B2360183
theorem B2099675 : Blo 980594 2099675 := bstep (se 1 (by rfl) ⟨1574756, by rfl⟩ : syracuseStep 2099675 = 3149513) B3149513
theorem B2361953 : Blo 980594 2361953 := bstep (se 2 (by rfl) ⟨885732, by rfl⟩ : syracuseStep 2361953 = 1771465) B1771465
theorem B3312251 : Blo 980594 3312251 := bstep (se 1 (by rfl) ⟨2484188, by rfl⟩ : syracuseStep 3312251 = 4968377) B4968377
theorem B3738251 : Blo 980594 3738251 := bstep (se 1 (by rfl) ⟨2803688, by rfl⟩ : syracuseStep 3738251 = 5607377) B5607377
theorem B3312413 : Blo 980594 3312413 := bstep (se 3 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 3312413 = 1242155) B1242155
theorem B5606603 : Blo 980594 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B3313115 : Blo 980594 3313115 := bstep (se 1 (by rfl) ⟨2484836, by rfl⟩ : syracuseStep 3313115 = 4969673) B4969673
theorem B3149371 : Blo 980594 3149371 := bstep (se 1 (by rfl) ⟨2362028, by rfl⟩ : syracuseStep 3149371 = 4724057) B4724057
theorem B16813655 : Blo 980594 16813655 := bstep (se 1 (by rfl) ⟨12610241, by rfl⟩ : syracuseStep 16813655 = 25220483) B25220483
theorem B2395745 : Blo 980594 2395745 := bstep (se 2 (by rfl) ⟨898404, by rfl⟩ : syracuseStep 2395745 = 1796809) B1796809
theorem B3149435 : Blo 980594 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B2101153 : Blo 980594 2101153 := bstep (se 2 (by rfl) ⟨787932, by rfl⟩ : syracuseStep 2101153 = 1575865) B1575865
theorem B6295589 : Blo 980594 6295589 := bstep (se 4 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 6295589 = 1180423) B1180423
theorem B10621043 : Blo 980594 10621043 := bstep (se 1 (by rfl) ⟨7965782, by rfl⟩ : syracuseStep 10621043 = 15931565) B15931565
theorem B3313817 : Blo 980594 3313817 := bstep (se 2 (by rfl) ⟨1242681, by rfl⟩ : syracuseStep 3313817 = 2485363) B2485363
theorem B3543851 : Blo 980594 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B14160689 : Blo 980594 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B2102203 : Blo 980594 2102203 := bstep (se 1 (by rfl) ⟨1576652, by rfl⟩ : syracuseStep 2102203 = 3153305) B3153305
theorem B3315005 : Blo 980594 3315005 := bstep (se 3 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 3315005 = 1243127) B1243127
theorem B7476623 : Blo 980594 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B12916235 : Blo 980594 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B14358059 : Blo 980594 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B2266987 : Blo 980594 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B3315869 : Blo 980594 3315869 := bstep (se 3 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 3315869 = 1243451) B1243451
theorem B3316409 : Blo 980594 3316409 := bstep (se 2 (by rfl) ⟨1243653, by rfl⟩ : syracuseStep 3316409 = 2487307) B2487307
theorem B3775187 : Blo 980594 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B2661295 : Blo 980594 2661295 := bstep (se 1 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 2661295 = 3991943) B3991943
theorem B3317003 : Blo 980594 3317003 := bstep (se 1 (by rfl) ⟨2487752, by rfl⟩ : syracuseStep 3317003 = 4975505) B4975505
theorem B9706787 : Blo 980594 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B11181401 : Blo 980594 11181401 := bstep (se 2 (by rfl) ⟨4193025, by rfl⟩ : syracuseStep 11181401 = 8386051) B8386051
theorem B3317273 : Blo 980594 3317273 := bstep (se 2 (by rfl) ⟨1243977, by rfl⟩ : syracuseStep 3317273 = 2487955) B2487955
theorem B15966071 : Blo 980594 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B8069665 : Blo 980594 8069665 := bstep (se 2 (by rfl) ⟨3026124, by rfl⟩ : syracuseStep 8069665 = 6052249) B6052249
theorem B3318407 : Blo 980594 3318407 := bstep (se 1 (by rfl) ⟨2488805, by rfl⟩ : syracuseStep 3318407 = 4977611) B4977611
theorem B3318461 : Blo 980594 3318461 := bstep (se 3 (by rfl) ⟨622211, by rfl⟩ : syracuseStep 3318461 = 1244423) B1244423
theorem B3318623 : Blo 980594 3318623 := bstep (se 1 (by rfl) ⟨2488967, by rfl⟩ : syracuseStep 3318623 = 4977935) B4977935
theorem B5677931 : Blo 980594 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B3318785 : Blo 980594 3318785 := bstep (se 2 (by rfl) ⟨1244544, by rfl⟩ : syracuseStep 3318785 = 2489089) B2489089
theorem B53880025 : Blo 980594 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B5383415 : Blo 980594 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B2794895 : Blo 980594 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B8496737 : Blo 980594 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B3319595 : Blo 980594 3319595 := bstep (se 1 (by rfl) ⟨2489696, by rfl⟩ : syracuseStep 3319595 = 4979393) B4979393
theorem B7087931 : Blo 980594 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B3319865 : Blo 980594 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B18851939 : Blo 980594 18851939 := bstep (se 1 (by rfl) ⟨14138954, by rfl⟩ : syracuseStep 18851939 = 28277909) B28277909
theorem B3320189 : Blo 980594 3320189 := bstep (se 3 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 3320189 = 1245071) B1245071
theorem B4205191 : Blo 980594 4205191 := bstep (se 1 (by rfl) ⟨3153893, by rfl⟩ : syracuseStep 4205191 = 6307787) B6307787
theorem B3320459 : Blo 980594 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B11938549 : Blo 980594 11938549 := bstep (se 5 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 11938549 = 1119239) B1119239
theorem B2206457 : Blo 980594 2206457 := bstep (se 2 (by rfl) ⟨827421, by rfl⟩ : syracuseStep 2206457 = 1654843) B1654843
theorem B1682363 : Blo 980594 1682363 := bstep (se 1 (by rfl) ⟨1261772, by rfl⟩ : syracuseStep 1682363 = 2523545) B2523545
theorem B2206727 : Blo 980594 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B2206799 : Blo 980594 2206799 := bstep (se 1 (by rfl) ⟨1655099, by rfl⟩ : syracuseStep 2206799 = 3310199) B3310199
theorem B7449893 : Blo 980594 7449893 := bstep (se 4 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 7449893 = 1396855) B1396855
theorem B51064123 : Blo 980594 51064123 := bstep (se 1 (by rfl) ⟨38298092, by rfl⟩ : syracuseStep 51064123 = 76596185) B76596185
theorem B14167385 : Blo 980594 14167385 := bstep (se 2 (by rfl) ⟨5312769, by rfl⟩ : syracuseStep 14167385 = 10625539) B10625539
theorem B65514865 : Blo 980594 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B2207195 : Blo 980594 2207195 := bstep (se 1 (by rfl) ⟨1655396, by rfl⟩ : syracuseStep 2207195 = 3310793) B3310793
theorem B3321377 : Blo 980594 3321377 := bstep (se 2 (by rfl) ⟨1245516, by rfl⟩ : syracuseStep 3321377 = 2491033) B2491033
theorem B6303329 : Blo 980594 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B6303379 : Blo 980594 6303379 := bstep (se 1 (by rfl) ⟨4727534, by rfl⟩ : syracuseStep 6303379 = 9455069) B9455069
theorem B3321593 : Blo 980594 3321593 := bstep (se 2 (by rfl) ⟨1245597, by rfl⟩ : syracuseStep 3321593 = 2491195) B2491195
theorem B2207663 : Blo 980594 2207663 := bstep (se 1 (by rfl) ⟨1655747, by rfl⟩ : syracuseStep 2207663 = 3311495) B3311495
theorem B3321863 : Blo 980594 3321863 := bstep (se 1 (by rfl) ⟨2491397, by rfl⟩ : syracuseStep 3321863 = 4982795) B4982795
theorem B3321971 : Blo 980594 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B2207915 : Blo 980594 2207915 := bstep (se 1 (by rfl) ⟨1655936, by rfl⟩ : syracuseStep 2207915 = 3311873) B3311873
theorem B1683703 : Blo 980594 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B3322241 : Blo 980594 3322241 := bstep (se 2 (by rfl) ⟨1245840, by rfl⟩ : syracuseStep 3322241 = 2491681) B2491681
theorem B2830835 : Blo 980594 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B3355145 : Blo 980594 3355145 := bstep (se 2 (by rfl) ⟨1258179, by rfl⟩ : syracuseStep 3355145 = 2516359) B2516359
theorem B2208455 : Blo 980594 2208455 := bstep (se 1 (by rfl) ⟨1656341, by rfl⟩ : syracuseStep 2208455 = 3312683) B3312683
theorem B3781559 : Blo 980594 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B5977061 : Blo 980594 5977061 := bstep (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) B1120699
theorem B3028367 : Blo 980594 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B9450917 : Blo 980594 9450917 := bstep (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) B1772047
theorem B7091621 : Blo 980594 7091621 := bstep (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) B1329679
theorem B2209319 : Blo 980594 2209319 := bstep (se 1 (by rfl) ⟨1656989, by rfl⟩ : syracuseStep 2209319 = 3313979) B3313979
theorem B2209643 : Blo 980594 2209643 := bstep (se 1 (by rfl) ⟨1657232, by rfl⟩ : syracuseStep 2209643 = 3314465) B3314465
theorem B2209697 : Blo 980594 2209697 := bstep (se 2 (by rfl) ⟨828636, by rfl⟩ : syracuseStep 2209697 = 1657273) B1657273
theorem B2799623 : Blo 980594 2799623 := bstep (se 1 (by rfl) ⟨2099717, by rfl⟩ : syracuseStep 2799623 = 4199435) B4199435
theorem B7977037 : Blo 980594 7977037 := bstep (se 3 (by rfl) ⟨1495694, by rfl⟩ : syracuseStep 7977037 = 2991389) B2991389
theorem B2210039 : Blo 980594 2210039 := bstep (se 1 (by rfl) ⟨1657529, by rfl⟩ : syracuseStep 2210039 = 3315059) B3315059
theorem B40319531 : Blo 980594 40319531 := bstep (se 1 (by rfl) ⟨30239648, by rfl⟩ : syracuseStep 40319531 = 60479297) B60479297
theorem B5978909 : Blo 980594 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B2210633 : Blo 980594 2210633 := bstep (se 2 (by rfl) ⟨828987, by rfl⟩ : syracuseStep 2210633 = 1657975) B1657975
theorem B3980215 : Blo 980594 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B6732953 : Blo 980594 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B3980555 : Blo 980594 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B1916513 : Blo 980594 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B2211425 : Blo 980594 2211425 := bstep (se 2 (by rfl) ⟨829284, by rfl⟩ : syracuseStep 2211425 = 1658569) B1658569
theorem B12599171 : Blo 980594 12599171 := bstep (se 1 (by rfl) ⟨9449378, by rfl⟩ : syracuseStep 12599171 = 18898757) B18898757
theorem B2211767 : Blo 980594 2211767 := bstep (se 1 (by rfl) ⟨1658825, by rfl⟩ : syracuseStep 2211767 = 3317651) B3317651
theorem B5980175 : Blo 980594 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1654823 : Blo 980594 1654823 := bstep (se 1 (by rfl) ⟨1241117, by rfl⟩ : syracuseStep 1654823 = 2482235) B2482235
theorem B10076237 : Blo 980594 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B1655113 : Blo 980594 1655113 := bstep (se 2 (by rfl) ⟨620667, by rfl⟩ : syracuseStep 1655113 = 1241335) B1241335
theorem B1655147 : Blo 980594 1655147 := bstep (se 1 (by rfl) ⟨1241360, by rfl⟩ : syracuseStep 1655147 = 2482721) B2482721
theorem B2212361 : Blo 980594 2212361 := bstep (se 2 (by rfl) ⟨829635, by rfl⟩ : syracuseStep 2212361 = 1659271) B1659271
theorem B2802185 : Blo 980594 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B2048591 : Blo 980594 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B1655545 : Blo 980594 1655545 := bstep (se 2 (by rfl) ⟨620829, by rfl⟩ : syracuseStep 1655545 = 1241659) B1241659
theorem B3195677 : Blo 980594 3195677 := bstep (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) B1198379
theorem B2212703 : Blo 980594 2212703 := bstep (se 1 (by rfl) ⟨1659527, by rfl⟩ : syracuseStep 2212703 = 3319055) B3319055
theorem B2802539 : Blo 980594 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B1655815 : Blo 980594 1655815 := bstep (se 1 (by rfl) ⟨1241861, by rfl⟩ : syracuseStep 1655815 = 2483723) B2483723
theorem B2212883 : Blo 980594 2212883 := bstep (se 1 (by rfl) ⟨1659662, by rfl⟩ : syracuseStep 2212883 = 3319325) B3319325
theorem B4965623 : Blo 980594 4965623 := bstep (se 1 (by rfl) ⟨3724217, by rfl⟩ : syracuseStep 4965623 = 7448435) B7448435
theorem B2213225 : Blo 980594 2213225 := bstep (se 2 (by rfl) ⟨829959, by rfl⟩ : syracuseStep 2213225 = 1659919) B1659919
theorem B1263023 : Blo 980594 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B1656247 : Blo 980594 1656247 := bstep (se 1 (by rfl) ⟨1242185, by rfl⟩ : syracuseStep 1656247 = 2484371) B2484371
theorem B2803187 : Blo 980594 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B1656443 : Blo 980594 1656443 := bstep (se 1 (by rfl) ⟨1242332, by rfl⟩ : syracuseStep 1656443 = 2484665) B2484665
theorem B4966109 : Blo 980594 4966109 := bstep (se 3 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 4966109 = 1862291) B1862291
theorem B15124259 : Blo 980594 15124259 := bstep (se 1 (by rfl) ⟨11343194, by rfl⟩ : syracuseStep 15124259 = 22686389) B22686389
theorem B7456697 : Blo 980594 7456697 := bstep (se 2 (by rfl) ⟨2796261, by rfl⟩ : syracuseStep 7456697 = 5592523) B5592523
theorem B2213819 : Blo 980594 2213819 := bstep (se 1 (by rfl) ⟨1660364, by rfl⟩ : syracuseStep 2213819 = 3320729) B3320729
theorem B2803643 : Blo 980594 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B1656841 : Blo 980594 1656841 := bstep (se 2 (by rfl) ⟨621315, by rfl⟩ : syracuseStep 1656841 = 1242631) B1242631
theorem B2213945 : Blo 980594 2213945 := bstep (se 2 (by rfl) ⟨830229, by rfl⟩ : syracuseStep 2213945 = 1660459) B1660459
theorem B5589107 : Blo 980594 5589107 := bstep (se 1 (by rfl) ⟨4191830, by rfl⟩ : syracuseStep 5589107 = 8383661) B8383661
theorem B1657003 : Blo 980594 1657003 := bstep (se 1 (by rfl) ⟨1242752, by rfl⟩ : syracuseStep 1657003 = 2485505) B2485505
theorem B2214287 : Blo 980594 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B1657307 : Blo 980594 1657307 := bstep (se 1 (by rfl) ⟨1242980, by rfl⟩ : syracuseStep 1657307 = 2485961) B2485961
theorem B1657543 : Blo 980594 1657543 := bstep (se 1 (by rfl) ⟨1243157, by rfl⟩ : syracuseStep 1657543 = 2486315) B2486315
theorem B2214611 : Blo 980594 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B1657705 : Blo 980594 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B1330025 : Blo 980594 1330025 := bstep (se 2 (by rfl) ⟨498759, by rfl⟩ : syracuseStep 1330025 = 997519) B997519
theorem B1330615 : Blo 980594 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B1658299 : Blo 980594 1658299 := bstep (se 1 (by rfl) ⟨1243724, by rfl⟩ : syracuseStep 1658299 = 2487449) B2487449
theorem B1134043 : Blo 980594 1134043 := bstep (se 1 (by rfl) ⟨850532, by rfl⟩ : syracuseStep 1134043 = 1701065) B1701065
theorem B2838041 : Blo 980594 2838041 := bstep (se 2 (by rfl) ⟨1064265, by rfl⟩ : syracuseStep 2838041 = 2128531) B2128531
theorem B1658407 : Blo 980594 1658407 := bstep (se 1 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 1658407 = 2487611) B2487611
theorem B13618775 : Blo 980594 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B1658731 : Blo 980594 1658731 := bstep (se 1 (by rfl) ⟨1244048, by rfl⟩ : syracuseStep 1658731 = 2488097) B2488097
theorem B9424775 : Blo 980594 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B16765541 : Blo 980594 16765541 := bstep (se 4 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 16765541 = 3143539) B3143539
theorem B7459613 : Blo 980594 7459613 := bstep (se 3 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 7459613 = 2797355) B2797355
theorem B3724127 : Blo 980594 3724127 := bstep (se 1 (by rfl) ⟨2793095, by rfl⟩ : syracuseStep 3724127 = 5586191) B5586191
theorem B43078501 : Blo 980594 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B1594255 : Blo 980594 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B1659791 : Blo 980594 1659791 := bstep (se 1 (by rfl) ⟨1244843, by rfl⟩ : syracuseStep 1659791 = 2489687) B2489687
theorem B1660027 : Blo 980594 1660027 := bstep (se 1 (by rfl) ⟨1245020, by rfl⟩ : syracuseStep 1660027 = 2490041) B2490041
theorem B1594567 : Blo 980594 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B13456601 : Blo 980594 13456601 := bstep (se 2 (by rfl) ⟨5046225, by rfl⟩ : syracuseStep 13456601 = 10092451) B10092451
theorem B1103323 : Blo 980594 1103323 := bstep (se 1 (by rfl) ⟨827492, by rfl⟩ : syracuseStep 1103323 = 1654985) B1654985
theorem B3593737 : Blo 980594 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B3724825 : Blo 980594 3724825 := bstep (se 2 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 3724825 = 2793619) B2793619
theorem B5592797 : Blo 980594 5592797 := bstep (se 3 (by rfl) ⟨1048649, by rfl⟩ : syracuseStep 5592797 = 2097299) B2097299
theorem B3725099 : Blo 980594 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B3725129 : Blo 980594 3725129 := bstep (se 2 (by rfl) ⟨1396923, by rfl⟩ : syracuseStep 3725129 = 2793847) B2793847
theorem B145446731 : Blo 980594 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B1103791 : Blo 980594 1103791 := bstep (se 1 (by rfl) ⟨827843, by rfl⟩ : syracuseStep 1103791 = 1655687) B1655687
theorem B1660891 : Blo 980594 1660891 := bstep (se 1 (by rfl) ⟨1245668, by rfl⟩ : syracuseStep 1660891 = 2491337) B2491337
theorem B1104223 : Blo 980594 1104223 := bstep (se 1 (by rfl) ⟨828167, by rfl⟩ : syracuseStep 1104223 = 1656335) B1656335
theorem B3365435 : Blo 980594 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B1104583 : Blo 980594 1104583 := bstep (se 1 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 1104583 = 1656875) B1656875
theorem B4971293 : Blo 980594 4971293 := bstep (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) B1864235
theorem B14179141 : Blo 980594 14179141 := bstep (se 4 (by rfl) ⟨1329294, by rfl⟩ : syracuseStep 14179141 = 2658589) B2658589
theorem B1399771 : Blo 980594 1399771 := bstep (se 1 (by rfl) ⟨1049828, by rfl⟩ : syracuseStep 1399771 = 2099657) B2099657
theorem B1105447 : Blo 980594 1105447 := bstep (se 1 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 1105447 = 1658171) B1658171
theorem B1891919 : Blo 980594 1891919 := bstep (se 1 (by rfl) ⟨1418939, by rfl⟩ : syracuseStep 1891919 = 2837879) B2837879
theorem B8380037 : Blo 980594 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B6283493 : Blo 980594 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B3727741 : Blo 980594 3727741 := bstep (se 3 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 3727741 = 1397903) B1397903
theorem B11658241 : Blo 980594 11658241 := bstep (se 2 (by rfl) ⟨4371840, by rfl⟩ : syracuseStep 11658241 = 8743681) B8743681
theorem B2483207 : Blo 980594 2483207 := bstep (se 1 (by rfl) ⟨1862405, by rfl⟩ : syracuseStep 2483207 = 3724811) B3724811
theorem B7463987 : Blo 980594 7463987 := bstep (se 1 (by rfl) ⟨5597990, by rfl⟩ : syracuseStep 7463987 = 11195981) B11195981
theorem B2483257 : Blo 980594 2483257 := bstep (se 2 (by rfl) ⟨931221, by rfl⟩ : syracuseStep 2483257 = 1862443) B1862443
theorem B1991803 : Blo 980594 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B1107067 : Blo 980594 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B2483561 : Blo 980594 2483561 := bstep (se 2 (by rfl) ⟨931335, by rfl⟩ : syracuseStep 2483561 = 1862671) B1862671
theorem B214820261 : Blo 980594 214820261 := bstep (se 4 (by rfl) ⟨20139399, by rfl⟩ : syracuseStep 214820261 = 40278799) B40278799
theorem B17917451 : Blo 980594 17917451 := bstep (se 1 (by rfl) ⟨13438088, by rfl⟩ : syracuseStep 17917451 = 26876177) B26876177
theorem B1107535 : Blo 980594 1107535 := bstep (se 1 (by rfl) ⟨830651, by rfl⟩ : syracuseStep 1107535 = 1661303) B1661303
theorem B13428575 : Blo 980594 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B1993223 : Blo 980594 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B3729959 : Blo 980594 3729959 := bstep (se 1 (by rfl) ⟨2797469, by rfl⟩ : syracuseStep 3729959 = 5594939) B5594939
theorem B31878157 : Blo 980594 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B4975667 : Blo 980594 4975667 := bstep (se 1 (by rfl) ⟨3731750, by rfl⟩ : syracuseStep 4975667 = 7463501) B7463501
theorem B9432463 : Blo 980594 9432463 := bstep (se 1 (by rfl) ⟨7074347, by rfl⟩ : syracuseStep 9432463 = 14148695) B14148695
theorem B5598629 : Blo 980594 5598629 := bstep (se 4 (by rfl) ⟨524871, by rfl⟩ : syracuseStep 5598629 = 1049743) B1049743
theorem B3730931 : Blo 980594 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B367586819 : Blo 980594 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B2485799 : Blo 980594 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B3731129 : Blo 980594 3731129 := bstep (se 2 (by rfl) ⟨1399173, by rfl⟩ : syracuseStep 3731129 = 2798347) B2798347
theorem B3731143 : Blo 980594 3731143 := bstep (se 1 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 3731143 = 5596715) B5596715
theorem B1863415 : Blo 980594 1863415 := bstep (se 1 (by rfl) ⟨1397561, by rfl⟩ : syracuseStep 1863415 = 2795123) B2795123
theorem B2486123 : Blo 980594 2486123 := bstep (se 1 (by rfl) ⟨1864592, by rfl⟩ : syracuseStep 2486123 = 3729185) B3729185
theorem B1863643 : Blo 980594 1863643 := bstep (se 1 (by rfl) ⟨1397732, by rfl⟩ : syracuseStep 1863643 = 2795465) B2795465
theorem B1863719 : Blo 980594 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B5599313 : Blo 980594 5599313 := bstep (se 2 (by rfl) ⟨2099742, by rfl⟩ : syracuseStep 5599313 = 4199485) B4199485
theorem B1863803 : Blo 980594 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B5304637 : Blo 980594 5304637 := bstep (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) B1989239
theorem B1241563 : Blo 980594 1241563 := bstep (se 1 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 1241563 = 1862345) B1862345
theorem B2486771 : Blo 980594 2486771 := bstep (se 1 (by rfl) ⟨1865078, by rfl⟩ : syracuseStep 2486771 = 3730157) B3730157
theorem B1471055 : Blo 980594 1471055 := bstep (se 1 (by rfl) ⟨1103291, by rfl⟩ : syracuseStep 1471055 = 2206583) B2206583
theorem B1864289 : Blo 980594 1864289 := bstep (se 2 (by rfl) ⟨699108, by rfl⟩ : syracuseStep 1864289 = 1398217) B1398217
theorem B4977287 : Blo 980594 4977287 := bstep (se 1 (by rfl) ⟨3732965, by rfl⟩ : syracuseStep 4977287 = 7465931) B7465931
theorem B3732115 : Blo 980594 3732115 := bstep (se 1 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 3732115 = 5598173) B5598173
theorem B1471175 : Blo 980594 1471175 := bstep (se 1 (by rfl) ⟨1103381, by rfl⟩ : syracuseStep 1471175 = 2206763) B2206763
theorem B2486983 : Blo 980594 2486983 := bstep (se 1 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 2486983 = 3730475) B3730475
theorem B4715293 : Blo 980594 4715293 := bstep (se 3 (by rfl) ⟨884117, by rfl⟩ : syracuseStep 4715293 = 1768235) B1768235
theorem B1471337 : Blo 980594 1471337 := bstep (se 2 (by rfl) ⟨551751, by rfl⟩ : syracuseStep 1471337 = 1103503) B1103503
theorem B1471415 : Blo 980594 1471415 := bstep (se 1 (by rfl) ⟨1103561, by rfl⟩ : syracuseStep 1471415 = 2207123) B2207123
theorem B1471451 : Blo 980594 1471451 := bstep (se 1 (by rfl) ⟨1103588, by rfl⟩ : syracuseStep 1471451 = 2207177) B2207177
theorem B1471919 : Blo 980594 1471919 := bstep (se 1 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 1471919 = 2207879) B2207879
theorem B1472009 : Blo 980594 1472009 := bstep (se 2 (by rfl) ⟨552003, by rfl⟩ : syracuseStep 1472009 = 1104007) B1104007
theorem B1472039 : Blo 980594 1472039 := bstep (se 1 (by rfl) ⟨1104029, by rfl⟩ : syracuseStep 1472039 = 2208059) B2208059
theorem B2487905 : Blo 980594 2487905 := bstep (se 2 (by rfl) ⟨932964, by rfl⟩ : syracuseStep 2487905 = 1865929) B1865929
theorem B980603 : Blo 980594 980603 := bstep (se 1 (by rfl) ⟨735452, by rfl⟩ : syracuseStep 980603 = 1470905) B1470905
theorem B1472123 : Blo 980594 1472123 := bstep (se 1 (by rfl) ⟨1104092, by rfl⟩ : syracuseStep 1472123 = 2208185) B2208185
theorem B980655 : Blo 980594 980655 := bstep (se 1 (by rfl) ⟨735491, by rfl⟩ : syracuseStep 980655 = 1470983) B1470983
theorem B980679 : Blo 980594 980679 := bstep (se 1 (by rfl) ⟨735509, by rfl⟩ : syracuseStep 980679 = 1471019) B1471019
theorem B12613319 : Blo 980594 12613319 := bstep (se 1 (by rfl) ⟨9459989, by rfl⟩ : syracuseStep 12613319 = 18919979) B18919979
theorem B980699 : Blo 980594 980699 := bstep (se 1 (by rfl) ⟨735524, by rfl⟩ : syracuseStep 980699 = 1471049) B1471049
theorem B1472249 : Blo 980594 1472249 := bstep (se 2 (by rfl) ⟨552093, by rfl⟩ : syracuseStep 1472249 = 1104187) B1104187
theorem B980775 : Blo 980594 980775 := bstep (se 1 (by rfl) ⟨735581, by rfl⟩ : syracuseStep 980775 = 1471163) B1471163
theorem B3536713 : Blo 980594 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B980815 : Blo 980594 980815 := bstep (se 1 (by rfl) ⟨735611, by rfl⟩ : syracuseStep 980815 = 1471223) B1471223
theorem B980831 : Blo 980594 980831 := bstep (se 1 (by rfl) ⟨735623, by rfl⟩ : syracuseStep 980831 = 1471247) B1471247
theorem B1472351 : Blo 980594 1472351 := bstep (se 1 (by rfl) ⟨1104263, by rfl⟩ : syracuseStep 1472351 = 2208527) B2208527
theorem B1472363 : Blo 980594 1472363 := bstep (se 1 (by rfl) ⟨1104272, by rfl⟩ : syracuseStep 1472363 = 2208545) B2208545
theorem B12580717 : Blo 980594 12580717 := bstep (se 3 (by rfl) ⟨2358884, by rfl⟩ : syracuseStep 12580717 = 4717769) B4717769
theorem B980859 : Blo 980594 980859 := bstep (se 1 (by rfl) ⟨735644, by rfl⟩ : syracuseStep 980859 = 1471289) B1471289
theorem B980911 : Blo 980594 980911 := bstep (se 1 (by rfl) ⟨735683, by rfl⟩ : syracuseStep 980911 = 1471367) B1471367
theorem B980935 : Blo 980594 980935 := bstep (se 1 (by rfl) ⟨735701, by rfl⟩ : syracuseStep 980935 = 1471403) B1471403
theorem B980955 : Blo 980594 980955 := bstep (se 1 (by rfl) ⟨735716, by rfl⟩ : syracuseStep 980955 = 1471433) B1471433
theorem B1865747 : Blo 980594 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B981031 : Blo 980594 981031 := bstep (se 1 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 981031 = 1471547) B1471547
theorem B4978745 : Blo 980594 4978745 := bstep (se 2 (by rfl) ⟨1867029, by rfl⟩ : syracuseStep 4978745 = 3734059) B3734059
theorem B981071 : Blo 980594 981071 := bstep (se 1 (by rfl) ⟨735803, by rfl⟩ : syracuseStep 981071 = 1471607) B1471607
theorem B1472591 : Blo 980594 1472591 := bstep (se 1 (by rfl) ⟨1104443, by rfl⟩ : syracuseStep 1472591 = 2208887) B2208887
theorem B981087 : Blo 980594 981087 := bstep (se 1 (by rfl) ⟨735815, by rfl⟩ : syracuseStep 981087 = 1471631) B1471631
theorem B1767521 : Blo 980594 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B981115 : Blo 980594 981115 := bstep (se 1 (by rfl) ⟨735836, by rfl⟩ : syracuseStep 981115 = 1471673) B1471673
theorem B38271133 : Blo 980594 38271133 := bstep (se 3 (by rfl) ⟨7175837, by rfl⟩ : syracuseStep 38271133 = 14351675) B14351675
theorem B8976541 : Blo 980594 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B981167 : Blo 980594 981167 := bstep (se 1 (by rfl) ⟨735875, by rfl⟩ : syracuseStep 981167 = 1471751) B1471751
theorem B981191 : Blo 980594 981191 := bstep (se 1 (by rfl) ⟨735893, by rfl⟩ : syracuseStep 981191 = 1471787) B1471787
theorem B1472711 : Blo 980594 1472711 := bstep (se 1 (by rfl) ⟨1104533, by rfl⟩ : syracuseStep 1472711 = 2209067) B2209067
theorem B981211 : Blo 980594 981211 := bstep (se 1 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 981211 = 1471817) B1471817
theorem B981287 : Blo 980594 981287 := bstep (se 1 (by rfl) ⟨735965, by rfl⟩ : syracuseStep 981287 = 1471931) B1471931
theorem B981327 : Blo 980594 981327 := bstep (se 1 (by rfl) ⟨735995, by rfl⟩ : syracuseStep 981327 = 1471991) B1471991
theorem B3733847 : Blo 980594 3733847 := bstep (se 1 (by rfl) ⟨2800385, by rfl⟩ : syracuseStep 3733847 = 5600771) B5600771
theorem B981343 : Blo 980594 981343 := bstep (se 1 (by rfl) ⟨736007, by rfl⟩ : syracuseStep 981343 = 1472015) B1472015
theorem B3144041 : Blo 980594 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B1472873 : Blo 980594 1472873 := bstep (se 2 (by rfl) ⟨552327, by rfl⟩ : syracuseStep 1472873 = 1104655) B1104655
theorem B981371 : Blo 980594 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B981423 : Blo 980594 981423 := bstep (se 1 (by rfl) ⟨736067, by rfl⟩ : syracuseStep 981423 = 1472135) B1472135
theorem B1472951 : Blo 980594 1472951 := bstep (se 1 (by rfl) ⟨1104713, by rfl⟩ : syracuseStep 1472951 = 2209427) B2209427
theorem B981447 : Blo 980594 981447 := bstep (se 1 (by rfl) ⟨736085, by rfl⟩ : syracuseStep 981447 = 1472171) B1472171
theorem B2357723 : Blo 980594 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B981467 : Blo 980594 981467 := bstep (se 1 (by rfl) ⟨736100, by rfl⟩ : syracuseStep 981467 = 1472201) B1472201
theorem B1472987 : Blo 980594 1472987 := bstep (se 1 (by rfl) ⟨1104740, by rfl⟩ : syracuseStep 1472987 = 2209481) B2209481
theorem B2095625 : Blo 980594 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B981543 : Blo 980594 981543 := bstep (se 1 (by rfl) ⟨736157, by rfl⟩ : syracuseStep 981543 = 1472315) B1472315
theorem B981583 : Blo 980594 981583 := bstep (se 1 (by rfl) ⟨736187, by rfl⟩ : syracuseStep 981583 = 1472375) B1472375
theorem B981599 : Blo 980594 981599 := bstep (se 1 (by rfl) ⟨736199, by rfl⟩ : syracuseStep 981599 = 1472399) B1472399
theorem B981627 : Blo 980594 981627 := bstep (se 1 (by rfl) ⟨736220, by rfl⟩ : syracuseStep 981627 = 1472441) B1472441
theorem B981679 : Blo 980594 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B981703 : Blo 980594 981703 := bstep (se 1 (by rfl) ⟨736277, by rfl⟩ : syracuseStep 981703 = 1472555) B1472555
theorem B981723 : Blo 980594 981723 := bstep (se 1 (by rfl) ⟨736292, by rfl⟩ : syracuseStep 981723 = 1472585) B1472585
theorem B981799 : Blo 980594 981799 := bstep (se 1 (by rfl) ⟨736349, by rfl⟩ : syracuseStep 981799 = 1472699) B1472699
theorem B981839 : Blo 980594 981839 := bstep (se 1 (by rfl) ⟨736379, by rfl⟩ : syracuseStep 981839 = 1472759) B1472759
theorem B981855 : Blo 980594 981855 := bstep (se 1 (by rfl) ⟨736391, by rfl⟩ : syracuseStep 981855 = 1472783) B1472783
theorem B981883 : Blo 980594 981883 := bstep (se 1 (by rfl) ⟨736412, by rfl⟩ : syracuseStep 981883 = 1472825) B1472825
theorem B981935 : Blo 980594 981935 := bstep (se 1 (by rfl) ⟨736451, by rfl⟩ : syracuseStep 981935 = 1472903) B1472903
theorem B1473455 : Blo 980594 1473455 := bstep (se 1 (by rfl) ⟨1105091, by rfl⟩ : syracuseStep 1473455 = 2210183) B2210183
theorem B981959 : Blo 980594 981959 := bstep (se 1 (by rfl) ⟨736469, by rfl⟩ : syracuseStep 981959 = 1472939) B1472939
theorem B981979 : Blo 980594 981979 := bstep (se 1 (by rfl) ⟨736484, by rfl⟩ : syracuseStep 981979 = 1472969) B1472969
theorem B1473545 : Blo 980594 1473545 := bstep (se 2 (by rfl) ⟨552579, by rfl⟩ : syracuseStep 1473545 = 1105159) B1105159
theorem B3144719 : Blo 980594 3144719 := bstep (se 1 (by rfl) ⟨2358539, by rfl⟩ : syracuseStep 3144719 = 4717079) B4717079
theorem B4193299 : Blo 980594 4193299 := bstep (se 1 (by rfl) ⟨3144974, by rfl⟩ : syracuseStep 4193299 = 6289949) B6289949
theorem B2489363 : Blo 980594 2489363 := bstep (se 1 (by rfl) ⟨1867022, by rfl⟩ : syracuseStep 2489363 = 3734045) B3734045
theorem B982055 : Blo 980594 982055 := bstep (se 1 (by rfl) ⟨736541, by rfl⟩ : syracuseStep 982055 = 1473083) B1473083
theorem B1473575 : Blo 980594 1473575 := bstep (se 1 (by rfl) ⟨1105181, by rfl⟩ : syracuseStep 1473575 = 2210363) B2210363
theorem B982095 : Blo 980594 982095 := bstep (se 1 (by rfl) ⟨736571, by rfl⟩ : syracuseStep 982095 = 1473143) B1473143
theorem B982111 : Blo 980594 982111 := bstep (se 1 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 982111 = 1473167) B1473167
theorem B982139 : Blo 980594 982139 := bstep (se 1 (by rfl) ⟨736604, by rfl⟩ : syracuseStep 982139 = 1473209) B1473209
theorem B1473659 : Blo 980594 1473659 := bstep (se 1 (by rfl) ⟨1105244, by rfl⟩ : syracuseStep 1473659 = 2210489) B2210489
theorem B982191 : Blo 980594 982191 := bstep (se 1 (by rfl) ⟨736643, by rfl⟩ : syracuseStep 982191 = 1473287) B1473287
theorem B982215 : Blo 980594 982215 := bstep (se 1 (by rfl) ⟨736661, by rfl⟩ : syracuseStep 982215 = 1473323) B1473323
theorem B982235 : Blo 980594 982235 := bstep (se 1 (by rfl) ⟨736676, by rfl⟩ : syracuseStep 982235 = 1473353) B1473353
theorem B1473785 : Blo 980594 1473785 := bstep (se 2 (by rfl) ⟨552669, by rfl⟩ : syracuseStep 1473785 = 1105339) B1105339
theorem B982311 : Blo 980594 982311 := bstep (se 1 (by rfl) ⟨736733, by rfl⟩ : syracuseStep 982311 = 1473467) B1473467
theorem B982351 : Blo 980594 982351 := bstep (se 1 (by rfl) ⟨736763, by rfl⟩ : syracuseStep 982351 = 1473527) B1473527
theorem B982367 : Blo 980594 982367 := bstep (se 1 (by rfl) ⟨736775, by rfl⟩ : syracuseStep 982367 = 1473551) B1473551
theorem B1473887 : Blo 980594 1473887 := bstep (se 1 (by rfl) ⟨1105415, by rfl⟩ : syracuseStep 1473887 = 2210831) B2210831
theorem B1473899 : Blo 980594 1473899 := bstep (se 1 (by rfl) ⟨1105424, by rfl⟩ : syracuseStep 1473899 = 2210849) B2210849
theorem B982395 : Blo 980594 982395 := bstep (se 1 (by rfl) ⟨736796, by rfl⟩ : syracuseStep 982395 = 1473593) B1473593
theorem B1867151 : Blo 980594 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B1047983 : Blo 980594 1047983 := bstep (se 1 (by rfl) ⟨785987, by rfl⟩ : syracuseStep 1047983 = 1571975) B1571975
theorem B982447 : Blo 980594 982447 := bstep (se 1 (by rfl) ⟨736835, by rfl⟩ : syracuseStep 982447 = 1473671) B1473671
theorem B1768891 : Blo 980594 1768891 := bstep (se 1 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 1768891 = 2653337) B2653337
theorem B982471 : Blo 980594 982471 := bstep (se 1 (by rfl) ⟨736853, by rfl⟩ : syracuseStep 982471 = 1473707) B1473707
theorem B982491 : Blo 980594 982491 := bstep (se 1 (by rfl) ⟨736868, by rfl⟩ : syracuseStep 982491 = 1473737) B1473737
theorem B982567 : Blo 980594 982567 := bstep (se 1 (by rfl) ⟨736925, by rfl⟩ : syracuseStep 982567 = 1473851) B1473851
theorem B1867303 : Blo 980594 1867303 := bstep (se 1 (by rfl) ⟨1400477, by rfl⟩ : syracuseStep 1867303 = 2800955) B2800955
theorem B982607 : Blo 980594 982607 := bstep (se 1 (by rfl) ⟨736955, by rfl⟩ : syracuseStep 982607 = 1473911) B1473911
theorem B1474127 : Blo 980594 1474127 := bstep (se 1 (by rfl) ⟨1105595, by rfl⟩ : syracuseStep 1474127 = 2211191) B2211191
theorem B982623 : Blo 980594 982623 := bstep (se 1 (by rfl) ⟨736967, by rfl⟩ : syracuseStep 982623 = 1473935) B1473935
theorem B982651 : Blo 980594 982651 := bstep (se 1 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 982651 = 1473977) B1473977
theorem B1867387 : Blo 980594 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B982703 : Blo 980594 982703 := bstep (se 1 (by rfl) ⟨737027, by rfl⟩ : syracuseStep 982703 = 1474055) B1474055
theorem B982727 : Blo 980594 982727 := bstep (se 1 (by rfl) ⟨737045, by rfl⟩ : syracuseStep 982727 = 1474091) B1474091
theorem B1474247 : Blo 980594 1474247 := bstep (se 1 (by rfl) ⟨1105685, by rfl⟩ : syracuseStep 1474247 = 2211371) B2211371
theorem B7470791 : Blo 980594 7470791 := bstep (se 1 (by rfl) ⟨5603093, by rfl⟩ : syracuseStep 7470791 = 11206187) B11206187
theorem B982747 : Blo 980594 982747 := bstep (se 1 (by rfl) ⟨737060, by rfl⟩ : syracuseStep 982747 = 1474121) B1474121
theorem B982823 : Blo 980594 982823 := bstep (se 1 (by rfl) ⟨737117, by rfl⟩ : syracuseStep 982823 = 1474235) B1474235
theorem B982863 : Blo 980594 982863 := bstep (se 1 (by rfl) ⟨737147, by rfl⟩ : syracuseStep 982863 = 1474295) B1474295
theorem B2359135 : Blo 980594 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B982879 : Blo 980594 982879 := bstep (se 1 (by rfl) ⟨737159, by rfl⟩ : syracuseStep 982879 = 1474319) B1474319
theorem B1474409 : Blo 980594 1474409 := bstep (se 2 (by rfl) ⟨552903, by rfl⟩ : syracuseStep 1474409 = 1105807) B1105807
theorem B17956727 : Blo 980594 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B982907 : Blo 980594 982907 := bstep (se 1 (by rfl) ⟨737180, by rfl⟩ : syracuseStep 982907 = 1474361) B1474361
theorem B982959 : Blo 980594 982959 := bstep (se 1 (by rfl) ⟨737219, by rfl⟩ : syracuseStep 982959 = 1474439) B1474439
theorem B1474487 : Blo 980594 1474487 := bstep (se 1 (by rfl) ⟨1105865, by rfl⟩ : syracuseStep 1474487 = 2211731) B2211731
theorem B982983 : Blo 980594 982983 := bstep (se 1 (by rfl) ⟨737237, by rfl⟩ : syracuseStep 982983 = 1474475) B1474475
theorem B983003 : Blo 980594 983003 := bstep (se 1 (by rfl) ⟨737252, by rfl⟩ : syracuseStep 983003 = 1474505) B1474505
theorem B1474523 : Blo 980594 1474523 := bstep (se 1 (by rfl) ⟨1105892, by rfl⟩ : syracuseStep 1474523 = 2211785) B2211785
theorem B6717491 : Blo 980594 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B2490497 : Blo 980594 2490497 := bstep (se 2 (by rfl) ⟨933936, by rfl⟩ : syracuseStep 2490497 = 1867873) B1867873
theorem B2359577 : Blo 980594 2359577 := bstep (se 2 (by rfl) ⟨884841, by rfl⟩ : syracuseStep 2359577 = 1769683) B1769683
theorem B983327 : Blo 980594 983327 := bstep (se 1 (by rfl) ⟨737495, by rfl⟩ : syracuseStep 983327 = 1474991) B1474991
theorem B1474907 : Blo 980594 1474907 := bstep (se 1 (by rfl) ⟨1106180, by rfl⟩ : syracuseStep 1474907 = 2212361) B2212361
theorem B983387 : Blo 980594 983387 := bstep (se 1 (by rfl) ⟨737540, by rfl⟩ : syracuseStep 983387 = 1475081) B1475081
theorem B1868123 : Blo 980594 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B983407 : Blo 980594 983407 := bstep (se 1 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 983407 = 1475111) B1475111
theorem B983463 : Blo 980594 983463 := bstep (se 1 (by rfl) ⟨737597, by rfl⟩ : syracuseStep 983463 = 1475195) B1475195
theorem B983547 : Blo 980594 983547 := bstep (se 1 (by rfl) ⟨737660, by rfl⟩ : syracuseStep 983547 = 1475321) B1475321
theorem B1475135 : Blo 980594 1475135 := bstep (se 1 (by rfl) ⟨1106351, by rfl⟩ : syracuseStep 1475135 = 2212703) B2212703
theorem B983615 : Blo 980594 983615 := bstep (se 1 (by rfl) ⟨737711, by rfl⟩ : syracuseStep 983615 = 1475423) B1475423
theorem B983623 : Blo 980594 983623 := bstep (se 1 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 983623 = 1475435) B1475435
theorem B1868359 : Blo 980594 1868359 := bstep (se 1 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 1868359 = 2802539) B2802539
theorem B2097743 : Blo 980594 2097743 := bstep (se 1 (by rfl) ⟨1573307, by rfl⟩ : syracuseStep 2097743 = 3146615) B3146615
theorem B7471763 : Blo 980594 7471763 := bstep (se 1 (by rfl) ⟨5603822, by rfl⟩ : syracuseStep 7471763 = 11207645) B11207645
theorem B1245871 : Blo 980594 1245871 := bstep (se 1 (by rfl) ⟨934403, by rfl⟩ : syracuseStep 1245871 = 1868807) B1868807
theorem B1475255 : Blo 980594 1475255 := bstep (se 1 (by rfl) ⟨1106441, by rfl⟩ : syracuseStep 1475255 = 2212883) B2212883
theorem B983775 : Blo 980594 983775 := bstep (se 1 (by rfl) ⟨737831, by rfl⟩ : syracuseStep 983775 = 1475663) B1475663
theorem B983855 : Blo 980594 983855 := bstep (se 1 (by rfl) ⟨737891, by rfl⟩ : syracuseStep 983855 = 1475783) B1475783
theorem B3310415 : Blo 980594 3310415 := bstep (se 1 (by rfl) ⟨2482811, by rfl⟩ : syracuseStep 3310415 = 4965623) B4965623
theorem B1475483 : Blo 980594 1475483 := bstep (se 1 (by rfl) ⟨1106612, by rfl⟩ : syracuseStep 1475483 = 2213225) B2213225
theorem B983963 : Blo 980594 983963 := bstep (se 1 (by rfl) ⟨737972, by rfl⟩ : syracuseStep 983963 = 1475945) B1475945
theorem B2491307 : Blo 980594 2491307 := bstep (se 1 (by rfl) ⟨1868480, by rfl⟩ : syracuseStep 2491307 = 3736961) B3736961
theorem B984015 : Blo 980594 984015 := bstep (se 1 (by rfl) ⟨738011, by rfl⟩ : syracuseStep 984015 = 1476023) B1476023
theorem B984039 : Blo 980594 984039 := bstep (se 1 (by rfl) ⟨738029, by rfl⟩ : syracuseStep 984039 = 1476059) B1476059
theorem B4195385 : Blo 980594 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B3310739 : Blo 980594 3310739 := bstep (se 1 (by rfl) ⟨2483054, by rfl⟩ : syracuseStep 3310739 = 4966109) B4966109
theorem B3540115 : Blo 980594 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B984351 : Blo 980594 984351 := bstep (se 1 (by rfl) ⟨738263, by rfl⟩ : syracuseStep 984351 = 1476527) B1476527
theorem B1475879 : Blo 980594 1475879 := bstep (se 1 (by rfl) ⟨1106909, by rfl⟩ : syracuseStep 1475879 = 2213819) B2213819
theorem B1869095 : Blo 980594 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B984411 : Blo 980594 984411 := bstep (se 1 (by rfl) ⟨738308, by rfl⟩ : syracuseStep 984411 = 1476617) B1476617
theorem B984431 : Blo 980594 984431 := bstep (se 1 (by rfl) ⟨738323, by rfl⟩ : syracuseStep 984431 = 1476647) B1476647
theorem B1475963 : Blo 980594 1475963 := bstep (se 1 (by rfl) ⟨1106972, by rfl⟩ : syracuseStep 1475963 = 2213945) B2213945
theorem B3311009 : Blo 980594 3311009 := bstep (se 2 (by rfl) ⟨1241628, by rfl⟩ : syracuseStep 3311009 = 2483257) B2483257
theorem B4195745 : Blo 980594 4195745 := bstep (se 2 (by rfl) ⟨1573404, by rfl⟩ : syracuseStep 4195745 = 3146809) B3146809
theorem B984487 : Blo 980594 984487 := bstep (se 1 (by rfl) ⟨738365, by rfl⟩ : syracuseStep 984487 = 1476731) B1476731
theorem B2655737 : Blo 980594 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B1476089 : Blo 980594 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B984571 : Blo 980594 984571 := bstep (se 1 (by rfl) ⟨738428, by rfl⟩ : syracuseStep 984571 = 1476857) B1476857
theorem B1476191 : Blo 980594 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B1574635 : Blo 980594 1574635 := bstep (se 1 (by rfl) ⟨1180976, by rfl⟩ : syracuseStep 1574635 = 2361953) B2361953
theorem B2492167 : Blo 980594 2492167 := bstep (se 1 (by rfl) ⟨1869125, by rfl⟩ : syracuseStep 2492167 = 3738251) B3738251
theorem B1476407 : Blo 980594 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B4982633 : Blo 980594 4982633 := bstep (se 2 (by rfl) ⟨1868487, by rfl⟩ : syracuseStep 4982633 = 3736975) B3736975
theorem B8521805 : Blo 980594 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B1476713 : Blo 980594 1476713 := bstep (se 2 (by rfl) ⟨553767, by rfl⟩ : syracuseStep 1476713 = 1107535) B1107535
theorem B3737735 : Blo 980594 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B9079183 : Blo 980594 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B11209103 : Blo 980594 11209103 := bstep (se 1 (by rfl) ⟨8406827, by rfl⟩ : syracuseStep 11209103 = 16813655) B16813655
theorem B2099623 : Blo 980594 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B4197059 : Blo 980594 4197059 := bstep (se 1 (by rfl) ⟨3147794, by rfl⟩ : syracuseStep 4197059 = 6295589) B6295589
theorem B7080695 : Blo 980594 7080695 := bstep (se 1 (by rfl) ⟨5310521, by rfl⟩ : syracuseStep 7080695 = 10621043) B10621043
theorem B12586049 : Blo 980594 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B11177027 : Blo 980594 11177027 := bstep (se 1 (by rfl) ⟨8382770, by rfl⟩ : syracuseStep 11177027 = 16765541) B16765541
theorem B8391761 : Blo 980594 8391761 := bstep (se 2 (by rfl) ⟨3146910, by rfl⟩ : syracuseStep 8391761 = 6293821) B6293821
theorem B9440459 : Blo 980594 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B5606921 : Blo 980594 5606921 := bstep (se 2 (by rfl) ⟨2102595, by rfl⟩ : syracuseStep 5606921 = 4205191) B4205191
theorem B4984415 : Blo 980594 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B9572039 : Blo 980594 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B96964487 : Blo 980594 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B7475165 : Blo 980594 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B42504209 : Blo 980594 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B11178485 : Blo 980594 11178485 := bstep (se 5 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 11178485 = 1047983) B1047983
theorem B13472245 : Blo 980594 13472245 := bstep (se 5 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 13472245 = 1263023) B1263023
theorem B3314195 : Blo 980594 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B1774153 : Blo 980594 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B4199161 : Blo 980594 4199161 := bstep (se 2 (by rfl) ⟨1574685, by rfl⟩ : syracuseStep 4199161 = 3149371) B3149371
theorem B3315977 : Blo 980594 3315977 := bstep (se 2 (by rfl) ⟨1243491, by rfl⟩ : syracuseStep 3315977 = 2486983) B2486983
theorem B4725287 : Blo 980594 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B8952383 : Blo 980594 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B10067165 : Blo 980594 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B1121575 : Blo 980594 1121575 := bstep (se 1 (by rfl) ⟨841181, by rfl⟩ : syracuseStep 1121575 = 1682363) B1682363
theorem B4791649 : Blo 980594 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B3317111 : Blo 980594 3317111 := bstep (se 1 (by rfl) ⟨2487833, by rfl⟩ : syracuseStep 3317111 = 4975667) B4975667
theorem B9444923 : Blo 980594 9444923 := bstep (se 1 (by rfl) ⟨7083692, by rfl⟩ : syracuseStep 9444923 = 14167385) B14167385
theorem B4202219 : Blo 980594 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B3022649 : Blo 980594 3022649 := bstep (se 2 (by rfl) ⟨1133493, by rfl⟩ : syracuseStep 3022649 = 2266987) B2266987
theorem B51028177 : Blo 980594 51028177 := bstep (se 2 (by rfl) ⟨19135566, by rfl⟩ : syracuseStep 51028177 = 38271133) B38271133
theorem B11968721 : Blo 980594 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B2236763 : Blo 980594 2236763 := bstep (se 1 (by rfl) ⟨1677572, by rfl⟩ : syracuseStep 2236763 = 3355145) B3355145
theorem B3318191 : Blo 980594 3318191 := bstep (se 1 (by rfl) ⟨2488643, by rfl⟩ : syracuseStep 3318191 = 4977287) B4977287
theorem B6300611 : Blo 980594 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B4727747 : Blo 980594 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B3548393 : Blo 980594 3548393 := bstep (se 2 (by rfl) ⟨1330647, by rfl⟩ : syracuseStep 3548393 = 2661295) B2661295
theorem B3319163 : Blo 980594 3319163 := bstep (se 1 (by rfl) ⟨2489372, by rfl⟩ : syracuseStep 3319163 = 4978745) B4978745
theorem B26879687 : Blo 980594 26879687 := bstep (se 1 (by rfl) ⟨20159765, by rfl⟩ : syracuseStep 26879687 = 40319531) B40319531
theorem B11971151 : Blo 980594 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B8399447 : Blo 980594 8399447 := bstep (se 1 (by rfl) ⟨6299585, by rfl⟩ : syracuseStep 8399447 = 12599171) B12599171
theorem B3320567 : Blo 980594 3320567 := bstep (se 1 (by rfl) ⟨2490425, by rfl⟩ : syracuseStep 3320567 = 4980851) B4980851
theorem B2206619 : Blo 980594 2206619 := bstep (se 1 (by rfl) ⟨1654964, by rfl⟩ : syracuseStep 2206619 = 3309929) B3309929
theorem B2206817 : Blo 980594 2206817 := bstep (se 2 (by rfl) ⟨827556, by rfl⟩ : syracuseStep 2206817 = 1655113) B1655113
theorem B2796763 : Blo 980594 2796763 := bstep (se 1 (by rfl) ⟨2097572, by rfl⟩ : syracuseStep 2796763 = 4195145) B4195145
theorem B2207015 : Blo 980594 2207015 := bstep (se 1 (by rfl) ⟨1655261, by rfl⟩ : syracuseStep 2207015 = 3310523) B3310523
theorem B10759553 : Blo 980594 10759553 := bstep (se 2 (by rfl) ⟨4034832, by rfl⟩ : syracuseStep 10759553 = 8069665) B8069665
theorem B5680649 : Blo 980594 5680649 := bstep (se 2 (by rfl) ⟨2130243, by rfl⟩ : syracuseStep 5680649 = 4260487) B4260487
theorem B2207393 : Blo 980594 2207393 := bstep (se 2 (by rfl) ⟨827772, by rfl⟩ : syracuseStep 2207393 = 1655545) B1655545
theorem B7450379 : Blo 980594 7450379 := bstep (se 1 (by rfl) ⟨5587784, by rfl⟩ : syracuseStep 7450379 = 11175569) B11175569
theorem B3321647 : Blo 980594 3321647 := bstep (se 1 (by rfl) ⟨2491235, by rfl⟩ : syracuseStep 3321647 = 4982471) B4982471
theorem B2273129 : Blo 980594 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B7548893 : Blo 980594 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B15544321 : Blo 980594 15544321 := bstep (se 2 (by rfl) ⟨5829120, by rfl⟩ : syracuseStep 15544321 = 11658241) B11658241
theorem B2207753 : Blo 980594 2207753 := bstep (se 2 (by rfl) ⟨827907, by rfl⟩ : syracuseStep 2207753 = 1655815) B1655815
theorem B71840033 : Blo 980594 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B2208167 : Blo 980594 2208167 := bstep (se 1 (by rfl) ⟨1656125, by rfl⟩ : syracuseStep 2208167 = 3312251) B3312251
theorem B2208275 : Blo 980594 2208275 := bstep (se 1 (by rfl) ⟨1656206, by rfl⟩ : syracuseStep 2208275 = 3312413) B3312413
theorem B2208329 : Blo 980594 2208329 := bstep (se 2 (by rfl) ⟨828123, by rfl⟩ : syracuseStep 2208329 = 1656247) B1656247
theorem B9450269 : Blo 980594 9450269 := bstep (se 3 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 9450269 = 3543851) B3543851
theorem B2208743 : Blo 980594 2208743 := bstep (se 1 (by rfl) ⟨1656557, by rfl⟩ : syracuseStep 2208743 = 3313115) B3313115
theorem B2209121 : Blo 980594 2209121 := bstep (se 2 (by rfl) ⟨828420, by rfl⟩ : syracuseStep 2209121 = 1656841) B1656841
theorem B2209211 : Blo 980594 2209211 := bstep (se 1 (by rfl) ⟨1656908, by rfl⟩ : syracuseStep 2209211 = 3313817) B3313817
theorem B2209337 : Blo 980594 2209337 := bstep (se 2 (by rfl) ⟨828501, by rfl⟩ : syracuseStep 2209337 = 1657003) B1657003
theorem B2210003 : Blo 980594 2210003 := bstep (se 1 (by rfl) ⟨1657502, by rfl⟩ : syracuseStep 2210003 = 3315005) B3315005
theorem B2210057 : Blo 980594 2210057 := bstep (se 2 (by rfl) ⟨828771, by rfl⟩ : syracuseStep 2210057 = 1657543) B1657543
theorem B8075645 : Blo 980594 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B2210273 : Blo 980594 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B2210579 : Blo 980594 2210579 := bstep (se 1 (by rfl) ⟨1657934, by rfl⟩ : syracuseStep 2210579 = 3315869) B3315869
theorem B2243623 : Blo 980594 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2210939 : Blo 980594 2210939 := bstep (se 1 (by rfl) ⟨1658204, by rfl⟩ : syracuseStep 2210939 = 3316409) B3316409
theorem B2211065 : Blo 980594 2211065 := bstep (se 2 (by rfl) ⟨829149, by rfl⟩ : syracuseStep 2211065 = 1658299) B1658299
theorem B2211209 : Blo 980594 2211209 := bstep (se 2 (by rfl) ⟨829203, by rfl⟩ : syracuseStep 2211209 = 1658407) B1658407
theorem B2211335 : Blo 980594 2211335 := bstep (se 1 (by rfl) ⟨1658501, by rfl⟩ : syracuseStep 2211335 = 3317003) B3317003
theorem B6471191 : Blo 980594 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B8404505 : Blo 980594 8404505 := bstep (se 2 (by rfl) ⟨3151689, by rfl⟩ : syracuseStep 8404505 = 6303379) B6303379
theorem B7454267 : Blo 980594 7454267 := bstep (se 1 (by rfl) ⟨5590700, by rfl⟩ : syracuseStep 7454267 = 11181401) B11181401
theorem B2211515 : Blo 980594 2211515 := bstep (se 1 (by rfl) ⟨1658636, by rfl⟩ : syracuseStep 2211515 = 3317273) B3317273
theorem B1261279 : Blo 980594 1261279 := bstep (se 1 (by rfl) ⟨945959, by rfl⟩ : syracuseStep 1261279 = 1891919) B1891919
theorem B5586691 : Blo 980594 5586691 := bstep (se 1 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 5586691 = 8380037) B8380037
theorem B2211641 : Blo 980594 2211641 := bstep (se 2 (by rfl) ⟨829365, by rfl⟩ : syracuseStep 2211641 = 1658731) B1658731
theorem B2801537 : Blo 980594 2801537 := bstep (se 2 (by rfl) ⟨1050576, by rfl⟩ : syracuseStep 2801537 = 2101153) B2101153
theorem B2244937 : Blo 980594 2244937 := bstep (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) B1683703
theorem B2212271 : Blo 980594 2212271 := bstep (se 1 (by rfl) ⟨1659203, by rfl⟩ : syracuseStep 2212271 = 3318407) B3318407
theorem B2212307 : Blo 980594 2212307 := bstep (se 1 (by rfl) ⟨1659230, by rfl⟩ : syracuseStep 2212307 = 3318461) B3318461
theorem B2212415 : Blo 980594 2212415 := bstep (se 1 (by rfl) ⟨1659311, by rfl⟩ : syracuseStep 2212415 = 3318623) B3318623
theorem B3785287 : Blo 980594 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B1655417 : Blo 980594 1655417 := bstep (se 2 (by rfl) ⟨620781, by rfl⟩ : syracuseStep 1655417 = 1241563) B1241563
theorem B2212523 : Blo 980594 2212523 := bstep (se 1 (by rfl) ⟨1659392, by rfl⟩ : syracuseStep 2212523 = 3318785) B3318785
theorem B1655471 : Blo 980594 1655471 := bstep (se 1 (by rfl) ⟨1241603, by rfl⟩ : syracuseStep 1655471 = 2483207) B2483207
theorem B3588943 : Blo 980594 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B1655707 : Blo 980594 1655707 := bstep (se 1 (by rfl) ⟨1241780, by rfl⟩ : syracuseStep 1655707 = 2483561) B2483561
theorem B143213507 : Blo 980594 143213507 := bstep (se 1 (by rfl) ⟨107410130, by rfl⟩ : syracuseStep 143213507 = 214820261) B214820261
theorem B11944967 : Blo 980594 11944967 := bstep (se 1 (by rfl) ⟨8958725, by rfl⟩ : syracuseStep 11944967 = 17917451) B17917451
theorem B2213063 : Blo 980594 2213063 := bstep (se 1 (by rfl) ⟨1659797, by rfl⟩ : syracuseStep 2213063 = 3319595) B3319595
theorem B2802937 : Blo 980594 2802937 := bstep (se 2 (by rfl) ⟨1051101, by rfl⟩ : syracuseStep 2802937 = 2102203) B2102203
theorem B2213243 : Blo 980594 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B12567959 : Blo 980594 12567959 := bstep (se 1 (by rfl) ⟨9425969, by rfl⟩ : syracuseStep 12567959 = 18851939) B18851939
theorem B2213369 : Blo 980594 2213369 := bstep (se 2 (by rfl) ⟨830013, by rfl⟩ : syracuseStep 2213369 = 1660027) B1660027
theorem B2213459 : Blo 980594 2213459 := bstep (se 1 (by rfl) ⟨1660094, by rfl⟩ : syracuseStep 2213459 = 3320189) B3320189
theorem B1328815 : Blo 980594 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B2213639 : Blo 980594 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B4966433 : Blo 980594 4966433 := bstep (se 2 (by rfl) ⟨1862412, by rfl⟩ : syracuseStep 4966433 = 3724825) B3724825
theorem B4966595 : Blo 980594 4966595 := bstep (se 1 (by rfl) ⟨3724946, by rfl⟩ : syracuseStep 4966595 = 7449893) B7449893
theorem B245057879 : Blo 980594 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B2214251 : Blo 980594 2214251 := bstep (se 1 (by rfl) ⟨1660688, by rfl⟩ : syracuseStep 2214251 = 3321377) B3321377
theorem B1657199 : Blo 980594 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B6048229 : Blo 980594 6048229 := bstep (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) B1134043
theorem B2214395 : Blo 980594 2214395 := bstep (se 1 (by rfl) ⟨1660796, by rfl⟩ : syracuseStep 2214395 = 3321593) B3321593
theorem B1657415 : Blo 980594 1657415 := bstep (se 1 (by rfl) ⟨1243061, by rfl⟩ : syracuseStep 1657415 = 2486123) B2486123
theorem B2214521 : Blo 980594 2214521 := bstep (se 2 (by rfl) ⟨830445, by rfl⟩ : syracuseStep 2214521 = 1660891) B1660891
theorem B2214575 : Blo 980594 2214575 := bstep (se 1 (by rfl) ⟨1660931, by rfl⟩ : syracuseStep 2214575 = 3321863) B3321863
theorem B2214647 : Blo 980594 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B10636049 : Blo 980594 10636049 := bstep (se 2 (by rfl) ⟨3988518, by rfl⟩ : syracuseStep 10636049 = 7977037) B7977037
theorem B2214827 : Blo 980594 2214827 := bstep (se 1 (by rfl) ⟨1661120, by rfl⟩ : syracuseStep 2214827 = 3322241) B3322241
theorem B1657847 : Blo 980594 1657847 := bstep (se 1 (by rfl) ⟨1243385, by rfl⟩ : syracuseStep 1657847 = 2486771) B2486771
theorem B3984707 : Blo 980594 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B1658603 : Blo 980594 1658603 := bstep (se 1 (by rfl) ⟨1243952, by rfl⟩ : syracuseStep 1658603 = 2487905) B2487905
theorem B8408879 : Blo 980594 8408879 := bstep (se 1 (by rfl) ⟨6306659, by rfl⟩ : syracuseStep 8408879 = 12613319) B12613319
theorem B5591065 : Blo 980594 5591065 := bstep (se 2 (by rfl) ⟨2096649, by rfl⟩ : syracuseStep 5591065 = 4193299) B4193299
theorem B1397083 : Blo 980594 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B3985939 : Blo 980594 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B1659575 : Blo 980594 1659575 := bstep (se 1 (by rfl) ⟨1244681, by rfl⟩ : syracuseStep 1659575 = 2489363) B2489363
theorem B3986783 : Blo 980594 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B1103215 : Blo 980594 1103215 := bstep (se 1 (by rfl) ⟨827411, by rfl⟩ : syracuseStep 1103215 = 1654823) B1654823
theorem B1660297 : Blo 980594 1660297 := bstep (se 2 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 1660297 = 1245223) B1245223
theorem B2840071 : Blo 980594 2840071 := bstep (se 1 (by rfl) ⟨2130053, by rfl⟩ : syracuseStep 2840071 = 4260107) B4260107
theorem B1103431 : Blo 980594 1103431 := bstep (se 1 (by rfl) ⟨827573, by rfl⟩ : syracuseStep 1103431 = 1655147) B1655147
theorem B1365727 : Blo 980594 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B1660729 : Blo 980594 1660729 := bstep (se 2 (by rfl) ⟨622773, by rfl⟩ : syracuseStep 1660729 = 1245547) B1245547
theorem B4970321 : Blo 980594 4970321 := bstep (se 2 (by rfl) ⟨1863870, by rfl⟩ : syracuseStep 4970321 = 3727741) B3727741
theorem B7952417 : Blo 980594 7952417 := bstep (se 2 (by rfl) ⟨2982156, by rfl⟩ : syracuseStep 7952417 = 5964313) B5964313
theorem B1661033 : Blo 980594 1661033 := bstep (se 2 (by rfl) ⟨622887, by rfl⟩ : syracuseStep 1661033 = 1245775) B1245775
theorem B1104295 : Blo 980594 1104295 := bstep (se 1 (by rfl) ⟨828221, by rfl⟩ : syracuseStep 1104295 = 1656443) B1656443
theorem B4971131 : Blo 980594 4971131 := bstep (se 1 (by rfl) ⟨3728348, by rfl⟩ : syracuseStep 4971131 = 7456697) B7456697
theorem B3726071 : Blo 980594 3726071 := bstep (se 1 (by rfl) ⟨2794553, by rfl⟩ : syracuseStep 3726071 = 5589107) B5589107
theorem B1399783 : Blo 980594 1399783 := bstep (se 1 (by rfl) ⟨1049837, by rfl⟩ : syracuseStep 1399783 = 2099675) B2099675
theorem B1104871 : Blo 980594 1104871 := bstep (se 1 (by rfl) ⟨828653, by rfl⟩ : syracuseStep 1104871 = 1657307) B1657307
theorem B1892027 : Blo 980594 1892027 := bstep (se 1 (by rfl) ⟨1419020, by rfl⟩ : syracuseStep 1892027 = 2838041) B2838041
theorem B1597163 : Blo 980594 1597163 := bstep (se 1 (by rfl) ⟨1197872, by rfl⟩ : syracuseStep 1597163 = 2395745) B2395745
theorem B6283183 : Blo 980594 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B4973075 : Blo 980594 4973075 := bstep (se 1 (by rfl) ⟨3729806, by rfl⟩ : syracuseStep 4973075 = 7459613) B7459613
theorem B2482751 : Blo 980594 2482751 := bstep (se 1 (by rfl) ⟨1862063, by rfl⟩ : syracuseStep 2482751 = 3724127) B3724127
theorem B1106527 : Blo 980594 1106527 := bstep (se 1 (by rfl) ⟨829895, by rfl⟩ : syracuseStep 1106527 = 1659791) B1659791
theorem B8971067 : Blo 980594 8971067 := bstep (se 1 (by rfl) ⟨6728300, by rfl⟩ : syracuseStep 8971067 = 13456601) B13456601
theorem B15918065 : Blo 980594 15918065 := bstep (se 2 (by rfl) ⟨5969274, by rfl⟩ : syracuseStep 15918065 = 11938549) B11938549
theorem B8610823 : Blo 980594 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B3728531 : Blo 980594 3728531 := bstep (se 1 (by rfl) ⟨2796398, by rfl⟩ : syracuseStep 3728531 = 5592797) B5592797
theorem B2483399 : Blo 980594 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B2483419 : Blo 980594 2483419 := bstep (se 1 (by rfl) ⟨1862564, by rfl⟩ : syracuseStep 2483419 = 3725129) B3725129
theorem B68085497 : Blo 980594 68085497 := bstep (se 2 (by rfl) ⟨25532061, by rfl⟩ : syracuseStep 68085497 = 51064123) B51064123
theorem B87353153 : Blo 980594 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B12576617 : Blo 980594 12576617 := bstep (se 2 (by rfl) ⟨4716231, by rfl⟩ : syracuseStep 12576617 = 9432463) B9432463
theorem B40331357 : Blo 980594 40331357 := bstep (se 3 (by rfl) ⟨7562129, by rfl⟩ : syracuseStep 40331357 = 15124259) B15124259
theorem B4974857 : Blo 980594 4974857 := bstep (se 2 (by rfl) ⟨1865571, by rfl⟩ : syracuseStep 4974857 = 3731143) B3731143
theorem B2484553 : Blo 980594 2484553 := bstep (se 2 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 2484553 = 1863415) B1863415
theorem B7465445 : Blo 980594 7465445 := bstep (se 4 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 7465445 = 1399771) B1399771
theorem B10644047 : Blo 980594 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B2484857 : Blo 980594 2484857 := bstep (se 2 (by rfl) ⟨931821, by rfl⟩ : syracuseStep 2484857 = 1863643) B1863643
theorem B4188995 : Blo 980594 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B4713389 : Blo 980594 4713389 := bstep (se 3 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 4713389 = 1767521) B1767521
theorem B7072849 : Blo 980594 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B4975991 : Blo 980594 4975991 := bstep (se 1 (by rfl) ⟨3731993, by rfl⟩ : syracuseStep 4975991 = 7463987) B7463987
theorem B4976153 : Blo 980594 4976153 := bstep (se 2 (by rfl) ⟨1866057, by rfl⟩ : syracuseStep 4976153 = 3732115) B3732115
theorem B1863263 : Blo 980594 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B6287057 : Blo 980594 6287057 := bstep (se 2 (by rfl) ⟨2357646, by rfl⟩ : syracuseStep 6287057 = 4715293) B4715293
theorem B5664491 : Blo 980594 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B57438001 : Blo 980594 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B2125673 : Blo 980594 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B2126089 : Blo 980594 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B2486639 : Blo 980594 2486639 := bstep (se 1 (by rfl) ⟨1864979, by rfl⟩ : syracuseStep 2486639 = 3729959) B3729959
theorem B1470971 : Blo 980594 1470971 := bstep (se 1 (by rfl) ⟨1103228, by rfl⟩ : syracuseStep 1470971 = 2206457) B2206457
theorem B1471097 : Blo 980594 1471097 := bstep (se 2 (by rfl) ⟨551661, by rfl⟩ : syracuseStep 1471097 = 1103323) B1103323
theorem B1471151 : Blo 980594 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B1471199 : Blo 980594 1471199 := bstep (se 1 (by rfl) ⟨1103399, by rfl⟩ : syracuseStep 1471199 = 2206799) B2206799
theorem B3732419 : Blo 980594 3732419 := bstep (se 1 (by rfl) ⟨2799314, by rfl⟩ : syracuseStep 3732419 = 5598629) B5598629
theorem B1471463 : Blo 980594 1471463 := bstep (se 1 (by rfl) ⟨1103597, by rfl⟩ : syracuseStep 1471463 = 2207195) B2207195
theorem B2487287 : Blo 980594 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B4715617 : Blo 980594 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B2487419 : Blo 980594 2487419 := bstep (se 1 (by rfl) ⟨1865564, by rfl⟩ : syracuseStep 2487419 = 3731129) B3731129
theorem B16774289 : Blo 980594 16774289 := bstep (se 2 (by rfl) ⟨6290358, by rfl⟩ : syracuseStep 16774289 = 12580717) B12580717
theorem B1471721 : Blo 980594 1471721 := bstep (se 2 (by rfl) ⟨551895, by rfl⟩ : syracuseStep 1471721 = 1103791) B1103791
theorem B1471775 : Blo 980594 1471775 := bstep (se 1 (by rfl) ⟨1103831, by rfl⟩ : syracuseStep 1471775 = 2207663) B2207663
theorem B1242479 : Blo 980594 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B3732875 : Blo 980594 3732875 := bstep (se 1 (by rfl) ⟨2799656, by rfl⟩ : syracuseStep 3732875 = 5599313) B5599313
theorem B1242535 : Blo 980594 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B1471943 : Blo 980594 1471943 := bstep (se 1 (by rfl) ⟨1103957, by rfl⟩ : syracuseStep 1471943 = 2207915) B2207915
theorem B980703 : Blo 980594 980703 := bstep (se 1 (by rfl) ⟨735527, by rfl⟩ : syracuseStep 980703 = 1471055) B1471055
theorem B1242859 : Blo 980594 1242859 := bstep (se 1 (by rfl) ⟨932144, by rfl⟩ : syracuseStep 1242859 = 1864289) B1864289
theorem B1472297 : Blo 980594 1472297 := bstep (se 2 (by rfl) ⟨552111, by rfl⟩ : syracuseStep 1472297 = 1104223) B1104223
theorem B980783 : Blo 980594 980783 := bstep (se 1 (by rfl) ⟨735587, by rfl⟩ : syracuseStep 980783 = 1471175) B1471175
theorem B1472303 : Blo 980594 1472303 := bstep (se 1 (by rfl) ⟨1104227, by rfl⟩ : syracuseStep 1472303 = 2208455) B2208455
theorem B980891 : Blo 980594 980891 := bstep (se 1 (by rfl) ⟨735668, by rfl⟩ : syracuseStep 980891 = 1471337) B1471337
theorem B980943 : Blo 980594 980943 := bstep (se 1 (by rfl) ⟨735707, by rfl⟩ : syracuseStep 980943 = 1471415) B1471415
theorem B2521039 : Blo 980594 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B980967 : Blo 980594 980967 := bstep (se 1 (by rfl) ⟨735725, by rfl⟩ : syracuseStep 980967 = 1471451) B1471451
theorem B1472777 : Blo 980594 1472777 := bstep (se 2 (by rfl) ⟨552291, by rfl⟩ : syracuseStep 1472777 = 1104583) B1104583
theorem B981279 : Blo 980594 981279 := bstep (se 1 (by rfl) ⟨735959, by rfl⟩ : syracuseStep 981279 = 1471919) B1471919
theorem B981339 : Blo 980594 981339 := bstep (se 1 (by rfl) ⟨736004, by rfl⟩ : syracuseStep 981339 = 1472009) B1472009
theorem B981359 : Blo 980594 981359 := bstep (se 1 (by rfl) ⟨736019, by rfl⟩ : syracuseStep 981359 = 1472039) B1472039
theorem B1472879 : Blo 980594 1472879 := bstep (se 1 (by rfl) ⟨1104659, by rfl⟩ : syracuseStep 1472879 = 2209319) B2209319
theorem B4979069 : Blo 980594 4979069 := bstep (se 3 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 4979069 = 1867151) B1867151
theorem B981415 : Blo 980594 981415 := bstep (se 1 (by rfl) ⟨736061, by rfl⟩ : syracuseStep 981415 = 1472123) B1472123
theorem B18905521 : Blo 980594 18905521 := bstep (se 2 (by rfl) ⟨7089570, by rfl⟩ : syracuseStep 18905521 = 14179141) B14179141
theorem B14186933 : Blo 980594 14186933 := bstep (se 5 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 14186933 = 1330025) B1330025
theorem B981499 : Blo 980594 981499 := bstep (se 1 (by rfl) ⟨736124, by rfl⟩ : syracuseStep 981499 = 1472249) B1472249
theorem B981567 : Blo 980594 981567 := bstep (se 1 (by rfl) ⟨736175, by rfl⟩ : syracuseStep 981567 = 1472351) B1472351
theorem B981575 : Blo 980594 981575 := bstep (se 1 (by rfl) ⟨736181, by rfl⟩ : syracuseStep 981575 = 1472363) B1472363
theorem B1473095 : Blo 980594 1473095 := bstep (se 1 (by rfl) ⟨1104821, by rfl⟩ : syracuseStep 1473095 = 2209643) B2209643
theorem B5306953 : Blo 980594 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B1473131 : Blo 980594 1473131 := bstep (se 1 (by rfl) ⟨1104848, by rfl⟩ : syracuseStep 1473131 = 2209697) B2209697
theorem B1866415 : Blo 980594 1866415 := bstep (se 1 (by rfl) ⟨1399811, by rfl⟩ : syracuseStep 1866415 = 2799623) B2799623
theorem B1243831 : Blo 980594 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B981727 : Blo 980594 981727 := bstep (se 1 (by rfl) ⟨736295, by rfl⟩ : syracuseStep 981727 = 1472591) B1472591
theorem B981807 : Blo 980594 981807 := bstep (se 1 (by rfl) ⟨736355, by rfl⟩ : syracuseStep 981807 = 1472711) B1472711
theorem B1473359 : Blo 980594 1473359 := bstep (se 1 (by rfl) ⟨1105019, by rfl⟩ : syracuseStep 1473359 = 2210039) B2210039
theorem B2489231 : Blo 980594 2489231 := bstep (se 1 (by rfl) ⟨1866923, by rfl⟩ : syracuseStep 2489231 = 3733847) B3733847
theorem B2096027 : Blo 980594 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B981915 : Blo 980594 981915 := bstep (se 1 (by rfl) ⟨736436, by rfl⟩ : syracuseStep 981915 = 1472873) B1472873
theorem B981967 : Blo 980594 981967 := bstep (se 1 (by rfl) ⟨736475, by rfl⟩ : syracuseStep 981967 = 1472951) B1472951
theorem B1571815 : Blo 980594 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B981991 : Blo 980594 981991 := bstep (se 1 (by rfl) ⟨736493, by rfl⟩ : syracuseStep 981991 = 1472987) B1472987
theorem B12582053 : Blo 980594 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B1473755 : Blo 980594 1473755 := bstep (se 1 (by rfl) ⟨1105316, by rfl⟩ : syracuseStep 1473755 = 2210633) B2210633
theorem B2358521 : Blo 980594 2358521 := bstep (se 2 (by rfl) ⟨884445, by rfl⟩ : syracuseStep 2358521 = 1768891) B1768891
theorem B982303 : Blo 980594 982303 := bstep (se 1 (by rfl) ⟨736727, by rfl⟩ : syracuseStep 982303 = 1473455) B1473455
theorem B982363 : Blo 980594 982363 := bstep (se 1 (by rfl) ⟨736772, by rfl⟩ : syracuseStep 982363 = 1473545) B1473545
theorem B2096479 : Blo 980594 2096479 := bstep (se 1 (by rfl) ⟨1572359, by rfl⟩ : syracuseStep 2096479 = 3144719) B3144719
theorem B982383 : Blo 980594 982383 := bstep (se 1 (by rfl) ⟨736787, by rfl⟩ : syracuseStep 982383 = 1473575) B1473575
theorem B1473929 : Blo 980594 1473929 := bstep (se 2 (by rfl) ⟨552723, by rfl⟩ : syracuseStep 1473929 = 1105447) B1105447
theorem B2489737 : Blo 980594 2489737 := bstep (se 2 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 2489737 = 1867303) B1867303
theorem B982439 : Blo 980594 982439 := bstep (se 1 (by rfl) ⟨736829, by rfl⟩ : syracuseStep 982439 = 1473659) B1473659
theorem B4488635 : Blo 980594 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B2489849 : Blo 980594 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B982523 : Blo 980594 982523 := bstep (se 1 (by rfl) ⟨736892, by rfl⟩ : syracuseStep 982523 = 1473785) B1473785
theorem B2653703 : Blo 980594 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B982591 : Blo 980594 982591 := bstep (se 1 (by rfl) ⟨736943, by rfl⟩ : syracuseStep 982591 = 1473887) B1473887
theorem B982599 : Blo 980594 982599 := bstep (se 1 (by rfl) ⟨736949, by rfl⟩ : syracuseStep 982599 = 1473899) B1473899
theorem B982751 : Blo 980594 982751 := bstep (se 1 (by rfl) ⟨737063, by rfl⟩ : syracuseStep 982751 = 1474127) B1474127
theorem B1277675 : Blo 980594 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B1474283 : Blo 980594 1474283 := bstep (se 1 (by rfl) ⟨1105712, by rfl⟩ : syracuseStep 1474283 = 2211425) B2211425
theorem B982831 : Blo 980594 982831 := bstep (se 1 (by rfl) ⟨737123, by rfl⟩ : syracuseStep 982831 = 1474247) B1474247
theorem B4980527 : Blo 980594 4980527 := bstep (se 1 (by rfl) ⟨3735395, by rfl⟩ : syracuseStep 4980527 = 7470791) B7470791
theorem B982939 : Blo 980594 982939 := bstep (se 1 (by rfl) ⟨737204, by rfl⟩ : syracuseStep 982939 = 1474409) B1474409
theorem B982991 : Blo 980594 982991 := bstep (se 1 (by rfl) ⟨737243, by rfl⟩ : syracuseStep 982991 = 1474487) B1474487
theorem B1474511 : Blo 980594 1474511 := bstep (se 1 (by rfl) ⟨1105883, by rfl⟩ : syracuseStep 1474511 = 2211767) B2211767
theorem B983015 : Blo 980594 983015 := bstep (se 1 (by rfl) ⟨737261, by rfl⟩ : syracuseStep 983015 = 1474523) B1474523
theorem B82903045 : Blo 980594 82903045 := bstep (se 4 (by rfl) ⟨7772160, by rfl⟩ : syracuseStep 82903045 = 15544321) B15544321
theorem B983271 : Blo 980594 983271 := bstep (se 1 (by rfl) ⟨737453, by rfl⟩ : syracuseStep 983271 = 1474907) B1474907
theorem B1474847 : Blo 980594 1474847 := bstep (se 1 (by rfl) ⟨1106135, by rfl⟩ : syracuseStep 1474847 = 2212271) B2212271
theorem B1474871 : Blo 980594 1474871 := bstep (se 1 (by rfl) ⟨1106153, by rfl⟩ : syracuseStep 1474871 = 2212307) B2212307
theorem B1474943 : Blo 980594 1474943 := bstep (se 1 (by rfl) ⟨1106207, by rfl⟩ : syracuseStep 1474943 = 2212415) B2212415
theorem B983423 : Blo 980594 983423 := bstep (se 1 (by rfl) ⟨737567, by rfl⟩ : syracuseStep 983423 = 1475135) B1475135
theorem B4981175 : Blo 980594 4981175 := bstep (se 1 (by rfl) ⟨3735881, by rfl⟩ : syracuseStep 4981175 = 7471763) B7471763
theorem B1475015 : Blo 980594 1475015 := bstep (se 1 (by rfl) ⟨1106261, by rfl⟩ : syracuseStep 1475015 = 2212523) B2212523
theorem B983503 : Blo 980594 983503 := bstep (se 1 (by rfl) ⟨737627, by rfl⟩ : syracuseStep 983503 = 1475255) B1475255
theorem B983655 : Blo 980594 983655 := bstep (se 1 (by rfl) ⟨737741, by rfl⟩ : syracuseStep 983655 = 1475483) B1475483
theorem B6292205 : Blo 980594 6292205 := bstep (se 3 (by rfl) ⟨1179788, by rfl⟩ : syracuseStep 6292205 = 2359577) B2359577
theorem B5047049 : Blo 980594 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B2491145 : Blo 980594 2491145 := bstep (se 2 (by rfl) ⟨934179, by rfl⟩ : syracuseStep 2491145 = 1868359) B1868359
theorem B1475369 : Blo 980594 1475369 := bstep (se 2 (by rfl) ⟨553263, by rfl⟩ : syracuseStep 1475369 = 1106527) B1106527
theorem B1475375 : Blo 980594 1475375 := bstep (se 1 (by rfl) ⟨1106531, by rfl⟩ : syracuseStep 1475375 = 2213063) B2213063
theorem B983919 : Blo 980594 983919 := bstep (se 1 (by rfl) ⟨737939, by rfl⟩ : syracuseStep 983919 = 1475879) B1475879
theorem B4981661 : Blo 980594 4981661 := bstep (se 3 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 4981661 = 1868123) B1868123
theorem B1475495 : Blo 980594 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B983975 : Blo 980594 983975 := bstep (se 1 (by rfl) ⟨737981, by rfl⟩ : syracuseStep 983975 = 1475963) B1475963
theorem B1770491 : Blo 980594 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B1475579 : Blo 980594 1475579 := bstep (se 1 (by rfl) ⟨1106684, by rfl⟩ : syracuseStep 1475579 = 2213369) B2213369
theorem B984059 : Blo 980594 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B1475639 : Blo 980594 1475639 := bstep (se 1 (by rfl) ⟨1106729, by rfl⟩ : syracuseStep 1475639 = 2213459) B2213459
theorem B984127 : Blo 980594 984127 := bstep (se 1 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 984127 = 1476191) B1476191
theorem B4785257 : Blo 980594 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B1475759 : Blo 980594 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B984271 : Blo 980594 984271 := bstep (se 1 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 984271 = 1476407) B1476407
theorem B3310955 : Blo 980594 3310955 := bstep (se 1 (by rfl) ⟨2483216, by rfl⟩ : syracuseStep 3310955 = 4966433) B4966433
theorem B984475 : Blo 980594 984475 := bstep (se 1 (by rfl) ⟨738356, by rfl⟩ : syracuseStep 984475 = 1476713) B1476713
theorem B2491823 : Blo 980594 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B3311063 : Blo 980594 3311063 := bstep (se 1 (by rfl) ⟨2483297, by rfl⟩ : syracuseStep 3311063 = 4966595) B4966595
theorem B1476167 : Blo 980594 1476167 := bstep (se 1 (by rfl) ⟨1107125, by rfl⟩ : syracuseStep 1476167 = 2214251) B2214251
theorem B7472735 : Blo 980594 7472735 := bstep (se 1 (by rfl) ⟨5604551, by rfl⟩ : syracuseStep 7472735 = 11209103) B11209103
theorem B3311225 : Blo 980594 3311225 := bstep (se 2 (by rfl) ⟨1241709, by rfl⟩ : syracuseStep 3311225 = 2483419) B2483419
theorem B3737249 : Blo 980594 3737249 := bstep (se 2 (by rfl) ⟨1401468, by rfl⟩ : syracuseStep 3737249 = 2802937) B2802937
theorem B1476263 : Blo 980594 1476263 := bstep (se 1 (by rfl) ⟨1107197, by rfl⟩ : syracuseStep 1476263 = 2214395) B2214395
theorem B1476347 : Blo 980594 1476347 := bstep (se 1 (by rfl) ⟨1107260, by rfl⟩ : syracuseStep 1476347 = 2214521) B2214521
theorem B1476383 : Blo 980594 1476383 := bstep (se 1 (by rfl) ⟨1107287, by rfl⟩ : syracuseStep 1476383 = 2214575) B2214575
theorem B4720463 : Blo 980594 4720463 := bstep (se 1 (by rfl) ⟨3540347, by rfl⟩ : syracuseStep 4720463 = 7080695) B7080695
theorem B1476431 : Blo 980594 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B1476551 : Blo 980594 1476551 := bstep (se 1 (by rfl) ⟨1107413, by rfl⟩ : syracuseStep 1476551 = 2214827) B2214827
theorem B8390699 : Blo 980594 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B6293639 : Blo 980594 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B2656471 : Blo 980594 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B1771753 : Blo 980594 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B2099513 : Blo 980594 2099513 := bstep (se 2 (by rfl) ⟨787317, by rfl⟩ : syracuseStep 2099513 = 1574635) B1574635
theorem B3737947 : Blo 980594 3737947 := bstep (se 1 (by rfl) ⟨2803460, by rfl⟩ : syracuseStep 3737947 = 5606921) B5606921
theorem B5605919 : Blo 980594 5605919 := bstep (se 1 (by rfl) ⟨4204439, by rfl⟩ : syracuseStep 5605919 = 8408879) B8408879
theorem B4983443 : Blo 980594 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B31853245 : Blo 980594 31853245 := bstep (se 3 (by rfl) ⟨5972483, by rfl⟩ : syracuseStep 31853245 = 11944967) B11944967
theorem B3312737 : Blo 980594 3312737 := bstep (se 2 (by rfl) ⟨1242276, by rfl⟩ : syracuseStep 3312737 = 2484553) B2484553
theorem B8064305 : Blo 980594 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B4984253 : Blo 980594 4984253 := bstep (se 3 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 4984253 = 1869095) B1869095
theorem B2657855 : Blo 980594 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B3313277 : Blo 980594 3313277 := bstep (se 3 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 3313277 = 1242479) B1242479
theorem B3313547 : Blo 980594 3313547 := bstep (se 1 (by rfl) ⟨2485160, by rfl⟩ : syracuseStep 3313547 = 4970321) B4970321
theorem B3150191 : Blo 980594 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B5968255 : Blo 980594 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B3314087 : Blo 980594 3314087 := bstep (se 1 (by rfl) ⟨2485565, by rfl⟩ : syracuseStep 3314087 = 4971131) B4971131
theorem B6296615 : Blo 980594 6296615 := bstep (se 1 (by rfl) ⟨4722461, by rfl⟩ : syracuseStep 6296615 = 9444923) B9444923
theorem B76584001 : Blo 980594 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B3315383 : Blo 980594 3315383 := bstep (se 1 (by rfl) ⟨2486537, by rfl⟩ : syracuseStep 3315383 = 4973075) B4973075
theorem B4200407 : Blo 980594 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B17962993 : Blo 980594 17962993 := bstep (se 2 (by rfl) ⟨6736122, by rfl⟩ : syracuseStep 17962993 = 13472245) B13472245
theorem B5314585 : Blo 980594 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B2365537 : Blo 980594 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B18880613 : Blo 980594 18880613 := bstep (se 4 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 18880613 = 3540115) B3540115
theorem B2365595 : Blo 980594 2365595 := bstep (se 1 (by rfl) ⟨1774196, by rfl⟩ : syracuseStep 2365595 = 3548393) B3548393
theorem B45390331 : Blo 980594 45390331 := bstep (se 1 (by rfl) ⟨34042748, by rfl⟩ : syracuseStep 45390331 = 68085497) B68085497
theorem B58235435 : Blo 980594 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B3316571 : Blo 980594 3316571 := bstep (se 1 (by rfl) ⟨2487428, by rfl⟩ : syracuseStep 3316571 = 4974857) B4974857
theorem B2792663 : Blo 980594 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B3317327 : Blo 980594 3317327 := bstep (se 1 (by rfl) ⟨2487995, by rfl⟩ : syracuseStep 3317327 = 4975991) B4975991
theorem B3317435 : Blo 980594 3317435 := bstep (se 1 (by rfl) ⟨2488076, by rfl⟩ : syracuseStep 3317435 = 4976153) B4976153
theorem B3776327 : Blo 980594 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B1417115 : Blo 980594 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B1515419 : Blo 980594 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B6300179 : Blo 980594 6300179 := bstep (se 1 (by rfl) ⟨4725134, by rfl⟩ : syracuseStep 6300179 = 9450269) B9450269
theorem B25207361 : Blo 980594 25207361 := bstep (se 2 (by rfl) ⟨9452760, by rfl⟩ : syracuseStep 25207361 = 18905521) B18905521
theorem B11182859 : Blo 980594 11182859 := bstep (se 1 (by rfl) ⟨8387144, by rfl⟩ : syracuseStep 11182859 = 16774289) B16774289
theorem B11969693 : Blo 980594 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B15148397 : Blo 980594 15148397 := bstep (se 3 (by rfl) ⟨2840324, by rfl⟩ : syracuseStep 15148397 = 5680649) B5680649
theorem B2991497 : Blo 980594 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B5383763 : Blo 980594 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B3319379 : Blo 980594 3319379 := bstep (se 1 (by rfl) ⟨2489534, by rfl⟩ : syracuseStep 3319379 = 4979069) B4979069
theorem B2795305 : Blo 980594 2795305 := bstep (se 2 (by rfl) ⟨1048239, by rfl⟩ : syracuseStep 2795305 = 2096479) B2096479
theorem B3319649 : Blo 980594 3319649 := bstep (se 2 (by rfl) ⟨1244868, by rfl⟩ : syracuseStep 3319649 = 2489737) B2489737
theorem B1681705 : Blo 980594 1681705 := bstep (se 2 (by rfl) ⟨630639, by rfl⟩ : syracuseStep 1681705 = 1261279) B1261279
theorem B7448921 : Blo 980594 7448921 := bstep (se 2 (by rfl) ⟨2793345, by rfl⟩ : syracuseStep 7448921 = 5586691) B5586691
theorem B3320351 : Blo 980594 3320351 := bstep (se 1 (by rfl) ⟨2490263, by rfl⟩ : syracuseStep 3320351 = 4980527) B4980527
theorem B68037569 : Blo 980594 68037569 := bstep (se 2 (by rfl) ⟨25514088, by rfl⟩ : syracuseStep 68037569 = 51028177) B51028177
theorem B2993249 : Blo 980594 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B2206943 : Blo 980594 2206943 := bstep (se 1 (by rfl) ⟨1655207, by rfl⟩ : syracuseStep 2206943 = 3310415) B3310415
theorem B2796923 : Blo 980594 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B2207159 : Blo 980594 2207159 := bstep (se 1 (by rfl) ⟨1655369, by rfl⟩ : syracuseStep 2207159 = 3310739) B3310739
theorem B2207339 : Blo 980594 2207339 := bstep (se 1 (by rfl) ⟨1655504, by rfl⟩ : syracuseStep 2207339 = 3311009) B3311009
theorem B2797163 : Blo 980594 2797163 := bstep (se 1 (by rfl) ⟨2097872, by rfl⟩ : syracuseStep 2797163 = 4195745) B4195745
theorem B2207609 : Blo 980594 2207609 := bstep (se 2 (by rfl) ⟨827853, by rfl⟩ : syracuseStep 2207609 = 1655707) B1655707
theorem B3321755 : Blo 980594 3321755 := bstep (se 1 (by rfl) ⟨2491316, by rfl⟩ : syracuseStep 3321755 = 4982633) B4982633
theorem B11481097 : Blo 980594 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B2798039 : Blo 980594 2798039 := bstep (se 1 (by rfl) ⟨2098529, by rfl⟩ : syracuseStep 2798039 = 4197059) B4197059
theorem B7090699 : Blo 980594 7090699 := bstep (se 1 (by rfl) ⟨5318024, by rfl⟩ : syracuseStep 7090699 = 10636049) B10636049
theorem B7451351 : Blo 980594 7451351 := bstep (se 1 (by rfl) ⟨5588513, by rfl⟩ : syracuseStep 7451351 = 11177027) B11177027
theorem B3322889 : Blo 980594 3322889 := bstep (se 2 (by rfl) ⟨1246083, by rfl⟩ : syracuseStep 3322889 = 2492167) B2492167
theorem B3322943 : Blo 980594 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B7452323 : Blo 980594 7452323 := bstep (se 1 (by rfl) ⟨5589242, by rfl⟩ : syracuseStep 7452323 = 11178485) B11178485
theorem B2209463 : Blo 980594 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B12105577 : Blo 980594 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B2799497 : Blo 980594 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B2210651 : Blo 980594 2210651 := bstep (se 1 (by rfl) ⟨1657988, by rfl⟩ : syracuseStep 2210651 = 3315977) B3315977
theorem B2211407 : Blo 980594 2211407 := bstep (se 1 (by rfl) ⟨1658555, by rfl⟩ : syracuseStep 2211407 = 3317111) B3317111
theorem B1261351 : Blo 980594 1261351 := bstep (se 1 (by rfl) ⟨946013, by rfl⟩ : syracuseStep 1261351 = 1892027) B1892027
theorem B2801479 : Blo 980594 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B2015099 : Blo 980594 2015099 := bstep (se 1 (by rfl) ⟨1511324, by rfl⟩ : syracuseStep 2015099 = 3022649) B3022649
theorem B7454753 : Blo 980594 7454753 := bstep (se 2 (by rfl) ⟨2795532, by rfl⟩ : syracuseStep 7454753 = 5591065) B5591065
theorem B7979147 : Blo 980594 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B22724813 : Blo 980594 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B1491175 : Blo 980594 1491175 := bstep (se 1 (by rfl) ⟨1118381, by rfl⟩ : syracuseStep 1491175 = 2236763) B2236763
theorem B2212127 : Blo 980594 2212127 := bstep (se 1 (by rfl) ⟨1659095, by rfl⟩ : syracuseStep 2212127 = 3318191) B3318191
theorem B2834785 : Blo 980594 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B1655167 : Blo 980594 1655167 := bstep (se 1 (by rfl) ⟨1241375, by rfl⟩ : syracuseStep 1655167 = 2482751) B2482751
theorem B5980711 : Blo 980594 5980711 := bstep (se 1 (by rfl) ⟨4485533, by rfl⟩ : syracuseStep 5980711 = 8971067) B8971067
theorem B1655599 : Blo 980594 1655599 := bstep (se 1 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 1655599 = 2483399) B2483399
theorem B2212775 : Blo 980594 2212775 := bstep (se 1 (by rfl) ⟨1659581, by rfl⟩ : syracuseStep 2212775 = 3319163) B3319163
theorem B26887571 : Blo 980594 26887571 := bstep (se 1 (by rfl) ⟨20165678, by rfl⟩ : syracuseStep 26887571 = 40331357) B40331357
theorem B7980767 : Blo 980594 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B7096031 : Blo 980594 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B1656571 : Blo 980594 1656571 := bstep (se 1 (by rfl) ⟨1242428, by rfl⟩ : syracuseStep 1656571 = 2484857) B2484857
theorem B2213711 : Blo 980594 2213711 := bstep (se 1 (by rfl) ⟨1660283, by rfl⟩ : syracuseStep 2213711 = 3320567) B3320567
theorem B2213729 : Blo 980594 2213729 := bstep (se 2 (by rfl) ⟨830148, by rfl⟩ : syracuseStep 2213729 = 1660297) B1660297
theorem B1656713 : Blo 980594 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B3786761 : Blo 980594 3786761 := bstep (se 2 (by rfl) ⟨1420035, by rfl⟩ : syracuseStep 3786761 = 2840071) B2840071
theorem B1820969 : Blo 980594 1820969 := bstep (se 2 (by rfl) ⟨682863, by rfl⟩ : syracuseStep 1820969 = 1365727) B1365727
theorem B1657145 : Blo 980594 1657145 := bstep (se 2 (by rfl) ⟨621429, by rfl⟩ : syracuseStep 1657145 = 1242859) B1242859
theorem B2214305 : Blo 980594 2214305 := bstep (se 2 (by rfl) ⟨830364, by rfl⟩ : syracuseStep 2214305 = 1660729) B1660729
theorem B4966919 : Blo 980594 4966919 := bstep (se 1 (by rfl) ⟨3725189, by rfl⟩ : syracuseStep 4966919 = 7450379) B7450379
theorem B2214431 : Blo 980594 2214431 := bstep (se 1 (by rfl) ⟨1660823, by rfl⟩ : syracuseStep 2214431 = 3321647) B3321647
theorem B3361385 : Blo 980594 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B5032595 : Blo 980594 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B47893355 : Blo 980594 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B1657759 : Blo 980594 1657759 := bstep (se 1 (by rfl) ⟨1243319, by rfl⟩ : syracuseStep 1657759 = 2486639) B2486639
theorem B1658191 : Blo 980594 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B1658279 : Blo 980594 1658279 := bstep (se 1 (by rfl) ⟨1243709, by rfl⟩ : syracuseStep 1658279 = 2487419) B2487419
theorem B1658441 : Blo 980594 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B17256509 : Blo 980594 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B4968701 : Blo 980594 4968701 := bstep (se 3 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 4968701 = 1863263) B1863263
theorem B9457955 : Blo 980594 9457955 := bstep (se 1 (by rfl) ⟨7093466, by rfl⟩ : syracuseStep 9457955 = 14186933) B14186933
theorem B1495433 : Blo 980594 1495433 := bstep (se 2 (by rfl) ⟨560787, by rfl⟩ : syracuseStep 1495433 = 1121575) B1121575
theorem B54514133 : Blo 980594 54514133 := bstep (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) B1277675
theorem B1659487 : Blo 980594 1659487 := bstep (se 1 (by rfl) ⟨1244615, by rfl⟩ : syracuseStep 1659487 = 2489231) B2489231
theorem B1397351 : Blo 980594 1397351 := bstep (se 1 (by rfl) ⟨1048013, by rfl⟩ : syracuseStep 1397351 = 2096027) B2096027
theorem B1659899 : Blo 980594 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B4969511 : Blo 980594 4969511 := bstep (se 1 (by rfl) ⟨3727133, by rfl⟩ : syracuseStep 4969511 = 7454267) B7454267
theorem B8377577 : Blo 980594 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B4478327 : Blo 980594 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B1660331 : Blo 980594 1660331 := bstep (se 1 (by rfl) ⟨1245248, by rfl⟩ : syracuseStep 1660331 = 2490497) B2490497
theorem B1103611 : Blo 980594 1103611 := bstep (se 1 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 1103611 = 1655417) B1655417
theorem B1103647 : Blo 980594 1103647 := bstep (se 1 (by rfl) ⟨827735, by rfl⟩ : syracuseStep 1103647 = 1655471) B1655471
theorem B1660871 : Blo 980594 1660871 := bstep (se 1 (by rfl) ⟨1245653, by rfl⟩ : syracuseStep 1660871 = 2491307) B2491307
theorem B95475671 : Blo 980594 95475671 := bstep (se 1 (by rfl) ⟨71606753, by rfl⟩ : syracuseStep 95475671 = 143213507) B143213507
theorem B1661161 : Blo 980594 1661161 := bstep (se 2 (by rfl) ⟨622935, by rfl⟩ : syracuseStep 1661161 = 1245871) B1245871
theorem B8378639 : Blo 980594 8378639 := bstep (se 1 (by rfl) ⟨6283979, by rfl⟩ : syracuseStep 8378639 = 12567959) B12567959
theorem B5593981 : Blo 980594 5593981 := bstep (se 3 (by rfl) ⟨1048871, by rfl⟩ : syracuseStep 5593981 = 2097743) B2097743
theorem B163371919 : Blo 980594 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B1104799 : Blo 980594 1104799 := bstep (se 1 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 1104799 = 1657199) B1657199
theorem B1104943 : Blo 980594 1104943 := bstep (se 1 (by rfl) ⟨828707, by rfl⟩ : syracuseStep 1104943 = 1657415) B1657415
theorem B1105231 : Blo 980594 1105231 := bstep (se 1 (by rfl) ⟨828923, by rfl⟩ : syracuseStep 1105231 = 1657847) B1657847
theorem B5594507 : Blo 980594 5594507 := bstep (se 1 (by rfl) ⟨4195880, by rfl⟩ : syracuseStep 5594507 = 8391761) B8391761
theorem B6381359 : Blo 980594 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B1105735 : Blo 980594 1105735 := bstep (se 1 (by rfl) ⟨829301, by rfl⟩ : syracuseStep 1105735 = 1658603) B1658603
theorem B12607325 : Blo 980594 12607325 := bstep (se 3 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 12607325 = 4727747) B4727747
theorem B64642991 : Blo 980594 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B28336139 : Blo 980594 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B1106383 : Blo 980594 1106383 := bstep (se 1 (by rfl) ⟨829787, by rfl⟩ : syracuseStep 1106383 = 1659575) B1659575
theorem B5301611 : Blo 980594 5301611 := bstep (se 1 (by rfl) ⟨3976208, by rfl⟩ : syracuseStep 5301611 = 7952417) B7952417
theorem B1107355 : Blo 980594 1107355 := bstep (se 1 (by rfl) ⟨830516, by rfl⟩ : syracuseStep 1107355 = 1661033) B1661033
theorem B9430465 : Blo 980594 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B3729017 : Blo 980594 3729017 := bstep (se 2 (by rfl) ⟨1398381, by rfl⟩ : syracuseStep 3729017 = 2796763) B2796763
theorem B2484047 : Blo 980594 2484047 := bstep (se 1 (by rfl) ⟨1863035, by rfl⟩ : syracuseStep 2484047 = 3726071) B3726071
theorem B6711443 : Blo 980594 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B8383013 : Blo 980594 8383013 := bstep (se 4 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 8383013 = 1571815) B1571815
theorem B1862777 : Blo 980594 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B10612043 : Blo 980594 10612043 := bstep (se 1 (by rfl) ⟨7959032, by rfl⟩ : syracuseStep 10612043 = 15918065) B15918065
theorem B2485687 : Blo 980594 2485687 := bstep (se 1 (by rfl) ⟨1864265, by rfl⟩ : syracuseStep 2485687 = 3728531) B3728531
theorem B5598881 : Blo 980594 5598881 := bstep (se 2 (by rfl) ⟨2099580, by rfl⟩ : syracuseStep 5598881 = 4199161) B4199161
theorem B17919791 : Blo 980594 17919791 := bstep (se 1 (by rfl) ⟨13439843, by rfl⟩ : syracuseStep 17919791 = 26879687) B26879687
theorem B8384411 : Blo 980594 8384411 := bstep (se 1 (by rfl) ⟨6288308, by rfl⟩ : syracuseStep 8384411 = 12576617) B12576617
theorem B6287489 : Blo 980594 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B4976963 : Blo 980594 4976963 := bstep (se 1 (by rfl) ⟨3732722, by rfl⟩ : syracuseStep 4976963 = 7465445) B7465445
theorem B5599631 : Blo 980594 5599631 := bstep (se 1 (by rfl) ⟨4199723, by rfl⟩ : syracuseStep 5599631 = 8399447) B8399447
theorem B1470953 : Blo 980594 1470953 := bstep (se 2 (by rfl) ⟨551607, by rfl⟩ : syracuseStep 1470953 = 1103215) B1103215
theorem B1471079 : Blo 980594 1471079 := bstep (se 1 (by rfl) ⟨1103309, by rfl⟩ : syracuseStep 1471079 = 2206619) B2206619
theorem B3142259 : Blo 980594 3142259 := bstep (se 1 (by rfl) ⟨2356694, by rfl⟩ : syracuseStep 3142259 = 4713389) B4713389
theorem B1471211 : Blo 980594 1471211 := bstep (se 1 (by rfl) ⟨1103408, by rfl⟩ : syracuseStep 1471211 = 2206817) B2206817
theorem B1471241 : Blo 980594 1471241 := bstep (se 2 (by rfl) ⟨551715, by rfl⟩ : syracuseStep 1471241 = 1103431) B1103431
theorem B1471343 : Blo 980594 1471343 := bstep (se 1 (by rfl) ⟨1103507, by rfl⟩ : syracuseStep 1471343 = 2207015) B2207015
theorem B7173035 : Blo 980594 7173035 := bstep (se 1 (by rfl) ⟨5379776, by rfl⟩ : syracuseStep 7173035 = 10759553) B10759553
theorem B1471595 : Blo 980594 1471595 := bstep (se 1 (by rfl) ⟨1103696, by rfl⟩ : syracuseStep 1471595 = 2207393) B2207393
theorem B17036405 : Blo 980594 17036405 := bstep (se 5 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 17036405 = 1597163) B1597163
theorem B4191371 : Blo 980594 4191371 := bstep (se 1 (by rfl) ⟨3143528, by rfl⟩ : syracuseStep 4191371 = 6287057) B6287057
theorem B1471835 : Blo 980594 1471835 := bstep (se 1 (by rfl) ⟨1103876, by rfl⟩ : syracuseStep 1471835 = 2207753) B2207753
theorem B1472111 : Blo 980594 1472111 := bstep (se 1 (by rfl) ⟨1104083, by rfl⟩ : syracuseStep 1472111 = 2208167) B2208167
theorem B980647 : Blo 980594 980647 := bstep (se 1 (by rfl) ⟨735485, by rfl⟩ : syracuseStep 980647 = 1470971) B1470971
theorem B1472183 : Blo 980594 1472183 := bstep (se 1 (by rfl) ⟨1104137, by rfl⟩ : syracuseStep 1472183 = 2208275) B2208275
theorem B1472219 : Blo 980594 1472219 := bstep (se 1 (by rfl) ⟨1104164, by rfl⟩ : syracuseStep 1472219 = 2208329) B2208329
theorem B980731 : Blo 980594 980731 := bstep (se 1 (by rfl) ⟨735548, by rfl⟩ : syracuseStep 980731 = 1471097) B1471097
theorem B980767 : Blo 980594 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B980799 : Blo 980594 980799 := bstep (se 1 (by rfl) ⟨735599, by rfl⟩ : syracuseStep 980799 = 1471199) B1471199
theorem B1472393 : Blo 980594 1472393 := bstep (se 2 (by rfl) ⟨552147, by rfl⟩ : syracuseStep 1472393 = 1104295) B1104295
theorem B2488279 : Blo 980594 2488279 := bstep (se 1 (by rfl) ⟨1866209, by rfl⟩ : syracuseStep 2488279 = 3732419) B3732419
theorem B980975 : Blo 980594 980975 := bstep (se 1 (by rfl) ⟨735731, by rfl⟩ : syracuseStep 980975 = 1471463) B1471463
theorem B1472495 : Blo 980594 1472495 := bstep (se 1 (by rfl) ⟨1104371, by rfl⟩ : syracuseStep 1472495 = 2208743) B2208743
theorem B7075937 : Blo 980594 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B981147 : Blo 980594 981147 := bstep (se 1 (by rfl) ⟨735860, by rfl⟩ : syracuseStep 981147 = 1471721) B1471721
theorem B981183 : Blo 980594 981183 := bstep (se 1 (by rfl) ⟨735887, by rfl⟩ : syracuseStep 981183 = 1471775) B1471775
theorem B2488553 : Blo 980594 2488553 := bstep (se 2 (by rfl) ⟨933207, by rfl⟩ : syracuseStep 2488553 = 1866415) B1866415
theorem B1472747 : Blo 980594 1472747 := bstep (se 1 (by rfl) ⟨1104560, by rfl⟩ : syracuseStep 1472747 = 2209121) B2209121
theorem B2488583 : Blo 980594 2488583 := bstep (se 1 (by rfl) ⟨1866437, by rfl⟩ : syracuseStep 2488583 = 3732875) B3732875
theorem B1472807 : Blo 980594 1472807 := bstep (se 1 (by rfl) ⟨1104605, by rfl⟩ : syracuseStep 1472807 = 2209211) B2209211
theorem B981295 : Blo 980594 981295 := bstep (se 1 (by rfl) ⟨735971, by rfl⟩ : syracuseStep 981295 = 1471943) B1471943
theorem B1472891 : Blo 980594 1472891 := bstep (se 1 (by rfl) ⟨1104668, by rfl⟩ : syracuseStep 1472891 = 2209337) B2209337
theorem B981531 : Blo 980594 981531 := bstep (se 1 (by rfl) ⟨736148, by rfl⟩ : syracuseStep 981531 = 1472297) B1472297
theorem B981535 : Blo 980594 981535 := bstep (se 1 (by rfl) ⟨736151, by rfl⟩ : syracuseStep 981535 = 1472303) B1472303
theorem B1473161 : Blo 980594 1473161 := bstep (se 2 (by rfl) ⟨552435, by rfl⟩ : syracuseStep 1473161 = 1104871) B1104871
theorem B1866377 : Blo 980594 1866377 := bstep (se 2 (by rfl) ⟨699891, by rfl⟩ : syracuseStep 1866377 = 1399783) B1399783
theorem B1473335 : Blo 980594 1473335 := bstep (se 1 (by rfl) ⟨1105001, by rfl⟩ : syracuseStep 1473335 = 2210003) B2210003
theorem B981851 : Blo 980594 981851 := bstep (se 1 (by rfl) ⟨736388, by rfl⟩ : syracuseStep 981851 = 1472777) B1472777
theorem B1473371 : Blo 980594 1473371 := bstep (se 1 (by rfl) ⟨1105028, by rfl⟩ : syracuseStep 1473371 = 2210057) B2210057
theorem B981919 : Blo 980594 981919 := bstep (se 1 (by rfl) ⟨736439, by rfl⟩ : syracuseStep 981919 = 1472879) B1472879
theorem B1473515 : Blo 980594 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B982063 : Blo 980594 982063 := bstep (se 1 (by rfl) ⟨736547, by rfl⟩ : syracuseStep 982063 = 1473095) B1473095
theorem B982087 : Blo 980594 982087 := bstep (se 1 (by rfl) ⟨736565, by rfl⟩ : syracuseStep 982087 = 1473131) B1473131
theorem B6388865 : Blo 980594 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B1473719 : Blo 980594 1473719 := bstep (se 1 (by rfl) ⟨1105289, by rfl⟩ : syracuseStep 1473719 = 2210579) B2210579
theorem B982239 : Blo 980594 982239 := bstep (se 1 (by rfl) ⟨736679, by rfl⟩ : syracuseStep 982239 = 1473359) B1473359
theorem B1473959 : Blo 980594 1473959 := bstep (se 1 (by rfl) ⟨1105469, by rfl⟩ : syracuseStep 1473959 = 2210939) B2210939
theorem B8388035 : Blo 980594 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B982503 : Blo 980594 982503 := bstep (se 1 (by rfl) ⟨736877, by rfl⟩ : syracuseStep 982503 = 1473755) B1473755
theorem B1572347 : Blo 980594 1572347 := bstep (se 1 (by rfl) ⟨1179260, by rfl⟩ : syracuseStep 1572347 = 2358521) B2358521
theorem B1474043 : Blo 980594 1474043 := bstep (se 1 (by rfl) ⟨1105532, by rfl⟩ : syracuseStep 1474043 = 2211065) B2211065
theorem B982619 : Blo 980594 982619 := bstep (se 1 (by rfl) ⟨736964, by rfl⟩ : syracuseStep 982619 = 1473929) B1473929
theorem B1474139 : Blo 980594 1474139 := bstep (se 1 (by rfl) ⟨1105604, by rfl⟩ : syracuseStep 1474139 = 2211209) B2211209
theorem B1769135 : Blo 980594 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B1474223 : Blo 980594 1474223 := bstep (se 1 (by rfl) ⟨1105667, by rfl⟩ : syracuseStep 1474223 = 2211335) B2211335
theorem B5603003 : Blo 980594 5603003 := bstep (se 1 (by rfl) ⟨4202252, by rfl⟩ : syracuseStep 5603003 = 8404505) B8404505
theorem B1474343 : Blo 980594 1474343 := bstep (se 1 (by rfl) ⟨1105757, by rfl⟩ : syracuseStep 1474343 = 2211515) B2211515
theorem B982855 : Blo 980594 982855 := bstep (se 1 (by rfl) ⟨737141, by rfl⟩ : syracuseStep 982855 = 1474283) B1474283
theorem B1474427 : Blo 980594 1474427 := bstep (se 1 (by rfl) ⟨1105820, by rfl⟩ : syracuseStep 1474427 = 2211641) B2211641
theorem B1867691 : Blo 980594 1867691 := bstep (se 1 (by rfl) ⟨1400768, by rfl⟩ : syracuseStep 1867691 = 2801537) B2801537
theorem B983007 : Blo 980594 983007 := bstep (se 1 (by rfl) ⟨737255, by rfl⟩ : syracuseStep 983007 = 1474511) B1474511
theorem B1474751 : Blo 980594 1474751 := bstep (se 1 (by rfl) ⟨1106063, by rfl⟩ : syracuseStep 1474751 = 2212127) B2212127
theorem B983231 : Blo 980594 983231 := bstep (se 1 (by rfl) ⟨737423, by rfl⟩ : syracuseStep 983231 = 1474847) B1474847
theorem B983247 : Blo 980594 983247 := bstep (se 1 (by rfl) ⟨737435, by rfl⟩ : syracuseStep 983247 = 1474871) B1474871
theorem B983295 : Blo 980594 983295 := bstep (se 1 (by rfl) ⟨737471, by rfl⟩ : syracuseStep 983295 = 1474943) B1474943
theorem B983343 : Blo 980594 983343 := bstep (se 1 (by rfl) ⟨737507, by rfl⟩ : syracuseStep 983343 = 1475015) B1475015
theorem B4194803 : Blo 980594 4194803 := bstep (se 1 (by rfl) ⟨3146102, by rfl⟩ : syracuseStep 4194803 = 6292205) B6292205
theorem B983579 : Blo 980594 983579 := bstep (se 1 (by rfl) ⟨737684, by rfl⟩ : syracuseStep 983579 = 1475369) B1475369
theorem B983583 : Blo 980594 983583 := bstep (se 1 (by rfl) ⟨737687, by rfl⟩ : syracuseStep 983583 = 1475375) B1475375
theorem B1475177 : Blo 980594 1475177 := bstep (se 2 (by rfl) ⟨553191, by rfl⟩ : syracuseStep 1475177 = 1106383) B1106383
theorem B1475183 : Blo 980594 1475183 := bstep (se 1 (by rfl) ⟨1106387, by rfl⟩ : syracuseStep 1475183 = 2212775) B2212775
theorem B983663 : Blo 980594 983663 := bstep (se 1 (by rfl) ⟨737747, by rfl⟩ : syracuseStep 983663 = 1475495) B1475495
theorem B1180327 : Blo 980594 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B983719 : Blo 980594 983719 := bstep (se 1 (by rfl) ⟨737789, by rfl⟩ : syracuseStep 983719 = 1475579) B1475579
theorem B983759 : Blo 980594 983759 := bstep (se 1 (by rfl) ⟨737819, by rfl⟩ : syracuseStep 983759 = 1475639) B1475639
theorem B983839 : Blo 980594 983839 := bstep (se 1 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 983839 = 1475759) B1475759
theorem B17925047 : Blo 980594 17925047 := bstep (se 1 (by rfl) ⟨13443785, by rfl⟩ : syracuseStep 17925047 = 26887571) B26887571
theorem B984111 : Blo 980594 984111 := bstep (se 1 (by rfl) ⟨738083, by rfl⟩ : syracuseStep 984111 = 1476167) B1476167
theorem B4981823 : Blo 980594 4981823 := bstep (se 1 (by rfl) ⟨3736367, by rfl⟩ : syracuseStep 4981823 = 7472735) B7472735
theorem B984175 : Blo 980594 984175 := bstep (se 1 (by rfl) ⟨738131, by rfl⟩ : syracuseStep 984175 = 1476263) B1476263
theorem B2491499 : Blo 980594 2491499 := bstep (se 1 (by rfl) ⟨1868624, by rfl⟩ : syracuseStep 2491499 = 3737249) B3737249
theorem B984231 : Blo 980594 984231 := bstep (se 1 (by rfl) ⟨738173, by rfl⟩ : syracuseStep 984231 = 1476347) B1476347
theorem B984255 : Blo 980594 984255 := bstep (se 1 (by rfl) ⟨738191, by rfl⟩ : syracuseStep 984255 = 1476383) B1476383
theorem B3146975 : Blo 980594 3146975 := bstep (se 1 (by rfl) ⟨2360231, by rfl⟩ : syracuseStep 3146975 = 4720463) B4720463
theorem B1475807 : Blo 980594 1475807 := bstep (se 1 (by rfl) ⟨1106855, by rfl⟩ : syracuseStep 1475807 = 2213711) B2213711
theorem B984287 : Blo 980594 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B1475819 : Blo 980594 1475819 := bstep (se 1 (by rfl) ⟨1106864, by rfl⟩ : syracuseStep 1475819 = 2213729) B2213729
theorem B984367 : Blo 980594 984367 := bstep (se 1 (by rfl) ⟨738275, by rfl⟩ : syracuseStep 984367 = 1476551) B1476551
theorem B1213979 : Blo 980594 1213979 := bstep (se 1 (by rfl) ⟨910484, by rfl⟩ : syracuseStep 1213979 = 1820969) B1820969
theorem B1476203 : Blo 980594 1476203 := bstep (se 1 (by rfl) ⟨1107152, by rfl⟩ : syracuseStep 1476203 = 2214305) B2214305
theorem B3311279 : Blo 980594 3311279 := bstep (se 1 (by rfl) ⟨2483459, by rfl⟩ : syracuseStep 3311279 = 4966919) B4966919
theorem B1476287 : Blo 980594 1476287 := bstep (se 1 (by rfl) ⟨1107215, by rfl⟩ : syracuseStep 1476287 = 2214431) B2214431
theorem B3737279 : Blo 980594 3737279 := bstep (se 1 (by rfl) ⟨2802959, by rfl⟩ : syracuseStep 3737279 = 5605919) B5605919
theorem B1476473 : Blo 980594 1476473 := bstep (se 2 (by rfl) ⟨553677, by rfl⟩ : syracuseStep 1476473 = 1107355) B1107355
theorem B5376203 : Blo 980594 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B1771903 : Blo 980594 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B11504339 : Blo 980594 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B3312467 : Blo 980594 3312467 := bstep (se 1 (by rfl) ⟨2484350, by rfl⟩ : syracuseStep 3312467 = 4968701) B4968701
theorem B3541961 : Blo 980594 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B2362337 : Blo 980594 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B36342755 : Blo 980594 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B4983929 : Blo 980594 4983929 := bstep (se 2 (by rfl) ⟨1868973, by rfl⟩ : syracuseStep 4983929 = 3737947) B3737947
theorem B3313007 : Blo 980594 3313007 := bstep (se 1 (by rfl) ⟨2484755, by rfl⟩ : syracuseStep 3313007 = 4969511) B4969511
theorem B4197743 : Blo 980594 4197743 := bstep (se 1 (by rfl) ⟨3148307, by rfl⟩ : syracuseStep 4197743 = 6296615) B6296615
theorem B2985551 : Blo 980594 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B42470993 : Blo 980594 42470993 := bstep (se 2 (by rfl) ⟨15926622, by rfl⟩ : syracuseStep 42470993 = 31853245) B31853245
theorem B12587075 : Blo 980594 12587075 := bstep (se 1 (by rfl) ⟨9440306, by rfl⟩ : syracuseStep 12587075 = 18880613) B18880613
theorem B1577063 : Blo 980594 1577063 := bstep (se 1 (by rfl) ⟨1182797, by rfl⟩ : syracuseStep 1577063 = 2365595) B2365595
theorem B3314249 : Blo 980594 3314249 := bstep (se 2 (by rfl) ⟨1242843, by rfl⟩ : syracuseStep 3314249 = 2485687) B2485687
theorem B15308129 : Blo 980594 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B10098029 : Blo 980594 10098029 := bstep (se 3 (by rfl) ⟨1893380, by rfl⟩ : syracuseStep 10098029 = 3786761) B3786761
theorem B4200119 : Blo 980594 4200119 := bstep (se 1 (by rfl) ⟨3150089, by rfl⟩ : syracuseStep 4200119 = 6300179) B6300179
theorem B16783037 : Blo 980594 16783037 := bstep (se 3 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 16783037 = 6293639) B6293639
theorem B10098931 : Blo 980594 10098931 := bstep (se 1 (by rfl) ⟨7574198, by rfl⟩ : syracuseStep 10098931 = 15148397) B15148397
theorem B102112001 : Blo 980594 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B45358379 : Blo 980594 45358379 := bstep (se 1 (by rfl) ⟨34018784, by rfl⟩ : syracuseStep 45358379 = 68037569) B68037569
theorem B3317705 : Blo 980594 3317705 := bstep (se 2 (by rfl) ⟨1244139, by rfl⟩ : syracuseStep 3317705 = 2488279) B2488279
theorem B7086113 : Blo 980594 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B3154049 : Blo 980594 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B3317975 : Blo 980594 3317975 := bstep (se 1 (by rfl) ⟨2488481, by rfl⟩ : syracuseStep 3317975 = 4976963) B4976963
theorem B2794247 : Blo 980594 2794247 := bstep (se 1 (by rfl) ⟨2095685, by rfl⟩ : syracuseStep 2794247 = 4191371) B4191371
theorem B6727205 : Blo 980594 6727205 := bstep (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) B1261351
theorem B64563077 : Blo 980594 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B3778973 : Blo 980594 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B110537393 : Blo 980594 110537393 := bstep (se 2 (by rfl) ⟨41451522, by rfl⟩ : syracuseStep 110537393 = 82903045) B82903045
theorem B5319431 : Blo 980594 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B3320783 : Blo 980594 3320783 := bstep (se 1 (by rfl) ⟨2490587, by rfl⟩ : syracuseStep 3320783 = 4981175) B4981175
theorem B3779713 : Blo 980594 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B2206889 : Blo 980594 2206889 := bstep (se 2 (by rfl) ⟨827583, by rfl⟩ : syracuseStep 2206889 = 1655167) B1655167
theorem B60599501 : Blo 980594 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B3321107 : Blo 980594 3321107 := bstep (se 1 (by rfl) ⟨2490830, by rfl⟩ : syracuseStep 3321107 = 4981661) B4981661
theorem B7974281 : Blo 980594 7974281 := bstep (se 2 (by rfl) ⟨2990355, by rfl⟩ : syracuseStep 7974281 = 5980711) B5980711
theorem B2207303 : Blo 980594 2207303 := bstep (se 1 (by rfl) ⟨1655477, by rfl⟩ : syracuseStep 2207303 = 3310955) B3310955
theorem B8400509 : Blo 980594 8400509 := bstep (se 3 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 8400509 = 3150191) B3150191
theorem B2207375 : Blo 980594 2207375 := bstep (se 1 (by rfl) ⟨1655531, by rfl⟩ : syracuseStep 2207375 = 3311063) B3311063
theorem B2207465 : Blo 980594 2207465 := bstep (se 2 (by rfl) ⟨827799, by rfl⟩ : syracuseStep 2207465 = 1655599) B1655599
theorem B2207483 : Blo 980594 2207483 := bstep (se 1 (by rfl) ⟨1655612, by rfl⟩ : syracuseStep 2207483 = 3311225) B3311225
theorem B5320511 : Blo 980594 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B4730687 : Blo 980594 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B3355063 : Blo 980594 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B3322295 : Blo 980594 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B31928903 : Blo 980594 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B2208491 : Blo 980594 2208491 := bstep (se 1 (by rfl) ⟨1656368, by rfl⟩ : syracuseStep 2208491 = 3312737) B3312737
theorem B3322835 : Blo 980594 3322835 := bstep (se 1 (by rfl) ⟨2492126, by rfl⟩ : syracuseStep 3322835 = 4984253) B4984253
theorem B2208761 : Blo 980594 2208761 := bstep (se 2 (by rfl) ⟨828285, by rfl⟩ : syracuseStep 2208761 = 1656571) B1656571
theorem B2208851 : Blo 980594 2208851 := bstep (se 1 (by rfl) ⟨1656638, by rfl⟩ : syracuseStep 2208851 = 3313277) B3313277
theorem B2209031 : Blo 980594 2209031 := bstep (se 1 (by rfl) ⟨1656773, by rfl⟩ : syracuseStep 2209031 = 3313547) B3313547
theorem B6305303 : Blo 980594 6305303 := bstep (se 1 (by rfl) ⟨4728977, by rfl⟩ : syracuseStep 6305303 = 9457955) B9457955
theorem B996955 : Blo 980594 996955 := bstep (se 1 (by rfl) ⟨747716, by rfl⟩ : syracuseStep 996955 = 1495433) B1495433
theorem B12760685 : Blo 980594 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B2209391 : Blo 980594 2209391 := bstep (se 1 (by rfl) ⟨1657043, by rfl⟩ : syracuseStep 2209391 = 3314087) B3314087
theorem B5585051 : Blo 980594 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B2210255 : Blo 980594 2210255 := bstep (se 1 (by rfl) ⟨1657691, by rfl⟩ : syracuseStep 2210255 = 3315383) B3315383
theorem B2210345 : Blo 980594 2210345 := bstep (se 2 (by rfl) ⟨828879, by rfl⟩ : syracuseStep 2210345 = 1657759) B1657759
theorem B63650447 : Blo 980594 63650447 := bstep (se 1 (by rfl) ⟨47737835, by rfl⟩ : syracuseStep 63650447 = 95475671) B95475671
theorem B2800271 : Blo 980594 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B5585759 : Blo 980594 5585759 := bstep (se 1 (by rfl) ⟨4189319, by rfl⟩ : syracuseStep 5585759 = 8378639) B8378639
theorem B2210921 : Blo 980594 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B2211047 : Blo 980594 2211047 := bstep (se 1 (by rfl) ⟨1658285, by rfl⟩ : syracuseStep 2211047 = 3316571) B3316571
theorem B2211551 : Blo 980594 2211551 := bstep (se 1 (by rfl) ⟨1658663, by rfl⟩ : syracuseStep 2211551 = 3317327) B3317327
theorem B2211623 : Blo 980594 2211623 := bstep (se 1 (by rfl) ⟨1658717, by rfl⟩ : syracuseStep 2211623 = 3317435) B3317435
theorem B8404883 : Blo 980594 8404883 := bstep (se 1 (by rfl) ⟨6303662, by rfl⟩ : syracuseStep 8404883 = 12607325) B12607325
theorem B18890759 : Blo 980594 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B7455239 : Blo 980594 7455239 := bstep (se 1 (by rfl) ⟨5591429, by rfl⟩ : syracuseStep 7455239 = 11182859) B11182859
theorem B9454265 : Blo 980594 9454265 := bstep (se 2 (by rfl) ⟨3545349, by rfl⟩ : syracuseStep 9454265 = 7090699) B7090699
theorem B7979795 : Blo 980594 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B2212649 : Blo 980594 2212649 := bstep (se 2 (by rfl) ⟨829743, by rfl⟩ : syracuseStep 2212649 = 1659487) B1659487
theorem B3589175 : Blo 980594 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B2212919 : Blo 980594 2212919 := bstep (se 1 (by rfl) ⟨1659689, by rfl⟩ : syracuseStep 2212919 = 3319379) B3319379
theorem B1656031 : Blo 980594 1656031 := bstep (se 1 (by rfl) ⟨1242023, by rfl⟩ : syracuseStep 1656031 = 2484047) B2484047
theorem B2213099 : Blo 980594 2213099 := bstep (se 1 (by rfl) ⟨1659824, by rfl⟩ : syracuseStep 2213099 = 3319649) B3319649
theorem B4474295 : Blo 980594 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B4965947 : Blo 980594 4965947 := bstep (se 1 (by rfl) ⟨3724460, by rfl⟩ : syracuseStep 4965947 = 7448921) B7448921
theorem B8963693 : Blo 980594 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B2213567 : Blo 980594 2213567 := bstep (se 1 (by rfl) ⟨1660175, by rfl⟩ : syracuseStep 2213567 = 3320351) B3320351
theorem B5588675 : Blo 980594 5588675 := bstep (se 1 (by rfl) ⟨4191506, by rfl⟩ : syracuseStep 5588675 = 8383013) B8383013
theorem B11946527 : Blo 980594 11946527 := bstep (se 1 (by rfl) ⟨8959895, by rfl⟩ : syracuseStep 11946527 = 17919791) B17919791
theorem B5589607 : Blo 980594 5589607 := bstep (se 1 (by rfl) ⟨4192205, by rfl⟩ : syracuseStep 5589607 = 8384411) B8384411
theorem B2214503 : Blo 980594 2214503 := bstep (se 1 (by rfl) ⟨1660877, by rfl⟩ : syracuseStep 2214503 = 3321755) B3321755
theorem B2214881 : Blo 980594 2214881 := bstep (se 2 (by rfl) ⟨830580, by rfl⟩ : syracuseStep 2214881 = 1661161) B1661161
theorem B4967405 : Blo 980594 4967405 := bstep (se 3 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 4967405 = 1862777) B1862777
theorem B4967567 : Blo 980594 4967567 := bstep (se 1 (by rfl) ⟨3725675, by rfl⟩ : syracuseStep 4967567 = 7451351) B7451351
theorem B2215259 : Blo 980594 2215259 := bstep (se 1 (by rfl) ⟨1661444, by rfl⟩ : syracuseStep 2215259 = 3322889) B3322889
theorem B2215295 : Blo 980594 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B11357603 : Blo 980594 11357603 := bstep (se 1 (by rfl) ⟨8518202, by rfl⟩ : syracuseStep 11357603 = 17036405) B17036405
theorem B4968215 : Blo 980594 4968215 := bstep (se 1 (by rfl) ⟨3726161, by rfl⟩ : syracuseStep 4968215 = 7452323) B7452323
theorem B7458641 : Blo 980594 7458641 := bstep (se 2 (by rfl) ⟨2796990, by rfl⟩ : syracuseStep 7458641 = 5593981) B5593981
theorem B217829225 : Blo 980594 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B1659035 : Blo 980594 1659035 := bstep (se 1 (by rfl) ⟨1244276, by rfl⟩ : syracuseStep 1659035 = 2488553) B2488553
theorem B1659055 : Blo 980594 1659055 := bstep (se 1 (by rfl) ⟨1244291, by rfl⟩ : syracuseStep 1659055 = 2488583) B2488583
theorem B689525237 : Blo 980594 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B5592023 : Blo 980594 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B4969835 : Blo 980594 4969835 := bstep (se 1 (by rfl) ⟨3727376, by rfl⟩ : syracuseStep 4969835 = 7454753) B7454753
theorem B1988233 : Blo 980594 1988233 := bstep (se 2 (by rfl) ⟨745587, by rfl⟩ : syracuseStep 1988233 = 1491175) B1491175
theorem B1660763 : Blo 980594 1660763 := bstep (se 1 (by rfl) ⟨1245572, by rfl⟩ : syracuseStep 1660763 = 2491145) B2491145
theorem B1661215 : Blo 980594 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B1104475 : Blo 980594 1104475 := bstep (se 1 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 1104475 = 1656713) B1656713
theorem B5593799 : Blo 980594 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B1104763 : Blo 980594 1104763 := bstep (se 1 (by rfl) ⟨828572, by rfl⟩ : syracuseStep 1104763 = 1657145) B1657145
theorem B1399675 : Blo 980594 1399675 := bstep (se 1 (by rfl) ⟨1049756, by rfl⟩ : syracuseStep 1399675 = 2099513) B2099513
theorem B8969093 : Blo 980594 8969093 := bstep (se 4 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 8969093 = 1681705) B1681705
theorem B3726269 : Blo 980594 3726269 := bstep (se 3 (by rfl) ⟨698675, by rfl⟩ : syracuseStep 3726269 = 1397351) B1397351
theorem B12573953 : Blo 980594 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B13458797 : Blo 980594 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B1105519 : Blo 980594 1105519 := bstep (se 1 (by rfl) ⟨829139, by rfl⟩ : syracuseStep 1105519 = 1658279) B1658279
theorem B1105627 : Blo 980594 1105627 := bstep (se 1 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 1105627 = 1658441) B1658441
theorem B3727073 : Blo 980594 3727073 := bstep (se 2 (by rfl) ⟨1397652, by rfl⟩ : syracuseStep 3727073 = 2795305) B2795305
theorem B1106599 : Blo 980594 1106599 := bstep (se 1 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 1106599 = 1659899) B1659899
theorem B1106887 : Blo 980594 1106887 := bstep (se 1 (by rfl) ⟨830165, by rfl⟩ : syracuseStep 1106887 = 1660331) B1660331
theorem B1107247 : Blo 980594 1107247 := bstep (se 1 (by rfl) ⟨830435, by rfl⟩ : syracuseStep 1107247 = 1660871) B1660871
theorem B31909301 : Blo 980594 31909301 := bstep (se 5 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 31909301 = 2991497) B2991497
theorem B38823623 : Blo 980594 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B1861775 : Blo 980594 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B3729671 : Blo 980594 3729671 := bstep (se 1 (by rfl) ⟨2797253, by rfl⟩ : syracuseStep 3729671 = 5594507) B5594507
theorem B4254239 : Blo 980594 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B2517551 : Blo 980594 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B1010279 : Blo 980594 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B16804907 : Blo 980594 16804907 := bstep (se 1 (by rfl) ⟨12603680, by rfl⟩ : syracuseStep 16804907 = 25207361) B25207361
theorem B7957673 : Blo 980594 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B3534407 : Blo 980594 3534407 := bstep (se 1 (by rfl) ⟨2650805, by rfl⟩ : syracuseStep 3534407 = 5301611) B5301611
theorem B2486011 : Blo 980594 2486011 := bstep (se 1 (by rfl) ⟨1864508, by rfl⟩ : syracuseStep 2486011 = 3729017) B3729017
theorem B1995499 : Blo 980594 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B1471295 : Blo 980594 1471295 := bstep (se 1 (by rfl) ⟨1103471, by rfl⟩ : syracuseStep 1471295 = 2206943) B2206943
theorem B7074695 : Blo 980594 7074695 := bstep (se 1 (by rfl) ⟨5306021, by rfl⟩ : syracuseStep 7074695 = 10612043) B10612043
theorem B1864615 : Blo 980594 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B1471439 : Blo 980594 1471439 := bstep (se 1 (by rfl) ⟨1103579, by rfl⟩ : syracuseStep 1471439 = 2207159) B2207159
theorem B1471481 : Blo 980594 1471481 := bstep (se 2 (by rfl) ⟨551805, by rfl⟩ : syracuseStep 1471481 = 1103611) B1103611
theorem B1471529 : Blo 980594 1471529 := bstep (se 2 (by rfl) ⟨551823, by rfl⟩ : syracuseStep 1471529 = 1103647) B1103647
theorem B1471559 : Blo 980594 1471559 := bstep (se 1 (by rfl) ⟨1103669, by rfl⟩ : syracuseStep 1471559 = 2207339) B2207339
theorem B1864775 : Blo 980594 1864775 := bstep (se 1 (by rfl) ⟨1398581, by rfl⟩ : syracuseStep 1864775 = 2797163) B2797163
theorem B3732587 : Blo 980594 3732587 := bstep (se 1 (by rfl) ⟨2799440, by rfl⟩ : syracuseStep 3732587 = 5598881) B5598881
theorem B1471739 : Blo 980594 1471739 := bstep (se 1 (by rfl) ⟨1103804, by rfl⟩ : syracuseStep 1471739 = 2207609) B2207609
theorem B23950657 : Blo 980594 23950657 := bstep (se 2 (by rfl) ⟨8981496, by rfl⟩ : syracuseStep 23950657 = 17962993) B17962993
theorem B4191659 : Blo 980594 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B3733087 : Blo 980594 3733087 := bstep (se 1 (by rfl) ⟨2799815, by rfl⟩ : syracuseStep 3733087 = 5599631) B5599631
theorem B1865359 : Blo 980594 1865359 := bstep (se 1 (by rfl) ⟨1399019, by rfl⟩ : syracuseStep 1865359 = 2798039) B2798039
theorem B980635 : Blo 980594 980635 := bstep (se 1 (by rfl) ⟨735476, by rfl⟩ : syracuseStep 980635 = 1470953) B1470953
theorem B980719 : Blo 980594 980719 := bstep (se 1 (by rfl) ⟨735539, by rfl⟩ : syracuseStep 980719 = 1471079) B1471079
theorem B2094839 : Blo 980594 2094839 := bstep (se 1 (by rfl) ⟨1571129, by rfl⟩ : syracuseStep 2094839 = 3142259) B3142259
theorem B980807 : Blo 980594 980807 := bstep (se 1 (by rfl) ⟨735605, by rfl⟩ : syracuseStep 980807 = 1471211) B1471211
theorem B980827 : Blo 980594 980827 := bstep (se 1 (by rfl) ⟨735620, by rfl⟩ : syracuseStep 980827 = 1471241) B1471241
theorem B980895 : Blo 980594 980895 := bstep (se 1 (by rfl) ⟨735671, by rfl⟩ : syracuseStep 980895 = 1471343) B1471343
theorem B4782023 : Blo 980594 4782023 := bstep (se 1 (by rfl) ⟨3586517, by rfl⟩ : syracuseStep 4782023 = 7173035) B7173035
theorem B60520441 : Blo 980594 60520441 := bstep (se 2 (by rfl) ⟨22695165, by rfl⟩ : syracuseStep 60520441 = 45390331) B45390331
theorem B981063 : Blo 980594 981063 := bstep (se 1 (by rfl) ⟨735797, by rfl⟩ : syracuseStep 981063 = 1471595) B1471595
theorem B981223 : Blo 980594 981223 := bstep (se 1 (by rfl) ⟨735917, by rfl⟩ : syracuseStep 981223 = 1471835) B1471835
theorem B981407 : Blo 980594 981407 := bstep (se 1 (by rfl) ⟨736055, by rfl⟩ : syracuseStep 981407 = 1472111) B1472111
theorem B981455 : Blo 980594 981455 := bstep (se 1 (by rfl) ⟨736091, by rfl⟩ : syracuseStep 981455 = 1472183) B1472183
theorem B1472975 : Blo 980594 1472975 := bstep (se 1 (by rfl) ⟨1104731, by rfl⟩ : syracuseStep 1472975 = 2209463) B2209463
theorem B981479 : Blo 980594 981479 := bstep (se 1 (by rfl) ⟨736109, by rfl⟩ : syracuseStep 981479 = 1472219) B1472219
theorem B1473065 : Blo 980594 1473065 := bstep (se 2 (by rfl) ⟨552399, by rfl⟩ : syracuseStep 1473065 = 1104799) B1104799
theorem B981595 : Blo 980594 981595 := bstep (se 1 (by rfl) ⟨736196, by rfl⟩ : syracuseStep 981595 = 1472393) B1472393
theorem B1866331 : Blo 980594 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B981663 : Blo 980594 981663 := bstep (se 1 (by rfl) ⟨736247, by rfl⟩ : syracuseStep 981663 = 1472495) B1472495
theorem B1473257 : Blo 980594 1473257 := bstep (se 2 (by rfl) ⟨552471, by rfl⟩ : syracuseStep 1473257 = 1104943) B1104943
theorem B4717291 : Blo 980594 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B981831 : Blo 980594 981831 := bstep (se 1 (by rfl) ⟨736373, by rfl⟩ : syracuseStep 981831 = 1472747) B1472747
theorem B981871 : Blo 980594 981871 := bstep (se 1 (by rfl) ⟨736403, by rfl⟩ : syracuseStep 981871 = 1472807) B1472807
theorem B981927 : Blo 980594 981927 := bstep (se 1 (by rfl) ⟨736445, by rfl⟩ : syracuseStep 981927 = 1472891) B1472891
theorem B982107 : Blo 980594 982107 := bstep (se 1 (by rfl) ⟨736580, by rfl⟩ : syracuseStep 982107 = 1473161) B1473161
theorem B1244251 : Blo 980594 1244251 := bstep (se 1 (by rfl) ⟨933188, by rfl⟩ : syracuseStep 1244251 = 1866377) B1866377
theorem B1473641 : Blo 980594 1473641 := bstep (se 2 (by rfl) ⟨552615, by rfl⟩ : syracuseStep 1473641 = 1105231) B1105231
theorem B4717693 : Blo 980594 4717693 := bstep (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) B1769135
theorem B982223 : Blo 980594 982223 := bstep (se 1 (by rfl) ⟨736667, by rfl⟩ : syracuseStep 982223 = 1473335) B1473335
theorem B982247 : Blo 980594 982247 := bstep (se 1 (by rfl) ⟨736685, by rfl⟩ : syracuseStep 982247 = 1473371) B1473371
theorem B1473767 : Blo 980594 1473767 := bstep (se 1 (by rfl) ⟨1105325, by rfl⟩ : syracuseStep 1473767 = 2210651) B2210651
theorem B982343 : Blo 980594 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B4259243 : Blo 980594 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B982479 : Blo 980594 982479 := bstep (se 1 (by rfl) ⟨736859, by rfl⟩ : syracuseStep 982479 = 1473719) B1473719
theorem B982639 : Blo 980594 982639 := bstep (se 1 (by rfl) ⟨736979, by rfl⟩ : syracuseStep 982639 = 1473959) B1473959
theorem B1048231 : Blo 980594 1048231 := bstep (se 1 (by rfl) ⟨786173, by rfl⟩ : syracuseStep 1048231 = 1572347) B1572347
theorem B982695 : Blo 980594 982695 := bstep (se 1 (by rfl) ⟨737021, by rfl⟩ : syracuseStep 982695 = 1474043) B1474043
theorem B1474271 : Blo 980594 1474271 := bstep (se 1 (by rfl) ⟨1105703, by rfl⟩ : syracuseStep 1474271 = 2211407) B2211407
theorem B982759 : Blo 980594 982759 := bstep (se 1 (by rfl) ⟨737069, by rfl⟩ : syracuseStep 982759 = 1474139) B1474139
theorem B1474313 : Blo 980594 1474313 := bstep (se 2 (by rfl) ⟨552867, by rfl⟩ : syracuseStep 1474313 = 1105735) B1105735
theorem B3735305 : Blo 980594 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B982815 : Blo 980594 982815 := bstep (se 1 (by rfl) ⟨737111, by rfl⟩ : syracuseStep 982815 = 1474223) B1474223
theorem B3735335 : Blo 980594 3735335 := bstep (se 1 (by rfl) ⟨2801501, by rfl⟩ : syracuseStep 3735335 = 5603003) B5603003
theorem B982895 : Blo 980594 982895 := bstep (se 1 (by rfl) ⟨737171, by rfl⟩ : syracuseStep 982895 = 1474343) B1474343
theorem B1343399 : Blo 980594 1343399 := bstep (se 1 (by rfl) ⟨1007549, by rfl⟩ : syracuseStep 1343399 = 2015099) B2015099
theorem B982951 : Blo 980594 982951 := bstep (se 1 (by rfl) ⟨737213, by rfl⟩ : syracuseStep 982951 = 1474427) B1474427
theorem B1245127 : Blo 980594 1245127 := bstep (se 1 (by rfl) ⟨933845, by rfl⟩ : syracuseStep 1245127 = 1867691) B1867691
theorem B983167 : Blo 980594 983167 := bstep (se 1 (by rfl) ⟨737375, by rfl⟩ : syracuseStep 983167 = 1474751) B1474751
theorem B983451 : Blo 980594 983451 := bstep (se 1 (by rfl) ⟨737588, by rfl⟩ : syracuseStep 983451 = 1475177) B1475177
theorem B983455 : Blo 980594 983455 := bstep (se 1 (by rfl) ⟨737591, by rfl⟩ : syracuseStep 983455 = 1475183) B1475183
theorem B1475099 : Blo 980594 1475099 := bstep (se 1 (by rfl) ⟨1106324, by rfl⟩ : syracuseStep 1475099 = 2212649) B2212649
theorem B2392783 : Blo 980594 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B1475279 : Blo 980594 1475279 := bstep (se 1 (by rfl) ⟨1106459, by rfl⟩ : syracuseStep 1475279 = 2212919) B2212919
theorem B2097983 : Blo 980594 2097983 := bstep (se 1 (by rfl) ⟨1573487, by rfl⟩ : syracuseStep 2097983 = 3146975) B3146975
theorem B983871 : Blo 980594 983871 := bstep (se 1 (by rfl) ⟨737903, by rfl⟩ : syracuseStep 983871 = 1475807) B1475807
theorem B1475399 : Blo 980594 1475399 := bstep (se 1 (by rfl) ⟨1106549, by rfl⟩ : syracuseStep 1475399 = 2213099) B2213099
theorem B983879 : Blo 980594 983879 := bstep (se 1 (by rfl) ⟨737909, by rfl⟩ : syracuseStep 983879 = 1475819) B1475819
theorem B1573769 : Blo 980594 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B1475465 : Blo 980594 1475465 := bstep (se 2 (by rfl) ⟨553299, by rfl⟩ : syracuseStep 1475465 = 1106599) B1106599
theorem B2982863 : Blo 980594 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B3310631 : Blo 980594 3310631 := bstep (se 1 (by rfl) ⟨2482973, by rfl⟩ : syracuseStep 3310631 = 4965947) B4965947
theorem B984135 : Blo 980594 984135 := bstep (se 1 (by rfl) ⟨738101, by rfl⟩ : syracuseStep 984135 = 1476203) B1476203
theorem B1475711 : Blo 980594 1475711 := bstep (se 1 (by rfl) ⟨1106783, by rfl⟩ : syracuseStep 1475711 = 2213567) B2213567
theorem B984191 : Blo 980594 984191 := bstep (se 1 (by rfl) ⟨738143, by rfl⟩ : syracuseStep 984191 = 1476287) B1476287
theorem B2491519 : Blo 980594 2491519 := bstep (se 1 (by rfl) ⟨1868639, by rfl⟩ : syracuseStep 2491519 = 3737279) B3737279
theorem B984315 : Blo 980594 984315 := bstep (se 1 (by rfl) ⟨738236, by rfl⟩ : syracuseStep 984315 = 1476473) B1476473
theorem B1475849 : Blo 980594 1475849 := bstep (se 2 (by rfl) ⟨553443, by rfl⟩ : syracuseStep 1475849 = 1106887) B1106887
theorem B7964351 : Blo 980594 7964351 := bstep (se 1 (by rfl) ⟨5973263, by rfl⟩ : syracuseStep 7964351 = 11946527) B11946527
theorem B1476329 : Blo 980594 1476329 := bstep (se 2 (by rfl) ⟨553623, by rfl⟩ : syracuseStep 1476329 = 1107247) B1107247
theorem B1476335 : Blo 980594 1476335 := bstep (se 1 (by rfl) ⟨1107251, by rfl⟩ : syracuseStep 1476335 = 2214503) B2214503
theorem B7669559 : Blo 980594 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B2361307 : Blo 980594 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B1574891 : Blo 980594 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1476587 : Blo 980594 1476587 := bstep (se 1 (by rfl) ⟨1107440, by rfl⟩ : syracuseStep 1476587 = 2214881) B2214881
theorem B3311603 : Blo 980594 3311603 := bstep (se 1 (by rfl) ⟨2483702, by rfl⟩ : syracuseStep 3311603 = 4967405) B4967405
theorem B3311711 : Blo 980594 3311711 := bstep (se 1 (by rfl) ⟨2483783, by rfl⟩ : syracuseStep 3311711 = 4967567) B4967567
theorem B1476839 : Blo 980594 1476839 := bstep (se 1 (by rfl) ⟨1107629, by rfl⟩ : syracuseStep 1476839 = 2215259) B2215259
theorem B1476863 : Blo 980594 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B7571735 : Blo 980594 7571735 := bstep (se 1 (by rfl) ⟨5678801, by rfl⟩ : syracuseStep 7571735 = 11357603) B11357603
theorem B17893669 : Blo 980594 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B28313995 : Blo 980594 28313995 := bstep (se 1 (by rfl) ⟨21235496, by rfl⟩ : syracuseStep 28313995 = 42470993) B42470993
theorem B3312143 : Blo 980594 3312143 := bstep (se 1 (by rfl) ⟨2484107, by rfl⟩ : syracuseStep 3312143 = 4968215) B4968215
theorem B8391383 : Blo 980594 8391383 := bstep (se 1 (by rfl) ⟨6293537, by rfl⟩ : syracuseStep 8391383 = 12587075) B12587075
theorem B1051375 : Blo 980594 1051375 := bstep (se 1 (by rfl) ⟨788531, by rfl⟩ : syracuseStep 1051375 = 1577063) B1577063
theorem B2362537 : Blo 980594 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B3313223 : Blo 980594 3313223 := bstep (se 1 (by rfl) ⟨2484917, by rfl⟩ : syracuseStep 3313223 = 4969835) B4969835
theorem B3314681 : Blo 980594 3314681 := bstep (se 2 (by rfl) ⟨1243005, by rfl⟩ : syracuseStep 3314681 = 2486011) B2486011
theorem B4724075 : Blo 980594 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B2102699 : Blo 980594 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B12949109 : Blo 980594 12949109 := bstep (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) B1213979
theorem B20158469 : Blo 980594 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B21272867 : Blo 980594 21272867 := bstep (se 1 (by rfl) ⟨15954650, by rfl⟩ : syracuseStep 21272867 = 31909301) B31909301
theorem B11344637 : Blo 980594 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2694077 : Blo 980594 2694077 := bstep (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) B1010279
theorem B1678367 : Blo 980594 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B3546287 : Blo 980594 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B5316187 : Blo 980594 5316187 := bstep (se 1 (by rfl) ⟨3987140, by rfl⟩ : syracuseStep 5316187 = 7974281) B7974281
theorem B3547007 : Blo 980594 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B3153791 : Blo 980594 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B5317093 : Blo 980594 5317093 := bstep (se 4 (by rfl) ⟨498477, by rfl⟩ : syracuseStep 5317093 = 996955) B996955
theorem B2794439 : Blo 980594 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B4203535 : Blo 980594 4203535 := bstep (se 1 (by rfl) ⟨3152651, by rfl⟩ : syracuseStep 4203535 = 6305303) B6305303
theorem B3188015 : Blo 980594 3188015 := bstep (se 1 (by rfl) ⟨2391011, by rfl⟩ : syracuseStep 3188015 = 4782023) B4782023
theorem B3582397 : Blo 980594 3582397 := bstep (se 3 (by rfl) ⟨671699, by rfl⟩ : syracuseStep 3582397 = 1343399) B1343399
theorem B12593839 : Blo 980594 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B2796535 : Blo 980594 2796535 := bstep (se 1 (by rfl) ⟨2097401, by rfl⟩ : syracuseStep 2796535 = 4194803) B4194803
theorem B6302843 : Blo 980594 6302843 := bstep (se 1 (by rfl) ⟨4727132, by rfl⟩ : syracuseStep 6302843 = 9454265) B9454265
theorem B5319863 : Blo 980594 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B3321215 : Blo 980594 3321215 := bstep (se 1 (by rfl) ⟨2490911, by rfl⟩ : syracuseStep 3321215 = 4981823) B4981823
theorem B5975795 : Blo 980594 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B2207519 : Blo 980594 2207519 := bstep (se 1 (by rfl) ⟨1655639, by rfl⟩ : syracuseStep 2207519 = 3311279) B3311279
theorem B3584135 : Blo 980594 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B2208041 : Blo 980594 2208041 := bstep (se 2 (by rfl) ⟨828015, by rfl⟩ : syracuseStep 2208041 = 1656031) B1656031
theorem B2208311 : Blo 980594 2208311 := bstep (se 1 (by rfl) ⟨1656233, by rfl⟩ : syracuseStep 2208311 = 3312467) B3312467
theorem B24228503 : Blo 980594 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B3322619 : Blo 980594 3322619 := bstep (se 1 (by rfl) ⟨2491964, by rfl⟩ : syracuseStep 3322619 = 4983929) B4983929
theorem B2208671 : Blo 980594 2208671 := bstep (se 1 (by rfl) ⟨1656503, by rfl⟩ : syracuseStep 2208671 = 3313007) B3313007
theorem B2798495 : Blo 980594 2798495 := bstep (se 1 (by rfl) ⟨2098871, by rfl⟩ : syracuseStep 2798495 = 4197743) B4197743
theorem B2209499 : Blo 980594 2209499 := bstep (se 1 (by rfl) ⟨1657124, by rfl⟩ : syracuseStep 2209499 = 3314249) B3314249
theorem B7452809 : Blo 980594 7452809 := bstep (se 2 (by rfl) ⟨2794803, by rfl⟩ : syracuseStep 7452809 = 5589607) B5589607
theorem B6732019 : Blo 980594 6732019 := bstep (se 1 (by rfl) ⟨5049014, by rfl⟩ : syracuseStep 6732019 = 10098029) B10098029
theorem B2800079 : Blo 980594 2800079 := bstep (se 1 (by rfl) ⟨2100059, by rfl⟩ : syracuseStep 2800079 = 4200119) B4200119
theorem B11188691 : Blo 980594 11188691 := bstep (se 1 (by rfl) ⟨8391518, by rfl⟩ : syracuseStep 11188691 = 16783037) B16783037
theorem B68074667 : Blo 980594 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B5979395 : Blo 980594 5979395 := bstep (se 1 (by rfl) ⟨4484546, by rfl⟩ : syracuseStep 5979395 = 8969093) B8969093
theorem B2211803 : Blo 980594 2211803 := bstep (se 1 (by rfl) ⟨1658852, by rfl⟩ : syracuseStep 2211803 = 3317705) B3317705
theorem B2211983 : Blo 980594 2211983 := bstep (se 1 (by rfl) ⟨1658987, by rfl⟩ : syracuseStep 2211983 = 3317975) B3317975
theorem B2212073 : Blo 980594 2212073 := bstep (se 2 (by rfl) ⟨829527, by rfl⟩ : syracuseStep 2212073 = 1659055) B1659055
theorem B43042051 : Blo 980594 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B31934209 : Blo 980594 31934209 := bstep (se 2 (by rfl) ⟨11975328, by rfl⟩ : syracuseStep 31934209 = 23950657) B23950657
theorem B294766381 : Blo 980594 294766381 := bstep (se 3 (by rfl) ⟨55268696, by rfl⟩ : syracuseStep 294766381 = 110537393) B110537393
theorem B2213855 : Blo 980594 2213855 := bstep (se 1 (by rfl) ⟨1660391, by rfl⟩ : syracuseStep 2213855 = 3320783) B3320783
theorem B2214071 : Blo 980594 2214071 := bstep (se 1 (by rfl) ⟨1660553, by rfl⟩ : syracuseStep 2214071 = 3321107) B3321107
theorem B80693921 : Blo 980594 80693921 := bstep (se 2 (by rfl) ⟨30260220, by rfl⟩ : syracuseStep 80693921 = 60520441) B60520441
theorem B2214863 : Blo 980594 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B2214953 : Blo 980594 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B21285935 : Blo 980594 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B2215223 : Blo 980594 2215223 := bstep (se 1 (by rfl) ⟨1661417, by rfl⟩ : syracuseStep 2215223 = 3322835) B3322835
theorem B10603909 : Blo 980594 10603909 := bstep (se 4 (by rfl) ⟨994116, by rfl⟩ : syracuseStep 10603909 = 1988233) B1988233
theorem B5590565 : Blo 980594 5590565 := bstep (se 4 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 5590565 = 1048231) B1048231
theorem B8507123 : Blo 980594 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B11357981 : Blo 980594 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B1396559 : Blo 980594 1396559 := bstep (se 1 (by rfl) ⟨1047419, by rfl⟩ : syracuseStep 1396559 = 2094839) B2094839
theorem B3723367 : Blo 980594 3723367 := bstep (se 1 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 3723367 = 5585051) B5585051
theorem B1659001 : Blo 980594 1659001 := bstep (se 2 (by rfl) ⟨622125, by rfl⟩ : syracuseStep 1659001 = 1244251) B1244251
theorem B3723839 : Blo 980594 3723839 := bstep (se 1 (by rfl) ⟨2792879, by rfl⟩ : syracuseStep 3723839 = 5585759) B5585759
theorem B1660169 : Blo 980594 1660169 := bstep (se 2 (by rfl) ⟨622563, by rfl⟩ : syracuseStep 1660169 = 1245127) B1245127
theorem B4970159 : Blo 980594 4970159 := bstep (se 1 (by rfl) ⟨3727619, by rfl⟩ : syracuseStep 4970159 = 7455239) B7455239
theorem B11950031 : Blo 980594 11950031 := bstep (se 1 (by rfl) ⟨8962523, by rfl⟩ : syracuseStep 11950031 = 17925047) B17925047
theorem B1660999 : Blo 980594 1660999 := bstep (se 1 (by rfl) ⟨1245749, by rfl⟩ : syracuseStep 1660999 = 2491499) B2491499
theorem B3725783 : Blo 980594 3725783 := bstep (se 1 (by rfl) ⟨2794337, by rfl⟩ : syracuseStep 3725783 = 5588675) B5588675
theorem B1838733965 : Blo 980594 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B1990367 : Blo 980594 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B4972427 : Blo 980594 4972427 := bstep (se 1 (by rfl) ⟨3729320, by rfl⟩ : syracuseStep 4972427 = 7458641) B7458641
theorem B145219483 : Blo 980594 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B1106023 : Blo 980594 1106023 := bstep (se 1 (by rfl) ⟨829517, by rfl⟩ : syracuseStep 1106023 = 1659035) B1659035
theorem B3728015 : Blo 980594 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B40821677 : Blo 980594 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B10642661 : Blo 980594 10642661 := bstep (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) B1995499
theorem B1107175 : Blo 980594 1107175 := bstep (se 1 (by rfl) ⟨830381, by rfl⟩ : syracuseStep 1107175 = 1660763) B1660763
theorem B3729199 : Blo 980594 3729199 := bstep (se 1 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 3729199 = 5593799) B5593799
theorem B2484179 : Blo 980594 2484179 := bstep (se 1 (by rfl) ⟨1863134, by rfl⟩ : syracuseStep 2484179 = 3726269) B3726269
theorem B8382635 : Blo 980594 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B30238919 : Blo 980594 30238919 := bstep (se 1 (by rfl) ⟨22679189, by rfl⟩ : syracuseStep 30238919 = 45358379) B45358379
theorem B8972531 : Blo 980594 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B2484715 : Blo 980594 2484715 := bstep (se 1 (by rfl) ⟨1863536, by rfl⟩ : syracuseStep 2484715 = 3727073) B3727073
theorem B1862831 : Blo 980594 1862831 := bstep (se 1 (by rfl) ⟨1397123, by rfl⟩ : syracuseStep 1862831 = 2794247) B2794247
theorem B4484803 : Blo 980594 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B25882415 : Blo 980594 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B2486153 : Blo 980594 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B1241183 : Blo 980594 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B2486447 : Blo 980594 2486447 := bstep (se 1 (by rfl) ⟨1864835, by rfl⟩ : syracuseStep 2486447 = 3729671) B3729671
theorem B2519315 : Blo 980594 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B7467389 : Blo 980594 7467389 := bstep (se 3 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 7467389 = 2800271) B2800271
theorem B11203271 : Blo 980594 11203271 := bstep (se 1 (by rfl) ⟨8402453, by rfl⟩ : syracuseStep 11203271 = 16804907) B16804907
theorem B1471259 : Blo 980594 1471259 := bstep (se 1 (by rfl) ⟨1103444, by rfl⟩ : syracuseStep 1471259 = 2206889) B2206889
theorem B5305115 : Blo 980594 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B4977449 : Blo 980594 4977449 := bstep (se 2 (by rfl) ⟨1866543, by rfl⟩ : syracuseStep 4977449 = 3733087) B3733087
theorem B40399667 : Blo 980594 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B2487145 : Blo 980594 2487145 := bstep (se 2 (by rfl) ⟨932679, by rfl⟩ : syracuseStep 2487145 = 1865359) B1865359
theorem B2356271 : Blo 980594 2356271 := bstep (se 1 (by rfl) ⟨1767203, by rfl⟩ : syracuseStep 2356271 = 3534407) B3534407
theorem B1471535 : Blo 980594 1471535 := bstep (se 1 (by rfl) ⟨1103651, by rfl⟩ : syracuseStep 1471535 = 2207303) B2207303
theorem B5600339 : Blo 980594 5600339 := bstep (se 1 (by rfl) ⟨4200254, by rfl⟩ : syracuseStep 5600339 = 8400509) B8400509
theorem B1471583 : Blo 980594 1471583 := bstep (se 1 (by rfl) ⟨1103687, by rfl⟩ : syracuseStep 1471583 = 2207375) B2207375
theorem B1471643 : Blo 980594 1471643 := bstep (se 1 (by rfl) ⟨1103732, by rfl⟩ : syracuseStep 1471643 = 2207465) B2207465
theorem B1471655 : Blo 980594 1471655 := bstep (se 1 (by rfl) ⟨1103741, by rfl⟩ : syracuseStep 1471655 = 2207483) B2207483
theorem B13465241 : Blo 980594 13465241 := bstep (se 2 (by rfl) ⟨5049465, by rfl⟩ : syracuseStep 13465241 = 10098931) B10098931
theorem B1472327 : Blo 980594 1472327 := bstep (se 1 (by rfl) ⟨1104245, by rfl⟩ : syracuseStep 1472327 = 2208491) B2208491
theorem B980863 : Blo 980594 980863 := bstep (se 1 (by rfl) ⟨735647, by rfl⟩ : syracuseStep 980863 = 1471295) B1471295
theorem B4716463 : Blo 980594 4716463 := bstep (se 1 (by rfl) ⟨3537347, by rfl⟩ : syracuseStep 4716463 = 7074695) B7074695
theorem B980959 : Blo 980594 980959 := bstep (se 1 (by rfl) ⟨735719, by rfl⟩ : syracuseStep 980959 = 1471439) B1471439
theorem B980987 : Blo 980594 980987 := bstep (se 1 (by rfl) ⟨735740, by rfl⟩ : syracuseStep 980987 = 1471481) B1471481
theorem B1472507 : Blo 980594 1472507 := bstep (se 1 (by rfl) ⟨1104380, by rfl⟩ : syracuseStep 1472507 = 2208761) B2208761
theorem B981019 : Blo 980594 981019 := bstep (se 1 (by rfl) ⟨735764, by rfl⟩ : syracuseStep 981019 = 1471529) B1471529
theorem B981039 : Blo 980594 981039 := bstep (se 1 (by rfl) ⟨735779, by rfl⟩ : syracuseStep 981039 = 1471559) B1471559
theorem B1243183 : Blo 980594 1243183 := bstep (se 1 (by rfl) ⟨932387, by rfl⟩ : syracuseStep 1243183 = 1864775) B1864775
theorem B1472567 : Blo 980594 1472567 := bstep (se 1 (by rfl) ⟨1104425, by rfl⟩ : syracuseStep 1472567 = 2208851) B2208851
theorem B2488391 : Blo 980594 2488391 := bstep (se 1 (by rfl) ⟨1866293, by rfl⟩ : syracuseStep 2488391 = 3732587) B3732587
theorem B1472633 : Blo 980594 1472633 := bstep (se 2 (by rfl) ⟨552237, by rfl⟩ : syracuseStep 1472633 = 1104475) B1104475
theorem B2488441 : Blo 980594 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B981159 : Blo 980594 981159 := bstep (se 1 (by rfl) ⟨735869, by rfl⟩ : syracuseStep 981159 = 1471739) B1471739
theorem B1472687 : Blo 980594 1472687 := bstep (se 1 (by rfl) ⟨1104515, by rfl⟩ : syracuseStep 1472687 = 2209031) B2209031
theorem B6289721 : Blo 980594 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B1472927 : Blo 980594 1472927 := bstep (se 1 (by rfl) ⟨1104695, by rfl⟩ : syracuseStep 1472927 = 2209391) B2209391
theorem B1473017 : Blo 980594 1473017 := bstep (se 2 (by rfl) ⟨552381, by rfl⟩ : syracuseStep 1473017 = 1104763) B1104763
theorem B1866233 : Blo 980594 1866233 := bstep (se 2 (by rfl) ⟨699837, by rfl⟩ : syracuseStep 1866233 = 1399675) B1399675
theorem B6290257 : Blo 980594 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B981983 : Blo 980594 981983 := bstep (se 1 (by rfl) ⟨736487, by rfl⟩ : syracuseStep 981983 = 1472975) B1472975
theorem B1473503 : Blo 980594 1473503 := bstep (se 1 (by rfl) ⟨1105127, by rfl⟩ : syracuseStep 1473503 = 2210255) B2210255
theorem B982043 : Blo 980594 982043 := bstep (se 1 (by rfl) ⟨736532, by rfl⟩ : syracuseStep 982043 = 1473065) B1473065
theorem B1473563 : Blo 980594 1473563 := bstep (se 1 (by rfl) ⟨1105172, by rfl⟩ : syracuseStep 1473563 = 2210345) B2210345
theorem B42433631 : Blo 980594 42433631 := bstep (se 1 (by rfl) ⟨31825223, by rfl⟩ : syracuseStep 42433631 = 63650447) B63650447
theorem B982171 : Blo 980594 982171 := bstep (se 1 (by rfl) ⟨736628, by rfl⟩ : syracuseStep 982171 = 1473257) B1473257
theorem B982427 : Blo 980594 982427 := bstep (se 1 (by rfl) ⟨736820, by rfl⟩ : syracuseStep 982427 = 1473641) B1473641
theorem B1473947 : Blo 980594 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B1474025 : Blo 980594 1474025 := bstep (se 2 (by rfl) ⟨552759, by rfl⟩ : syracuseStep 1474025 = 1105519) B1105519
theorem B982511 : Blo 980594 982511 := bstep (se 1 (by rfl) ⟨736883, by rfl⟩ : syracuseStep 982511 = 1473767) B1473767
theorem B1474031 : Blo 980594 1474031 := bstep (se 1 (by rfl) ⟨1105523, by rfl⟩ : syracuseStep 1474031 = 2211047) B2211047
theorem B1474169 : Blo 980594 1474169 := bstep (se 2 (by rfl) ⟨552813, by rfl⟩ : syracuseStep 1474169 = 1105627) B1105627
theorem B982847 : Blo 980594 982847 := bstep (se 1 (by rfl) ⟨737135, by rfl⟩ : syracuseStep 982847 = 1474271) B1474271
theorem B1474367 : Blo 980594 1474367 := bstep (se 1 (by rfl) ⟨1105775, by rfl⟩ : syracuseStep 1474367 = 2211551) B2211551
theorem B982875 : Blo 980594 982875 := bstep (se 1 (by rfl) ⟨737156, by rfl⟩ : syracuseStep 982875 = 1474313) B1474313
theorem B2490203 : Blo 980594 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B1474415 : Blo 980594 1474415 := bstep (se 1 (by rfl) ⟨1105811, by rfl⟩ : syracuseStep 1474415 = 2211623) B2211623
theorem B2490223 : Blo 980594 2490223 := bstep (se 1 (by rfl) ⟨1867667, by rfl⟩ : syracuseStep 2490223 = 3735335) B3735335
theorem B5603255 : Blo 980594 5603255 := bstep (se 1 (by rfl) ⟨4202441, by rfl⟩ : syracuseStep 5603255 = 8404883) B8404883
theorem B1474655 : Blo 980594 1474655 := bstep (se 1 (by rfl) ⟨1105991, by rfl⟩ : syracuseStep 1474655 = 2211983) B2211983
theorem B1474697 : Blo 980594 1474697 := bstep (se 2 (by rfl) ⟨553011, by rfl⟩ : syracuseStep 1474697 = 1106023) B1106023
theorem B1474715 : Blo 980594 1474715 := bstep (se 1 (by rfl) ⟨1106036, by rfl⟩ : syracuseStep 1474715 = 2212073) B2212073
theorem B3309821 : Blo 980594 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B983399 : Blo 980594 983399 := bstep (se 1 (by rfl) ⟨737549, by rfl⟩ : syracuseStep 983399 = 1475099) B1475099
theorem B983519 : Blo 980594 983519 := bstep (se 1 (by rfl) ⟨737639, by rfl⟩ : syracuseStep 983519 = 1475279) B1475279
theorem B983599 : Blo 980594 983599 := bstep (se 1 (by rfl) ⟨737699, by rfl⟩ : syracuseStep 983599 = 1475399) B1475399
theorem B983643 : Blo 980594 983643 := bstep (se 1 (by rfl) ⟨737732, by rfl⟩ : syracuseStep 983643 = 1475465) B1475465
theorem B983807 : Blo 980594 983807 := bstep (se 1 (by rfl) ⟨737855, by rfl⟩ : syracuseStep 983807 = 1475711) B1475711
theorem B983899 : Blo 980594 983899 := bstep (se 1 (by rfl) ⟨737924, by rfl⟩ : syracuseStep 983899 = 1475849) B1475849
theorem B5309567 : Blo 980594 5309567 := bstep (se 1 (by rfl) ⟨3982175, by rfl⟩ : syracuseStep 5309567 = 7964351) B7964351
theorem B984219 : Blo 980594 984219 := bstep (se 1 (by rfl) ⟨738164, by rfl⟩ : syracuseStep 984219 = 1476329) B1476329
theorem B984223 : Blo 980594 984223 := bstep (se 1 (by rfl) ⟨738167, by rfl⟩ : syracuseStep 984223 = 1476335) B1476335
theorem B5113039 : Blo 980594 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B1475903 : Blo 980594 1475903 := bstep (se 1 (by rfl) ⟨1106927, by rfl⟩ : syracuseStep 1475903 = 2213855) B2213855
theorem B1049927 : Blo 980594 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B984391 : Blo 980594 984391 := bstep (se 1 (by rfl) ⟨738293, by rfl⟩ : syracuseStep 984391 = 1476587) B1476587
theorem B5604713 : Blo 980594 5604713 := bstep (se 2 (by rfl) ⟨2101767, by rfl⟩ : syracuseStep 5604713 = 4203535) B4203535
theorem B1476047 : Blo 980594 1476047 := bstep (se 1 (by rfl) ⟨1107035, by rfl⟩ : syracuseStep 1476047 = 2214071) B2214071
theorem B984559 : Blo 980594 984559 := bstep (se 1 (by rfl) ⟨738419, by rfl⟩ : syracuseStep 984559 = 1476839) B1476839
theorem B984575 : Blo 980594 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B5047823 : Blo 980594 5047823 := bstep (se 1 (by rfl) ⟨3785867, by rfl⟩ : syracuseStep 5047823 = 7571735) B7571735
theorem B1476233 : Blo 980594 1476233 := bstep (se 2 (by rfl) ⟨553587, by rfl⟩ : syracuseStep 1476233 = 1107175) B1107175
theorem B1476575 : Blo 980594 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B1476635 : Blo 980594 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B14190623 : Blo 980594 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B1476815 : Blo 980594 1476815 := bstep (se 1 (by rfl) ⟨1107611, by rfl⟩ : syracuseStep 1476815 = 2215223) B2215223
theorem B4196717 : Blo 980594 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B393021841 : Blo 980594 393021841 := bstep (se 2 (by rfl) ⟨147383190, by rfl⟩ : syracuseStep 393021841 = 294766381) B294766381
theorem B5671415 : Blo 980594 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B7571987 : Blo 980594 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B3148409 : Blo 980594 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B23858225 : Blo 980594 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B37751993 : Blo 980594 37751993 := bstep (se 2 (by rfl) ⟨14156997, by rfl⟩ : syracuseStep 37751993 = 28313995) B28313995
theorem B3312953 : Blo 980594 3312953 := bstep (se 2 (by rfl) ⟨1242357, by rfl⟩ : syracuseStep 3312953 = 2484715) B2484715
theorem B3149383 : Blo 980594 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B3313439 : Blo 980594 3313439 := bstep (se 1 (by rfl) ⟨2485079, by rfl⟩ : syracuseStep 3313439 = 4970159) B4970159
theorem B7966687 : Blo 980594 7966687 := bstep (se 1 (by rfl) ⟨5975015, by rfl⟩ : syracuseStep 7966687 = 11950031) B11950031
theorem B13438979 : Blo 980594 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B1225822643 : Blo 980594 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B2364191 : Blo 980594 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B2364671 : Blo 980594 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B2102527 : Blo 980594 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B3314951 : Blo 980594 3314951 := bstep (se 1 (by rfl) ⟨2486213, by rfl⟩ : syracuseStep 3314951 = 4972427) B4972427
theorem B3316193 : Blo 980594 3316193 := bstep (se 2 (by rfl) ⟨1243572, by rfl⟩ : syracuseStep 3316193 = 2487145) B2487145
theorem B20159279 : Blo 980594 20159279 := bstep (se 1 (by rfl) ⟨15119459, by rfl⟩ : syracuseStep 20159279 = 30238919) B30238919
theorem B4201895 : Blo 980594 4201895 := bstep (se 1 (by rfl) ⟨3151421, by rfl⟩ : syracuseStep 4201895 = 6302843) B6302843
theorem B3546575 : Blo 980594 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B3317921 : Blo 980594 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B1679543 : Blo 980594 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B3318299 : Blo 980594 3318299 := bstep (se 1 (by rfl) ⟨2488724, by rfl⟩ : syracuseStep 3318299 = 4977449) B4977449
theorem B15935453 : Blo 980594 15935453 := bstep (se 3 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 15935453 = 5975795) B5975795
theorem B28289087 : Blo 980594 28289087 := bstep (se 1 (by rfl) ⟨21216815, by rfl⟩ : syracuseStep 28289087 = 42433631) B42433631
theorem B7088249 : Blo 980594 7088249 := bstep (se 2 (by rfl) ⟨2658093, by rfl⟩ : syracuseStep 7088249 = 5316187) B5316187
theorem B3320297 : Blo 980594 3320297 := bstep (se 2 (by rfl) ⟨1245111, by rfl⟩ : syracuseStep 3320297 = 2490223) B2490223
theorem B7089457 : Blo 980594 7089457 := bstep (se 2 (by rfl) ⟨2658546, by rfl⟩ : syracuseStep 7089457 = 5317093) B5317093
theorem B2207087 : Blo 980594 2207087 := bstep (se 1 (by rfl) ⟨1655315, by rfl⟩ : syracuseStep 2207087 = 3310631) B3310631
theorem B2207735 : Blo 980594 2207735 := bstep (se 1 (by rfl) ⟨1655801, by rfl⟩ : syracuseStep 2207735 = 3311603) B3311603
theorem B2207807 : Blo 980594 2207807 := bstep (se 1 (by rfl) ⟨1655855, by rfl⟩ : syracuseStep 2207807 = 3311711) B3311711
theorem B3322025 : Blo 980594 3322025 := bstep (se 2 (by rfl) ⟨1245759, by rfl⟩ : syracuseStep 3322025 = 2491519) B2491519
theorem B57389401 : Blo 980594 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B2208095 : Blo 980594 2208095 := bstep (se 1 (by rfl) ⟨1656071, by rfl⟩ : syracuseStep 2208095 = 3312143) B3312143
theorem B42578945 : Blo 980594 42578945 := bstep (se 2 (by rfl) ⟨15967104, by rfl⟩ : syracuseStep 42578945 = 31934209) B31934209
theorem B2208815 : Blo 980594 2208815 := bstep (se 1 (by rfl) ⟨1656611, by rfl⟩ : syracuseStep 2208815 = 3313223) B3313223
theorem B7451837 : Blo 980594 7451837 := bstep (se 3 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 7451837 = 2794439) B2794439
theorem B2209787 : Blo 980594 2209787 := bstep (se 1 (by rfl) ⟨1657340, by rfl⟩ : syracuseStep 2209787 = 3314681) B3314681
theorem B16791785 : Blo 980594 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B8632739 : Blo 980594 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B14138545 : Blo 980594 14138545 := bstep (se 2 (by rfl) ⟨5301954, by rfl⟩ : syracuseStep 14138545 = 10603909) B10603909
theorem B5979737 : Blo 980594 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B1326911 : Blo 980594 1326911 := bstep (se 1 (by rfl) ⟨995183, by rfl⟩ : syracuseStep 1326911 = 1990367) B1990367
theorem B4964489 : Blo 980594 4964489 := bstep (se 2 (by rfl) ⟨1861683, by rfl⟩ : syracuseStep 4964489 = 3723367) B3723367
theorem B2212001 : Blo 980594 2212001 := bstep (se 2 (by rfl) ⟨829500, by rfl⟩ : syracuseStep 2212001 = 1659001) B1659001
theorem B27214451 : Blo 980594 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B7095107 : Blo 980594 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B12600197 : Blo 980594 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B1656119 : Blo 980594 1656119 := bstep (se 1 (by rfl) ⟨1242089, by rfl⟩ : syracuseStep 1656119 = 2484179) B2484179
theorem B5588423 : Blo 980594 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B5981687 : Blo 980594 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B2214143 : Blo 980594 2214143 := bstep (se 1 (by rfl) ⟨1660607, by rfl⟩ : syracuseStep 2214143 = 3321215) B3321215
theorem B17254943 : Blo 980594 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B1657435 : Blo 980594 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B1657577 : Blo 980594 1657577 := bstep (se 2 (by rfl) ⟨621591, by rfl⟩ : syracuseStep 1657577 = 1243183) B1243183
theorem B4475645 : Blo 980594 4475645 := bstep (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) B1678367
theorem B2214665 : Blo 980594 2214665 := bstep (se 2 (by rfl) ⟨830499, by rfl⟩ : syracuseStep 2214665 = 1660999) B1660999
theorem B1657631 : Blo 980594 1657631 := bstep (se 1 (by rfl) ⟨1243223, by rfl⟩ : syracuseStep 1657631 = 2486447) B2486447
theorem B2215079 : Blo 980594 2215079 := bstep (se 1 (by rfl) ⟨1661309, by rfl⟩ : syracuseStep 2215079 = 3322619) B3322619
theorem B1658927 : Blo 980594 1658927 := bstep (se 1 (by rfl) ⟨1244195, by rfl⟩ : syracuseStep 1658927 = 2488391) B2488391
theorem B4968539 : Blo 980594 4968539 := bstep (se 1 (by rfl) ⟨3726404, by rfl⟩ : syracuseStep 4968539 = 7452809) B7452809
theorem B7459127 : Blo 980594 7459127 := bstep (se 1 (by rfl) ⟨5594345, by rfl⟩ : syracuseStep 7459127 = 11188691) B11188691
theorem B3986263 : Blo 980594 3986263 := bstep (se 1 (by rfl) ⟨2989697, by rfl⟩ : syracuseStep 3986263 = 5979395) B5979395
theorem B3724157 : Blo 980594 3724157 := bstep (se 3 (by rfl) ⟨698279, by rfl⟩ : syracuseStep 3724157 = 1396559) B1396559
theorem B1660135 : Blo 980594 1660135 := bstep (se 1 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 1660135 = 2490203) B2490203
theorem B9557693 : Blo 980594 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B1398655 : Blo 980594 1398655 := bstep (se 1 (by rfl) ⟨1048991, by rfl⟩ : syracuseStep 1398655 = 2097983) B2097983
theorem B53795947 : Blo 980594 53795947 := bstep (se 1 (by rfl) ⟨40346960, by rfl⟩ : syracuseStep 53795947 = 80693921) B80693921
theorem B5594255 : Blo 980594 5594255 := bstep (se 1 (by rfl) ⟨4195691, by rfl⟩ : syracuseStep 5594255 = 8391383) B8391383
theorem B14146973 : Blo 980594 14146973 := bstep (se 3 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 14146973 = 5305115) B5305115
theorem B3727043 : Blo 980594 3727043 := bstep (se 1 (by rfl) ⟨2795282, by rfl⟩ : syracuseStep 3727043 = 5590565) B5590565
theorem B4972265 : Blo 980594 4972265 := bstep (se 2 (by rfl) ⟨1864599, by rfl⟩ : syracuseStep 4972265 = 3729199) B3729199
theorem B7954301 : Blo 980594 7954301 := bstep (se 3 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 7954301 = 2982863) B2982863
theorem B2482559 : Blo 980594 2482559 := bstep (se 1 (by rfl) ⟨1861919, by rfl⟩ : syracuseStep 2482559 = 3723839) B3723839
theorem B4776529 : Blo 980594 4776529 := bstep (se 2 (by rfl) ⟨1791198, by rfl⟩ : syracuseStep 4776529 = 3582397) B3582397
theorem B1106779 : Blo 980594 1106779 := bstep (se 1 (by rfl) ⟨830084, by rfl⟩ : syracuseStep 1106779 = 1660169) B1660169
theorem B1401799 : Blo 980594 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1401833 : Blo 980594 1401833 := bstep (se 2 (by rfl) ⟨525687, by rfl⟩ : syracuseStep 1401833 = 1051375) B1051375
theorem B3728713 : Blo 980594 3728713 := bstep (se 2 (by rfl) ⟨1398267, by rfl⟩ : syracuseStep 3728713 = 2796535) B2796535
theorem B14181911 : Blo 980594 14181911 := bstep (se 1 (by rfl) ⟨10636433, by rfl⟩ : syracuseStep 14181911 = 21272867) B21272867
theorem B2483855 : Blo 980594 2483855 := bstep (se 1 (by rfl) ⟨1862891, by rfl⟩ : syracuseStep 2483855 = 3725783) B3725783
theorem B51046037 : Blo 980594 51046037 := bstep (se 6 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 51046037 = 2392783) B2392783
theorem B7563091 : Blo 980594 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B1796051 : Blo 980594 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B2485343 : Blo 980594 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B2125343 : Blo 980594 2125343 := bstep (se 1 (by rfl) ⟨1594007, by rfl⟩ : syracuseStep 2125343 = 3188015) B3188015
theorem B1241887 : Blo 980594 1241887 := bstep (se 1 (by rfl) ⟨931415, by rfl⟩ : syracuseStep 1241887 = 1862831) B1862831
theorem B1471679 : Blo 980594 1471679 := bstep (se 1 (by rfl) ⟨1103759, by rfl⟩ : syracuseStep 1471679 = 2207519) B2207519
theorem B6288617 : Blo 980594 6288617 := bstep (se 2 (by rfl) ⟨2358231, by rfl⟩ : syracuseStep 6288617 = 4716463) B4716463
theorem B1472027 : Blo 980594 1472027 := bstep (se 1 (by rfl) ⟨1104020, by rfl⟩ : syracuseStep 1472027 = 2208041) B2208041
theorem B4978259 : Blo 980594 4978259 := bstep (se 1 (by rfl) ⟨3733694, by rfl⟩ : syracuseStep 4978259 = 7467389) B7467389
theorem B8976025 : Blo 980594 8976025 := bstep (se 2 (by rfl) ⟨3366009, by rfl⟩ : syracuseStep 8976025 = 6732019) B6732019
theorem B1472207 : Blo 980594 1472207 := bstep (se 1 (by rfl) ⟨1104155, by rfl⟩ : syracuseStep 1472207 = 2208311) B2208311
theorem B16152335 : Blo 980594 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B7468847 : Blo 980594 7468847 := bstep (se 1 (by rfl) ⟨5601635, by rfl⟩ : syracuseStep 7468847 = 11203271) B11203271
theorem B980839 : Blo 980594 980839 := bstep (se 1 (by rfl) ⟨735629, by rfl⟩ : syracuseStep 980839 = 1471259) B1471259
theorem B26933111 : Blo 980594 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B1472447 : Blo 980594 1472447 := bstep (se 1 (by rfl) ⟨1104335, by rfl⟩ : syracuseStep 1472447 = 2208671) B2208671
theorem B1865663 : Blo 980594 1865663 := bstep (se 1 (by rfl) ⟨1399247, by rfl⟩ : syracuseStep 1865663 = 2798495) B2798495
theorem B1570847 : Blo 980594 1570847 := bstep (se 1 (by rfl) ⟨1178135, by rfl⟩ : syracuseStep 1570847 = 2356271) B2356271
theorem B981023 : Blo 980594 981023 := bstep (se 1 (by rfl) ⟨735767, by rfl⟩ : syracuseStep 981023 = 1471535) B1471535
theorem B3733559 : Blo 980594 3733559 := bstep (se 1 (by rfl) ⟨2800169, by rfl⟩ : syracuseStep 3733559 = 5600339) B5600339
theorem B981055 : Blo 980594 981055 := bstep (se 1 (by rfl) ⟨735791, by rfl⟩ : syracuseStep 981055 = 1471583) B1471583
theorem B981095 : Blo 980594 981095 := bstep (se 1 (by rfl) ⟨735821, by rfl⟩ : syracuseStep 981095 = 1471643) B1471643
theorem B981103 : Blo 980594 981103 := bstep (se 1 (by rfl) ⟨735827, by rfl⟩ : syracuseStep 981103 = 1471655) B1471655
theorem B8976827 : Blo 980594 8976827 := bstep (se 1 (by rfl) ⟨6732620, by rfl⟩ : syracuseStep 8976827 = 13465241) B13465241
theorem B8387009 : Blo 980594 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B1472999 : Blo 980594 1472999 := bstep (se 1 (by rfl) ⟨1104749, by rfl⟩ : syracuseStep 1472999 = 2209499) B2209499
theorem B981551 : Blo 980594 981551 := bstep (se 1 (by rfl) ⟨736163, by rfl⟩ : syracuseStep 981551 = 1472327) B1472327
theorem B981671 : Blo 980594 981671 := bstep (se 1 (by rfl) ⟨736253, by rfl⟩ : syracuseStep 981671 = 1472507) B1472507
theorem B981711 : Blo 980594 981711 := bstep (se 1 (by rfl) ⟨736283, by rfl⟩ : syracuseStep 981711 = 1472567) B1472567
theorem B981755 : Blo 980594 981755 := bstep (se 1 (by rfl) ⟨736316, by rfl⟩ : syracuseStep 981755 = 1472633) B1472633
theorem B981791 : Blo 980594 981791 := bstep (se 1 (by rfl) ⟨736343, by rfl⟩ : syracuseStep 981791 = 1472687) B1472687
theorem B4193147 : Blo 980594 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B981951 : Blo 980594 981951 := bstep (se 1 (by rfl) ⟨736463, by rfl⟩ : syracuseStep 981951 = 1472927) B1472927
theorem B1866719 : Blo 980594 1866719 := bstep (se 1 (by rfl) ⟨1400039, by rfl⟩ : syracuseStep 1866719 = 2800079) B2800079
theorem B982011 : Blo 980594 982011 := bstep (se 1 (by rfl) ⟨736508, by rfl⟩ : syracuseStep 982011 = 1473017) B1473017
theorem B1244155 : Blo 980594 1244155 := bstep (se 1 (by rfl) ⟨933116, by rfl⟩ : syracuseStep 1244155 = 1866233) B1866233
theorem B982335 : Blo 980594 982335 := bstep (se 1 (by rfl) ⟨736751, by rfl⟩ : syracuseStep 982335 = 1473503) B1473503
theorem B982375 : Blo 980594 982375 := bstep (se 1 (by rfl) ⟨736781, by rfl⟩ : syracuseStep 982375 = 1473563) B1473563
theorem B45383111 : Blo 980594 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B982631 : Blo 980594 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B982683 : Blo 980594 982683 := bstep (se 1 (by rfl) ⟨737012, by rfl⟩ : syracuseStep 982683 = 1474025) B1474025
theorem B982687 : Blo 980594 982687 := bstep (se 1 (by rfl) ⟨737015, by rfl⟩ : syracuseStep 982687 = 1474031) B1474031
theorem B982779 : Blo 980594 982779 := bstep (se 1 (by rfl) ⟨737084, by rfl⟩ : syracuseStep 982779 = 1474169) B1474169
theorem B193625977 : Blo 980594 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B982911 : Blo 980594 982911 := bstep (se 1 (by rfl) ⟨737183, by rfl⟩ : syracuseStep 982911 = 1474367) B1474367
theorem B982943 : Blo 980594 982943 := bstep (se 1 (by rfl) ⟨737207, by rfl⟩ : syracuseStep 982943 = 1474415) B1474415
theorem B3735503 : Blo 980594 3735503 := bstep (se 1 (by rfl) ⟨2801627, by rfl⟩ : syracuseStep 3735503 = 5603255) B5603255
theorem B1474535 : Blo 980594 1474535 := bstep (se 1 (by rfl) ⟨1105901, by rfl⟩ : syracuseStep 1474535 = 2211803) B2211803
theorem B983103 : Blo 980594 983103 := bstep (se 1 (by rfl) ⟨737327, by rfl⟩ : syracuseStep 983103 = 1474655) B1474655
theorem B3309659 : Blo 980594 3309659 := bstep (se 1 (by rfl) ⟨2482244, by rfl⟩ : syracuseStep 3309659 = 4964489) B4964489
theorem B983131 : Blo 980594 983131 := bstep (se 1 (by rfl) ⟨737348, by rfl⟩ : syracuseStep 983131 = 1474697) B1474697
theorem B983143 : Blo 980594 983143 := bstep (se 1 (by rfl) ⟨737357, by rfl⟩ : syracuseStep 983143 = 1474715) B1474715
theorem B1474667 : Blo 980594 1474667 := bstep (se 1 (by rfl) ⟨1106000, by rfl⟩ : syracuseStep 1474667 = 2212001) B2212001
theorem B3539711 : Blo 980594 3539711 := bstep (se 1 (by rfl) ⟨2654783, by rfl⟩ : syracuseStep 3539711 = 5309567) B5309567
theorem B983935 : Blo 980594 983935 := bstep (se 1 (by rfl) ⟨737951, by rfl⟩ : syracuseStep 983935 = 1475903) B1475903
theorem B3736475 : Blo 980594 3736475 := bstep (se 1 (by rfl) ⟨2802356, by rfl⟩ : syracuseStep 3736475 = 5604713) B5604713
theorem B984031 : Blo 980594 984031 := bstep (se 1 (by rfl) ⟨738023, by rfl⟩ : syracuseStep 984031 = 1476047) B1476047
theorem B984155 : Blo 980594 984155 := bstep (se 1 (by rfl) ⟨738116, by rfl⟩ : syracuseStep 984155 = 1476233) B1476233
theorem B1475705 : Blo 980594 1475705 := bstep (se 2 (by rfl) ⟨553389, by rfl⟩ : syracuseStep 1475705 = 1106779) B1106779
theorem B1869065 : Blo 980594 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B984383 : Blo 980594 984383 := bstep (se 1 (by rfl) ⟨738287, by rfl⟩ : syracuseStep 984383 = 1476575) B1476575
theorem B984423 : Blo 980594 984423 := bstep (se 1 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 984423 = 1476635) B1476635
theorem B984543 : Blo 980594 984543 := bstep (se 1 (by rfl) ⟨738407, by rfl⟩ : syracuseStep 984543 = 1476815) B1476815
theorem B1476095 : Blo 980594 1476095 := bstep (se 1 (by rfl) ⟨1107071, by rfl⟩ : syracuseStep 1476095 = 2214143) B2214143
theorem B6817385 : Blo 980594 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B5047991 : Blo 980594 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B11503295 : Blo 980594 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B2983763 : Blo 980594 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B1476443 : Blo 980594 1476443 := bstep (se 1 (by rfl) ⟨1107332, by rfl⟩ : syracuseStep 1476443 = 2214665) B2214665
theorem B1476719 : Blo 980594 1476719 := bstep (se 1 (by rfl) ⟨1107539, by rfl⟩ : syracuseStep 1476719 = 2215079) B2215079
theorem B25167995 : Blo 980594 25167995 := bstep (se 1 (by rfl) ⟨18875996, by rfl⟩ : syracuseStep 25167995 = 37751993) B37751993
theorem B3738221 : Blo 980594 3738221 := bstep (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) B1401833
theorem B3312359 : Blo 980594 3312359 := bstep (se 1 (by rfl) ⟨2484269, by rfl⟩ : syracuseStep 3312359 = 4968539) B4968539
theorem B1576127 : Blo 980594 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B524029121 : Blo 980594 524029121 := bstep (se 2 (by rfl) ⟨196510920, by rfl⟩ : syracuseStep 524029121 = 393021841) B393021841
theorem B13439519 : Blo 980594 13439519 := bstep (se 1 (by rfl) ⟨10079639, by rfl⟩ : syracuseStep 13439519 = 20159279) B20159279
theorem B4199177 : Blo 980594 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B2364383 : Blo 980594 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B3314843 : Blo 980594 3314843 := bstep (se 1 (by rfl) ⟨2486132, by rfl⟩ : syracuseStep 3314843 = 4972265) B4972265
theorem B4789469 : Blo 980594 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B10622249 : Blo 980594 10622249 := bstep (se 2 (by rfl) ⟨3983343, by rfl⟩ : syracuseStep 10622249 = 7966687) B7966687
theorem B1119695 : Blo 980594 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B76519201 : Blo 980594 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B10623635 : Blo 980594 10623635 := bstep (se 1 (by rfl) ⟨7967726, by rfl⟩ : syracuseStep 10623635 = 15935453) B15935453
theorem B11213477 : Blo 980594 11213477 := bstep (se 4 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 11213477 = 2102527) B2102527
theorem B4725499 : Blo 980594 4725499 := bstep (se 1 (by rfl) ⟨3544124, by rfl⟩ : syracuseStep 4725499 = 7088249) B7088249
theorem B8395757 : Blo 980594 8395757 := bstep (se 3 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 8395757 = 3148409) B3148409
theorem B1416895 : Blo 980594 1416895 := bstep (se 1 (by rfl) ⟨1062671, by rfl⟩ : syracuseStep 1416895 = 2125343) B2125343
theorem B28385963 : Blo 980594 28385963 := bstep (se 1 (by rfl) ⟨21289472, by rfl⟩ : syracuseStep 28385963 = 42578945) B42578945
theorem B3318839 : Blo 980594 3318839 := bstep (se 1 (by rfl) ⟨2489129, by rfl⟩ : syracuseStep 3318839 = 4978259) B4978259
theorem B18851393 : Blo 980594 18851393 := bstep (se 2 (by rfl) ⟨7069272, by rfl⟩ : syracuseStep 18851393 = 14138545) B14138545
theorem B2795431 : Blo 980594 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B30255407 : Blo 980594 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B2206547 : Blo 980594 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B4730071 : Blo 980594 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B8400131 : Blo 980594 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B6368705 : Blo 980594 6368705 := bstep (se 2 (by rfl) ⟨2388264, by rfl⟩ : syracuseStep 6368705 = 4776529) B4776529
theorem B2797811 : Blo 980594 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B15905483 : Blo 980594 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B2208635 : Blo 980594 2208635 := bstep (se 1 (by rfl) ⟨1656476, by rfl⟩ : syracuseStep 2208635 = 3312953) B3312953
theorem B2208959 : Blo 980594 2208959 := bstep (se 1 (by rfl) ⟨1656719, by rfl⟩ : syracuseStep 2208959 = 3313439) B3313439
theorem B8959319 : Blo 980594 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B817215095 : Blo 980594 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B6305789 : Blo 980594 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B2209913 : Blo 980594 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B2209967 : Blo 980594 2209967 := bstep (se 1 (by rfl) ⟨1657475, by rfl⟩ : syracuseStep 2209967 = 3314951) B3314951
theorem B2799805 : Blo 980594 2799805 := bstep (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) B1049927
theorem B6371795 : Blo 980594 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B2210795 : Blo 980594 2210795 := bstep (se 1 (by rfl) ⟨1658096, by rfl⟩ : syracuseStep 2210795 = 3316193) B3316193
theorem B9452609 : Blo 980594 9452609 := bstep (se 2 (by rfl) ⟨3544728, by rfl⟩ : syracuseStep 9452609 = 7089457) B7089457
theorem B2801263 : Blo 980594 2801263 := bstep (se 1 (by rfl) ⟨2100947, by rfl⟩ : syracuseStep 2801263 = 4201895) B4201895
theorem B2211947 : Blo 980594 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B1655039 : Blo 980594 1655039 := bstep (se 1 (by rfl) ⟨1241279, by rfl⟩ : syracuseStep 1655039 = 2482559) B2482559
theorem B2212199 : Blo 980594 2212199 := bstep (se 1 (by rfl) ⟨1659149, by rfl⟩ : syracuseStep 2212199 = 3318299) B3318299
theorem B9454607 : Blo 980594 9454607 := bstep (se 1 (by rfl) ⟨7090955, by rfl⟩ : syracuseStep 9454607 = 14181911) B14181911
theorem B1655849 : Blo 980594 1655849 := bstep (se 2 (by rfl) ⟨620943, by rfl⟩ : syracuseStep 1655849 = 1241887) B1241887
theorem B1655903 : Blo 980594 1655903 := bstep (se 1 (by rfl) ⟨1241927, by rfl⟩ : syracuseStep 1655903 = 2483855) B2483855
theorem B34030691 : Blo 980594 34030691 := bstep (se 1 (by rfl) ⟨25523018, by rfl⟩ : syracuseStep 34030691 = 51046037) B51046037
theorem B15123773 : Blo 980594 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B18859391 : Blo 980594 18859391 := bstep (se 1 (by rfl) ⟨14144543, by rfl⟩ : syracuseStep 18859391 = 28289087) B28289087
theorem B2213513 : Blo 980594 2213513 := bstep (se 2 (by rfl) ⟨830067, by rfl⟩ : syracuseStep 2213513 = 1660135) B1660135
theorem B2213531 : Blo 980594 2213531 := bstep (se 1 (by rfl) ⟨1660148, by rfl⟩ : syracuseStep 2213531 = 3320297) B3320297
theorem B1656895 : Blo 980594 1656895 := bstep (se 1 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 1656895 = 2485343) B2485343
theorem B2214683 : Blo 980594 2214683 := bstep (se 1 (by rfl) ⟨1661012, by rfl⟩ : syracuseStep 2214683 = 3322025) B3322025
theorem B4967891 : Blo 980594 4967891 := bstep (se 1 (by rfl) ⟨3725918, by rfl⟩ : syracuseStep 4967891 = 7451837) B7451837
theorem B10768223 : Blo 980594 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B1658873 : Blo 980594 1658873 := bstep (se 2 (by rfl) ⟨622077, by rfl⟩ : syracuseStep 1658873 = 1244155) B1244155
theorem B11194523 : Blo 980594 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B5755159 : Blo 980594 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B5984551 : Blo 980594 5984551 := bstep (se 1 (by rfl) ⟨4488413, by rfl⟩ : syracuseStep 5984551 = 8976827) B8976827
theorem B5591339 : Blo 980594 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B3986491 : Blo 980594 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B258167969 : Blo 980594 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B18142967 : Blo 980594 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1104079 : Blo 980594 1104079 := bstep (se 1 (by rfl) ⟨828059, by rfl⟩ : syracuseStep 1104079 = 1656119) B1656119
theorem B3725615 : Blo 980594 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B3987791 : Blo 980594 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B3365215 : Blo 980594 3365215 := bstep (se 1 (by rfl) ⟨2523911, by rfl⟩ : syracuseStep 3365215 = 5047823) B5047823
theorem B9460415 : Blo 980594 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B4971617 : Blo 980594 4971617 := bstep (se 2 (by rfl) ⟨1864356, by rfl⟩ : syracuseStep 4971617 = 3728713) B3728713
theorem B1105051 : Blo 980594 1105051 := bstep (se 1 (by rfl) ⟨828788, by rfl⟩ : syracuseStep 1105051 = 1657577) B1657577
theorem B1105087 : Blo 980594 1105087 := bstep (se 1 (by rfl) ⟨828815, by rfl⟩ : syracuseStep 1105087 = 1657631) B1657631
theorem B10084121 : Blo 980594 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B1105951 : Blo 980594 1105951 := bstep (se 1 (by rfl) ⟨829463, by rfl⟩ : syracuseStep 1105951 = 1658927) B1658927
theorem B4972751 : Blo 980594 4972751 := bstep (se 1 (by rfl) ⟨3729563, by rfl⟩ : syracuseStep 4972751 = 7459127) B7459127
theorem B2482771 : Blo 980594 2482771 := bstep (se 1 (by rfl) ⟨1862078, by rfl⟩ : syracuseStep 2482771 = 3724157) B3724157
theorem B21260069 : Blo 980594 21260069 := bstep (se 4 (by rfl) ⟨1993131, by rfl⟩ : syracuseStep 21260069 = 3986263) B3986263
theorem B3729503 : Blo 980594 3729503 := bstep (se 1 (by rfl) ⟨2797127, by rfl⟩ : syracuseStep 3729503 = 5594255) B5594255
theorem B9431315 : Blo 980594 9431315 := bstep (se 1 (by rfl) ⟨7073486, by rfl⟩ : syracuseStep 9431315 = 14146973) B14146973
theorem B2484695 : Blo 980594 2484695 := bstep (se 1 (by rfl) ⟨1863521, by rfl⟩ : syracuseStep 2484695 = 3727043) B3727043
theorem B5302867 : Blo 980594 5302867 := bstep (se 1 (by rfl) ⟨3977150, by rfl⟩ : syracuseStep 5302867 = 7954301) B7954301
theorem B4188925 : Blo 980594 4188925 := bstep (se 3 (by rfl) ⟨785423, by rfl⟩ : syracuseStep 4188925 = 1570847) B1570847
theorem B1471391 : Blo 980594 1471391 := bstep (se 1 (by rfl) ⟨1103543, by rfl⟩ : syracuseStep 1471391 = 2207087) B2207087
theorem B1864873 : Blo 980594 1864873 := bstep (se 2 (by rfl) ⟨699327, by rfl⟩ : syracuseStep 1864873 = 1398655) B1398655
theorem B1471823 : Blo 980594 1471823 := bstep (se 1 (by rfl) ⟨1103867, by rfl⟩ : syracuseStep 1471823 = 2207735) B2207735
theorem B1471871 : Blo 980594 1471871 := bstep (se 1 (by rfl) ⟨1103903, by rfl⟩ : syracuseStep 1471871 = 2207807) B2207807
theorem B1472063 : Blo 980594 1472063 := bstep (se 1 (by rfl) ⟨1104047, by rfl⟩ : syracuseStep 1472063 = 2208095) B2208095
theorem B14153717 : Blo 980594 14153717 := bstep (se 5 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 14153717 = 1326911) B1326911
theorem B1472543 : Blo 980594 1472543 := bstep (se 1 (by rfl) ⟨1104407, by rfl⟩ : syracuseStep 1472543 = 2208815) B2208815
theorem B981119 : Blo 980594 981119 := bstep (se 1 (by rfl) ⟨735839, by rfl⟩ : syracuseStep 981119 = 1471679) B1471679
theorem B47872133 : Blo 980594 47872133 := bstep (se 4 (by rfl) ⟨4488012, by rfl⟩ : syracuseStep 47872133 = 8976025) B8976025
theorem B4192411 : Blo 980594 4192411 := bstep (se 1 (by rfl) ⟨3144308, by rfl⟩ : syracuseStep 4192411 = 6288617) B6288617
theorem B981351 : Blo 980594 981351 := bstep (se 1 (by rfl) ⟨736013, by rfl⟩ : syracuseStep 981351 = 1472027) B1472027
theorem B981471 : Blo 980594 981471 := bstep (se 1 (by rfl) ⟨736103, by rfl⟩ : syracuseStep 981471 = 1472207) B1472207
theorem B4979231 : Blo 980594 4979231 := bstep (se 1 (by rfl) ⟨3734423, by rfl⟩ : syracuseStep 4979231 = 7468847) B7468847
theorem B17955407 : Blo 980594 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B981631 : Blo 980594 981631 := bstep (se 1 (by rfl) ⟨736223, by rfl⟩ : syracuseStep 981631 = 1472447) B1472447
theorem B1243775 : Blo 980594 1243775 := bstep (se 1 (by rfl) ⟨932831, by rfl⟩ : syracuseStep 1243775 = 1865663) B1865663
theorem B1473191 : Blo 980594 1473191 := bstep (se 1 (by rfl) ⟨1104893, by rfl⟩ : syracuseStep 1473191 = 2209787) B2209787
theorem B2489039 : Blo 980594 2489039 := bstep (se 1 (by rfl) ⟨1866779, by rfl⟩ : syracuseStep 2489039 = 3733559) B3733559
theorem B71727929 : Blo 980594 71727929 := bstep (se 2 (by rfl) ⟨26897973, by rfl⟩ : syracuseStep 71727929 = 53795947) B53795947
theorem B981999 : Blo 980594 981999 := bstep (se 1 (by rfl) ⟨736499, by rfl⟩ : syracuseStep 981999 = 1472999) B1472999
theorem B1244479 : Blo 980594 1244479 := bstep (se 1 (by rfl) ⟨933359, by rfl⟩ : syracuseStep 1244479 = 1866719) B1866719
theorem B2490335 : Blo 980594 2490335 := bstep (se 1 (by rfl) ⟨1867751, by rfl⟩ : syracuseStep 2490335 = 3735503) B3735503
theorem B983023 : Blo 980594 983023 := bstep (se 1 (by rfl) ⟨737267, by rfl⟩ : syracuseStep 983023 = 1474535) B1474535
theorem B1474601 : Blo 980594 1474601 := bstep (se 2 (by rfl) ⟨552975, by rfl⟩ : syracuseStep 1474601 = 1105951) B1105951
theorem B1474631 : Blo 980594 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B983111 : Blo 980594 983111 := bstep (se 1 (by rfl) ⟨737333, by rfl⟩ : syracuseStep 983111 = 1474667) B1474667
theorem B1474799 : Blo 980594 1474799 := bstep (se 1 (by rfl) ⟨1106099, by rfl⟩ : syracuseStep 1474799 = 2212199) B2212199
theorem B2490983 : Blo 980594 2490983 := bstep (se 1 (by rfl) ⟨1868237, by rfl⟩ : syracuseStep 2490983 = 3736475) B3736475
theorem B983803 : Blo 980594 983803 := bstep (se 1 (by rfl) ⟨737852, by rfl⟩ : syracuseStep 983803 = 1475705) B1475705
theorem B3310361 : Blo 980594 3310361 := bstep (se 2 (by rfl) ⟨1241385, by rfl⟩ : syracuseStep 3310361 = 2482771) B2482771
theorem B1246043 : Blo 980594 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B984063 : Blo 980594 984063 := bstep (se 1 (by rfl) ⟨738047, by rfl⟩ : syracuseStep 984063 = 1476095) B1476095
theorem B1475675 : Blo 980594 1475675 := bstep (se 1 (by rfl) ⟨1106756, by rfl⟩ : syracuseStep 1475675 = 2213513) B2213513
theorem B1475687 : Blo 980594 1475687 := bstep (se 1 (by rfl) ⟨1106765, by rfl⟩ : syracuseStep 1475687 = 2213531) B2213531
theorem B7668863 : Blo 980594 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B984295 : Blo 980594 984295 := bstep (se 1 (by rfl) ⟨738221, by rfl⟩ : syracuseStep 984295 = 1476443) B1476443
theorem B984479 : Blo 980594 984479 := bstep (se 1 (by rfl) ⟨738359, by rfl⟩ : syracuseStep 984479 = 1476719) B1476719
theorem B16778663 : Blo 980594 16778663 := bstep (se 1 (by rfl) ⟨12583997, by rfl⟩ : syracuseStep 16778663 = 25167995) B25167995
theorem B2492147 : Blo 980594 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B1476455 : Blo 980594 1476455 := bstep (se 1 (by rfl) ⟨1107341, by rfl⟩ : syracuseStep 1476455 = 2214683) B2214683
theorem B9439229 : Blo 980594 9439229 := bstep (se 3 (by rfl) ⟨1769855, by rfl⟩ : syracuseStep 9439229 = 3539711) B3539711
theorem B1050751 : Blo 980594 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B3311927 : Blo 980594 3311927 := bstep (se 1 (by rfl) ⟨2483945, by rfl⟩ : syracuseStep 3311927 = 4967891) B4967891
theorem B7178815 : Blo 980594 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B1576255 : Blo 980594 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B7081499 : Blo 980594 7081499 := bstep (se 1 (by rfl) ⟨5311124, by rfl⟩ : syracuseStep 7081499 = 10622249) B10622249
theorem B2658527 : Blo 980594 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B7082423 : Blo 980594 7082423 := bstep (se 1 (by rfl) ⟨5311817, by rfl⟩ : syracuseStep 7082423 = 10623635) B10623635
theorem B7475651 : Blo 980594 7475651 := bstep (se 1 (by rfl) ⟨5606738, by rfl⟩ : syracuseStep 7475651 = 11213477) B11213477
theorem B3314411 : Blo 980594 3314411 := bstep (se 1 (by rfl) ⟨2485808, by rfl⟩ : syracuseStep 3314411 = 4971617) B4971617
theorem B6722747 : Blo 980594 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B3315167 : Blo 980594 3315167 := bstep (se 1 (by rfl) ⟨2486375, by rfl⟩ : syracuseStep 3315167 = 4972751) B4972751
theorem B7673545 : Blo 980594 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B5315321 : Blo 980594 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B3316733 : Blo 980594 3316733 := bstep (se 3 (by rfl) ⟨621887, by rfl⟩ : syracuseStep 3316733 = 1243775) B1243775
theorem B5972879 : Blo 980594 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B6300665 : Blo 980594 6300665 := bstep (se 2 (by rfl) ⟨2362749, by rfl⟩ : syracuseStep 6300665 = 4725499) B4725499
theorem B544810063 : Blo 980594 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B4203859 : Blo 980594 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B3319487 : Blo 980594 3319487 := bstep (se 1 (by rfl) ⟨2489615, by rfl⟩ : syracuseStep 3319487 = 4979231) B4979231
theorem B11970271 : Blo 980594 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B47818619 : Blo 980594 47818619 := bstep (se 1 (by rfl) ⟨35863964, by rfl⟩ : syracuseStep 47818619 = 71727929) B71727929
theorem B6301739 : Blo 980594 6301739 := bstep (se 1 (by rfl) ⟨4726304, by rfl⟩ : syracuseStep 6301739 = 9452609) B9452609
theorem B2206439 : Blo 980594 2206439 := bstep (se 1 (by rfl) ⟨1654829, by rfl⟩ : syracuseStep 2206439 = 3309659) B3309659
theorem B6303071 : Blo 980594 6303071 := bstep (se 1 (by rfl) ⟨4727303, by rfl⟩ : syracuseStep 6303071 = 9454607) B9454607
theorem B22687127 : Blo 980594 22687127 := bstep (se 1 (by rfl) ⟨17015345, by rfl⟩ : syracuseStep 22687127 = 34030691) B34030691
theorem B2208239 : Blo 980594 2208239 := bstep (se 1 (by rfl) ⟨1656179, by rfl⟩ : syracuseStep 2208239 = 3312359) B3312359
theorem B349352747 : Blo 980594 349352747 := bstep (se 1 (by rfl) ⟨262014560, by rfl⟩ : syracuseStep 349352747 = 524029121) B524029121
theorem B2209193 : Blo 980594 2209193 := bstep (se 2 (by rfl) ⟨828447, by rfl⟩ : syracuseStep 2209193 = 1656895) B1656895
theorem B8959679 : Blo 980594 8959679 := bstep (se 1 (by rfl) ⟨6719759, by rfl⟩ : syracuseStep 8959679 = 13439519) B13439519
theorem B2799451 : Blo 980594 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B2209895 : Blo 980594 2209895 := bstep (se 1 (by rfl) ⟨1657421, by rfl⟩ : syracuseStep 2209895 = 3314843) B3314843
theorem B172111979 : Blo 980594 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B3192979 : Blo 980594 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B5585233 : Blo 980594 5585233 := bstep (se 2 (by rfl) ⟨2094462, by rfl⟩ : syracuseStep 5585233 = 4188925) B4188925
theorem B30227093 : Blo 980594 30227093 := bstep (se 6 (by rfl) ⟨708447, by rfl⟩ : syracuseStep 30227093 = 1416895) B1416895
theorem B6306761 : Blo 980594 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B6306943 : Blo 980594 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B48381245 : Blo 980594 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B11943413 : Blo 980594 11943413 := bstep (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) B1119695
theorem B7979401 : Blo 980594 7979401 := bstep (se 2 (by rfl) ⟨2992275, by rfl⟩ : syracuseStep 7979401 = 5984551) B5984551
theorem B18923975 : Blo 980594 18923975 := bstep (se 1 (by rfl) ⟨14192981, by rfl⟩ : syracuseStep 18923975 = 28385963) B28385963
theorem B2212559 : Blo 980594 2212559 := bstep (se 1 (by rfl) ⟨1659419, by rfl⟩ : syracuseStep 2212559 = 3318839) B3318839
theorem B12567595 : Blo 980594 12567595 := bstep (se 1 (by rfl) ⟨9425696, by rfl⟩ : syracuseStep 12567595 = 18851393) B18851393
theorem B14173379 : Blo 980594 14173379 := bstep (se 1 (by rfl) ⟨10630034, by rfl⟩ : syracuseStep 14173379 = 21260069) B21260069
theorem B16991453 : Blo 980594 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B20170271 : Blo 980594 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B1656463 : Blo 980594 1656463 := bstep (se 1 (by rfl) ⟨1242347, by rfl⟩ : syracuseStep 1656463 = 2484695) B2484695
theorem B4245803 : Blo 980594 4245803 := bstep (se 1 (by rfl) ⟨3184352, by rfl⟩ : syracuseStep 4245803 = 6368705) B6368705
theorem B102025601 : Blo 980594 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B5589881 : Blo 980594 5589881 := bstep (se 2 (by rfl) ⟨2096205, by rfl⟩ : syracuseStep 5589881 = 4192411) B4192411
theorem B10603655 : Blo 980594 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B1659305 : Blo 980594 1659305 := bstep (se 2 (by rfl) ⟨622239, by rfl⟩ : syracuseStep 1659305 = 1244479) B1244479
theorem B1659359 : Blo 980594 1659359 := bstep (se 1 (by rfl) ⟨1244519, by rfl⟩ : syracuseStep 1659359 = 2489039) B2489039
theorem B1660223 : Blo 980594 1660223 := bstep (se 1 (by rfl) ⟨1245167, by rfl⟩ : syracuseStep 1660223 = 2490335) B2490335
theorem B1103359 : Blo 980594 1103359 := bstep (se 1 (by rfl) ⟨827519, by rfl⟩ : syracuseStep 1103359 = 1655039) B1655039
theorem B1103899 : Blo 980594 1103899 := bstep (se 1 (by rfl) ⟨827924, by rfl⟩ : syracuseStep 1103899 = 1655849) B1655849
theorem B1103935 : Blo 980594 1103935 := bstep (se 1 (by rfl) ⟨827951, by rfl⟩ : syracuseStep 1103935 = 1655903) B1655903
theorem B10082515 : Blo 980594 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B12572927 : Blo 980594 12572927 := bstep (se 1 (by rfl) ⟨9429695, by rfl⟩ : syracuseStep 12572927 = 18859391) B18859391
theorem B4544923 : Blo 980594 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B3365327 : Blo 980594 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B17947813 : Blo 980594 17947813 := bstep (se 4 (by rfl) ⟨1682607, by rfl⟩ : syracuseStep 17947813 = 3365215) B3365215
theorem B3727241 : Blo 980594 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B1105915 : Blo 980594 1105915 := bstep (se 1 (by rfl) ⟨829436, by rfl⟩ : syracuseStep 1105915 = 1658873) B1658873
theorem B7463015 : Blo 980594 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B3727559 : Blo 980594 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B7070489 : Blo 980594 7070489 := bstep (se 2 (by rfl) ⟨2651433, by rfl⟩ : syracuseStep 7070489 = 5302867) B5302867
theorem B2483743 : Blo 980594 2483743 := bstep (se 1 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 2483743 = 3725615) B3725615
theorem B5597171 : Blo 980594 5597171 := bstep (se 1 (by rfl) ⟨4197878, by rfl⟩ : syracuseStep 5597171 = 8395757) B8395757
theorem B7956701 : Blo 980594 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B2486335 : Blo 980594 2486335 := bstep (se 1 (by rfl) ⟨1864751, by rfl⟩ : syracuseStep 2486335 = 3729503) B3729503
theorem B6287543 : Blo 980594 6287543 := bstep (se 1 (by rfl) ⟨4715657, by rfl⟩ : syracuseStep 6287543 = 9431315) B9431315
theorem B2486497 : Blo 980594 2486497 := bstep (se 2 (by rfl) ⟨932436, by rfl⟩ : syracuseStep 2486497 = 1864873) B1864873
theorem B1471031 : Blo 980594 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B5600087 : Blo 980594 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B1865207 : Blo 980594 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B3733073 : Blo 980594 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B1472105 : Blo 980594 1472105 := bstep (se 2 (by rfl) ⟨552039, by rfl⟩ : syracuseStep 1472105 = 1104079) B1104079
theorem B1472423 : Blo 980594 1472423 := bstep (se 1 (by rfl) ⟨1104317, by rfl⟩ : syracuseStep 1472423 = 2208635) B2208635
theorem B980927 : Blo 980594 980927 := bstep (se 1 (by rfl) ⟨735695, by rfl⟩ : syracuseStep 980927 = 1471391) B1471391
theorem B1472639 : Blo 980594 1472639 := bstep (se 1 (by rfl) ⟨1104479, by rfl⟩ : syracuseStep 1472639 = 2208959) B2208959
theorem B981215 : Blo 980594 981215 := bstep (se 1 (by rfl) ⟨735911, by rfl⟩ : syracuseStep 981215 = 1471823) B1471823
theorem B981247 : Blo 980594 981247 := bstep (se 1 (by rfl) ⟨735935, by rfl⟩ : syracuseStep 981247 = 1471871) B1471871
theorem B981375 : Blo 980594 981375 := bstep (se 1 (by rfl) ⟨736031, by rfl⟩ : syracuseStep 981375 = 1472063) B1472063
theorem B9435811 : Blo 980594 9435811 := bstep (se 1 (by rfl) ⟨7076858, by rfl⟩ : syracuseStep 9435811 = 14153717) B14153717
theorem B981695 : Blo 980594 981695 := bstep (se 1 (by rfl) ⟨736271, by rfl⟩ : syracuseStep 981695 = 1472543) B1472543
theorem B1473275 : Blo 980594 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B31914755 : Blo 980594 31914755 := bstep (se 1 (by rfl) ⟨23936066, by rfl⟩ : syracuseStep 31914755 = 47872133) B47872133
theorem B1473311 : Blo 980594 1473311 := bstep (se 1 (by rfl) ⟨1104983, by rfl⟩ : syracuseStep 1473311 = 2209967) B2209967
theorem B1473401 : Blo 980594 1473401 := bstep (se 2 (by rfl) ⟨552525, by rfl⟩ : syracuseStep 1473401 = 1105051) B1105051
theorem B1473449 : Blo 980594 1473449 := bstep (se 2 (by rfl) ⟨552543, by rfl⟩ : syracuseStep 1473449 = 1105087) B1105087
theorem B982127 : Blo 980594 982127 := bstep (se 1 (by rfl) ⟨736595, by rfl⟩ : syracuseStep 982127 = 1473191) B1473191
theorem B1473863 : Blo 980594 1473863 := bstep (se 1 (by rfl) ⟨1105397, by rfl⟩ : syracuseStep 1473863 = 2210795) B2210795
theorem B3735017 : Blo 980594 3735017 := bstep (se 2 (by rfl) ⟨1400631, by rfl⟩ : syracuseStep 3735017 = 2801263) B2801263
theorem B983067 : Blo 980594 983067 := bstep (se 1 (by rfl) ⟨737300, by rfl⟩ : syracuseStep 983067 = 1474601) B1474601
theorem B983087 : Blo 980594 983087 := bstep (se 1 (by rfl) ⟨737315, by rfl⟩ : syracuseStep 983087 = 1474631) B1474631
theorem B983199 : Blo 980594 983199 := bstep (se 1 (by rfl) ⟨737399, by rfl⟩ : syracuseStep 983199 = 1474799) B1474799
theorem B12615983 : Blo 980594 12615983 := bstep (se 1 (by rfl) ⟨9461987, by rfl⟩ : syracuseStep 12615983 = 18923975) B18923975
theorem B1475039 : Blo 980594 1475039 := bstep (se 1 (by rfl) ⟨1106279, by rfl⟩ : syracuseStep 1475039 = 2212559) B2212559
theorem B5604005 : Blo 980594 5604005 := bstep (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) B1050751
theorem B983783 : Blo 980594 983783 := bstep (se 1 (by rfl) ⟨737837, by rfl⟩ : syracuseStep 983783 = 1475675) B1475675
theorem B5112575 : Blo 980594 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B984303 : Blo 980594 984303 := bstep (se 1 (by rfl) ⟨738227, by rfl⟩ : syracuseStep 984303 = 1476455) B1476455
theorem B6292819 : Blo 980594 6292819 := bstep (se 1 (by rfl) ⟨4719614, by rfl⟩ : syracuseStep 6292819 = 9439229) B9439229
theorem B983791 : Blo 980594 983791 := bstep (se 1 (by rfl) ⟨737843, by rfl⟩ : syracuseStep 983791 = 1475687) B1475687
theorem B5605145 : Blo 980594 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B3311657 : Blo 980594 3311657 := bstep (se 2 (by rfl) ⟨1241871, by rfl⟩ : syracuseStep 3311657 = 2483743) B2483743
theorem B15960361 : Blo 980594 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B4720999 : Blo 980594 4720999 := bstep (se 1 (by rfl) ⟨3540749, by rfl⟩ : syracuseStep 4720999 = 7081499) B7081499
theorem B1772351 : Blo 980594 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B4721615 : Blo 980594 4721615 := bstep (se 1 (by rfl) ⟨3541211, by rfl⟩ : syracuseStep 4721615 = 7082423) B7082423
theorem B4983767 : Blo 980594 4983767 := bstep (se 1 (by rfl) ⟨3737825, by rfl⟩ : syracuseStep 4983767 = 7475651) B7475651
theorem B9571753 : Blo 980594 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B2101673 : Blo 980594 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B3315113 : Blo 980594 3315113 := bstep (se 2 (by rfl) ⟨1243167, by rfl⟩ : syracuseStep 3315113 = 2486335) B2486335
theorem B3315329 : Blo 980594 3315329 := bstep (se 2 (by rfl) ⟨1243248, by rfl⟩ : syracuseStep 3315329 = 2486497) B2486497
theorem B4200443 : Blo 980594 4200443 := bstep (se 1 (by rfl) ⟨3150332, by rfl⟩ : syracuseStep 4200443 = 6300665) B6300665
theorem B4201159 : Blo 980594 4201159 := bstep (se 1 (by rfl) ⟨3150869, by rfl⟩ : syracuseStep 4201159 = 6301739) B6301739
theorem B4202047 : Blo 980594 4202047 := bstep (se 1 (by rfl) ⟨3151535, by rfl⟩ : syracuseStep 4202047 = 6303071) B6303071
theorem B10231393 : Blo 980594 10231393 := bstep (se 2 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 10231393 = 7673545) B7673545
theorem B16818029 : Blo 980594 16818029 := bstep (se 3 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 16818029 = 6306761) B6306761
theorem B13443353 : Blo 980594 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B7446977 : Blo 980594 7446977 := bstep (se 2 (by rfl) ⟨2792616, by rfl⟩ : syracuseStep 7446977 = 5585233) B5585233
theorem B5973119 : Blo 980594 5973119 := bstep (se 1 (by rfl) ⟨4479839, by rfl⟩ : syracuseStep 5973119 = 8959679) B8959679
theorem B23930417 : Blo 980594 23930417 := bstep (se 2 (by rfl) ⟨8973906, by rfl⟩ : syracuseStep 23930417 = 17947813) B17947813
theorem B21276503 : Blo 980594 21276503 := bstep (se 1 (by rfl) ⟨15957377, by rfl⟩ : syracuseStep 21276503 = 31914755) B31914755
theorem B32254163 : Blo 980594 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B2206907 : Blo 980594 2206907 := bstep (se 1 (by rfl) ⟨1655180, by rfl⟩ : syracuseStep 2206907 = 3310361) B3310361
theorem B9448919 : Blo 980594 9448919 := bstep (se 1 (by rfl) ⟨7086689, by rfl⟩ : syracuseStep 9448919 = 14173379) B14173379
theorem B11185775 : Blo 980594 11185775 := bstep (se 1 (by rfl) ⟨8389331, by rfl⟩ : syracuseStep 11185775 = 16778663) B16778663
theorem B13446847 : Blo 980594 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B16756793 : Blo 980594 16756793 := bstep (se 2 (by rfl) ⟨6283797, by rfl⟩ : syracuseStep 16756793 = 12567595) B12567595
theorem B726413417 : Blo 980594 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B2830535 : Blo 980594 2830535 := bstep (se 1 (by rfl) ⟨2122901, by rfl⟩ : syracuseStep 2830535 = 4245803) B4245803
theorem B2207951 : Blo 980594 2207951 := bstep (se 1 (by rfl) ⟨1655963, by rfl⟩ : syracuseStep 2207951 = 3311927) B3311927
theorem B2208617 : Blo 980594 2208617 := bstep (se 2 (by rfl) ⟨828231, by rfl⟩ : syracuseStep 2208617 = 1656463) B1656463
theorem B3322781 : Blo 980594 3322781 := bstep (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) B1246043
theorem B2209607 : Blo 980594 2209607 := bstep (se 1 (by rfl) ⟨1657205, by rfl⟩ : syracuseStep 2209607 = 3314411) B3314411
theorem B2210111 : Blo 980594 2210111 := bstep (se 1 (by rfl) ⟨1657583, by rfl⟩ : syracuseStep 2210111 = 3315167) B3315167
theorem B2243551 : Blo 980594 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B2211155 : Blo 980594 2211155 := bstep (se 1 (by rfl) ⟨1658366, by rfl⟩ : syracuseStep 2211155 = 3316733) B3316733
theorem B458965277 : Blo 980594 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B3981919 : Blo 980594 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B2212991 : Blo 980594 2212991 := bstep (se 1 (by rfl) ⟨1659743, by rfl⟩ : syracuseStep 2212991 = 3319487) B3319487
theorem B14174189 : Blo 980594 14174189 := bstep (se 3 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 14174189 = 5315321) B5315321
theorem B15124751 : Blo 980594 15124751 := bstep (se 1 (by rfl) ⟨11343563, by rfl⟩ : syracuseStep 15124751 = 22687127) B22687127
theorem B232901831 : Blo 980594 232901831 := bstep (se 1 (by rfl) ⟨174676373, by rfl⟩ : syracuseStep 232901831 = 349352747) B349352747
theorem B8409257 : Blo 980594 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B1660655 : Blo 980594 1660655 := bstep (se 1 (by rfl) ⟨1245491, by rfl⟩ : syracuseStep 1660655 = 2490983) B2490983
theorem B10639201 : Blo 980594 10639201 := bstep (se 2 (by rfl) ⟨3989700, by rfl⟩ : syracuseStep 10639201 = 7979401) B7979401
theorem B11327635 : Blo 980594 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B1661431 : Blo 980594 1661431 := bstep (se 1 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 1661431 = 2492147) B2492147
theorem B68017067 : Blo 980594 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B3726587 : Blo 980594 3726587 := bstep (se 1 (by rfl) ⟨2794940, by rfl⟩ : syracuseStep 3726587 = 5589881) B5589881
theorem B7069103 : Blo 980594 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B1106203 : Blo 980594 1106203 := bstep (se 1 (by rfl) ⟨829652, by rfl⟩ : syracuseStep 1106203 = 1659305) B1659305
theorem B1106239 : Blo 980594 1106239 := bstep (se 1 (by rfl) ⟨829679, by rfl⟩ : syracuseStep 1106239 = 1659359) B1659359
theorem B4481831 : Blo 980594 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B1106815 : Blo 980594 1106815 := bstep (se 1 (by rfl) ⟨830111, by rfl⟩ : syracuseStep 1106815 = 1660223) B1660223
theorem B4973885 : Blo 980594 4973885 := bstep (se 3 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 4973885 = 1865207) B1865207
theorem B8381951 : Blo 980594 8381951 := bstep (se 1 (by rfl) ⟨6286463, by rfl⟩ : syracuseStep 8381951 = 12572927) B12572927
theorem B2484827 : Blo 980594 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B4975343 : Blo 980594 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B2485039 : Blo 980594 2485039 := bstep (se 1 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 2485039 = 3727559) B3727559
theorem B4713659 : Blo 980594 4713659 := bstep (se 1 (by rfl) ⟨3535244, by rfl⟩ : syracuseStep 4713659 = 7070489) B7070489
theorem B31879079 : Blo 980594 31879079 := bstep (se 1 (by rfl) ⟨23909309, by rfl⟩ : syracuseStep 31879079 = 47818619) B47818619
theorem B3731447 : Blo 980594 3731447 := bstep (se 1 (by rfl) ⟨2798585, by rfl⟩ : syracuseStep 3731447 = 5597171) B5597171
theorem B5304467 : Blo 980594 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B1470959 : Blo 980594 1470959 := bstep (se 1 (by rfl) ⟨1103219, by rfl⟩ : syracuseStep 1470959 = 2206439) B2206439
theorem B1471145 : Blo 980594 1471145 := bstep (se 2 (by rfl) ⟨551679, by rfl⟩ : syracuseStep 1471145 = 1103359) B1103359
theorem B3732601 : Blo 980594 3732601 := bstep (se 2 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 3732601 = 2799451) B2799451
theorem B1471865 : Blo 980594 1471865 := bstep (se 2 (by rfl) ⟨551949, by rfl⟩ : syracuseStep 1471865 = 1103899) B1103899
theorem B1471913 : Blo 980594 1471913 := bstep (se 2 (by rfl) ⟨551967, by rfl⟩ : syracuseStep 1471913 = 1103935) B1103935
theorem B4191695 : Blo 980594 4191695 := bstep (se 1 (by rfl) ⟨3143771, by rfl⟩ : syracuseStep 4191695 = 6287543) B6287543
theorem B4257305 : Blo 980594 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B1472159 : Blo 980594 1472159 := bstep (se 1 (by rfl) ⟨1104119, by rfl⟩ : syracuseStep 1472159 = 2208239) B2208239
theorem B980687 : Blo 980594 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B6059897 : Blo 980594 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B3733391 : Blo 980594 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B12581081 : Blo 980594 12581081 := bstep (se 2 (by rfl) ⟨4717905, by rfl⟩ : syracuseStep 12581081 = 9435811) B9435811
theorem B1472795 : Blo 980594 1472795 := bstep (se 1 (by rfl) ⟨1104596, by rfl⟩ : syracuseStep 1472795 = 2209193) B2209193
theorem B2488715 : Blo 980594 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B981403 : Blo 980594 981403 := bstep (se 1 (by rfl) ⟨736052, by rfl⟩ : syracuseStep 981403 = 1472105) B1472105
theorem B981615 : Blo 980594 981615 := bstep (se 1 (by rfl) ⟨736211, by rfl⟩ : syracuseStep 981615 = 1472423) B1472423
theorem B1473263 : Blo 980594 1473263 := bstep (se 1 (by rfl) ⟨1104947, by rfl⟩ : syracuseStep 1473263 = 2209895) B2209895
theorem B981759 : Blo 980594 981759 := bstep (se 1 (by rfl) ⟨736319, by rfl⟩ : syracuseStep 981759 = 1472639) B1472639
theorem B20151395 : Blo 980594 20151395 := bstep (se 1 (by rfl) ⟨15113546, by rfl⟩ : syracuseStep 20151395 = 30227093) B30227093
theorem B982183 : Blo 980594 982183 := bstep (se 1 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 982183 = 1473275) B1473275
theorem B982207 : Blo 980594 982207 := bstep (se 1 (by rfl) ⟨736655, by rfl⟩ : syracuseStep 982207 = 1473311) B1473311
theorem B982267 : Blo 980594 982267 := bstep (se 1 (by rfl) ⟨736700, by rfl⟩ : syracuseStep 982267 = 1473401) B1473401
theorem B982299 : Blo 980594 982299 := bstep (se 1 (by rfl) ⟨736724, by rfl⟩ : syracuseStep 982299 = 1473449) B1473449
theorem B982575 : Blo 980594 982575 := bstep (se 1 (by rfl) ⟨736931, by rfl⟩ : syracuseStep 982575 = 1473863) B1473863
theorem B2490011 : Blo 980594 2490011 := bstep (se 1 (by rfl) ⟨1867508, by rfl⟩ : syracuseStep 2490011 = 3735017) B3735017
theorem B7962275 : Blo 980594 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B1474553 : Blo 980594 1474553 := bstep (se 2 (by rfl) ⟨552957, by rfl⟩ : syracuseStep 1474553 = 1105915) B1105915
theorem B983359 : Blo 980594 983359 := bstep (se 1 (by rfl) ⟨737519, by rfl⟩ : syracuseStep 983359 = 1475039) B1475039
theorem B1474937 : Blo 980594 1474937 := bstep (se 2 (by rfl) ⟨553101, by rfl⟩ : syracuseStep 1474937 = 1106203) B1106203
theorem B1474985 : Blo 980594 1474985 := bstep (se 2 (by rfl) ⟨553119, by rfl⟩ : syracuseStep 1474985 = 1106239) B1106239
theorem B3736003 : Blo 980594 3736003 := bstep (se 1 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 3736003 = 5604005) B5604005
theorem B3408383 : Blo 980594 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B1475327 : Blo 980594 1475327 := bstep (se 1 (by rfl) ⟨1106495, by rfl⟩ : syracuseStep 1475327 = 2212991) B2212991
theorem B5309225 : Blo 980594 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B5604461 : Blo 980594 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B1475753 : Blo 980594 1475753 := bstep (se 2 (by rfl) ⟨553407, by rfl⟩ : syracuseStep 1475753 = 1106815) B1106815
theorem B3736763 : Blo 980594 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B8390425 : Blo 980594 8390425 := bstep (se 2 (by rfl) ⟨3146409, by rfl⟩ : syracuseStep 8390425 = 6292819) B6292819
theorem B1181567 : Blo 980594 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B3147743 : Blo 980594 3147743 := bstep (se 1 (by rfl) ⟨2360807, by rfl⟩ : syracuseStep 3147743 = 4721615) B4721615
theorem B5606171 : Blo 980594 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B6294665 : Blo 980594 6294665 := bstep (se 2 (by rfl) ⟨2360499, by rfl⟩ : syracuseStep 6294665 = 4720999) B4720999
theorem B3313385 : Blo 980594 3313385 := bstep (se 2 (by rfl) ⟨1242519, by rfl⟩ : syracuseStep 3313385 = 2485039) B2485039
theorem B17929129 : Blo 980594 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B11212019 : Blo 980594 11212019 := bstep (se 1 (by rfl) ⟨8409014, by rfl⟩ : syracuseStep 11212019 = 16818029) B16818029
theorem B2987887 : Blo 980594 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B3315923 : Blo 980594 3315923 := bstep (se 1 (by rfl) ⟨2486942, by rfl⟩ : syracuseStep 3315923 = 4973885) B4973885
theorem B21502775 : Blo 980594 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B3316895 : Blo 980594 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B6299279 : Blo 980594 6299279 := bstep (se 1 (by rfl) ⟨4724459, by rfl⟩ : syracuseStep 6299279 = 9448919) B9448919
theorem B2794463 : Blo 980594 2794463 := bstep (se 1 (by rfl) ⟨2095847, by rfl⟩ : syracuseStep 2794463 = 4191695) B4191695
theorem B4039931 : Blo 980594 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B2991401 : Blo 980594 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B13641857 : Blo 980594 13641857 := bstep (se 2 (by rfl) ⟨5115696, by rfl⟩ : syracuseStep 13641857 = 10231393) B10231393
theorem B9449459 : Blo 980594 9449459 := bstep (se 1 (by rfl) ⟨7087094, by rfl⟩ : syracuseStep 9449459 = 14174189) B14174189
theorem B2207771 : Blo 980594 2207771 := bstep (se 1 (by rfl) ⟨1655828, by rfl⟩ : syracuseStep 2207771 = 3311657) B3311657
theorem B3322511 : Blo 980594 3322511 := bstep (se 1 (by rfl) ⟨2491883, by rfl⟩ : syracuseStep 3322511 = 4983767) B4983767
theorem B155267887 : Blo 980594 155267887 := bstep (se 1 (by rfl) ⟨116450915, by rfl⟩ : syracuseStep 155267887 = 232901831) B232901831
theorem B21280481 : Blo 980594 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B2210075 : Blo 980594 2210075 := bstep (se 1 (by rfl) ⟨1657556, by rfl⟩ : syracuseStep 2210075 = 3315113) B3315113
theorem B2210219 : Blo 980594 2210219 := bstep (se 1 (by rfl) ⟨1657664, by rfl⟩ : syracuseStep 2210219 = 3315329) B3315329
theorem B2800295 : Blo 980594 2800295 := bstep (se 1 (by rfl) ⟨2100221, by rfl⟩ : syracuseStep 2800295 = 4200443) B4200443
theorem B8962235 : Blo 980594 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B4964651 : Blo 980594 4964651 := bstep (se 1 (by rfl) ⟨3723488, by rfl⟩ : syracuseStep 4964651 = 7446977) B7446977
theorem B3982079 : Blo 980594 3982079 := bstep (se 1 (by rfl) ⟨2986559, by rfl⟩ : syracuseStep 3982079 = 5973119) B5973119
theorem B5587967 : Blo 980594 5587967 := bstep (se 1 (by rfl) ⟨4190975, by rfl⟩ : syracuseStep 5587967 = 8381951) B8381951
theorem B1656551 : Blo 980594 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B7457183 : Blo 980594 7457183 := bstep (se 1 (by rfl) ⟨5592887, by rfl⟩ : syracuseStep 7457183 = 11185775) B11185775
theorem B21252719 : Blo 980594 21252719 := bstep (se 1 (by rfl) ⟨15939539, by rfl⟩ : syracuseStep 21252719 = 31879079) B31879079
theorem B1887023 : Blo 980594 1887023 := bstep (se 1 (by rfl) ⟨1415267, by rfl⟩ : syracuseStep 1887023 = 2830535) B2830535
theorem B2215187 : Blo 980594 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B2215241 : Blo 980594 2215241 := bstep (se 2 (by rfl) ⟨830715, by rfl⟩ : syracuseStep 2215241 = 1661431) B1661431
theorem B2838203 : Blo 980594 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B1659143 : Blo 980594 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B1660007 : Blo 980594 1660007 := bstep (se 1 (by rfl) ⟨1245005, by rfl⟩ : syracuseStep 1660007 = 2490011) B2490011
theorem B305976851 : Blo 980594 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B8410655 : Blo 980594 8410655 := bstep (se 1 (by rfl) ⟨6307991, by rfl⟩ : syracuseStep 8410655 = 12615983) B12615983
theorem B10083167 : Blo 980594 10083167 := bstep (se 1 (by rfl) ⟨7562375, by rfl⟩ : syracuseStep 10083167 = 15124751) B15124751
theorem B1107103 : Blo 980594 1107103 := bstep (se 1 (by rfl) ⟨830327, by rfl⟩ : syracuseStep 1107103 = 1660655) B1660655
theorem B45344711 : Blo 980594 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B2484391 : Blo 980594 2484391 := bstep (se 1 (by rfl) ⟨1863293, by rfl⟩ : syracuseStep 2484391 = 3726587) B3726587
theorem B4712735 : Blo 980594 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B15953611 : Blo 980594 15953611 := bstep (se 1 (by rfl) ⟨11965208, by rfl⟩ : syracuseStep 15953611 = 23930417) B23930417
theorem B14184335 : Blo 980594 14184335 := bstep (se 1 (by rfl) ⟨10638251, by rfl⟩ : syracuseStep 14184335 = 21276503) B21276503
theorem B4976801 : Blo 980594 4976801 := bstep (se 2 (by rfl) ⟨1866300, by rfl⟩ : syracuseStep 4976801 = 3732601) B3732601
theorem B1471271 : Blo 980594 1471271 := bstep (se 1 (by rfl) ⟨1103453, by rfl⟩ : syracuseStep 1471271 = 2206907) B2206907
theorem B3142439 : Blo 980594 3142439 := bstep (se 1 (by rfl) ⟨2356829, by rfl⟩ : syracuseStep 3142439 = 4713659) B4713659
theorem B51049349 : Blo 980594 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B14185601 : Blo 980594 14185601 := bstep (se 2 (by rfl) ⟨5319600, by rfl⟩ : syracuseStep 14185601 = 10639201) B10639201
theorem B2487631 : Blo 980594 2487631 := bstep (se 1 (by rfl) ⟨1865723, by rfl⟩ : syracuseStep 2487631 = 3731447) B3731447
theorem B11171195 : Blo 980594 11171195 := bstep (se 1 (by rfl) ⟨8378396, by rfl⟩ : syracuseStep 11171195 = 16756793) B16756793
theorem B484275611 : Blo 980594 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B3536311 : Blo 980594 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B1471967 : Blo 980594 1471967 := bstep (se 1 (by rfl) ⟨1103975, by rfl⟩ : syracuseStep 1471967 = 2207951) B2207951
theorem B15103513 : Blo 980594 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B980639 : Blo 980594 980639 := bstep (se 1 (by rfl) ⟨735479, by rfl⟩ : syracuseStep 980639 = 1470959) B1470959
theorem B980763 : Blo 980594 980763 := bstep (se 1 (by rfl) ⟨735572, by rfl⟩ : syracuseStep 980763 = 1471145) B1471145
theorem B1472411 : Blo 980594 1472411 := bstep (se 1 (by rfl) ⟨1104308, by rfl⟩ : syracuseStep 1472411 = 2208617) B2208617
theorem B981243 : Blo 980594 981243 := bstep (se 1 (by rfl) ⟨735932, by rfl⟩ : syracuseStep 981243 = 1471865) B1471865
theorem B5601545 : Blo 980594 5601545 := bstep (se 2 (by rfl) ⟨2100579, by rfl⟩ : syracuseStep 5601545 = 4201159) B4201159
theorem B981275 : Blo 980594 981275 := bstep (se 1 (by rfl) ⟨735956, by rfl⟩ : syracuseStep 981275 = 1471913) B1471913
theorem B981439 : Blo 980594 981439 := bstep (se 1 (by rfl) ⟨736079, by rfl⟩ : syracuseStep 981439 = 1472159) B1472159
theorem B1473071 : Blo 980594 1473071 := bstep (se 1 (by rfl) ⟨1104803, by rfl⟩ : syracuseStep 1473071 = 2209607) B2209607
theorem B2488927 : Blo 980594 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B8387387 : Blo 980594 8387387 := bstep (se 1 (by rfl) ⟨6290540, by rfl⟩ : syracuseStep 8387387 = 12581081) B12581081
theorem B981863 : Blo 980594 981863 := bstep (se 1 (by rfl) ⟨736397, by rfl⟩ : syracuseStep 981863 = 1472795) B1472795
theorem B1473407 : Blo 980594 1473407 := bstep (se 1 (by rfl) ⟨1105055, by rfl⟩ : syracuseStep 1473407 = 2210111) B2210111
theorem B982175 : Blo 980594 982175 := bstep (se 1 (by rfl) ⟨736631, by rfl⟩ : syracuseStep 982175 = 1473263) B1473263
theorem B13434263 : Blo 980594 13434263 := bstep (se 1 (by rfl) ⟨10075697, by rfl⟩ : syracuseStep 13434263 = 20151395) B20151395
theorem B5602729 : Blo 980594 5602729 := bstep (se 2 (by rfl) ⟨2101023, by rfl⟩ : syracuseStep 5602729 = 4202047) B4202047
theorem B1474103 : Blo 980594 1474103 := bstep (se 1 (by rfl) ⟨1105577, by rfl⟩ : syracuseStep 1474103 = 2211155) B2211155
theorem B5308183 : Blo 980594 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B983035 : Blo 980594 983035 := bstep (se 1 (by rfl) ⟨737276, by rfl⟩ : syracuseStep 983035 = 1474553) B1474553
theorem B3309767 : Blo 980594 3309767 := bstep (se 1 (by rfl) ⟨2482325, by rfl⟩ : syracuseStep 3309767 = 4964651) B4964651
theorem B983291 : Blo 980594 983291 := bstep (se 1 (by rfl) ⟨737468, by rfl⟩ : syracuseStep 983291 = 1474937) B1474937
theorem B983323 : Blo 980594 983323 := bstep (se 1 (by rfl) ⟨737492, by rfl⟩ : syracuseStep 983323 = 1474985) B1474985
theorem B983551 : Blo 980594 983551 := bstep (se 1 (by rfl) ⟨737663, by rfl⟩ : syracuseStep 983551 = 1475327) B1475327
theorem B3539483 : Blo 980594 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B4981337 : Blo 980594 4981337 := bstep (se 2 (by rfl) ⟨1868001, by rfl⟩ : syracuseStep 4981337 = 3736003) B3736003
theorem B3736307 : Blo 980594 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B983835 : Blo 980594 983835 := bstep (se 1 (by rfl) ⟨737876, by rfl⟩ : syracuseStep 983835 = 1475753) B1475753
theorem B2491175 : Blo 980594 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B2098495 : Blo 980594 2098495 := bstep (se 1 (by rfl) ⟨1573871, by rfl⟩ : syracuseStep 2098495 = 3147743) B3147743
theorem B1476137 : Blo 980594 1476137 := bstep (se 2 (by rfl) ⟨553551, by rfl⟩ : syracuseStep 1476137 = 1107103) B1107103
theorem B3737447 : Blo 980594 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B10618877 : Blo 980594 10618877 := bstep (se 3 (by rfl) ⟨1991039, by rfl⟩ : syracuseStep 10618877 = 3982079) B3982079
theorem B4196443 : Blo 980594 4196443 := bstep (se 1 (by rfl) ⟨3147332, by rfl⟩ : syracuseStep 4196443 = 6294665) B6294665
theorem B1476791 : Blo 980594 1476791 := bstep (se 1 (by rfl) ⟨1107593, by rfl⟩ : syracuseStep 1476791 = 2215187) B2215187
theorem B1476827 : Blo 980594 1476827 := bstep (se 1 (by rfl) ⟨1107620, by rfl⟩ : syracuseStep 1476827 = 2215241) B2215241
theorem B3312521 : Blo 980594 3312521 := bstep (se 2 (by rfl) ⟨1242195, by rfl⟩ : syracuseStep 3312521 = 2484391) B2484391
theorem B7474679 : Blo 980594 7474679 := bstep (se 1 (by rfl) ⟨5606009, by rfl⟩ : syracuseStep 7474679 = 11212019) B11212019
theorem B203984567 : Blo 980594 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B5607103 : Blo 980594 5607103 := bstep (se 1 (by rfl) ⟨4205327, by rfl⟩ : syracuseStep 5607103 = 8410655) B8410655
theorem B6722111 : Blo 980594 6722111 := bstep (se 1 (by rfl) ⟨5041583, by rfl⟩ : syracuseStep 6722111 = 10083167) B10083167
theorem B21271481 : Blo 980594 21271481 := bstep (se 2 (by rfl) ⟨7976805, by rfl⟩ : syracuseStep 21271481 = 15953611) B15953611
theorem B3150845 : Blo 980594 3150845 := bstep (se 3 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 3150845 = 1181567) B1181567
theorem B4199519 : Blo 980594 4199519 := bstep (se 1 (by rfl) ⟨3149639, by rfl⟩ : syracuseStep 4199519 = 6299279) B6299279
theorem B2693287 : Blo 980594 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B3316841 : Blo 980594 3316841 := bstep (se 2 (by rfl) ⟨1243815, by rfl⟩ : syracuseStep 3316841 = 2487631) B2487631
theorem B6299639 : Blo 980594 6299639 := bstep (se 1 (by rfl) ⟨4724729, by rfl⟩ : syracuseStep 6299639 = 9449459) B9449459
theorem B3317867 : Blo 980594 3317867 := bstep (se 1 (by rfl) ⟨2488400, by rfl⟩ : syracuseStep 3317867 = 4976801) B4976801
theorem B3318569 : Blo 980594 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B7447463 : Blo 980594 7447463 := bstep (se 1 (by rfl) ⟨5585597, by rfl⟩ : syracuseStep 7447463 = 11171195) B11171195
theorem B8956175 : Blo 980594 8956175 := bstep (se 1 (by rfl) ⟨6717131, by rfl⟩ : syracuseStep 8956175 = 13434263) B13434263
theorem B5974823 : Blo 980594 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B2272255 : Blo 980594 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B14168479 : Blo 980594 14168479 := bstep (se 1 (by rfl) ⟨10626359, by rfl⟩ : syracuseStep 14168479 = 21252719) B21252719
theorem B1258015 : Blo 980594 1258015 := bstep (se 1 (by rfl) ⟨943511, by rfl⟩ : syracuseStep 1258015 = 1887023) B1887023
theorem B11187233 : Blo 980594 11187233 := bstep (se 2 (by rfl) ⟨4195212, by rfl⟩ : syracuseStep 11187233 = 8390425) B8390425
theorem B2208923 : Blo 980594 2208923 := bstep (se 1 (by rfl) ⟨1656692, by rfl⟩ : syracuseStep 2208923 = 3313385) B3313385
theorem B2210615 : Blo 980594 2210615 := bstep (se 1 (by rfl) ⟨1657961, by rfl⟩ : syracuseStep 2210615 = 3315923) B3315923
theorem B14335183 : Blo 980594 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B2211263 : Blo 980594 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B23905505 : Blo 980594 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B30229807 : Blo 980594 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B9094571 : Blo 980594 9094571 := bstep (se 1 (by rfl) ⟨6820928, by rfl⟩ : syracuseStep 9094571 = 13641857) B13641857
theorem B20138017 : Blo 980594 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B3983849 : Blo 980594 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B9456223 : Blo 980594 9456223 := bstep (se 1 (by rfl) ⟨7092167, by rfl⟩ : syracuseStep 9456223 = 14184335) B14184335
theorem B2215007 : Blo 980594 2215007 := bstep (se 1 (by rfl) ⟨1661255, by rfl⟩ : syracuseStep 2215007 = 3322511) B3322511
theorem B34032899 : Blo 980594 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B9457067 : Blo 980594 9457067 := bstep (se 1 (by rfl) ⟨7092800, by rfl⟩ : syracuseStep 9457067 = 14185601) B14185601
theorem B322850407 : Blo 980594 322850407 := bstep (se 1 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 322850407 = 484275611) B484275611
theorem B5591591 : Blo 980594 5591591 := bstep (se 1 (by rfl) ⟨4193693, by rfl⟩ : syracuseStep 5591591 = 8387387) B8387387
theorem B3725311 : Blo 980594 3725311 := bstep (se 1 (by rfl) ⟨2793983, by rfl⟩ : syracuseStep 3725311 = 5587967) B5587967
theorem B1104367 : Blo 980594 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B4971455 : Blo 980594 4971455 := bstep (se 1 (by rfl) ⟨3728591, by rfl⟩ : syracuseStep 4971455 = 7457183) B7457183
theorem B1892135 : Blo 980594 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B1106095 : Blo 980594 1106095 := bstep (se 1 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 1106095 = 1659143) B1659143
theorem B1106671 : Blo 980594 1106671 := bstep (se 1 (by rfl) ⟨830003, by rfl⟩ : syracuseStep 1106671 = 1660007) B1660007
theorem B1862975 : Blo 980594 1862975 := bstep (se 1 (by rfl) ⟨1397231, by rfl⟩ : syracuseStep 1862975 = 2794463) B2794463
theorem B1994267 : Blo 980594 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B207023849 : Blo 980594 207023849 := bstep (se 2 (by rfl) ⟨77633943, by rfl⟩ : syracuseStep 207023849 = 155267887) B155267887
theorem B3141823 : Blo 980594 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B4715081 : Blo 980594 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B1471847 : Blo 980594 1471847 := bstep (se 1 (by rfl) ⟨1103885, by rfl⟩ : syracuseStep 1471847 = 2207771) B2207771
theorem B980847 : Blo 980594 980847 := bstep (se 1 (by rfl) ⟨735635, by rfl⟩ : syracuseStep 980847 = 1471271) B1471271
theorem B2094959 : Blo 980594 2094959 := bstep (se 1 (by rfl) ⟨1571219, by rfl⟩ : syracuseStep 2094959 = 3142439) B3142439
theorem B981311 : Blo 980594 981311 := bstep (se 1 (by rfl) ⟨735983, by rfl⟩ : syracuseStep 981311 = 1471967) B1471967
theorem B14186987 : Blo 980594 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B981607 : Blo 980594 981607 := bstep (se 1 (by rfl) ⟨736205, by rfl⟩ : syracuseStep 981607 = 1472411) B1472411
theorem B3734363 : Blo 980594 3734363 := bstep (se 1 (by rfl) ⟨2800772, by rfl⟩ : syracuseStep 3734363 = 5601545) B5601545
theorem B1473383 : Blo 980594 1473383 := bstep (se 1 (by rfl) ⟨1105037, by rfl⟩ : syracuseStep 1473383 = 2210075) B2210075
theorem B1473479 : Blo 980594 1473479 := bstep (se 1 (by rfl) ⟨1105109, by rfl⟩ : syracuseStep 1473479 = 2210219) B2210219
theorem B982047 : Blo 980594 982047 := bstep (se 1 (by rfl) ⟨736535, by rfl⟩ : syracuseStep 982047 = 1473071) B1473071
theorem B1866863 : Blo 980594 1866863 := bstep (se 1 (by rfl) ⟨1400147, by rfl⟩ : syracuseStep 1866863 = 2800295) B2800295
theorem B7470305 : Blo 980594 7470305 := bstep (se 2 (by rfl) ⟨2801364, by rfl⟩ : syracuseStep 7470305 = 5602729) B5602729
theorem B982271 : Blo 980594 982271 := bstep (se 1 (by rfl) ⟨736703, by rfl⟩ : syracuseStep 982271 = 1473407) B1473407
theorem B7077577 : Blo 980594 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B982735 : Blo 980594 982735 := bstep (se 1 (by rfl) ⟨737051, by rfl⟩ : syracuseStep 982735 = 1474103) B1474103
theorem B1474793 : Blo 980594 1474793 := bstep (se 2 (by rfl) ⟨553047, by rfl⟩ : syracuseStep 1474793 = 1106095) B1106095
theorem B2359655 : Blo 980594 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B2490871 : Blo 980594 2490871 := bstep (se 1 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 2490871 = 3736307) B3736307
theorem B6063047 : Blo 980594 6063047 := bstep (se 1 (by rfl) ⟨4547285, by rfl⟩ : syracuseStep 6063047 = 9094571) B9094571
theorem B1475561 : Blo 980594 1475561 := bstep (se 2 (by rfl) ⟨553335, by rfl⟩ : syracuseStep 1475561 = 1106671) B1106671
theorem B984091 : Blo 980594 984091 := bstep (se 1 (by rfl) ⟨738068, by rfl⟩ : syracuseStep 984091 = 1476137) B1476137
theorem B2491631 : Blo 980594 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B7079251 : Blo 980594 7079251 := bstep (se 1 (by rfl) ⟨5309438, by rfl⟩ : syracuseStep 7079251 = 10618877) B10618877
theorem B984527 : Blo 980594 984527 := bstep (se 1 (by rfl) ⟨738395, by rfl⟩ : syracuseStep 984527 = 1476791) B1476791
theorem B984551 : Blo 980594 984551 := bstep (se 1 (by rfl) ⟨738413, by rfl⟩ : syracuseStep 984551 = 1476827) B1476827
theorem B2655899 : Blo 980594 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B40306409 : Blo 980594 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B1476671 : Blo 980594 1476671 := bstep (se 1 (by rfl) ⟨1107503, by rfl⟩ : syracuseStep 1476671 = 2215007) B2215007
theorem B4983119 : Blo 980594 4983119 := bstep (se 1 (by rfl) ⟨3737339, by rfl⟩ : syracuseStep 4983119 = 7474679) B7474679
theorem B135989711 : Blo 980594 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B2100563 : Blo 980594 2100563 := bstep (se 1 (by rfl) ⟨1575422, by rfl⟩ : syracuseStep 2100563 = 3150845) B3150845
theorem B3314303 : Blo 980594 3314303 := bstep (se 1 (by rfl) ⟨2485727, by rfl⟩ : syracuseStep 3314303 = 4971455) B4971455
theorem B7476137 : Blo 980594 7476137 := bstep (se 2 (by rfl) ⟨2803551, by rfl⟩ : syracuseStep 7476137 = 5607103) B5607103
theorem B4199759 : Blo 980594 4199759 := bstep (se 1 (by rfl) ⟨3149819, by rfl⟩ : syracuseStep 4199759 = 6299639) B6299639
theorem B1677353 : Blo 980594 1677353 := bstep (se 2 (by rfl) ⟨629007, by rfl⟩ : syracuseStep 1677353 = 1258015) B1258015
theorem B5318045 : Blo 980594 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B19113577 : Blo 980594 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B48474773 : Blo 980594 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B2206511 : Blo 980594 2206511 := bstep (se 1 (by rfl) ⟨1654883, by rfl⟩ : syracuseStep 2206511 = 3309767) B3309767
theorem B3320891 : Blo 980594 3320891 := bstep (se 1 (by rfl) ⟨2490668, by rfl⟩ : syracuseStep 3320891 = 4981337) B4981337
theorem B15937003 : Blo 980594 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B2797993 : Blo 980594 2797993 := bstep (se 2 (by rfl) ⟨1049247, by rfl⟩ : syracuseStep 2797993 = 2098495) B2098495
theorem B2208347 : Blo 980594 2208347 := bstep (se 1 (by rfl) ⟨1656260, by rfl⟩ : syracuseStep 2208347 = 3312521) B3312521
theorem B22688599 : Blo 980594 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B6304711 : Blo 980594 6304711 := bstep (se 1 (by rfl) ⟨4728533, by rfl⟩ : syracuseStep 6304711 = 9457067) B9457067
theorem B26850689 : Blo 980594 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B2799679 : Blo 980594 2799679 := bstep (se 1 (by rfl) ⟨2099759, by rfl⟩ : syracuseStep 2799679 = 4199519) B4199519
theorem B2211227 : Blo 980594 2211227 := bstep (se 1 (by rfl) ⟨1658420, by rfl⟩ : syracuseStep 2211227 = 3316841) B3316841
theorem B1261423 : Blo 980594 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B2211911 : Blo 980594 2211911 := bstep (se 1 (by rfl) ⟨1658933, by rfl⟩ : syracuseStep 2211911 = 3317867) B3317867
theorem B2212379 : Blo 980594 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B18891305 : Blo 980594 18891305 := bstep (se 2 (by rfl) ⟨7084239, by rfl⟩ : syracuseStep 18891305 = 14168479) B14168479
theorem B4964975 : Blo 980594 4964975 := bstep (se 1 (by rfl) ⟨3723731, by rfl⟩ : syracuseStep 4964975 = 7447463) B7447463
theorem B3983215 : Blo 980594 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B4967081 : Blo 980594 4967081 := bstep (se 2 (by rfl) ⟨1862655, by rfl⟩ : syracuseStep 4967081 = 3725311) B3725311
theorem B3591049 : Blo 980594 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B7458155 : Blo 980594 7458155 := bstep (se 1 (by rfl) ⟨5593616, by rfl⟩ : syracuseStep 7458155 = 11187233) B11187233
theorem B1396639 : Blo 980594 1396639 := bstep (se 1 (by rfl) ⟨1047479, by rfl⟩ : syracuseStep 1396639 = 2094959) B2094959
theorem B9457991 : Blo 980594 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B1660783 : Blo 980594 1660783 := bstep (se 1 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 1660783 = 2491175) B2491175
theorem B5595257 : Blo 980594 5595257 := bstep (se 2 (by rfl) ⟨2098221, by rfl⟩ : syracuseStep 5595257 = 4196443) B4196443
theorem B3727727 : Blo 980594 3727727 := bstep (se 1 (by rfl) ⟨2795795, by rfl⟩ : syracuseStep 3727727 = 5591591) B5591591
theorem B4481407 : Blo 980594 4481407 := bstep (se 1 (by rfl) ⟨3361055, by rfl⟩ : syracuseStep 4481407 = 6722111) B6722111
theorem B14180987 : Blo 980594 14180987 := bstep (se 1 (by rfl) ⟨10635740, by rfl⟩ : syracuseStep 14180987 = 21271481) B21271481
theorem B12608297 : Blo 980594 12608297 := bstep (se 2 (by rfl) ⟨4728111, by rfl⟩ : syracuseStep 12608297 = 9456223) B9456223
theorem B430467209 : Blo 980594 430467209 := bstep (se 2 (by rfl) ⟨161425203, by rfl⟩ : syracuseStep 430467209 = 322850407) B322850407
theorem B4189097 : Blo 980594 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B23883133 : Blo 980594 23883133 := bstep (se 3 (by rfl) ⟨4478087, by rfl⟩ : syracuseStep 23883133 = 8956175) B8956175
theorem B1241983 : Blo 980594 1241983 := bstep (se 1 (by rfl) ⟨931487, by rfl⟩ : syracuseStep 1241983 = 1862975) B1862975
theorem B138015899 : Blo 980594 138015899 := bstep (se 1 (by rfl) ⟨103511924, by rfl⟩ : syracuseStep 138015899 = 207023849) B207023849
theorem B3143387 : Blo 980594 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B1472489 : Blo 980594 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B1472615 : Blo 980594 1472615 := bstep (se 1 (by rfl) ⟨1104461, by rfl⟩ : syracuseStep 1472615 = 2208923) B2208923
theorem B981231 : Blo 980594 981231 := bstep (se 1 (by rfl) ⟨735923, by rfl⟩ : syracuseStep 981231 = 1471847) B1471847
theorem B1473743 : Blo 980594 1473743 := bstep (se 1 (by rfl) ⟨1105307, by rfl⟩ : syracuseStep 1473743 = 2210615) B2210615
theorem B2489575 : Blo 980594 2489575 := bstep (se 1 (by rfl) ⟨1867181, by rfl⟩ : syracuseStep 2489575 = 3734363) B3734363
theorem B982255 : Blo 980594 982255 := bstep (se 1 (by rfl) ⟨736691, by rfl⟩ : syracuseStep 982255 = 1473383) B1473383
theorem B982319 : Blo 980594 982319 := bstep (se 1 (by rfl) ⟨736739, by rfl⟩ : syracuseStep 982319 = 1473479) B1473479
theorem B1244575 : Blo 980594 1244575 := bstep (se 1 (by rfl) ⟨933431, by rfl⟩ : syracuseStep 1244575 = 1866863) B1866863
theorem B4980203 : Blo 980594 4980203 := bstep (se 1 (by rfl) ⟨3735152, by rfl⟩ : syracuseStep 4980203 = 7470305) B7470305
theorem B9436769 : Blo 980594 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B1474175 : Blo 980594 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B1474607 : Blo 980594 1474607 := bstep (se 1 (by rfl) ⟨1105955, by rfl⟩ : syracuseStep 1474607 = 2211911) B2211911
theorem B983195 : Blo 980594 983195 := bstep (se 1 (by rfl) ⟨737396, by rfl⟩ : syracuseStep 983195 = 1474793) B1474793
theorem B1573103 : Blo 980594 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B1474919 : Blo 980594 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B3309983 : Blo 980594 3309983 := bstep (se 1 (by rfl) ⟨2482487, by rfl⟩ : syracuseStep 3309983 = 4964975) B4964975
theorem B17891765 : Blo 980594 17891765 := bstep (se 5 (by rfl) ⟨838676, by rfl⟩ : syracuseStep 17891765 = 1677353) B1677353
theorem B983707 : Blo 980594 983707 := bstep (se 1 (by rfl) ⟨737780, by rfl⟩ : syracuseStep 983707 = 1475561) B1475561
theorem B1770599 : Blo 980594 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B26870939 : Blo 980594 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B984447 : Blo 980594 984447 := bstep (se 1 (by rfl) ⟨738335, by rfl⟩ : syracuseStep 984447 = 1476671) B1476671
theorem B9439001 : Blo 980594 9439001 := bstep (se 2 (by rfl) ⟨3539625, by rfl⟩ : syracuseStep 9439001 = 7079251) B7079251
theorem B3311387 : Blo 980594 3311387 := bstep (se 1 (by rfl) ⟨2483540, by rfl⟩ : syracuseStep 3311387 = 4967081) B4967081
theorem B5310953 : Blo 980594 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B4984091 : Blo 980594 4984091 := bstep (se 1 (by rfl) ⟨3738068, by rfl⟩ : syracuseStep 4984091 = 7476137) B7476137
theorem B4788065 : Blo 980594 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B3545363 : Blo 980594 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B30251465 : Blo 980594 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B32316515 : Blo 980594 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B2792731 : Blo 980594 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B17900459 : Blo 980594 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B3319433 : Blo 980594 3319433 := bstep (se 2 (by rfl) ⟨1244787, by rfl⟩ : syracuseStep 3319433 = 2489575) B2489575
theorem B6727589 : Blo 980594 6727589 := bstep (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) B1261423
theorem B3320135 : Blo 980594 3320135 := bstep (se 1 (by rfl) ⟨2490101, by rfl⟩ : syracuseStep 3320135 = 4980203) B4980203
theorem B12594203 : Blo 980594 12594203 := bstep (se 1 (by rfl) ⟨9445652, by rfl⟩ : syracuseStep 12594203 = 18891305) B18891305
theorem B5975209 : Blo 980594 5975209 := bstep (se 2 (by rfl) ⟨2240703, by rfl⟩ : syracuseStep 5975209 = 4481407) B4481407
theorem B4042031 : Blo 980594 4042031 := bstep (se 1 (by rfl) ⟨3031523, by rfl⟩ : syracuseStep 4042031 = 6063047) B6063047
theorem B3321161 : Blo 980594 3321161 := bstep (se 2 (by rfl) ⟨1245435, by rfl⟩ : syracuseStep 3321161 = 2490871) B2490871
theorem B3322079 : Blo 980594 3322079 := bstep (se 1 (by rfl) ⟨2491559, by rfl⟩ : syracuseStep 3322079 = 4983119) B4983119
theorem B6305327 : Blo 980594 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B2209535 : Blo 980594 2209535 := bstep (se 1 (by rfl) ⟨1657151, by rfl⟩ : syracuseStep 2209535 = 3314303) B3314303
theorem B2799839 : Blo 980594 2799839 := bstep (se 1 (by rfl) ⟨2099879, by rfl⟩ : syracuseStep 2799839 = 4199759) B4199759
theorem B21249337 : Blo 980594 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B9453991 : Blo 980594 9453991 := bstep (se 1 (by rfl) ⟨7090493, by rfl⟩ : syracuseStep 9453991 = 14180987) B14180987
theorem B8405531 : Blo 980594 8405531 := bstep (se 1 (by rfl) ⟨6304148, by rfl⟩ : syracuseStep 8405531 = 12608297) B12608297
theorem B1655977 : Blo 980594 1655977 := bstep (se 2 (by rfl) ⟨620991, by rfl⟩ : syracuseStep 1655977 = 1241983) B1241983
theorem B8406281 : Blo 980594 8406281 := bstep (se 2 (by rfl) ⟨3152355, by rfl⟩ : syracuseStep 8406281 = 6304711) B6304711
theorem B2213927 : Blo 980594 2213927 := bstep (se 1 (by rfl) ⟨1660445, by rfl⟩ : syracuseStep 2213927 = 3320891) B3320891
theorem B2214377 : Blo 980594 2214377 := bstep (se 2 (by rfl) ⟨830391, by rfl⟩ : syracuseStep 2214377 = 1660783) B1660783
theorem B1659433 : Blo 980594 1659433 := bstep (se 2 (by rfl) ⟨622287, by rfl⟩ : syracuseStep 1659433 = 1244575) B1244575
theorem B1661087 : Blo 980594 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B90659807 : Blo 980594 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B1400375 : Blo 980594 1400375 := bstep (se 1 (by rfl) ⟨1050281, by rfl⟩ : syracuseStep 1400375 = 2100563) B2100563
theorem B4972103 : Blo 980594 4972103 := bstep (se 1 (by rfl) ⟨3729077, by rfl⟩ : syracuseStep 4972103 = 7458155) B7458155
theorem B31844177 : Blo 980594 31844177 := bstep (se 2 (by rfl) ⟨11941566, by rfl⟩ : syracuseStep 31844177 = 23883133) B23883133
theorem B1862185 : Blo 980594 1862185 := bstep (se 2 (by rfl) ⟨698319, by rfl⟩ : syracuseStep 1862185 = 1396639) B1396639
theorem B3730171 : Blo 980594 3730171 := bstep (se 1 (by rfl) ⟨2797628, by rfl⟩ : syracuseStep 3730171 = 5595257) B5595257
theorem B2485151 : Blo 980594 2485151 := bstep (se 1 (by rfl) ⟨1863863, by rfl⟩ : syracuseStep 2485151 = 3727727) B3727727
theorem B3730657 : Blo 980594 3730657 := bstep (se 2 (by rfl) ⟨1398996, by rfl⟩ : syracuseStep 3730657 = 2797993) B2797993
theorem B286978139 : Blo 980594 286978139 := bstep (se 1 (by rfl) ⟨215233604, by rfl⟩ : syracuseStep 286978139 = 430467209) B430467209
theorem B1471007 : Blo 980594 1471007 := bstep (se 1 (by rfl) ⟨1103255, by rfl⟩ : syracuseStep 1471007 = 2206511) B2206511
theorem B3732905 : Blo 980594 3732905 := bstep (se 2 (by rfl) ⟨1399839, by rfl⟩ : syracuseStep 3732905 = 2799679) B2799679
theorem B1472231 : Blo 980594 1472231 := bstep (se 1 (by rfl) ⟨1104173, by rfl⟩ : syracuseStep 1472231 = 2208347) B2208347
theorem B101939077 : Blo 980594 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B92010599 : Blo 980594 92010599 := bstep (se 1 (by rfl) ⟨69007949, by rfl⟩ : syracuseStep 92010599 = 138015899) B138015899
theorem B2095591 : Blo 980594 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B981659 : Blo 980594 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B981743 : Blo 980594 981743 := bstep (se 1 (by rfl) ⟨736307, by rfl⟩ : syracuseStep 981743 = 1472615) B1472615
theorem B982495 : Blo 980594 982495 := bstep (se 1 (by rfl) ⟨736871, by rfl⟩ : syracuseStep 982495 = 1473743) B1473743
theorem B1474151 : Blo 980594 1474151 := bstep (se 1 (by rfl) ⟨1105613, by rfl⟩ : syracuseStep 1474151 = 2211227) B2211227
theorem B6291179 : Blo 980594 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B982783 : Blo 980594 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B983071 : Blo 980594 983071 := bstep (se 1 (by rfl) ⟨737303, by rfl⟩ : syracuseStep 983071 = 1474607) B1474607
theorem B1048735 : Blo 980594 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B983279 : Blo 980594 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B11927843 : Blo 980594 11927843 := bstep (se 1 (by rfl) ⟨8945882, by rfl⟩ : syracuseStep 11927843 = 17891765) B17891765
theorem B5603687 : Blo 980594 5603687 := bstep (se 1 (by rfl) ⟨4202765, by rfl⟩ : syracuseStep 5603687 = 8405531) B8405531
theorem B5604187 : Blo 980594 5604187 := bstep (se 1 (by rfl) ⟨4203140, by rfl⟩ : syracuseStep 5604187 = 8406281) B8406281
theorem B6292667 : Blo 980594 6292667 := bstep (se 1 (by rfl) ⟨4719500, by rfl⟩ : syracuseStep 6292667 = 9439001) B9439001
theorem B1475951 : Blo 980594 1475951 := bstep (se 1 (by rfl) ⟨1106963, by rfl⟩ : syracuseStep 1475951 = 2213927) B2213927
theorem B3540635 : Blo 980594 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B1476251 : Blo 980594 1476251 := bstep (se 1 (by rfl) ⟨1107188, by rfl⟩ : syracuseStep 1476251 = 2214377) B2214377
theorem B4721597 : Blo 980594 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B2363575 : Blo 980594 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B7966945 : Blo 980594 7966945 := bstep (se 2 (by rfl) ⟨2987604, by rfl⟩ : syracuseStep 7966945 = 5975209) B5975209
theorem B3314735 : Blo 980594 3314735 := bstep (se 1 (by rfl) ⟨2486051, by rfl⟩ : syracuseStep 3314735 = 4972103) B4972103
theorem B11933639 : Blo 980594 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B8396135 : Blo 980594 8396135 := bstep (se 1 (by rfl) ⟨6297101, by rfl⟩ : syracuseStep 8396135 = 12594203) B12594203
theorem B2794121 : Blo 980594 2794121 := bstep (se 2 (by rfl) ⟨1047795, by rfl⟩ : syracuseStep 2794121 = 2095591) B2095591
theorem B4203551 : Blo 980594 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B2206655 : Blo 980594 2206655 := bstep (se 1 (by rfl) ⟨1654991, by rfl⟩ : syracuseStep 2206655 = 3309983) B3309983
theorem B2207591 : Blo 980594 2207591 := bstep (se 1 (by rfl) ⟨1655693, by rfl⟩ : syracuseStep 2207591 = 3311387) B3311387
theorem B2207969 : Blo 980594 2207969 := bstep (se 2 (by rfl) ⟨827988, by rfl⟩ : syracuseStep 2207969 = 1655977) B1655977
theorem B3322727 : Blo 980594 3322727 := bstep (se 1 (by rfl) ⟨2492045, by rfl⟩ : syracuseStep 3322727 = 4984091) B4984091
theorem B3192043 : Blo 980594 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B20167643 : Blo 980594 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B60439871 : Blo 980594 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B21544343 : Blo 980594 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B2212577 : Blo 980594 2212577 := bstep (se 2 (by rfl) ⟨829716, by rfl⟩ : syracuseStep 2212577 = 1659433) B1659433
theorem B2212955 : Blo 980594 2212955 := bstep (se 1 (by rfl) ⟨1659716, by rfl⟩ : syracuseStep 2212955 = 3319433) B3319433
theorem B2213423 : Blo 980594 2213423 := bstep (se 1 (by rfl) ⟨1660067, by rfl⟩ : syracuseStep 2213423 = 3320135) B3320135
theorem B1656767 : Blo 980594 1656767 := bstep (se 1 (by rfl) ⟨1242575, by rfl⟩ : syracuseStep 1656767 = 2485151) B2485151
theorem B2214107 : Blo 980594 2214107 := bstep (se 1 (by rfl) ⟨1660580, by rfl⟩ : syracuseStep 2214107 = 3321161) B3321161
theorem B191318759 : Blo 980594 191318759 := bstep (se 1 (by rfl) ⟨143489069, by rfl⟩ : syracuseStep 191318759 = 286978139) B286978139
theorem B2214719 : Blo 980594 2214719 := bstep (se 1 (by rfl) ⟨1661039, by rfl⟩ : syracuseStep 2214719 = 3322079) B3322079
theorem B3723641 : Blo 980594 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B28332449 : Blo 980594 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B12605321 : Blo 980594 12605321 := bstep (se 2 (by rfl) ⟨4726995, by rfl⟩ : syracuseStep 12605321 = 9453991) B9453991
theorem B17913959 : Blo 980594 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B43114997 : Blo 980594 43114997 := bstep (se 5 (by rfl) ⟨2021015, by rfl⟩ : syracuseStep 43114997 = 4042031) B4042031
theorem B2482913 : Blo 980594 2482913 := bstep (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) B1862185
theorem B4973561 : Blo 980594 4973561 := bstep (se 2 (by rfl) ⟨1865085, by rfl⟩ : syracuseStep 4973561 = 3730171) B3730171
theorem B1107391 : Blo 980594 1107391 := bstep (se 1 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 1107391 = 1661087) B1661087
theorem B4974209 : Blo 980594 4974209 := bstep (se 2 (by rfl) ⟨1865328, by rfl⟩ : syracuseStep 4974209 = 3730657) B3730657
theorem B21229451 : Blo 980594 21229451 := bstep (se 1 (by rfl) ⟨15922088, by rfl⟩ : syracuseStep 21229451 = 31844177) B31844177
theorem B4485059 : Blo 980594 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B135918769 : Blo 980594 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B980671 : Blo 980594 980671 := bstep (se 1 (by rfl) ⟨735503, by rfl⟩ : syracuseStep 980671 = 1471007) B1471007
theorem B2488603 : Blo 980594 2488603 := bstep (se 1 (by rfl) ⟨1866452, by rfl⟩ : syracuseStep 2488603 = 3732905) B3732905
theorem B981487 : Blo 980594 981487 := bstep (se 1 (by rfl) ⟨736115, by rfl⟩ : syracuseStep 981487 = 1472231) B1472231
theorem B1473023 : Blo 980594 1473023 := bstep (se 1 (by rfl) ⟨1104767, by rfl⟩ : syracuseStep 1473023 = 2209535) B2209535
theorem B61340399 : Blo 980594 61340399 := bstep (se 1 (by rfl) ⟨46005299, by rfl⟩ : syracuseStep 61340399 = 92010599) B92010599
theorem B3734333 : Blo 980594 3734333 := bstep (se 3 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 3734333 = 1400375) B1400375
theorem B1866559 : Blo 980594 1866559 := bstep (se 1 (by rfl) ⟨1399919, by rfl⟩ : syracuseStep 1866559 = 2799839) B2799839
theorem B982767 : Blo 980594 982767 := bstep (se 1 (by rfl) ⟨737075, by rfl⟩ : syracuseStep 982767 = 1474151) B1474151
theorem B4194119 : Blo 980594 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B3735791 : Blo 980594 3735791 := bstep (se 1 (by rfl) ⟨2801843, by rfl⟩ : syracuseStep 3735791 = 5603687) B5603687
theorem B1475051 : Blo 980594 1475051 := bstep (se 1 (by rfl) ⟨1106288, by rfl⟩ : syracuseStep 1475051 = 2212577) B2212577
theorem B1475303 : Blo 980594 1475303 := bstep (se 1 (by rfl) ⟨1106477, by rfl⟩ : syracuseStep 1475303 = 2212955) B2212955
theorem B4195111 : Blo 980594 4195111 := bstep (se 1 (by rfl) ⟨3146333, by rfl⟩ : syracuseStep 4195111 = 6292667) B6292667
theorem B983967 : Blo 980594 983967 := bstep (se 1 (by rfl) ⟨737975, by rfl⟩ : syracuseStep 983967 = 1475951) B1475951
theorem B1475615 : Blo 980594 1475615 := bstep (se 1 (by rfl) ⟨1106711, by rfl⟩ : syracuseStep 1475615 = 2213423) B2213423
theorem B2360423 : Blo 980594 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B984167 : Blo 980594 984167 := bstep (se 1 (by rfl) ⟨738125, by rfl⟩ : syracuseStep 984167 = 1476251) B1476251
theorem B7472249 : Blo 980594 7472249 := bstep (se 2 (by rfl) ⟨2802093, by rfl⟩ : syracuseStep 7472249 = 5604187) B5604187
theorem B1476071 : Blo 980594 1476071 := bstep (se 1 (by rfl) ⟨1107053, by rfl⟩ : syracuseStep 1476071 = 2214107) B2214107
theorem B1476479 : Blo 980594 1476479 := bstep (se 1 (by rfl) ⟨1107359, by rfl⟩ : syracuseStep 1476479 = 2214719) B2214719
theorem B1476521 : Blo 980594 1476521 := bstep (se 2 (by rfl) ⟨553695, by rfl⟩ : syracuseStep 1476521 = 1107391) B1107391
theorem B3147731 : Blo 980594 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B3151433 : Blo 980594 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B10622593 : Blo 980594 10622593 := bstep (se 2 (by rfl) ⟨3983472, by rfl⟩ : syracuseStep 10622593 = 7966945) B7966945
theorem B28743331 : Blo 980594 28743331 := bstep (se 1 (by rfl) ⟨21557498, by rfl⟩ : syracuseStep 28743331 = 43114997) B43114997
theorem B3315707 : Blo 980594 3315707 := bstep (se 1 (by rfl) ⟨2486780, by rfl⟩ : syracuseStep 3315707 = 4973561) B4973561
theorem B3316139 : Blo 980594 3316139 := bstep (se 1 (by rfl) ⟨2487104, by rfl⟩ : syracuseStep 3316139 = 4974209) B4974209
theorem B53780381 : Blo 980594 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B2990039 : Blo 980594 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B3318137 : Blo 980594 3318137 := bstep (se 2 (by rfl) ⟨1244301, by rfl⟩ : syracuseStep 3318137 = 2488603) B2488603
theorem B11184317 : Blo 980594 11184317 := bstep (se 3 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 11184317 = 4194119) B4194119
theorem B14362895 : Blo 980594 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B127545839 : Blo 980594 127545839 := bstep (se 1 (by rfl) ⟨95659379, by rfl⟩ : syracuseStep 127545839 = 191318759) B191318759
theorem B18888299 : Blo 980594 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B2209823 : Blo 980594 2209823 := bstep (se 1 (by rfl) ⟨1657367, by rfl⟩ : syracuseStep 2209823 = 3314735) B3314735
theorem B8403547 : Blo 980594 8403547 := bstep (se 1 (by rfl) ⟨6302660, by rfl⟩ : syracuseStep 8403547 = 12605321) B12605321
theorem B11942639 : Blo 980594 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B1655275 : Blo 980594 1655275 := bstep (se 1 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 1655275 = 2482913) B2482913
theorem B2802367 : Blo 980594 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B181225025 : Blo 980594 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B2215151 : Blo 980594 2215151 := bstep (se 1 (by rfl) ⟨1661363, by rfl⟩ : syracuseStep 2215151 = 3322727) B3322727
theorem B40293247 : Blo 980594 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B7951895 : Blo 980594 7951895 := bstep (se 1 (by rfl) ⟨5963921, by rfl⟩ : syracuseStep 7951895 = 11927843) B11927843
theorem B1398313 : Blo 980594 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B1104511 : Blo 980594 1104511 := bstep (se 1 (by rfl) ⟨828383, by rfl⟩ : syracuseStep 1104511 = 1656767) B1656767
theorem B2482427 : Blo 980594 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B7955759 : Blo 980594 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B5597423 : Blo 980594 5597423 := bstep (se 1 (by rfl) ⟨4198067, by rfl⟩ : syracuseStep 5597423 = 8396135) B8396135
theorem B1862747 : Blo 980594 1862747 := bstep (se 1 (by rfl) ⟨1397060, by rfl⟩ : syracuseStep 1862747 = 2794121) B2794121
theorem B4256057 : Blo 980594 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B1471103 : Blo 980594 1471103 := bstep (se 1 (by rfl) ⟨1103327, by rfl⟩ : syracuseStep 1471103 = 2206655) B2206655
theorem B1471727 : Blo 980594 1471727 := bstep (se 1 (by rfl) ⟨1103795, by rfl⟩ : syracuseStep 1471727 = 2207591) B2207591
theorem B14152967 : Blo 980594 14152967 := bstep (se 1 (by rfl) ⟨10614725, by rfl⟩ : syracuseStep 14152967 = 21229451) B21229451
theorem B1471979 : Blo 980594 1471979 := bstep (se 1 (by rfl) ⟨1103984, by rfl⟩ : syracuseStep 1471979 = 2207969) B2207969
theorem B2488745 : Blo 980594 2488745 := bstep (se 2 (by rfl) ⟨933279, by rfl⟩ : syracuseStep 2488745 = 1866559) B1866559
theorem B982015 : Blo 980594 982015 := bstep (se 1 (by rfl) ⟨736511, by rfl⟩ : syracuseStep 982015 = 1473023) B1473023
theorem B40893599 : Blo 980594 40893599 := bstep (se 1 (by rfl) ⟨30670199, by rfl⟩ : syracuseStep 40893599 = 61340399) B61340399
theorem B2489555 : Blo 980594 2489555 := bstep (se 1 (by rfl) ⟨1867166, by rfl⟩ : syracuseStep 2489555 = 3734333) B3734333
theorem B2490527 : Blo 980594 2490527 := bstep (se 1 (by rfl) ⟨1867895, by rfl⟩ : syracuseStep 2490527 = 3735791) B3735791
theorem B983367 : Blo 980594 983367 := bstep (se 1 (by rfl) ⟨737525, by rfl⟩ : syracuseStep 983367 = 1475051) B1475051
theorem B983535 : Blo 980594 983535 := bstep (se 1 (by rfl) ⟨737651, by rfl⟩ : syracuseStep 983535 = 1475303) B1475303
theorem B983743 : Blo 980594 983743 := bstep (se 1 (by rfl) ⟨737807, by rfl⟩ : syracuseStep 983743 = 1475615) B1475615
theorem B1573615 : Blo 980594 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B4981499 : Blo 980594 4981499 := bstep (se 1 (by rfl) ⟨3736124, by rfl⟩ : syracuseStep 4981499 = 7472249) B7472249
theorem B3736489 : Blo 980594 3736489 := bstep (se 2 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 3736489 = 2802367) B2802367
theorem B984047 : Blo 980594 984047 := bstep (se 1 (by rfl) ⟨738035, by rfl⟩ : syracuseStep 984047 = 1476071) B1476071
theorem B120816683 : Blo 980594 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B984319 : Blo 980594 984319 := bstep (se 1 (by rfl) ⟨738239, by rfl⟩ : syracuseStep 984319 = 1476479) B1476479
theorem B984347 : Blo 980594 984347 := bstep (se 1 (by rfl) ⟨738260, by rfl⟩ : syracuseStep 984347 = 1476521) B1476521
theorem B2098487 : Blo 980594 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1476767 : Blo 980594 1476767 := bstep (se 1 (by rfl) ⟨1107575, by rfl⟩ : syracuseStep 1476767 = 2215151) B2215151
theorem B35853587 : Blo 980594 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B9575263 : Blo 980594 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B14163457 : Blo 980594 14163457 := bstep (se 2 (by rfl) ⟨5311296, by rfl⟩ : syracuseStep 14163457 = 10622593) B10622593
theorem B12592199 : Blo 980594 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B7973437 : Blo 980594 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B2207033 : Blo 980594 2207033 := bstep (se 2 (by rfl) ⟨827637, by rfl⟩ : syracuseStep 2207033 = 1655275) B1655275
theorem B21215357 : Blo 980594 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B2210471 : Blo 980594 2210471 := bstep (se 1 (by rfl) ⟨1657853, by rfl⟩ : syracuseStep 2210471 = 3315707) B3315707
theorem B8403821 : Blo 980594 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B2210759 : Blo 980594 2210759 := bstep (se 1 (by rfl) ⟨1658069, by rfl⟩ : syracuseStep 2210759 = 3316139) B3316139
theorem B1654951 : Blo 980594 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B2212091 : Blo 980594 2212091 := bstep (se 1 (by rfl) ⟨1659068, by rfl⟩ : syracuseStep 2212091 = 3318137) B3318137
theorem B53724329 : Blo 980594 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B7456211 : Blo 980594 7456211 := bstep (se 1 (by rfl) ⟨5592158, by rfl⟩ : syracuseStep 7456211 = 11184317) B11184317
theorem B38324441 : Blo 980594 38324441 := bstep (se 2 (by rfl) ⟨14371665, by rfl⟩ : syracuseStep 38324441 = 28743331) B28743331
theorem B2837371 : Blo 980594 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B7457669 : Blo 980594 7457669 := bstep (se 4 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 7457669 = 1398313) B1398313
theorem B1659163 : Blo 980594 1659163 := bstep (se 1 (by rfl) ⟨1244372, by rfl⟩ : syracuseStep 1659163 = 2488745) B2488745
theorem B1659703 : Blo 980594 1659703 := bstep (se 1 (by rfl) ⟨1244777, by rfl⟩ : syracuseStep 1659703 = 2489555) B2489555
theorem B5593481 : Blo 980594 5593481 := bstep (se 2 (by rfl) ⟨2097555, by rfl⟩ : syracuseStep 5593481 = 4195111) B4195111
theorem B5301263 : Blo 980594 5301263 := bstep (se 1 (by rfl) ⟨3975947, by rfl⟩ : syracuseStep 5301263 = 7951895) B7951895
theorem B3731615 : Blo 980594 3731615 := bstep (se 1 (by rfl) ⟨2798711, by rfl⟩ : syracuseStep 3731615 = 5597423) B5597423
theorem B1241831 : Blo 980594 1241831 := bstep (se 1 (by rfl) ⟨931373, by rfl⟩ : syracuseStep 1241831 = 1862747) B1862747
theorem B85030559 : Blo 980594 85030559 := bstep (se 1 (by rfl) ⟨63772919, by rfl⟩ : syracuseStep 85030559 = 127545839) B127545839
theorem B109049597 : Blo 980594 109049597 := bstep (se 3 (by rfl) ⟨20446799, by rfl⟩ : syracuseStep 109049597 = 40893599) B40893599
theorem B980735 : Blo 980594 980735 := bstep (se 1 (by rfl) ⟨735551, by rfl⟩ : syracuseStep 980735 = 1471103) B1471103
theorem B11204729 : Blo 980594 11204729 := bstep (se 2 (by rfl) ⟨4201773, by rfl⟩ : syracuseStep 11204729 = 8403547) B8403547
theorem B981151 : Blo 980594 981151 := bstep (se 1 (by rfl) ⟨735863, by rfl⟩ : syracuseStep 981151 = 1471727) B1471727
theorem B1472681 : Blo 980594 1472681 := bstep (se 2 (by rfl) ⟨552255, by rfl⟩ : syracuseStep 1472681 = 1104511) B1104511
theorem B9435311 : Blo 980594 9435311 := bstep (se 1 (by rfl) ⟨7076483, by rfl⟩ : syracuseStep 9435311 = 14152967) B14152967
theorem B981319 : Blo 980594 981319 := bstep (se 1 (by rfl) ⟨735989, by rfl⟩ : syracuseStep 981319 = 1471979) B1471979
theorem B1473215 : Blo 980594 1473215 := bstep (se 1 (by rfl) ⟨1104911, by rfl⟩ : syracuseStep 1473215 = 2209823) B2209823
theorem B7961759 : Blo 980594 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B1474727 : Blo 980594 1474727 := bstep (se 1 (by rfl) ⟨1106045, by rfl⟩ : syracuseStep 1474727 = 2212091) B2212091
theorem B80544455 : Blo 980594 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B35816219 : Blo 980594 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B2098153 : Blo 980594 2098153 := bstep (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) B1573615
theorem B4981985 : Blo 980594 4981985 := bstep (se 2 (by rfl) ⟨1868244, by rfl⟩ : syracuseStep 4981985 = 3736489) B3736489
theorem B984511 : Blo 980594 984511 := bstep (se 1 (by rfl) ⟨738383, by rfl⟩ : syracuseStep 984511 = 1476767) B1476767
theorem B3311549 : Blo 980594 3311549 := bstep (se 3 (by rfl) ⟨620915, by rfl⟩ : syracuseStep 3311549 = 1241831) B1241831
theorem B8394799 : Blo 980594 8394799 := bstep (se 1 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 8394799 = 12592199) B12592199
theorem B18884609 : Blo 980594 18884609 := bstep (se 2 (by rfl) ⟨7081728, by rfl⟩ : syracuseStep 18884609 = 14163457) B14163457
theorem B2206601 : Blo 980594 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B3320999 : Blo 980594 3320999 := bstep (se 1 (by rfl) ⟨2490749, by rfl⟩ : syracuseStep 3320999 = 4981499) B4981499
theorem B10631249 : Blo 980594 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B23902391 : Blo 980594 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B3783161 : Blo 980594 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B51068069 : Blo 980594 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B2212217 : Blo 980594 2212217 := bstep (se 2 (by rfl) ⟨829581, by rfl⟩ : syracuseStep 2212217 = 1659163) B1659163
theorem B2212937 : Blo 980594 2212937 := bstep (se 2 (by rfl) ⟨829851, by rfl⟩ : syracuseStep 2212937 = 1659703) B1659703
theorem B72699731 : Blo 980594 72699731 := bstep (se 1 (by rfl) ⟨54524798, by rfl⟩ : syracuseStep 72699731 = 109049597) B109049597
theorem B14143571 : Blo 980594 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B1660351 : Blo 980594 1660351 := bstep (se 1 (by rfl) ⟨1245263, by rfl⟩ : syracuseStep 1660351 = 2490527) B2490527
theorem B4970807 : Blo 980594 4970807 := bstep (se 1 (by rfl) ⟨3728105, by rfl⟩ : syracuseStep 4970807 = 7456211) B7456211
theorem B25549627 : Blo 980594 25549627 := bstep (se 1 (by rfl) ⟨19162220, by rfl⟩ : syracuseStep 25549627 = 38324441) B38324441
theorem B4971779 : Blo 980594 4971779 := bstep (se 1 (by rfl) ⟨3728834, by rfl⟩ : syracuseStep 4971779 = 7457669) B7457669
theorem B5595965 : Blo 980594 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B3728987 : Blo 980594 3728987 := bstep (se 1 (by rfl) ⟨2796740, by rfl⟩ : syracuseStep 3728987 = 5593481) B5593481
theorem B3534175 : Blo 980594 3534175 := bstep (se 1 (by rfl) ⟨2650631, by rfl⟩ : syracuseStep 3534175 = 5301263) B5301263
theorem B1471355 : Blo 980594 1471355 := bstep (se 1 (by rfl) ⟨1103516, by rfl⟩ : syracuseStep 1471355 = 2207033) B2207033
theorem B2487743 : Blo 980594 2487743 := bstep (se 1 (by rfl) ⟨1865807, by rfl⟩ : syracuseStep 2487743 = 3731615) B3731615
theorem B56687039 : Blo 980594 56687039 := bstep (se 1 (by rfl) ⟨42515279, by rfl⟩ : syracuseStep 56687039 = 85030559) B85030559
theorem B7469819 : Blo 980594 7469819 := bstep (se 1 (by rfl) ⟨5602364, by rfl⟩ : syracuseStep 7469819 = 11204729) B11204729
theorem B981787 : Blo 980594 981787 := bstep (se 1 (by rfl) ⟨736340, by rfl⟩ : syracuseStep 981787 = 1472681) B1472681
theorem B6290207 : Blo 980594 6290207 := bstep (se 1 (by rfl) ⟨4717655, by rfl⟩ : syracuseStep 6290207 = 9435311) B9435311
theorem B1473647 : Blo 980594 1473647 := bstep (se 1 (by rfl) ⟨1105235, by rfl⟩ : syracuseStep 1473647 = 2210471) B2210471
theorem B982143 : Blo 980594 982143 := bstep (se 1 (by rfl) ⟨736607, by rfl⟩ : syracuseStep 982143 = 1473215) B1473215
theorem B5602547 : Blo 980594 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B1473839 : Blo 980594 1473839 := bstep (se 1 (by rfl) ⟨1105379, by rfl⟩ : syracuseStep 1473839 = 2210759) B2210759
theorem B5307839 : Blo 980594 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B983151 : Blo 980594 983151 := bstep (se 1 (by rfl) ⟨737363, by rfl⟩ : syracuseStep 983151 = 1474727) B1474727
theorem B1474811 : Blo 980594 1474811 := bstep (se 1 (by rfl) ⟨1106108, by rfl⟩ : syracuseStep 1474811 = 2212217) B2212217
theorem B1475291 : Blo 980594 1475291 := bstep (se 1 (by rfl) ⟨1106468, by rfl⟩ : syracuseStep 1475291 = 2212937) B2212937
theorem B48466487 : Blo 980594 48466487 := bstep (se 1 (by rfl) ⟨36349865, by rfl⟩ : syracuseStep 48466487 = 72699731) B72699731
theorem B3313871 : Blo 980594 3313871 := bstep (se 1 (by rfl) ⟨2485403, by rfl⟩ : syracuseStep 3313871 = 4970807) B4970807
theorem B3314519 : Blo 980594 3314519 := bstep (se 1 (by rfl) ⟨2485889, by rfl⟩ : syracuseStep 3314519 = 4971779) B4971779
theorem B12589739 : Blo 980594 12589739 := bstep (se 1 (by rfl) ⟨9442304, by rfl⟩ : syracuseStep 12589739 = 18884609) B18884609
theorem B18848933 : Blo 980594 18848933 := bstep (se 4 (by rfl) ⟨1767087, by rfl⟩ : syracuseStep 18848933 = 3534175) B3534175
theorem B7087499 : Blo 980594 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B15934927 : Blo 980594 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B37791359 : Blo 980594 37791359 := bstep (se 1 (by rfl) ⟨28343519, by rfl⟩ : syracuseStep 37791359 = 56687039) B56687039
theorem B3321323 : Blo 980594 3321323 := bstep (se 1 (by rfl) ⟨2490992, by rfl⟩ : syracuseStep 3321323 = 4981985) B4981985
theorem B2207699 : Blo 980594 2207699 := bstep (se 1 (by rfl) ⟨1655774, by rfl⟩ : syracuseStep 2207699 = 3311549) B3311549
theorem B11190149 : Blo 980594 11190149 := bstep (se 4 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 11190149 = 2098153) B2098153
theorem B2213801 : Blo 980594 2213801 := bstep (se 2 (by rfl) ⟨830175, by rfl⟩ : syracuseStep 2213801 = 1660351) B1660351
theorem B2213999 : Blo 980594 2213999 := bstep (se 1 (by rfl) ⟨1660499, by rfl⟩ : syracuseStep 2213999 = 3320999) B3320999
theorem B11193065 : Blo 980594 11193065 := bstep (se 2 (by rfl) ⟨4197399, by rfl⟩ : syracuseStep 11193065 = 8394799) B8394799
theorem B1658495 : Blo 980594 1658495 := bstep (se 1 (by rfl) ⟨1243871, by rfl⟩ : syracuseStep 1658495 = 2487743) B2487743
theorem B34066169 : Blo 980594 34066169 := bstep (se 2 (by rfl) ⟨12774813, by rfl⟩ : syracuseStep 34066169 = 25549627) B25549627
theorem B53696303 : Blo 980594 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B23877479 : Blo 980594 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B9429047 : Blo 980594 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B3730643 : Blo 980594 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B2485991 : Blo 980594 2485991 := bstep (se 1 (by rfl) ⟨1864493, by rfl⟩ : syracuseStep 2485991 = 3728987) B3728987
theorem B1471067 : Blo 980594 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B980903 : Blo 980594 980903 := bstep (se 1 (by rfl) ⟨735677, by rfl⟩ : syracuseStep 980903 = 1471355) B1471355
theorem B2522107 : Blo 980594 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B4979879 : Blo 980594 4979879 := bstep (se 1 (by rfl) ⟨3734909, by rfl⟩ : syracuseStep 4979879 = 7469819) B7469819
theorem B4193471 : Blo 980594 4193471 := bstep (se 1 (by rfl) ⟨3145103, by rfl⟩ : syracuseStep 4193471 = 6290207) B6290207
theorem B982431 : Blo 980594 982431 := bstep (se 1 (by rfl) ⟨736823, by rfl⟩ : syracuseStep 982431 = 1473647) B1473647
theorem B34045379 : Blo 980594 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B3735031 : Blo 980594 3735031 := bstep (se 1 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 3735031 = 5602547) B5602547
theorem B982559 : Blo 980594 982559 := bstep (se 1 (by rfl) ⟨736919, by rfl⟩ : syracuseStep 982559 = 1473839) B1473839
theorem B3538559 : Blo 980594 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B983207 : Blo 980594 983207 := bstep (se 1 (by rfl) ⟨737405, by rfl⟩ : syracuseStep 983207 = 1474811) B1474811
theorem B983527 : Blo 980594 983527 := bstep (se 1 (by rfl) ⟨737645, by rfl⟩ : syracuseStep 983527 = 1475291) B1475291
theorem B1475867 : Blo 980594 1475867 := bstep (se 1 (by rfl) ⟨1106900, by rfl⟩ : syracuseStep 1475867 = 2213801) B2213801
theorem B1475999 : Blo 980594 1475999 := bstep (se 1 (by rfl) ⟨1106999, by rfl⟩ : syracuseStep 1475999 = 2213999) B2213999
theorem B32310991 : Blo 980594 32310991 := bstep (se 1 (by rfl) ⟨24233243, by rfl⟩ : syracuseStep 32310991 = 48466487) B48466487
theorem B22710779 : Blo 980594 22710779 := bstep (se 1 (by rfl) ⟨17033084, by rfl⟩ : syracuseStep 22710779 = 34066169) B34066169
theorem B8393159 : Blo 980594 8393159 := bstep (se 1 (by rfl) ⟨6294869, by rfl⟩ : syracuseStep 8393159 = 12589739) B12589739
theorem B4724999 : Blo 980594 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B3319919 : Blo 980594 3319919 := bstep (se 1 (by rfl) ⟨2489939, by rfl⟩ : syracuseStep 3319919 = 4979879) B4979879
theorem B2795647 : Blo 980594 2795647 := bstep (se 1 (by rfl) ⟨2096735, by rfl⟩ : syracuseStep 2795647 = 4193471) B4193471
theorem B21246569 : Blo 980594 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B2209247 : Blo 980594 2209247 := bstep (se 1 (by rfl) ⟨1656935, by rfl⟩ : syracuseStep 2209247 = 3313871) B3313871
theorem B2209679 : Blo 980594 2209679 := bstep (se 1 (by rfl) ⟨1657259, by rfl⟩ : syracuseStep 2209679 = 3314519) B3314519
theorem B35797535 : Blo 980594 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B12565955 : Blo 980594 12565955 := bstep (se 1 (by rfl) ⟨9424466, by rfl⟩ : syracuseStep 12565955 = 18848933) B18848933
theorem B2214215 : Blo 980594 2214215 := bstep (se 1 (by rfl) ⟨1660661, by rfl⟩ : syracuseStep 2214215 = 3321323) B3321323
theorem B1657327 : Blo 980594 1657327 := bstep (se 1 (by rfl) ⟨1242995, by rfl⟩ : syracuseStep 1657327 = 2485991) B2485991
theorem B3362809 : Blo 980594 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B22696919 : Blo 980594 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B7460099 : Blo 980594 7460099 := bstep (se 1 (by rfl) ⟨5595074, by rfl⟩ : syracuseStep 7460099 = 11190149) B11190149
theorem B7462043 : Blo 980594 7462043 := bstep (se 1 (by rfl) ⟨5596532, by rfl⟩ : syracuseStep 7462043 = 11193065) B11193065
theorem B1105663 : Blo 980594 1105663 := bstep (se 1 (by rfl) ⟨829247, by rfl⟩ : syracuseStep 1105663 = 1658495) B1658495
theorem B15918319 : Blo 980594 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B6286031 : Blo 980594 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B25194239 : Blo 980594 25194239 := bstep (se 1 (by rfl) ⟨18895679, by rfl⟩ : syracuseStep 25194239 = 37791359) B37791359
theorem B2487095 : Blo 980594 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B1471799 : Blo 980594 1471799 := bstep (se 1 (by rfl) ⟨1103849, by rfl⟩ : syracuseStep 1471799 = 2207699) B2207699
theorem B980711 : Blo 980594 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B4980041 : Blo 980594 4980041 := bstep (se 2 (by rfl) ⟨1867515, by rfl⟩ : syracuseStep 4980041 = 3735031) B3735031
theorem B2359039 : Blo 980594 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B983911 : Blo 980594 983911 := bstep (se 1 (by rfl) ⟨737933, by rfl⟩ : syracuseStep 983911 = 1475867) B1475867
theorem B983999 : Blo 980594 983999 := bstep (se 1 (by rfl) ⟨737999, by rfl⟩ : syracuseStep 983999 = 1475999) B1475999
theorem B1476143 : Blo 980594 1476143 := bstep (se 1 (by rfl) ⟨1107107, by rfl⟩ : syracuseStep 1476143 = 2214215) B2214215
theorem B15140519 : Blo 980594 15140519 := bstep (se 1 (by rfl) ⟨11355389, by rfl⟩ : syracuseStep 15140519 = 22710779) B22710779
theorem B3149999 : Blo 980594 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B14164379 : Blo 980594 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B23865023 : Blo 980594 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B3320027 : Blo 980594 3320027 := bstep (se 1 (by rfl) ⟨2490020, by rfl⟩ : syracuseStep 3320027 = 4980041) B4980041
theorem B2209769 : Blo 980594 2209769 := bstep (se 2 (by rfl) ⟨828663, by rfl⟩ : syracuseStep 2209769 = 1657327) B1657327
theorem B2213279 : Blo 980594 2213279 := bstep (se 1 (by rfl) ⟨1659959, by rfl⟩ : syracuseStep 2213279 = 3319919) B3319919
theorem B16796159 : Blo 980594 16796159 := bstep (se 1 (by rfl) ⟨12597119, by rfl⟩ : syracuseStep 16796159 = 25194239) B25194239
theorem B1658063 : Blo 980594 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B8377303 : Blo 980594 8377303 := bstep (se 1 (by rfl) ⟨6282977, by rfl⟩ : syracuseStep 8377303 = 12565955) B12565955
theorem B21224425 : Blo 980594 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B43081321 : Blo 980594 43081321 := bstep (se 2 (by rfl) ⟨16155495, by rfl⟩ : syracuseStep 43081321 = 32310991) B32310991
theorem B3727529 : Blo 980594 3727529 := bstep (se 2 (by rfl) ⟨1397823, by rfl⟩ : syracuseStep 3727529 = 2795647) B2795647
theorem B5595439 : Blo 980594 5595439 := bstep (se 1 (by rfl) ⟨4196579, by rfl⟩ : syracuseStep 5595439 = 8393159) B8393159
theorem B15131279 : Blo 980594 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B4973399 : Blo 980594 4973399 := bstep (se 1 (by rfl) ⟨3730049, by rfl⟩ : syracuseStep 4973399 = 7460099) B7460099
theorem B4974695 : Blo 980594 4974695 := bstep (se 1 (by rfl) ⟨3731021, by rfl⟩ : syracuseStep 4974695 = 7462043) B7462043
theorem B4483745 : Blo 980594 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B4190687 : Blo 980594 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B981199 : Blo 980594 981199 := bstep (se 1 (by rfl) ⟨735899, by rfl⟩ : syracuseStep 981199 = 1471799) B1471799
theorem B1472831 : Blo 980594 1472831 := bstep (se 1 (by rfl) ⟨1104623, by rfl⟩ : syracuseStep 1472831 = 2209247) B2209247
theorem B1473119 : Blo 980594 1473119 := bstep (se 1 (by rfl) ⟨1104839, by rfl⟩ : syracuseStep 1473119 = 2209679) B2209679
theorem B3145385 : Blo 980594 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B1474217 : Blo 980594 1474217 := bstep (se 2 (by rfl) ⟨552831, by rfl⟩ : syracuseStep 1474217 = 1105663) B1105663
theorem B1475519 : Blo 980594 1475519 := bstep (se 1 (by rfl) ⟨1106639, by rfl⟩ : syracuseStep 1475519 = 2213279) B2213279
theorem B984095 : Blo 980594 984095 := bstep (se 1 (by rfl) ⟨738071, by rfl⟩ : syracuseStep 984095 = 1476143) B1476143
theorem B10093679 : Blo 980594 10093679 := bstep (se 1 (by rfl) ⟨7570259, by rfl⟩ : syracuseStep 10093679 = 15140519) B15140519
theorem B2099999 : Blo 980594 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B9442919 : Blo 980594 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B3315599 : Blo 980594 3315599 := bstep (se 1 (by rfl) ⟨2486699, by rfl⟩ : syracuseStep 3315599 = 4973399) B4973399
theorem B3316463 : Blo 980594 3316463 := bstep (se 1 (by rfl) ⟨2487347, by rfl⟩ : syracuseStep 3316463 = 4974695) B4974695
theorem B2989163 : Blo 980594 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B2793791 : Blo 980594 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B15910015 : Blo 980594 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B2213351 : Blo 980594 2213351 := bstep (se 1 (by rfl) ⟨1660013, by rfl⟩ : syracuseStep 2213351 = 3320027) B3320027
theorem B28299233 : Blo 980594 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B7460585 : Blo 980594 7460585 := bstep (se 2 (by rfl) ⟨2797719, by rfl⟩ : syracuseStep 7460585 = 5595439) B5595439
theorem B11197439 : Blo 980594 11197439 := bstep (se 1 (by rfl) ⟨8398079, by rfl⟩ : syracuseStep 11197439 = 16796159) B16796159
theorem B1105375 : Blo 980594 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B2485019 : Blo 980594 2485019 := bstep (se 1 (by rfl) ⟨1863764, by rfl⟩ : syracuseStep 2485019 = 3727529) B3727529
theorem B10087519 : Blo 980594 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B11169737 : Blo 980594 11169737 := bstep (se 2 (by rfl) ⟨4188651, by rfl⟩ : syracuseStep 11169737 = 8377303) B8377303
theorem B1473179 : Blo 980594 1473179 := bstep (se 1 (by rfl) ⟨1104884, by rfl⟩ : syracuseStep 1473179 = 2209769) B2209769
theorem B981887 : Blo 980594 981887 := bstep (se 1 (by rfl) ⟨736415, by rfl⟩ : syracuseStep 981887 = 1472831) B1472831
theorem B982079 : Blo 980594 982079 := bstep (se 1 (by rfl) ⟨736559, by rfl⟩ : syracuseStep 982079 = 1473119) B1473119
theorem B57441761 : Blo 980594 57441761 := bstep (se 2 (by rfl) ⟨21540660, by rfl⟩ : syracuseStep 57441761 = 43081321) B43081321
theorem B2096923 : Blo 980594 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B982811 : Blo 980594 982811 := bstep (se 1 (by rfl) ⟨737108, by rfl⟩ : syracuseStep 982811 = 1474217) B1474217
theorem B983679 : Blo 980594 983679 := bstep (se 1 (by rfl) ⟨737759, by rfl⟩ : syracuseStep 983679 = 1475519) B1475519
theorem B1475567 : Blo 980594 1475567 := bstep (se 1 (by rfl) ⟨1106675, by rfl⟩ : syracuseStep 1475567 = 2213351) B2213351
theorem B7446491 : Blo 980594 7446491 := bstep (se 1 (by rfl) ⟨5584868, by rfl⟩ : syracuseStep 7446491 = 11169737) B11169737
theorem B2795897 : Blo 980594 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B6729119 : Blo 980594 6729119 := bstep (se 1 (by rfl) ⟨5046839, by rfl⟩ : syracuseStep 6729119 = 10093679) B10093679
theorem B21213353 : Blo 980594 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B2210399 : Blo 980594 2210399 := bstep (se 1 (by rfl) ⟨1657799, by rfl⟩ : syracuseStep 2210399 = 3315599) B3315599
theorem B13450025 : Blo 980594 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B25181117 : Blo 980594 25181117 := bstep (se 3 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 25181117 = 9442919) B9442919
theorem B2210975 : Blo 980594 2210975 := bstep (se 1 (by rfl) ⟨1658231, by rfl⟩ : syracuseStep 2210975 = 3316463) B3316463
theorem B1656679 : Blo 980594 1656679 := bstep (se 1 (by rfl) ⟨1242509, by rfl⟩ : syracuseStep 1656679 = 2485019) B2485019
theorem B38294507 : Blo 980594 38294507 := bstep (se 1 (by rfl) ⟨28720880, by rfl⟩ : syracuseStep 38294507 = 57441761) B57441761
theorem B1399999 : Blo 980594 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B18866155 : Blo 980594 18866155 := bstep (se 1 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 18866155 = 28299233) B28299233
theorem B4973723 : Blo 980594 4973723 := bstep (se 1 (by rfl) ⟨3730292, by rfl⟩ : syracuseStep 4973723 = 7460585) B7460585
theorem B7464959 : Blo 980594 7464959 := bstep (se 1 (by rfl) ⟨5598719, by rfl⟩ : syracuseStep 7464959 = 11197439) B11197439
theorem B1992775 : Blo 980594 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B1862527 : Blo 980594 1862527 := bstep (se 1 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 1862527 = 2793791) B2793791
theorem B982119 : Blo 980594 982119 := bstep (se 1 (by rfl) ⟨736589, by rfl⟩ : syracuseStep 982119 = 1473179) B1473179
theorem B1473833 : Blo 980594 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B983711 : Blo 980594 983711 := bstep (se 1 (by rfl) ⟨737783, by rfl⟩ : syracuseStep 983711 = 1475567) B1475567
theorem B2657033 : Blo 980594 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B25529671 : Blo 980594 25529671 := bstep (se 1 (by rfl) ⟨19147253, by rfl⟩ : syracuseStep 25529671 = 38294507) B38294507
theorem B3315815 : Blo 980594 3315815 := bstep (se 1 (by rfl) ⟨2486861, by rfl⟩ : syracuseStep 3315815 = 4973723) B4973723
theorem B16787411 : Blo 980594 16787411 := bstep (se 1 (by rfl) ⟨12590558, by rfl⟩ : syracuseStep 16787411 = 25181117) B25181117
theorem B56568941 : Blo 980594 56568941 := bstep (se 3 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 56568941 = 21213353) B21213353
theorem B2208905 : Blo 980594 2208905 := bstep (se 2 (by rfl) ⟨828339, by rfl⟩ : syracuseStep 2208905 = 1656679) B1656679
theorem B4964327 : Blo 980594 4964327 := bstep (se 1 (by rfl) ⟨3723245, by rfl⟩ : syracuseStep 4964327 = 7446491) B7446491
theorem B7455725 : Blo 980594 7455725 := bstep (se 3 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 7455725 = 2795897) B2795897
theorem B8966683 : Blo 980594 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B25154873 : Blo 980594 25154873 := bstep (se 2 (by rfl) ⟨9433077, by rfl⟩ : syracuseStep 25154873 = 18866155) B18866155
theorem B2483369 : Blo 980594 2483369 := bstep (se 2 (by rfl) ⟨931263, by rfl⟩ : syracuseStep 2483369 = 1862527) B1862527
theorem B4976639 : Blo 980594 4976639 := bstep (se 1 (by rfl) ⟨3732479, by rfl⟩ : syracuseStep 4976639 = 7464959) B7464959
theorem B4486079 : Blo 980594 4486079 := bstep (se 1 (by rfl) ⟨3364559, by rfl⟩ : syracuseStep 4486079 = 6729119) B6729119
theorem B1866665 : Blo 980594 1866665 := bstep (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) B1399999
theorem B1473599 : Blo 980594 1473599 := bstep (se 1 (by rfl) ⟨1105199, by rfl⟩ : syracuseStep 1473599 = 2210399) B2210399
theorem B1473983 : Blo 980594 1473983 := bstep (se 1 (by rfl) ⟨1105487, by rfl⟩ : syracuseStep 1473983 = 2210975) B2210975
theorem B982555 : Blo 980594 982555 := bstep (se 1 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 982555 = 1473833) B1473833
theorem B1771355 : Blo 980594 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B3317759 : Blo 980594 3317759 := bstep (se 1 (by rfl) ⟨2488319, by rfl⟩ : syracuseStep 3317759 = 4976639) B4976639
theorem B2990719 : Blo 980594 2990719 := bstep (se 1 (by rfl) ⟨2243039, by rfl⟩ : syracuseStep 2990719 = 4486079) B4486079
theorem B47822309 : Blo 980594 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B2210543 : Blo 980594 2210543 := bstep (se 1 (by rfl) ⟨1657907, by rfl⟩ : syracuseStep 2210543 = 3315815) B3315815
theorem B1655579 : Blo 980594 1655579 := bstep (se 1 (by rfl) ⟨1241684, by rfl⟩ : syracuseStep 1655579 = 2483369) B2483369
theorem B11191607 : Blo 980594 11191607 := bstep (se 1 (by rfl) ⟨8393705, by rfl⟩ : syracuseStep 11191607 = 16787411) B16787411
theorem B4970483 : Blo 980594 4970483 := bstep (se 1 (by rfl) ⟨3727862, by rfl⟩ : syracuseStep 4970483 = 7455725) B7455725
theorem B16769915 : Blo 980594 16769915 := bstep (se 1 (by rfl) ⟨12577436, by rfl⟩ : syracuseStep 16769915 = 25154873) B25154873
theorem B34039561 : Blo 980594 34039561 := bstep (se 2 (by rfl) ⟨12764835, by rfl⟩ : syracuseStep 34039561 = 25529671) B25529671
theorem B37712627 : Blo 980594 37712627 := bstep (se 1 (by rfl) ⟨28284470, by rfl⟩ : syracuseStep 37712627 = 56568941) B56568941
theorem B4977773 : Blo 980594 4977773 := bstep (se 3 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 4977773 = 1866665) B1866665
theorem B1472603 : Blo 980594 1472603 := bstep (se 1 (by rfl) ⟨1104452, by rfl⟩ : syracuseStep 1472603 = 2208905) B2208905
theorem B982399 : Blo 980594 982399 := bstep (se 1 (by rfl) ⟨736799, by rfl⟩ : syracuseStep 982399 = 1473599) B1473599
theorem B982655 : Blo 980594 982655 := bstep (se 1 (by rfl) ⟨736991, by rfl⟩ : syracuseStep 982655 = 1473983) B1473983
theorem B3309551 : Blo 980594 3309551 := bstep (se 1 (by rfl) ⟨2482163, by rfl⟩ : syracuseStep 3309551 = 4964327) B4964327
theorem B45386081 : Blo 980594 45386081 := bstep (se 2 (by rfl) ⟨17019780, by rfl⟩ : syracuseStep 45386081 = 34039561) B34039561
theorem B3313655 : Blo 980594 3313655 := bstep (se 1 (by rfl) ⟨2485241, by rfl⟩ : syracuseStep 3313655 = 4970483) B4970483
theorem B4723613 : Blo 980594 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B11179943 : Blo 980594 11179943 := bstep (se 1 (by rfl) ⟨8384957, by rfl⟩ : syracuseStep 11179943 = 16769915) B16769915
theorem B25141751 : Blo 980594 25141751 := bstep (se 1 (by rfl) ⟨18856313, by rfl⟩ : syracuseStep 25141751 = 37712627) B37712627
theorem B3318515 : Blo 980594 3318515 := bstep (se 1 (by rfl) ⟨2488886, by rfl⟩ : syracuseStep 3318515 = 4977773) B4977773
theorem B2206367 : Blo 980594 2206367 := bstep (se 1 (by rfl) ⟨1654775, by rfl⟩ : syracuseStep 2206367 = 3309551) B3309551
theorem B2211839 : Blo 980594 2211839 := bstep (se 1 (by rfl) ⟨1658879, by rfl⟩ : syracuseStep 2211839 = 3317759) B3317759
theorem B1103719 : Blo 980594 1103719 := bstep (se 1 (by rfl) ⟨827789, by rfl⟩ : syracuseStep 1103719 = 1655579) B1655579
theorem B3987625 : Blo 980594 3987625 := bstep (se 2 (by rfl) ⟨1495359, by rfl⟩ : syracuseStep 3987625 = 2990719) B2990719
theorem B7461071 : Blo 980594 7461071 := bstep (se 1 (by rfl) ⟨5595803, by rfl⟩ : syracuseStep 7461071 = 11191607) B11191607
theorem B31881539 : Blo 980594 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B981735 : Blo 980594 981735 := bstep (se 1 (by rfl) ⟨736301, by rfl⟩ : syracuseStep 981735 = 1472603) B1472603
theorem B1473695 : Blo 980594 1473695 := bstep (se 1 (by rfl) ⟨1105271, by rfl⟩ : syracuseStep 1473695 = 2210543) B2210543
theorem B3149075 : Blo 980594 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B5316833 : Blo 980594 5316833 := bstep (se 2 (by rfl) ⟨1993812, by rfl⟩ : syracuseStep 5316833 = 3987625) B3987625
theorem B30257387 : Blo 980594 30257387 := bstep (se 1 (by rfl) ⟨22693040, by rfl⟩ : syracuseStep 30257387 = 45386081) B45386081
theorem B2209103 : Blo 980594 2209103 := bstep (se 1 (by rfl) ⟨1656827, by rfl⟩ : syracuseStep 2209103 = 3313655) B3313655
theorem B7453295 : Blo 980594 7453295 := bstep (se 1 (by rfl) ⟨5589971, by rfl⟩ : syracuseStep 7453295 = 11179943) B11179943
theorem B16761167 : Blo 980594 16761167 := bstep (se 1 (by rfl) ⟨12570875, by rfl⟩ : syracuseStep 16761167 = 25141751) B25141751
theorem B2212343 : Blo 980594 2212343 := bstep (se 1 (by rfl) ⟨1659257, by rfl⟩ : syracuseStep 2212343 = 3318515) B3318515
theorem B21254359 : Blo 980594 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B4974047 : Blo 980594 4974047 := bstep (se 1 (by rfl) ⟨3730535, by rfl⟩ : syracuseStep 4974047 = 7461071) B7461071
theorem B1470911 : Blo 980594 1470911 := bstep (se 1 (by rfl) ⟨1103183, by rfl⟩ : syracuseStep 1470911 = 2206367) B2206367
theorem B1471625 : Blo 980594 1471625 := bstep (se 2 (by rfl) ⟨551859, by rfl⟩ : syracuseStep 1471625 = 1103719) B1103719
theorem B982463 : Blo 980594 982463 := bstep (se 1 (by rfl) ⟨736847, by rfl⟩ : syracuseStep 982463 = 1473695) B1473695
theorem B1474559 : Blo 980594 1474559 := bstep (se 1 (by rfl) ⟨1105919, by rfl⟩ : syracuseStep 1474559 = 2211839) B2211839
theorem B11174111 : Blo 980594 11174111 := bstep (se 1 (by rfl) ⟨8380583, by rfl⟩ : syracuseStep 11174111 = 16761167) B16761167
theorem B1474895 : Blo 980594 1474895 := bstep (se 1 (by rfl) ⟨1106171, by rfl⟩ : syracuseStep 1474895 = 2212343) B2212343
theorem B3544555 : Blo 980594 3544555 := bstep (se 1 (by rfl) ⟨2658416, by rfl⟩ : syracuseStep 3544555 = 5316833) B5316833
theorem B3316031 : Blo 980594 3316031 := bstep (se 1 (by rfl) ⟨2487023, by rfl⟩ : syracuseStep 3316031 = 4974047) B4974047
theorem B8397533 : Blo 980594 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B20171591 : Blo 980594 20171591 := bstep (se 1 (by rfl) ⟨15128693, by rfl⟩ : syracuseStep 20171591 = 30257387) B30257387
theorem B4968863 : Blo 980594 4968863 := bstep (se 1 (by rfl) ⟨3726647, by rfl⟩ : syracuseStep 4968863 = 7453295) B7453295
theorem B28339145 : Blo 980594 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B980607 : Blo 980594 980607 := bstep (se 1 (by rfl) ⟨735455, by rfl⟩ : syracuseStep 980607 = 1470911) B1470911
theorem B983039 : Blo 980594 983039 := bstep (se 1 (by rfl) ⟨737279, by rfl⟩ : syracuseStep 983039 = 1474559) B1474559
theorem B981083 : Blo 980594 981083 := bstep (se 1 (by rfl) ⟨735812, by rfl⟩ : syracuseStep 981083 = 1471625) B1471625
theorem B1472735 : Blo 980594 1472735 := bstep (se 1 (by rfl) ⟨1104551, by rfl⟩ : syracuseStep 1472735 = 2209103) B2209103
theorem B983263 : Blo 980594 983263 := bstep (se 1 (by rfl) ⟨737447, by rfl⟩ : syracuseStep 983263 = 1474895) B1474895
theorem B3312575 : Blo 980594 3312575 := bstep (se 1 (by rfl) ⟨2484431, by rfl⟩ : syracuseStep 3312575 = 4968863) B4968863
theorem B4726073 : Blo 980594 4726073 := bstep (se 2 (by rfl) ⟨1772277, by rfl⟩ : syracuseStep 4726073 = 3544555) B3544555
theorem B7449407 : Blo 980594 7449407 := bstep (se 1 (by rfl) ⟨5587055, by rfl⟩ : syracuseStep 7449407 = 11174111) B11174111
theorem B13447727 : Blo 980594 13447727 := bstep (se 1 (by rfl) ⟨10085795, by rfl⟩ : syracuseStep 13447727 = 20171591) B20171591
theorem B2210687 : Blo 980594 2210687 := bstep (se 1 (by rfl) ⟨1658015, by rfl⟩ : syracuseStep 2210687 = 3316031) B3316031
theorem B18892763 : Blo 980594 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B5598355 : Blo 980594 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B981823 : Blo 980594 981823 := bstep (se 1 (by rfl) ⟨736367, by rfl⟩ : syracuseStep 981823 = 1472735) B1472735
theorem B12595175 : Blo 980594 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B2208383 : Blo 980594 2208383 := bstep (se 1 (by rfl) ⟨1656287, by rfl⟩ : syracuseStep 2208383 = 3312575) B3312575
theorem B4966271 : Blo 980594 4966271 := bstep (se 1 (by rfl) ⟨3724703, by rfl⟩ : syracuseStep 4966271 = 7449407) B7449407
theorem B8965151 : Blo 980594 8965151 := bstep (se 1 (by rfl) ⟨6723863, by rfl⟩ : syracuseStep 8965151 = 13447727) B13447727
theorem B12602861 : Blo 980594 12602861 := bstep (se 3 (by rfl) ⟨2363036, by rfl⟩ : syracuseStep 12602861 = 4726073) B4726073
theorem B7464473 : Blo 980594 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B1473791 : Blo 980594 1473791 := bstep (se 1 (by rfl) ⟨1105343, by rfl⟩ : syracuseStep 1473791 = 2210687) B2210687
theorem B3310847 : Blo 980594 3310847 := bstep (se 1 (by rfl) ⟨2483135, by rfl⟩ : syracuseStep 3310847 = 4966271) B4966271
theorem B8396783 : Blo 980594 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B5976767 : Blo 980594 5976767 := bstep (se 1 (by rfl) ⟨4482575, by rfl⟩ : syracuseStep 5976767 = 8965151) B8965151
theorem B8401907 : Blo 980594 8401907 := bstep (se 1 (by rfl) ⟨6301430, by rfl⟩ : syracuseStep 8401907 = 12602861) B12602861
theorem B4976315 : Blo 980594 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B1472255 : Blo 980594 1472255 := bstep (se 1 (by rfl) ⟨1104191, by rfl⟩ : syracuseStep 1472255 = 2208383) B2208383
theorem B982527 : Blo 980594 982527 := bstep (se 1 (by rfl) ⟨736895, by rfl⟩ : syracuseStep 982527 = 1473791) B1473791
theorem B3317543 : Blo 980594 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B2207231 : Blo 980594 2207231 := bstep (se 1 (by rfl) ⟨1655423, by rfl⟩ : syracuseStep 2207231 = 3310847) B3310847
theorem B15938045 : Blo 980594 15938045 := bstep (se 3 (by rfl) ⟨2988383, by rfl⟩ : syracuseStep 15938045 = 5976767) B5976767
theorem B5597855 : Blo 980594 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B5601271 : Blo 980594 5601271 := bstep (se 1 (by rfl) ⟨4200953, by rfl⟩ : syracuseStep 5601271 = 8401907) B8401907
theorem B981503 : Blo 980594 981503 := bstep (se 1 (by rfl) ⟨736127, by rfl⟩ : syracuseStep 981503 = 1472255) B1472255
theorem B10625363 : Blo 980594 10625363 := bstep (se 1 (by rfl) ⟨7969022, by rfl⟩ : syracuseStep 10625363 = 15938045) B15938045
theorem B2211695 : Blo 980594 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B3731903 : Blo 980594 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B1471487 : Blo 980594 1471487 := bstep (se 1 (by rfl) ⟨1103615, by rfl⟩ : syracuseStep 1471487 = 2207231) B2207231
theorem B7468361 : Blo 980594 7468361 := bstep (se 2 (by rfl) ⟨2800635, by rfl⟩ : syracuseStep 7468361 = 5601271) B5601271
theorem B7083575 : Blo 980594 7083575 := bstep (se 1 (by rfl) ⟨5312681, by rfl⟩ : syracuseStep 7083575 = 10625363) B10625363
theorem B2487935 : Blo 980594 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B980991 : Blo 980594 980991 := bstep (se 1 (by rfl) ⟨735743, by rfl⟩ : syracuseStep 980991 = 1471487) B1471487
theorem B4978907 : Blo 980594 4978907 := bstep (se 1 (by rfl) ⟨3734180, by rfl⟩ : syracuseStep 4978907 = 7468361) B7468361
theorem B1474463 : Blo 980594 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B4722383 : Blo 980594 4722383 := bstep (se 1 (by rfl) ⟨3541787, by rfl⟩ : syracuseStep 4722383 = 7083575) B7083575
theorem B3319271 : Blo 980594 3319271 := bstep (se 1 (by rfl) ⟨2489453, by rfl⟩ : syracuseStep 3319271 = 4978907) B4978907
theorem B1658623 : Blo 980594 1658623 := bstep (se 1 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 1658623 = 2487935) B2487935
theorem B982975 : Blo 980594 982975 := bstep (se 1 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 982975 = 1474463) B1474463
theorem B3148255 : Blo 980594 3148255 := bstep (se 1 (by rfl) ⟨2361191, by rfl⟩ : syracuseStep 3148255 = 4722383) B4722383
theorem B2211497 : Blo 980594 2211497 := bstep (se 2 (by rfl) ⟨829311, by rfl⟩ : syracuseStep 2211497 = 1658623) B1658623
theorem B2212847 : Blo 980594 2212847 := bstep (se 1 (by rfl) ⟨1659635, by rfl⟩ : syracuseStep 2212847 = 3319271) B3319271
theorem B1475231 : Blo 980594 1475231 := bstep (se 1 (by rfl) ⟨1106423, by rfl⟩ : syracuseStep 1475231 = 2212847) B2212847
theorem B4197673 : Blo 980594 4197673 := bstep (se 2 (by rfl) ⟨1574127, by rfl⟩ : syracuseStep 4197673 = 3148255) B3148255
theorem B1474331 : Blo 980594 1474331 := bstep (se 1 (by rfl) ⟨1105748, by rfl⟩ : syracuseStep 1474331 = 2211497) B2211497
theorem B983487 : Blo 980594 983487 := bstep (se 1 (by rfl) ⟨737615, by rfl⟩ : syracuseStep 983487 = 1475231) B1475231
theorem B5596897 : Blo 980594 5596897 := bstep (se 2 (by rfl) ⟨2098836, by rfl⟩ : syracuseStep 5596897 = 4197673) B4197673
theorem B982887 : Blo 980594 982887 := bstep (se 1 (by rfl) ⟨737165, by rfl⟩ : syracuseStep 982887 = 1474331) B1474331
theorem B7462529 : Blo 980594 7462529 := bstep (se 2 (by rfl) ⟨2798448, by rfl⟩ : syracuseStep 7462529 = 5596897) B5596897
theorem B4975019 : Blo 980594 4975019 := bstep (se 1 (by rfl) ⟨3731264, by rfl⟩ : syracuseStep 4975019 = 7462529) B7462529
theorem B3316679 : Blo 980594 3316679 := bstep (se 1 (by rfl) ⟨2487509, by rfl⟩ : syracuseStep 3316679 = 4975019) B4975019
theorem B2211119 : Blo 980594 2211119 := bstep (se 1 (by rfl) ⟨1658339, by rfl⟩ : syracuseStep 2211119 = 3316679) B3316679
theorem B1474079 : Blo 980594 1474079 := bstep (se 1 (by rfl) ⟨1105559, by rfl⟩ : syracuseStep 1474079 = 2211119) B2211119
theorem B982719 : Blo 980594 982719 := bstep (se 1 (by rfl) ⟨737039, by rfl⟩ : syracuseStep 982719 = 1474079) B1474079

theorem C0 (j : ℕ) (h1 : 245148 ≤ j) (h2 : j ≤ 245847) : Blo 980594 (4 * j + 3) := by
  interval_cases j
  · exact B980595
  · exact B980599
  · exact B980603
  · exact B980607
  · exact B980611
  · exact B980615
  · exact B980619
  · exact B980623
  · exact B980627
  · exact B980631
  · exact B980635
  · exact B980639
  · exact B980643
  · exact B980647
  · exact B980651
  · exact B980655
  · exact B980659
  · exact B980663
  · exact B980667
  · exact B980671
  · exact B980675
  · exact B980679
  · exact B980683
  · exact B980687
  · exact B980691
  · exact B980695
  · exact B980699
  · exact B980703
  · exact B980707
  · exact B980711
  · exact B980715
  · exact B980719
  · exact B980723
  · exact B980727
  · exact B980731
  · exact B980735
  · exact B980739
  · exact B980743
  · exact B980747
  · exact B980751
  · exact B980755
  · exact B980759
  · exact B980763
  · exact B980767
  · exact B980771
  · exact B980775
  · exact B980779
  · exact B980783
  · exact B980787
  · exact B980791
  · exact B980795
  · exact B980799
  · exact B980803
  · exact B980807
  · exact B980811
  · exact B980815
  · exact B980819
  · exact B980823
  · exact B980827
  · exact B980831
  · exact B980835
  · exact B980839
  · exact B980843
  · exact B980847
  · exact B980851
  · exact B980855
  · exact B980859
  · exact B980863
  · exact B980867
  · exact B980871
  · exact B980875
  · exact B980879
  · exact B980883
  · exact B980887
  · exact B980891
  · exact B980895
  · exact B980899
  · exact B980903
  · exact B980907
  · exact B980911
  · exact B980915
  · exact B980919
  · exact B980923
  · exact B980927
  · exact B980931
  · exact B980935
  · exact B980939
  · exact B980943
  · exact B980947
  · exact B980951
  · exact B980955
  · exact B980959
  · exact B980963
  · exact B980967
  · exact B980971
  · exact B980975
  · exact B980979
  · exact B980983
  · exact B980987
  · exact B980991
  · exact B980995
  · exact B980999
  · exact B981003
  · exact B981007
  · exact B981011
  · exact B981015
  · exact B981019
  · exact B981023
  · exact B981027
  · exact B981031
  · exact B981035
  · exact B981039
  · exact B981043
  · exact B981047
  · exact B981051
  · exact B981055
  · exact B981059
  · exact B981063
  · exact B981067
  · exact B981071
  · exact B981075
  · exact B981079
  · exact B981083
  · exact B981087
  · exact B981091
  · exact B981095
  · exact B981099
  · exact B981103
  · exact B981107
  · exact B981111
  · exact B981115
  · exact B981119
  · exact B981123
  · exact B981127
  · exact B981131
  · exact B981135
  · exact B981139
  · exact B981143
  · exact B981147
  · exact B981151
  · exact B981155
  · exact B981159
  · exact B981163
  · exact B981167
  · exact B981171
  · exact B981175
  · exact B981179
  · exact B981183
  · exact B981187
  · exact B981191
  · exact B981195
  · exact B981199
  · exact B981203
  · exact B981207
  · exact B981211
  · exact B981215
  · exact B981219
  · exact B981223
  · exact B981227
  · exact B981231
  · exact B981235
  · exact B981239
  · exact B981243
  · exact B981247
  · exact B981251
  · exact B981255
  · exact B981259
  · exact B981263
  · exact B981267
  · exact B981271
  · exact B981275
  · exact B981279
  · exact B981283
  · exact B981287
  · exact B981291
  · exact B981295
  · exact B981299
  · exact B981303
  · exact B981307
  · exact B981311
  · exact B981315
  · exact B981319
  · exact B981323
  · exact B981327
  · exact B981331
  · exact B981335
  · exact B981339
  · exact B981343
  · exact B981347
  · exact B981351
  · exact B981355
  · exact B981359
  · exact B981363
  · exact B981367
  · exact B981371
  · exact B981375
  · exact B981379
  · exact B981383
  · exact B981387
  · exact B981391
  · exact B981395
  · exact B981399
  · exact B981403
  · exact B981407
  · exact B981411
  · exact B981415
  · exact B981419
  · exact B981423
  · exact B981427
  · exact B981431
  · exact B981435
  · exact B981439
  · exact B981443
  · exact B981447
  · exact B981451
  · exact B981455
  · exact B981459
  · exact B981463
  · exact B981467
  · exact B981471
  · exact B981475
  · exact B981479
  · exact B981483
  · exact B981487
  · exact B981491
  · exact B981495
  · exact B981499
  · exact B981503
  · exact B981507
  · exact B981511
  · exact B981515
  · exact B981519
  · exact B981523
  · exact B981527
  · exact B981531
  · exact B981535
  · exact B981539
  · exact B981543
  · exact B981547
  · exact B981551
  · exact B981555
  · exact B981559
  · exact B981563
  · exact B981567
  · exact B981571
  · exact B981575
  · exact B981579
  · exact B981583
  · exact B981587
  · exact B981591
  · exact B981595
  · exact B981599
  · exact B981603
  · exact B981607
  · exact B981611
  · exact B981615
  · exact B981619
  · exact B981623
  · exact B981627
  · exact B981631
  · exact B981635
  · exact B981639
  · exact B981643
  · exact B981647
  · exact B981651
  · exact B981655
  · exact B981659
  · exact B981663
  · exact B981667
  · exact B981671
  · exact B981675
  · exact B981679
  · exact B981683
  · exact B981687
  · exact B981691
  · exact B981695
  · exact B981699
  · exact B981703
  · exact B981707
  · exact B981711
  · exact B981715
  · exact B981719
  · exact B981723
  · exact B981727
  · exact B981731
  · exact B981735
  · exact B981739
  · exact B981743
  · exact B981747
  · exact B981751
  · exact B981755
  · exact B981759
  · exact B981763
  · exact B981767
  · exact B981771
  · exact B981775
  · exact B981779
  · exact B981783
  · exact B981787
  · exact B981791
  · exact B981795
  · exact B981799
  · exact B981803
  · exact B981807
  · exact B981811
  · exact B981815
  · exact B981819
  · exact B981823
  · exact B981827
  · exact B981831
  · exact B981835
  · exact B981839
  · exact B981843
  · exact B981847
  · exact B981851
  · exact B981855
  · exact B981859
  · exact B981863
  · exact B981867
  · exact B981871
  · exact B981875
  · exact B981879
  · exact B981883
  · exact B981887
  · exact B981891
  · exact B981895
  · exact B981899
  · exact B981903
  · exact B981907
  · exact B981911
  · exact B981915
  · exact B981919
  · exact B981923
  · exact B981927
  · exact B981931
  · exact B981935
  · exact B981939
  · exact B981943
  · exact B981947
  · exact B981951
  · exact B981955
  · exact B981959
  · exact B981963
  · exact B981967
  · exact B981971
  · exact B981975
  · exact B981979
  · exact B981983
  · exact B981987
  · exact B981991
  · exact B981995
  · exact B981999
  · exact B982003
  · exact B982007
  · exact B982011
  · exact B982015
  · exact B982019
  · exact B982023
  · exact B982027
  · exact B982031
  · exact B982035
  · exact B982039
  · exact B982043
  · exact B982047
  · exact B982051
  · exact B982055
  · exact B982059
  · exact B982063
  · exact B982067
  · exact B982071
  · exact B982075
  · exact B982079
  · exact B982083
  · exact B982087
  · exact B982091
  · exact B982095
  · exact B982099
  · exact B982103
  · exact B982107
  · exact B982111
  · exact B982115
  · exact B982119
  · exact B982123
  · exact B982127
  · exact B982131
  · exact B982135
  · exact B982139
  · exact B982143
  · exact B982147
  · exact B982151
  · exact B982155
  · exact B982159
  · exact B982163
  · exact B982167
  · exact B982171
  · exact B982175
  · exact B982179
  · exact B982183
  · exact B982187
  · exact B982191
  · exact B982195
  · exact B982199
  · exact B982203
  · exact B982207
  · exact B982211
  · exact B982215
  · exact B982219
  · exact B982223
  · exact B982227
  · exact B982231
  · exact B982235
  · exact B982239
  · exact B982243
  · exact B982247
  · exact B982251
  · exact B982255
  · exact B982259
  · exact B982263
  · exact B982267
  · exact B982271
  · exact B982275
  · exact B982279
  · exact B982283
  · exact B982287
  · exact B982291
  · exact B982295
  · exact B982299
  · exact B982303
  · exact B982307
  · exact B982311
  · exact B982315
  · exact B982319
  · exact B982323
  · exact B982327
  · exact B982331
  · exact B982335
  · exact B982339
  · exact B982343
  · exact B982347
  · exact B982351
  · exact B982355
  · exact B982359
  · exact B982363
  · exact B982367
  · exact B982371
  · exact B982375
  · exact B982379
  · exact B982383
  · exact B982387
  · exact B982391
  · exact B982395
  · exact B982399
  · exact B982403
  · exact B982407
  · exact B982411
  · exact B982415
  · exact B982419
  · exact B982423
  · exact B982427
  · exact B982431
  · exact B982435
  · exact B982439
  · exact B982443
  · exact B982447
  · exact B982451
  · exact B982455
  · exact B982459
  · exact B982463
  · exact B982467
  · exact B982471
  · exact B982475
  · exact B982479
  · exact B982483
  · exact B982487
  · exact B982491
  · exact B982495
  · exact B982499
  · exact B982503
  · exact B982507
  · exact B982511
  · exact B982515
  · exact B982519
  · exact B982523
  · exact B982527
  · exact B982531
  · exact B982535
  · exact B982539
  · exact B982543
  · exact B982547
  · exact B982551
  · exact B982555
  · exact B982559
  · exact B982563
  · exact B982567
  · exact B982571
  · exact B982575
  · exact B982579
  · exact B982583
  · exact B982587
  · exact B982591
  · exact B982595
  · exact B982599
  · exact B982603
  · exact B982607
  · exact B982611
  · exact B982615
  · exact B982619
  · exact B982623
  · exact B982627
  · exact B982631
  · exact B982635
  · exact B982639
  · exact B982643
  · exact B982647
  · exact B982651
  · exact B982655
  · exact B982659
  · exact B982663
  · exact B982667
  · exact B982671
  · exact B982675
  · exact B982679
  · exact B982683
  · exact B982687
  · exact B982691
  · exact B982695
  · exact B982699
  · exact B982703
  · exact B982707
  · exact B982711
  · exact B982715
  · exact B982719
  · exact B982723
  · exact B982727
  · exact B982731
  · exact B982735
  · exact B982739
  · exact B982743
  · exact B982747
  · exact B982751
  · exact B982755
  · exact B982759
  · exact B982763
  · exact B982767
  · exact B982771
  · exact B982775
  · exact B982779
  · exact B982783
  · exact B982787
  · exact B982791
  · exact B982795
  · exact B982799
  · exact B982803
  · exact B982807
  · exact B982811
  · exact B982815
  · exact B982819
  · exact B982823
  · exact B982827
  · exact B982831
  · exact B982835
  · exact B982839
  · exact B982843
  · exact B982847
  · exact B982851
  · exact B982855
  · exact B982859
  · exact B982863
  · exact B982867
  · exact B982871
  · exact B982875
  · exact B982879
  · exact B982883
  · exact B982887
  · exact B982891
  · exact B982895
  · exact B982899
  · exact B982903
  · exact B982907
  · exact B982911
  · exact B982915
  · exact B982919
  · exact B982923
  · exact B982927
  · exact B982931
  · exact B982935
  · exact B982939
  · exact B982943
  · exact B982947
  · exact B982951
  · exact B982955
  · exact B982959
  · exact B982963
  · exact B982967
  · exact B982971
  · exact B982975
  · exact B982979
  · exact B982983
  · exact B982987
  · exact B982991
  · exact B982995
  · exact B982999
  · exact B983003
  · exact B983007
  · exact B983011
  · exact B983015
  · exact B983019
  · exact B983023
  · exact B983027
  · exact B983031
  · exact B983035
  · exact B983039
  · exact B983043
  · exact B983047
  · exact B983051
  · exact B983055
  · exact B983059
  · exact B983063
  · exact B983067
  · exact B983071
  · exact B983075
  · exact B983079
  · exact B983083
  · exact B983087
  · exact B983091
  · exact B983095
  · exact B983099
  · exact B983103
  · exact B983107
  · exact B983111
  · exact B983115
  · exact B983119
  · exact B983123
  · exact B983127
  · exact B983131
  · exact B983135
  · exact B983139
  · exact B983143
  · exact B983147
  · exact B983151
  · exact B983155
  · exact B983159
  · exact B983163
  · exact B983167
  · exact B983171
  · exact B983175
  · exact B983179
  · exact B983183
  · exact B983187
  · exact B983191
  · exact B983195
  · exact B983199
  · exact B983203
  · exact B983207
  · exact B983211
  · exact B983215
  · exact B983219
  · exact B983223
  · exact B983227
  · exact B983231
  · exact B983235
  · exact B983239
  · exact B983243
  · exact B983247
  · exact B983251
  · exact B983255
  · exact B983259
  · exact B983263
  · exact B983267
  · exact B983271
  · exact B983275
  · exact B983279
  · exact B983283
  · exact B983287
  · exact B983291
  · exact B983295
  · exact B983299
  · exact B983303
  · exact B983307
  · exact B983311
  · exact B983315
  · exact B983319
  · exact B983323
  · exact B983327
  · exact B983331
  · exact B983335
  · exact B983339
  · exact B983343
  · exact B983347
  · exact B983351
  · exact B983355
  · exact B983359
  · exact B983363
  · exact B983367
  · exact B983371
  · exact B983375
  · exact B983379
  · exact B983383
  · exact B983387
  · exact B983391

theorem C1 (j : ℕ) (h1 : 245848 ≤ j) (h2 : j ≤ 246147) : Blo 980594 (4 * j + 3) := by
  interval_cases j
  · exact B983395
  · exact B983399
  · exact B983403
  · exact B983407
  · exact B983411
  · exact B983415
  · exact B983419
  · exact B983423
  · exact B983427
  · exact B983431
  · exact B983435
  · exact B983439
  · exact B983443
  · exact B983447
  · exact B983451
  · exact B983455
  · exact B983459
  · exact B983463
  · exact B983467
  · exact B983471
  · exact B983475
  · exact B983479
  · exact B983483
  · exact B983487
  · exact B983491
  · exact B983495
  · exact B983499
  · exact B983503
  · exact B983507
  · exact B983511
  · exact B983515
  · exact B983519
  · exact B983523
  · exact B983527
  · exact B983531
  · exact B983535
  · exact B983539
  · exact B983543
  · exact B983547
  · exact B983551
  · exact B983555
  · exact B983559
  · exact B983563
  · exact B983567
  · exact B983571
  · exact B983575
  · exact B983579
  · exact B983583
  · exact B983587
  · exact B983591
  · exact B983595
  · exact B983599
  · exact B983603
  · exact B983607
  · exact B983611
  · exact B983615
  · exact B983619
  · exact B983623
  · exact B983627
  · exact B983631
  · exact B983635
  · exact B983639
  · exact B983643
  · exact B983647
  · exact B983651
  · exact B983655
  · exact B983659
  · exact B983663
  · exact B983667
  · exact B983671
  · exact B983675
  · exact B983679
  · exact B983683
  · exact B983687
  · exact B983691
  · exact B983695
  · exact B983699
  · exact B983703
  · exact B983707
  · exact B983711
  · exact B983715
  · exact B983719
  · exact B983723
  · exact B983727
  · exact B983731
  · exact B983735
  · exact B983739
  · exact B983743
  · exact B983747
  · exact B983751
  · exact B983755
  · exact B983759
  · exact B983763
  · exact B983767
  · exact B983771
  · exact B983775
  · exact B983779
  · exact B983783
  · exact B983787
  · exact B983791
  · exact B983795
  · exact B983799
  · exact B983803
  · exact B983807
  · exact B983811
  · exact B983815
  · exact B983819
  · exact B983823
  · exact B983827
  · exact B983831
  · exact B983835
  · exact B983839
  · exact B983843
  · exact B983847
  · exact B983851
  · exact B983855
  · exact B983859
  · exact B983863
  · exact B983867
  · exact B983871
  · exact B983875
  · exact B983879
  · exact B983883
  · exact B983887
  · exact B983891
  · exact B983895
  · exact B983899
  · exact B983903
  · exact B983907
  · exact B983911
  · exact B983915
  · exact B983919
  · exact B983923
  · exact B983927
  · exact B983931
  · exact B983935
  · exact B983939
  · exact B983943
  · exact B983947
  · exact B983951
  · exact B983955
  · exact B983959
  · exact B983963
  · exact B983967
  · exact B983971
  · exact B983975
  · exact B983979
  · exact B983983
  · exact B983987
  · exact B983991
  · exact B983995
  · exact B983999
  · exact B984003
  · exact B984007
  · exact B984011
  · exact B984015
  · exact B984019
  · exact B984023
  · exact B984027
  · exact B984031
  · exact B984035
  · exact B984039
  · exact B984043
  · exact B984047
  · exact B984051
  · exact B984055
  · exact B984059
  · exact B984063
  · exact B984067
  · exact B984071
  · exact B984075
  · exact B984079
  · exact B984083
  · exact B984087
  · exact B984091
  · exact B984095
  · exact B984099
  · exact B984103
  · exact B984107
  · exact B984111
  · exact B984115
  · exact B984119
  · exact B984123
  · exact B984127
  · exact B984131
  · exact B984135
  · exact B984139
  · exact B984143
  · exact B984147
  · exact B984151
  · exact B984155
  · exact B984159
  · exact B984163
  · exact B984167
  · exact B984171
  · exact B984175
  · exact B984179
  · exact B984183
  · exact B984187
  · exact B984191
  · exact B984195
  · exact B984199
  · exact B984203
  · exact B984207
  · exact B984211
  · exact B984215
  · exact B984219
  · exact B984223
  · exact B984227
  · exact B984231
  · exact B984235
  · exact B984239
  · exact B984243
  · exact B984247
  · exact B984251
  · exact B984255
  · exact B984259
  · exact B984263
  · exact B984267
  · exact B984271
  · exact B984275
  · exact B984279
  · exact B984283
  · exact B984287
  · exact B984291
  · exact B984295
  · exact B984299
  · exact B984303
  · exact B984307
  · exact B984311
  · exact B984315
  · exact B984319
  · exact B984323
  · exact B984327
  · exact B984331
  · exact B984335
  · exact B984339
  · exact B984343
  · exact B984347
  · exact B984351
  · exact B984355
  · exact B984359
  · exact B984363
  · exact B984367
  · exact B984371
  · exact B984375
  · exact B984379
  · exact B984383
  · exact B984387
  · exact B984391
  · exact B984395
  · exact B984399
  · exact B984403
  · exact B984407
  · exact B984411
  · exact B984415
  · exact B984419
  · exact B984423
  · exact B984427
  · exact B984431
  · exact B984435
  · exact B984439
  · exact B984443
  · exact B984447
  · exact B984451
  · exact B984455
  · exact B984459
  · exact B984463
  · exact B984467
  · exact B984471
  · exact B984475
  · exact B984479
  · exact B984483
  · exact B984487
  · exact B984491
  · exact B984495
  · exact B984499
  · exact B984503
  · exact B984507
  · exact B984511
  · exact B984515
  · exact B984519
  · exact B984523
  · exact B984527
  · exact B984531
  · exact B984535
  · exact B984539
  · exact B984543
  · exact B984547
  · exact B984551
  · exact B984555
  · exact B984559
  · exact B984563
  · exact B984567
  · exact B984571
  · exact B984575
  · exact B984579
  · exact B984583
  · exact B984587
  · exact B984591

theorem solution (m : ℕ) (hlo : 980594 ≤ m) (hhi : m ≤ 984594) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 245148 ≤ j := by omega
    have hj2 : j ≤ 246147 := by omega
    have hb : Blo 980594 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 245848 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
