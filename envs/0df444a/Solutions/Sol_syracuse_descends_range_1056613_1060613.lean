-- Prove2me | solution 1 for syracuse_descends_range_1056613_1060613
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:27.85797+00:00
-- url     : https://prove2.me/submissions/cb9e626d-a5c0-436e-8d37-2af93c442bc3

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


theorem B3571829 : Blo 1056613 3571829 := bbase (se 5 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 3571829 = 334859) (by norm_num)
theorem B3866821 : Blo 1056613 3866821 := bbase (se 4 (by rfl) ⟨362514, by rfl⟩ : syracuseStep 3866821 = 725029) (by norm_num)
theorem B5439941 : Blo 1056613 5439941 := bbase (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) (by norm_num)
theorem B2261461 : Blo 1056613 2261461 := bbase (se 7 (by rfl) ⟨26501, by rfl⟩ : syracuseStep 2261461 = 53003) (by norm_num)
theorem B3572261 : Blo 1056613 3572261 := bbase (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) (by norm_num)
theorem B3867173 : Blo 1056613 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1508005 : Blo 1056613 1508005 := bbase (se 4 (by rfl) ⟨141375, by rfl⟩ : syracuseStep 1508005 = 282751) (by norm_num)
theorem B2261837 : Blo 1056613 2261837 := bbase (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) (by norm_num)
theorem B4522837 : Blo 1056613 4522837 := bbase (se 9 (by rfl) ⟨13250, by rfl⟩ : syracuseStep 4522837 = 26501) (by norm_num)
theorem B4522853 : Blo 1056613 4522853 := bbase (se 4 (by rfl) ⟨424017, by rfl⟩ : syracuseStep 4522853 = 848035) (by norm_num)
theorem B6030197 : Blo 1056613 6030197 := bbase (se 5 (by rfl) ⟨282665, by rfl⟩ : syracuseStep 6030197 = 565331) (by norm_num)
theorem B9044885 : Blo 1056613 9044885 := bbase (se 6 (by rfl) ⟨211989, by rfl⟩ : syracuseStep 9044885 = 423979) (by norm_num)
theorem B3015589 : Blo 1056613 3015589 := bbase (se 4 (by rfl) ⟨282711, by rfl⟩ : syracuseStep 3015589 = 565423) (by norm_num)
theorem B3572693 : Blo 1056613 3572693 := bbase (se 7 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 3572693 = 83735) (by norm_num)
theorem B8029205 : Blo 1056613 8029205 := bbase (se 6 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 8029205 = 376369) (by norm_num)
theorem B3573125 : Blo 1056613 3573125 := bbase (se 4 (by rfl) ⟨334980, by rfl⟩ : syracuseStep 3573125 = 669961) (by norm_num)
theorem B4294021 : Blo 1056613 4294021 := bbase (se 4 (by rfl) ⟨402564, by rfl⟩ : syracuseStep 4294021 = 805129) (by norm_num)
theorem B1508797 : Blo 1056613 1508797 := bbase (se 3 (by rfl) ⟨282899, by rfl⟩ : syracuseStep 1508797 = 565799) (by norm_num)
theorem B2721293 : Blo 1056613 2721293 := bbase (se 3 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 2721293 = 1020485) (by norm_num)
theorem B1509133 : Blo 1056613 1509133 := bbase (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) (by norm_num)
theorem B3573557 : Blo 1056613 3573557 := bbase (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) (by norm_num)
theorem B3868517 : Blo 1056613 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B1509349 : Blo 1056613 1509349 := bbase (se 4 (by rfl) ⟨141501, by rfl⟩ : syracuseStep 1509349 = 283003) (by norm_num)
theorem B3016693 : Blo 1056613 3016693 := bbase (se 5 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 3016693 = 282815) (by norm_num)
theorem B1837061 : Blo 1056613 1837061 := bbase (se 4 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 1837061 = 344449) (by norm_num)
theorem B6031381 : Blo 1056613 6031381 := bbase (se 6 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 6031381 = 282721) (by norm_num)
theorem B2295877 : Blo 1056613 2295877 := bbase (se 4 (by rfl) ⟨215238, by rfl⟩ : syracuseStep 2295877 = 430477) (by norm_num)
theorem B3573989 : Blo 1056613 3573989 := bbase (se 4 (by rfl) ⟨335061, by rfl⟩ : syracuseStep 3573989 = 670123) (by norm_num)
theorem B2034013 : Blo 1056613 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B1509725 : Blo 1056613 1509725 := bbase (se 3 (by rfl) ⟨283073, by rfl⟩ : syracuseStep 1509725 = 566147) (by norm_num)
theorem B2263477 : Blo 1056613 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B3213877 : Blo 1056613 3213877 := bbase (se 5 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 3213877 = 301301) (by norm_num)
theorem B3574421 : Blo 1056613 3574421 := bbase (se 6 (by rfl) ⟨83775, by rfl⟩ : syracuseStep 3574421 = 167551) (by norm_num)
theorem B3050453 : Blo 1056613 3050453 := bbase (se 7 (by rfl) ⟨35747, by rfl⟩ : syracuseStep 3050453 = 71495) (by norm_num)
theorem B1608701 : Blo 1056613 1608701 := bbase (se 3 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 1608701 = 603263) (by norm_num)
theorem B4525109 : Blo 1056613 4525109 := bbase (se 5 (by rfl) ⟨212114, by rfl⟩ : syracuseStep 4525109 = 424229) (by norm_num)
theorem B3574853 : Blo 1056613 3574853 := bbase (se 4 (by rfl) ⟨335142, by rfl⟩ : syracuseStep 3574853 = 670285) (by norm_num)
theorem B3673349 : Blo 1056613 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B2264365 : Blo 1056613 2264365 := bbase (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) (by norm_num)
theorem B4296149 : Blo 1056613 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B3018197 : Blo 1056613 3018197 := bbase (se 7 (by rfl) ⟨35369, by rfl⟩ : syracuseStep 3018197 = 70739) (by norm_num)
theorem B3575285 : Blo 1056613 3575285 := bbase (se 5 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 3575285 = 335183) (by norm_num)
theorem B4820485 : Blo 1056613 4820485 := bbase (se 4 (by rfl) ⟨451920, by rfl⟩ : syracuseStep 4820485 = 903841) (by norm_num)
theorem B2068021 : Blo 1056613 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B3215045 : Blo 1056613 3215045 := bbase (se 4 (by rfl) ⟨301410, by rfl⟩ : syracuseStep 3215045 = 602821) (by norm_num)
theorem B2264861 : Blo 1056613 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B9047861 : Blo 1056613 9047861 := bbase (se 5 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 9047861 = 848237) (by norm_num)
theorem B1740629 : Blo 1056613 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B3575717 : Blo 1056613 3575717 := bbase (se 4 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 3575717 = 670447) (by norm_num)
theorem B6033365 : Blo 1056613 6033365 := bbase (se 7 (by rfl) ⟨70703, by rfl⟩ : syracuseStep 6033365 = 141407) (by norm_num)
theorem B10850357 : Blo 1056613 10850357 := bbase (se 5 (by rfl) ⟨508610, by rfl⟩ : syracuseStep 10850357 = 1017221) (by norm_num)
theorem B6787253 : Blo 1056613 6787253 := bbase (se 5 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 6787253 = 636305) (by norm_num)
theorem B3576149 : Blo 1056613 3576149 := bbase (se 10 (by rfl) ⟨5238, by rfl⟩ : syracuseStep 3576149 = 10477) (by norm_num)
theorem B3215845 : Blo 1056613 3215845 := bbase (se 4 (by rfl) ⟨301485, by rfl⟩ : syracuseStep 3215845 = 602971) (by norm_num)
theorem B2036477 : Blo 1056613 2036477 := bbase (se 3 (by rfl) ⟨381839, by rfl⟩ : syracuseStep 2036477 = 763679) (by norm_num)
theorem B3576581 : Blo 1056613 3576581 := bbase (se 4 (by rfl) ⟨335304, by rfl⟩ : syracuseStep 3576581 = 670609) (by norm_num)
theorem B18060245 : Blo 1056613 18060245 := bbase (se 7 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 18060245 = 423287) (by norm_num)
theorem B3019781 : Blo 1056613 3019781 := bbase (se 4 (by rfl) ⟨283104, by rfl⟩ : syracuseStep 3019781 = 566209) (by norm_num)
theorem B1905709 : Blo 1056613 1905709 := bbase (se 3 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 1905709 = 714641) (by norm_num)
theorem B1610813 : Blo 1056613 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B3577013 : Blo 1056613 3577013 := bbase (se 5 (by rfl) ⟨167672, by rfl⟩ : syracuseStep 3577013 = 335345) (by norm_num)
theorem B1611037 : Blo 1056613 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B3577445 : Blo 1056613 3577445 := bbase (se 4 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 3577445 = 670771) (by norm_num)
theorem B5084981 : Blo 1056613 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B8591285 : Blo 1056613 8591285 := bbase (se 5 (by rfl) ⟨402716, by rfl⟩ : syracuseStep 8591285 = 805433) (by norm_num)
theorem B1087429 : Blo 1056613 1087429 := bbase (se 4 (by rfl) ⟨101946, by rfl⟩ : syracuseStep 1087429 = 203893) (by norm_num)
theorem B1906637 : Blo 1056613 1906637 := bbase (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) (by norm_num)
theorem B3577877 : Blo 1056613 3577877 := bbase (se 6 (by rfl) ⟨83856, by rfl⟩ : syracuseStep 3577877 = 167713) (by norm_num)
theorem B6035573 : Blo 1056613 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B5151125 : Blo 1056613 5151125 := bbase (se 6 (by rfl) ⟨120729, by rfl⟩ : syracuseStep 5151125 = 241459) (by norm_num)
theorem B1612205 : Blo 1056613 1612205 := bbase (se 3 (by rfl) ⟨302288, by rfl⟩ : syracuseStep 1612205 = 604577) (by norm_num)
theorem B3578309 : Blo 1056613 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B2857621 : Blo 1056613 2857621 := bbase (se 6 (by rfl) ⟨66975, by rfl⟩ : syracuseStep 2857621 = 133951) (by norm_num)
theorem B1907381 : Blo 1056613 1907381 := bbase (se 5 (by rfl) ⟨89408, by rfl⟩ : syracuseStep 1907381 = 178817) (by norm_num)
theorem B3578741 : Blo 1056613 3578741 := bbase (se 5 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 3578741 = 335507) (by norm_num)
theorem B4529141 : Blo 1056613 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B2006117 : Blo 1056613 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B4299925 : Blo 1056613 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B3579173 : Blo 1056613 3579173 := bbase (se 4 (by rfl) ⟨335547, by rfl⟩ : syracuseStep 3579173 = 671095) (by norm_num)
theorem B5086597 : Blo 1056613 5086597 := bbase (se 4 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 5086597 = 953737) (by norm_num)
theorem B1908397 : Blo 1056613 1908397 := bbase (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) (by norm_num)
theorem B2006869 : Blo 1056613 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B2236285 : Blo 1056613 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B1908613 : Blo 1056613 1908613 := bbase (se 4 (by rfl) ⟨178932, by rfl⟩ : syracuseStep 1908613 = 357865) (by norm_num)
theorem B2007013 : Blo 1056613 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B2007173 : Blo 1056613 2007173 := bbase (se 4 (by rfl) ⟨188172, by rfl⟩ : syracuseStep 2007173 = 376345) (by norm_num)
theorem B2007317 : Blo 1056613 2007317 := bbase (se 6 (by rfl) ⟨47046, by rfl⟩ : syracuseStep 2007317 = 94093) (by norm_num)
theorem B3809845 : Blo 1056613 3809845 := bbase (se 5 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 3809845 = 357173) (by norm_num)
theorem B2007605 : Blo 1056613 2007605 := bbase (se 5 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 2007605 = 188213) (by norm_num)
theorem B8036981 : Blo 1056613 8036981 := bbase (se 5 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 8036981 = 753467) (by norm_num)
theorem B1909405 : Blo 1056613 1909405 := bbase (se 3 (by rfl) ⟨358013, by rfl⟩ : syracuseStep 1909405 = 716027) (by norm_num)
theorem B2007757 : Blo 1056613 2007757 := bbase (se 3 (by rfl) ⟨376454, by rfl⟩ : syracuseStep 2007757 = 752909) (by norm_num)
theorem B1188697 : Blo 1056613 1188697 := bbase (se 2 (by rfl) ⟨445761, by rfl⟩ : syracuseStep 1188697 = 891523) (by norm_num)
theorem B3810149 : Blo 1056613 3810149 := bbase (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) (by norm_num)
theorem B2859893 : Blo 1056613 2859893 := bbase (se 5 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 2859893 = 268115) (by norm_num)
theorem B1188733 : Blo 1056613 1188733 := bbase (se 3 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 1188733 = 445775) (by norm_num)
theorem B1188769 : Blo 1056613 1188769 := bbase (se 2 (by rfl) ⟨445788, by rfl⟩ : syracuseStep 1188769 = 891577) (by norm_num)
theorem B1188805 : Blo 1056613 1188805 := bbase (se 4 (by rfl) ⟨111450, by rfl⟩ : syracuseStep 1188805 = 222901) (by norm_num)
theorem B5350373 : Blo 1056613 5350373 := bbase (se 4 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 5350373 = 1003195) (by norm_num)
theorem B1188841 : Blo 1056613 1188841 := bbase (se 2 (by rfl) ⟨445815, by rfl⟩ : syracuseStep 1188841 = 891631) (by norm_num)
theorem B2008061 : Blo 1056613 2008061 := bbase (se 3 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 2008061 = 753023) (by norm_num)
theorem B1188877 : Blo 1056613 1188877 := bbase (se 3 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 1188877 = 445829) (by norm_num)
theorem B1188913 : Blo 1056613 1188913 := bbase (se 2 (by rfl) ⟨445842, by rfl⟩ : syracuseStep 1188913 = 891685) (by norm_num)
theorem B1188949 : Blo 1056613 1188949 := bbase (se 8 (by rfl) ⟨6966, by rfl⟩ : syracuseStep 1188949 = 13933) (by norm_num)
theorem B1188985 : Blo 1056613 1188985 := bbase (se 2 (by rfl) ⟨445869, by rfl⟩ : syracuseStep 1188985 = 891739) (by norm_num)
theorem B1189021 : Blo 1056613 1189021 := bbase (se 3 (by rfl) ⟨222941, by rfl⟩ : syracuseStep 1189021 = 445883) (by norm_num)
theorem B1189057 : Blo 1056613 1189057 := bbase (se 2 (by rfl) ⟨445896, by rfl⟩ : syracuseStep 1189057 = 891793) (by norm_num)
theorem B1189093 : Blo 1056613 1189093 := bbase (se 4 (by rfl) ⟨111477, by rfl⟩ : syracuseStep 1189093 = 222955) (by norm_num)
theorem B1189129 : Blo 1056613 1189129 := bbase (se 2 (by rfl) ⟨445923, by rfl⟩ : syracuseStep 1189129 = 891847) (by norm_num)
theorem B1189165 : Blo 1056613 1189165 := bbase (se 3 (by rfl) ⟨222968, by rfl⟩ : syracuseStep 1189165 = 445937) (by norm_num)
theorem B1910069 : Blo 1056613 1910069 := bbase (se 5 (by rfl) ⟨89534, by rfl⟩ : syracuseStep 1910069 = 179069) (by norm_num)
theorem B1189201 : Blo 1056613 1189201 := bbase (se 2 (by rfl) ⟨445950, by rfl⟩ : syracuseStep 1189201 = 891901) (by norm_num)
theorem B1189237 : Blo 1056613 1189237 := bbase (se 5 (by rfl) ⟨55745, by rfl⟩ : syracuseStep 1189237 = 111491) (by norm_num)
theorem B1189273 : Blo 1056613 1189273 := bbase (se 2 (by rfl) ⟨445977, by rfl⟩ : syracuseStep 1189273 = 891955) (by norm_num)
theorem B1189309 : Blo 1056613 1189309 := bbase (se 3 (by rfl) ⟨222995, by rfl⟩ : syracuseStep 1189309 = 445991) (by norm_num)
theorem B1910213 : Blo 1056613 1910213 := bbase (se 4 (by rfl) ⟨179082, by rfl⟩ : syracuseStep 1910213 = 358165) (by norm_num)
theorem B1189345 : Blo 1056613 1189345 := bbase (se 2 (by rfl) ⟨446004, by rfl⟩ : syracuseStep 1189345 = 892009) (by norm_num)
theorem B1189381 : Blo 1056613 1189381 := bbase (se 4 (by rfl) ⟨111504, by rfl⟩ : syracuseStep 1189381 = 223009) (by norm_num)
theorem B1812005 : Blo 1056613 1812005 := bbase (se 4 (by rfl) ⟨169875, by rfl⟩ : syracuseStep 1812005 = 339751) (by norm_num)
theorem B1189417 : Blo 1056613 1189417 := bbase (se 2 (by rfl) ⟨446031, by rfl⟩ : syracuseStep 1189417 = 892063) (by norm_num)
theorem B1287733 : Blo 1056613 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B1189453 : Blo 1056613 1189453 := bbase (se 3 (by rfl) ⟨223022, by rfl⟩ : syracuseStep 1189453 = 446045) (by norm_num)
theorem B1189489 : Blo 1056613 1189489 := bbase (se 2 (by rfl) ⟨446058, by rfl⟩ : syracuseStep 1189489 = 892117) (by norm_num)
theorem B1189525 : Blo 1056613 1189525 := bbase (se 6 (by rfl) ⟨27879, by rfl⟩ : syracuseStep 1189525 = 55759) (by norm_num)
theorem B1189561 : Blo 1056613 1189561 := bbase (se 2 (by rfl) ⟨446085, by rfl⟩ : syracuseStep 1189561 = 892171) (by norm_num)
theorem B1189597 : Blo 1056613 1189597 := bbase (se 3 (by rfl) ⟨223049, by rfl⟩ : syracuseStep 1189597 = 446099) (by norm_num)
theorem B2008813 : Blo 1056613 2008813 := bbase (se 3 (by rfl) ⟨376652, by rfl⟩ : syracuseStep 2008813 = 753305) (by norm_num)
theorem B1189633 : Blo 1056613 1189633 := bbase (se 2 (by rfl) ⟨446112, by rfl⟩ : syracuseStep 1189633 = 892225) (by norm_num)
theorem B1189669 : Blo 1056613 1189669 := bbase (se 4 (by rfl) ⟨111531, by rfl⟩ : syracuseStep 1189669 = 223063) (by norm_num)
theorem B1189705 : Blo 1056613 1189705 := bbase (se 2 (by rfl) ⟨446139, by rfl⟩ : syracuseStep 1189705 = 892279) (by norm_num)
theorem B1189741 : Blo 1056613 1189741 := bbase (se 3 (by rfl) ⟨223076, by rfl⟩ : syracuseStep 1189741 = 446153) (by norm_num)
theorem B1288045 : Blo 1056613 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B2008957 : Blo 1056613 2008957 := bbase (se 3 (by rfl) ⟨376679, by rfl⟩ : syracuseStep 2008957 = 753359) (by norm_num)
theorem B1189777 : Blo 1056613 1189777 := bbase (se 2 (by rfl) ⟨446166, by rfl⟩ : syracuseStep 1189777 = 892333) (by norm_num)
theorem B1189813 : Blo 1056613 1189813 := bbase (se 5 (by rfl) ⟨55772, by rfl⟩ : syracuseStep 1189813 = 111545) (by norm_num)
theorem B1189849 : Blo 1056613 1189849 := bbase (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) (by norm_num)
theorem B1189885 : Blo 1056613 1189885 := bbase (se 3 (by rfl) ⟨223103, by rfl⟩ : syracuseStep 1189885 = 446207) (by norm_num)
theorem B2009117 : Blo 1056613 2009117 := bbase (se 3 (by rfl) ⟨376709, by rfl⟩ : syracuseStep 2009117 = 753419) (by norm_num)
theorem B1189921 : Blo 1056613 1189921 := bbase (se 2 (by rfl) ⟨446220, by rfl⟩ : syracuseStep 1189921 = 892441) (by norm_num)
theorem B1189957 : Blo 1056613 1189957 := bbase (se 4 (by rfl) ⟨111558, by rfl⟩ : syracuseStep 1189957 = 223117) (by norm_num)
theorem B6793301 : Blo 1056613 6793301 := bbase (se 8 (by rfl) ⟨39804, by rfl⟩ : syracuseStep 6793301 = 79609) (by norm_num)
theorem B1189993 : Blo 1056613 1189993 := bbase (se 2 (by rfl) ⟨446247, by rfl⟩ : syracuseStep 1189993 = 892495) (by norm_num)
theorem B1190029 : Blo 1056613 1190029 := bbase (se 3 (by rfl) ⟨223130, by rfl⟩ : syracuseStep 1190029 = 446261) (by norm_num)
theorem B2009261 : Blo 1056613 2009261 := bbase (se 3 (by rfl) ⟨376736, by rfl⟩ : syracuseStep 2009261 = 753473) (by norm_num)
theorem B1190065 : Blo 1056613 1190065 := bbase (se 2 (by rfl) ⟨446274, by rfl⟩ : syracuseStep 1190065 = 892549) (by norm_num)
theorem B1190101 : Blo 1056613 1190101 := bbase (se 7 (by rfl) ⟨13946, by rfl⟩ : syracuseStep 1190101 = 27893) (by norm_num)
theorem B5351669 : Blo 1056613 5351669 := bbase (se 5 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 5351669 = 501719) (by norm_num)
theorem B1190137 : Blo 1056613 1190137 := bbase (se 2 (by rfl) ⟨446301, by rfl⟩ : syracuseStep 1190137 = 892603) (by norm_num)
theorem B1190173 : Blo 1056613 1190173 := bbase (se 3 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 1190173 = 446315) (by norm_num)
theorem B1812773 : Blo 1056613 1812773 := bbase (se 4 (by rfl) ⟨169947, by rfl⟩ : syracuseStep 1812773 = 339895) (by norm_num)
theorem B1190209 : Blo 1056613 1190209 := bbase (se 2 (by rfl) ⟨446328, by rfl⟩ : syracuseStep 1190209 = 892657) (by norm_num)
theorem B1190245 : Blo 1056613 1190245 := bbase (se 4 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 1190245 = 223171) (by norm_num)
theorem B1190281 : Blo 1056613 1190281 := bbase (se 2 (by rfl) ⟨446355, by rfl⟩ : syracuseStep 1190281 = 892711) (by norm_num)
theorem B1190317 : Blo 1056613 1190317 := bbase (se 3 (by rfl) ⟨223184, by rfl⟩ : syracuseStep 1190317 = 446369) (by norm_num)
theorem B2009549 : Blo 1056613 2009549 := bbase (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) (by norm_num)
theorem B1190353 : Blo 1056613 1190353 := bbase (se 2 (by rfl) ⟨446382, by rfl⟩ : syracuseStep 1190353 = 892765) (by norm_num)
theorem B1190389 : Blo 1056613 1190389 := bbase (se 5 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 1190389 = 111599) (by norm_num)
theorem B1190425 : Blo 1056613 1190425 := bbase (se 2 (by rfl) ⟨446409, by rfl⟩ : syracuseStep 1190425 = 892819) (by norm_num)
theorem B1190461 : Blo 1056613 1190461 := bbase (se 3 (by rfl) ⟨223211, by rfl⟩ : syracuseStep 1190461 = 446423) (by norm_num)
theorem B1190497 : Blo 1056613 1190497 := bbase (se 2 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 1190497 = 892873) (by norm_num)
theorem B2009701 : Blo 1056613 2009701 := bbase (se 4 (by rfl) ⟨188409, by rfl⟩ : syracuseStep 2009701 = 376819) (by norm_num)
theorem B1190533 : Blo 1056613 1190533 := bbase (se 4 (by rfl) ⟨111612, by rfl⟩ : syracuseStep 1190533 = 223225) (by norm_num)
theorem B1190569 : Blo 1056613 1190569 := bbase (se 2 (by rfl) ⟨446463, by rfl⟩ : syracuseStep 1190569 = 892927) (by norm_num)
theorem B1190605 : Blo 1056613 1190605 := bbase (se 3 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 1190605 = 446477) (by norm_num)
theorem B1190641 : Blo 1056613 1190641 := bbase (se 2 (by rfl) ⟨446490, by rfl⟩ : syracuseStep 1190641 = 892981) (by norm_num)
theorem B1190677 : Blo 1056613 1190677 := bbase (se 6 (by rfl) ⟨27906, by rfl⟩ : syracuseStep 1190677 = 55813) (by norm_num)
theorem B1190713 : Blo 1056613 1190713 := bbase (se 2 (by rfl) ⟨446517, by rfl⟩ : syracuseStep 1190713 = 893035) (by norm_num)
theorem B1190749 : Blo 1056613 1190749 := bbase (se 3 (by rfl) ⟨223265, by rfl⟩ : syracuseStep 1190749 = 446531) (by norm_num)
theorem B1190785 : Blo 1056613 1190785 := bbase (se 2 (by rfl) ⟨446544, by rfl⟩ : syracuseStep 1190785 = 893089) (by norm_num)
theorem B2010005 : Blo 1056613 2010005 := bbase (se 6 (by rfl) ⟨47109, by rfl⟩ : syracuseStep 2010005 = 94219) (by norm_num)
theorem B1190821 : Blo 1056613 1190821 := bbase (se 4 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 1190821 = 223279) (by norm_num)
theorem B1813445 : Blo 1056613 1813445 := bbase (se 4 (by rfl) ⟨170010, by rfl⟩ : syracuseStep 1813445 = 340021) (by norm_num)
theorem B1190857 : Blo 1056613 1190857 := bbase (se 2 (by rfl) ⟨446571, by rfl⟩ : syracuseStep 1190857 = 893143) (by norm_num)
theorem B1190893 : Blo 1056613 1190893 := bbase (se 3 (by rfl) ⟨223292, by rfl⟩ : syracuseStep 1190893 = 446585) (by norm_num)
theorem B1190929 : Blo 1056613 1190929 := bbase (se 2 (by rfl) ⟨446598, by rfl⟩ : syracuseStep 1190929 = 893197) (by norm_num)
theorem B1190965 : Blo 1056613 1190965 := bbase (se 5 (by rfl) ⟨55826, by rfl⟩ : syracuseStep 1190965 = 111653) (by norm_num)
theorem B15281237 : Blo 1056613 15281237 := bbase (se 8 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 15281237 = 179077) (by norm_num)
theorem B1191001 : Blo 1056613 1191001 := bbase (se 2 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 1191001 = 893251) (by norm_num)
theorem B1191037 : Blo 1056613 1191037 := bbase (se 3 (by rfl) ⟨223319, by rfl⟩ : syracuseStep 1191037 = 446639) (by norm_num)
theorem B2862229 : Blo 1056613 2862229 := bbase (se 6 (by rfl) ⟨67083, by rfl⟩ : syracuseStep 2862229 = 134167) (by norm_num)
theorem B1191073 : Blo 1056613 1191073 := bbase (se 2 (by rfl) ⟨446652, by rfl⟩ : syracuseStep 1191073 = 893305) (by norm_num)
theorem B1191109 : Blo 1056613 1191109 := bbase (se 4 (by rfl) ⟨111666, by rfl⟩ : syracuseStep 1191109 = 223333) (by norm_num)
theorem B1191145 : Blo 1056613 1191145 := bbase (se 2 (by rfl) ⟨446679, by rfl⟩ : syracuseStep 1191145 = 893359) (by norm_num)
theorem B1813757 : Blo 1056613 1813757 := bbase (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) (by norm_num)
theorem B1191181 : Blo 1056613 1191181 := bbase (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) (by norm_num)
theorem B1191217 : Blo 1056613 1191217 := bbase (se 2 (by rfl) ⟨446706, by rfl⟩ : syracuseStep 1191217 = 893413) (by norm_num)
theorem B1224001 : Blo 1056613 1224001 := bbase (se 2 (by rfl) ⟨459000, by rfl⟩ : syracuseStep 1224001 = 918001) (by norm_num)
theorem B1191253 : Blo 1056613 1191253 := bbase (se 11 (by rfl) ⟨872, by rfl⟩ : syracuseStep 1191253 = 1745) (by norm_num)
theorem B1191289 : Blo 1056613 1191289 := bbase (se 2 (by rfl) ⟨446733, by rfl⟩ : syracuseStep 1191289 = 893467) (by norm_num)
theorem B1191325 : Blo 1056613 1191325 := bbase (se 3 (by rfl) ⟨223373, by rfl⟩ : syracuseStep 1191325 = 446747) (by norm_num)
theorem B1191361 : Blo 1056613 1191361 := bbase (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) (by norm_num)
theorem B1191397 : Blo 1056613 1191397 := bbase (se 4 (by rfl) ⟨111693, by rfl⟩ : syracuseStep 1191397 = 223387) (by norm_num)
theorem B5352965 : Blo 1056613 5352965 := bbase (se 4 (by rfl) ⟨501840, by rfl⟩ : syracuseStep 5352965 = 1003681) (by norm_num)
theorem B1191433 : Blo 1056613 1191433 := bbase (se 2 (by rfl) ⟨446787, by rfl⟩ : syracuseStep 1191433 = 893575) (by norm_num)
theorem B13544981 : Blo 1056613 13544981 := bbase (se 6 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 13544981 = 634921) (by norm_num)
theorem B3059237 : Blo 1056613 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B1191469 : Blo 1056613 1191469 := bbase (se 3 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 1191469 = 446801) (by norm_num)
theorem B2862661 : Blo 1056613 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B1191505 : Blo 1056613 1191505 := bbase (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) (by norm_num)
theorem B14462549 : Blo 1056613 14462549 := bbase (se 8 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 14462549 = 169483) (by norm_num)
theorem B1191541 : Blo 1056613 1191541 := bbase (se 5 (by rfl) ⟨55853, by rfl⟩ : syracuseStep 1191541 = 111707) (by norm_num)
theorem B2010757 : Blo 1056613 2010757 := bbase (se 4 (by rfl) ⟨188508, by rfl⟩ : syracuseStep 2010757 = 377017) (by norm_num)
theorem B3059333 : Blo 1056613 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B1191577 : Blo 1056613 1191577 := bbase (se 2 (by rfl) ⟨446841, by rfl⟩ : syracuseStep 1191577 = 893683) (by norm_num)
theorem B1191613 : Blo 1056613 1191613 := bbase (se 3 (by rfl) ⟨223427, by rfl⟩ : syracuseStep 1191613 = 446855) (by norm_num)
theorem B1191649 : Blo 1056613 1191649 := bbase (se 2 (by rfl) ⟨446868, by rfl⟩ : syracuseStep 1191649 = 893737) (by norm_num)
theorem B1191685 : Blo 1056613 1191685 := bbase (se 4 (by rfl) ⟨111720, by rfl⟩ : syracuseStep 1191685 = 223441) (by norm_num)
theorem B5713685 : Blo 1056613 5713685 := bbase (se 6 (by rfl) ⟨133914, by rfl⟩ : syracuseStep 5713685 = 267829) (by norm_num)
theorem B2010901 : Blo 1056613 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B1191721 : Blo 1056613 1191721 := bbase (se 2 (by rfl) ⟨446895, by rfl⟩ : syracuseStep 1191721 = 893791) (by norm_num)
theorem B1584941 : Blo 1056613 1584941 := bbase (se 3 (by rfl) ⟨297176, by rfl⟩ : syracuseStep 1584941 = 594353) (by norm_num)
theorem B1584965 : Blo 1056613 1584965 := bbase (se 4 (by rfl) ⟨148590, by rfl⟩ : syracuseStep 1584965 = 297181) (by norm_num)
theorem B1191757 : Blo 1056613 1191757 := bbase (se 3 (by rfl) ⟨223454, by rfl⟩ : syracuseStep 1191757 = 446909) (by norm_num)
theorem B1584989 : Blo 1056613 1584989 := bbase (se 3 (by rfl) ⟨297185, by rfl⟩ : syracuseStep 1584989 = 594371) (by norm_num)
theorem B1191793 : Blo 1056613 1191793 := bbase (se 2 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 1191793 = 893845) (by norm_num)
theorem B1585013 : Blo 1056613 1585013 := bbase (se 5 (by rfl) ⟨74297, by rfl⟩ : syracuseStep 1585013 = 148595) (by norm_num)
theorem B1585037 : Blo 1056613 1585037 := bbase (se 3 (by rfl) ⟨297194, by rfl⟩ : syracuseStep 1585037 = 594389) (by norm_num)
theorem B1191829 : Blo 1056613 1191829 := bbase (se 6 (by rfl) ⟨27933, by rfl⟩ : syracuseStep 1191829 = 55867) (by norm_num)
theorem B1585061 : Blo 1056613 1585061 := bbase (se 4 (by rfl) ⟨148599, by rfl⟩ : syracuseStep 1585061 = 297199) (by norm_num)
theorem B1355701 : Blo 1056613 1355701 := bbase (se 5 (by rfl) ⟨63548, by rfl⟩ : syracuseStep 1355701 = 127097) (by norm_num)
theorem B2011061 : Blo 1056613 2011061 := bbase (se 5 (by rfl) ⟨94268, by rfl⟩ : syracuseStep 2011061 = 188537) (by norm_num)
theorem B1191865 : Blo 1056613 1191865 := bbase (se 2 (by rfl) ⟨446949, by rfl⟩ : syracuseStep 1191865 = 893899) (by norm_num)
theorem B1585085 : Blo 1056613 1585085 := bbase (se 3 (by rfl) ⟨297203, by rfl⟩ : syracuseStep 1585085 = 594407) (by norm_num)
theorem B1585109 : Blo 1056613 1585109 := bbase (se 7 (by rfl) ⟨18575, by rfl⟩ : syracuseStep 1585109 = 37151) (by norm_num)
theorem B1191901 : Blo 1056613 1191901 := bbase (se 3 (by rfl) ⟨223481, by rfl⟩ : syracuseStep 1191901 = 446963) (by norm_num)
theorem B1585133 : Blo 1056613 1585133 := bbase (se 3 (by rfl) ⟨297212, by rfl⟩ : syracuseStep 1585133 = 594425) (by norm_num)
theorem B1191937 : Blo 1056613 1191937 := bbase (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) (by norm_num)
theorem B1585157 : Blo 1056613 1585157 := bbase (se 4 (by rfl) ⟨148608, by rfl⟩ : syracuseStep 1585157 = 297217) (by norm_num)
theorem B3387413 : Blo 1056613 3387413 := bbase (se 6 (by rfl) ⟨79392, by rfl⟩ : syracuseStep 3387413 = 158785) (by norm_num)
theorem B1585181 : Blo 1056613 1585181 := bbase (se 3 (by rfl) ⟨297221, by rfl⟩ : syracuseStep 1585181 = 594443) (by norm_num)
theorem B1191973 : Blo 1056613 1191973 := bbase (se 4 (by rfl) ⟨111747, by rfl⟩ : syracuseStep 1191973 = 223495) (by norm_num)
theorem B1585205 : Blo 1056613 1585205 := bbase (se 5 (by rfl) ⟨74306, by rfl⟩ : syracuseStep 1585205 = 148613) (by norm_num)
theorem B2011205 : Blo 1056613 2011205 := bbase (se 4 (by rfl) ⟨188550, by rfl⟩ : syracuseStep 2011205 = 377101) (by norm_num)
theorem B1192009 : Blo 1056613 1192009 := bbase (se 2 (by rfl) ⟨447003, by rfl⟩ : syracuseStep 1192009 = 894007) (by norm_num)
theorem B1585229 : Blo 1056613 1585229 := bbase (se 3 (by rfl) ⟨297230, by rfl⟩ : syracuseStep 1585229 = 594461) (by norm_num)
theorem B1585253 : Blo 1056613 1585253 := bbase (se 4 (by rfl) ⟨148617, by rfl⟩ : syracuseStep 1585253 = 297235) (by norm_num)
theorem B1192045 : Blo 1056613 1192045 := bbase (se 3 (by rfl) ⟨223508, by rfl⟩ : syracuseStep 1192045 = 447017) (by norm_num)
theorem B1585277 : Blo 1056613 1585277 := bbase (se 3 (by rfl) ⟨297239, by rfl⟩ : syracuseStep 1585277 = 594479) (by norm_num)
theorem B1192081 : Blo 1056613 1192081 := bbase (se 2 (by rfl) ⟨447030, by rfl⟩ : syracuseStep 1192081 = 894061) (by norm_num)
theorem B1585301 : Blo 1056613 1585301 := bbase (se 6 (by rfl) ⟨37155, by rfl⟩ : syracuseStep 1585301 = 74311) (by norm_num)
theorem B1585325 : Blo 1056613 1585325 := bbase (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) (by norm_num)
theorem B1192117 : Blo 1056613 1192117 := bbase (se 5 (by rfl) ⟨55880, by rfl⟩ : syracuseStep 1192117 = 111761) (by norm_num)
theorem B1585349 : Blo 1056613 1585349 := bbase (se 4 (by rfl) ⟨148626, by rfl⟩ : syracuseStep 1585349 = 297253) (by norm_num)
theorem B1192153 : Blo 1056613 1192153 := bbase (se 2 (by rfl) ⟨447057, by rfl⟩ : syracuseStep 1192153 = 894115) (by norm_num)
theorem B1585373 : Blo 1056613 1585373 := bbase (se 3 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 1585373 = 594515) (by norm_num)
theorem B1585397 : Blo 1056613 1585397 := bbase (se 5 (by rfl) ⟨74315, by rfl⟩ : syracuseStep 1585397 = 148631) (by norm_num)
theorem B1192189 : Blo 1056613 1192189 := bbase (se 3 (by rfl) ⟨223535, by rfl⟩ : syracuseStep 1192189 = 447071) (by norm_num)
theorem B1585421 : Blo 1056613 1585421 := bbase (se 3 (by rfl) ⟨297266, by rfl⟩ : syracuseStep 1585421 = 594533) (by norm_num)
theorem B1192225 : Blo 1056613 1192225 := bbase (se 2 (by rfl) ⟨447084, by rfl⟩ : syracuseStep 1192225 = 894169) (by norm_num)
theorem B1585445 : Blo 1056613 1585445 := bbase (se 4 (by rfl) ⟨148635, by rfl⟩ : syracuseStep 1585445 = 297271) (by norm_num)
theorem B1585469 : Blo 1056613 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1192261 : Blo 1056613 1192261 := bbase (se 4 (by rfl) ⟨111774, by rfl⟩ : syracuseStep 1192261 = 223549) (by norm_num)
theorem B1585493 : Blo 1056613 1585493 := bbase (se 10 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 1585493 = 4645) (by norm_num)
theorem B2011493 : Blo 1056613 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1192297 : Blo 1056613 1192297 := bbase (se 2 (by rfl) ⟨447111, by rfl⟩ : syracuseStep 1192297 = 894223) (by norm_num)
theorem B1585517 : Blo 1056613 1585517 := bbase (se 3 (by rfl) ⟨297284, by rfl⟩ : syracuseStep 1585517 = 594569) (by norm_num)
theorem B1585541 : Blo 1056613 1585541 := bbase (se 4 (by rfl) ⟨148644, by rfl⟩ : syracuseStep 1585541 = 297289) (by norm_num)
theorem B1192333 : Blo 1056613 1192333 := bbase (se 3 (by rfl) ⟨223562, by rfl⟩ : syracuseStep 1192333 = 447125) (by norm_num)
theorem B1585565 : Blo 1056613 1585565 := bbase (se 3 (by rfl) ⟨297293, by rfl⟩ : syracuseStep 1585565 = 594587) (by norm_num)
theorem B1192369 : Blo 1056613 1192369 := bbase (se 2 (by rfl) ⟨447138, by rfl⟩ : syracuseStep 1192369 = 894277) (by norm_num)
theorem B1585589 : Blo 1056613 1585589 := bbase (se 5 (by rfl) ⟨74324, by rfl⟩ : syracuseStep 1585589 = 148649) (by norm_num)
theorem B1585613 : Blo 1056613 1585613 := bbase (se 3 (by rfl) ⟨297302, by rfl⟩ : syracuseStep 1585613 = 594605) (by norm_num)
theorem B1192405 : Blo 1056613 1192405 := bbase (se 7 (by rfl) ⟨13973, by rfl⟩ : syracuseStep 1192405 = 27947) (by norm_num)
theorem B1585637 : Blo 1056613 1585637 := bbase (se 4 (by rfl) ⟨148653, by rfl⟩ : syracuseStep 1585637 = 297307) (by norm_num)
theorem B1192441 : Blo 1056613 1192441 := bbase (se 2 (by rfl) ⟨447165, by rfl⟩ : syracuseStep 1192441 = 894331) (by norm_num)
theorem B1585661 : Blo 1056613 1585661 := bbase (se 3 (by rfl) ⟨297311, by rfl⟩ : syracuseStep 1585661 = 594623) (by norm_num)
theorem B2011645 : Blo 1056613 2011645 := bbase (se 3 (by rfl) ⟨377183, by rfl⟩ : syracuseStep 2011645 = 754367) (by norm_num)
theorem B1585685 : Blo 1056613 1585685 := bbase (se 6 (by rfl) ⟨37164, by rfl⟩ : syracuseStep 1585685 = 74329) (by norm_num)
theorem B1192477 : Blo 1056613 1192477 := bbase (se 3 (by rfl) ⟨223589, by rfl⟩ : syracuseStep 1192477 = 447179) (by norm_num)
theorem B1585709 : Blo 1056613 1585709 := bbase (se 3 (by rfl) ⟨297320, by rfl⟩ : syracuseStep 1585709 = 594641) (by norm_num)
theorem B1192513 : Blo 1056613 1192513 := bbase (se 2 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 1192513 = 894385) (by norm_num)
theorem B1585733 : Blo 1056613 1585733 := bbase (se 4 (by rfl) ⟨148662, by rfl⟩ : syracuseStep 1585733 = 297325) (by norm_num)
theorem B1585757 : Blo 1056613 1585757 := bbase (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) (by norm_num)
theorem B1192549 : Blo 1056613 1192549 := bbase (se 4 (by rfl) ⟨111801, by rfl⟩ : syracuseStep 1192549 = 223603) (by norm_num)
theorem B1585781 : Blo 1056613 1585781 := bbase (se 5 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 1585781 = 148667) (by norm_num)
theorem B1192585 : Blo 1056613 1192585 := bbase (se 2 (by rfl) ⟨447219, by rfl⟩ : syracuseStep 1192585 = 894439) (by norm_num)
theorem B1585805 : Blo 1056613 1585805 := bbase (se 3 (by rfl) ⟨297338, by rfl⟩ : syracuseStep 1585805 = 594677) (by norm_num)
theorem B1225373 : Blo 1056613 1225373 := bbase (se 3 (by rfl) ⟨229757, by rfl⟩ : syracuseStep 1225373 = 459515) (by norm_num)
theorem B1585829 : Blo 1056613 1585829 := bbase (se 4 (by rfl) ⟨148671, by rfl⟩ : syracuseStep 1585829 = 297343) (by norm_num)
theorem B1192621 : Blo 1056613 1192621 := bbase (se 3 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 1192621 = 447233) (by norm_num)
theorem B1585853 : Blo 1056613 1585853 := bbase (se 3 (by rfl) ⟨297347, by rfl⟩ : syracuseStep 1585853 = 594695) (by norm_num)
theorem B1192657 : Blo 1056613 1192657 := bbase (se 2 (by rfl) ⟨447246, by rfl⟩ : syracuseStep 1192657 = 894493) (by norm_num)
theorem B1585877 : Blo 1056613 1585877 := bbase (se 7 (by rfl) ⟨18584, by rfl⟩ : syracuseStep 1585877 = 37169) (by norm_num)
theorem B2142949 : Blo 1056613 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B1585901 : Blo 1056613 1585901 := bbase (se 3 (by rfl) ⟨297356, by rfl⟩ : syracuseStep 1585901 = 594713) (by norm_num)
theorem B1192693 : Blo 1056613 1192693 := bbase (se 5 (by rfl) ⟨55907, by rfl⟩ : syracuseStep 1192693 = 111815) (by norm_num)
theorem B1585925 : Blo 1056613 1585925 := bbase (se 4 (by rfl) ⟨148680, by rfl⟩ : syracuseStep 1585925 = 297361) (by norm_num)
theorem B5354261 : Blo 1056613 5354261 := bbase (se 6 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 5354261 = 250981) (by norm_num)
theorem B1192729 : Blo 1056613 1192729 := bbase (se 2 (by rfl) ⟨447273, by rfl⟩ : syracuseStep 1192729 = 894547) (by norm_num)
theorem B1585949 : Blo 1056613 1585949 := bbase (se 3 (by rfl) ⟨297365, by rfl⟩ : syracuseStep 1585949 = 594731) (by norm_num)
theorem B2143021 : Blo 1056613 2143021 := bbase (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) (by norm_num)
theorem B2011949 : Blo 1056613 2011949 := bbase (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) (by norm_num)
theorem B1585973 : Blo 1056613 1585973 := bbase (se 5 (by rfl) ⟨74342, by rfl⟩ : syracuseStep 1585973 = 148685) (by norm_num)
theorem B1192765 : Blo 1056613 1192765 := bbase (se 3 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 1192765 = 447287) (by norm_num)
theorem B1585997 : Blo 1056613 1585997 := bbase (se 3 (by rfl) ⟨297374, by rfl⟩ : syracuseStep 1585997 = 594749) (by norm_num)
theorem B1192801 : Blo 1056613 1192801 := bbase (se 2 (by rfl) ⟨447300, by rfl⟩ : syracuseStep 1192801 = 894601) (by norm_num)
theorem B1586021 : Blo 1056613 1586021 := bbase (se 4 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 1586021 = 297379) (by norm_num)
theorem B1586045 : Blo 1056613 1586045 := bbase (se 3 (by rfl) ⟨297383, by rfl⟩ : syracuseStep 1586045 = 594767) (by norm_num)
theorem B1192837 : Blo 1056613 1192837 := bbase (se 4 (by rfl) ⟨111828, by rfl⟩ : syracuseStep 1192837 = 223657) (by norm_num)
theorem B1586069 : Blo 1056613 1586069 := bbase (se 6 (by rfl) ⟨37173, by rfl⟩ : syracuseStep 1586069 = 74347) (by norm_num)
theorem B1192873 : Blo 1056613 1192873 := bbase (se 2 (by rfl) ⟨447327, by rfl⟩ : syracuseStep 1192873 = 894655) (by norm_num)
theorem B1586093 : Blo 1056613 1586093 := bbase (se 3 (by rfl) ⟨297392, by rfl⟩ : syracuseStep 1586093 = 594785) (by norm_num)
theorem B1586117 : Blo 1056613 1586117 := bbase (se 4 (by rfl) ⟨148698, by rfl⟩ : syracuseStep 1586117 = 297397) (by norm_num)
theorem B1192909 : Blo 1056613 1192909 := bbase (se 3 (by rfl) ⟨223670, by rfl⟩ : syracuseStep 1192909 = 447341) (by norm_num)
theorem B1586141 : Blo 1056613 1586141 := bbase (se 3 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 1586141 = 594803) (by norm_num)
theorem B1192945 : Blo 1056613 1192945 := bbase (se 2 (by rfl) ⟨447354, by rfl⟩ : syracuseStep 1192945 = 894709) (by norm_num)
theorem B1586165 : Blo 1056613 1586165 := bbase (se 5 (by rfl) ⟨74351, by rfl⟩ : syracuseStep 1586165 = 148703) (by norm_num)
theorem B1586189 : Blo 1056613 1586189 := bbase (se 3 (by rfl) ⟨297410, by rfl⟩ : syracuseStep 1586189 = 594821) (by norm_num)
theorem B1192981 : Blo 1056613 1192981 := bbase (se 6 (by rfl) ⟨27960, by rfl⟩ : syracuseStep 1192981 = 55921) (by norm_num)
theorem B1586213 : Blo 1056613 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B1193017 : Blo 1056613 1193017 := bbase (se 2 (by rfl) ⟨447381, by rfl⟩ : syracuseStep 1193017 = 894763) (by norm_num)
theorem B1586237 : Blo 1056613 1586237 := bbase (se 3 (by rfl) ⟨297419, by rfl⟩ : syracuseStep 1586237 = 594839) (by norm_num)
theorem B1586261 : Blo 1056613 1586261 := bbase (se 8 (by rfl) ⟨9294, by rfl⟩ : syracuseStep 1586261 = 18589) (by norm_num)
theorem B1193053 : Blo 1056613 1193053 := bbase (se 3 (by rfl) ⟨223697, by rfl⟩ : syracuseStep 1193053 = 447395) (by norm_num)
theorem B1586285 : Blo 1056613 1586285 := bbase (se 3 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 1586285 = 594857) (by norm_num)
theorem B1193089 : Blo 1056613 1193089 := bbase (se 2 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 1193089 = 894817) (by norm_num)
theorem B1586309 : Blo 1056613 1586309 := bbase (se 4 (by rfl) ⟨148716, by rfl⟩ : syracuseStep 1586309 = 297433) (by norm_num)
theorem B1586333 : Blo 1056613 1586333 := bbase (se 3 (by rfl) ⟨297437, by rfl⟩ : syracuseStep 1586333 = 594875) (by norm_num)
theorem B1193125 : Blo 1056613 1193125 := bbase (se 4 (by rfl) ⟨111855, by rfl⟩ : syracuseStep 1193125 = 223711) (by norm_num)
theorem B1586357 : Blo 1056613 1586357 := bbase (se 5 (by rfl) ⟨74360, by rfl⟩ : syracuseStep 1586357 = 148721) (by norm_num)
theorem B1193161 : Blo 1056613 1193161 := bbase (se 2 (by rfl) ⟨447435, by rfl⟩ : syracuseStep 1193161 = 894871) (by norm_num)
theorem B1586381 : Blo 1056613 1586381 := bbase (se 3 (by rfl) ⟨297446, by rfl⟩ : syracuseStep 1586381 = 594893) (by norm_num)
theorem B1586405 : Blo 1056613 1586405 := bbase (se 4 (by rfl) ⟨148725, by rfl⟩ : syracuseStep 1586405 = 297451) (by norm_num)
theorem B1586429 : Blo 1056613 1586429 := bbase (se 3 (by rfl) ⟨297455, by rfl⟩ : syracuseStep 1586429 = 594911) (by norm_num)
theorem B3257605 : Blo 1056613 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B1586453 : Blo 1056613 1586453 := bbase (se 6 (by rfl) ⟨37182, by rfl⟩ : syracuseStep 1586453 = 74365) (by norm_num)
theorem B1586477 : Blo 1056613 1586477 := bbase (se 3 (by rfl) ⟨297464, by rfl⟩ : syracuseStep 1586477 = 594929) (by norm_num)
theorem B1783093 : Blo 1056613 1783093 := bbase (se 5 (by rfl) ⟨83582, by rfl⟩ : syracuseStep 1783093 = 167165) (by norm_num)
theorem B1586501 : Blo 1056613 1586501 := bbase (se 4 (by rfl) ⟨148734, by rfl⟩ : syracuseStep 1586501 = 297469) (by norm_num)
theorem B1586525 : Blo 1056613 1586525 := bbase (se 3 (by rfl) ⟨297473, by rfl⟩ : syracuseStep 1586525 = 594947) (by norm_num)
theorem B1586549 : Blo 1056613 1586549 := bbase (se 5 (by rfl) ⟨74369, by rfl⟩ : syracuseStep 1586549 = 148739) (by norm_num)
theorem B1783181 : Blo 1056613 1783181 := bbase (se 3 (by rfl) ⟨334346, by rfl⟩ : syracuseStep 1783181 = 668693) (by norm_num)
theorem B1586573 : Blo 1056613 1586573 := bbase (se 3 (by rfl) ⟨297482, by rfl⟩ : syracuseStep 1586573 = 594965) (by norm_num)
theorem B1586597 : Blo 1056613 1586597 := bbase (se 4 (by rfl) ⟨148743, by rfl⟩ : syracuseStep 1586597 = 297487) (by norm_num)
theorem B1586621 : Blo 1056613 1586621 := bbase (se 3 (by rfl) ⟨297491, by rfl⟩ : syracuseStep 1586621 = 594983) (by norm_num)
theorem B14464469 : Blo 1056613 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B1586645 : Blo 1056613 1586645 := bbase (se 7 (by rfl) ⟨18593, by rfl⟩ : syracuseStep 1586645 = 37187) (by norm_num)
theorem B1586669 : Blo 1056613 1586669 := bbase (se 3 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 1586669 = 595001) (by norm_num)
theorem B1586693 : Blo 1056613 1586693 := bbase (se 4 (by rfl) ⟨148752, by rfl⟩ : syracuseStep 1586693 = 297505) (by norm_num)
theorem B1783309 : Blo 1056613 1783309 := bbase (se 3 (by rfl) ⟨334370, by rfl⟩ : syracuseStep 1783309 = 668741) (by norm_num)
theorem B1586717 : Blo 1056613 1586717 := bbase (se 3 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 1586717 = 595019) (by norm_num)
theorem B2012701 : Blo 1056613 2012701 := bbase (se 3 (by rfl) ⟨377381, by rfl⟩ : syracuseStep 2012701 = 754763) (by norm_num)
theorem B5092901 : Blo 1056613 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B1586741 : Blo 1056613 1586741 := bbase (se 5 (by rfl) ⟨74378, by rfl⟩ : syracuseStep 1586741 = 148757) (by norm_num)
theorem B1586765 : Blo 1056613 1586765 := bbase (se 3 (by rfl) ⟨297518, by rfl⟩ : syracuseStep 1586765 = 595037) (by norm_num)
theorem B1783397 : Blo 1056613 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B1586789 : Blo 1056613 1586789 := bbase (se 4 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 1586789 = 297523) (by norm_num)
theorem B1586813 : Blo 1056613 1586813 := bbase (se 3 (by rfl) ⟨297527, by rfl⟩ : syracuseStep 1586813 = 595055) (by norm_num)
theorem B1586837 : Blo 1056613 1586837 := bbase (se 6 (by rfl) ⟨37191, by rfl⟩ : syracuseStep 1586837 = 74383) (by norm_num)
theorem B1586861 : Blo 1056613 1586861 := bbase (se 3 (by rfl) ⟨297536, by rfl⟩ : syracuseStep 1586861 = 595073) (by norm_num)
theorem B2012845 : Blo 1056613 2012845 := bbase (se 3 (by rfl) ⟨377408, by rfl⟩ : syracuseStep 2012845 = 754817) (by norm_num)
theorem B1586885 : Blo 1056613 1586885 := bbase (se 4 (by rfl) ⟨148770, by rfl⟩ : syracuseStep 1586885 = 297541) (by norm_num)
theorem B3487445 : Blo 1056613 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B1586909 : Blo 1056613 1586909 := bbase (se 3 (by rfl) ⟨297545, by rfl⟩ : syracuseStep 1586909 = 595091) (by norm_num)
theorem B1783525 : Blo 1056613 1783525 := bbase (se 4 (by rfl) ⟨167205, by rfl⟩ : syracuseStep 1783525 = 334411) (by norm_num)
theorem B1586933 : Blo 1056613 1586933 := bbase (se 5 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 1586933 = 148775) (by norm_num)
theorem B1586957 : Blo 1056613 1586957 := bbase (se 3 (by rfl) ⟨297554, by rfl⟩ : syracuseStep 1586957 = 595109) (by norm_num)
theorem B1586981 : Blo 1056613 1586981 := bbase (se 4 (by rfl) ⟨148779, by rfl⟩ : syracuseStep 1586981 = 297559) (by norm_num)
theorem B1783613 : Blo 1056613 1783613 := bbase (se 3 (by rfl) ⟨334427, by rfl⟩ : syracuseStep 1783613 = 668855) (by norm_num)
theorem B1587005 : Blo 1056613 1587005 := bbase (se 3 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 1587005 = 595127) (by norm_num)
theorem B2013005 : Blo 1056613 2013005 := bbase (se 3 (by rfl) ⟨377438, by rfl⟩ : syracuseStep 2013005 = 754877) (by norm_num)
theorem B1587029 : Blo 1056613 1587029 := bbase (se 9 (by rfl) ⟨4649, by rfl⟩ : syracuseStep 1587029 = 9299) (by norm_num)
theorem B1587053 : Blo 1056613 1587053 := bbase (se 3 (by rfl) ⟨297572, by rfl⟩ : syracuseStep 1587053 = 595145) (by norm_num)
theorem B1587077 : Blo 1056613 1587077 := bbase (se 4 (by rfl) ⟨148788, by rfl⟩ : syracuseStep 1587077 = 297577) (by norm_num)
theorem B1587101 : Blo 1056613 1587101 := bbase (se 3 (by rfl) ⟨297581, by rfl⟩ : syracuseStep 1587101 = 595163) (by norm_num)
theorem B1587125 : Blo 1056613 1587125 := bbase (se 5 (by rfl) ⟨74396, by rfl⟩ : syracuseStep 1587125 = 148793) (by norm_num)
theorem B1783741 : Blo 1056613 1783741 := bbase (se 3 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 1783741 = 668903) (by norm_num)
theorem B1587149 : Blo 1056613 1587149 := bbase (se 3 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 1587149 = 595181) (by norm_num)
theorem B2013149 : Blo 1056613 2013149 := bbase (se 3 (by rfl) ⟨377465, by rfl⟩ : syracuseStep 2013149 = 754931) (by norm_num)
theorem B1587173 : Blo 1056613 1587173 := bbase (se 4 (by rfl) ⟨148797, by rfl⟩ : syracuseStep 1587173 = 297595) (by norm_num)
theorem B1587197 : Blo 1056613 1587197 := bbase (se 3 (by rfl) ⟨297599, by rfl⟩ : syracuseStep 1587197 = 595199) (by norm_num)
theorem B4012037 : Blo 1056613 4012037 := bbase (se 4 (by rfl) ⟨376128, by rfl⟩ : syracuseStep 4012037 = 752257) (by norm_num)
theorem B1783829 : Blo 1056613 1783829 := bbase (se 6 (by rfl) ⟨41808, by rfl⟩ : syracuseStep 1783829 = 83617) (by norm_num)
theorem B1587221 : Blo 1056613 1587221 := bbase (se 6 (by rfl) ⟨37200, by rfl⟩ : syracuseStep 1587221 = 74401) (by norm_num)
theorem B5355557 : Blo 1056613 5355557 := bbase (se 4 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 5355557 = 1004167) (by norm_num)
theorem B1587245 : Blo 1056613 1587245 := bbase (se 3 (by rfl) ⟨297608, by rfl⟩ : syracuseStep 1587245 = 595217) (by norm_num)
theorem B5716021 : Blo 1056613 5716021 := bbase (se 5 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 5716021 = 535877) (by norm_num)
theorem B1587269 : Blo 1056613 1587269 := bbase (se 4 (by rfl) ⟨148806, by rfl⟩ : syracuseStep 1587269 = 297613) (by norm_num)
theorem B1587293 : Blo 1056613 1587293 := bbase (se 3 (by rfl) ⟨297617, by rfl⟩ : syracuseStep 1587293 = 595235) (by norm_num)
theorem B3815525 : Blo 1056613 3815525 := bbase (se 4 (by rfl) ⟨357705, by rfl⟩ : syracuseStep 3815525 = 715411) (by norm_num)
theorem B1587317 : Blo 1056613 1587317 := bbase (se 5 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 1587317 = 148811) (by norm_num)
theorem B1587341 : Blo 1056613 1587341 := bbase (se 3 (by rfl) ⟨297626, by rfl⟩ : syracuseStep 1587341 = 595253) (by norm_num)
theorem B1783957 : Blo 1056613 1783957 := bbase (se 6 (by rfl) ⟨41811, by rfl⟩ : syracuseStep 1783957 = 83623) (by norm_num)
theorem B1587365 : Blo 1056613 1587365 := bbase (se 4 (by rfl) ⟨148815, by rfl⟩ : syracuseStep 1587365 = 297631) (by norm_num)
theorem B1587389 : Blo 1056613 1587389 := bbase (se 3 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 1587389 = 595271) (by norm_num)
theorem B1587413 : Blo 1056613 1587413 := bbase (se 7 (by rfl) ⟨18602, by rfl⟩ : syracuseStep 1587413 = 37205) (by norm_num)
theorem B2865365 : Blo 1056613 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1784045 : Blo 1056613 1784045 := bbase (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) (by norm_num)
theorem B1587437 : Blo 1056613 1587437 := bbase (se 3 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 1587437 = 595289) (by norm_num)
theorem B1128697 : Blo 1056613 1128697 := bbase (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) (by norm_num)
theorem B2013437 : Blo 1056613 2013437 := bbase (se 3 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 2013437 = 755039) (by norm_num)
theorem B1587461 : Blo 1056613 1587461 := bbase (se 4 (by rfl) ⟨148824, by rfl⟩ : syracuseStep 1587461 = 297649) (by norm_num)
theorem B1587485 : Blo 1056613 1587485 := bbase (se 3 (by rfl) ⟨297653, by rfl⟩ : syracuseStep 1587485 = 595307) (by norm_num)
theorem B4012325 : Blo 1056613 4012325 := bbase (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) (by norm_num)
theorem B1587509 : Blo 1056613 1587509 := bbase (se 5 (by rfl) ⟨74414, by rfl⟩ : syracuseStep 1587509 = 148829) (by norm_num)
theorem B1587533 : Blo 1056613 1587533 := bbase (se 3 (by rfl) ⟨297662, by rfl⟩ : syracuseStep 1587533 = 595325) (by norm_num)
theorem B198162773 : Blo 1056613 198162773 := bbase (se 10 (by rfl) ⟨290277, by rfl⟩ : syracuseStep 198162773 = 580555) (by norm_num)
theorem B1587557 : Blo 1056613 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B1784173 : Blo 1056613 1784173 := bbase (se 3 (by rfl) ⟨334532, by rfl⟩ : syracuseStep 1784173 = 669065) (by norm_num)
theorem B1128817 : Blo 1056613 1128817 := bbase (se 2 (by rfl) ⟨423306, by rfl⟩ : syracuseStep 1128817 = 846613) (by norm_num)
theorem B1587581 : Blo 1056613 1587581 := bbase (se 3 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 1587581 = 595343) (by norm_num)
theorem B1587605 : Blo 1056613 1587605 := bbase (se 6 (by rfl) ⟨37209, by rfl⟩ : syracuseStep 1587605 = 74419) (by norm_num)
theorem B1587629 : Blo 1056613 1587629 := bbase (se 3 (by rfl) ⟨297680, by rfl⟩ : syracuseStep 1587629 = 595361) (by norm_num)
theorem B1784261 : Blo 1056613 1784261 := bbase (se 4 (by rfl) ⟨167274, by rfl⟩ : syracuseStep 1784261 = 334549) (by norm_num)
theorem B1587653 : Blo 1056613 1587653 := bbase (se 4 (by rfl) ⟨148842, by rfl⟩ : syracuseStep 1587653 = 297685) (by norm_num)
theorem B1587677 : Blo 1056613 1587677 := bbase (se 3 (by rfl) ⟨297689, by rfl⟩ : syracuseStep 1587677 = 595379) (by norm_num)
theorem B1587701 : Blo 1056613 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B1587725 : Blo 1056613 1587725 := bbase (se 3 (by rfl) ⟨297698, by rfl⟩ : syracuseStep 1587725 = 595397) (by norm_num)
theorem B1587749 : Blo 1056613 1587749 := bbase (se 4 (by rfl) ⟨148851, by rfl⟩ : syracuseStep 1587749 = 297703) (by norm_num)
theorem B1587773 : Blo 1056613 1587773 := bbase (se 3 (by rfl) ⟨297707, by rfl⟩ : syracuseStep 1587773 = 595415) (by norm_num)
theorem B1784389 : Blo 1056613 1784389 := bbase (se 4 (by rfl) ⟨167286, by rfl⟩ : syracuseStep 1784389 = 334573) (by norm_num)
theorem B1587797 : Blo 1056613 1587797 := bbase (se 8 (by rfl) ⟨9303, by rfl⟩ : syracuseStep 1587797 = 18607) (by norm_num)
theorem B1129069 : Blo 1056613 1129069 := bbase (se 3 (by rfl) ⟨211700, by rfl⟩ : syracuseStep 1129069 = 423401) (by norm_num)
theorem B1587821 : Blo 1056613 1587821 := bbase (se 3 (by rfl) ⟨297716, by rfl⟩ : syracuseStep 1587821 = 595433) (by norm_num)
theorem B1129073 : Blo 1056613 1129073 := bbase (se 2 (by rfl) ⟨423402, by rfl⟩ : syracuseStep 1129073 = 846805) (by norm_num)
theorem B1587845 : Blo 1056613 1587845 := bbase (se 4 (by rfl) ⟨148860, by rfl⟩ : syracuseStep 1587845 = 297721) (by norm_num)
theorem B1784477 : Blo 1056613 1784477 := bbase (se 3 (by rfl) ⟨334589, by rfl⟩ : syracuseStep 1784477 = 669179) (by norm_num)
theorem B1587869 : Blo 1056613 1587869 := bbase (se 3 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 1587869 = 595451) (by norm_num)
theorem B1587893 : Blo 1056613 1587893 := bbase (se 5 (by rfl) ⟨74432, by rfl⟩ : syracuseStep 1587893 = 148865) (by norm_num)
theorem B1587917 : Blo 1056613 1587917 := bbase (se 3 (by rfl) ⟨297734, by rfl⟩ : syracuseStep 1587917 = 595469) (by norm_num)
theorem B1587941 : Blo 1056613 1587941 := bbase (se 4 (by rfl) ⟨148869, by rfl⟩ : syracuseStep 1587941 = 297739) (by norm_num)
theorem B1587965 : Blo 1056613 1587965 := bbase (se 3 (by rfl) ⟨297743, by rfl⟩ : syracuseStep 1587965 = 595487) (by norm_num)
theorem B1587989 : Blo 1056613 1587989 := bbase (se 6 (by rfl) ⟨37218, by rfl⟩ : syracuseStep 1587989 = 74437) (by norm_num)
theorem B1784605 : Blo 1056613 1784605 := bbase (se 3 (by rfl) ⟨334613, by rfl⟩ : syracuseStep 1784605 = 669227) (by norm_num)
theorem B3390245 : Blo 1056613 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B1588013 : Blo 1056613 1588013 := bbase (se 3 (by rfl) ⟨297752, by rfl⟩ : syracuseStep 1588013 = 595505) (by norm_num)
theorem B1588037 : Blo 1056613 1588037 := bbase (se 4 (by rfl) ⟨148878, by rfl⟩ : syracuseStep 1588037 = 297757) (by norm_num)
theorem B1588061 : Blo 1056613 1588061 := bbase (se 3 (by rfl) ⟨297761, by rfl⟩ : syracuseStep 1588061 = 595523) (by norm_num)
theorem B1784693 : Blo 1056613 1784693 := bbase (se 5 (by rfl) ⟨83657, by rfl⟩ : syracuseStep 1784693 = 167315) (by norm_num)
theorem B1588085 : Blo 1056613 1588085 := bbase (se 5 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 1588085 = 148883) (by norm_num)
theorem B1588109 : Blo 1056613 1588109 := bbase (se 3 (by rfl) ⟨297770, by rfl⟩ : syracuseStep 1588109 = 595541) (by norm_num)
theorem B1588133 : Blo 1056613 1588133 := bbase (se 4 (by rfl) ⟨148887, by rfl⟩ : syracuseStep 1588133 = 297775) (by norm_num)
theorem B1588157 : Blo 1056613 1588157 := bbase (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) (by norm_num)
theorem B1588181 : Blo 1056613 1588181 := bbase (se 7 (by rfl) ⟨18611, by rfl⟩ : syracuseStep 1588181 = 37223) (by norm_num)
theorem B1588205 : Blo 1056613 1588205 := bbase (se 3 (by rfl) ⟨297788, by rfl⟩ : syracuseStep 1588205 = 595577) (by norm_num)
theorem B1784821 : Blo 1056613 1784821 := bbase (se 5 (by rfl) ⟨83663, by rfl⟩ : syracuseStep 1784821 = 167327) (by norm_num)
theorem B1588229 : Blo 1056613 1588229 := bbase (se 4 (by rfl) ⟨148896, by rfl⟩ : syracuseStep 1588229 = 297793) (by norm_num)
theorem B1588253 : Blo 1056613 1588253 := bbase (se 3 (by rfl) ⟨297797, by rfl⟩ : syracuseStep 1588253 = 595595) (by norm_num)
theorem B1588277 : Blo 1056613 1588277 := bbase (se 5 (by rfl) ⟨74450, by rfl⟩ : syracuseStep 1588277 = 148901) (by norm_num)
theorem B1784909 : Blo 1056613 1784909 := bbase (se 3 (by rfl) ⟨334670, by rfl⟩ : syracuseStep 1784909 = 669341) (by norm_num)
theorem B1588301 : Blo 1056613 1588301 := bbase (se 3 (by rfl) ⟨297806, by rfl⟩ : syracuseStep 1588301 = 595613) (by norm_num)
theorem B2866261 : Blo 1056613 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B1588325 : Blo 1056613 1588325 := bbase (se 4 (by rfl) ⟨148905, by rfl⟩ : syracuseStep 1588325 = 297811) (by norm_num)
theorem B1588349 : Blo 1056613 1588349 := bbase (se 3 (by rfl) ⟨297815, by rfl⟩ : syracuseStep 1588349 = 595631) (by norm_num)
theorem B1588373 : Blo 1056613 1588373 := bbase (se 6 (by rfl) ⟨37227, by rfl⟩ : syracuseStep 1588373 = 74455) (by norm_num)
theorem B1129637 : Blo 1056613 1129637 := bbase (se 4 (by rfl) ⟨105903, by rfl⟩ : syracuseStep 1129637 = 211807) (by norm_num)
theorem B1588397 : Blo 1056613 1588397 := bbase (se 3 (by rfl) ⟨297824, by rfl⟩ : syracuseStep 1588397 = 595649) (by norm_num)
theorem B1588421 : Blo 1056613 1588421 := bbase (se 4 (by rfl) ⟨148914, by rfl⟩ : syracuseStep 1588421 = 297829) (by norm_num)
theorem B1785037 : Blo 1056613 1785037 := bbase (se 3 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 1785037 = 669389) (by norm_num)
theorem B1588445 : Blo 1056613 1588445 := bbase (se 3 (by rfl) ⟨297833, by rfl⟩ : syracuseStep 1588445 = 595667) (by norm_num)
theorem B1588469 : Blo 1056613 1588469 := bbase (se 5 (by rfl) ⟨74459, by rfl⟩ : syracuseStep 1588469 = 148919) (by norm_num)
theorem B1588493 : Blo 1056613 1588493 := bbase (se 3 (by rfl) ⟨297842, by rfl⟩ : syracuseStep 1588493 = 595685) (by norm_num)
theorem B1785125 : Blo 1056613 1785125 := bbase (se 4 (by rfl) ⟨167355, by rfl⟩ : syracuseStep 1785125 = 334711) (by norm_num)
theorem B1588517 : Blo 1056613 1588517 := bbase (se 4 (by rfl) ⟨148923, by rfl⟩ : syracuseStep 1588517 = 297847) (by norm_num)
theorem B5356853 : Blo 1056613 5356853 := bbase (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) (by norm_num)
theorem B1588541 : Blo 1056613 1588541 := bbase (se 3 (by rfl) ⟨297851, by rfl⟩ : syracuseStep 1588541 = 595703) (by norm_num)
theorem B1588565 : Blo 1056613 1588565 := bbase (se 11 (by rfl) ⟨1163, by rfl⟩ : syracuseStep 1588565 = 2327) (by norm_num)
theorem B1129825 : Blo 1056613 1129825 := bbase (se 2 (by rfl) ⟨423684, by rfl⟩ : syracuseStep 1129825 = 847369) (by norm_num)
theorem B1588589 : Blo 1056613 1588589 := bbase (se 3 (by rfl) ⟨297860, by rfl⟩ : syracuseStep 1588589 = 595721) (by norm_num)
theorem B2538877 : Blo 1056613 2538877 := bbase (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) (by norm_num)
theorem B1588613 : Blo 1056613 1588613 := bbase (se 4 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 1588613 = 297865) (by norm_num)
theorem B12041621 : Blo 1056613 12041621 := bbase (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) (by norm_num)
theorem B1588637 : Blo 1056613 1588637 := bbase (se 3 (by rfl) ⟨297869, by rfl⟩ : syracuseStep 1588637 = 595739) (by norm_num)
theorem B1785253 : Blo 1056613 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B1588661 : Blo 1056613 1588661 := bbase (se 5 (by rfl) ⟨74468, by rfl⟩ : syracuseStep 1588661 = 148937) (by norm_num)
theorem B4013509 : Blo 1056613 4013509 := bbase (se 4 (by rfl) ⟨376266, by rfl⟩ : syracuseStep 4013509 = 752533) (by norm_num)
theorem B1588685 : Blo 1056613 1588685 := bbase (se 3 (by rfl) ⟨297878, by rfl⟩ : syracuseStep 1588685 = 595757) (by norm_num)
theorem B1588709 : Blo 1056613 1588709 := bbase (se 4 (by rfl) ⟨148941, by rfl⟩ : syracuseStep 1588709 = 297883) (by norm_num)
theorem B1785341 : Blo 1056613 1785341 := bbase (se 3 (by rfl) ⟨334751, by rfl⟩ : syracuseStep 1785341 = 669503) (by norm_num)
theorem B1588733 : Blo 1056613 1588733 := bbase (se 3 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 1588733 = 595775) (by norm_num)
theorem B3816965 : Blo 1056613 3816965 := bbase (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) (by norm_num)
theorem B1588757 : Blo 1056613 1588757 := bbase (se 6 (by rfl) ⟨37236, by rfl⟩ : syracuseStep 1588757 = 74473) (by norm_num)
theorem B1588781 : Blo 1056613 1588781 := bbase (se 3 (by rfl) ⟨297896, by rfl⟩ : syracuseStep 1588781 = 595793) (by norm_num)
theorem B1588805 : Blo 1056613 1588805 := bbase (se 4 (by rfl) ⟨148950, by rfl⟩ : syracuseStep 1588805 = 297901) (by norm_num)
theorem B1588829 : Blo 1056613 1588829 := bbase (se 3 (by rfl) ⟨297905, by rfl⟩ : syracuseStep 1588829 = 595811) (by norm_num)
theorem B1588853 : Blo 1056613 1588853 := bbase (se 5 (by rfl) ⟨74477, by rfl⟩ : syracuseStep 1588853 = 148955) (by norm_num)
theorem B1785469 : Blo 1056613 1785469 := bbase (se 3 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 1785469 = 669551) (by norm_num)
theorem B1359497 : Blo 1056613 1359497 := bbase (se 2 (by rfl) ⟨509811, by rfl⟩ : syracuseStep 1359497 = 1019623) (by norm_num)
theorem B1588877 : Blo 1056613 1588877 := bbase (se 3 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 1588877 = 595829) (by norm_num)
theorem B3391141 : Blo 1056613 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B1588901 : Blo 1056613 1588901 := bbase (se 4 (by rfl) ⟨148959, by rfl⟩ : syracuseStep 1588901 = 297919) (by norm_num)
theorem B1588925 : Blo 1056613 1588925 := bbase (se 3 (by rfl) ⟨297923, by rfl⟩ : syracuseStep 1588925 = 595847) (by norm_num)
theorem B1785557 : Blo 1056613 1785557 := bbase (se 7 (by rfl) ⟨20924, by rfl⟩ : syracuseStep 1785557 = 41849) (by norm_num)
theorem B1588949 : Blo 1056613 1588949 := bbase (se 7 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 1588949 = 37241) (by norm_num)
theorem B1588973 : Blo 1056613 1588973 := bbase (se 3 (by rfl) ⟨297932, by rfl⟩ : syracuseStep 1588973 = 595865) (by norm_num)
theorem B4013813 : Blo 1056613 4013813 := bbase (se 5 (by rfl) ⟨188147, by rfl⟩ : syracuseStep 4013813 = 376295) (by norm_num)
theorem B1588997 : Blo 1056613 1588997 := bbase (se 4 (by rfl) ⟨148968, by rfl⟩ : syracuseStep 1588997 = 297937) (by norm_num)
theorem B1589021 : Blo 1056613 1589021 := bbase (se 3 (by rfl) ⟨297941, by rfl⟩ : syracuseStep 1589021 = 595883) (by norm_num)
theorem B1589045 : Blo 1056613 1589045 := bbase (se 5 (by rfl) ⟨74486, by rfl⟩ : syracuseStep 1589045 = 148973) (by norm_num)
theorem B1589069 : Blo 1056613 1589069 := bbase (se 3 (by rfl) ⟨297950, by rfl⟩ : syracuseStep 1589069 = 595901) (by norm_num)
theorem B1785685 : Blo 1056613 1785685 := bbase (se 9 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 1785685 = 10463) (by norm_num)
theorem B1589093 : Blo 1056613 1589093 := bbase (se 4 (by rfl) ⟨148977, by rfl⟩ : syracuseStep 1589093 = 297955) (by norm_num)
theorem B1589117 : Blo 1056613 1589117 := bbase (se 3 (by rfl) ⟨297959, by rfl⟩ : syracuseStep 1589117 = 595919) (by norm_num)
theorem B1589141 : Blo 1056613 1589141 := bbase (se 6 (by rfl) ⟨37245, by rfl⟩ : syracuseStep 1589141 = 74491) (by norm_num)
theorem B1785773 : Blo 1056613 1785773 := bbase (se 3 (by rfl) ⟨334832, by rfl⟩ : syracuseStep 1785773 = 669665) (by norm_num)
theorem B1589165 : Blo 1056613 1589165 := bbase (se 3 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 1589165 = 595937) (by norm_num)
theorem B1589189 : Blo 1056613 1589189 := bbase (se 4 (by rfl) ⟨148986, by rfl⟩ : syracuseStep 1589189 = 297973) (by norm_num)
theorem B1589213 : Blo 1056613 1589213 := bbase (se 3 (by rfl) ⟨297977, by rfl⟩ : syracuseStep 1589213 = 595955) (by norm_num)
theorem B1589237 : Blo 1056613 1589237 := bbase (se 5 (by rfl) ⟨74495, by rfl⟩ : syracuseStep 1589237 = 148991) (by norm_num)
theorem B1589261 : Blo 1056613 1589261 := bbase (se 3 (by rfl) ⟨297986, by rfl⟩ : syracuseStep 1589261 = 595973) (by norm_num)
theorem B1589285 : Blo 1056613 1589285 := bbase (se 4 (by rfl) ⟨148995, by rfl⟩ : syracuseStep 1589285 = 297991) (by norm_num)
theorem B1785901 : Blo 1056613 1785901 := bbase (se 3 (by rfl) ⟨334856, by rfl⟩ : syracuseStep 1785901 = 669713) (by norm_num)
theorem B1589309 : Blo 1056613 1589309 := bbase (se 3 (by rfl) ⟨297995, by rfl⟩ : syracuseStep 1589309 = 595991) (by norm_num)
theorem B1589333 : Blo 1056613 1589333 := bbase (se 8 (by rfl) ⟨9312, by rfl⟩ : syracuseStep 1589333 = 18625) (by norm_num)
theorem B1589357 : Blo 1056613 1589357 := bbase (se 3 (by rfl) ⟨298004, by rfl⟩ : syracuseStep 1589357 = 596009) (by norm_num)
theorem B1785989 : Blo 1056613 1785989 := bbase (se 4 (by rfl) ⟨167436, by rfl⟩ : syracuseStep 1785989 = 334873) (by norm_num)
theorem B1589381 : Blo 1056613 1589381 := bbase (se 4 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 1589381 = 298009) (by norm_num)
theorem B1130645 : Blo 1056613 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B1589405 : Blo 1056613 1589405 := bbase (se 3 (by rfl) ⟨298013, by rfl⟩ : syracuseStep 1589405 = 596027) (by norm_num)
theorem B1589429 : Blo 1056613 1589429 := bbase (se 5 (by rfl) ⟨74504, by rfl⟩ : syracuseStep 1589429 = 149009) (by norm_num)
theorem B1589453 : Blo 1056613 1589453 := bbase (se 3 (by rfl) ⟨298022, by rfl⟩ : syracuseStep 1589453 = 596045) (by norm_num)
theorem B8044757 : Blo 1056613 8044757 := bbase (se 7 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 8044757 = 188549) (by norm_num)
theorem B1589477 : Blo 1056613 1589477 := bbase (se 4 (by rfl) ⟨149013, by rfl⟩ : syracuseStep 1589477 = 298027) (by norm_num)
theorem B5095669 : Blo 1056613 5095669 := bbase (se 5 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 5095669 = 477719) (by norm_num)
theorem B1589501 : Blo 1056613 1589501 := bbase (se 3 (by rfl) ⟨298031, by rfl⟩ : syracuseStep 1589501 = 596063) (by norm_num)
theorem B1786117 : Blo 1056613 1786117 := bbase (se 4 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 1786117 = 334897) (by norm_num)
theorem B1589525 : Blo 1056613 1589525 := bbase (se 6 (by rfl) ⟨37254, by rfl⟩ : syracuseStep 1589525 = 74509) (by norm_num)
theorem B1589549 : Blo 1056613 1589549 := bbase (se 3 (by rfl) ⟨298040, by rfl⟩ : syracuseStep 1589549 = 596081) (by norm_num)
theorem B1589573 : Blo 1056613 1589573 := bbase (se 4 (by rfl) ⟨149022, by rfl⟩ : syracuseStep 1589573 = 298045) (by norm_num)
theorem B1786205 : Blo 1056613 1786205 := bbase (se 3 (by rfl) ⟨334913, by rfl⟩ : syracuseStep 1786205 = 669827) (by norm_num)
theorem B1589597 : Blo 1056613 1589597 := bbase (se 3 (by rfl) ⟨298049, by rfl⟩ : syracuseStep 1589597 = 596099) (by norm_num)
theorem B1589621 : Blo 1056613 1589621 := bbase (se 5 (by rfl) ⟨74513, by rfl⟩ : syracuseStep 1589621 = 149027) (by norm_num)
theorem B1589645 : Blo 1056613 1589645 := bbase (se 3 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 1589645 = 596117) (by norm_num)
theorem B1589669 : Blo 1056613 1589669 := bbase (se 4 (by rfl) ⟨149031, by rfl⟩ : syracuseStep 1589669 = 298063) (by norm_num)
theorem B1589693 : Blo 1056613 1589693 := bbase (se 3 (by rfl) ⟨298067, by rfl⟩ : syracuseStep 1589693 = 596135) (by norm_num)
theorem B2539973 : Blo 1056613 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B1589717 : Blo 1056613 1589717 := bbase (se 7 (by rfl) ⟨18629, by rfl⟩ : syracuseStep 1589717 = 37259) (by norm_num)
theorem B1786333 : Blo 1056613 1786333 := bbase (se 3 (by rfl) ⟨334937, by rfl⟩ : syracuseStep 1786333 = 669875) (by norm_num)
theorem B1589741 : Blo 1056613 1589741 := bbase (se 3 (by rfl) ⟨298076, by rfl⟩ : syracuseStep 1589741 = 596153) (by norm_num)
theorem B1589765 : Blo 1056613 1589765 := bbase (se 4 (by rfl) ⟨149040, by rfl⟩ : syracuseStep 1589765 = 298081) (by norm_num)
theorem B1589789 : Blo 1056613 1589789 := bbase (se 3 (by rfl) ⟨298085, by rfl⟩ : syracuseStep 1589789 = 596171) (by norm_num)
theorem B1786421 : Blo 1056613 1786421 := bbase (se 5 (by rfl) ⟨83738, by rfl⟩ : syracuseStep 1786421 = 167477) (by norm_num)
theorem B1589813 : Blo 1056613 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B5358149 : Blo 1056613 5358149 := bbase (se 4 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 5358149 = 1004653) (by norm_num)
theorem B1589837 : Blo 1056613 1589837 := bbase (se 3 (by rfl) ⟨298094, by rfl⟩ : syracuseStep 1589837 = 596189) (by norm_num)
theorem B1131089 : Blo 1056613 1131089 := bbase (se 2 (by rfl) ⟨424158, by rfl⟩ : syracuseStep 1131089 = 848317) (by norm_num)
theorem B5423701 : Blo 1056613 5423701 := bbase (se 8 (by rfl) ⟨31779, by rfl⟩ : syracuseStep 5423701 = 63559) (by norm_num)
theorem B1589861 : Blo 1056613 1589861 := bbase (se 4 (by rfl) ⟨149049, by rfl⟩ : syracuseStep 1589861 = 298099) (by norm_num)
theorem B1589885 : Blo 1056613 1589885 := bbase (se 3 (by rfl) ⟨298103, by rfl⟩ : syracuseStep 1589885 = 596207) (by norm_num)
theorem B1589909 : Blo 1056613 1589909 := bbase (se 6 (by rfl) ⟨37263, by rfl⟩ : syracuseStep 1589909 = 74527) (by norm_num)
theorem B1589933 : Blo 1056613 1589933 := bbase (se 3 (by rfl) ⟨298112, by rfl⟩ : syracuseStep 1589933 = 596225) (by norm_num)
theorem B1786549 : Blo 1056613 1786549 := bbase (se 5 (by rfl) ⟨83744, by rfl⟩ : syracuseStep 1786549 = 167489) (by norm_num)
theorem B1589957 : Blo 1056613 1589957 := bbase (se 4 (by rfl) ⟨149058, by rfl⟩ : syracuseStep 1589957 = 298117) (by norm_num)
theorem B1589981 : Blo 1056613 1589981 := bbase (se 3 (by rfl) ⟨298121, by rfl⟩ : syracuseStep 1589981 = 596243) (by norm_num)
theorem B2540261 : Blo 1056613 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B1590005 : Blo 1056613 1590005 := bbase (se 5 (by rfl) ⟨74531, by rfl⟩ : syracuseStep 1590005 = 149063) (by norm_num)
theorem B1786637 : Blo 1056613 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B1590029 : Blo 1056613 1590029 := bbase (se 3 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 1590029 = 596261) (by norm_num)
theorem B1590053 : Blo 1056613 1590053 := bbase (se 4 (by rfl) ⟨149067, by rfl⟩ : syracuseStep 1590053 = 298135) (by norm_num)
theorem B1590077 : Blo 1056613 1590077 := bbase (se 3 (by rfl) ⟨298139, by rfl⟩ : syracuseStep 1590077 = 596279) (by norm_num)
theorem B1131337 : Blo 1056613 1131337 := bbase (se 2 (by rfl) ⟨424251, by rfl⟩ : syracuseStep 1131337 = 848503) (by norm_num)
theorem B2900821 : Blo 1056613 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B1590101 : Blo 1056613 1590101 := bbase (se 9 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 1590101 = 9317) (by norm_num)
theorem B1590125 : Blo 1056613 1590125 := bbase (se 3 (by rfl) ⟨298148, by rfl⟩ : syracuseStep 1590125 = 596297) (by norm_num)
theorem B1590149 : Blo 1056613 1590149 := bbase (se 4 (by rfl) ⟨149076, by rfl⟩ : syracuseStep 1590149 = 298153) (by norm_num)
theorem B1786765 : Blo 1056613 1786765 := bbase (se 3 (by rfl) ⟨335018, by rfl⟩ : syracuseStep 1786765 = 670037) (by norm_num)
theorem B1590173 : Blo 1056613 1590173 := bbase (se 3 (by rfl) ⟨298157, by rfl⟩ : syracuseStep 1590173 = 596315) (by norm_num)
theorem B1590197 : Blo 1056613 1590197 := bbase (se 5 (by rfl) ⟨74540, by rfl⟩ : syracuseStep 1590197 = 149081) (by norm_num)
theorem B1590221 : Blo 1056613 1590221 := bbase (se 3 (by rfl) ⟨298166, by rfl⟩ : syracuseStep 1590221 = 596333) (by norm_num)
theorem B1786853 : Blo 1056613 1786853 := bbase (se 4 (by rfl) ⟨167517, by rfl⟩ : syracuseStep 1786853 = 335035) (by norm_num)
theorem B1590245 : Blo 1056613 1590245 := bbase (se 4 (by rfl) ⟨149085, by rfl⟩ : syracuseStep 1590245 = 298171) (by norm_num)
theorem B1590269 : Blo 1056613 1590269 := bbase (se 3 (by rfl) ⟨298175, by rfl⟩ : syracuseStep 1590269 = 596351) (by norm_num)
theorem B1590293 : Blo 1056613 1590293 := bbase (se 6 (by rfl) ⟨37272, by rfl⟩ : syracuseStep 1590293 = 74545) (by norm_num)
theorem B1590317 : Blo 1056613 1590317 := bbase (se 3 (by rfl) ⟨298184, by rfl⟩ : syracuseStep 1590317 = 596369) (by norm_num)
theorem B1590341 : Blo 1056613 1590341 := bbase (se 4 (by rfl) ⟨149094, by rfl⟩ : syracuseStep 1590341 = 298189) (by norm_num)
theorem B1590365 : Blo 1056613 1590365 := bbase (se 3 (by rfl) ⟨298193, by rfl⟩ : syracuseStep 1590365 = 596387) (by norm_num)
theorem B1786981 : Blo 1056613 1786981 := bbase (se 4 (by rfl) ⟨167529, by rfl⟩ : syracuseStep 1786981 = 335059) (by norm_num)
theorem B1590389 : Blo 1056613 1590389 := bbase (se 5 (by rfl) ⟨74549, by rfl⟩ : syracuseStep 1590389 = 149099) (by norm_num)
theorem B1590413 : Blo 1056613 1590413 := bbase (se 3 (by rfl) ⟨298202, by rfl⟩ : syracuseStep 1590413 = 596405) (by norm_num)
theorem B1590437 : Blo 1056613 1590437 := bbase (se 4 (by rfl) ⟨149103, by rfl⟩ : syracuseStep 1590437 = 298207) (by norm_num)
theorem B1787069 : Blo 1056613 1787069 := bbase (se 3 (by rfl) ⟨335075, by rfl⟩ : syracuseStep 1787069 = 670151) (by norm_num)
theorem B1590461 : Blo 1056613 1590461 := bbase (se 3 (by rfl) ⟨298211, by rfl⟩ : syracuseStep 1590461 = 596423) (by norm_num)
theorem B1590485 : Blo 1056613 1590485 := bbase (se 7 (by rfl) ⟨18638, by rfl⟩ : syracuseStep 1590485 = 37277) (by norm_num)
theorem B1590509 : Blo 1056613 1590509 := bbase (se 3 (by rfl) ⟨298220, by rfl⟩ : syracuseStep 1590509 = 596441) (by norm_num)
theorem B1131769 : Blo 1056613 1131769 := bbase (se 2 (by rfl) ⟨424413, by rfl⟩ : syracuseStep 1131769 = 848827) (by norm_num)
theorem B1590533 : Blo 1056613 1590533 := bbase (se 4 (by rfl) ⟨149112, by rfl⟩ : syracuseStep 1590533 = 298225) (by norm_num)
theorem B1590557 : Blo 1056613 1590557 := bbase (se 3 (by rfl) ⟨298229, by rfl⟩ : syracuseStep 1590557 = 596459) (by norm_num)
theorem B1590581 : Blo 1056613 1590581 := bbase (se 5 (by rfl) ⟨74558, by rfl⟩ : syracuseStep 1590581 = 149117) (by norm_num)
theorem B1787197 : Blo 1056613 1787197 := bbase (se 3 (by rfl) ⟨335099, by rfl⟩ : syracuseStep 1787197 = 670199) (by norm_num)
theorem B1131841 : Blo 1056613 1131841 := bbase (se 2 (by rfl) ⟨424440, by rfl⟩ : syracuseStep 1131841 = 848881) (by norm_num)
theorem B1590605 : Blo 1056613 1590605 := bbase (se 3 (by rfl) ⟨298238, by rfl⟩ : syracuseStep 1590605 = 596477) (by norm_num)
theorem B1590629 : Blo 1056613 1590629 := bbase (se 4 (by rfl) ⟨149121, by rfl⟩ : syracuseStep 1590629 = 298243) (by norm_num)
theorem B1590653 : Blo 1056613 1590653 := bbase (se 3 (by rfl) ⟨298247, by rfl⟩ : syracuseStep 1590653 = 596495) (by norm_num)
theorem B1787285 : Blo 1056613 1787285 := bbase (se 6 (by rfl) ⟨41889, by rfl⟩ : syracuseStep 1787285 = 83779) (by norm_num)
theorem B1590677 : Blo 1056613 1590677 := bbase (se 6 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 1590677 = 74563) (by norm_num)
theorem B1590701 : Blo 1056613 1590701 := bbase (se 3 (by rfl) ⟨298256, by rfl⟩ : syracuseStep 1590701 = 596513) (by norm_num)
theorem B1590725 : Blo 1056613 1590725 := bbase (se 4 (by rfl) ⟨149130, by rfl⟩ : syracuseStep 1590725 = 298261) (by norm_num)
theorem B1590749 : Blo 1056613 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1590773 : Blo 1056613 1590773 := bbase (se 5 (by rfl) ⟨74567, by rfl⟩ : syracuseStep 1590773 = 149135) (by norm_num)
theorem B1590797 : Blo 1056613 1590797 := bbase (se 3 (by rfl) ⟨298274, by rfl⟩ : syracuseStep 1590797 = 596549) (by norm_num)
theorem B1787413 : Blo 1056613 1787413 := bbase (se 6 (by rfl) ⟨41892, by rfl⟩ : syracuseStep 1787413 = 83785) (by norm_num)
theorem B1590821 : Blo 1056613 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B2573869 : Blo 1056613 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B1590845 : Blo 1056613 1590845 := bbase (se 3 (by rfl) ⟨298283, by rfl⟩ : syracuseStep 1590845 = 596567) (by norm_num)
theorem B1590869 : Blo 1056613 1590869 := bbase (se 8 (by rfl) ⟨9321, by rfl⟩ : syracuseStep 1590869 = 18643) (by norm_num)
theorem B1787501 : Blo 1056613 1787501 := bbase (se 3 (by rfl) ⟨335156, by rfl⟩ : syracuseStep 1787501 = 670313) (by norm_num)
theorem B1590893 : Blo 1056613 1590893 := bbase (se 3 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 1590893 = 596585) (by norm_num)
theorem B4834933 : Blo 1056613 4834933 := bbase (se 5 (by rfl) ⟨226637, by rfl⟩ : syracuseStep 4834933 = 453275) (by norm_num)
theorem B1590917 : Blo 1056613 1590917 := bbase (se 4 (by rfl) ⟨149148, by rfl⟩ : syracuseStep 1590917 = 298297) (by norm_num)
theorem B6440597 : Blo 1056613 6440597 := bbase (se 6 (by rfl) ⟨150951, by rfl⟩ : syracuseStep 6440597 = 301903) (by norm_num)
theorem B1132213 : Blo 1056613 1132213 := bbase (se 5 (by rfl) ⟨53072, by rfl⟩ : syracuseStep 1132213 = 106145) (by norm_num)
theorem B2377421 : Blo 1056613 2377421 := bbase (se 3 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 2377421 = 891533) (by norm_num)
theorem B1787629 : Blo 1056613 1787629 := bbase (se 3 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 1787629 = 670361) (by norm_num)
theorem B3098357 : Blo 1056613 3098357 := bbase (se 5 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 3098357 = 290471) (by norm_num)
theorem B2377493 : Blo 1056613 2377493 := bbase (se 6 (by rfl) ⟨55722, by rfl⟩ : syracuseStep 2377493 = 111445) (by norm_num)
theorem B4015925 : Blo 1056613 4015925 := bbase (se 5 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 4015925 = 376493) (by norm_num)
theorem B1787717 : Blo 1056613 1787717 := bbase (se 4 (by rfl) ⟨167598, by rfl⟩ : syracuseStep 1787717 = 335197) (by norm_num)
theorem B5359445 : Blo 1056613 5359445 := bbase (se 9 (by rfl) ⟨15701, by rfl⟩ : syracuseStep 5359445 = 31403) (by norm_num)
theorem B2377565 : Blo 1056613 2377565 := bbase (se 3 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 2377565 = 891587) (by norm_num)
theorem B2377637 : Blo 1056613 2377637 := bbase (se 4 (by rfl) ⟨222903, by rfl⟩ : syracuseStep 2377637 = 445807) (by norm_num)
theorem B1787845 : Blo 1056613 1787845 := bbase (se 4 (by rfl) ⟨167610, by rfl⟩ : syracuseStep 1787845 = 335221) (by norm_num)
theorem B2377709 : Blo 1056613 2377709 := bbase (se 3 (by rfl) ⟨445820, by rfl⟩ : syracuseStep 2377709 = 891641) (by norm_num)
theorem B1787933 : Blo 1056613 1787933 := bbase (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) (by norm_num)
theorem B1132589 : Blo 1056613 1132589 := bbase (se 3 (by rfl) ⟨212360, by rfl⟩ : syracuseStep 1132589 = 424721) (by norm_num)
theorem B2377781 : Blo 1056613 2377781 := bbase (se 5 (by rfl) ⟨111458, by rfl⟩ : syracuseStep 2377781 = 222917) (by norm_num)
theorem B12863573 : Blo 1056613 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B4016213 : Blo 1056613 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B8144981 : Blo 1056613 8144981 := bbase (se 8 (by rfl) ⟨47724, by rfl⟩ : syracuseStep 8144981 = 95449) (by norm_num)
theorem B2377853 : Blo 1056613 2377853 := bbase (se 3 (by rfl) ⟨445847, by rfl⟩ : syracuseStep 2377853 = 891695) (by norm_num)
theorem B1788061 : Blo 1056613 1788061 := bbase (se 3 (by rfl) ⟨335261, by rfl⟩ : syracuseStep 1788061 = 670523) (by norm_num)
theorem B2377925 : Blo 1056613 2377925 := bbase (se 4 (by rfl) ⟨222930, by rfl⟩ : syracuseStep 2377925 = 445861) (by norm_num)
theorem B3623125 : Blo 1056613 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B1788149 : Blo 1056613 1788149 := bbase (se 5 (by rfl) ⟨83819, by rfl⟩ : syracuseStep 1788149 = 167639) (by norm_num)
theorem B2377997 : Blo 1056613 2377997 := bbase (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) (by norm_num)
theorem B2378069 : Blo 1056613 2378069 := bbase (se 10 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 2378069 = 6967) (by norm_num)
theorem B1788277 : Blo 1056613 1788277 := bbase (se 5 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 1788277 = 167651) (by norm_num)
theorem B2378141 : Blo 1056613 2378141 := bbase (se 3 (by rfl) ⟨445901, by rfl⟩ : syracuseStep 2378141 = 891803) (by norm_num)
theorem B1788365 : Blo 1056613 1788365 := bbase (se 3 (by rfl) ⟨335318, by rfl⟩ : syracuseStep 1788365 = 670637) (by norm_num)
theorem B2378213 : Blo 1056613 2378213 := bbase (se 4 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 2378213 = 445915) (by norm_num)
theorem B3394037 : Blo 1056613 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B2378285 : Blo 1056613 2378285 := bbase (se 3 (by rfl) ⟨445928, by rfl⟩ : syracuseStep 2378285 = 891857) (by norm_num)
theorem B1788493 : Blo 1056613 1788493 := bbase (se 3 (by rfl) ⟨335342, by rfl⟩ : syracuseStep 1788493 = 670685) (by norm_num)
theorem B2378357 : Blo 1056613 2378357 := bbase (se 5 (by rfl) ⟨111485, by rfl⟩ : syracuseStep 2378357 = 222971) (by norm_num)
theorem B1788581 : Blo 1056613 1788581 := bbase (se 4 (by rfl) ⟨167679, by rfl⟩ : syracuseStep 1788581 = 335359) (by norm_num)
theorem B2378429 : Blo 1056613 2378429 := bbase (se 3 (by rfl) ⟨445955, by rfl⟩ : syracuseStep 2378429 = 891911) (by norm_num)
theorem B2378501 : Blo 1056613 2378501 := bbase (se 4 (by rfl) ⟨222984, by rfl⟩ : syracuseStep 2378501 = 445969) (by norm_num)
theorem B2542357 : Blo 1056613 2542357 := bbase (se 6 (by rfl) ⟨59586, by rfl⟩ : syracuseStep 2542357 = 119173) (by norm_num)
theorem B1788709 : Blo 1056613 1788709 := bbase (se 4 (by rfl) ⟨167691, by rfl⟩ : syracuseStep 1788709 = 335383) (by norm_num)
theorem B2378573 : Blo 1056613 2378573 := bbase (se 3 (by rfl) ⟨445982, by rfl⟩ : syracuseStep 2378573 = 891965) (by norm_num)
theorem B1788797 : Blo 1056613 1788797 := bbase (se 3 (by rfl) ⟨335399, by rfl⟩ : syracuseStep 1788797 = 670799) (by norm_num)
theorem B1428373 : Blo 1056613 1428373 := bbase (se 6 (by rfl) ⟨33477, by rfl⟩ : syracuseStep 1428373 = 66955) (by norm_num)
theorem B2378645 : Blo 1056613 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B2378717 : Blo 1056613 2378717 := bbase (se 3 (by rfl) ⟨446009, by rfl⟩ : syracuseStep 2378717 = 892019) (by norm_num)
theorem B1788925 : Blo 1056613 1788925 := bbase (se 3 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 1788925 = 670847) (by norm_num)
theorem B2378789 : Blo 1056613 2378789 := bbase (se 4 (by rfl) ⟨223011, by rfl⟩ : syracuseStep 2378789 = 446023) (by norm_num)
theorem B1789013 : Blo 1056613 1789013 := bbase (se 8 (by rfl) ⟨10482, by rfl⟩ : syracuseStep 1789013 = 20965) (by norm_num)
theorem B5360741 : Blo 1056613 5360741 := bbase (se 4 (by rfl) ⟨502569, by rfl⟩ : syracuseStep 5360741 = 1005139) (by norm_num)
theorem B2378861 : Blo 1056613 2378861 := bbase (se 3 (by rfl) ⟨446036, by rfl⟩ : syracuseStep 2378861 = 892073) (by norm_num)
theorem B2378933 : Blo 1056613 2378933 := bbase (se 5 (by rfl) ⟨111512, by rfl⟩ : syracuseStep 2378933 = 223025) (by norm_num)
theorem B1789141 : Blo 1056613 1789141 := bbase (se 7 (by rfl) ⟨20966, by rfl⟩ : syracuseStep 1789141 = 41933) (by norm_num)
theorem B4017397 : Blo 1056613 4017397 := bbase (se 5 (by rfl) ⟨188315, by rfl⟩ : syracuseStep 4017397 = 376631) (by norm_num)
theorem B2379005 : Blo 1056613 2379005 := bbase (se 3 (by rfl) ⟨446063, by rfl⟩ : syracuseStep 2379005 = 892127) (by norm_num)
theorem B1789229 : Blo 1056613 1789229 := bbase (se 3 (by rfl) ⟨335480, by rfl⟩ : syracuseStep 1789229 = 670961) (by norm_num)
theorem B2379077 : Blo 1056613 2379077 := bbase (se 4 (by rfl) ⟨223038, by rfl⟩ : syracuseStep 2379077 = 446077) (by norm_num)
theorem B2379149 : Blo 1056613 2379149 := bbase (se 3 (by rfl) ⟨446090, by rfl⟩ : syracuseStep 2379149 = 892181) (by norm_num)
theorem B2543021 : Blo 1056613 2543021 := bbase (se 3 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 2543021 = 953633) (by norm_num)
theorem B1789357 : Blo 1056613 1789357 := bbase (se 3 (by rfl) ⟨335504, by rfl⟩ : syracuseStep 1789357 = 671009) (by norm_num)
theorem B2379221 : Blo 1056613 2379221 := bbase (se 7 (by rfl) ⟨27881, by rfl⟩ : syracuseStep 2379221 = 55763) (by norm_num)
theorem B1789445 : Blo 1056613 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B2379293 : Blo 1056613 2379293 := bbase (se 3 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 2379293 = 892235) (by norm_num)
theorem B4017701 : Blo 1056613 4017701 := bbase (se 4 (by rfl) ⟨376659, by rfl⟩ : syracuseStep 4017701 = 753319) (by norm_num)
theorem B9653813 : Blo 1056613 9653813 := bbase (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) (by norm_num)
theorem B2379365 : Blo 1056613 2379365 := bbase (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) (by norm_num)
theorem B1789573 : Blo 1056613 1789573 := bbase (se 4 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 1789573 = 335545) (by norm_num)
theorem B2379437 : Blo 1056613 2379437 := bbase (se 3 (by rfl) ⟨446144, by rfl⟩ : syracuseStep 2379437 = 892289) (by norm_num)
theorem B1789661 : Blo 1056613 1789661 := bbase (se 3 (by rfl) ⟨335561, by rfl⟩ : syracuseStep 1789661 = 671123) (by norm_num)
theorem B2379509 : Blo 1056613 2379509 := bbase (se 5 (by rfl) ⟨111539, by rfl⟩ : syracuseStep 2379509 = 223079) (by norm_num)
theorem B3624725 : Blo 1056613 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2379581 : Blo 1056613 2379581 := bbase (se 3 (by rfl) ⟨446171, by rfl⟩ : syracuseStep 2379581 = 892343) (by norm_num)
theorem B36622165 : Blo 1056613 36622165 := bbase (se 9 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 36622165 = 214583) (by norm_num)
theorem B1429373 : Blo 1056613 1429373 := bbase (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) (by norm_num)
theorem B2379653 : Blo 1056613 2379653 := bbase (se 4 (by rfl) ⟨223092, by rfl⟩ : syracuseStep 2379653 = 446185) (by norm_num)
theorem B2379725 : Blo 1056613 2379725 := bbase (se 3 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 2379725 = 892397) (by norm_num)
theorem B2379797 : Blo 1056613 2379797 := bbase (se 6 (by rfl) ⟨55776, by rfl⟩ : syracuseStep 2379797 = 111553) (by norm_num)
theorem B2674741 : Blo 1056613 2674741 := bbase (se 5 (by rfl) ⟨125378, by rfl⟩ : syracuseStep 2674741 = 250757) (by norm_num)
theorem B2379869 : Blo 1056613 2379869 := bbase (se 3 (by rfl) ⟨446225, by rfl⟩ : syracuseStep 2379869 = 892451) (by norm_num)
theorem B2674853 : Blo 1056613 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B2379941 : Blo 1056613 2379941 := bbase (se 4 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 2379941 = 446239) (by norm_num)
theorem B2380013 : Blo 1056613 2380013 := bbase (se 3 (by rfl) ⟨446252, by rfl⟩ : syracuseStep 2380013 = 892505) (by norm_num)
theorem B4837637 : Blo 1056613 4837637 := bbase (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) (by norm_num)
theorem B1429805 : Blo 1056613 1429805 := bbase (se 3 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 1429805 = 536177) (by norm_num)
theorem B2380085 : Blo 1056613 2380085 := bbase (se 5 (by rfl) ⟨111566, by rfl⟩ : syracuseStep 2380085 = 223133) (by norm_num)
theorem B2675045 : Blo 1056613 2675045 := bbase (se 4 (by rfl) ⟨250785, by rfl⟩ : syracuseStep 2675045 = 501571) (by norm_num)
theorem B5362037 : Blo 1056613 5362037 := bbase (se 5 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 5362037 = 502691) (by norm_num)
theorem B2380157 : Blo 1056613 2380157 := bbase (se 3 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 2380157 = 892559) (by norm_num)
theorem B4837781 : Blo 1056613 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B2380229 : Blo 1056613 2380229 := bbase (se 4 (by rfl) ⟨223146, by rfl⟩ : syracuseStep 2380229 = 446293) (by norm_num)
theorem B2380301 : Blo 1056613 2380301 := bbase (se 3 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 2380301 = 892613) (by norm_num)
theorem B11424341 : Blo 1056613 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B2380373 : Blo 1056613 2380373 := bbase (se 8 (by rfl) ⟨13947, by rfl⟩ : syracuseStep 2380373 = 27895) (by norm_num)
theorem B2380445 : Blo 1056613 2380445 := bbase (se 3 (by rfl) ⟨446333, by rfl⟩ : syracuseStep 2380445 = 892667) (by norm_num)
theorem B2675389 : Blo 1056613 2675389 := bbase (se 3 (by rfl) ⟨501635, by rfl⟩ : syracuseStep 2675389 = 1003271) (by norm_num)
theorem B3396293 : Blo 1056613 3396293 := bbase (se 4 (by rfl) ⟨318402, by rfl⟩ : syracuseStep 3396293 = 636805) (by norm_num)
theorem B2380517 : Blo 1056613 2380517 := bbase (se 4 (by rfl) ⟨223173, by rfl⟩ : syracuseStep 2380517 = 446347) (by norm_num)
theorem B10867445 : Blo 1056613 10867445 := bbase (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) (by norm_num)
theorem B1430293 : Blo 1056613 1430293 := bbase (se 6 (by rfl) ⟨33522, by rfl⟩ : syracuseStep 1430293 = 67045) (by norm_num)
theorem B2675501 : Blo 1056613 2675501 := bbase (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) (by norm_num)
theorem B2380589 : Blo 1056613 2380589 := bbase (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) (by norm_num)
theorem B1692533 : Blo 1056613 1692533 := bbase (se 5 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 1692533 = 158675) (by norm_num)
theorem B2380661 : Blo 1056613 2380661 := bbase (se 5 (by rfl) ⟨111593, by rfl⟩ : syracuseStep 2380661 = 223187) (by norm_num)
theorem B2380733 : Blo 1056613 2380733 := bbase (se 3 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 2380733 = 892775) (by norm_num)
theorem B2675693 : Blo 1056613 2675693 := bbase (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) (by norm_num)
theorem B2380805 : Blo 1056613 2380805 := bbase (se 4 (by rfl) ⟨223200, by rfl⟩ : syracuseStep 2380805 = 446401) (by norm_num)
theorem B11457557 : Blo 1056613 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B1692733 : Blo 1056613 1692733 := bbase (se 3 (by rfl) ⟨317387, by rfl⟩ : syracuseStep 1692733 = 634775) (by norm_num)
theorem B2380877 : Blo 1056613 2380877 := bbase (se 3 (by rfl) ⟨446414, by rfl⟩ : syracuseStep 2380877 = 892829) (by norm_num)
theorem B2380949 : Blo 1056613 2380949 := bbase (se 6 (by rfl) ⟨55803, by rfl⟩ : syracuseStep 2380949 = 111607) (by norm_num)
theorem B2544797 : Blo 1056613 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B2381021 : Blo 1056613 2381021 := bbase (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) (by norm_num)
theorem B3265813 : Blo 1056613 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B2381093 : Blo 1056613 2381093 := bbase (se 4 (by rfl) ⟨223227, by rfl⟩ : syracuseStep 2381093 = 446455) (by norm_num)
theorem B1692989 : Blo 1056613 1692989 := bbase (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) (by norm_num)
theorem B2676037 : Blo 1056613 2676037 := bbase (se 4 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 2676037 = 501757) (by norm_num)
theorem B2381165 : Blo 1056613 2381165 := bbase (se 3 (by rfl) ⟨446468, by rfl⟩ : syracuseStep 2381165 = 892937) (by norm_num)
theorem B5428613 : Blo 1056613 5428613 := bbase (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) (by norm_num)
theorem B2676149 : Blo 1056613 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B2381237 : Blo 1056613 2381237 := bbase (se 5 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 2381237 = 223241) (by norm_num)
theorem B3397061 : Blo 1056613 3397061 := bbase (se 4 (by rfl) ⟨318474, by rfl⟩ : syracuseStep 3397061 = 636949) (by norm_num)
theorem B2381309 : Blo 1056613 2381309 := bbase (se 3 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 2381309 = 892991) (by norm_num)
theorem B2381381 : Blo 1056613 2381381 := bbase (se 4 (by rfl) ⟨223254, by rfl⟩ : syracuseStep 2381381 = 446509) (by norm_num)
theorem B4019813 : Blo 1056613 4019813 := bbase (se 4 (by rfl) ⟨376857, by rfl⟩ : syracuseStep 4019813 = 753715) (by norm_num)
theorem B2676341 : Blo 1056613 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B1431157 : Blo 1056613 1431157 := bbase (se 5 (by rfl) ⟨67085, by rfl⟩ : syracuseStep 1431157 = 134171) (by norm_num)
theorem B5363333 : Blo 1056613 5363333 := bbase (se 4 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 5363333 = 1005625) (by norm_num)
theorem B2381453 : Blo 1056613 2381453 := bbase (se 3 (by rfl) ⟨446522, by rfl⟩ : syracuseStep 2381453 = 893045) (by norm_num)
theorem B8574677 : Blo 1056613 8574677 := bbase (se 7 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 8574677 = 200969) (by norm_num)
theorem B2381525 : Blo 1056613 2381525 := bbase (se 7 (by rfl) ⟨27908, by rfl⟩ : syracuseStep 2381525 = 55817) (by norm_num)
theorem B17880853 : Blo 1056613 17880853 := bbase (se 6 (by rfl) ⟨419082, by rfl⟩ : syracuseStep 17880853 = 838165) (by norm_num)
theorem B2381597 : Blo 1056613 2381597 := bbase (se 3 (by rfl) ⟨446549, by rfl⟩ : syracuseStep 2381597 = 893099) (by norm_num)
theorem B2381669 : Blo 1056613 2381669 := bbase (se 4 (by rfl) ⟨223281, by rfl⟩ : syracuseStep 2381669 = 446563) (by norm_num)
theorem B4020101 : Blo 1056613 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B2381741 : Blo 1056613 2381741 := bbase (se 3 (by rfl) ⟨446576, by rfl⟩ : syracuseStep 2381741 = 893153) (by norm_num)
theorem B3397573 : Blo 1056613 3397573 := bbase (se 4 (by rfl) ⟨318522, by rfl⟩ : syracuseStep 3397573 = 637045) (by norm_num)
theorem B2676685 : Blo 1056613 2676685 := bbase (se 3 (by rfl) ⟨501878, by rfl⟩ : syracuseStep 2676685 = 1003757) (by norm_num)
theorem B2414549 : Blo 1056613 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B2381813 : Blo 1056613 2381813 := bbase (se 5 (by rfl) ⟨111647, by rfl⟩ : syracuseStep 2381813 = 223295) (by norm_num)
theorem B2676797 : Blo 1056613 2676797 := bbase (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) (by norm_num)
theorem B2381885 : Blo 1056613 2381885 := bbase (se 3 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 2381885 = 893207) (by norm_num)
theorem B2381957 : Blo 1056613 2381957 := bbase (se 4 (by rfl) ⟨223308, by rfl⟩ : syracuseStep 2381957 = 446617) (by norm_num)
theorem B2382029 : Blo 1056613 2382029 := bbase (se 3 (by rfl) ⟨446630, by rfl⟩ : syracuseStep 2382029 = 893261) (by norm_num)
theorem B2676989 : Blo 1056613 2676989 := bbase (se 3 (by rfl) ⟨501935, by rfl⟩ : syracuseStep 2676989 = 1003871) (by norm_num)
theorem B2382101 : Blo 1056613 2382101 := bbase (se 6 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 2382101 = 111661) (by norm_num)
theorem B2382173 : Blo 1056613 2382173 := bbase (se 3 (by rfl) ⟨446657, by rfl⟩ : syracuseStep 2382173 = 893315) (by norm_num)
theorem B1694117 : Blo 1056613 1694117 := bbase (se 4 (by rfl) ⟨158823, by rfl⟩ : syracuseStep 1694117 = 317647) (by norm_num)
theorem B2382245 : Blo 1056613 2382245 := bbase (se 4 (by rfl) ⟨223335, by rfl⟩ : syracuseStep 2382245 = 446671) (by norm_num)
theorem B2382317 : Blo 1056613 2382317 := bbase (se 3 (by rfl) ⟨446684, by rfl⟩ : syracuseStep 2382317 = 893369) (by norm_num)
theorem B2382389 : Blo 1056613 2382389 := bbase (se 5 (by rfl) ⟨111674, by rfl⟩ : syracuseStep 2382389 = 223349) (by norm_num)
theorem B1071689 : Blo 1056613 1071689 := bbase (se 2 (by rfl) ⟨401883, by rfl⟩ : syracuseStep 1071689 = 803767) (by norm_num)
theorem B2677333 : Blo 1056613 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B2382461 : Blo 1056613 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B2677445 : Blo 1056613 2677445 := bbase (se 4 (by rfl) ⟨251010, by rfl⟩ : syracuseStep 2677445 = 502021) (by norm_num)
theorem B2382533 : Blo 1056613 2382533 := bbase (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) (by norm_num)
theorem B2382605 : Blo 1056613 2382605 := bbase (se 3 (by rfl) ⟨446738, by rfl⟩ : syracuseStep 2382605 = 893477) (by norm_num)
theorem B2382677 : Blo 1056613 2382677 := bbase (se 9 (by rfl) ⟨6980, by rfl⟩ : syracuseStep 2382677 = 13961) (by norm_num)
theorem B2677637 : Blo 1056613 2677637 := bbase (se 4 (by rfl) ⟨251028, by rfl⟩ : syracuseStep 2677637 = 502057) (by norm_num)
theorem B5364629 : Blo 1056613 5364629 := bbase (se 6 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 5364629 = 251467) (by norm_num)
theorem B6445973 : Blo 1056613 6445973 := bbase (se 6 (by rfl) ⟨151077, by rfl⟩ : syracuseStep 6445973 = 302155) (by norm_num)
theorem B2382749 : Blo 1056613 2382749 := bbase (se 3 (by rfl) ⟨446765, by rfl⟩ : syracuseStep 2382749 = 893531) (by norm_num)
theorem B1694629 : Blo 1056613 1694629 := bbase (se 4 (by rfl) ⟨158871, by rfl⟩ : syracuseStep 1694629 = 317743) (by norm_num)
theorem B2382821 : Blo 1056613 2382821 := bbase (se 4 (by rfl) ⟨223389, by rfl⟩ : syracuseStep 2382821 = 446779) (by norm_num)
theorem B4021285 : Blo 1056613 4021285 := bbase (se 4 (by rfl) ⟨376995, by rfl⟩ : syracuseStep 4021285 = 753991) (by norm_num)
theorem B2382893 : Blo 1056613 2382893 := bbase (se 3 (by rfl) ⟨446792, by rfl⟩ : syracuseStep 2382893 = 893585) (by norm_num)
theorem B2382965 : Blo 1056613 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B2415781 : Blo 1056613 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B3267749 : Blo 1056613 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B2383037 : Blo 1056613 2383037 := bbase (se 3 (by rfl) ⟨446819, by rfl⟩ : syracuseStep 2383037 = 893639) (by norm_num)
theorem B2546893 : Blo 1056613 2546893 := bbase (se 3 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 2546893 = 955085) (by norm_num)
theorem B2677981 : Blo 1056613 2677981 := bbase (se 3 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 2677981 = 1004243) (by norm_num)
theorem B2383109 : Blo 1056613 2383109 := bbase (se 4 (by rfl) ⟨223416, by rfl⟩ : syracuseStep 2383109 = 446833) (by norm_num)
theorem B2415901 : Blo 1056613 2415901 := bbase (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) (by norm_num)
theorem B2678093 : Blo 1056613 2678093 := bbase (se 3 (by rfl) ⟨502142, by rfl⟩ : syracuseStep 2678093 = 1004285) (by norm_num)
theorem B2383181 : Blo 1056613 2383181 := bbase (se 3 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 2383181 = 893693) (by norm_num)
theorem B13557077 : Blo 1056613 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B4021589 : Blo 1056613 4021589 := bbase (se 11 (by rfl) ⟨2945, by rfl⟩ : syracuseStep 4021589 = 5891) (by norm_num)
theorem B2383253 : Blo 1056613 2383253 := bbase (se 6 (by rfl) ⟨55857, by rfl⟩ : syracuseStep 2383253 = 111715) (by norm_num)
theorem B1072549 : Blo 1056613 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B1695173 : Blo 1056613 1695173 := bbase (se 4 (by rfl) ⟨158922, by rfl⟩ : syracuseStep 1695173 = 317845) (by norm_num)
theorem B2383325 : Blo 1056613 2383325 := bbase (se 3 (by rfl) ⟨446873, by rfl⟩ : syracuseStep 2383325 = 893747) (by norm_num)
theorem B2678285 : Blo 1056613 2678285 := bbase (se 3 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 2678285 = 1004357) (by norm_num)
theorem B1629733 : Blo 1056613 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B2383397 : Blo 1056613 2383397 := bbase (se 4 (by rfl) ⟨223443, by rfl⟩ : syracuseStep 2383397 = 446887) (by norm_num)
theorem B2383469 : Blo 1056613 2383469 := bbase (se 3 (by rfl) ⟨446900, by rfl⟩ : syracuseStep 2383469 = 893801) (by norm_num)
theorem B2383541 : Blo 1056613 2383541 := bbase (se 5 (by rfl) ⟨111728, by rfl⟩ : syracuseStep 2383541 = 223457) (by norm_num)
theorem B1072849 : Blo 1056613 1072849 := bbase (se 2 (by rfl) ⟨402318, by rfl⟩ : syracuseStep 1072849 = 804637) (by norm_num)
theorem B2383613 : Blo 1056613 2383613 := bbase (se 3 (by rfl) ⟨446927, by rfl⟩ : syracuseStep 2383613 = 893855) (by norm_num)
theorem B8052533 : Blo 1056613 8052533 := bbase (se 5 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 8052533 = 754925) (by norm_num)
theorem B2383685 : Blo 1056613 2383685 := bbase (se 4 (by rfl) ⟨223470, by rfl⟩ : syracuseStep 2383685 = 446941) (by norm_num)
theorem B2678629 : Blo 1056613 2678629 := bbase (se 4 (by rfl) ⟨251121, by rfl⟩ : syracuseStep 2678629 = 502243) (by norm_num)
theorem B1269641 : Blo 1056613 1269641 := bbase (se 2 (by rfl) ⟨476115, by rfl⟩ : syracuseStep 1269641 = 952231) (by norm_num)
theorem B2383757 : Blo 1056613 2383757 := bbase (se 3 (by rfl) ⟨446954, by rfl⟩ : syracuseStep 2383757 = 893909) (by norm_num)
theorem B2547605 : Blo 1056613 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B2678741 : Blo 1056613 2678741 := bbase (se 7 (by rfl) ⟨31391, by rfl⟩ : syracuseStep 2678741 = 62783) (by norm_num)
theorem B2383829 : Blo 1056613 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B6119381 : Blo 1056613 6119381 := bbase (se 7 (by rfl) ⟨71711, by rfl⟩ : syracuseStep 6119381 = 143423) (by norm_num)
theorem B1695725 : Blo 1056613 1695725 := bbase (se 3 (by rfl) ⟨317948, by rfl⟩ : syracuseStep 1695725 = 635897) (by norm_num)
theorem B1695757 : Blo 1056613 1695757 := bbase (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) (by norm_num)
theorem B2383901 : Blo 1056613 2383901 := bbase (se 3 (by rfl) ⟨446981, by rfl⟩ : syracuseStep 2383901 = 893963) (by norm_num)
theorem B4284485 : Blo 1056613 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B2383973 : Blo 1056613 2383973 := bbase (se 4 (by rfl) ⟨223497, by rfl⟩ : syracuseStep 2383973 = 446995) (by norm_num)
theorem B2678933 : Blo 1056613 2678933 := bbase (se 6 (by rfl) ⟨62787, by rfl⟩ : syracuseStep 2678933 = 125575) (by norm_num)
theorem B5365925 : Blo 1056613 5365925 := bbase (se 4 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 5365925 = 1006111) (by norm_num)
theorem B2384045 : Blo 1056613 2384045 := bbase (se 3 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 2384045 = 894017) (by norm_num)
theorem B2384117 : Blo 1056613 2384117 := bbase (se 5 (by rfl) ⟨111755, by rfl⟩ : syracuseStep 2384117 = 223511) (by norm_num)
theorem B5726485 : Blo 1056613 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B2547989 : Blo 1056613 2547989 := bbase (se 6 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 2547989 = 119437) (by norm_num)
theorem B2384189 : Blo 1056613 2384189 := bbase (se 3 (by rfl) ⟨447035, by rfl⟩ : syracuseStep 2384189 = 894071) (by norm_num)
theorem B235266389 : Blo 1056613 235266389 := bbase (se 10 (by rfl) ⟨344628, by rfl⟩ : syracuseStep 235266389 = 689257) (by norm_num)
theorem B2384261 : Blo 1056613 2384261 := bbase (se 4 (by rfl) ⟨223524, by rfl⟩ : syracuseStep 2384261 = 447049) (by norm_num)
theorem B2384333 : Blo 1056613 2384333 := bbase (se 3 (by rfl) ⟨447062, by rfl⟩ : syracuseStep 2384333 = 894125) (by norm_num)
theorem B2679277 : Blo 1056613 2679277 := bbase (se 3 (by rfl) ⟨502364, by rfl⟩ : syracuseStep 2679277 = 1004729) (by norm_num)
theorem B2384405 : Blo 1056613 2384405 := bbase (se 6 (by rfl) ⟨55884, by rfl⟩ : syracuseStep 2384405 = 111769) (by norm_num)
theorem B2581021 : Blo 1056613 2581021 := bbase (se 3 (by rfl) ⟨483941, by rfl⟩ : syracuseStep 2581021 = 967883) (by norm_num)
theorem B2548277 : Blo 1056613 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B1270361 : Blo 1056613 1270361 := bbase (se 2 (by rfl) ⟨476385, by rfl⟩ : syracuseStep 1270361 = 952771) (by norm_num)
theorem B2679389 : Blo 1056613 2679389 := bbase (se 3 (by rfl) ⟨502385, by rfl⟩ : syracuseStep 2679389 = 1004771) (by norm_num)
theorem B2384477 : Blo 1056613 2384477 := bbase (se 3 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 2384477 = 894179) (by norm_num)
theorem B2384549 : Blo 1056613 2384549 := bbase (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) (by norm_num)
theorem B2384621 : Blo 1056613 2384621 := bbase (se 3 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 2384621 = 894233) (by norm_num)
theorem B2417413 : Blo 1056613 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B2679581 : Blo 1056613 2679581 := bbase (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) (by norm_num)
theorem B2384693 : Blo 1056613 2384693 := bbase (se 5 (by rfl) ⟨111782, by rfl⟩ : syracuseStep 2384693 = 223565) (by norm_num)
theorem B1631069 : Blo 1056613 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B2384765 : Blo 1056613 2384765 := bbase (se 3 (by rfl) ⟨447143, by rfl⟩ : syracuseStep 2384765 = 894287) (by norm_num)
theorem B1270669 : Blo 1056613 1270669 := bbase (se 3 (by rfl) ⟨238250, by rfl⟩ : syracuseStep 1270669 = 476501) (by norm_num)
theorem B1696685 : Blo 1056613 1696685 := bbase (se 3 (by rfl) ⟨318128, by rfl⟩ : syracuseStep 1696685 = 636257) (by norm_num)
theorem B2384837 : Blo 1056613 2384837 := bbase (se 4 (by rfl) ⟨223578, by rfl⟩ : syracuseStep 2384837 = 447157) (by norm_num)
theorem B1270765 : Blo 1056613 1270765 := bbase (se 3 (by rfl) ⟨238268, by rfl⟩ : syracuseStep 1270765 = 476537) (by norm_num)
theorem B6022133 : Blo 1056613 6022133 := bbase (se 5 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 6022133 = 564575) (by norm_num)
theorem B2384909 : Blo 1056613 2384909 := bbase (se 3 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 2384909 = 894341) (by norm_num)
theorem B10183765 : Blo 1056613 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B2384981 : Blo 1056613 2384981 := bbase (se 8 (by rfl) ⟨13974, by rfl⟩ : syracuseStep 2384981 = 27949) (by norm_num)
theorem B2679925 : Blo 1056613 2679925 := bbase (se 5 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 2679925 = 251243) (by norm_num)
theorem B1270909 : Blo 1056613 1270909 := bbase (se 3 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 1270909 = 476591) (by norm_num)
theorem B2385053 : Blo 1056613 2385053 := bbase (se 3 (by rfl) ⟨447197, by rfl⟩ : syracuseStep 2385053 = 894395) (by norm_num)
theorem B2680037 : Blo 1056613 2680037 := bbase (se 4 (by rfl) ⟨251253, by rfl⟩ : syracuseStep 2680037 = 502507) (by norm_num)
theorem B2385125 : Blo 1056613 2385125 := bbase (se 4 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 2385125 = 447211) (by norm_num)
theorem B2385197 : Blo 1056613 2385197 := bbase (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) (by norm_num)
theorem B30532949 : Blo 1056613 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B2385269 : Blo 1056613 2385269 := bbase (se 5 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 2385269 = 223619) (by norm_num)
theorem B4023701 : Blo 1056613 4023701 := bbase (se 6 (by rfl) ⟨94305, by rfl⟩ : syracuseStep 4023701 = 188611) (by norm_num)
theorem B2680229 : Blo 1056613 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B5367221 : Blo 1056613 5367221 := bbase (se 5 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 5367221 = 503177) (by norm_num)
theorem B2385341 : Blo 1056613 2385341 := bbase (se 3 (by rfl) ⟨447251, by rfl⟩ : syracuseStep 2385341 = 894503) (by norm_num)
theorem B2385413 : Blo 1056613 2385413 := bbase (se 4 (by rfl) ⟨223632, by rfl⟩ : syracuseStep 2385413 = 447265) (by norm_num)
theorem B2385485 : Blo 1056613 2385485 := bbase (se 3 (by rfl) ⟨447278, by rfl⟩ : syracuseStep 2385485 = 894557) (by norm_num)
theorem B1697365 : Blo 1056613 1697365 := bbase (se 8 (by rfl) ⟨9945, by rfl⟩ : syracuseStep 1697365 = 19891) (by norm_num)
theorem B1697429 : Blo 1056613 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B2385557 : Blo 1056613 2385557 := bbase (se 6 (by rfl) ⟨55911, by rfl⟩ : syracuseStep 2385557 = 111823) (by norm_num)
theorem B1762973 : Blo 1056613 1762973 := bbase (se 3 (by rfl) ⟨330557, by rfl⟩ : syracuseStep 1762973 = 661115) (by norm_num)
theorem B4023989 : Blo 1056613 4023989 := bbase (se 5 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 4023989 = 377249) (by norm_num)
theorem B2385629 : Blo 1056613 2385629 := bbase (se 3 (by rfl) ⟨447305, by rfl⟩ : syracuseStep 2385629 = 894611) (by norm_num)
theorem B2680573 : Blo 1056613 2680573 := bbase (se 3 (by rfl) ⟨502607, by rfl⟩ : syracuseStep 2680573 = 1005215) (by norm_num)
theorem B2385701 : Blo 1056613 2385701 := bbase (se 4 (by rfl) ⟨223659, by rfl⟩ : syracuseStep 2385701 = 447319) (by norm_num)
theorem B2680685 : Blo 1056613 2680685 := bbase (se 3 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 2680685 = 1005257) (by norm_num)
theorem B2385773 : Blo 1056613 2385773 := bbase (se 3 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 2385773 = 894665) (by norm_num)
theorem B6776693 : Blo 1056613 6776693 := bbase (se 5 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 6776693 = 635315) (by norm_num)
theorem B9168821 : Blo 1056613 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B2385845 : Blo 1056613 2385845 := bbase (se 5 (by rfl) ⟨111836, by rfl⟩ : syracuseStep 2385845 = 223673) (by norm_num)
theorem B1337305 : Blo 1056613 1337305 := bbase (se 2 (by rfl) ⟨501489, by rfl⟩ : syracuseStep 1337305 = 1002979) (by norm_num)
theorem B2385917 : Blo 1056613 2385917 := bbase (se 3 (by rfl) ⟨447359, by rfl⟩ : syracuseStep 2385917 = 894719) (by norm_num)
theorem B1206289 : Blo 1056613 1206289 := bbase (se 2 (by rfl) ⟨452358, by rfl⟩ : syracuseStep 1206289 = 904717) (by norm_num)
theorem B2680877 : Blo 1056613 2680877 := bbase (se 3 (by rfl) ⟨502664, by rfl⟩ : syracuseStep 2680877 = 1005329) (by norm_num)
theorem B1337401 : Blo 1056613 1337401 := bbase (se 2 (by rfl) ⟨501525, by rfl⟩ : syracuseStep 1337401 = 1003051) (by norm_num)
theorem B2385989 : Blo 1056613 2385989 := bbase (se 4 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 2385989 = 447373) (by norm_num)
theorem B1271909 : Blo 1056613 1271909 := bbase (se 4 (by rfl) ⟨119241, by rfl⟩ : syracuseStep 1271909 = 238483) (by norm_num)
theorem B2386061 : Blo 1056613 2386061 := bbase (se 3 (by rfl) ⟨447386, by rfl⟩ : syracuseStep 2386061 = 894773) (by norm_num)
theorem B2386133 : Blo 1056613 2386133 := bbase (se 7 (by rfl) ⟨27962, by rfl⟩ : syracuseStep 2386133 = 55925) (by norm_num)
theorem B1337573 : Blo 1056613 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1337629 : Blo 1056613 1337629 := bbase (se 3 (by rfl) ⟨250805, by rfl⟩ : syracuseStep 1337629 = 501611) (by norm_num)
theorem B2386205 : Blo 1056613 2386205 := bbase (se 3 (by rfl) ⟨447413, by rfl⟩ : syracuseStep 2386205 = 894827) (by norm_num)
theorem B2386277 : Blo 1056613 2386277 := bbase (se 4 (by rfl) ⟨223713, by rfl⟩ : syracuseStep 2386277 = 447427) (by norm_num)
theorem B1337725 : Blo 1056613 1337725 := bbase (se 3 (by rfl) ⟨250823, by rfl⟩ : syracuseStep 1337725 = 501647) (by norm_num)
theorem B2681221 : Blo 1056613 2681221 := bbase (se 4 (by rfl) ⟨251364, by rfl⟩ : syracuseStep 2681221 = 502729) (by norm_num)
theorem B2386349 : Blo 1056613 2386349 := bbase (se 3 (by rfl) ⟨447440, by rfl⟩ : syracuseStep 2386349 = 894881) (by norm_num)
theorem B2681333 : Blo 1056613 2681333 := bbase (se 5 (by rfl) ⟨125687, by rfl⟩ : syracuseStep 2681333 = 251375) (by norm_num)
theorem B2714141 : Blo 1056613 2714141 := bbase (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) (by norm_num)
theorem B1337897 : Blo 1056613 1337897 := bbase (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) (by norm_num)
theorem B1337953 : Blo 1056613 1337953 := bbase (se 2 (by rfl) ⟨501732, by rfl⟩ : syracuseStep 1337953 = 1003465) (by norm_num)
theorem B3566213 : Blo 1056613 3566213 := bbase (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) (by norm_num)
theorem B2681525 : Blo 1056613 2681525 := bbase (se 5 (by rfl) ⟨125696, by rfl⟩ : syracuseStep 2681525 = 251393) (by norm_num)
theorem B1338049 : Blo 1056613 1338049 := bbase (se 2 (by rfl) ⟨501768, by rfl⟩ : syracuseStep 1338049 = 1003537) (by norm_num)
theorem B3009221 : Blo 1056613 3009221 := bbase (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) (by norm_num)
theorem B5368517 : Blo 1056613 5368517 := bbase (se 4 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 5368517 = 1006597) (by norm_num)
theorem B1272601 : Blo 1056613 1272601 := bbase (se 2 (by rfl) ⟨477225, by rfl⟩ : syracuseStep 1272601 = 954451) (by norm_num)
theorem B4025173 : Blo 1056613 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B1338221 : Blo 1056613 1338221 := bbase (se 3 (by rfl) ⟨250916, by rfl⟩ : syracuseStep 1338221 = 501833) (by norm_num)
theorem B1338277 : Blo 1056613 1338277 := bbase (se 4 (by rfl) ⟨125463, by rfl⟩ : syracuseStep 1338277 = 250927) (by norm_num)
theorem B1698749 : Blo 1056613 1698749 := bbase (se 3 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 1698749 = 637031) (by norm_num)
theorem B1272817 : Blo 1056613 1272817 := bbase (se 2 (by rfl) ⟨477306, by rfl⟩ : syracuseStep 1272817 = 954613) (by norm_num)
theorem B1338373 : Blo 1056613 1338373 := bbase (se 4 (by rfl) ⟨125472, by rfl⟩ : syracuseStep 1338373 = 250945) (by norm_num)
theorem B2681869 : Blo 1056613 2681869 := bbase (se 3 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 2681869 = 1005701) (by norm_num)
theorem B3566645 : Blo 1056613 3566645 := bbase (se 5 (by rfl) ⟨167186, by rfl⟩ : syracuseStep 3566645 = 334373) (by norm_num)
theorem B2714717 : Blo 1056613 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B2681981 : Blo 1056613 2681981 := bbase (se 3 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 2681981 = 1005743) (by norm_num)
theorem B4025477 : Blo 1056613 4025477 := bbase (se 4 (by rfl) ⟨377388, by rfl⟩ : syracuseStep 4025477 = 754777) (by norm_num)
theorem B2714797 : Blo 1056613 2714797 := bbase (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) (by norm_num)
theorem B1338545 : Blo 1056613 1338545 := bbase (se 2 (by rfl) ⟨501954, by rfl⟩ : syracuseStep 1338545 = 1003909) (by norm_num)
theorem B4517045 : Blo 1056613 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B1338601 : Blo 1056613 1338601 := bbase (se 2 (by rfl) ⟨501975, by rfl⟩ : syracuseStep 1338601 = 1003951) (by norm_num)
theorem B2682173 : Blo 1056613 2682173 := bbase (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) (by norm_num)
theorem B1338697 : Blo 1056613 1338697 := bbase (se 2 (by rfl) ⟨502011, by rfl⟩ : syracuseStep 1338697 = 1004023) (by norm_num)
theorem B3009973 : Blo 1056613 3009973 := bbase (se 5 (by rfl) ⟨141092, by rfl⟩ : syracuseStep 3009973 = 282185) (by norm_num)
theorem B1863109 : Blo 1056613 1863109 := bbase (se 4 (by rfl) ⟨174666, by rfl⟩ : syracuseStep 1863109 = 349333) (by norm_num)
theorem B3567077 : Blo 1056613 3567077 := bbase (se 4 (by rfl) ⟨334413, by rfl⟩ : syracuseStep 3567077 = 668827) (by norm_num)
theorem B4287973 : Blo 1056613 4287973 := bbase (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) (by norm_num)
theorem B1338869 : Blo 1056613 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B1338925 : Blo 1056613 1338925 := bbase (se 3 (by rfl) ⟨251048, by rfl⟩ : syracuseStep 1338925 = 502097) (by norm_num)
theorem B1339021 : Blo 1056613 1339021 := bbase (se 3 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 1339021 = 502133) (by norm_num)
theorem B2682517 : Blo 1056613 2682517 := bbase (se 6 (by rfl) ⟨62871, by rfl⟩ : syracuseStep 2682517 = 125743) (by norm_num)
theorem B2682629 : Blo 1056613 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B2256677 : Blo 1056613 2256677 := bbase (se 4 (by rfl) ⟨211563, by rfl⟩ : syracuseStep 2256677 = 423127) (by norm_num)
theorem B5730101 : Blo 1056613 5730101 := bbase (se 5 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 5730101 = 537197) (by norm_num)
theorem B1339193 : Blo 1056613 1339193 := bbase (se 2 (by rfl) ⟨502197, by rfl⟩ : syracuseStep 1339193 = 1004395) (by norm_num)
theorem B1339249 : Blo 1056613 1339249 := bbase (se 2 (by rfl) ⟨502218, by rfl⟩ : syracuseStep 1339249 = 1004437) (by norm_num)
theorem B3567509 : Blo 1056613 3567509 := bbase (se 6 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 3567509 = 167227) (by norm_num)
theorem B2256797 : Blo 1056613 2256797 := bbase (se 3 (by rfl) ⟨423149, by rfl⟩ : syracuseStep 2256797 = 846299) (by norm_num)
theorem B2682821 : Blo 1056613 2682821 := bbase (se 4 (by rfl) ⟨251514, by rfl⟩ : syracuseStep 2682821 = 503029) (by norm_num)
theorem B1339345 : Blo 1056613 1339345 := bbase (se 2 (by rfl) ⟨502254, by rfl⟩ : syracuseStep 1339345 = 1004509) (by norm_num)
theorem B1208369 : Blo 1056613 1208369 := bbase (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) (by norm_num)
theorem B2715709 : Blo 1056613 2715709 := bbase (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) (by norm_num)
theorem B1339517 : Blo 1056613 1339517 := bbase (se 3 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 1339517 = 502319) (by norm_num)
theorem B1339573 : Blo 1056613 1339573 := bbase (se 5 (by rfl) ⟨62792, by rfl⟩ : syracuseStep 1339573 = 125585) (by norm_num)
theorem B9662645 : Blo 1056613 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B1339669 : Blo 1056613 1339669 := bbase (se 6 (by rfl) ⟨31398, by rfl⟩ : syracuseStep 1339669 = 62797) (by norm_num)
theorem B2683165 : Blo 1056613 2683165 := bbase (se 3 (by rfl) ⟨503093, by rfl⟩ : syracuseStep 2683165 = 1006187) (by norm_num)
theorem B3567941 : Blo 1056613 3567941 := bbase (se 4 (by rfl) ⟨334494, by rfl⟩ : syracuseStep 3567941 = 668989) (by norm_num)
theorem B2683277 : Blo 1056613 2683277 := bbase (se 3 (by rfl) ⟨503114, by rfl⟩ : syracuseStep 2683277 = 1006229) (by norm_num)
theorem B1339841 : Blo 1056613 1339841 := bbase (se 2 (by rfl) ⟨502440, by rfl⟩ : syracuseStep 1339841 = 1004881) (by norm_num)
theorem B1339897 : Blo 1056613 1339897 := bbase (se 2 (by rfl) ⟨502461, by rfl⟩ : syracuseStep 1339897 = 1004923) (by norm_num)
theorem B2257429 : Blo 1056613 2257429 := bbase (se 6 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 2257429 = 105817) (by norm_num)
theorem B2683469 : Blo 1056613 2683469 := bbase (se 3 (by rfl) ⟨503150, by rfl⟩ : syracuseStep 2683469 = 1006301) (by norm_num)
theorem B1339993 : Blo 1056613 1339993 := bbase (se 2 (by rfl) ⟨502497, by rfl⟩ : syracuseStep 1339993 = 1004995) (by norm_num)
theorem B1208953 : Blo 1056613 1208953 := bbase (se 2 (by rfl) ⟨453357, by rfl⟩ : syracuseStep 1208953 = 906715) (by norm_num)
theorem B2618029 : Blo 1056613 2618029 := bbase (se 3 (by rfl) ⟨490880, by rfl⟩ : syracuseStep 2618029 = 981761) (by norm_num)
theorem B3568373 : Blo 1056613 3568373 := bbase (se 5 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 3568373 = 334535) (by norm_num)
theorem B1340165 : Blo 1056613 1340165 := bbase (se 4 (by rfl) ⟨125640, by rfl⟩ : syracuseStep 1340165 = 251281) (by norm_num)
theorem B1340221 : Blo 1056613 1340221 := bbase (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) (by norm_num)
theorem B1340317 : Blo 1056613 1340317 := bbase (se 3 (by rfl) ⟨251309, by rfl⟩ : syracuseStep 1340317 = 502619) (by norm_num)
theorem B4518821 : Blo 1056613 4518821 := bbase (se 4 (by rfl) ⟨423639, by rfl⟩ : syracuseStep 4518821 = 847279) (by norm_num)
theorem B2683813 : Blo 1056613 2683813 := bbase (se 4 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 2683813 = 503215) (by norm_num)
theorem B4584421 : Blo 1056613 4584421 := bbase (se 4 (by rfl) ⟨429789, by rfl⟩ : syracuseStep 4584421 = 859579) (by norm_num)
theorem B2683925 : Blo 1056613 2683925 := bbase (se 6 (by rfl) ⟨62904, by rfl⟩ : syracuseStep 2683925 = 125809) (by norm_num)
theorem B1340489 : Blo 1056613 1340489 := bbase (se 2 (by rfl) ⟨502683, by rfl⟩ : syracuseStep 1340489 = 1005367) (by norm_num)
theorem B1340545 : Blo 1056613 1340545 := bbase (se 2 (by rfl) ⟨502704, by rfl⟩ : syracuseStep 1340545 = 1005409) (by norm_num)
theorem B4519061 : Blo 1056613 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B3568805 : Blo 1056613 3568805 := bbase (se 4 (by rfl) ⟨334575, by rfl⟩ : syracuseStep 3568805 = 669151) (by norm_num)
theorem B2684117 : Blo 1056613 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B1340641 : Blo 1056613 1340641 := bbase (se 2 (by rfl) ⟨502740, by rfl⟩ : syracuseStep 1340641 = 1005481) (by norm_num)
theorem B2258317 : Blo 1056613 2258317 := bbase (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) (by norm_num)
theorem B1340813 : Blo 1056613 1340813 := bbase (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) (by norm_num)
theorem B1340869 : Blo 1056613 1340869 := bbase (se 4 (by rfl) ⟨125706, by rfl⟩ : syracuseStep 1340869 = 251413) (by norm_num)
theorem B2258437 : Blo 1056613 2258437 := bbase (se 4 (by rfl) ⟨211728, by rfl⟩ : syracuseStep 2258437 = 423457) (by norm_num)
theorem B1340965 : Blo 1056613 1340965 := bbase (se 4 (by rfl) ⟨125715, by rfl⟩ : syracuseStep 1340965 = 251431) (by norm_num)
theorem B2684461 : Blo 1056613 2684461 := bbase (se 3 (by rfl) ⟨503336, by rfl⟩ : syracuseStep 2684461 = 1006673) (by norm_num)
theorem B3569237 : Blo 1056613 3569237 := bbase (se 8 (by rfl) ⟨20913, by rfl⟩ : syracuseStep 3569237 = 41827) (by norm_num)
theorem B2684573 : Blo 1056613 2684573 := bbase (se 3 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 2684573 = 1006715) (by norm_num)
theorem B5732021 : Blo 1056613 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B1341137 : Blo 1056613 1341137 := bbase (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) (by norm_num)
theorem B2258693 : Blo 1056613 2258693 := bbase (se 4 (by rfl) ⟨211752, by rfl⟩ : syracuseStep 2258693 = 423505) (by norm_num)
theorem B1341193 : Blo 1056613 1341193 := bbase (se 2 (by rfl) ⟨502947, by rfl⟩ : syracuseStep 1341193 = 1005895) (by norm_num)
theorem B1341289 : Blo 1056613 1341289 := bbase (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) (by norm_num)
theorem B3569669 : Blo 1056613 3569669 := bbase (se 4 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 3569669 = 669313) (by norm_num)
theorem B1341461 : Blo 1056613 1341461 := bbase (se 6 (by rfl) ⟨31440, by rfl⟩ : syracuseStep 1341461 = 62881) (by norm_num)
theorem B1505317 : Blo 1056613 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B1341517 : Blo 1056613 1341517 := bbase (se 3 (by rfl) ⟨251534, by rfl⟩ : syracuseStep 1341517 = 503069) (by norm_num)
theorem B1341613 : Blo 1056613 1341613 := bbase (se 3 (by rfl) ⟨251552, by rfl⟩ : syracuseStep 1341613 = 503105) (by norm_num)
theorem B3012821 : Blo 1056613 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B1341785 : Blo 1056613 1341785 := bbase (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) (by norm_num)
theorem B1341841 : Blo 1056613 1341841 := bbase (se 2 (by rfl) ⟨503190, by rfl⟩ : syracuseStep 1341841 = 1006381) (by norm_num)
theorem B2685349 : Blo 1056613 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B3570101 : Blo 1056613 3570101 := bbase (se 5 (by rfl) ⟨167348, by rfl⟩ : syracuseStep 3570101 = 334697) (by norm_num)
theorem B1341937 : Blo 1056613 1341937 := bbase (se 2 (by rfl) ⟨503226, by rfl⟩ : syracuseStep 1341937 = 1006453) (by norm_num)
theorem B1505909 : Blo 1056613 1505909 := bbase (se 5 (by rfl) ⟨70589, by rfl⟩ : syracuseStep 1505909 = 141179) (by norm_num)
theorem B2259581 : Blo 1056613 2259581 := bbase (se 3 (by rfl) ⟨423671, by rfl⟩ : syracuseStep 2259581 = 847343) (by norm_num)
theorem B1342109 : Blo 1056613 1342109 := bbase (se 3 (by rfl) ⟨251645, by rfl⟩ : syracuseStep 1342109 = 503291) (by norm_num)
theorem B1505989 : Blo 1056613 1505989 := bbase (se 4 (by rfl) ⟨141186, by rfl⟩ : syracuseStep 1505989 = 282373) (by norm_num)
theorem B8583893 : Blo 1056613 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B1342165 : Blo 1056613 1342165 := bbase (se 7 (by rfl) ⟨15728, by rfl⟩ : syracuseStep 1342165 = 31457) (by norm_num)
theorem B1342261 : Blo 1056613 1342261 := bbase (se 5 (by rfl) ⟨62918, by rfl⟩ : syracuseStep 1342261 = 125837) (by norm_num)
theorem B1506109 : Blo 1056613 1506109 := bbase (se 3 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 1506109 = 564791) (by norm_num)
theorem B3570533 : Blo 1056613 3570533 := bbase (se 4 (by rfl) ⟨334737, by rfl⟩ : syracuseStep 3570533 = 669475) (by norm_num)
theorem B2259821 : Blo 1056613 2259821 := bbase (se 3 (by rfl) ⟨423716, by rfl⟩ : syracuseStep 2259821 = 847433) (by norm_num)
theorem B2718605 : Blo 1056613 2718605 := bbase (se 3 (by rfl) ⟨509738, by rfl⟩ : syracuseStep 2718605 = 1019477) (by norm_num)
theorem B2063261 : Blo 1056613 2063261 := bbase (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) (by norm_num)
theorem B1506205 : Blo 1056613 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B1932317 : Blo 1056613 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B2718749 : Blo 1056613 2718749 := bbase (se 3 (by rfl) ⟨509765, by rfl⟩ : syracuseStep 2718749 = 1019531) (by norm_num)
theorem B3570965 : Blo 1056613 3570965 := bbase (se 6 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 3570965 = 167389) (by norm_num)
theorem B2260325 : Blo 1056613 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B2260333 : Blo 1056613 2260333 := bbase (se 3 (by rfl) ⟨423812, by rfl⟩ : syracuseStep 2260333 = 847625) (by norm_num)
theorem B3014005 : Blo 1056613 3014005 := bbase (se 5 (by rfl) ⟨141281, by rfl⟩ : syracuseStep 3014005 = 282563) (by norm_num)
theorem B4521349 : Blo 1056613 4521349 := bbase (se 4 (by rfl) ⟨423876, by rfl⟩ : syracuseStep 4521349 = 847753) (by norm_num)
theorem B1506701 : Blo 1056613 1506701 := bbase (se 3 (by rfl) ⟨282506, by rfl⟩ : syracuseStep 1506701 = 565013) (by norm_num)
theorem B11435413 : Blo 1056613 11435413 := bbase (se 6 (by rfl) ⟨268017, by rfl⟩ : syracuseStep 11435413 = 536035) (by norm_num)
theorem B3014165 : Blo 1056613 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B3571397 : Blo 1056613 3571397 := bbase (se 4 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 3571397 = 669637) (by norm_num)
theorem B3014405 : Blo 1056613 3014405 := bbase (se 4 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 3014405 = 565201) (by norm_num)
theorem B1507253 : Blo 1056613 1507253 := bbase (se 5 (by rfl) ⟨70652, by rfl⟩ : syracuseStep 1507253 = 141305) (by norm_num)
theorem B3014597 : Blo 1056613 3014597 := bbase (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) (by norm_num)
theorem B10878965 : Blo 1056613 10878965 := bbase (se 5 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 10878965 = 1019903) (by norm_num)
theorem B2261009 : Blo 1056613 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B20611381 : Blo 1056613 20611381 := bstep (se 5 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 20611381 = 1932317) B1932317
theorem B3572045 : Blo 1056613 3572045 := bstep (se 3 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 3572045 = 1339517) B1339517
theorem B7635313 : Blo 1056613 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B3572099 : Blo 1056613 3572099 := bstep (se 1 (by rfl) ⟨2679074, by rfl⟩ : syracuseStep 3572099 = 5358149) B5358149
theorem B3015053 : Blo 1056613 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B1507891 : Blo 1056613 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B3015235 : Blo 1056613 3015235 := bstep (se 1 (by rfl) ⟨2261426, by rfl⟩ : syracuseStep 3015235 = 4522853) B4522853
theorem B6029923 : Blo 1056613 6029923 := bstep (se 1 (by rfl) ⟨4522442, by rfl⟩ : syracuseStep 6029923 = 9044885) B9044885
theorem B3015281 : Blo 1056613 3015281 := bstep (se 2 (by rfl) ⟨1130730, by rfl⟩ : syracuseStep 3015281 = 2261461) B2261461
theorem B3572369 : Blo 1056613 3572369 := bstep (se 2 (by rfl) ⟨1339638, by rfl⟩ : syracuseStep 3572369 = 2679277) B2679277
theorem B3441361 : Blo 1056613 3441361 := bstep (se 2 (by rfl) ⟨1290510, by rfl⟩ : syracuseStep 3441361 = 2581021) B2581021
theorem B5079793 : Blo 1056613 5079793 := bstep (se 2 (by rfl) ⟨1904922, by rfl⟩ : syracuseStep 5079793 = 3809845) B3809845
theorem B4293731 : Blo 1056613 4293731 := bstep (se 1 (by rfl) ⟨3220298, by rfl⟩ : syracuseStep 4293731 = 6440597) B6440597
theorem B3867761 : Blo 1056613 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B6030449 : Blo 1056613 6030449 := bstep (se 2 (by rfl) ⟨2261418, by rfl⟩ : syracuseStep 6030449 = 4522837) B4522837
theorem B2065571 : Blo 1056613 2065571 := bstep (se 1 (by rfl) ⟨1549178, by rfl⟩ : syracuseStep 2065571 = 3098357) B3098357
theorem B3572909 : Blo 1056613 3572909 := bstep (se 3 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 3572909 = 1339841) B1339841
theorem B3572963 : Blo 1056613 3572963 := bstep (se 1 (by rfl) ⟨2679722, by rfl⟩ : syracuseStep 3572963 = 5359445) B5359445
theorem B3573233 : Blo 1056613 3573233 := bstep (se 2 (by rfl) ⟨1339962, by rfl⟩ : syracuseStep 3573233 = 2679925) B2679925
theorem B1509025 : Blo 1056613 1509025 := bstep (se 2 (by rfl) ⟨565884, by rfl⟩ : syracuseStep 1509025 = 1131769) B1131769
theorem B2262691 : Blo 1056613 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B1509121 : Blo 1056613 1509121 := bstep (se 2 (by rfl) ⟨565920, by rfl⟩ : syracuseStep 1509121 = 1131841) B1131841
theorem B2033635 : Blo 1056613 2033635 := bstep (se 1 (by rfl) ⟨1525226, by rfl⟩ : syracuseStep 2033635 = 3050453) B3050453
theorem B3573773 : Blo 1056613 3573773 := bstep (se 3 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 3573773 = 1340165) B1340165
theorem B3016739 : Blo 1056613 3016739 := bstep (se 1 (by rfl) ⟨2262554, by rfl⟩ : syracuseStep 3016739 = 4525109) B4525109
theorem B3573827 : Blo 1056613 3573827 := bstep (se 1 (by rfl) ⟨2680370, by rfl⟩ : syracuseStep 3573827 = 5360741) B5360741
theorem B2263153 : Blo 1056613 2263153 := bstep (se 2 (by rfl) ⟨848682, by rfl⟩ : syracuseStep 2263153 = 1697365) B1697365
theorem B1509617 : Blo 1056613 1509617 := bstep (se 2 (by rfl) ⟨566106, by rfl⟩ : syracuseStep 1509617 = 1132213) B1132213
theorem B3574097 : Blo 1056613 3574097 := bstep (se 2 (by rfl) ⟨1340286, by rfl⟩ : syracuseStep 3574097 = 2680573) B2680573
theorem B4524493 : Blo 1056613 4524493 := bstep (se 3 (by rfl) ⟨848342, by rfl⟩ : syracuseStep 4524493 = 1696685) B1696685
theorem B6031907 : Blo 1056613 6031907 := bstep (se 1 (by rfl) ⟨4523930, by rfl⟩ : syracuseStep 6031907 = 9047861) B9047861
theorem B1608385 : Blo 1056613 1608385 := bstep (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) B1206289
theorem B4524835 : Blo 1056613 4524835 := bstep (se 1 (by rfl) ⟨3393626, by rfl⟩ : syracuseStep 4524835 = 6787253) B6787253
theorem B4295501 : Blo 1056613 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B3574637 : Blo 1056613 3574637 := bstep (se 3 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 3574637 = 1340489) B1340489
theorem B3574691 : Blo 1056613 3574691 := bstep (se 1 (by rfl) ⟨2681018, by rfl⟩ : syracuseStep 3574691 = 5362037) B5362037
theorem B6786125 : Blo 1056613 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B2264195 : Blo 1056613 2264195 := bstep (se 1 (by rfl) ⟨1698146, by rfl⟩ : syracuseStep 2264195 = 3396293) B3396293
theorem B7244963 : Blo 1056613 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B3574961 : Blo 1056613 3574961 := bstep (se 2 (by rfl) ⟨1340610, by rfl⟩ : syracuseStep 3574961 = 2681221) B2681221
theorem B3017969 : Blo 1056613 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B7638371 : Blo 1056613 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B2264707 : Blo 1056613 2264707 := bstep (se 1 (by rfl) ⟨1698530, by rfl⟩ : syracuseStep 2264707 = 3397061) B3397061
theorem B3575501 : Blo 1056613 3575501 := bstep (se 3 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 3575501 = 1340813) B1340813
theorem B3575555 : Blo 1056613 3575555 := bstep (se 1 (by rfl) ⟨2681666, by rfl⟩ : syracuseStep 3575555 = 5363333) B5363333
theorem B1609699 : Blo 1056613 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B3575825 : Blo 1056613 3575825 := bstep (se 2 (by rfl) ⟨1340934, by rfl⟩ : syracuseStep 3575825 = 2681869) B2681869
theorem B6033797 : Blo 1056613 6033797 := bstep (se 4 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 6033797 = 1131337) B1131337
theorem B3576365 : Blo 1056613 3576365 := bstep (se 3 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 3576365 = 1341137) B1341137
theorem B3576419 : Blo 1056613 3576419 := bstep (se 1 (by rfl) ⟨2682314, by rfl⟩ : syracuseStep 3576419 = 5364629) B5364629
theorem B4297315 : Blo 1056613 4297315 := bstep (se 1 (by rfl) ⟨3222986, by rfl⟩ : syracuseStep 4297315 = 6445973) B6445973
theorem B3019427 : Blo 1056613 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B6427313 : Blo 1056613 6427313 := bstep (se 2 (by rfl) ⟨2410242, by rfl⟩ : syracuseStep 6427313 = 4820485) B4820485
theorem B2757361 : Blo 1056613 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B8033093 : Blo 1056613 8033093 := bstep (se 4 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 8033093 = 1506205) B1506205
theorem B3576689 : Blo 1056613 3576689 := bstep (se 2 (by rfl) ⟨1341258, by rfl⟩ : syracuseStep 3576689 = 2682517) B2682517
theorem B48829553 : Blo 1056613 48829553 := bstep (se 2 (by rfl) ⟨18311082, by rfl⟩ : syracuseStep 48829553 = 36622165) B36622165
theorem B24450245 : Blo 1056613 24450245 := bstep (se 4 (by rfl) ⟨2292210, by rfl⟩ : syracuseStep 24450245 = 4584421) B4584421
theorem B5084365 : Blo 1056613 5084365 := bstep (se 3 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 5084365 = 1906637) B1906637
theorem B1807601 : Blo 1056613 1807601 := bstep (se 2 (by rfl) ⟨677850, by rfl⟩ : syracuseStep 1807601 = 1355701) B1355701
theorem B6788357 : Blo 1056613 6788357 := bstep (se 4 (by rfl) ⟨636408, by rfl⟩ : syracuseStep 6788357 = 1272817) B1272817
theorem B2856323 : Blo 1056613 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B3577229 : Blo 1056613 3577229 := bstep (se 3 (by rfl) ⟨670730, by rfl⟩ : syracuseStep 3577229 = 1341461) B1341461
theorem B3577283 : Blo 1056613 3577283 := bstep (se 1 (by rfl) ⟨2682962, by rfl⟩ : syracuseStep 3577283 = 5365925) B5365925
theorem B3020237 : Blo 1056613 3020237 := bstep (se 3 (by rfl) ⟨566294, by rfl⟩ : syracuseStep 3020237 = 1132589) B1132589
theorem B3577553 : Blo 1056613 3577553 := bstep (se 2 (by rfl) ⟨1341582, by rfl⟩ : syracuseStep 3577553 = 2683165) B2683165
theorem B1087379 : Blo 1056613 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B1906595 : Blo 1056613 1906595 := bstep (se 1 (by rfl) ⟨1429946, by rfl⟩ : syracuseStep 1906595 = 2859893) B2859893
theorem B1611937 : Blo 1056613 1611937 := bstep (se 2 (by rfl) ⟨604476, by rfl⟩ : syracuseStep 1611937 = 1208953) B1208953
theorem B12064949 : Blo 1056613 12064949 := bstep (se 5 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 12064949 = 1131089) B1131089
theorem B20355299 : Blo 1056613 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B3578093 : Blo 1056613 3578093 := bstep (se 3 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 3578093 = 1341785) B1341785
theorem B3578147 : Blo 1056613 3578147 := bstep (se 1 (by rfl) ⟨2683610, by rfl⟩ : syracuseStep 3578147 = 5367221) B5367221
theorem B2857265 : Blo 1056613 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B1907057 : Blo 1056613 1907057 := bstep (se 2 (by rfl) ⟨715146, by rfl⟩ : syracuseStep 1907057 = 1430293) B1430293
theorem B2857361 : Blo 1056613 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B3578417 : Blo 1056613 3578417 := bstep (se 2 (by rfl) ⟨1341906, by rfl⟩ : syracuseStep 3578417 = 2683813) B2683813
theorem B4528867 : Blo 1056613 4528867 := bstep (se 1 (by rfl) ⟨3396650, by rfl⟩ : syracuseStep 4528867 = 6793301) B6793301
theorem B2857837 : Blo 1056613 2857837 := bstep (se 3 (by rfl) ⟨535844, by rfl⟩ : syracuseStep 2857837 = 1071689) B1071689
theorem B1809427 : Blo 1056613 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B3578957 : Blo 1056613 3578957 := bstep (se 3 (by rfl) ⟨671054, by rfl⟩ : syracuseStep 3578957 = 1342109) B1342109
theorem B2006147 : Blo 1056613 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B3579011 : Blo 1056613 3579011 := bstep (se 1 (by rfl) ⟨2684258, by rfl⟩ : syracuseStep 3579011 = 5368517) B5368517
theorem B3579281 : Blo 1056613 3579281 := bstep (se 2 (by rfl) ⟨1342230, by rfl⟩ : syracuseStep 3579281 = 2684461) B2684461
theorem B1809811 : Blo 1056613 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B1908209 : Blo 1056613 1908209 := bstep (se 2 (by rfl) ⟨715578, by rfl⟩ : syracuseStep 1908209 = 1431157) B1431157
theorem B2039491 : Blo 1056613 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B9641699 : Blo 1056613 9641699 := bstep (se 1 (by rfl) ⟨7231274, by rfl⟩ : syracuseStep 9641699 = 14462549) B14462549
theorem B2039555 : Blo 1056613 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B3809123 : Blo 1056613 3809123 := bstep (se 1 (by rfl) ⟨2856842, by rfl⟩ : syracuseStep 3809123 = 5713685) B5713685
theorem B1056627 : Blo 1056613 1056627 := bstep (se 1 (by rfl) ⟨792470, by rfl⟩ : syracuseStep 1056627 = 1584941) B1584941
theorem B1056643 : Blo 1056613 1056643 := bstep (se 1 (by rfl) ⟨792482, by rfl⟩ : syracuseStep 1056643 = 1584965) B1584965
theorem B1056659 : Blo 1056613 1056659 := bstep (se 1 (by rfl) ⟨792494, by rfl⟩ : syracuseStep 1056659 = 1584989) B1584989
theorem B1056675 : Blo 1056613 1056675 := bstep (se 1 (by rfl) ⟨792506, by rfl⟩ : syracuseStep 1056675 = 1585013) B1585013
theorem B1449905 : Blo 1056613 1449905 := bstep (se 2 (by rfl) ⟨543714, by rfl⟩ : syracuseStep 1449905 = 1087429) B1087429
theorem B1056691 : Blo 1056613 1056691 := bstep (se 1 (by rfl) ⟨792518, by rfl⟩ : syracuseStep 1056691 = 1585037) B1585037
theorem B4530097 : Blo 1056613 4530097 := bstep (se 2 (by rfl) ⟨1698786, by rfl⟩ : syracuseStep 4530097 = 3397573) B3397573
theorem B1056707 : Blo 1056613 1056707 := bstep (se 1 (by rfl) ⟨792530, by rfl⟩ : syracuseStep 1056707 = 1585061) B1585061
theorem B1056723 : Blo 1056613 1056723 := bstep (se 1 (by rfl) ⟨792542, by rfl⟩ : syracuseStep 1056723 = 1585085) B1585085
theorem B1056739 : Blo 1056613 1056739 := bstep (se 1 (by rfl) ⟨792554, by rfl⟩ : syracuseStep 1056739 = 1585109) B1585109
theorem B1056755 : Blo 1056613 1056755 := bstep (se 1 (by rfl) ⟨792566, by rfl⟩ : syracuseStep 1056755 = 1585133) B1585133
theorem B1056771 : Blo 1056613 1056771 := bstep (se 1 (by rfl) ⟨792578, by rfl⟩ : syracuseStep 1056771 = 1585157) B1585157
theorem B1056787 : Blo 1056613 1056787 := bstep (se 1 (by rfl) ⟨792590, by rfl⟩ : syracuseStep 1056787 = 1585181) B1585181
theorem B1056803 : Blo 1056613 1056803 := bstep (se 1 (by rfl) ⟨792602, by rfl⟩ : syracuseStep 1056803 = 1585205) B1585205
theorem B2007089 : Blo 1056613 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B1056819 : Blo 1056613 1056819 := bstep (se 1 (by rfl) ⟨792614, by rfl⟩ : syracuseStep 1056819 = 1585229) B1585229
theorem B1056835 : Blo 1056613 1056835 := bstep (se 1 (by rfl) ⟨792626, by rfl⟩ : syracuseStep 1056835 = 1585253) B1585253
theorem B1056851 : Blo 1056613 1056851 := bstep (se 1 (by rfl) ⟨792638, by rfl⟩ : syracuseStep 1056851 = 1585277) B1585277
theorem B1056867 : Blo 1056613 1056867 := bstep (se 1 (by rfl) ⟨792650, by rfl⟩ : syracuseStep 1056867 = 1585301) B1585301
theorem B1056883 : Blo 1056613 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B1056899 : Blo 1056613 1056899 := bstep (se 1 (by rfl) ⟨792674, by rfl⟩ : syracuseStep 1056899 = 1585349) B1585349
theorem B1056915 : Blo 1056613 1056915 := bstep (se 1 (by rfl) ⟨792686, by rfl⟩ : syracuseStep 1056915 = 1585373) B1585373
theorem B1056931 : Blo 1056613 1056931 := bstep (se 1 (by rfl) ⟨792698, by rfl⟩ : syracuseStep 1056931 = 1585397) B1585397
theorem B1056947 : Blo 1056613 1056947 := bstep (se 1 (by rfl) ⟨792710, by rfl⟩ : syracuseStep 1056947 = 1585421) B1585421
theorem B1056963 : Blo 1056613 1056963 := bstep (se 1 (by rfl) ⟨792722, by rfl⟩ : syracuseStep 1056963 = 1585445) B1585445
theorem B1056979 : Blo 1056613 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1056995 : Blo 1056613 1056995 := bstep (se 1 (by rfl) ⟨792746, by rfl⟩ : syracuseStep 1056995 = 1585493) B1585493
theorem B1057011 : Blo 1056613 1057011 := bstep (se 1 (by rfl) ⟨792758, by rfl⟩ : syracuseStep 1057011 = 1585517) B1585517
theorem B1057027 : Blo 1056613 1057027 := bstep (se 1 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 1057027 = 1585541) B1585541
theorem B1057043 : Blo 1056613 1057043 := bstep (se 1 (by rfl) ⟨792782, by rfl⟩ : syracuseStep 1057043 = 1585565) B1585565
theorem B1057059 : Blo 1056613 1057059 := bstep (se 1 (by rfl) ⟨792794, by rfl⟩ : syracuseStep 1057059 = 1585589) B1585589
theorem B1057075 : Blo 1056613 1057075 := bstep (se 1 (by rfl) ⟨792806, by rfl⟩ : syracuseStep 1057075 = 1585613) B1585613
theorem B1057091 : Blo 1056613 1057091 := bstep (se 1 (by rfl) ⟨792818, by rfl⟩ : syracuseStep 1057091 = 1585637) B1585637
theorem B1057107 : Blo 1056613 1057107 := bstep (se 1 (by rfl) ⟨792830, by rfl⟩ : syracuseStep 1057107 = 1585661) B1585661
theorem B1057123 : Blo 1056613 1057123 := bstep (se 1 (by rfl) ⟨792842, by rfl⟩ : syracuseStep 1057123 = 1585685) B1585685
theorem B1057139 : Blo 1056613 1057139 := bstep (se 1 (by rfl) ⟨792854, by rfl⟩ : syracuseStep 1057139 = 1585709) B1585709
theorem B1057155 : Blo 1056613 1057155 := bstep (se 1 (by rfl) ⟨792866, by rfl⟩ : syracuseStep 1057155 = 1585733) B1585733
theorem B1057171 : Blo 1056613 1057171 := bstep (se 1 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 1057171 = 1585757) B1585757
theorem B1057187 : Blo 1056613 1057187 := bstep (se 1 (by rfl) ⟨792890, by rfl⟩ : syracuseStep 1057187 = 1585781) B1585781
theorem B1057203 : Blo 1056613 1057203 := bstep (se 1 (by rfl) ⟨792902, by rfl⟩ : syracuseStep 1057203 = 1585805) B1585805
theorem B1057219 : Blo 1056613 1057219 := bstep (se 1 (by rfl) ⟨792914, by rfl⟩ : syracuseStep 1057219 = 1585829) B1585829
theorem B1057235 : Blo 1056613 1057235 := bstep (se 1 (by rfl) ⟨792926, by rfl⟩ : syracuseStep 1057235 = 1585853) B1585853
theorem B1057251 : Blo 1056613 1057251 := bstep (se 1 (by rfl) ⟨792938, by rfl⟩ : syracuseStep 1057251 = 1585877) B1585877
theorem B1057267 : Blo 1056613 1057267 := bstep (se 1 (by rfl) ⟨792950, by rfl⟩ : syracuseStep 1057267 = 1585901) B1585901
theorem B1057283 : Blo 1056613 1057283 := bstep (se 1 (by rfl) ⟨792962, by rfl⟩ : syracuseStep 1057283 = 1585925) B1585925
theorem B1057299 : Blo 1056613 1057299 := bstep (se 1 (by rfl) ⟨792974, by rfl⟩ : syracuseStep 1057299 = 1585949) B1585949
theorem B1057315 : Blo 1056613 1057315 := bstep (se 1 (by rfl) ⟨792986, by rfl⟩ : syracuseStep 1057315 = 1585973) B1585973
theorem B3580465 : Blo 1056613 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B1057331 : Blo 1056613 1057331 := bstep (se 1 (by rfl) ⟨792998, by rfl⟩ : syracuseStep 1057331 = 1585997) B1585997
theorem B1057347 : Blo 1056613 1057347 := bstep (se 1 (by rfl) ⟨793010, by rfl⟩ : syracuseStep 1057347 = 1586021) B1586021
theorem B1057363 : Blo 1056613 1057363 := bstep (se 1 (by rfl) ⟨793022, by rfl⟩ : syracuseStep 1057363 = 1586045) B1586045
theorem B1057379 : Blo 1056613 1057379 := bstep (se 1 (by rfl) ⟨793034, by rfl⟩ : syracuseStep 1057379 = 1586069) B1586069
theorem B1057395 : Blo 1056613 1057395 := bstep (se 1 (by rfl) ⟨793046, by rfl⟩ : syracuseStep 1057395 = 1586093) B1586093
theorem B1057411 : Blo 1056613 1057411 := bstep (se 1 (by rfl) ⟨793058, by rfl⟩ : syracuseStep 1057411 = 1586117) B1586117
theorem B1057427 : Blo 1056613 1057427 := bstep (se 1 (by rfl) ⟨793070, by rfl⟩ : syracuseStep 1057427 = 1586141) B1586141
theorem B1057443 : Blo 1056613 1057443 := bstep (se 1 (by rfl) ⟨793082, by rfl⟩ : syracuseStep 1057443 = 1586165) B1586165
theorem B1057459 : Blo 1056613 1057459 := bstep (se 1 (by rfl) ⟨793094, by rfl⟩ : syracuseStep 1057459 = 1586189) B1586189
theorem B1057475 : Blo 1056613 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1057491 : Blo 1056613 1057491 := bstep (se 1 (by rfl) ⟨793118, by rfl⟩ : syracuseStep 1057491 = 1586237) B1586237
theorem B1057507 : Blo 1056613 1057507 := bstep (se 1 (by rfl) ⟨793130, by rfl⟩ : syracuseStep 1057507 = 1586261) B1586261
theorem B1057523 : Blo 1056613 1057523 := bstep (se 1 (by rfl) ⟨793142, by rfl⟩ : syracuseStep 1057523 = 1586285) B1586285
theorem B1057539 : Blo 1056613 1057539 := bstep (se 1 (by rfl) ⟨793154, by rfl⟩ : syracuseStep 1057539 = 1586309) B1586309
theorem B1057555 : Blo 1056613 1057555 := bstep (se 1 (by rfl) ⟨793166, by rfl⟩ : syracuseStep 1057555 = 1586333) B1586333
theorem B1057571 : Blo 1056613 1057571 := bstep (se 1 (by rfl) ⟨793178, by rfl⟩ : syracuseStep 1057571 = 1586357) B1586357
theorem B1057587 : Blo 1056613 1057587 := bstep (se 1 (by rfl) ⟨793190, by rfl⟩ : syracuseStep 1057587 = 1586381) B1586381
theorem B1057603 : Blo 1056613 1057603 := bstep (se 1 (by rfl) ⟨793202, by rfl⟩ : syracuseStep 1057603 = 1586405) B1586405
theorem B1057619 : Blo 1056613 1057619 := bstep (se 1 (by rfl) ⟨793214, by rfl⟩ : syracuseStep 1057619 = 1586429) B1586429
theorem B1057635 : Blo 1056613 1057635 := bstep (se 1 (by rfl) ⟨793226, by rfl⟩ : syracuseStep 1057635 = 1586453) B1586453
theorem B3810161 : Blo 1056613 3810161 := bstep (se 2 (by rfl) ⟨1428810, by rfl⟩ : syracuseStep 3810161 = 2857621) B2857621
theorem B1057651 : Blo 1056613 1057651 := bstep (se 1 (by rfl) ⟨793238, by rfl⟩ : syracuseStep 1057651 = 1586477) B1586477
theorem B1057667 : Blo 1056613 1057667 := bstep (se 1 (by rfl) ⟨793250, by rfl⟩ : syracuseStep 1057667 = 1586501) B1586501
theorem B1057683 : Blo 1056613 1057683 := bstep (se 1 (by rfl) ⟨793262, by rfl⟩ : syracuseStep 1057683 = 1586525) B1586525
theorem B1057699 : Blo 1056613 1057699 := bstep (se 1 (by rfl) ⟨793274, by rfl⟩ : syracuseStep 1057699 = 1586549) B1586549
theorem B2007985 : Blo 1056613 2007985 := bstep (se 2 (by rfl) ⟨752994, by rfl⟩ : syracuseStep 2007985 = 1505989) B1505989
theorem B1188787 : Blo 1056613 1188787 := bstep (se 1 (by rfl) ⟨891590, by rfl⟩ : syracuseStep 1188787 = 1783181) B1783181
theorem B1057715 : Blo 1056613 1057715 := bstep (se 1 (by rfl) ⟨793286, by rfl⟩ : syracuseStep 1057715 = 1586573) B1586573
theorem B1057731 : Blo 1056613 1057731 := bstep (se 1 (by rfl) ⟨793298, by rfl⟩ : syracuseStep 1057731 = 1586597) B1586597
theorem B1057747 : Blo 1056613 1057747 := bstep (se 1 (by rfl) ⟨793310, by rfl⟩ : syracuseStep 1057747 = 1586621) B1586621
theorem B9642979 : Blo 1056613 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B1057763 : Blo 1056613 1057763 := bstep (se 1 (by rfl) ⟨793322, by rfl⟩ : syracuseStep 1057763 = 1586645) B1586645
theorem B1057779 : Blo 1056613 1057779 := bstep (se 1 (by rfl) ⟨793334, by rfl⟩ : syracuseStep 1057779 = 1586669) B1586669
theorem B1057795 : Blo 1056613 1057795 := bstep (se 1 (by rfl) ⟨793346, by rfl⟩ : syracuseStep 1057795 = 1586693) B1586693
theorem B1057811 : Blo 1056613 1057811 := bstep (se 1 (by rfl) ⟨793358, by rfl⟩ : syracuseStep 1057811 = 1586717) B1586717
theorem B1057827 : Blo 1056613 1057827 := bstep (se 1 (by rfl) ⟨793370, by rfl⟩ : syracuseStep 1057827 = 1586741) B1586741
theorem B1057843 : Blo 1056613 1057843 := bstep (se 1 (by rfl) ⟨793382, by rfl⟩ : syracuseStep 1057843 = 1586765) B1586765
theorem B1188931 : Blo 1056613 1188931 := bstep (se 1 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 1188931 = 1783397) B1783397
theorem B1057859 : Blo 1056613 1057859 := bstep (se 1 (by rfl) ⟨793394, by rfl⟩ : syracuseStep 1057859 = 1586789) B1586789
theorem B2008145 : Blo 1056613 2008145 := bstep (se 2 (by rfl) ⟨753054, by rfl⟩ : syracuseStep 2008145 = 1506109) B1506109
theorem B1057875 : Blo 1056613 1057875 := bstep (se 1 (by rfl) ⟨793406, by rfl⟩ : syracuseStep 1057875 = 1586813) B1586813
theorem B1057891 : Blo 1056613 1057891 := bstep (se 1 (by rfl) ⟨793418, by rfl⟩ : syracuseStep 1057891 = 1586837) B1586837
theorem B1057907 : Blo 1056613 1057907 := bstep (se 1 (by rfl) ⟨793430, by rfl⟩ : syracuseStep 1057907 = 1586861) B1586861
theorem B1057923 : Blo 1056613 1057923 := bstep (se 1 (by rfl) ⟨793442, by rfl⟩ : syracuseStep 1057923 = 1586885) B1586885
theorem B1057939 : Blo 1056613 1057939 := bstep (se 1 (by rfl) ⟨793454, by rfl⟩ : syracuseStep 1057939 = 1586909) B1586909
theorem B1057955 : Blo 1056613 1057955 := bstep (se 1 (by rfl) ⟨793466, by rfl⟩ : syracuseStep 1057955 = 1586933) B1586933
theorem B1057971 : Blo 1056613 1057971 := bstep (se 1 (by rfl) ⟨793478, by rfl⟩ : syracuseStep 1057971 = 1586957) B1586957
theorem B1057987 : Blo 1056613 1057987 := bstep (se 1 (by rfl) ⟨793490, by rfl⟩ : syracuseStep 1057987 = 1586981) B1586981
theorem B1189075 : Blo 1056613 1189075 := bstep (se 1 (by rfl) ⟨891806, by rfl⟩ : syracuseStep 1189075 = 1783613) B1783613
theorem B1058003 : Blo 1056613 1058003 := bstep (se 1 (by rfl) ⟨793502, by rfl⟩ : syracuseStep 1058003 = 1587005) B1587005
theorem B1058019 : Blo 1056613 1058019 := bstep (se 1 (by rfl) ⟨793514, by rfl⟩ : syracuseStep 1058019 = 1587029) B1587029
theorem B1058035 : Blo 1056613 1058035 := bstep (se 1 (by rfl) ⟨793526, by rfl⟩ : syracuseStep 1058035 = 1587053) B1587053
theorem B1058051 : Blo 1056613 1058051 := bstep (se 1 (by rfl) ⟨793538, by rfl⟩ : syracuseStep 1058051 = 1587077) B1587077
theorem B1058067 : Blo 1056613 1058067 := bstep (se 1 (by rfl) ⟨793550, by rfl⟩ : syracuseStep 1058067 = 1587101) B1587101
theorem B1058083 : Blo 1056613 1058083 := bstep (se 1 (by rfl) ⟨793562, by rfl⟩ : syracuseStep 1058083 = 1587125) B1587125
theorem B1058099 : Blo 1056613 1058099 := bstep (se 1 (by rfl) ⟨793574, by rfl⟩ : syracuseStep 1058099 = 1587149) B1587149
theorem B1058115 : Blo 1056613 1058115 := bstep (se 1 (by rfl) ⟨793586, by rfl⟩ : syracuseStep 1058115 = 1587173) B1587173
theorem B1058131 : Blo 1056613 1058131 := bstep (se 1 (by rfl) ⟨793598, by rfl⟩ : syracuseStep 1058131 = 1587197) B1587197
theorem B1189219 : Blo 1056613 1189219 := bstep (se 1 (by rfl) ⟨891914, by rfl⟩ : syracuseStep 1189219 = 1783829) B1783829
theorem B1058147 : Blo 1056613 1058147 := bstep (se 1 (by rfl) ⟨793610, by rfl⟩ : syracuseStep 1058147 = 1587221) B1587221
theorem B1058163 : Blo 1056613 1058163 := bstep (se 1 (by rfl) ⟨793622, by rfl⟩ : syracuseStep 1058163 = 1587245) B1587245
theorem B1058179 : Blo 1056613 1058179 := bstep (se 1 (by rfl) ⟨793634, by rfl⟩ : syracuseStep 1058179 = 1587269) B1587269
theorem B1058195 : Blo 1056613 1058195 := bstep (se 1 (by rfl) ⟨793646, by rfl⟩ : syracuseStep 1058195 = 1587293) B1587293
theorem B1058211 : Blo 1056613 1058211 := bstep (se 1 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 1058211 = 1587317) B1587317
theorem B1058227 : Blo 1056613 1058227 := bstep (se 1 (by rfl) ⟨793670, by rfl⟩ : syracuseStep 1058227 = 1587341) B1587341
theorem B1058243 : Blo 1056613 1058243 := bstep (se 1 (by rfl) ⟨793682, by rfl⟩ : syracuseStep 1058243 = 1587365) B1587365
theorem B1058259 : Blo 1056613 1058259 := bstep (se 1 (by rfl) ⟨793694, by rfl⟩ : syracuseStep 1058259 = 1587389) B1587389
theorem B2008547 : Blo 1056613 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B1058275 : Blo 1056613 1058275 := bstep (se 1 (by rfl) ⟨793706, by rfl⟩ : syracuseStep 1058275 = 1587413) B1587413
theorem B1910243 : Blo 1056613 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B1189363 : Blo 1056613 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B1058291 : Blo 1056613 1058291 := bstep (se 1 (by rfl) ⟨793718, by rfl⟩ : syracuseStep 1058291 = 1587437) B1587437
theorem B1058307 : Blo 1056613 1058307 := bstep (se 1 (by rfl) ⟨793730, by rfl⟩ : syracuseStep 1058307 = 1587461) B1587461
theorem B1058323 : Blo 1056613 1058323 := bstep (se 1 (by rfl) ⟨793742, by rfl⟩ : syracuseStep 1058323 = 1587485) B1587485
theorem B1058339 : Blo 1056613 1058339 := bstep (se 1 (by rfl) ⟨793754, by rfl⟩ : syracuseStep 1058339 = 1587509) B1587509
theorem B3221041 : Blo 1056613 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1058355 : Blo 1056613 1058355 := bstep (se 1 (by rfl) ⟨793766, by rfl⟩ : syracuseStep 1058355 = 1587533) B1587533
theorem B1058371 : Blo 1056613 1058371 := bstep (se 1 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 1058371 = 1587557) B1587557
theorem B1058387 : Blo 1056613 1058387 := bstep (se 1 (by rfl) ⟨793790, by rfl⟩ : syracuseStep 1058387 = 1587581) B1587581
theorem B1058403 : Blo 1056613 1058403 := bstep (se 1 (by rfl) ⟨793802, by rfl⟩ : syracuseStep 1058403 = 1587605) B1587605
theorem B1058419 : Blo 1056613 1058419 := bstep (se 1 (by rfl) ⟨793814, by rfl⟩ : syracuseStep 1058419 = 1587629) B1587629
theorem B1189507 : Blo 1056613 1189507 := bstep (se 1 (by rfl) ⟨892130, by rfl⟩ : syracuseStep 1189507 = 1784261) B1784261
theorem B1058435 : Blo 1056613 1058435 := bstep (se 1 (by rfl) ⟨793826, by rfl⟩ : syracuseStep 1058435 = 1587653) B1587653
theorem B1058451 : Blo 1056613 1058451 := bstep (se 1 (by rfl) ⟨793838, by rfl⟩ : syracuseStep 1058451 = 1587677) B1587677
theorem B1058467 : Blo 1056613 1058467 := bstep (se 1 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 1058467 = 1587701) B1587701
theorem B1058483 : Blo 1056613 1058483 := bstep (se 1 (by rfl) ⟨793862, by rfl⟩ : syracuseStep 1058483 = 1587725) B1587725
theorem B1058499 : Blo 1056613 1058499 := bstep (se 1 (by rfl) ⟨793874, by rfl⟩ : syracuseStep 1058499 = 1587749) B1587749
theorem B3221201 : Blo 1056613 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B1058515 : Blo 1056613 1058515 := bstep (se 1 (by rfl) ⟨793886, by rfl⟩ : syracuseStep 1058515 = 1587773) B1587773
theorem B1058531 : Blo 1056613 1058531 := bstep (se 1 (by rfl) ⟨793898, by rfl⟩ : syracuseStep 1058531 = 1587797) B1587797
theorem B1058547 : Blo 1056613 1058547 := bstep (se 1 (by rfl) ⟨793910, by rfl⟩ : syracuseStep 1058547 = 1587821) B1587821
theorem B1058563 : Blo 1056613 1058563 := bstep (se 1 (by rfl) ⟨793922, by rfl⟩ : syracuseStep 1058563 = 1587845) B1587845
theorem B1189651 : Blo 1056613 1189651 := bstep (se 1 (by rfl) ⟨892238, by rfl⟩ : syracuseStep 1189651 = 1784477) B1784477
theorem B1058579 : Blo 1056613 1058579 := bstep (se 1 (by rfl) ⟨793934, by rfl⟩ : syracuseStep 1058579 = 1587869) B1587869
theorem B1058595 : Blo 1056613 1058595 := bstep (se 1 (by rfl) ⟨793946, by rfl⟩ : syracuseStep 1058595 = 1587893) B1587893
theorem B1058611 : Blo 1056613 1058611 := bstep (se 1 (by rfl) ⟨793958, by rfl⟩ : syracuseStep 1058611 = 1587917) B1587917
theorem B1058627 : Blo 1056613 1058627 := bstep (se 1 (by rfl) ⟨793970, by rfl⟩ : syracuseStep 1058627 = 1587941) B1587941
theorem B3385169 : Blo 1056613 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B1058643 : Blo 1056613 1058643 := bstep (se 1 (by rfl) ⟨793982, by rfl⟩ : syracuseStep 1058643 = 1587965) B1587965
theorem B1058659 : Blo 1056613 1058659 := bstep (se 1 (by rfl) ⟨793994, by rfl⟩ : syracuseStep 1058659 = 1587989) B1587989
theorem B15247217 : Blo 1056613 15247217 := bstep (se 2 (by rfl) ⟨5717706, by rfl⟩ : syracuseStep 15247217 = 11435413) B11435413
theorem B1058675 : Blo 1056613 1058675 := bstep (se 1 (by rfl) ⟨794006, by rfl⟩ : syracuseStep 1058675 = 1588013) B1588013
theorem B1058691 : Blo 1056613 1058691 := bstep (se 1 (by rfl) ⟨794018, by rfl⟩ : syracuseStep 1058691 = 1588037) B1588037
theorem B1058707 : Blo 1056613 1058707 := bstep (se 1 (by rfl) ⟨794030, by rfl⟩ : syracuseStep 1058707 = 1588061) B1588061
theorem B1189795 : Blo 1056613 1189795 := bstep (se 1 (by rfl) ⟨892346, by rfl⟩ : syracuseStep 1189795 = 1784693) B1784693
theorem B1058723 : Blo 1056613 1058723 := bstep (se 1 (by rfl) ⟨794042, by rfl⟩ : syracuseStep 1058723 = 1588085) B1588085
theorem B5351345 : Blo 1056613 5351345 := bstep (se 2 (by rfl) ⟨2006754, by rfl⟩ : syracuseStep 5351345 = 4013509) B4013509
theorem B1058739 : Blo 1056613 1058739 := bstep (se 1 (by rfl) ⟨794054, by rfl⟩ : syracuseStep 1058739 = 1588109) B1588109
theorem B1812403 : Blo 1056613 1812403 := bstep (se 1 (by rfl) ⟨1359302, by rfl⟩ : syracuseStep 1812403 = 2718605) B2718605
theorem B1058755 : Blo 1056613 1058755 := bstep (se 1 (by rfl) ⟨794066, by rfl⟩ : syracuseStep 1058755 = 1588133) B1588133
theorem B1058771 : Blo 1056613 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B1058787 : Blo 1056613 1058787 := bstep (se 1 (by rfl) ⟨794090, by rfl⟩ : syracuseStep 1058787 = 1588181) B1588181
theorem B1058803 : Blo 1056613 1058803 := bstep (se 1 (by rfl) ⟨794102, by rfl⟩ : syracuseStep 1058803 = 1588205) B1588205
theorem B1058819 : Blo 1056613 1058819 := bstep (se 1 (by rfl) ⟨794114, by rfl⟩ : syracuseStep 1058819 = 1588229) B1588229
theorem B1058835 : Blo 1056613 1058835 := bstep (se 1 (by rfl) ⟨794126, by rfl⟩ : syracuseStep 1058835 = 1588253) B1588253
theorem B1812499 : Blo 1056613 1812499 := bstep (se 1 (by rfl) ⟨1359374, by rfl⟩ : syracuseStep 1812499 = 2718749) B2718749
theorem B1058851 : Blo 1056613 1058851 := bstep (se 1 (by rfl) ⟨794138, by rfl⟩ : syracuseStep 1058851 = 1588277) B1588277
theorem B2172977 : Blo 1056613 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B1189939 : Blo 1056613 1189939 := bstep (se 1 (by rfl) ⟨892454, by rfl⟩ : syracuseStep 1189939 = 1784909) B1784909
theorem B1058867 : Blo 1056613 1058867 := bstep (se 1 (by rfl) ⟨794150, by rfl⟩ : syracuseStep 1058867 = 1588301) B1588301
theorem B1058883 : Blo 1056613 1058883 := bstep (se 1 (by rfl) ⟨794162, by rfl⟩ : syracuseStep 1058883 = 1588325) B1588325
theorem B6039629 : Blo 1056613 6039629 := bstep (se 3 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 6039629 = 2264861) B2264861
theorem B1058899 : Blo 1056613 1058899 := bstep (se 1 (by rfl) ⟨794174, by rfl⟩ : syracuseStep 1058899 = 1588349) B1588349
theorem B1058915 : Blo 1056613 1058915 := bstep (se 1 (by rfl) ⟨794186, by rfl⟩ : syracuseStep 1058915 = 1588373) B1588373
theorem B1058931 : Blo 1056613 1058931 := bstep (se 1 (by rfl) ⟨794198, by rfl⟩ : syracuseStep 1058931 = 1588397) B1588397
theorem B1058947 : Blo 1056613 1058947 := bstep (se 1 (by rfl) ⟨794210, by rfl⟩ : syracuseStep 1058947 = 1588421) B1588421
theorem B1058963 : Blo 1056613 1058963 := bstep (se 1 (by rfl) ⟨794222, by rfl⟩ : syracuseStep 1058963 = 1588445) B1588445
theorem B1058979 : Blo 1056613 1058979 := bstep (se 1 (by rfl) ⟨794234, by rfl⟩ : syracuseStep 1058979 = 1588469) B1588469
theorem B1058995 : Blo 1056613 1058995 := bstep (se 1 (by rfl) ⟨794246, by rfl⟩ : syracuseStep 1058995 = 1588493) B1588493
theorem B1190083 : Blo 1056613 1190083 := bstep (se 1 (by rfl) ⟨892562, by rfl⟩ : syracuseStep 1190083 = 1785125) B1785125
theorem B1059011 : Blo 1056613 1059011 := bstep (se 1 (by rfl) ⟨794258, by rfl⟩ : syracuseStep 1059011 = 1588517) B1588517
theorem B1059027 : Blo 1056613 1059027 := bstep (se 1 (by rfl) ⟨794270, by rfl⟩ : syracuseStep 1059027 = 1588541) B1588541
theorem B1059043 : Blo 1056613 1059043 := bstep (se 1 (by rfl) ⟨794282, by rfl⟩ : syracuseStep 1059043 = 1588565) B1588565
theorem B1059059 : Blo 1056613 1059059 := bstep (se 1 (by rfl) ⟨794294, by rfl⟩ : syracuseStep 1059059 = 1588589) B1588589
theorem B1059075 : Blo 1056613 1059075 := bstep (se 1 (by rfl) ⟨794306, by rfl⟩ : syracuseStep 1059075 = 1588613) B1588613
theorem B1059091 : Blo 1056613 1059091 := bstep (se 1 (by rfl) ⟨794318, by rfl⟩ : syracuseStep 1059091 = 1588637) B1588637
theorem B1059107 : Blo 1056613 1059107 := bstep (se 1 (by rfl) ⟨794330, by rfl⟩ : syracuseStep 1059107 = 1588661) B1588661
theorem B1059123 : Blo 1056613 1059123 := bstep (se 1 (by rfl) ⟨794342, by rfl⟩ : syracuseStep 1059123 = 1588685) B1588685
theorem B1059139 : Blo 1056613 1059139 := bstep (se 1 (by rfl) ⟨794354, by rfl⟩ : syracuseStep 1059139 = 1588709) B1588709
theorem B3811661 : Blo 1056613 3811661 := bstep (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) B1429373
theorem B1190227 : Blo 1056613 1190227 := bstep (se 1 (by rfl) ⟨892670, by rfl⟩ : syracuseStep 1190227 = 1785341) B1785341
theorem B1059155 : Blo 1056613 1059155 := bstep (se 1 (by rfl) ⟨794366, by rfl⟩ : syracuseStep 1059155 = 1588733) B1588733
theorem B2009443 : Blo 1056613 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B1059171 : Blo 1056613 1059171 := bstep (se 1 (by rfl) ⟨794378, by rfl⟩ : syracuseStep 1059171 = 1588757) B1588757
theorem B3385709 : Blo 1056613 3385709 := bstep (se 3 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 3385709 = 1269641) B1269641
theorem B1059187 : Blo 1056613 1059187 := bstep (se 1 (by rfl) ⟨794390, by rfl⟩ : syracuseStep 1059187 = 1588781) B1588781
theorem B1059203 : Blo 1056613 1059203 := bstep (se 1 (by rfl) ⟨794402, by rfl⟩ : syracuseStep 1059203 = 1588805) B1588805
theorem B1059219 : Blo 1056613 1059219 := bstep (se 1 (by rfl) ⟨794414, by rfl⟩ : syracuseStep 1059219 = 1588829) B1588829
theorem B1059235 : Blo 1056613 1059235 := bstep (se 1 (by rfl) ⟨794426, by rfl⟩ : syracuseStep 1059235 = 1588853) B1588853
theorem B1059251 : Blo 1056613 1059251 := bstep (se 1 (by rfl) ⟨794438, by rfl⟩ : syracuseStep 1059251 = 1588877) B1588877
theorem B1059267 : Blo 1056613 1059267 := bstep (se 1 (by rfl) ⟨794450, by rfl⟩ : syracuseStep 1059267 = 1588901) B1588901
theorem B1059283 : Blo 1056613 1059283 := bstep (se 1 (by rfl) ⟨794462, by rfl⟩ : syracuseStep 1059283 = 1588925) B1588925
theorem B1190371 : Blo 1056613 1190371 := bstep (se 1 (by rfl) ⟨892778, by rfl⟩ : syracuseStep 1190371 = 1785557) B1785557
theorem B1059299 : Blo 1056613 1059299 := bstep (se 1 (by rfl) ⟨794474, by rfl⟩ : syracuseStep 1059299 = 1588949) B1588949
theorem B1059315 : Blo 1056613 1059315 := bstep (se 1 (by rfl) ⟨794486, by rfl⟩ : syracuseStep 1059315 = 1588973) B1588973
theorem B2009603 : Blo 1056613 2009603 := bstep (se 1 (by rfl) ⟨1507202, by rfl⟩ : syracuseStep 2009603 = 3014405) B3014405
theorem B1059331 : Blo 1056613 1059331 := bstep (se 1 (by rfl) ⟨794498, by rfl⟩ : syracuseStep 1059331 = 1588997) B1588997
theorem B8038925 : Blo 1056613 8038925 := bstep (se 3 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 8038925 = 3014597) B3014597
theorem B1059347 : Blo 1056613 1059347 := bstep (se 1 (by rfl) ⟨794510, by rfl⟩ : syracuseStep 1059347 = 1589021) B1589021
theorem B1059363 : Blo 1056613 1059363 := bstep (se 1 (by rfl) ⟨794522, by rfl⟩ : syracuseStep 1059363 = 1589045) B1589045
theorem B1059379 : Blo 1056613 1059379 := bstep (se 1 (by rfl) ⟨794534, by rfl⟩ : syracuseStep 1059379 = 1589069) B1589069
theorem B1059395 : Blo 1056613 1059395 := bstep (se 1 (by rfl) ⟨794546, by rfl⟩ : syracuseStep 1059395 = 1589093) B1589093
theorem B1059411 : Blo 1056613 1059411 := bstep (se 1 (by rfl) ⟨794558, by rfl⟩ : syracuseStep 1059411 = 1589117) B1589117
theorem B1059427 : Blo 1056613 1059427 := bstep (se 1 (by rfl) ⟨794570, by rfl⟩ : syracuseStep 1059427 = 1589141) B1589141
theorem B1190515 : Blo 1056613 1190515 := bstep (se 1 (by rfl) ⟨892886, by rfl⟩ : syracuseStep 1190515 = 1785773) B1785773
theorem B1059443 : Blo 1056613 1059443 := bstep (se 1 (by rfl) ⟨794582, by rfl⟩ : syracuseStep 1059443 = 1589165) B1589165
theorem B1059459 : Blo 1056613 1059459 := bstep (se 1 (by rfl) ⟨794594, by rfl⟩ : syracuseStep 1059459 = 1589189) B1589189
theorem B1059475 : Blo 1056613 1059475 := bstep (se 1 (by rfl) ⟨794606, by rfl⟩ : syracuseStep 1059475 = 1589213) B1589213
theorem B7252643 : Blo 1056613 7252643 := bstep (se 1 (by rfl) ⟨5439482, by rfl⟩ : syracuseStep 7252643 = 10878965) B10878965
theorem B1059491 : Blo 1056613 1059491 := bstep (se 1 (by rfl) ⟨794618, by rfl⟩ : syracuseStep 1059491 = 1589237) B1589237
theorem B1059507 : Blo 1056613 1059507 := bstep (se 1 (by rfl) ⟨794630, by rfl⟩ : syracuseStep 1059507 = 1589261) B1589261
theorem B1059523 : Blo 1056613 1059523 := bstep (se 1 (by rfl) ⟨794642, by rfl⟩ : syracuseStep 1059523 = 1589285) B1589285
theorem B1059539 : Blo 1056613 1059539 := bstep (se 1 (by rfl) ⟨794654, by rfl⟩ : syracuseStep 1059539 = 1589309) B1589309
theorem B1059555 : Blo 1056613 1059555 := bstep (se 1 (by rfl) ⟨794666, by rfl⟩ : syracuseStep 1059555 = 1589333) B1589333
theorem B1059571 : Blo 1056613 1059571 := bstep (se 1 (by rfl) ⟨794678, by rfl⟩ : syracuseStep 1059571 = 1589357) B1589357
theorem B1190659 : Blo 1056613 1190659 := bstep (se 1 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 1190659 = 1785989) B1785989
theorem B1059587 : Blo 1056613 1059587 := bstep (se 1 (by rfl) ⟨794690, by rfl⟩ : syracuseStep 1059587 = 1589381) B1589381
theorem B1059603 : Blo 1056613 1059603 := bstep (se 1 (by rfl) ⟨794702, by rfl⟩ : syracuseStep 1059603 = 1589405) B1589405
theorem B1059619 : Blo 1056613 1059619 := bstep (se 1 (by rfl) ⟨794714, by rfl⟩ : syracuseStep 1059619 = 1589429) B1589429
theorem B3222317 : Blo 1056613 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B1059635 : Blo 1056613 1059635 := bstep (se 1 (by rfl) ⟨794726, by rfl⟩ : syracuseStep 1059635 = 1589453) B1589453
theorem B1059651 : Blo 1056613 1059651 := bstep (se 1 (by rfl) ⟨794738, by rfl⟩ : syracuseStep 1059651 = 1589477) B1589477
theorem B1059667 : Blo 1056613 1059667 := bstep (se 1 (by rfl) ⟨794750, by rfl⟩ : syracuseStep 1059667 = 1589501) B1589501
theorem B1059683 : Blo 1056613 1059683 := bstep (se 1 (by rfl) ⟨794762, by rfl⟩ : syracuseStep 1059683 = 1589525) B1589525
theorem B1059699 : Blo 1056613 1059699 := bstep (se 1 (by rfl) ⟨794774, by rfl⟩ : syracuseStep 1059699 = 1589549) B1589549
theorem B1059715 : Blo 1056613 1059715 := bstep (se 1 (by rfl) ⟨794786, by rfl⟩ : syracuseStep 1059715 = 1589573) B1589573
theorem B1190803 : Blo 1056613 1190803 := bstep (se 1 (by rfl) ⟨893102, by rfl⟩ : syracuseStep 1190803 = 1786205) B1786205
theorem B1059731 : Blo 1056613 1059731 := bstep (se 1 (by rfl) ⟨794798, by rfl⟩ : syracuseStep 1059731 = 1589597) B1589597
theorem B1059747 : Blo 1056613 1059747 := bstep (se 1 (by rfl) ⟨794810, by rfl⟩ : syracuseStep 1059747 = 1589621) B1589621
theorem B1059763 : Blo 1056613 1059763 := bstep (se 1 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 1059763 = 1589645) B1589645
theorem B1059779 : Blo 1056613 1059779 := bstep (se 1 (by rfl) ⟨794834, by rfl⟩ : syracuseStep 1059779 = 1589669) B1589669
theorem B1059795 : Blo 1056613 1059795 := bstep (se 1 (by rfl) ⟨794846, by rfl⟩ : syracuseStep 1059795 = 1589693) B1589693
theorem B1059811 : Blo 1056613 1059811 := bstep (se 1 (by rfl) ⟨794858, by rfl⟩ : syracuseStep 1059811 = 1589717) B1589717
theorem B6794225 : Blo 1056613 6794225 := bstep (se 2 (by rfl) ⟨2547834, by rfl⟩ : syracuseStep 6794225 = 5095669) B5095669
theorem B1059827 : Blo 1056613 1059827 := bstep (se 1 (by rfl) ⟨794870, by rfl⟩ : syracuseStep 1059827 = 1589741) B1589741
theorem B1059843 : Blo 1056613 1059843 := bstep (se 1 (by rfl) ⟨794882, by rfl⟩ : syracuseStep 1059843 = 1589765) B1589765
theorem B1059859 : Blo 1056613 1059859 := bstep (se 1 (by rfl) ⟨794894, by rfl⟩ : syracuseStep 1059859 = 1589789) B1589789
theorem B1190947 : Blo 1056613 1190947 := bstep (se 1 (by rfl) ⟨893210, by rfl⟩ : syracuseStep 1190947 = 1786421) B1786421
theorem B1059875 : Blo 1056613 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B1059891 : Blo 1056613 1059891 := bstep (se 1 (by rfl) ⟨794918, by rfl⟩ : syracuseStep 1059891 = 1589837) B1589837
theorem B1059907 : Blo 1056613 1059907 := bstep (se 1 (by rfl) ⟨794930, by rfl⟩ : syracuseStep 1059907 = 1589861) B1589861
theorem B1059923 : Blo 1056613 1059923 := bstep (se 1 (by rfl) ⟨794942, by rfl⟩ : syracuseStep 1059923 = 1589885) B1589885
theorem B1059939 : Blo 1056613 1059939 := bstep (se 1 (by rfl) ⟨794954, by rfl⟩ : syracuseStep 1059939 = 1589909) B1589909
theorem B1059955 : Blo 1056613 1059955 := bstep (se 1 (by rfl) ⟨794966, by rfl⟩ : syracuseStep 1059955 = 1589933) B1589933
theorem B1059971 : Blo 1056613 1059971 := bstep (se 1 (by rfl) ⟨794978, by rfl⟩ : syracuseStep 1059971 = 1589957) B1589957
theorem B1059987 : Blo 1056613 1059987 := bstep (se 1 (by rfl) ⟨794990, by rfl⟩ : syracuseStep 1059987 = 1589981) B1589981
theorem B1060003 : Blo 1056613 1060003 := bstep (se 1 (by rfl) ⟨795002, by rfl⟩ : syracuseStep 1060003 = 1590005) B1590005
theorem B1191091 : Blo 1056613 1191091 := bstep (se 1 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 1191091 = 1786637) B1786637
theorem B1060019 : Blo 1056613 1060019 := bstep (se 1 (by rfl) ⟨795014, by rfl⟩ : syracuseStep 1060019 = 1590029) B1590029
theorem B1060035 : Blo 1056613 1060035 := bstep (se 1 (by rfl) ⟨795026, by rfl⟩ : syracuseStep 1060035 = 1590053) B1590053
theorem B1060051 : Blo 1056613 1060051 := bstep (se 1 (by rfl) ⟨795038, by rfl⟩ : syracuseStep 1060051 = 1590077) B1590077
theorem B1060067 : Blo 1056613 1060067 := bstep (se 1 (by rfl) ⟨795050, by rfl⟩ : syracuseStep 1060067 = 1590101) B1590101
theorem B1060083 : Blo 1056613 1060083 := bstep (se 1 (by rfl) ⟨795062, by rfl⟩ : syracuseStep 1060083 = 1590125) B1590125
theorem B1060099 : Blo 1056613 1060099 := bstep (se 1 (by rfl) ⟨795074, by rfl⟩ : syracuseStep 1060099 = 1590149) B1590149
theorem B1060115 : Blo 1056613 1060115 := bstep (se 1 (by rfl) ⟨795086, by rfl⟩ : syracuseStep 1060115 = 1590173) B1590173
theorem B1060131 : Blo 1056613 1060131 := bstep (se 1 (by rfl) ⟨795098, by rfl⟩ : syracuseStep 1060131 = 1590197) B1590197
theorem B1060147 : Blo 1056613 1060147 := bstep (se 1 (by rfl) ⟨795110, by rfl⟩ : syracuseStep 1060147 = 1590221) B1590221
theorem B1191235 : Blo 1056613 1191235 := bstep (se 1 (by rfl) ⟨893426, by rfl⟩ : syracuseStep 1191235 = 1786853) B1786853
theorem B1060163 : Blo 1056613 1060163 := bstep (se 1 (by rfl) ⟨795122, by rfl⟩ : syracuseStep 1060163 = 1590245) B1590245
theorem B1060179 : Blo 1056613 1060179 := bstep (se 1 (by rfl) ⟨795134, by rfl⟩ : syracuseStep 1060179 = 1590269) B1590269
theorem B5352803 : Blo 1056613 5352803 := bstep (se 1 (by rfl) ⟨4014602, by rfl⟩ : syracuseStep 5352803 = 8029205) B8029205
theorem B1060195 : Blo 1056613 1060195 := bstep (se 1 (by rfl) ⟨795146, by rfl⟩ : syracuseStep 1060195 = 1590293) B1590293
theorem B1060211 : Blo 1056613 1060211 := bstep (se 1 (by rfl) ⟨795158, by rfl⟩ : syracuseStep 1060211 = 1590317) B1590317
theorem B1060227 : Blo 1056613 1060227 := bstep (se 1 (by rfl) ⟨795170, by rfl⟩ : syracuseStep 1060227 = 1590341) B1590341
theorem B1060243 : Blo 1056613 1060243 := bstep (se 1 (by rfl) ⟨795182, by rfl⟩ : syracuseStep 1060243 = 1590365) B1590365
theorem B1060259 : Blo 1056613 1060259 := bstep (se 1 (by rfl) ⟨795194, by rfl⟩ : syracuseStep 1060259 = 1590389) B1590389
theorem B1060275 : Blo 1056613 1060275 := bstep (se 1 (by rfl) ⟨795206, by rfl⟩ : syracuseStep 1060275 = 1590413) B1590413
theorem B1060291 : Blo 1056613 1060291 := bstep (se 1 (by rfl) ⟨795218, by rfl⟩ : syracuseStep 1060291 = 1590437) B1590437
theorem B3812813 : Blo 1056613 3812813 := bstep (se 3 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 3812813 = 1429805) B1429805
theorem B1191379 : Blo 1056613 1191379 := bstep (se 1 (by rfl) ⟨893534, by rfl⟩ : syracuseStep 1191379 = 1787069) B1787069
theorem B1060307 : Blo 1056613 1060307 := bstep (se 1 (by rfl) ⟨795230, by rfl⟩ : syracuseStep 1060307 = 1590461) B1590461
theorem B1060323 : Blo 1056613 1060323 := bstep (se 1 (by rfl) ⟨795242, by rfl⟩ : syracuseStep 1060323 = 1590485) B1590485
theorem B1060339 : Blo 1056613 1060339 := bstep (se 1 (by rfl) ⟨795254, by rfl⟩ : syracuseStep 1060339 = 1590509) B1590509
theorem B1060355 : Blo 1056613 1060355 := bstep (se 1 (by rfl) ⟨795266, by rfl⟩ : syracuseStep 1060355 = 1590533) B1590533
theorem B1060371 : Blo 1056613 1060371 := bstep (se 1 (by rfl) ⟨795278, by rfl⟩ : syracuseStep 1060371 = 1590557) B1590557
theorem B1060387 : Blo 1056613 1060387 := bstep (se 1 (by rfl) ⟨795290, by rfl⟩ : syracuseStep 1060387 = 1590581) B1590581
theorem B2010673 : Blo 1056613 2010673 := bstep (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) B1508005
theorem B1060403 : Blo 1056613 1060403 := bstep (se 1 (by rfl) ⟨795302, by rfl⟩ : syracuseStep 1060403 = 1590605) B1590605
theorem B1060419 : Blo 1056613 1060419 := bstep (se 1 (by rfl) ⟨795314, by rfl⟩ : syracuseStep 1060419 = 1590629) B1590629
theorem B1060435 : Blo 1056613 1060435 := bstep (se 1 (by rfl) ⟨795326, by rfl⟩ : syracuseStep 1060435 = 1590653) B1590653
theorem B1191523 : Blo 1056613 1191523 := bstep (se 1 (by rfl) ⟨893642, by rfl⟩ : syracuseStep 1191523 = 1787285) B1787285
theorem B1060451 : Blo 1056613 1060451 := bstep (se 1 (by rfl) ⟨795338, by rfl⟩ : syracuseStep 1060451 = 1590677) B1590677
theorem B1060467 : Blo 1056613 1060467 := bstep (se 1 (by rfl) ⟨795350, by rfl⟩ : syracuseStep 1060467 = 1590701) B1590701
theorem B1060483 : Blo 1056613 1060483 := bstep (se 1 (by rfl) ⟨795362, by rfl⟩ : syracuseStep 1060483 = 1590725) B1590725
theorem B1060499 : Blo 1056613 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1060515 : Blo 1056613 1060515 := bstep (se 1 (by rfl) ⟨795386, by rfl⟩ : syracuseStep 1060515 = 1590773) B1590773
theorem B3223217 : Blo 1056613 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B1060531 : Blo 1056613 1060531 := bstep (se 1 (by rfl) ⟨795398, by rfl⟩ : syracuseStep 1060531 = 1590797) B1590797
theorem B1814195 : Blo 1056613 1814195 := bstep (se 1 (by rfl) ⟨1360646, by rfl⟩ : syracuseStep 1814195 = 2721293) B2721293
theorem B1060547 : Blo 1056613 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B20623045 : Blo 1056613 20623045 := bstep (se 4 (by rfl) ⟨1933410, by rfl⟩ : syracuseStep 20623045 = 3866821) B3866821
theorem B1060563 : Blo 1056613 1060563 := bstep (se 1 (by rfl) ⟨795422, by rfl⟩ : syracuseStep 1060563 = 1590845) B1590845
theorem B1060579 : Blo 1056613 1060579 := bstep (se 1 (by rfl) ⟨795434, by rfl⟩ : syracuseStep 1060579 = 1590869) B1590869
theorem B1191667 : Blo 1056613 1191667 := bstep (se 1 (by rfl) ⟨893750, by rfl⟩ : syracuseStep 1191667 = 1787501) B1787501
theorem B1060595 : Blo 1056613 1060595 := bstep (se 1 (by rfl) ⟨795446, by rfl⟩ : syracuseStep 1060595 = 1590893) B1590893
theorem B1060611 : Blo 1056613 1060611 := bstep (se 1 (by rfl) ⟨795458, by rfl⟩ : syracuseStep 1060611 = 1590917) B1590917
theorem B1584929 : Blo 1056613 1584929 := bstep (se 2 (by rfl) ⟨594348, by rfl⟩ : syracuseStep 1584929 = 1188697) B1188697
theorem B1584947 : Blo 1056613 1584947 := bstep (se 1 (by rfl) ⟨1188710, by rfl⟩ : syracuseStep 1584947 = 2377421) B2377421
theorem B1584977 : Blo 1056613 1584977 := bstep (se 2 (by rfl) ⟨594366, by rfl⟩ : syracuseStep 1584977 = 1188733) B1188733
theorem B1584995 : Blo 1056613 1584995 := bstep (se 1 (by rfl) ⟨1188746, by rfl⟩ : syracuseStep 1584995 = 2377493) B2377493
theorem B1585025 : Blo 1056613 1585025 := bstep (se 2 (by rfl) ⟨594384, by rfl⟩ : syracuseStep 1585025 = 1188769) B1188769
theorem B1191811 : Blo 1056613 1191811 := bstep (se 1 (by rfl) ⟨893858, by rfl⟩ : syracuseStep 1191811 = 1787717) B1787717
theorem B1585043 : Blo 1056613 1585043 := bstep (se 1 (by rfl) ⟨1188782, by rfl⟩ : syracuseStep 1585043 = 2377565) B2377565
theorem B1585073 : Blo 1056613 1585073 := bstep (se 2 (by rfl) ⟨594402, by rfl⟩ : syracuseStep 1585073 = 1188805) B1188805
theorem B1585091 : Blo 1056613 1585091 := bstep (se 1 (by rfl) ⟨1188818, by rfl⟩ : syracuseStep 1585091 = 2377637) B2377637
theorem B1585121 : Blo 1056613 1585121 := bstep (se 2 (by rfl) ⟨594420, by rfl⟩ : syracuseStep 1585121 = 1188841) B1188841
theorem B1585139 : Blo 1056613 1585139 := bstep (se 1 (by rfl) ⟨1188854, by rfl⟩ : syracuseStep 1585139 = 2377709) B2377709
theorem B1224707 : Blo 1056613 1224707 := bstep (se 1 (by rfl) ⟨918530, by rfl⟩ : syracuseStep 1224707 = 1837061) B1837061
theorem B1585169 : Blo 1056613 1585169 := bstep (se 2 (by rfl) ⟨594438, by rfl⟩ : syracuseStep 1585169 = 1188877) B1188877
theorem B1191955 : Blo 1056613 1191955 := bstep (se 1 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 1191955 = 1787933) B1787933
theorem B1585187 : Blo 1056613 1585187 := bstep (se 1 (by rfl) ⟨1188890, by rfl⟩ : syracuseStep 1585187 = 2377781) B2377781
theorem B1585217 : Blo 1056613 1585217 := bstep (se 2 (by rfl) ⟨594456, by rfl⟩ : syracuseStep 1585217 = 1188913) B1188913
theorem B1585235 : Blo 1056613 1585235 := bstep (se 1 (by rfl) ⟨1188926, by rfl⟩ : syracuseStep 1585235 = 2377853) B2377853
theorem B1585265 : Blo 1056613 1585265 := bstep (se 2 (by rfl) ⟨594474, by rfl⟩ : syracuseStep 1585265 = 1188949) B1188949
theorem B13578353 : Blo 1056613 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B1585283 : Blo 1056613 1585283 := bstep (se 1 (by rfl) ⟨1188962, by rfl⟩ : syracuseStep 1585283 = 2377925) B2377925
theorem B5353613 : Blo 1056613 5353613 := bstep (se 3 (by rfl) ⟨1003802, by rfl⟩ : syracuseStep 5353613 = 2007605) B2007605
theorem B1585313 : Blo 1056613 1585313 := bstep (se 2 (by rfl) ⟨594492, by rfl⟩ : syracuseStep 1585313 = 1188985) B1188985
theorem B1192099 : Blo 1056613 1192099 := bstep (se 1 (by rfl) ⟨894074, by rfl⟩ : syracuseStep 1192099 = 1788149) B1788149
theorem B1585331 : Blo 1056613 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B1585361 : Blo 1056613 1585361 := bstep (se 2 (by rfl) ⟨594510, by rfl⟩ : syracuseStep 1585361 = 1189021) B1189021
theorem B1585379 : Blo 1056613 1585379 := bstep (se 1 (by rfl) ⟨1189034, by rfl⟩ : syracuseStep 1585379 = 2378069) B2378069
theorem B3387629 : Blo 1056613 3387629 := bstep (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) B1270361
theorem B1585409 : Blo 1056613 1585409 := bstep (se 2 (by rfl) ⟨594528, by rfl⟩ : syracuseStep 1585409 = 1189057) B1189057
theorem B1585427 : Blo 1056613 1585427 := bstep (se 1 (by rfl) ⟨1189070, by rfl⟩ : syracuseStep 1585427 = 2378141) B2378141
theorem B1585457 : Blo 1056613 1585457 := bstep (se 2 (by rfl) ⟨594546, by rfl⟩ : syracuseStep 1585457 = 1189093) B1189093
theorem B1192243 : Blo 1056613 1192243 := bstep (se 1 (by rfl) ⟨894182, by rfl⟩ : syracuseStep 1192243 = 1788365) B1788365
theorem B1585475 : Blo 1056613 1585475 := bstep (se 1 (by rfl) ⟨1189106, by rfl⟩ : syracuseStep 1585475 = 2378213) B2378213
theorem B1585505 : Blo 1056613 1585505 := bstep (se 2 (by rfl) ⟨594564, by rfl⟩ : syracuseStep 1585505 = 1189129) B1189129
theorem B1585523 : Blo 1056613 1585523 := bstep (se 1 (by rfl) ⟨1189142, by rfl⟩ : syracuseStep 1585523 = 2378285) B2378285
theorem B1585553 : Blo 1056613 1585553 := bstep (se 2 (by rfl) ⟨594582, by rfl⟩ : syracuseStep 1585553 = 1189165) B1189165
theorem B1585571 : Blo 1056613 1585571 := bstep (se 1 (by rfl) ⟨1189178, by rfl⟩ : syracuseStep 1585571 = 2378357) B2378357
theorem B1585601 : Blo 1056613 1585601 := bstep (se 2 (by rfl) ⟨594600, by rfl⟩ : syracuseStep 1585601 = 1189201) B1189201
theorem B1192387 : Blo 1056613 1192387 := bstep (se 1 (by rfl) ⟨894290, by rfl⟩ : syracuseStep 1192387 = 1788581) B1788581
theorem B1585619 : Blo 1056613 1585619 := bstep (se 1 (by rfl) ⟨1189214, by rfl⟩ : syracuseStep 1585619 = 2378429) B2378429
theorem B1585649 : Blo 1056613 1585649 := bstep (se 2 (by rfl) ⟨594618, by rfl⟩ : syracuseStep 1585649 = 1189237) B1189237
theorem B1585667 : Blo 1056613 1585667 := bstep (se 1 (by rfl) ⟨1189250, by rfl⟩ : syracuseStep 1585667 = 2378501) B2378501
theorem B1585697 : Blo 1056613 1585697 := bstep (se 2 (by rfl) ⟨594636, by rfl⟩ : syracuseStep 1585697 = 1189273) B1189273
theorem B1585715 : Blo 1056613 1585715 := bstep (se 1 (by rfl) ⟨1189286, by rfl⟩ : syracuseStep 1585715 = 2378573) B2378573
theorem B1585745 : Blo 1056613 1585745 := bstep (se 2 (by rfl) ⟨594654, by rfl⟩ : syracuseStep 1585745 = 1189309) B1189309
theorem B2011729 : Blo 1056613 2011729 := bstep (se 2 (by rfl) ⟨754398, by rfl⟩ : syracuseStep 2011729 = 1508797) B1508797
theorem B1192531 : Blo 1056613 1192531 := bstep (se 1 (by rfl) ⟨894398, by rfl⟩ : syracuseStep 1192531 = 1788797) B1788797
theorem B1585763 : Blo 1056613 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B1585793 : Blo 1056613 1585793 := bstep (se 2 (by rfl) ⟨594672, by rfl⟩ : syracuseStep 1585793 = 1189345) B1189345
theorem B1585811 : Blo 1056613 1585811 := bstep (se 1 (by rfl) ⟨1189358, by rfl⟩ : syracuseStep 1585811 = 2378717) B2378717
theorem B1585841 : Blo 1056613 1585841 := bstep (se 2 (by rfl) ⟨594690, by rfl⟩ : syracuseStep 1585841 = 1189381) B1189381
theorem B1585859 : Blo 1056613 1585859 := bstep (se 1 (by rfl) ⟨1189394, by rfl⟩ : syracuseStep 1585859 = 2378789) B2378789
theorem B1585889 : Blo 1056613 1585889 := bstep (se 2 (by rfl) ⟨594708, by rfl⟩ : syracuseStep 1585889 = 1189417) B1189417
theorem B1192675 : Blo 1056613 1192675 := bstep (se 1 (by rfl) ⟨894506, by rfl⟩ : syracuseStep 1192675 = 1789013) B1789013
theorem B1716977 : Blo 1056613 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B1585907 : Blo 1056613 1585907 := bstep (se 1 (by rfl) ⟨1189430, by rfl⟩ : syracuseStep 1585907 = 2378861) B2378861
theorem B1585937 : Blo 1056613 1585937 := bstep (se 2 (by rfl) ⟨594726, by rfl⟩ : syracuseStep 1585937 = 1189453) B1189453
theorem B1585955 : Blo 1056613 1585955 := bstep (se 1 (by rfl) ⟨1189466, by rfl⟩ : syracuseStep 1585955 = 2378933) B2378933
theorem B1585985 : Blo 1056613 1585985 := bstep (se 2 (by rfl) ⟨594744, by rfl⟩ : syracuseStep 1585985 = 1189489) B1189489
theorem B1586003 : Blo 1056613 1586003 := bstep (se 1 (by rfl) ⟨1189502, by rfl⟩ : syracuseStep 1586003 = 2379005) B2379005
theorem B1586033 : Blo 1056613 1586033 := bstep (se 2 (by rfl) ⟨594762, by rfl⟩ : syracuseStep 1586033 = 1189525) B1189525
theorem B1192819 : Blo 1056613 1192819 := bstep (se 1 (by rfl) ⟨894614, by rfl⟩ : syracuseStep 1192819 = 1789229) B1789229
theorem B1586051 : Blo 1056613 1586051 := bstep (se 1 (by rfl) ⟨1189538, by rfl⟩ : syracuseStep 1586051 = 2379077) B2379077
theorem B1586081 : Blo 1056613 1586081 := bstep (se 2 (by rfl) ⟨594780, by rfl⟩ : syracuseStep 1586081 = 1189561) B1189561
theorem B1586099 : Blo 1056613 1586099 := bstep (se 1 (by rfl) ⟨1189574, by rfl⟩ : syracuseStep 1586099 = 2379149) B2379149
theorem B1586129 : Blo 1056613 1586129 := bstep (se 2 (by rfl) ⟨594798, by rfl⟩ : syracuseStep 1586129 = 1189597) B1189597
theorem B1586147 : Blo 1056613 1586147 := bstep (se 1 (by rfl) ⟨1189610, by rfl⟩ : syracuseStep 1586147 = 2379221) B2379221
theorem B2864099 : Blo 1056613 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B2012131 : Blo 1056613 2012131 := bstep (se 1 (by rfl) ⟨1509098, by rfl⟩ : syracuseStep 2012131 = 3018197) B3018197
theorem B1586177 : Blo 1056613 1586177 := bstep (se 2 (by rfl) ⟨594816, by rfl⟩ : syracuseStep 1586177 = 1189633) B1189633
theorem B1192963 : Blo 1056613 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B2012177 : Blo 1056613 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B1586195 : Blo 1056613 1586195 := bstep (se 1 (by rfl) ⟨1189646, by rfl⟩ : syracuseStep 1586195 = 2379293) B2379293
theorem B6435875 : Blo 1056613 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B1586225 : Blo 1056613 1586225 := bstep (se 2 (by rfl) ⟨594834, by rfl⟩ : syracuseStep 1586225 = 1189669) B1189669
theorem B1586243 : Blo 1056613 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B1586273 : Blo 1056613 1586273 := bstep (se 2 (by rfl) ⟨594852, by rfl⟩ : syracuseStep 1586273 = 1189705) B1189705
theorem B1586291 : Blo 1056613 1586291 := bstep (se 1 (by rfl) ⟨1189718, by rfl⟩ : syracuseStep 1586291 = 2379437) B2379437
theorem B2143363 : Blo 1056613 2143363 := bstep (se 1 (by rfl) ⟨1607522, by rfl⟩ : syracuseStep 2143363 = 3215045) B3215045
theorem B1586321 : Blo 1056613 1586321 := bstep (se 2 (by rfl) ⟨594870, by rfl⟩ : syracuseStep 1586321 = 1189741) B1189741
theorem B1193107 : Blo 1056613 1193107 := bstep (se 1 (by rfl) ⟨894830, by rfl⟩ : syracuseStep 1193107 = 1789661) B1789661
theorem B1586339 : Blo 1056613 1586339 := bstep (se 1 (by rfl) ⟨1189754, by rfl⟩ : syracuseStep 1586339 = 2379509) B2379509
theorem B1586369 : Blo 1056613 1586369 := bstep (se 2 (by rfl) ⟨594888, by rfl⟩ : syracuseStep 1586369 = 1189777) B1189777
theorem B17151173 : Blo 1056613 17151173 := bstep (se 4 (by rfl) ⟨1607922, by rfl⟩ : syracuseStep 17151173 = 3215845) B3215845
theorem B1586387 : Blo 1056613 1586387 := bstep (se 1 (by rfl) ⟨1189790, by rfl⟩ : syracuseStep 1586387 = 2379581) B2379581
theorem B1586417 : Blo 1056613 1586417 := bstep (se 2 (by rfl) ⟨594906, by rfl⟩ : syracuseStep 1586417 = 1189813) B1189813
theorem B1586435 : Blo 1056613 1586435 := bstep (se 1 (by rfl) ⟨1189826, by rfl⟩ : syracuseStep 1586435 = 2379653) B2379653
theorem B1783073 : Blo 1056613 1783073 := bstep (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) B1337305
theorem B1586465 : Blo 1056613 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B2012465 : Blo 1056613 2012465 := bstep (se 2 (by rfl) ⟨754674, by rfl⟩ : syracuseStep 2012465 = 1509349) B1509349
theorem B1586483 : Blo 1056613 1586483 := bstep (se 1 (by rfl) ⟨1189862, by rfl⟩ : syracuseStep 1586483 = 2379725) B2379725
theorem B1586513 : Blo 1056613 1586513 := bstep (se 2 (by rfl) ⟨594942, by rfl⟩ : syracuseStep 1586513 = 1189885) B1189885
theorem B1586531 : Blo 1056613 1586531 := bstep (se 1 (by rfl) ⟨1189898, by rfl⟩ : syracuseStep 1586531 = 2379797) B2379797
theorem B8041841 : Blo 1056613 8041841 := bstep (se 2 (by rfl) ⟨3015690, by rfl⟩ : syracuseStep 8041841 = 6031381) B6031381
theorem B1586561 : Blo 1056613 1586561 := bstep (se 2 (by rfl) ⟨594960, by rfl⟩ : syracuseStep 1586561 = 1189921) B1189921
theorem B1586579 : Blo 1056613 1586579 := bstep (se 1 (by rfl) ⟨1189934, by rfl⟩ : syracuseStep 1586579 = 2379869) B2379869
theorem B1783201 : Blo 1056613 1783201 := bstep (se 2 (by rfl) ⟨668700, by rfl⟩ : syracuseStep 1783201 = 1337401) B1337401
theorem B1586609 : Blo 1056613 1586609 := bstep (se 2 (by rfl) ⟨594978, by rfl⟩ : syracuseStep 1586609 = 1189957) B1189957
theorem B3061169 : Blo 1056613 3061169 := bstep (se 2 (by rfl) ⟨1147938, by rfl⟩ : syracuseStep 3061169 = 2295877) B2295877
theorem B1783235 : Blo 1056613 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B1586627 : Blo 1056613 1586627 := bstep (se 1 (by rfl) ⟨1189970, by rfl⟩ : syracuseStep 1586627 = 2379941) B2379941
theorem B1586657 : Blo 1056613 1586657 := bstep (se 2 (by rfl) ⟨594996, by rfl⟩ : syracuseStep 1586657 = 1189993) B1189993
theorem B1586675 : Blo 1056613 1586675 := bstep (se 1 (by rfl) ⟨1190006, by rfl⟩ : syracuseStep 1586675 = 2380013) B2380013
theorem B3225091 : Blo 1056613 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B1586705 : Blo 1056613 1586705 := bstep (se 2 (by rfl) ⟨595014, by rfl⟩ : syracuseStep 1586705 = 1190029) B1190029
theorem B1586723 : Blo 1056613 1586723 := bstep (se 1 (by rfl) ⟨1190042, by rfl⟩ : syracuseStep 1586723 = 2380085) B2380085
theorem B1586753 : Blo 1056613 1586753 := bstep (se 2 (by rfl) ⟨595032, by rfl⟩ : syracuseStep 1586753 = 1190065) B1190065
theorem B1783363 : Blo 1056613 1783363 := bstep (se 1 (by rfl) ⟨1337522, by rfl⟩ : syracuseStep 1783363 = 2675045) B2675045
theorem B1586771 : Blo 1056613 1586771 := bstep (se 1 (by rfl) ⟨1190078, by rfl⟩ : syracuseStep 1586771 = 2380157) B2380157
theorem B3225187 : Blo 1056613 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B1586801 : Blo 1056613 1586801 := bstep (se 2 (by rfl) ⟨595050, by rfl⟩ : syracuseStep 1586801 = 1190101) B1190101
theorem B4830833 : Blo 1056613 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B1586819 : Blo 1056613 1586819 := bstep (se 1 (by rfl) ⟨1190114, by rfl⟩ : syracuseStep 1586819 = 2380229) B2380229
theorem B1586849 : Blo 1056613 1586849 := bstep (se 2 (by rfl) ⟨595068, by rfl⟩ : syracuseStep 1586849 = 1190137) B1190137
theorem B1586867 : Blo 1056613 1586867 := bstep (se 1 (by rfl) ⟨1190150, by rfl⟩ : syracuseStep 1586867 = 2380301) B2380301
theorem B1783505 : Blo 1056613 1783505 := bstep (se 2 (by rfl) ⟨668814, by rfl⟩ : syracuseStep 1783505 = 1337629) B1337629
theorem B1586897 : Blo 1056613 1586897 := bstep (se 2 (by rfl) ⟨595086, by rfl⟩ : syracuseStep 1586897 = 1190173) B1190173
theorem B1586915 : Blo 1056613 1586915 := bstep (se 1 (by rfl) ⟨1190186, by rfl⟩ : syracuseStep 1586915 = 2380373) B2380373
theorem B1586945 : Blo 1056613 1586945 := bstep (se 2 (by rfl) ⟨595104, by rfl⟩ : syracuseStep 1586945 = 1190209) B1190209
theorem B1586963 : Blo 1056613 1586963 := bstep (se 1 (by rfl) ⟨1190222, by rfl⟩ : syracuseStep 1586963 = 2380445) B2380445
theorem B1586993 : Blo 1056613 1586993 := bstep (se 2 (by rfl) ⟨595122, by rfl⟩ : syracuseStep 1586993 = 1190245) B1190245
theorem B1587011 : Blo 1056613 1587011 := bstep (se 1 (by rfl) ⟨1190258, by rfl⟩ : syracuseStep 1587011 = 2380517) B2380517
theorem B1783633 : Blo 1056613 1783633 := bstep (se 2 (by rfl) ⟨668862, by rfl⟩ : syracuseStep 1783633 = 1337725) B1337725
theorem B1357651 : Blo 1056613 1357651 := bstep (se 1 (by rfl) ⟨1018238, by rfl⟩ : syracuseStep 1357651 = 2036477) B2036477
theorem B1587041 : Blo 1056613 1587041 := bstep (se 2 (by rfl) ⟨595140, by rfl⟩ : syracuseStep 1587041 = 1190281) B1190281
theorem B1783667 : Blo 1056613 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B1587059 : Blo 1056613 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B1587089 : Blo 1056613 1587089 := bstep (se 2 (by rfl) ⟨595158, by rfl⟩ : syracuseStep 1587089 = 1190317) B1190317
theorem B1587107 : Blo 1056613 1587107 := bstep (se 1 (by rfl) ⟨1190330, by rfl⟩ : syracuseStep 1587107 = 2380661) B2380661
theorem B1587137 : Blo 1056613 1587137 := bstep (se 2 (by rfl) ⟨595176, by rfl⟩ : syracuseStep 1587137 = 1190353) B1190353
theorem B1587155 : Blo 1056613 1587155 := bstep (se 1 (by rfl) ⟨1190366, by rfl⟩ : syracuseStep 1587155 = 2380733) B2380733
theorem B12040163 : Blo 1056613 12040163 := bstep (se 1 (by rfl) ⟨9030122, by rfl⟩ : syracuseStep 12040163 = 18060245) B18060245
theorem B1587185 : Blo 1056613 1587185 := bstep (se 2 (by rfl) ⟨595194, by rfl⟩ : syracuseStep 1587185 = 1190389) B1190389
theorem B1783795 : Blo 1056613 1783795 := bstep (se 1 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 1783795 = 2675693) B2675693
theorem B1587203 : Blo 1056613 1587203 := bstep (se 1 (by rfl) ⟨1190402, by rfl⟩ : syracuseStep 1587203 = 2380805) B2380805
theorem B2013187 : Blo 1056613 2013187 := bstep (se 1 (by rfl) ⟨1509890, by rfl⟩ : syracuseStep 2013187 = 3019781) B3019781
theorem B1587233 : Blo 1056613 1587233 := bstep (se 2 (by rfl) ⟨595212, by rfl⟩ : syracuseStep 1587233 = 1190425) B1190425
theorem B1587251 : Blo 1056613 1587251 := bstep (se 1 (by rfl) ⟨1190438, by rfl⟩ : syracuseStep 1587251 = 2380877) B2380877
theorem B1587281 : Blo 1056613 1587281 := bstep (se 2 (by rfl) ⟨595230, by rfl⟩ : syracuseStep 1587281 = 1190461) B1190461
theorem B1587299 : Blo 1056613 1587299 := bstep (se 1 (by rfl) ⟨1190474, by rfl⟩ : syracuseStep 1587299 = 2380949) B2380949
theorem B1783937 : Blo 1056613 1783937 := bstep (se 2 (by rfl) ⟨668976, by rfl⟩ : syracuseStep 1783937 = 1337953) B1337953
theorem B1587329 : Blo 1056613 1587329 := bstep (se 2 (by rfl) ⟨595248, by rfl⟩ : syracuseStep 1587329 = 1190497) B1190497
theorem B1587347 : Blo 1056613 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B1587377 : Blo 1056613 1587377 := bstep (se 2 (by rfl) ⟨595266, by rfl⟩ : syracuseStep 1587377 = 1190533) B1190533
theorem B1587395 : Blo 1056613 1587395 := bstep (se 1 (by rfl) ⟨1190546, by rfl⟩ : syracuseStep 1587395 = 2381093) B2381093
theorem B1128659 : Blo 1056613 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B1587425 : Blo 1056613 1587425 := bstep (se 2 (by rfl) ⟨595284, by rfl⟩ : syracuseStep 1587425 = 1190569) B1190569
theorem B1587443 : Blo 1056613 1587443 := bstep (se 1 (by rfl) ⟨1190582, by rfl⟩ : syracuseStep 1587443 = 2381165) B2381165
theorem B1784065 : Blo 1056613 1784065 := bstep (se 2 (by rfl) ⟨669024, by rfl⟩ : syracuseStep 1784065 = 1338049) B1338049
theorem B3619075 : Blo 1056613 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B1587473 : Blo 1056613 1587473 := bstep (se 2 (by rfl) ⟨595302, by rfl⟩ : syracuseStep 1587473 = 1190605) B1190605
theorem B1784099 : Blo 1056613 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B1587491 : Blo 1056613 1587491 := bstep (se 1 (by rfl) ⟨1190618, by rfl⟩ : syracuseStep 1587491 = 2381237) B2381237
theorem B1587521 : Blo 1056613 1587521 := bstep (se 2 (by rfl) ⟨595320, by rfl⟩ : syracuseStep 1587521 = 1190641) B1190641
theorem B1587539 : Blo 1056613 1587539 := bstep (se 1 (by rfl) ⟨1190654, by rfl⟩ : syracuseStep 1587539 = 2381309) B2381309
theorem B3389809 : Blo 1056613 3389809 := bstep (se 2 (by rfl) ⟨1271178, by rfl⟩ : syracuseStep 3389809 = 2542357) B2542357
theorem B1587569 : Blo 1056613 1587569 := bstep (se 2 (by rfl) ⟨595338, by rfl⟩ : syracuseStep 1587569 = 1190677) B1190677
theorem B1587587 : Blo 1056613 1587587 := bstep (se 1 (by rfl) ⟨1190690, by rfl⟩ : syracuseStep 1587587 = 2381381) B2381381
theorem B1587617 : Blo 1056613 1587617 := bstep (se 2 (by rfl) ⟨595356, by rfl⟩ : syracuseStep 1587617 = 1190713) B1190713
theorem B1784227 : Blo 1056613 1784227 := bstep (se 1 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 1784227 = 2676341) B2676341
theorem B1587635 : Blo 1056613 1587635 := bstep (se 1 (by rfl) ⟨1190726, by rfl⟩ : syracuseStep 1587635 = 2381453) B2381453
theorem B1587665 : Blo 1056613 1587665 := bstep (se 2 (by rfl) ⟨595374, by rfl⟩ : syracuseStep 1587665 = 1190749) B1190749
theorem B5716451 : Blo 1056613 5716451 := bstep (se 1 (by rfl) ⟨4287338, by rfl⟩ : syracuseStep 5716451 = 8574677) B8574677
theorem B1587683 : Blo 1056613 1587683 := bstep (se 1 (by rfl) ⟨1190762, by rfl⟩ : syracuseStep 1587683 = 2381525) B2381525
theorem B1587713 : Blo 1056613 1587713 := bstep (se 2 (by rfl) ⟨595392, by rfl⟩ : syracuseStep 1587713 = 1190785) B1190785
theorem B1587731 : Blo 1056613 1587731 := bstep (se 1 (by rfl) ⟨1190798, by rfl⟩ : syracuseStep 1587731 = 2381597) B2381597
theorem B3389987 : Blo 1056613 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B1784369 : Blo 1056613 1784369 := bstep (se 2 (by rfl) ⟨669138, by rfl⟩ : syracuseStep 1784369 = 1338277) B1338277
theorem B1587761 : Blo 1056613 1587761 := bstep (se 2 (by rfl) ⟨595410, by rfl⟩ : syracuseStep 1587761 = 1190821) B1190821
theorem B1587779 : Blo 1056613 1587779 := bstep (se 1 (by rfl) ⟨1190834, by rfl⟩ : syracuseStep 1587779 = 2381669) B2381669
theorem B1587809 : Blo 1056613 1587809 := bstep (se 2 (by rfl) ⟨595428, by rfl⟩ : syracuseStep 1587809 = 1190857) B1190857
theorem B1587827 : Blo 1056613 1587827 := bstep (se 1 (by rfl) ⟨1190870, by rfl⟩ : syracuseStep 1587827 = 2381741) B2381741
theorem B1587857 : Blo 1056613 1587857 := bstep (se 2 (by rfl) ⟨595446, by rfl⟩ : syracuseStep 1587857 = 1190893) B1190893
theorem B1587875 : Blo 1056613 1587875 := bstep (se 1 (by rfl) ⟨1190906, by rfl⟩ : syracuseStep 1587875 = 2381813) B2381813
theorem B1784497 : Blo 1056613 1784497 := bstep (se 2 (by rfl) ⟨669186, by rfl⟩ : syracuseStep 1784497 = 1338373) B1338373
theorem B1587905 : Blo 1056613 1587905 := bstep (se 2 (by rfl) ⟨595464, by rfl⟩ : syracuseStep 1587905 = 1190929) B1190929
theorem B1784531 : Blo 1056613 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B1587923 : Blo 1056613 1587923 := bstep (se 1 (by rfl) ⟨1190942, by rfl⟩ : syracuseStep 1587923 = 2381885) B2381885
theorem B1587953 : Blo 1056613 1587953 := bstep (se 2 (by rfl) ⟨595482, by rfl⟩ : syracuseStep 1587953 = 1190965) B1190965
theorem B1587971 : Blo 1056613 1587971 := bstep (se 1 (by rfl) ⟨1190978, by rfl⟩ : syracuseStep 1587971 = 2381957) B2381957
theorem B1588001 : Blo 1056613 1588001 := bstep (se 2 (by rfl) ⟨595500, by rfl⟩ : syracuseStep 1588001 = 1191001) B1191001
theorem B1588019 : Blo 1056613 1588019 := bstep (se 1 (by rfl) ⟨1191014, by rfl⟩ : syracuseStep 1588019 = 2382029) B2382029
theorem B1588049 : Blo 1056613 1588049 := bstep (se 2 (by rfl) ⟨595518, by rfl⟩ : syracuseStep 1588049 = 1191037) B1191037
theorem B1784659 : Blo 1056613 1784659 := bstep (se 1 (by rfl) ⟨1338494, by rfl⟩ : syracuseStep 1784659 = 2676989) B2676989
theorem B1588067 : Blo 1056613 1588067 := bstep (se 1 (by rfl) ⟨1191050, by rfl⟩ : syracuseStep 1588067 = 2382101) B2382101
theorem B3816305 : Blo 1056613 3816305 := bstep (se 2 (by rfl) ⟨1431114, by rfl⟩ : syracuseStep 3816305 = 2862229) B2862229
theorem B1588097 : Blo 1056613 1588097 := bstep (se 2 (by rfl) ⟨595536, by rfl⟩ : syracuseStep 1588097 = 1191073) B1191073
theorem B3619729 : Blo 1056613 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B1588115 : Blo 1056613 1588115 := bstep (se 1 (by rfl) ⟨1191086, by rfl⟩ : syracuseStep 1588115 = 2382173) B2382173
theorem B1588145 : Blo 1056613 1588145 := bstep (se 2 (by rfl) ⟨595554, by rfl⟩ : syracuseStep 1588145 = 1191109) B1191109
theorem B1129411 : Blo 1056613 1129411 := bstep (se 1 (by rfl) ⟨847058, by rfl⟩ : syracuseStep 1129411 = 1694117) B1694117
theorem B1588163 : Blo 1056613 1588163 := bstep (se 1 (by rfl) ⟨1191122, by rfl⟩ : syracuseStep 1588163 = 2382245) B2382245
theorem B1784801 : Blo 1056613 1784801 := bstep (se 2 (by rfl) ⟨669300, by rfl⟩ : syracuseStep 1784801 = 1338601) B1338601
theorem B1588193 : Blo 1056613 1588193 := bstep (se 2 (by rfl) ⟨595572, by rfl⟩ : syracuseStep 1588193 = 1191145) B1191145
theorem B5356529 : Blo 1056613 5356529 := bstep (se 2 (by rfl) ⟨2008698, by rfl⟩ : syracuseStep 5356529 = 4017397) B4017397
theorem B1588211 : Blo 1056613 1588211 := bstep (se 1 (by rfl) ⟨1191158, by rfl⟩ : syracuseStep 1588211 = 2382317) B2382317
theorem B1588241 : Blo 1056613 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B1588259 : Blo 1056613 1588259 := bstep (se 1 (by rfl) ⟨1191194, by rfl⟩ : syracuseStep 1588259 = 2382389) B2382389
theorem B1588289 : Blo 1056613 1588289 := bstep (se 2 (by rfl) ⟨595608, by rfl⟩ : syracuseStep 1588289 = 1191217) B1191217
theorem B1588307 : Blo 1056613 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B1784929 : Blo 1056613 1784929 := bstep (se 2 (by rfl) ⟨669348, by rfl⟩ : syracuseStep 1784929 = 1338697) B1338697
theorem B1588337 : Blo 1056613 1588337 := bstep (se 2 (by rfl) ⟨595626, by rfl⟩ : syracuseStep 1588337 = 1191253) B1191253
theorem B1784963 : Blo 1056613 1784963 := bstep (se 1 (by rfl) ⟨1338722, by rfl⟩ : syracuseStep 1784963 = 2677445) B2677445
theorem B1588355 : Blo 1056613 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B1588385 : Blo 1056613 1588385 := bstep (se 2 (by rfl) ⟨595644, by rfl⟩ : syracuseStep 1588385 = 1191289) B1191289
theorem B1588403 : Blo 1056613 1588403 := bstep (se 1 (by rfl) ⟨1191302, by rfl⟩ : syracuseStep 1588403 = 2382605) B2382605
theorem B1588433 : Blo 1056613 1588433 := bstep (se 2 (by rfl) ⟨595662, by rfl⟩ : syracuseStep 1588433 = 1191325) B1191325
theorem B1588451 : Blo 1056613 1588451 := bstep (se 1 (by rfl) ⟨1191338, by rfl⟩ : syracuseStep 1588451 = 2382677) B2382677
theorem B4013297 : Blo 1056613 4013297 := bstep (se 2 (by rfl) ⟨1504986, by rfl⟩ : syracuseStep 4013297 = 3009973) B3009973
theorem B1588481 : Blo 1056613 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B1785091 : Blo 1056613 1785091 := bstep (se 1 (by rfl) ⟨1338818, by rfl⟩ : syracuseStep 1785091 = 2677637) B2677637
theorem B1588499 : Blo 1056613 1588499 := bstep (se 1 (by rfl) ⟨1191374, by rfl⟩ : syracuseStep 1588499 = 2382749) B2382749
theorem B5717297 : Blo 1056613 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B1588529 : Blo 1056613 1588529 := bstep (se 2 (by rfl) ⟨595698, by rfl⟩ : syracuseStep 1588529 = 1191397) B1191397
theorem B1588547 : Blo 1056613 1588547 := bstep (se 1 (by rfl) ⟨1191410, by rfl⟩ : syracuseStep 1588547 = 2382821) B2382821
theorem B1588577 : Blo 1056613 1588577 := bstep (se 2 (by rfl) ⟨595716, by rfl⟩ : syracuseStep 1588577 = 1191433) B1191433
theorem B1588595 : Blo 1056613 1588595 := bstep (se 1 (by rfl) ⟨1191446, by rfl⟩ : syracuseStep 1588595 = 2382893) B2382893
theorem B1785233 : Blo 1056613 1785233 := bstep (se 2 (by rfl) ⟨669462, by rfl⟩ : syracuseStep 1785233 = 1338925) B1338925
theorem B1588625 : Blo 1056613 1588625 := bstep (se 2 (by rfl) ⟨595734, by rfl⟩ : syracuseStep 1588625 = 1191469) B1191469
theorem B1588643 : Blo 1056613 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B3816881 : Blo 1056613 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B1588673 : Blo 1056613 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B2178499 : Blo 1056613 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B7617989 : Blo 1056613 7617989 := bstep (se 4 (by rfl) ⟨714186, by rfl⟩ : syracuseStep 7617989 = 1428373) B1428373
theorem B1588691 : Blo 1056613 1588691 := bstep (se 1 (by rfl) ⟨1191518, by rfl⟩ : syracuseStep 1588691 = 2383037) B2383037
theorem B1588721 : Blo 1056613 1588721 := bstep (se 2 (by rfl) ⟨595770, by rfl⟩ : syracuseStep 1588721 = 1191541) B1191541
theorem B1588739 : Blo 1056613 1588739 := bstep (se 1 (by rfl) ⟨1191554, by rfl⟩ : syracuseStep 1588739 = 2383109) B2383109
theorem B1785361 : Blo 1056613 1785361 := bstep (se 2 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 1785361 = 1339021) B1339021
theorem B1588769 : Blo 1056613 1588769 := bstep (se 2 (by rfl) ⟨595788, by rfl⟩ : syracuseStep 1588769 = 1191577) B1191577
theorem B1785395 : Blo 1056613 1785395 := bstep (se 1 (by rfl) ⟨1339046, by rfl⟩ : syracuseStep 1785395 = 2678093) B2678093
theorem B1588787 : Blo 1056613 1588787 := bstep (se 1 (by rfl) ⟨1191590, by rfl⟩ : syracuseStep 1588787 = 2383181) B2383181
theorem B1588817 : Blo 1056613 1588817 := bstep (se 2 (by rfl) ⟨595806, by rfl⟩ : syracuseStep 1588817 = 1191613) B1191613
theorem B1588835 : Blo 1056613 1588835 := bstep (se 1 (by rfl) ⟨1191626, by rfl⟩ : syracuseStep 1588835 = 2383253) B2383253
theorem B1588865 : Blo 1056613 1588865 := bstep (se 2 (by rfl) ⟨595824, by rfl⟩ : syracuseStep 1588865 = 1191649) B1191649
theorem B1588883 : Blo 1056613 1588883 := bstep (se 1 (by rfl) ⟨1191662, by rfl⟩ : syracuseStep 1588883 = 2383325) B2383325
theorem B1588913 : Blo 1056613 1588913 := bstep (se 2 (by rfl) ⟨595842, by rfl⟩ : syracuseStep 1588913 = 1191685) B1191685
theorem B1785523 : Blo 1056613 1785523 := bstep (se 1 (by rfl) ⟨1339142, by rfl⟩ : syracuseStep 1785523 = 2678285) B2678285
theorem B1588931 : Blo 1056613 1588931 := bstep (se 1 (by rfl) ⟨1191698, by rfl⟩ : syracuseStep 1588931 = 2383397) B2383397
theorem B1588961 : Blo 1056613 1588961 := bstep (se 2 (by rfl) ⟨595860, by rfl⟩ : syracuseStep 1588961 = 1191721) B1191721
theorem B1588979 : Blo 1056613 1588979 := bstep (se 1 (by rfl) ⟨1191734, by rfl⟩ : syracuseStep 1588979 = 2383469) B2383469
theorem B1589009 : Blo 1056613 1589009 := bstep (se 2 (by rfl) ⟨595878, by rfl⟩ : syracuseStep 1589009 = 1191757) B1191757
theorem B1589027 : Blo 1056613 1589027 := bstep (se 1 (by rfl) ⟨1191770, by rfl⟩ : syracuseStep 1589027 = 2383541) B2383541
theorem B1785665 : Blo 1056613 1785665 := bstep (se 2 (by rfl) ⟨669624, by rfl⟩ : syracuseStep 1785665 = 1339249) B1339249
theorem B1589057 : Blo 1056613 1589057 := bstep (se 2 (by rfl) ⟨595896, by rfl⟩ : syracuseStep 1589057 = 1191793) B1191793
theorem B1589075 : Blo 1056613 1589075 := bstep (se 1 (by rfl) ⟨1191806, by rfl⟩ : syracuseStep 1589075 = 2383613) B2383613
theorem B1589105 : Blo 1056613 1589105 := bstep (se 2 (by rfl) ⟨595914, by rfl⟩ : syracuseStep 1589105 = 1191829) B1191829
theorem B1589123 : Blo 1056613 1589123 := bstep (se 1 (by rfl) ⟨1191842, by rfl⟩ : syracuseStep 1589123 = 2383685) B2383685
theorem B1589153 : Blo 1056613 1589153 := bstep (se 2 (by rfl) ⟨595932, by rfl⟩ : syracuseStep 1589153 = 1191865) B1191865
theorem B1589171 : Blo 1056613 1589171 := bstep (se 1 (by rfl) ⟨1191878, by rfl⟩ : syracuseStep 1589171 = 2383757) B2383757
theorem B1785793 : Blo 1056613 1785793 := bstep (se 2 (by rfl) ⟨669672, by rfl⟩ : syracuseStep 1785793 = 1339345) B1339345
theorem B1589201 : Blo 1056613 1589201 := bstep (se 2 (by rfl) ⟨595950, by rfl⟩ : syracuseStep 1589201 = 1191901) B1191901
theorem B1785827 : Blo 1056613 1785827 := bstep (se 1 (by rfl) ⟨1339370, by rfl⟩ : syracuseStep 1785827 = 2678741) B2678741
theorem B1589219 : Blo 1056613 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B4079587 : Blo 1056613 4079587 := bstep (se 1 (by rfl) ⟨3059690, by rfl⟩ : syracuseStep 4079587 = 6119381) B6119381
theorem B1130483 : Blo 1056613 1130483 := bstep (se 1 (by rfl) ⟨847862, by rfl⟩ : syracuseStep 1130483 = 1695725) B1695725
theorem B1589249 : Blo 1056613 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B1589267 : Blo 1056613 1589267 := bstep (se 1 (by rfl) ⟨1191950, by rfl⟩ : syracuseStep 1589267 = 2383901) B2383901
theorem B1589297 : Blo 1056613 1589297 := bstep (se 2 (by rfl) ⟨595986, by rfl⟩ : syracuseStep 1589297 = 1191973) B1191973
theorem B1589315 : Blo 1056613 1589315 := bstep (se 1 (by rfl) ⟨1191986, by rfl⟩ : syracuseStep 1589315 = 2383973) B2383973
theorem B3620945 : Blo 1056613 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B1589345 : Blo 1056613 1589345 := bstep (se 2 (by rfl) ⟨596004, by rfl⟩ : syracuseStep 1589345 = 1192009) B1192009
theorem B1785955 : Blo 1056613 1785955 := bstep (se 1 (by rfl) ⟨1339466, by rfl⟩ : syracuseStep 1785955 = 2678933) B2678933
theorem B1589363 : Blo 1056613 1589363 := bstep (se 1 (by rfl) ⟨1192022, by rfl⟩ : syracuseStep 1589363 = 2384045) B2384045
theorem B1589393 : Blo 1056613 1589393 := bstep (se 2 (by rfl) ⟨596022, by rfl⟩ : syracuseStep 1589393 = 1192045) B1192045
theorem B1589411 : Blo 1056613 1589411 := bstep (se 1 (by rfl) ⟨1192058, by rfl⟩ : syracuseStep 1589411 = 2384117) B2384117
theorem B1589441 : Blo 1056613 1589441 := bstep (se 2 (by rfl) ⟨596040, by rfl⟩ : syracuseStep 1589441 = 1192081) B1192081
theorem B1589459 : Blo 1056613 1589459 := bstep (se 1 (by rfl) ⟨1192094, by rfl⟩ : syracuseStep 1589459 = 2384189) B2384189
theorem B156844259 : Blo 1056613 156844259 := bstep (se 1 (by rfl) ⟨117633194, by rfl⟩ : syracuseStep 156844259 = 235266389) B235266389
theorem B1786097 : Blo 1056613 1786097 := bstep (se 2 (by rfl) ⟨669786, by rfl⟩ : syracuseStep 1786097 = 1339573) B1339573
theorem B1589489 : Blo 1056613 1589489 := bstep (se 2 (by rfl) ⟨596058, by rfl⟩ : syracuseStep 1589489 = 1192117) B1192117
theorem B1589507 : Blo 1056613 1589507 := bstep (se 1 (by rfl) ⟨1192130, by rfl⟩ : syracuseStep 1589507 = 2384261) B2384261
theorem B3391757 : Blo 1056613 3391757 := bstep (se 3 (by rfl) ⟨635954, by rfl⟩ : syracuseStep 3391757 = 1271909) B1271909
theorem B1589537 : Blo 1056613 1589537 := bstep (se 2 (by rfl) ⟨596076, by rfl⟩ : syracuseStep 1589537 = 1192153) B1192153
theorem B1589555 : Blo 1056613 1589555 := bstep (se 1 (by rfl) ⟨1192166, by rfl⟩ : syracuseStep 1589555 = 2384333) B2384333
theorem B1589585 : Blo 1056613 1589585 := bstep (se 2 (by rfl) ⟨596094, by rfl⟩ : syracuseStep 1589585 = 1192189) B1192189
theorem B1589603 : Blo 1056613 1589603 := bstep (se 1 (by rfl) ⟨1192202, by rfl⟩ : syracuseStep 1589603 = 2384405) B2384405
theorem B1786225 : Blo 1056613 1786225 := bstep (se 2 (by rfl) ⟨669834, by rfl⟩ : syracuseStep 1786225 = 1339669) B1339669
theorem B1589633 : Blo 1056613 1589633 := bstep (se 2 (by rfl) ⟨596112, by rfl⟩ : syracuseStep 1589633 = 1192225) B1192225
theorem B1786259 : Blo 1056613 1786259 := bstep (se 1 (by rfl) ⟨1339694, by rfl⟩ : syracuseStep 1786259 = 2679389) B2679389
theorem B1589651 : Blo 1056613 1589651 := bstep (se 1 (by rfl) ⟨1192238, by rfl⟩ : syracuseStep 1589651 = 2384477) B2384477
theorem B5357987 : Blo 1056613 5357987 := bstep (se 1 (by rfl) ⟨4018490, by rfl⟩ : syracuseStep 5357987 = 8036981) B8036981
theorem B1589681 : Blo 1056613 1589681 := bstep (se 2 (by rfl) ⟨596130, by rfl⟩ : syracuseStep 1589681 = 1192261) B1192261
theorem B1589699 : Blo 1056613 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B1589729 : Blo 1056613 1589729 := bstep (se 2 (by rfl) ⟨596148, by rfl⟩ : syracuseStep 1589729 = 1192297) B1192297
theorem B1589747 : Blo 1056613 1589747 := bstep (se 1 (by rfl) ⟨1192310, by rfl⟩ : syracuseStep 1589747 = 2384621) B2384621
theorem B1589777 : Blo 1056613 1589777 := bstep (se 2 (by rfl) ⟨596166, by rfl⟩ : syracuseStep 1589777 = 1192333) B1192333
theorem B1786387 : Blo 1056613 1786387 := bstep (se 1 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 1786387 = 2679581) B2679581
theorem B1589795 : Blo 1056613 1589795 := bstep (se 1 (by rfl) ⟨1192346, by rfl⟩ : syracuseStep 1589795 = 2384693) B2384693
theorem B1589825 : Blo 1056613 1589825 := bstep (se 2 (by rfl) ⟨596184, by rfl⟩ : syracuseStep 1589825 = 1192369) B1192369
theorem B2540099 : Blo 1056613 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B1589843 : Blo 1056613 1589843 := bstep (se 1 (by rfl) ⟨1192382, by rfl⟩ : syracuseStep 1589843 = 2384765) B2384765
theorem B1589873 : Blo 1056613 1589873 := bstep (se 2 (by rfl) ⟨596202, by rfl⟩ : syracuseStep 1589873 = 1192405) B1192405
theorem B1589891 : Blo 1056613 1589891 := bstep (se 1 (by rfl) ⟨1192418, by rfl⟩ : syracuseStep 1589891 = 2384837) B2384837
theorem B1786529 : Blo 1056613 1786529 := bstep (se 2 (by rfl) ⟨669948, by rfl⟩ : syracuseStep 1786529 = 1339897) B1339897
theorem B1589921 : Blo 1056613 1589921 := bstep (se 2 (by rfl) ⟨596220, by rfl⟩ : syracuseStep 1589921 = 1192441) B1192441
theorem B4014755 : Blo 1056613 4014755 := bstep (se 1 (by rfl) ⟨3011066, by rfl⟩ : syracuseStep 4014755 = 6022133) B6022133
theorem B1589939 : Blo 1056613 1589939 := bstep (se 1 (by rfl) ⟨1192454, by rfl⟩ : syracuseStep 1589939 = 2384909) B2384909
theorem B1589969 : Blo 1056613 1589969 := bstep (se 2 (by rfl) ⟨596238, by rfl⟩ : syracuseStep 1589969 = 1192477) B1192477
theorem B1589987 : Blo 1056613 1589987 := bstep (se 1 (by rfl) ⟨1192490, by rfl⟩ : syracuseStep 1589987 = 2384981) B2384981
theorem B1590017 : Blo 1056613 1590017 := bstep (se 2 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 1590017 = 1192513) B1192513
theorem B1590035 : Blo 1056613 1590035 := bstep (se 1 (by rfl) ⟨1192526, by rfl⟩ : syracuseStep 1590035 = 2385053) B2385053
theorem B1786657 : Blo 1056613 1786657 := bstep (se 2 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 1786657 = 1339993) B1339993
theorem B1590065 : Blo 1056613 1590065 := bstep (se 2 (by rfl) ⟨596274, by rfl⟩ : syracuseStep 1590065 = 1192549) B1192549
theorem B1786691 : Blo 1056613 1786691 := bstep (se 1 (by rfl) ⟨1340018, by rfl⟩ : syracuseStep 1786691 = 2680037) B2680037
theorem B1590083 : Blo 1056613 1590083 := bstep (se 1 (by rfl) ⟨1192562, by rfl⟩ : syracuseStep 1590083 = 2385125) B2385125
theorem B1590113 : Blo 1056613 1590113 := bstep (se 2 (by rfl) ⟨596292, by rfl⟩ : syracuseStep 1590113 = 1192585) B1192585
theorem B1590131 : Blo 1056613 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B1590161 : Blo 1056613 1590161 := bstep (se 2 (by rfl) ⟨596310, by rfl⟩ : syracuseStep 1590161 = 1192621) B1192621
theorem B3490705 : Blo 1056613 3490705 := bstep (se 2 (by rfl) ⟨1309014, by rfl⟩ : syracuseStep 3490705 = 2618029) B2618029
theorem B1590179 : Blo 1056613 1590179 := bstep (se 1 (by rfl) ⟨1192634, by rfl⟩ : syracuseStep 1590179 = 2385269) B2385269
theorem B1590209 : Blo 1056613 1590209 := bstep (se 2 (by rfl) ⟨596328, by rfl⟩ : syracuseStep 1590209 = 1192657) B1192657
theorem B1786819 : Blo 1056613 1786819 := bstep (se 1 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 1786819 = 2680229) B2680229
theorem B1590227 : Blo 1056613 1590227 := bstep (se 1 (by rfl) ⟨1192670, by rfl⟩ : syracuseStep 1590227 = 2385341) B2385341
theorem B1590257 : Blo 1056613 1590257 := bstep (se 2 (by rfl) ⟨596346, by rfl⟩ : syracuseStep 1590257 = 1192693) B1192693
theorem B1590275 : Blo 1056613 1590275 := bstep (se 1 (by rfl) ⟨1192706, by rfl⟩ : syracuseStep 1590275 = 2385413) B2385413
theorem B1590305 : Blo 1056613 1590305 := bstep (se 2 (by rfl) ⟨596364, by rfl⟩ : syracuseStep 1590305 = 1192729) B1192729
theorem B1590323 : Blo 1056613 1590323 := bstep (se 1 (by rfl) ⟨1192742, by rfl⟩ : syracuseStep 1590323 = 2385485) B2385485
theorem B1786961 : Blo 1056613 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B1590353 : Blo 1056613 1590353 := bstep (se 2 (by rfl) ⟨596382, by rfl⟩ : syracuseStep 1590353 = 1192765) B1192765
theorem B1131619 : Blo 1056613 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B1590371 : Blo 1056613 1590371 := bstep (se 1 (by rfl) ⟨1192778, by rfl⟩ : syracuseStep 1590371 = 2385557) B2385557
theorem B1590401 : Blo 1056613 1590401 := bstep (se 2 (by rfl) ⟨596400, by rfl⟩ : syracuseStep 1590401 = 1192801) B1192801
theorem B1590419 : Blo 1056613 1590419 := bstep (se 1 (by rfl) ⟨1192814, by rfl⟩ : syracuseStep 1590419 = 2385629) B2385629
theorem B1590449 : Blo 1056613 1590449 := bstep (se 2 (by rfl) ⟨596418, by rfl⟩ : syracuseStep 1590449 = 1192837) B1192837
theorem B1590467 : Blo 1056613 1590467 := bstep (se 1 (by rfl) ⟨1192850, by rfl⟩ : syracuseStep 1590467 = 2385701) B2385701
theorem B5358797 : Blo 1056613 5358797 := bstep (se 3 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 5358797 = 2009549) B2009549
theorem B1787089 : Blo 1056613 1787089 := bstep (se 2 (by rfl) ⟨670158, by rfl⟩ : syracuseStep 1787089 = 1340317) B1340317
theorem B1590497 : Blo 1056613 1590497 := bstep (se 2 (by rfl) ⟨596436, by rfl⟩ : syracuseStep 1590497 = 1192873) B1192873
theorem B1787123 : Blo 1056613 1787123 := bstep (se 1 (by rfl) ⟨1340342, by rfl⟩ : syracuseStep 1787123 = 2680685) B2680685
theorem B1590515 : Blo 1056613 1590515 := bstep (se 1 (by rfl) ⟨1192886, by rfl⟩ : syracuseStep 1590515 = 2385773) B2385773
theorem B1590545 : Blo 1056613 1590545 := bstep (se 2 (by rfl) ⟨596454, by rfl⟩ : syracuseStep 1590545 = 1192909) B1192909
theorem B6112547 : Blo 1056613 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B1590563 : Blo 1056613 1590563 := bstep (se 1 (by rfl) ⟨1192922, by rfl⟩ : syracuseStep 1590563 = 2385845) B2385845
theorem B1590593 : Blo 1056613 1590593 := bstep (se 2 (by rfl) ⟨596472, by rfl⟩ : syracuseStep 1590593 = 1192945) B1192945
theorem B1590611 : Blo 1056613 1590611 := bstep (se 1 (by rfl) ⟨1192958, by rfl⟩ : syracuseStep 1590611 = 2385917) B2385917
theorem B1590641 : Blo 1056613 1590641 := bstep (se 2 (by rfl) ⟨596490, by rfl⟩ : syracuseStep 1590641 = 1192981) B1192981
theorem B1787251 : Blo 1056613 1787251 := bstep (se 1 (by rfl) ⟨1340438, by rfl⟩ : syracuseStep 1787251 = 2680877) B2680877
theorem B1590659 : Blo 1056613 1590659 := bstep (se 1 (by rfl) ⟨1192994, by rfl⟩ : syracuseStep 1590659 = 2385989) B2385989
theorem B2540945 : Blo 1056613 2540945 := bstep (se 2 (by rfl) ⟨952854, by rfl⟩ : syracuseStep 2540945 = 1905709) B1905709
theorem B1590689 : Blo 1056613 1590689 := bstep (se 2 (by rfl) ⟨596508, by rfl⟩ : syracuseStep 1590689 = 1193017) B1193017
theorem B1590707 : Blo 1056613 1590707 := bstep (se 1 (by rfl) ⟨1193030, by rfl⟩ : syracuseStep 1590707 = 2386061) B2386061
theorem B1590737 : Blo 1056613 1590737 := bstep (se 2 (by rfl) ⟨596526, by rfl⟩ : syracuseStep 1590737 = 1193053) B1193053
theorem B1590755 : Blo 1056613 1590755 := bstep (se 1 (by rfl) ⟨1193066, by rfl⟩ : syracuseStep 1590755 = 2386133) B2386133
theorem B1787393 : Blo 1056613 1787393 := bstep (se 2 (by rfl) ⟨670272, by rfl⟩ : syracuseStep 1787393 = 1340545) B1340545
theorem B1590785 : Blo 1056613 1590785 := bstep (se 2 (by rfl) ⟨596544, by rfl⟩ : syracuseStep 1590785 = 1193089) B1193089
theorem B1590803 : Blo 1056613 1590803 := bstep (se 1 (by rfl) ⟨1193102, by rfl⟩ : syracuseStep 1590803 = 2386205) B2386205
theorem B1590833 : Blo 1056613 1590833 := bstep (se 2 (by rfl) ⟨596562, by rfl⟩ : syracuseStep 1590833 = 1193125) B1193125
theorem B1590851 : Blo 1056613 1590851 := bstep (se 1 (by rfl) ⟨1193138, by rfl⟩ : syracuseStep 1590851 = 2386277) B2386277
theorem B12076613 : Blo 1056613 12076613 := bstep (se 4 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 12076613 = 2264365) B2264365
theorem B1590881 : Blo 1056613 1590881 := bstep (se 2 (by rfl) ⟨596580, by rfl⟩ : syracuseStep 1590881 = 1193161) B1193161
theorem B1590899 : Blo 1056613 1590899 := bstep (se 1 (by rfl) ⟨1193174, by rfl⟩ : syracuseStep 1590899 = 2386349) B2386349
theorem B1787521 : Blo 1056613 1787521 := bstep (se 2 (by rfl) ⟨670320, by rfl⟩ : syracuseStep 1787521 = 1340641) B1340641
theorem B4015757 : Blo 1056613 4015757 := bstep (se 3 (by rfl) ⟨752954, by rfl⟩ : syracuseStep 4015757 = 1505909) B1505909
theorem B1787555 : Blo 1056613 1787555 := bstep (se 1 (by rfl) ⟨1340666, by rfl⟩ : syracuseStep 1787555 = 2681333) B2681333
theorem B4343473 : Blo 1056613 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B2148049 : Blo 1056613 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B2377457 : Blo 1056613 2377457 := bstep (se 2 (by rfl) ⟨891546, by rfl⟩ : syracuseStep 2377457 = 1783093) B1783093
theorem B2377475 : Blo 1056613 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B1787683 : Blo 1056613 1787683 := bstep (se 1 (by rfl) ⟨1340762, by rfl⟩ : syracuseStep 1787683 = 2681525) B2681525
theorem B1787825 : Blo 1056613 1787825 := bstep (se 2 (by rfl) ⟨670434, by rfl⟩ : syracuseStep 1787825 = 1340869) B1340869
theorem B1132499 : Blo 1056613 1132499 := bstep (se 1 (by rfl) ⟨849374, by rfl⟩ : syracuseStep 1132499 = 1698749) B1698749
theorem B2377745 : Blo 1056613 2377745 := bstep (se 2 (by rfl) ⟨891654, by rfl⟩ : syracuseStep 2377745 = 1783309) B1783309
theorem B2377763 : Blo 1056613 2377763 := bstep (se 1 (by rfl) ⟨1783322, by rfl⟩ : syracuseStep 2377763 = 3566645) B3566645
theorem B1787953 : Blo 1056613 1787953 := bstep (se 2 (by rfl) ⟨670482, by rfl⟩ : syracuseStep 1787953 = 1340965) B1340965
theorem B1787987 : Blo 1056613 1787987 := bstep (se 1 (by rfl) ⟨1340990, by rfl⟩ : syracuseStep 1787987 = 2681981) B2681981
theorem B1788115 : Blo 1056613 1788115 := bstep (se 1 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 1788115 = 2682173) B2682173
theorem B2378033 : Blo 1056613 2378033 := bstep (se 2 (by rfl) ⟨891762, by rfl⟩ : syracuseStep 2378033 = 1783525) B1783525
theorem B2378051 : Blo 1056613 2378051 := bstep (se 1 (by rfl) ⟨1783538, by rfl⟩ : syracuseStep 2378051 = 3567077) B3567077
theorem B1788257 : Blo 1056613 1788257 := bstep (se 2 (by rfl) ⟨670596, by rfl⟩ : syracuseStep 1788257 = 1341193) B1341193
theorem B9029987 : Blo 1056613 9029987 := bstep (se 1 (by rfl) ⟨6772490, by rfl⟩ : syracuseStep 9029987 = 13544981) B13544981
theorem B23841137 : Blo 1056613 23841137 := bstep (se 2 (by rfl) ⟨8940426, by rfl⟩ : syracuseStep 23841137 = 17880853) B17880853
theorem B1788385 : Blo 1056613 1788385 := bstep (se 2 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 1788385 = 1341289) B1341289
theorem B1788419 : Blo 1056613 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B3820067 : Blo 1056613 3820067 := bstep (se 1 (by rfl) ⟨2865050, by rfl⟩ : syracuseStep 3820067 = 5730101) B5730101
theorem B2378321 : Blo 1056613 2378321 := bstep (se 2 (by rfl) ⟨891870, by rfl⟩ : syracuseStep 2378321 = 1783741) B1783741
theorem B2378339 : Blo 1056613 2378339 := bstep (se 1 (by rfl) ⟨1783754, by rfl⟩ : syracuseStep 2378339 = 3567509) B3567509
theorem B1788547 : Blo 1056613 1788547 := bstep (se 1 (by rfl) ⟨1341410, by rfl⟩ : syracuseStep 1788547 = 2682821) B2682821
theorem B7621361 : Blo 1056613 7621361 := bstep (se 2 (by rfl) ⟨2858010, by rfl⟩ : syracuseStep 7621361 = 5716021) B5716021
theorem B1788689 : Blo 1056613 1788689 := bstep (se 2 (by rfl) ⟨670758, by rfl⟩ : syracuseStep 1788689 = 1341517) B1341517
theorem B6441763 : Blo 1056613 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B2378609 : Blo 1056613 2378609 := bstep (se 2 (by rfl) ⟨891978, by rfl⟩ : syracuseStep 2378609 = 1783957) B1783957
theorem B2378627 : Blo 1056613 2378627 := bstep (se 1 (by rfl) ⟨1783970, by rfl⟩ : syracuseStep 2378627 = 3567941) B3567941
theorem B1788817 : Blo 1056613 1788817 := bstep (se 2 (by rfl) ⟨670806, by rfl⟩ : syracuseStep 1788817 = 1341613) B1341613
theorem B1788851 : Blo 1056613 1788851 := bstep (se 1 (by rfl) ⟨1341638, by rfl⟩ : syracuseStep 1788851 = 2683277) B2683277
theorem B1788979 : Blo 1056613 1788979 := bstep (se 1 (by rfl) ⟨1341734, by rfl⟩ : syracuseStep 1788979 = 2683469) B2683469
theorem B2378897 : Blo 1056613 2378897 := bstep (se 2 (by rfl) ⟨892086, by rfl⟩ : syracuseStep 2378897 = 1784173) B1784173
theorem B2378915 : Blo 1056613 2378915 := bstep (se 1 (by rfl) ⟨1784186, by rfl⟩ : syracuseStep 2378915 = 3568373) B3568373
theorem B1789121 : Blo 1056613 1789121 := bstep (se 2 (by rfl) ⟨670920, by rfl⟩ : syracuseStep 1789121 = 1341841) B1341841
theorem B1789249 : Blo 1056613 1789249 := bstep (se 2 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 1789249 = 1341937) B1341937
theorem B4836685 : Blo 1056613 4836685 := bstep (se 3 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 4836685 = 1813757) B1813757
theorem B1789283 : Blo 1056613 1789283 := bstep (se 1 (by rfl) ⟨1341962, by rfl⟩ : syracuseStep 1789283 = 2683925) B2683925
theorem B2379185 : Blo 1056613 2379185 := bstep (se 2 (by rfl) ⟨892194, by rfl⟩ : syracuseStep 2379185 = 1784389) B1784389
theorem B2379203 : Blo 1056613 2379203 := bstep (se 1 (by rfl) ⟨1784402, by rfl⟩ : syracuseStep 2379203 = 3568805) B3568805
theorem B1789411 : Blo 1056613 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B1789553 : Blo 1056613 1789553 := bstep (se 2 (by rfl) ⟨671082, by rfl⟩ : syracuseStep 1789553 = 1342165) B1342165
theorem B3395267 : Blo 1056613 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B4017869 : Blo 1056613 4017869 := bstep (se 3 (by rfl) ⟨753350, by rfl⟩ : syracuseStep 4017869 = 1506701) B1506701
theorem B2379473 : Blo 1056613 2379473 := bstep (se 2 (by rfl) ⟨892302, by rfl⟩ : syracuseStep 2379473 = 1784605) B1784605
theorem B2379491 : Blo 1056613 2379491 := bstep (se 1 (by rfl) ⟨1784618, by rfl⟩ : syracuseStep 2379491 = 3569237) B3569237
theorem B1789681 : Blo 1056613 1789681 := bstep (se 2 (by rfl) ⟨671130, by rfl⟩ : syracuseStep 1789681 = 1342261) B1342261
theorem B1789715 : Blo 1056613 1789715 := bstep (se 1 (by rfl) ⟨1342286, by rfl⟩ : syracuseStep 1789715 = 2684573) B2684573
theorem B3821347 : Blo 1056613 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B2379761 : Blo 1056613 2379761 := bstep (se 2 (by rfl) ⟨892410, by rfl⟩ : syracuseStep 2379761 = 1784821) B1784821
theorem B2674691 : Blo 1056613 2674691 := bstep (se 1 (by rfl) ⟨2006018, by rfl⟩ : syracuseStep 2674691 = 4012037) B4012037
theorem B2379779 : Blo 1056613 2379779 := bstep (se 1 (by rfl) ⟨1784834, by rfl⟩ : syracuseStep 2379779 = 3569669) B3569669
theorem B5361713 : Blo 1056613 5361713 := bstep (se 2 (by rfl) ⟨2010642, by rfl⟩ : syracuseStep 5361713 = 4021285) B4021285
theorem B2543683 : Blo 1056613 2543683 := bstep (se 1 (by rfl) ⟨1907762, by rfl⟩ : syracuseStep 2543683 = 3815525) B3815525
theorem B3821681 : Blo 1056613 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B2674883 : Blo 1056613 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B132108515 : Blo 1056613 132108515 := bstep (se 1 (by rfl) ⟨99081386, by rfl⟩ : syracuseStep 132108515 = 198162773) B198162773
theorem B2380049 : Blo 1056613 2380049 := bstep (se 2 (by rfl) ⟨892518, by rfl⟩ : syracuseStep 2380049 = 1785037) B1785037
theorem B3395857 : Blo 1056613 3395857 := bstep (se 2 (by rfl) ⟨1273446, by rfl⟩ : syracuseStep 3395857 = 2546893) B2546893
theorem B2380067 : Blo 1056613 2380067 := bstep (se 1 (by rfl) ⟨1785050, by rfl⟩ : syracuseStep 2380067 = 3570101) B3570101
theorem B3625325 : Blo 1056613 3625325 := bstep (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) B1359497
theorem B5722595 : Blo 1056613 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B4018673 : Blo 1056613 4018673 := bstep (se 2 (by rfl) ⟨1507002, by rfl⟩ : syracuseStep 4018673 = 3014005) B3014005
theorem B2380337 : Blo 1056613 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B1430065 : Blo 1056613 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B2380355 : Blo 1056613 2380355 := bstep (se 1 (by rfl) ⟨1785266, by rfl⟩ : syracuseStep 2380355 = 3570533) B3570533
theorem B6869573 : Blo 1056613 6869573 := bstep (se 4 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 6869573 = 1288045) B1288045
theorem B10179269 : Blo 1056613 10179269 := bstep (se 4 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 10179269 = 1908613) B1908613
theorem B2380625 : Blo 1056613 2380625 := bstep (se 2 (by rfl) ⟨892734, by rfl⟩ : syracuseStep 2380625 = 1785469) B1785469
theorem B2380643 : Blo 1056613 2380643 := bstep (se 1 (by rfl) ⟨1785482, by rfl⟩ : syracuseStep 2380643 = 3570965) B3570965
theorem B4641677 : Blo 1056613 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B2544529 : Blo 1056613 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B1430465 : Blo 1056613 1430465 := bstep (se 2 (by rfl) ⟨536424, by rfl⟩ : syracuseStep 1430465 = 1072849) B1072849
theorem B2544643 : Blo 1056613 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B2675825 : Blo 1056613 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B2380913 : Blo 1056613 2380913 := bstep (se 2 (by rfl) ⟨892842, by rfl⟩ : syracuseStep 2380913 = 1785685) B1785685
theorem B2380931 : Blo 1056613 2380931 := bstep (se 1 (by rfl) ⟨1785698, by rfl⟩ : syracuseStep 2380931 = 3571397) B3571397
theorem B4019341 : Blo 1056613 4019341 := bstep (se 3 (by rfl) ⟨753626, by rfl⟩ : syracuseStep 4019341 = 1507253) B1507253
theorem B2675875 : Blo 1056613 2675875 := bstep (se 1 (by rfl) ⟨2006906, by rfl⟩ : syracuseStep 2675875 = 4013813) B4013813
theorem B2676017 : Blo 1056613 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B2381201 : Blo 1056613 2381201 := bstep (se 2 (by rfl) ⟨892950, by rfl⟩ : syracuseStep 2381201 = 1785901) B1785901
theorem B2381219 : Blo 1056613 2381219 := bstep (se 1 (by rfl) ⟨1785914, by rfl⟩ : syracuseStep 2381219 = 3571829) B3571829
theorem B5363171 : Blo 1056613 5363171 := bstep (se 1 (by rfl) ⟨4022378, by rfl⟩ : syracuseStep 5363171 = 8044757) B8044757
theorem B1693315 : Blo 1056613 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B3626627 : Blo 1056613 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B2381489 : Blo 1056613 2381489 := bstep (se 2 (by rfl) ⟨893058, by rfl⟩ : syracuseStep 2381489 = 1786117) B1786117
theorem B2381507 : Blo 1056613 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B2578115 : Blo 1056613 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B4020131 : Blo 1056613 4020131 := bstep (se 1 (by rfl) ⟨3015098, by rfl⟩ : syracuseStep 4020131 = 6030197) B6030197
theorem B2381777 : Blo 1056613 2381777 := bstep (se 2 (by rfl) ⟨893166, by rfl⟩ : syracuseStep 2381777 = 1786333) B1786333
theorem B2381795 : Blo 1056613 2381795 := bstep (se 1 (by rfl) ⟨1786346, by rfl⟩ : syracuseStep 2381795 = 3572693) B3572693
theorem B7231601 : Blo 1056613 7231601 := bstep (se 2 (by rfl) ⟨2711850, by rfl⟩ : syracuseStep 7231601 = 5423701) B5423701
theorem B2545873 : Blo 1056613 2545873 := bstep (se 2 (by rfl) ⟨954702, by rfl⟩ : syracuseStep 2545873 = 1909405) B1909405
theorem B2382065 : Blo 1056613 2382065 := bstep (se 2 (by rfl) ⟨893274, by rfl⟩ : syracuseStep 2382065 = 1786549) B1786549
theorem B2382083 : Blo 1056613 2382083 := bstep (se 1 (by rfl) ⟨1786562, by rfl⟩ : syracuseStep 2382083 = 3573125) B3573125
theorem B5363981 : Blo 1056613 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B2677009 : Blo 1056613 2677009 := bstep (se 2 (by rfl) ⟨1003878, by rfl⟩ : syracuseStep 2677009 = 2007757) B2007757
theorem B1694225 : Blo 1056613 1694225 := bstep (se 2 (by rfl) ⟨635334, by rfl⟩ : syracuseStep 1694225 = 1270669) B1270669
theorem B2382353 : Blo 1056613 2382353 := bstep (se 2 (by rfl) ⟨893382, by rfl⟩ : syracuseStep 2382353 = 1786765) B1786765
theorem B2677283 : Blo 1056613 2677283 := bstep (se 1 (by rfl) ⟨2007962, by rfl⟩ : syracuseStep 2677283 = 4015925) B4015925
theorem B2382371 : Blo 1056613 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B4020785 : Blo 1056613 4020785 := bstep (se 2 (by rfl) ⟨1507794, by rfl⟩ : syracuseStep 4020785 = 3015589) B3015589
theorem B6019717 : Blo 1056613 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B1694353 : Blo 1056613 1694353 := bstep (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) B1270765
theorem B8575715 : Blo 1056613 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B2677475 : Blo 1056613 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B5429987 : Blo 1056613 5429987 := bstep (se 1 (by rfl) ⟨4072490, by rfl⟩ : syracuseStep 5429987 = 8144981) B8144981
theorem B2382641 : Blo 1056613 2382641 := bstep (se 2 (by rfl) ⟨893490, by rfl⟩ : syracuseStep 2382641 = 1786981) B1786981
theorem B2382659 : Blo 1056613 2382659 := bstep (se 1 (by rfl) ⟨1786994, by rfl⟩ : syracuseStep 2382659 = 3573989) B3573989
theorem B30464909 : Blo 1056613 30464909 := bstep (se 3 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 30464909 = 11424341) B11424341
theorem B2382929 : Blo 1056613 2382929 := bstep (se 2 (by rfl) ⟨893598, by rfl⟩ : syracuseStep 2382929 = 1787197) B1787197
theorem B2382947 : Blo 1056613 2382947 := bstep (se 1 (by rfl) ⟨1787210, by rfl⟩ : syracuseStep 2382947 = 3574421) B3574421
theorem B5725361 : Blo 1056613 5725361 := bstep (se 2 (by rfl) ⟨2147010, by rfl⟩ : syracuseStep 5725361 = 4294021) B4294021
theorem B6774029 : Blo 1056613 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B2383217 : Blo 1056613 2383217 := bstep (se 2 (by rfl) ⟨893706, by rfl⟩ : syracuseStep 2383217 = 1787413) B1787413
theorem B2383235 : Blo 1056613 2383235 := bstep (se 1 (by rfl) ⟨1787426, by rfl⟩ : syracuseStep 2383235 = 3574853) B3574853
theorem B3431825 : Blo 1056613 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B2448899 : Blo 1056613 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B1695347 : Blo 1056613 1695347 := bstep (se 1 (by rfl) ⟨1271510, by rfl⟩ : syracuseStep 1695347 = 2543021) B2543021
theorem B4513421 : Blo 1056613 4513421 := bstep (se 3 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 4513421 = 1692533) B1692533
theorem B2678417 : Blo 1056613 2678417 := bstep (se 2 (by rfl) ⟨1004406, by rfl⟩ : syracuseStep 2678417 = 2008813) B2008813
theorem B2383505 : Blo 1056613 2383505 := bstep (se 2 (by rfl) ⟨893814, by rfl⟩ : syracuseStep 2383505 = 1787629) B1787629
theorem B2383523 : Blo 1056613 2383523 := bstep (se 1 (by rfl) ⟨1787642, by rfl⟩ : syracuseStep 2383523 = 3575285) B3575285
theorem B2678467 : Blo 1056613 2678467 := bstep (se 1 (by rfl) ⟨2008850, by rfl⟩ : syracuseStep 2678467 = 4017701) B4017701
theorem B2678609 : Blo 1056613 2678609 := bstep (se 2 (by rfl) ⟨1004478, by rfl⟩ : syracuseStep 2678609 = 2008957) B2008957
theorem B2416483 : Blo 1056613 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B2383793 : Blo 1056613 2383793 := bstep (se 2 (by rfl) ⟨893922, by rfl⟩ : syracuseStep 2383793 = 1787845) B1787845
theorem B2383811 : Blo 1056613 2383811 := bstep (se 1 (by rfl) ⟨1787858, by rfl⟩ : syracuseStep 2383811 = 3575717) B3575717
theorem B4022243 : Blo 1056613 4022243 := bstep (se 1 (by rfl) ⟨3016682, by rfl⟩ : syracuseStep 4022243 = 6033365) B6033365
theorem B4022257 : Blo 1056613 4022257 := bstep (se 2 (by rfl) ⟨1508346, by rfl⟩ : syracuseStep 4022257 = 3016693) B3016693
theorem B7233571 : Blo 1056613 7233571 := bstep (se 1 (by rfl) ⟨5425178, by rfl⟩ : syracuseStep 7233571 = 10850357) B10850357
theorem B2384081 : Blo 1056613 2384081 := bstep (se 2 (by rfl) ⟨894030, by rfl⟩ : syracuseStep 2384081 = 1788061) B1788061
theorem B2384099 : Blo 1056613 2384099 := bstep (se 1 (by rfl) ⟨1788074, by rfl⟩ : syracuseStep 2384099 = 3576149) B3576149
theorem B2712017 : Blo 1056613 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B2384369 : Blo 1056613 2384369 := bstep (se 2 (by rfl) ⟨894138, by rfl⟩ : syracuseStep 2384369 = 1788277) B1788277
theorem B2384387 : Blo 1056613 2384387 := bstep (se 1 (by rfl) ⟨1788290, by rfl⟩ : syracuseStep 2384387 = 3576581) B3576581
theorem B6021701 : Blo 1056613 6021701 := bstep (se 4 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 6021701 = 1129069) B1129069
theorem B4285169 : Blo 1056613 4285169 := bstep (se 2 (by rfl) ⟨1606938, by rfl⟩ : syracuseStep 4285169 = 3213877) B3213877
theorem B2384657 : Blo 1056613 2384657 := bstep (se 2 (by rfl) ⟨894246, by rfl⟩ : syracuseStep 2384657 = 1788493) B1788493
theorem B2384675 : Blo 1056613 2384675 := bstep (se 1 (by rfl) ⟨1788506, by rfl⟩ : syracuseStep 2384675 = 3577013) B3577013
theorem B2679601 : Blo 1056613 2679601 := bstep (se 2 (by rfl) ⟨1004850, by rfl⟩ : syracuseStep 2679601 = 2009701) B2009701
theorem B1696801 : Blo 1056613 1696801 := bstep (se 2 (by rfl) ⟨636300, by rfl⟩ : syracuseStep 1696801 = 1272601) B1272601
theorem B2384945 : Blo 1056613 2384945 := bstep (se 2 (by rfl) ⟨894354, by rfl⟩ : syracuseStep 2384945 = 1788709) B1788709
theorem B2679875 : Blo 1056613 2679875 := bstep (se 1 (by rfl) ⟨2009906, by rfl⟩ : syracuseStep 2679875 = 4019813) B4019813
theorem B2384963 : Blo 1056613 2384963 := bstep (se 1 (by rfl) ⟨1788722, by rfl⟩ : syracuseStep 2384963 = 3577445) B3577445
theorem B5366897 : Blo 1056613 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B2680067 : Blo 1056613 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B5727523 : Blo 1056613 5727523 := bstep (se 1 (by rfl) ⟨4295642, by rfl⟩ : syracuseStep 5727523 = 8591285) B8591285
theorem B2385233 : Blo 1056613 2385233 := bstep (se 2 (by rfl) ⟨894462, by rfl⟩ : syracuseStep 2385233 = 1788925) B1788925
theorem B2385251 : Blo 1056613 2385251 := bstep (se 1 (by rfl) ⟨1788938, by rfl⟩ : syracuseStep 2385251 = 3577877) B3577877
theorem B4023715 : Blo 1056613 4023715 := bstep (se 1 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 4023715 = 6035573) B6035573
theorem B3434083 : Blo 1056613 3434083 := bstep (se 1 (by rfl) ⟨2575562, by rfl⟩ : syracuseStep 3434083 = 5151125) B5151125
theorem B2385521 : Blo 1056613 2385521 := bstep (se 2 (by rfl) ⟨894570, by rfl⟩ : syracuseStep 2385521 = 1789141) B1789141
theorem B1074803 : Blo 1056613 1074803 := bstep (se 1 (by rfl) ⟨806102, by rfl⟩ : syracuseStep 1074803 = 1612205) B1612205
theorem B2385539 : Blo 1056613 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1632001 : Blo 1056613 1632001 := bstep (se 2 (by rfl) ⟨612000, by rfl⟩ : syracuseStep 1632001 = 1224001) B1224001
theorem B1271587 : Blo 1056613 1271587 := bstep (se 1 (by rfl) ⟨953690, by rfl⟩ : syracuseStep 1271587 = 1907381) B1907381
theorem B2385809 : Blo 1056613 2385809 := bstep (se 2 (by rfl) ⟨894678, by rfl⟩ : syracuseStep 2385809 = 1789357) B1789357
theorem B2385827 : Blo 1056613 2385827 := bstep (se 1 (by rfl) ⟨1789370, by rfl⟩ : syracuseStep 2385827 = 3578741) B3578741
theorem B2484145 : Blo 1056613 2484145 := bstep (se 2 (by rfl) ⟨931554, by rfl⟩ : syracuseStep 2484145 = 1863109) B1863109
theorem B1337411 : Blo 1056613 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B2681009 : Blo 1056613 2681009 := bstep (se 2 (by rfl) ⟨1005378, by rfl⟩ : syracuseStep 2681009 = 2010757) B2010757
theorem B2386097 : Blo 1056613 2386097 := bstep (se 2 (by rfl) ⟨894786, by rfl⟩ : syracuseStep 2386097 = 1789573) B1789573
theorem B2386115 : Blo 1056613 2386115 := bstep (se 1 (by rfl) ⟨1789586, by rfl⟩ : syracuseStep 2386115 = 3579173) B3579173
theorem B9038051 : Blo 1056613 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B2681059 : Blo 1056613 2681059 := bstep (se 1 (by rfl) ⟨2010794, by rfl⟩ : syracuseStep 2681059 = 4021589) B4021589
theorem B10316045 : Blo 1056613 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B2681201 : Blo 1056613 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B5368355 : Blo 1056613 5368355 := bstep (se 1 (by rfl) ⟨4026266, by rfl⟩ : syracuseStep 5368355 = 8052533) B8052533
theorem B1698403 : Blo 1056613 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B3566321 : Blo 1056613 3566321 := bstep (se 2 (by rfl) ⟨1337370, by rfl⟩ : syracuseStep 3566321 = 2674741) B2674741
theorem B1338115 : Blo 1056613 1338115 := bstep (se 1 (by rfl) ⟨1003586, by rfl⟩ : syracuseStep 1338115 = 2007173) B2007173
theorem B1338211 : Blo 1056613 1338211 := bstep (se 1 (by rfl) ⟨1003658, by rfl⟩ : syracuseStep 1338211 = 2007317) B2007317
theorem B1698659 : Blo 1056613 1698659 := bstep (se 1 (by rfl) ⟨1273994, by rfl⟩ : syracuseStep 1698659 = 2547989) B2547989
theorem B1698851 : Blo 1056613 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B19328053 : Blo 1056613 19328053 := bstep (se 5 (by rfl) ⟨906002, by rfl⟩ : syracuseStep 19328053 = 1812005) B1812005
theorem B3566861 : Blo 1056613 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B3566915 : Blo 1056613 3566915 := bstep (se 1 (by rfl) ⟨2675186, by rfl⟩ : syracuseStep 3566915 = 5350373) B5350373
theorem B6778181 : Blo 1056613 6778181 := bstep (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) B1270909
theorem B5369165 : Blo 1056613 5369165 := bstep (se 3 (by rfl) ⟨1006718, by rfl⟩ : syracuseStep 5369165 = 2013437) B2013437
theorem B2682193 : Blo 1056613 2682193 := bstep (se 2 (by rfl) ⟨1005822, by rfl⟩ : syracuseStep 2682193 = 2011645) B2011645
theorem B1338707 : Blo 1056613 1338707 := bstep (se 1 (by rfl) ⟨1004030, by rfl⟩ : syracuseStep 1338707 = 2008061) B2008061
theorem B3009905 : Blo 1056613 3009905 := bstep (se 2 (by rfl) ⟨1128714, by rfl⟩ : syracuseStep 3009905 = 2257429) B2257429
theorem B1273379 : Blo 1056613 1273379 := bstep (se 1 (by rfl) ⟨955034, by rfl⟩ : syracuseStep 1273379 = 1910069) B1910069
theorem B4025933 : Blo 1056613 4025933 := bstep (se 3 (by rfl) ⟨754862, by rfl⟩ : syracuseStep 4025933 = 1509725) B1509725
theorem B3567185 : Blo 1056613 3567185 := bstep (se 2 (by rfl) ⟨1337694, by rfl⟩ : syracuseStep 3567185 = 2675389) B2675389
theorem B2682467 : Blo 1056613 2682467 := bstep (se 1 (by rfl) ⟨2011850, by rfl⟩ : syracuseStep 2682467 = 4023701) B4023701
theorem B1273475 : Blo 1056613 1273475 := bstep (se 1 (by rfl) ⟨955106, by rfl⟩ : syracuseStep 1273475 = 1910213) B1910213
theorem B1175315 : Blo 1056613 1175315 := bstep (se 1 (by rfl) ⟨881486, by rfl⟩ : syracuseStep 1175315 = 1762973) B1762973
theorem B2682659 : Blo 1056613 2682659 := bstep (se 1 (by rfl) ⟨2011994, by rfl⟩ : syracuseStep 2682659 = 4023989) B4023989
theorem B4517795 : Blo 1056613 4517795 := bstep (se 1 (by rfl) ⟨3388346, by rfl⟩ : syracuseStep 4517795 = 6776693) B6776693
theorem B1339411 : Blo 1056613 1339411 := bstep (se 1 (by rfl) ⟨1004558, by rfl⟩ : syracuseStep 1339411 = 2009117) B2009117
theorem B2256977 : Blo 1056613 2256977 := bstep (se 2 (by rfl) ⟨846366, by rfl⟩ : syracuseStep 2256977 = 1692733) B1692733
theorem B3567725 : Blo 1056613 3567725 := bstep (se 3 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 3567725 = 1337897) B1337897
theorem B1339507 : Blo 1056613 1339507 := bstep (se 1 (by rfl) ⟨1004630, by rfl⟩ : syracuseStep 1339507 = 2009261) B2009261
theorem B3567779 : Blo 1056613 3567779 := bstep (se 1 (by rfl) ⟨2675834, by rfl⟩ : syracuseStep 3567779 = 5351669) B5351669
theorem B1208515 : Blo 1056613 1208515 := bstep (se 1 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 1208515 = 1812773) B1812773
theorem B3010861 : Blo 1056613 3010861 := bstep (se 3 (by rfl) ⟨564536, by rfl⟩ : syracuseStep 3010861 = 1129073) B1129073
theorem B13070645 : Blo 1056613 13070645 := bstep (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) B1225373
theorem B6025549 : Blo 1056613 6025549 := bstep (se 3 (by rfl) ⟨1129790, by rfl⟩ : syracuseStep 6025549 = 2259581) B2259581
theorem B4354417 : Blo 1056613 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B3568049 : Blo 1056613 3568049 := bstep (se 2 (by rfl) ⟨1338018, by rfl⟩ : syracuseStep 3568049 = 2676037) B2676037
theorem B3011089 : Blo 1056613 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B1340003 : Blo 1056613 1340003 := bstep (se 1 (by rfl) ⟨1005002, by rfl⟩ : syracuseStep 1340003 = 2010005) B2010005
theorem B1208963 : Blo 1056613 1208963 := bstep (se 1 (by rfl) ⟨906722, by rfl⟩ : syracuseStep 1208963 = 1813445) B1813445
theorem B3011249 : Blo 1056613 3011249 := bstep (se 2 (by rfl) ⟨1129218, by rfl⟩ : syracuseStep 3011249 = 2258437) B2258437
theorem B2683601 : Blo 1056613 2683601 := bstep (se 2 (by rfl) ⟨1006350, by rfl⟩ : syracuseStep 2683601 = 2012701) B2012701
theorem B10187491 : Blo 1056613 10187491 := bstep (se 1 (by rfl) ⟨7640618, by rfl⟩ : syracuseStep 10187491 = 15281237) B15281237
theorem B2683651 : Blo 1056613 2683651 := bstep (se 1 (by rfl) ⟨2012738, by rfl⟩ : syracuseStep 2683651 = 4025477) B4025477
theorem B3011363 : Blo 1056613 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B2683793 : Blo 1056613 2683793 := bstep (se 2 (by rfl) ⟨1006422, by rfl⟩ : syracuseStep 2683793 = 2012845) B2012845
theorem B3568589 : Blo 1056613 3568589 := bstep (se 3 (by rfl) ⟨669110, by rfl⟩ : syracuseStep 3568589 = 1338221) B1338221
theorem B3568643 : Blo 1056613 3568643 := bstep (se 1 (by rfl) ⟨2676482, by rfl⟩ : syracuseStep 3568643 = 5352965) B5352965
theorem B1504451 : Blo 1056613 1504451 := bstep (se 1 (by rfl) ⟨1128338, by rfl⟩ : syracuseStep 1504451 = 2256677) B2256677
theorem B3568913 : Blo 1056613 3568913 := bstep (se 2 (by rfl) ⟨1338342, by rfl⟩ : syracuseStep 3568913 = 2676685) B2676685
theorem B1504531 : Blo 1056613 1504531 := bstep (se 1 (by rfl) ⟨1128398, by rfl⟩ : syracuseStep 1504531 = 2256797) B2256797
theorem B1340707 : Blo 1056613 1340707 := bstep (se 1 (by rfl) ⟨1005530, by rfl⟩ : syracuseStep 1340707 = 2011061) B2011061
theorem B4289869 : Blo 1056613 4289869 := bstep (se 3 (by rfl) ⟨804350, by rfl⟩ : syracuseStep 4289869 = 1608701) B1608701
theorem B2258275 : Blo 1056613 2258275 := bstep (se 1 (by rfl) ⟨1693706, by rfl⟩ : syracuseStep 2258275 = 3387413) B3387413
theorem B1340803 : Blo 1056613 1340803 := bstep (se 1 (by rfl) ⟨1005602, by rfl⟩ : syracuseStep 1340803 = 2011205) B2011205
theorem B3012365 : Blo 1056613 3012365 := bstep (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) B1129637
theorem B3569453 : Blo 1056613 3569453 := bstep (se 3 (by rfl) ⟨669272, by rfl⟩ : syracuseStep 3569453 = 1338545) B1338545
theorem B1505089 : Blo 1056613 1505089 := bstep (se 2 (by rfl) ⟨564408, by rfl⟩ : syracuseStep 1505089 = 1128817) B1128817
theorem B3569507 : Blo 1056613 3569507 := bstep (se 1 (by rfl) ⟨2677130, by rfl⟩ : syracuseStep 3569507 = 5354261) B5354261
theorem B1341299 : Blo 1056613 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B3012547 : Blo 1056613 3012547 := bstep (se 1 (by rfl) ⟨2259410, by rfl⟩ : syracuseStep 3012547 = 4518821) B4518821
theorem B25786309 : Blo 1056613 25786309 := bstep (se 4 (by rfl) ⟨2417466, by rfl⟩ : syracuseStep 25786309 = 4834933) B4834933
theorem B3012707 : Blo 1056613 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B3569777 : Blo 1056613 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B6027533 : Blo 1056613 6027533 := bstep (se 3 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 6027533 = 2260325) B2260325
theorem B2324963 : Blo 1056613 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B1505795 : Blo 1056613 1505795 := bstep (se 1 (by rfl) ⟨1129346, by rfl⟩ : syracuseStep 1505795 = 2258693) B2258693
theorem B4520461 : Blo 1056613 4520461 := bstep (se 3 (by rfl) ⟨847586, by rfl⟩ : syracuseStep 4520461 = 1695173) B1695173
theorem B2259505 : Blo 1056613 2259505 := bstep (se 2 (by rfl) ⟨847314, by rfl⟩ : syracuseStep 2259505 = 1694629) B1694629
theorem B1342003 : Blo 1056613 1342003 := bstep (se 1 (by rfl) ⟨1006502, by rfl⟩ : syracuseStep 1342003 = 2013005) B2013005
theorem B3570317 : Blo 1056613 3570317 := bstep (se 3 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 3570317 = 1338869) B1338869
theorem B1342099 : Blo 1056613 1342099 := bstep (se 1 (by rfl) ⟨1006574, by rfl⟩ : syracuseStep 1342099 = 2013149) B2013149
theorem B3570371 : Blo 1056613 3570371 := bstep (se 1 (by rfl) ⟨2677778, by rfl⟩ : syracuseStep 3570371 = 5355557) B5355557
theorem B5733233 : Blo 1056613 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B3570641 : Blo 1056613 3570641 := bstep (se 2 (by rfl) ⟨1338990, by rfl⟩ : syracuseStep 3570641 = 2677981) B2677981
theorem B1506433 : Blo 1056613 1506433 := bstep (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) B1129825
theorem B3013777 : Blo 1056613 3013777 := bstep (se 2 (by rfl) ⟨1130166, by rfl⟩ : syracuseStep 3013777 = 2260333) B2260333
theorem B6028465 : Blo 1056613 6028465 := bstep (se 2 (by rfl) ⟨2260674, by rfl⟩ : syracuseStep 6028465 = 4521349) B4521349
theorem B6782129 : Blo 1056613 6782129 := bstep (se 2 (by rfl) ⟨2543298, by rfl⟩ : syracuseStep 6782129 = 5086597) B5086597
theorem B2260163 : Blo 1056613 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1506547 : Blo 1056613 1506547 := bstep (se 1 (by rfl) ⟨1129910, by rfl⟩ : syracuseStep 1506547 = 2259821) B2259821
theorem B1375507 : Blo 1056613 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B3571181 : Blo 1056613 3571181 := bstep (se 3 (by rfl) ⟨669596, by rfl⟩ : syracuseStep 3571181 = 1339193) B1339193
theorem B3571235 : Blo 1056613 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B4521521 : Blo 1056613 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B8027747 : Blo 1056613 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B3571505 : Blo 1056613 3571505 := bstep (se 2 (by rfl) ⟨1339314, by rfl⟩ : syracuseStep 3571505 = 2678629) B2678629
theorem B2981713 : Blo 1056613 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B1507339 : Blo 1056613 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B9666661 : Blo 1056613 9666661 := bstep (se 4 (by rfl) ⟨906249, by rfl⟩ : syracuseStep 9666661 = 1812499) B1812499
theorem B104562839 : Blo 1056613 104562839 := bstep (se 1 (by rfl) ⟨78422129, by rfl⟩ : syracuseStep 104562839 = 156844259) B156844259
theorem B2261171 : Blo 1056613 2261171 := bstep (se 1 (by rfl) ⟨1695878, by rfl⟩ : syracuseStep 2261171 = 3391757) B3391757
theorem B3571991 : Blo 1056613 3571991 := bstep (se 1 (by rfl) ⟨2678993, by rfl⟩ : syracuseStep 3571991 = 5357987) B5357987
theorem B1377047 : Blo 1056613 1377047 := bstep (se 1 (by rfl) ⟨1032785, by rfl⟩ : syracuseStep 1377047 = 2065571) B2065571
theorem B3572531 : Blo 1056613 3572531 := bstep (se 1 (by rfl) ⟨2679398, by rfl⟩ : syracuseStep 3572531 = 5358797) B5358797
theorem B4588481 : Blo 1056613 4588481 := bstep (se 2 (by rfl) ⟨1720680, by rfl⟩ : syracuseStep 4588481 = 3441361) B3441361
theorem B3572801 : Blo 1056613 3572801 := bstep (se 2 (by rfl) ⟨1339800, by rfl⟩ : syracuseStep 3572801 = 2679601) B2679601
theorem B4654273 : Blo 1056613 4654273 := bstep (se 2 (by rfl) ⟨1745352, by rfl⟩ : syracuseStep 4654273 = 3490705) B3490705
theorem B2262401 : Blo 1056613 2262401 := bstep (se 2 (by rfl) ⟨848400, by rfl⟩ : syracuseStep 2262401 = 1696801) B1696801
theorem B1508825 : Blo 1056613 1508825 := bstep (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) B1131619
theorem B15894091 : Blo 1056613 15894091 := bstep (se 1 (by rfl) ⟨11920568, by rfl⟩ : syracuseStep 15894091 = 23841137) B23841137
theorem B3573341 : Blo 1056613 3573341 := bstep (se 3 (by rfl) ⟨670001, by rfl⟩ : syracuseStep 3573341 = 1340003) B1340003
theorem B7636697 : Blo 1056613 7636697 := bstep (se 2 (by rfl) ⟨2863761, by rfl⟩ : syracuseStep 7636697 = 5727523) B5727523
theorem B5080907 : Blo 1056613 5080907 := bstep (se 1 (by rfl) ⟨3810680, by rfl⟩ : syracuseStep 5080907 = 7621361) B7621361
theorem B4524083 : Blo 1056613 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B4294721 : Blo 1056613 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B1509463 : Blo 1056613 1509463 := bstep (se 1 (by rfl) ⟨1132097, by rfl⟩ : syracuseStep 1509463 = 2264195) B2264195
theorem B3016921 : Blo 1056613 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B2263511 : Blo 1056613 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B3312193 : Blo 1056613 3312193 := bstep (se 2 (by rfl) ⟨1242072, by rfl⟩ : syracuseStep 3312193 = 2484145) B2484145
theorem B7637597 : Blo 1056613 7637597 := bstep (se 3 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 7637597 = 2864099) B2864099
theorem B3574475 : Blo 1056613 3574475 := bstep (se 1 (by rfl) ⟨2680856, by rfl⟩ : syracuseStep 3574475 = 5361713) B5361713
theorem B3017537 : Blo 1056613 3017537 := bstep (se 2 (by rfl) ⟨1131576, by rfl⟩ : syracuseStep 3017537 = 2263153) B2263153
theorem B3574745 : Blo 1056613 3574745 := bstep (se 2 (by rfl) ⟨1340529, by rfl⟩ : syracuseStep 3574745 = 2681059) B2681059
theorem B6786179 : Blo 1056613 6786179 := bstep (se 1 (by rfl) ⟨5089634, by rfl⟩ : syracuseStep 6786179 = 10179269) B10179269
theorem B6032657 : Blo 1056613 6032657 := bstep (se 2 (by rfl) ⟨2262246, by rfl⟩ : syracuseStep 6032657 = 4524493) B4524493
theorem B4820269 : Blo 1056613 4820269 := bstep (se 3 (by rfl) ⟨903800, by rfl⟩ : syracuseStep 4820269 = 1807601) B1807601
theorem B2264537 : Blo 1056613 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B4525571 : Blo 1056613 4525571 := bstep (se 1 (by rfl) ⟨3394178, by rfl⟩ : syracuseStep 4525571 = 6788357) B6788357
theorem B3575447 : Blo 1056613 3575447 := bstep (se 1 (by rfl) ⟨2681585, by rfl⟩ : syracuseStep 3575447 = 5363171) B5363171
theorem B8589017 : Blo 1056613 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B6033113 : Blo 1056613 6033113 := bstep (se 2 (by rfl) ⟨2262417, by rfl⟩ : syracuseStep 6033113 = 4524835) B4524835
theorem B4821067 : Blo 1056613 4821067 := bstep (se 1 (by rfl) ⟨3615800, by rfl⟩ : syracuseStep 4821067 = 7231601) B7231601
theorem B13570199 : Blo 1056613 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B3575987 : Blo 1056613 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B1904843 : Blo 1056613 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B9671005 : Blo 1056613 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B3576257 : Blo 1056613 3576257 := bstep (se 2 (by rfl) ⟨1341096, by rfl⟩ : syracuseStep 3576257 = 2682193) B2682193
theorem B3019609 : Blo 1056613 3019609 := bstep (se 2 (by rfl) ⟨1132353, by rfl⟩ : syracuseStep 3019609 = 2264707) B2264707
theorem B27497393 : Blo 1056613 27497393 := bstep (se 2 (by rfl) ⟨10311522, by rfl⟩ : syracuseStep 27497393 = 20623045) B20623045
theorem B3576797 : Blo 1056613 3576797 := bstep (se 3 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 3576797 = 1341299) B1341299
theorem B6427799 : Blo 1056613 6427799 := bstep (se 1 (by rfl) ⟨4820849, by rfl⟩ : syracuseStep 6427799 = 9641699) B9641699
theorem B3019997 : Blo 1056613 3019997 := bstep (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) B1132499
theorem B1611353 : Blo 1056613 1611353 := bstep (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) B1208515
theorem B1808011 : Blo 1056613 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B4527809 : Blo 1056613 4527809 := bstep (se 2 (by rfl) ⟨1697928, by rfl⟩ : syracuseStep 4527809 = 3395857) B3395857
theorem B8034065 : Blo 1056613 8034065 := bstep (se 2 (by rfl) ⟨3012774, by rfl⟩ : syracuseStep 8034065 = 6025549) B6025549
theorem B2856779 : Blo 1056613 2856779 := bstep (se 1 (by rfl) ⟨2142584, by rfl⟩ : syracuseStep 2856779 = 4285169) B4285169
theorem B1906753 : Blo 1056613 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B3577931 : Blo 1056613 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B3676481 : Blo 1056613 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B3578201 : Blo 1056613 3578201 := bstep (se 2 (by rfl) ⟨1341825, by rfl⟩ : syracuseStep 3578201 = 2683651) B2683651
theorem B10164811 : Blo 1056613 10164811 := bstep (se 1 (by rfl) ⟨7623608, by rfl⟩ : syracuseStep 10164811 = 15247217) B15247217
theorem B15243869 : Blo 1056613 15243869 := bstep (se 3 (by rfl) ⟨2858225, by rfl⟩ : syracuseStep 15243869 = 5716451) B5716451
theorem B6199901 : Blo 1056613 6199901 := bstep (se 3 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 6199901 = 2324963) B2324963
theorem B1448651 : Blo 1056613 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B2857817 : Blo 1056613 2857817 := bstep (se 2 (by rfl) ⟨1071681, by rfl⟩ : syracuseStep 2857817 = 2143363) B2143363
theorem B3578903 : Blo 1056613 3578903 := bstep (se 1 (by rfl) ⟨2684177, by rfl⟩ : syracuseStep 3578903 = 5368355) B5368355
theorem B2006041 : Blo 1056613 2006041 := bstep (se 2 (by rfl) ⟨752265, by rfl⟩ : syracuseStep 2006041 = 1504531) B1504531
theorem B4529483 : Blo 1056613 4529483 := bstep (se 1 (by rfl) ⟨3397112, by rfl⟩ : syracuseStep 4529483 = 6794225) B6794225
theorem B4300121 : Blo 1056613 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B3579443 : Blo 1056613 3579443 := bstep (se 1 (by rfl) ⟨2684582, by rfl⟩ : syracuseStep 3579443 = 5369165) B5369165
theorem B2006603 : Blo 1056613 2006603 := bstep (se 1 (by rfl) ⟨1504952, by rfl⟩ : syracuseStep 2006603 = 3009905) B3009905
theorem B2006785 : Blo 1056613 2006785 := bstep (se 2 (by rfl) ⟨752544, by rfl⟩ : syracuseStep 2006785 = 1505089) B1505089
theorem B1810201 : Blo 1056613 1810201 := bstep (se 2 (by rfl) ⟨678825, by rfl⟩ : syracuseStep 1810201 = 1357651) B1357651
theorem B1056619 : Blo 1056613 1056619 := bstep (se 1 (by rfl) ⟨792464, by rfl⟩ : syracuseStep 1056619 = 1584929) B1584929
theorem B1056631 : Blo 1056613 1056631 := bstep (se 1 (by rfl) ⟨792473, by rfl⟩ : syracuseStep 1056631 = 1584947) B1584947
theorem B1056651 : Blo 1056613 1056651 := bstep (se 1 (by rfl) ⟨792488, by rfl⟩ : syracuseStep 1056651 = 1584977) B1584977
theorem B1056663 : Blo 1056613 1056663 := bstep (se 1 (by rfl) ⟨792497, by rfl⟩ : syracuseStep 1056663 = 1584995) B1584995
theorem B1056683 : Blo 1056613 1056683 := bstep (se 1 (by rfl) ⟨792512, by rfl⟩ : syracuseStep 1056683 = 1585025) B1585025
theorem B34381745 : Blo 1056613 34381745 := bstep (se 2 (by rfl) ⟨12893154, by rfl⟩ : syracuseStep 34381745 = 25786309) B25786309
theorem B1056695 : Blo 1056613 1056695 := bstep (se 1 (by rfl) ⟨792521, by rfl⟩ : syracuseStep 1056695 = 1585043) B1585043
theorem B1056715 : Blo 1056613 1056715 := bstep (se 1 (by rfl) ⟨792536, by rfl⟩ : syracuseStep 1056715 = 1585073) B1585073
theorem B1056727 : Blo 1056613 1056727 := bstep (se 1 (by rfl) ⟨792545, by rfl⟩ : syracuseStep 1056727 = 1585091) B1585091
theorem B1056747 : Blo 1056613 1056747 := bstep (se 1 (by rfl) ⟨792560, by rfl⟩ : syracuseStep 1056747 = 1585121) B1585121
theorem B1056759 : Blo 1056613 1056759 := bstep (se 1 (by rfl) ⟨792569, by rfl⟩ : syracuseStep 1056759 = 1585139) B1585139
theorem B1056779 : Blo 1056613 1056779 := bstep (se 1 (by rfl) ⟨792584, by rfl⟩ : syracuseStep 1056779 = 1585169) B1585169
theorem B1056791 : Blo 1056613 1056791 := bstep (se 1 (by rfl) ⟨792593, by rfl⟩ : syracuseStep 1056791 = 1585187) B1585187
theorem B1056811 : Blo 1056613 1056811 := bstep (se 1 (by rfl) ⟨792608, by rfl⟩ : syracuseStep 1056811 = 1585217) B1585217
theorem B1056823 : Blo 1056613 1056823 := bstep (se 1 (by rfl) ⟨792617, by rfl⟩ : syracuseStep 1056823 = 1585235) B1585235
theorem B1056843 : Blo 1056613 1056843 := bstep (se 1 (by rfl) ⟨792632, by rfl⟩ : syracuseStep 1056843 = 1585265) B1585265
theorem B9052235 : Blo 1056613 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B1056855 : Blo 1056613 1056855 := bstep (se 1 (by rfl) ⟨792641, by rfl⟩ : syracuseStep 1056855 = 1585283) B1585283
theorem B4530269 : Blo 1056613 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B1056875 : Blo 1056613 1056875 := bstep (se 1 (by rfl) ⟨792656, by rfl⟩ : syracuseStep 1056875 = 1585313) B1585313
theorem B1056887 : Blo 1056613 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B1056907 : Blo 1056613 1056907 := bstep (se 1 (by rfl) ⟨792680, by rfl⟩ : syracuseStep 1056907 = 1585361) B1585361
theorem B1056919 : Blo 1056613 1056919 := bstep (se 1 (by rfl) ⟨792689, by rfl⟩ : syracuseStep 1056919 = 1585379) B1585379
theorem B1056939 : Blo 1056613 1056939 := bstep (se 1 (by rfl) ⟨792704, by rfl⟩ : syracuseStep 1056939 = 1585409) B1585409
theorem B1056951 : Blo 1056613 1056951 := bstep (se 1 (by rfl) ⟨792713, by rfl⟩ : syracuseStep 1056951 = 1585427) B1585427
theorem B1056971 : Blo 1056613 1056971 := bstep (se 1 (by rfl) ⟨792728, by rfl⟩ : syracuseStep 1056971 = 1585457) B1585457
theorem B1056983 : Blo 1056613 1056983 := bstep (se 1 (by rfl) ⟨792737, by rfl⟩ : syracuseStep 1056983 = 1585475) B1585475
theorem B1057003 : Blo 1056613 1057003 := bstep (se 1 (by rfl) ⟨792752, by rfl⟩ : syracuseStep 1057003 = 1585505) B1585505
theorem B1057015 : Blo 1056613 1057015 := bstep (se 1 (by rfl) ⟨792761, by rfl⟩ : syracuseStep 1057015 = 1585523) B1585523
theorem B1057035 : Blo 1056613 1057035 := bstep (se 1 (by rfl) ⟨792776, by rfl⟩ : syracuseStep 1057035 = 1585553) B1585553
theorem B1057047 : Blo 1056613 1057047 := bstep (se 1 (by rfl) ⟨792785, by rfl⟩ : syracuseStep 1057047 = 1585571) B1585571
theorem B1057067 : Blo 1056613 1057067 := bstep (se 1 (by rfl) ⟨792800, by rfl⟩ : syracuseStep 1057067 = 1585601) B1585601
theorem B1057079 : Blo 1056613 1057079 := bstep (se 1 (by rfl) ⟨792809, by rfl⟩ : syracuseStep 1057079 = 1585619) B1585619
theorem B1057099 : Blo 1056613 1057099 := bstep (se 1 (by rfl) ⟨792824, by rfl⟩ : syracuseStep 1057099 = 1585649) B1585649
theorem B1057111 : Blo 1056613 1057111 := bstep (se 1 (by rfl) ⟨792833, by rfl⟩ : syracuseStep 1057111 = 1585667) B1585667
theorem B4825433 : Blo 1056613 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B5349725 : Blo 1056613 5349725 := bstep (se 3 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 5349725 = 2006147) B2006147
theorem B1057131 : Blo 1056613 1057131 := bstep (se 1 (by rfl) ⟨792848, by rfl⟩ : syracuseStep 1057131 = 1585697) B1585697
theorem B1057143 : Blo 1056613 1057143 := bstep (se 1 (by rfl) ⟨792857, by rfl⟩ : syracuseStep 1057143 = 1585715) B1585715
theorem B1057163 : Blo 1056613 1057163 := bstep (se 1 (by rfl) ⟨792872, by rfl⟩ : syracuseStep 1057163 = 1585745) B1585745
theorem B1057175 : Blo 1056613 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B1057195 : Blo 1056613 1057195 := bstep (se 1 (by rfl) ⟨792896, by rfl⟩ : syracuseStep 1057195 = 1585793) B1585793
theorem B1057207 : Blo 1056613 1057207 := bstep (se 1 (by rfl) ⟨792905, by rfl⟩ : syracuseStep 1057207 = 1585811) B1585811
theorem B1057227 : Blo 1056613 1057227 := bstep (se 1 (by rfl) ⟨792920, by rfl⟩ : syracuseStep 1057227 = 1585841) B1585841
theorem B2007499 : Blo 1056613 2007499 := bstep (se 1 (by rfl) ⟨1505624, by rfl⟩ : syracuseStep 2007499 = 3011249) B3011249
theorem B1057239 : Blo 1056613 1057239 := bstep (se 1 (by rfl) ⟨792929, by rfl⟩ : syracuseStep 1057239 = 1585859) B1585859
theorem B1057259 : Blo 1056613 1057259 := bstep (se 1 (by rfl) ⟨792944, by rfl⟩ : syracuseStep 1057259 = 1585889) B1585889
theorem B1057271 : Blo 1056613 1057271 := bstep (se 1 (by rfl) ⟨792953, by rfl⟩ : syracuseStep 1057271 = 1585907) B1585907
theorem B1057291 : Blo 1056613 1057291 := bstep (se 1 (by rfl) ⟨792968, by rfl⟩ : syracuseStep 1057291 = 1585937) B1585937
theorem B1057303 : Blo 1056613 1057303 := bstep (se 1 (by rfl) ⟨792977, by rfl⟩ : syracuseStep 1057303 = 1585955) B1585955
theorem B2007575 : Blo 1056613 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B1057323 : Blo 1056613 1057323 := bstep (se 1 (by rfl) ⟨792992, by rfl⟩ : syracuseStep 1057323 = 1585985) B1585985
theorem B1057335 : Blo 1056613 1057335 := bstep (se 1 (by rfl) ⟨793001, by rfl⟩ : syracuseStep 1057335 = 1586003) B1586003
theorem B1057355 : Blo 1056613 1057355 := bstep (se 1 (by rfl) ⟨793016, by rfl⟩ : syracuseStep 1057355 = 1586033) B1586033
theorem B1057367 : Blo 1056613 1057367 := bstep (se 1 (by rfl) ⟨793025, by rfl⟩ : syracuseStep 1057367 = 1586051) B1586051
theorem B1057387 : Blo 1056613 1057387 := bstep (se 1 (by rfl) ⟨793040, by rfl⟩ : syracuseStep 1057387 = 1586081) B1586081
theorem B1057399 : Blo 1056613 1057399 := bstep (se 1 (by rfl) ⟨793049, by rfl⟩ : syracuseStep 1057399 = 1586099) B1586099
theorem B1057419 : Blo 1056613 1057419 := bstep (se 1 (by rfl) ⟨793064, by rfl⟩ : syracuseStep 1057419 = 1586129) B1586129
theorem B1057431 : Blo 1056613 1057431 := bstep (se 1 (by rfl) ⟨793073, by rfl⟩ : syracuseStep 1057431 = 1586147) B1586147
theorem B1057451 : Blo 1056613 1057451 := bstep (se 1 (by rfl) ⟨793088, by rfl⟩ : syracuseStep 1057451 = 1586177) B1586177
theorem B1057463 : Blo 1056613 1057463 := bstep (se 1 (by rfl) ⟨793097, by rfl⟩ : syracuseStep 1057463 = 1586195) B1586195
theorem B1057483 : Blo 1056613 1057483 := bstep (se 1 (by rfl) ⟨793112, by rfl⟩ : syracuseStep 1057483 = 1586225) B1586225
theorem B1057495 : Blo 1056613 1057495 := bstep (se 1 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 1057495 = 1586243) B1586243
theorem B1057515 : Blo 1056613 1057515 := bstep (se 1 (by rfl) ⟨793136, by rfl⟩ : syracuseStep 1057515 = 1586273) B1586273
theorem B1057527 : Blo 1056613 1057527 := bstep (se 1 (by rfl) ⟨793145, by rfl⟩ : syracuseStep 1057527 = 1586291) B1586291
theorem B1057547 : Blo 1056613 1057547 := bstep (se 1 (by rfl) ⟨793160, by rfl⟩ : syracuseStep 1057547 = 1586321) B1586321
theorem B1057559 : Blo 1056613 1057559 := bstep (se 1 (by rfl) ⟨793169, by rfl⟩ : syracuseStep 1057559 = 1586339) B1586339
theorem B1057579 : Blo 1056613 1057579 := bstep (se 1 (by rfl) ⟨793184, by rfl⟩ : syracuseStep 1057579 = 1586369) B1586369
theorem B1057591 : Blo 1056613 1057591 := bstep (se 1 (by rfl) ⟨793193, by rfl⟩ : syracuseStep 1057591 = 1586387) B1586387
theorem B1057611 : Blo 1056613 1057611 := bstep (se 1 (by rfl) ⟨793208, by rfl⟩ : syracuseStep 1057611 = 1586417) B1586417
theorem B1057623 : Blo 1056613 1057623 := bstep (se 1 (by rfl) ⟨793217, by rfl⟩ : syracuseStep 1057623 = 1586435) B1586435
theorem B1188715 : Blo 1056613 1188715 := bstep (se 1 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 1188715 = 1783073) B1783073
theorem B1057643 : Blo 1056613 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B1057655 : Blo 1056613 1057655 := bstep (se 1 (by rfl) ⟨793241, by rfl⟩ : syracuseStep 1057655 = 1586483) B1586483
theorem B1057675 : Blo 1056613 1057675 := bstep (se 1 (by rfl) ⟨793256, by rfl⟩ : syracuseStep 1057675 = 1586513) B1586513
theorem B1057687 : Blo 1056613 1057687 := bstep (se 1 (by rfl) ⟨793265, by rfl⟩ : syracuseStep 1057687 = 1586531) B1586531
theorem B1057707 : Blo 1056613 1057707 := bstep (se 1 (by rfl) ⟨793280, by rfl⟩ : syracuseStep 1057707 = 1586561) B1586561
theorem B1057719 : Blo 1056613 1057719 := bstep (se 1 (by rfl) ⟨793289, by rfl⟩ : syracuseStep 1057719 = 1586579) B1586579
theorem B1057739 : Blo 1056613 1057739 := bstep (se 1 (by rfl) ⟨793304, by rfl⟩ : syracuseStep 1057739 = 1586609) B1586609
theorem B2040779 : Blo 1056613 2040779 := bstep (se 1 (by rfl) ⟨1530584, by rfl⟩ : syracuseStep 2040779 = 3061169) B3061169
theorem B1188823 : Blo 1056613 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B1057751 : Blo 1056613 1057751 := bstep (se 1 (by rfl) ⟨793313, by rfl⟩ : syracuseStep 1057751 = 1586627) B1586627
theorem B6038489 : Blo 1056613 6038489 := bstep (se 2 (by rfl) ⟨2264433, by rfl⟩ : syracuseStep 6038489 = 4528867) B4528867
theorem B1057771 : Blo 1056613 1057771 := bstep (se 1 (by rfl) ⟨793328, by rfl⟩ : syracuseStep 1057771 = 1586657) B1586657
theorem B1057783 : Blo 1056613 1057783 := bstep (se 1 (by rfl) ⟨793337, by rfl⟩ : syracuseStep 1057783 = 1586675) B1586675
theorem B1057803 : Blo 1056613 1057803 := bstep (se 1 (by rfl) ⟨793352, by rfl⟩ : syracuseStep 1057803 = 1586705) B1586705
theorem B1057815 : Blo 1056613 1057815 := bstep (se 1 (by rfl) ⟨793361, by rfl⟩ : syracuseStep 1057815 = 1586723) B1586723
theorem B1057835 : Blo 1056613 1057835 := bstep (se 1 (by rfl) ⟨793376, by rfl⟩ : syracuseStep 1057835 = 1586753) B1586753
theorem B1057847 : Blo 1056613 1057847 := bstep (se 1 (by rfl) ⟨793385, by rfl⟩ : syracuseStep 1057847 = 1586771) B1586771
theorem B1057867 : Blo 1056613 1057867 := bstep (se 1 (by rfl) ⟨793400, by rfl⟩ : syracuseStep 1057867 = 1586801) B1586801
theorem B3220555 : Blo 1056613 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B1057879 : Blo 1056613 1057879 := bstep (se 1 (by rfl) ⟨793409, by rfl⟩ : syracuseStep 1057879 = 1586819) B1586819
theorem B1057899 : Blo 1056613 1057899 := bstep (se 1 (by rfl) ⟨793424, by rfl⟩ : syracuseStep 1057899 = 1586849) B1586849
theorem B1057911 : Blo 1056613 1057911 := bstep (se 1 (by rfl) ⟨793433, by rfl⟩ : syracuseStep 1057911 = 1586867) B1586867
theorem B1189003 : Blo 1056613 1189003 := bstep (se 1 (by rfl) ⟨891752, by rfl⟩ : syracuseStep 1189003 = 1783505) B1783505
theorem B1057931 : Blo 1056613 1057931 := bstep (se 1 (by rfl) ⟨793448, by rfl⟩ : syracuseStep 1057931 = 1586897) B1586897
theorem B3810449 : Blo 1056613 3810449 := bstep (se 2 (by rfl) ⟨1428918, by rfl⟩ : syracuseStep 3810449 = 2857837) B2857837
theorem B1057943 : Blo 1056613 1057943 := bstep (se 1 (by rfl) ⟨793457, by rfl⟩ : syracuseStep 1057943 = 1586915) B1586915
theorem B1057963 : Blo 1056613 1057963 := bstep (se 1 (by rfl) ⟨793472, by rfl⟩ : syracuseStep 1057963 = 1586945) B1586945
theorem B2008243 : Blo 1056613 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B1057975 : Blo 1056613 1057975 := bstep (se 1 (by rfl) ⟨793481, by rfl⟩ : syracuseStep 1057975 = 1586963) B1586963
theorem B4826305 : Blo 1056613 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1057995 : Blo 1056613 1057995 := bstep (se 1 (by rfl) ⟨793496, by rfl⟩ : syracuseStep 1057995 = 1586993) B1586993
theorem B1058007 : Blo 1056613 1058007 := bstep (se 1 (by rfl) ⟨793505, by rfl⟩ : syracuseStep 1058007 = 1587011) B1587011
theorem B1058027 : Blo 1056613 1058027 := bstep (se 1 (by rfl) ⟨793520, by rfl⟩ : syracuseStep 1058027 = 1587041) B1587041
theorem B1189111 : Blo 1056613 1189111 := bstep (se 1 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 1189111 = 1783667) B1783667
theorem B1058039 : Blo 1056613 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B1058059 : Blo 1056613 1058059 := bstep (se 1 (by rfl) ⟨793544, by rfl⟩ : syracuseStep 1058059 = 1587089) B1587089
theorem B1058071 : Blo 1056613 1058071 := bstep (se 1 (by rfl) ⟨793553, by rfl⟩ : syracuseStep 1058071 = 1587107) B1587107
theorem B1058091 : Blo 1056613 1058091 := bstep (se 1 (by rfl) ⟨793568, by rfl⟩ : syracuseStep 1058091 = 1587137) B1587137
theorem B5088557 : Blo 1056613 5088557 := bstep (se 3 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 5088557 = 1908209) B1908209
theorem B1058103 : Blo 1056613 1058103 := bstep (se 1 (by rfl) ⟨793577, by rfl⟩ : syracuseStep 1058103 = 1587155) B1587155
theorem B1058123 : Blo 1056613 1058123 := bstep (se 1 (by rfl) ⟨793592, by rfl⟩ : syracuseStep 1058123 = 1587185) B1587185
theorem B1058135 : Blo 1056613 1058135 := bstep (se 1 (by rfl) ⟨793601, by rfl⟩ : syracuseStep 1058135 = 1587203) B1587203
theorem B1058155 : Blo 1056613 1058155 := bstep (se 1 (by rfl) ⟨793616, by rfl⟩ : syracuseStep 1058155 = 1587233) B1587233
theorem B1058167 : Blo 1056613 1058167 := bstep (se 1 (by rfl) ⟨793625, by rfl⟩ : syracuseStep 1058167 = 1587251) B1587251
theorem B1058187 : Blo 1056613 1058187 := bstep (se 1 (by rfl) ⟨793640, by rfl⟩ : syracuseStep 1058187 = 1587281) B1587281
theorem B2008471 : Blo 1056613 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B1058199 : Blo 1056613 1058199 := bstep (se 1 (by rfl) ⟨793649, by rfl⟩ : syracuseStep 1058199 = 1587299) B1587299
theorem B1189291 : Blo 1056613 1189291 := bstep (se 1 (by rfl) ⟨891968, by rfl⟩ : syracuseStep 1189291 = 1783937) B1783937
theorem B1058219 : Blo 1056613 1058219 := bstep (se 1 (by rfl) ⟨793664, by rfl⟩ : syracuseStep 1058219 = 1587329) B1587329
theorem B1058231 : Blo 1056613 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B1058251 : Blo 1056613 1058251 := bstep (se 1 (by rfl) ⟨793688, by rfl⟩ : syracuseStep 1058251 = 1587377) B1587377
theorem B1058263 : Blo 1056613 1058263 := bstep (se 1 (by rfl) ⟨793697, by rfl⟩ : syracuseStep 1058263 = 1587395) B1587395
theorem B1058283 : Blo 1056613 1058283 := bstep (se 1 (by rfl) ⟨793712, by rfl⟩ : syracuseStep 1058283 = 1587425) B1587425
theorem B1058295 : Blo 1056613 1058295 := bstep (se 1 (by rfl) ⟨793721, by rfl⟩ : syracuseStep 1058295 = 1587443) B1587443
theorem B2008577 : Blo 1056613 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B1058315 : Blo 1056613 1058315 := bstep (se 1 (by rfl) ⟨793736, by rfl⟩ : syracuseStep 1058315 = 1587473) B1587473
theorem B1189399 : Blo 1056613 1189399 := bstep (se 1 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 1189399 = 1784099) B1784099
theorem B1058327 : Blo 1056613 1058327 := bstep (se 1 (by rfl) ⟨793745, by rfl⟩ : syracuseStep 1058327 = 1587491) B1587491
theorem B1058347 : Blo 1056613 1058347 := bstep (se 1 (by rfl) ⟨793760, by rfl⟩ : syracuseStep 1058347 = 1587521) B1587521
theorem B1058359 : Blo 1056613 1058359 := bstep (se 1 (by rfl) ⟨793769, by rfl⟩ : syracuseStep 1058359 = 1587539) B1587539
theorem B8037953 : Blo 1056613 8037953 := bstep (se 2 (by rfl) ⟨3014232, by rfl⟩ : syracuseStep 8037953 = 6028465) B6028465
theorem B1058379 : Blo 1056613 1058379 := bstep (se 1 (by rfl) ⟨793784, by rfl⟩ : syracuseStep 1058379 = 1587569) B1587569
theorem B1058391 : Blo 1056613 1058391 := bstep (se 1 (by rfl) ⟨793793, by rfl⟩ : syracuseStep 1058391 = 1587587) B1587587
theorem B1058411 : Blo 1056613 1058411 := bstep (se 1 (by rfl) ⟨793808, by rfl⟩ : syracuseStep 1058411 = 1587617) B1587617
theorem B1058423 : Blo 1056613 1058423 := bstep (se 1 (by rfl) ⟨793817, by rfl⟩ : syracuseStep 1058423 = 1587635) B1587635
theorem B1058443 : Blo 1056613 1058443 := bstep (se 1 (by rfl) ⟨793832, by rfl⟩ : syracuseStep 1058443 = 1587665) B1587665
theorem B1058455 : Blo 1056613 1058455 := bstep (se 1 (by rfl) ⟨793841, by rfl⟩ : syracuseStep 1058455 = 1587683) B1587683
theorem B2008729 : Blo 1056613 2008729 := bstep (se 2 (by rfl) ⟨753273, by rfl⟩ : syracuseStep 2008729 = 1506547) B1506547
theorem B1058475 : Blo 1056613 1058475 := bstep (se 1 (by rfl) ⟨793856, by rfl⟩ : syracuseStep 1058475 = 1587713) B1587713
theorem B1058487 : Blo 1056613 1058487 := bstep (se 1 (by rfl) ⟨793865, by rfl⟩ : syracuseStep 1058487 = 1587731) B1587731
theorem B1189579 : Blo 1056613 1189579 := bstep (se 1 (by rfl) ⟨892184, by rfl⟩ : syracuseStep 1189579 = 1784369) B1784369
theorem B1058507 : Blo 1056613 1058507 := bstep (se 1 (by rfl) ⟨793880, by rfl⟩ : syracuseStep 1058507 = 1587761) B1587761
theorem B12035789 : Blo 1056613 12035789 := bstep (se 3 (by rfl) ⟨2256710, by rfl⟩ : syracuseStep 12035789 = 4513421) B4513421
theorem B1058519 : Blo 1056613 1058519 := bstep (se 1 (by rfl) ⟨793889, by rfl⟩ : syracuseStep 1058519 = 1587779) B1587779
theorem B1058539 : Blo 1056613 1058539 := bstep (se 1 (by rfl) ⟨793904, by rfl⟩ : syracuseStep 1058539 = 1587809) B1587809
theorem B1058551 : Blo 1056613 1058551 := bstep (se 1 (by rfl) ⟨793913, by rfl⟩ : syracuseStep 1058551 = 1587827) B1587827
theorem B1058571 : Blo 1056613 1058571 := bstep (se 1 (by rfl) ⟨793928, by rfl⟩ : syracuseStep 1058571 = 1587857) B1587857
theorem B1058583 : Blo 1056613 1058583 := bstep (se 1 (by rfl) ⟨793937, by rfl⟩ : syracuseStep 1058583 = 1587875) B1587875
theorem B1058603 : Blo 1056613 1058603 := bstep (se 1 (by rfl) ⟨793952, by rfl⟩ : syracuseStep 1058603 = 1587905) B1587905
theorem B1189687 : Blo 1056613 1189687 := bstep (se 1 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 1189687 = 1784531) B1784531
theorem B1058615 : Blo 1056613 1058615 := bstep (se 1 (by rfl) ⟨793961, by rfl⟩ : syracuseStep 1058615 = 1587923) B1587923
theorem B1058635 : Blo 1056613 1058635 := bstep (se 1 (by rfl) ⟨793976, by rfl⟩ : syracuseStep 1058635 = 1587953) B1587953
theorem B1058647 : Blo 1056613 1058647 := bstep (se 1 (by rfl) ⟨793985, by rfl⟩ : syracuseStep 1058647 = 1587971) B1587971
theorem B12887909 : Blo 1056613 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B1058667 : Blo 1056613 1058667 := bstep (se 1 (by rfl) ⟨794000, by rfl⟩ : syracuseStep 1058667 = 1588001) B1588001
theorem B1058679 : Blo 1056613 1058679 := bstep (se 1 (by rfl) ⟨794009, by rfl⟩ : syracuseStep 1058679 = 1588019) B1588019
theorem B1058699 : Blo 1056613 1058699 := bstep (se 1 (by rfl) ⟨794024, by rfl⟩ : syracuseStep 1058699 = 1588049) B1588049
theorem B1058711 : Blo 1056613 1058711 := bstep (se 1 (by rfl) ⟨794033, by rfl⟩ : syracuseStep 1058711 = 1588067) B1588067
theorem B1058731 : Blo 1056613 1058731 := bstep (se 1 (by rfl) ⟨794048, by rfl⟩ : syracuseStep 1058731 = 1588097) B1588097
theorem B1058743 : Blo 1056613 1058743 := bstep (se 1 (by rfl) ⟨794057, by rfl⟩ : syracuseStep 1058743 = 1588115) B1588115
theorem B1058763 : Blo 1056613 1058763 := bstep (se 1 (by rfl) ⟨794072, by rfl⟩ : syracuseStep 1058763 = 1588145) B1588145
theorem B1058775 : Blo 1056613 1058775 := bstep (se 1 (by rfl) ⟨794081, by rfl⟩ : syracuseStep 1058775 = 1588163) B1588163
theorem B1189867 : Blo 1056613 1189867 := bstep (se 1 (by rfl) ⟨892400, by rfl⟩ : syracuseStep 1189867 = 1784801) B1784801
theorem B1058795 : Blo 1056613 1058795 := bstep (se 1 (by rfl) ⟨794096, by rfl⟩ : syracuseStep 1058795 = 1588193) B1588193
theorem B1058807 : Blo 1056613 1058807 := bstep (se 1 (by rfl) ⟨794105, by rfl⟩ : syracuseStep 1058807 = 1588211) B1588211
theorem B1058827 : Blo 1056613 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B1058839 : Blo 1056613 1058839 := bstep (se 1 (by rfl) ⟨794129, by rfl⟩ : syracuseStep 1058839 = 1588259) B1588259
theorem B1058859 : Blo 1056613 1058859 := bstep (se 1 (by rfl) ⟨794144, by rfl⟩ : syracuseStep 1058859 = 1588289) B1588289
theorem B1058871 : Blo 1056613 1058871 := bstep (se 1 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 1058871 = 1588307) B1588307
theorem B1058891 : Blo 1056613 1058891 := bstep (se 1 (by rfl) ⟨794168, by rfl⟩ : syracuseStep 1058891 = 1588337) B1588337
theorem B1189975 : Blo 1056613 1189975 := bstep (se 1 (by rfl) ⟨892481, by rfl⟩ : syracuseStep 1189975 = 1784963) B1784963
theorem B1058903 : Blo 1056613 1058903 := bstep (se 1 (by rfl) ⟨794177, by rfl⟩ : syracuseStep 1058903 = 1588355) B1588355
theorem B1058923 : Blo 1056613 1058923 := bstep (se 1 (by rfl) ⟨794192, by rfl⟩ : syracuseStep 1058923 = 1588385) B1588385
theorem B1058935 : Blo 1056613 1058935 := bstep (se 1 (by rfl) ⟨794201, by rfl⟩ : syracuseStep 1058935 = 1588403) B1588403
theorem B1058955 : Blo 1056613 1058955 := bstep (se 1 (by rfl) ⟨794216, by rfl⟩ : syracuseStep 1058955 = 1588433) B1588433
theorem B1058967 : Blo 1056613 1058967 := bstep (se 1 (by rfl) ⟨794225, by rfl⟩ : syracuseStep 1058967 = 1588451) B1588451
theorem B1058987 : Blo 1056613 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B1058999 : Blo 1056613 1058999 := bstep (se 1 (by rfl) ⟨794249, by rfl⟩ : syracuseStep 1058999 = 1588499) B1588499
theorem B3811531 : Blo 1056613 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B1059019 : Blo 1056613 1059019 := bstep (se 1 (by rfl) ⟨794264, by rfl⟩ : syracuseStep 1059019 = 1588529) B1588529
theorem B1059031 : Blo 1056613 1059031 := bstep (se 1 (by rfl) ⟨794273, by rfl⟩ : syracuseStep 1059031 = 1588547) B1588547
theorem B1059051 : Blo 1056613 1059051 := bstep (se 1 (by rfl) ⟨794288, by rfl⟩ : syracuseStep 1059051 = 1588577) B1588577
theorem B1059063 : Blo 1056613 1059063 := bstep (se 1 (by rfl) ⟨794297, by rfl⟩ : syracuseStep 1059063 = 1588595) B1588595
theorem B1190155 : Blo 1056613 1190155 := bstep (se 1 (by rfl) ⟨892616, by rfl⟩ : syracuseStep 1190155 = 1785233) B1785233
theorem B1059083 : Blo 1056613 1059083 := bstep (se 1 (by rfl) ⟨794312, by rfl⟩ : syracuseStep 1059083 = 1588625) B1588625
theorem B1059095 : Blo 1056613 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B1059115 : Blo 1056613 1059115 := bstep (se 1 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 1059115 = 1588673) B1588673
theorem B1059127 : Blo 1056613 1059127 := bstep (se 1 (by rfl) ⟨794345, by rfl⟩ : syracuseStep 1059127 = 1588691) B1588691
theorem B1059147 : Blo 1056613 1059147 := bstep (se 1 (by rfl) ⟨794360, by rfl⟩ : syracuseStep 1059147 = 1588721) B1588721
theorem B1059159 : Blo 1056613 1059159 := bstep (se 1 (by rfl) ⟨794369, by rfl⟩ : syracuseStep 1059159 = 1588739) B1588739
theorem B1059179 : Blo 1056613 1059179 := bstep (se 1 (by rfl) ⟨794384, by rfl⟩ : syracuseStep 1059179 = 1588769) B1588769
theorem B1190263 : Blo 1056613 1190263 := bstep (se 1 (by rfl) ⟨892697, by rfl⟩ : syracuseStep 1190263 = 1785395) B1785395
theorem B1059191 : Blo 1056613 1059191 := bstep (se 1 (by rfl) ⟨794393, by rfl⟩ : syracuseStep 1059191 = 1588787) B1588787
theorem B1059211 : Blo 1056613 1059211 := bstep (se 1 (by rfl) ⟨794408, by rfl⟩ : syracuseStep 1059211 = 1588817) B1588817
theorem B5351831 : Blo 1056613 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B1059223 : Blo 1056613 1059223 := bstep (se 1 (by rfl) ⟨794417, by rfl⟩ : syracuseStep 1059223 = 1588835) B1588835
theorem B1059243 : Blo 1056613 1059243 := bstep (se 1 (by rfl) ⟨794432, by rfl⟩ : syracuseStep 1059243 = 1588865) B1588865
theorem B1059255 : Blo 1056613 1059255 := bstep (se 1 (by rfl) ⟨794441, by rfl⟩ : syracuseStep 1059255 = 1588883) B1588883
theorem B3975617 : Blo 1056613 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B1059275 : Blo 1056613 1059275 := bstep (se 1 (by rfl) ⟨794456, by rfl⟩ : syracuseStep 1059275 = 1588913) B1588913
theorem B1059287 : Blo 1056613 1059287 := bstep (se 1 (by rfl) ⟨794465, by rfl⟩ : syracuseStep 1059287 = 1588931) B1588931
theorem B1059307 : Blo 1056613 1059307 := bstep (se 1 (by rfl) ⟨794480, by rfl⟩ : syracuseStep 1059307 = 1588961) B1588961
theorem B1059319 : Blo 1056613 1059319 := bstep (se 1 (by rfl) ⟨794489, by rfl⟩ : syracuseStep 1059319 = 1588979) B1588979
theorem B1059339 : Blo 1056613 1059339 := bstep (se 1 (by rfl) ⟨794504, by rfl⟩ : syracuseStep 1059339 = 1589009) B1589009
theorem B1059351 : Blo 1056613 1059351 := bstep (se 1 (by rfl) ⟨794513, by rfl⟩ : syracuseStep 1059351 = 1589027) B1589027
theorem B1190443 : Blo 1056613 1190443 := bstep (se 1 (by rfl) ⟨892832, by rfl⟩ : syracuseStep 1190443 = 1785665) B1785665
theorem B1059371 : Blo 1056613 1059371 := bstep (se 1 (by rfl) ⟨794528, by rfl⟩ : syracuseStep 1059371 = 1589057) B1589057
theorem B1059383 : Blo 1056613 1059383 := bstep (se 1 (by rfl) ⟨794537, by rfl⟩ : syracuseStep 1059383 = 1589075) B1589075
theorem B6040129 : Blo 1056613 6040129 := bstep (se 2 (by rfl) ⟨2265048, by rfl⟩ : syracuseStep 6040129 = 4530097) B4530097
theorem B1059403 : Blo 1056613 1059403 := bstep (se 1 (by rfl) ⟨794552, by rfl⟩ : syracuseStep 1059403 = 1589105) B1589105
theorem B1059415 : Blo 1056613 1059415 := bstep (se 1 (by rfl) ⟨794561, by rfl⟩ : syracuseStep 1059415 = 1589123) B1589123
theorem B1059435 : Blo 1056613 1059435 := bstep (se 1 (by rfl) ⟨794576, by rfl⟩ : syracuseStep 1059435 = 1589153) B1589153
theorem B1059447 : Blo 1056613 1059447 := bstep (se 1 (by rfl) ⟨794585, by rfl⟩ : syracuseStep 1059447 = 1589171) B1589171
theorem B1059467 : Blo 1056613 1059467 := bstep (se 1 (by rfl) ⟨794600, by rfl⟩ : syracuseStep 1059467 = 1589201) B1589201
theorem B1190551 : Blo 1056613 1190551 := bstep (se 1 (by rfl) ⟨892913, by rfl⟩ : syracuseStep 1190551 = 1785827) B1785827
theorem B1059479 : Blo 1056613 1059479 := bstep (se 1 (by rfl) ⟨794609, by rfl⟩ : syracuseStep 1059479 = 1589219) B1589219
theorem B1059499 : Blo 1056613 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B1059511 : Blo 1056613 1059511 := bstep (se 1 (by rfl) ⟨794633, by rfl⟩ : syracuseStep 1059511 = 1589267) B1589267
theorem B1059531 : Blo 1056613 1059531 := bstep (se 1 (by rfl) ⟨794648, by rfl⟩ : syracuseStep 1059531 = 1589297) B1589297
theorem B1059543 : Blo 1056613 1059543 := bstep (se 1 (by rfl) ⟨794657, by rfl⟩ : syracuseStep 1059543 = 1589315) B1589315
theorem B9644761 : Blo 1056613 9644761 := bstep (se 2 (by rfl) ⟨3616785, by rfl⟩ : syracuseStep 9644761 = 7233571) B7233571
theorem B1059563 : Blo 1056613 1059563 := bstep (se 1 (by rfl) ⟨794672, by rfl⟩ : syracuseStep 1059563 = 1589345) B1589345
theorem B1059575 : Blo 1056613 1059575 := bstep (se 1 (by rfl) ⟨794681, by rfl⟩ : syracuseStep 1059575 = 1589363) B1589363
theorem B1059595 : Blo 1056613 1059595 := bstep (se 1 (by rfl) ⟨794696, by rfl⟩ : syracuseStep 1059595 = 1589393) B1589393
theorem B1059607 : Blo 1056613 1059607 := bstep (se 1 (by rfl) ⟨794705, by rfl⟩ : syracuseStep 1059607 = 1589411) B1589411
theorem B1059627 : Blo 1056613 1059627 := bstep (se 1 (by rfl) ⟨794720, by rfl⟩ : syracuseStep 1059627 = 1589441) B1589441
theorem B1059639 : Blo 1056613 1059639 := bstep (se 1 (by rfl) ⟨794729, by rfl⟩ : syracuseStep 1059639 = 1589459) B1589459
theorem B1190731 : Blo 1056613 1190731 := bstep (se 1 (by rfl) ⟨893048, by rfl⟩ : syracuseStep 1190731 = 1786097) B1786097
theorem B1059659 : Blo 1056613 1059659 := bstep (se 1 (by rfl) ⟨794744, by rfl⟩ : syracuseStep 1059659 = 1589489) B1589489
theorem B1059671 : Blo 1056613 1059671 := bstep (se 1 (by rfl) ⟨794753, by rfl⟩ : syracuseStep 1059671 = 1589507) B1589507
theorem B1059691 : Blo 1056613 1059691 := bstep (se 1 (by rfl) ⟨794768, by rfl⟩ : syracuseStep 1059691 = 1589537) B1589537
theorem B1059703 : Blo 1056613 1059703 := bstep (se 1 (by rfl) ⟨794777, by rfl⟩ : syracuseStep 1059703 = 1589555) B1589555
theorem B1059723 : Blo 1056613 1059723 := bstep (se 1 (by rfl) ⟨794792, by rfl⟩ : syracuseStep 1059723 = 1589585) B1589585
theorem B1059735 : Blo 1056613 1059735 := bstep (se 1 (by rfl) ⟨794801, by rfl⟩ : syracuseStep 1059735 = 1589603) B1589603
theorem B1059755 : Blo 1056613 1059755 := bstep (se 1 (by rfl) ⟨794816, by rfl⟩ : syracuseStep 1059755 = 1589633) B1589633
theorem B2010035 : Blo 1056613 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B1190839 : Blo 1056613 1190839 := bstep (se 1 (by rfl) ⟨893129, by rfl⟩ : syracuseStep 1190839 = 1786259) B1786259
theorem B1059767 : Blo 1056613 1059767 := bstep (se 1 (by rfl) ⟨794825, by rfl⟩ : syracuseStep 1059767 = 1589651) B1589651
theorem B1059787 : Blo 1056613 1059787 := bstep (se 1 (by rfl) ⟨794840, by rfl⟩ : syracuseStep 1059787 = 1589681) B1589681
theorem B1059799 : Blo 1056613 1059799 := bstep (se 1 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 1059799 = 1589699) B1589699
theorem B1059819 : Blo 1056613 1059819 := bstep (se 1 (by rfl) ⟨794864, by rfl⟩ : syracuseStep 1059819 = 1589729) B1589729
theorem B1059831 : Blo 1056613 1059831 := bstep (se 1 (by rfl) ⟨794873, by rfl⟩ : syracuseStep 1059831 = 1589747) B1589747
theorem B1059851 : Blo 1056613 1059851 := bstep (se 1 (by rfl) ⟨794888, by rfl⟩ : syracuseStep 1059851 = 1589777) B1589777
theorem B1059863 : Blo 1056613 1059863 := bstep (se 1 (by rfl) ⟨794897, by rfl⟩ : syracuseStep 1059863 = 1589795) B1589795
theorem B1059883 : Blo 1056613 1059883 := bstep (se 1 (by rfl) ⟨794912, by rfl⟩ : syracuseStep 1059883 = 1589825) B1589825
theorem B1059895 : Blo 1056613 1059895 := bstep (se 1 (by rfl) ⟨794921, by rfl⟩ : syracuseStep 1059895 = 1589843) B1589843
theorem B2010187 : Blo 1056613 2010187 := bstep (se 1 (by rfl) ⟨1507640, by rfl⟩ : syracuseStep 2010187 = 3015281) B3015281
theorem B1059915 : Blo 1056613 1059915 := bstep (se 1 (by rfl) ⟨794936, by rfl⟩ : syracuseStep 1059915 = 1589873) B1589873
theorem B1059927 : Blo 1056613 1059927 := bstep (se 1 (by rfl) ⟨794945, by rfl⟩ : syracuseStep 1059927 = 1589891) B1589891
theorem B1191019 : Blo 1056613 1191019 := bstep (se 1 (by rfl) ⟨893264, by rfl⟩ : syracuseStep 1191019 = 1786529) B1786529
theorem B1059947 : Blo 1056613 1059947 := bstep (se 1 (by rfl) ⟨794960, by rfl⟩ : syracuseStep 1059947 = 1589921) B1589921
theorem B1059959 : Blo 1056613 1059959 := bstep (se 1 (by rfl) ⟨794969, by rfl⟩ : syracuseStep 1059959 = 1589939) B1589939
theorem B1059979 : Blo 1056613 1059979 := bstep (se 1 (by rfl) ⟨794984, by rfl⟩ : syracuseStep 1059979 = 1589969) B1589969
theorem B1059991 : Blo 1056613 1059991 := bstep (se 1 (by rfl) ⟨794993, by rfl⟩ : syracuseStep 1059991 = 1589987) B1589987
theorem B1060011 : Blo 1056613 1060011 := bstep (se 1 (by rfl) ⟨795008, by rfl⟩ : syracuseStep 1060011 = 1590017) B1590017
theorem B1060023 : Blo 1056613 1060023 := bstep (se 1 (by rfl) ⟨795017, by rfl⟩ : syracuseStep 1060023 = 1590035) B1590035
theorem B1060043 : Blo 1056613 1060043 := bstep (se 1 (by rfl) ⟨795032, by rfl⟩ : syracuseStep 1060043 = 1590065) B1590065
theorem B1191127 : Blo 1056613 1191127 := bstep (se 1 (by rfl) ⟨893345, by rfl⟩ : syracuseStep 1191127 = 1786691) B1786691
theorem B1060055 : Blo 1056613 1060055 := bstep (se 1 (by rfl) ⟨795041, by rfl⟩ : syracuseStep 1060055 = 1590083) B1590083
theorem B1060075 : Blo 1056613 1060075 := bstep (se 1 (by rfl) ⟨795056, by rfl⟩ : syracuseStep 1060075 = 1590113) B1590113
theorem B1060087 : Blo 1056613 1060087 := bstep (se 1 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 1060087 = 1590131) B1590131
theorem B1060107 : Blo 1056613 1060107 := bstep (se 1 (by rfl) ⟨795080, by rfl⟩ : syracuseStep 1060107 = 1590161) B1590161
theorem B1060119 : Blo 1056613 1060119 := bstep (se 1 (by rfl) ⟨795089, by rfl⟩ : syracuseStep 1060119 = 1590179) B1590179
theorem B1060139 : Blo 1056613 1060139 := bstep (se 1 (by rfl) ⟨795104, by rfl⟩ : syracuseStep 1060139 = 1590209) B1590209
theorem B1060151 : Blo 1056613 1060151 := bstep (se 1 (by rfl) ⟨795113, by rfl⟩ : syracuseStep 1060151 = 1590227) B1590227
theorem B1060171 : Blo 1056613 1060171 := bstep (se 1 (by rfl) ⟨795128, by rfl⟩ : syracuseStep 1060171 = 1590257) B1590257
theorem B1060183 : Blo 1056613 1060183 := bstep (se 1 (by rfl) ⟨795137, by rfl⟩ : syracuseStep 1060183 = 1590275) B1590275
theorem B1060203 : Blo 1056613 1060203 := bstep (se 1 (by rfl) ⟨795152, by rfl⟩ : syracuseStep 1060203 = 1590305) B1590305
theorem B1060215 : Blo 1056613 1060215 := bstep (se 1 (by rfl) ⟨795161, by rfl⟩ : syracuseStep 1060215 = 1590323) B1590323
theorem B1191307 : Blo 1056613 1191307 := bstep (se 1 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 1191307 = 1786961) B1786961
theorem B1060235 : Blo 1056613 1060235 := bstep (se 1 (by rfl) ⟨795176, by rfl⟩ : syracuseStep 1060235 = 1590353) B1590353
theorem B2862487 : Blo 1056613 2862487 := bstep (se 1 (by rfl) ⟨2146865, by rfl⟩ : syracuseStep 2862487 = 4293731) B4293731
theorem B1060247 : Blo 1056613 1060247 := bstep (se 1 (by rfl) ⟨795185, by rfl⟩ : syracuseStep 1060247 = 1590371) B1590371
theorem B2010521 : Blo 1056613 2010521 := bstep (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) B1507891
theorem B1060267 : Blo 1056613 1060267 := bstep (se 1 (by rfl) ⟨795200, by rfl⟩ : syracuseStep 1060267 = 1590401) B1590401
theorem B1060279 : Blo 1056613 1060279 := bstep (se 1 (by rfl) ⟨795209, by rfl⟩ : syracuseStep 1060279 = 1590419) B1590419
theorem B1060299 : Blo 1056613 1060299 := bstep (se 1 (by rfl) ⟨795224, by rfl⟩ : syracuseStep 1060299 = 1590449) B1590449
theorem B1060311 : Blo 1056613 1060311 := bstep (se 1 (by rfl) ⟨795233, by rfl⟩ : syracuseStep 1060311 = 1590467) B1590467
theorem B8039897 : Blo 1056613 8039897 := bstep (se 2 (by rfl) ⟨3014961, by rfl⟩ : syracuseStep 8039897 = 6029923) B6029923
theorem B1060331 : Blo 1056613 1060331 := bstep (se 1 (by rfl) ⟨795248, by rfl⟩ : syracuseStep 1060331 = 1590497) B1590497
theorem B1191415 : Blo 1056613 1191415 := bstep (se 1 (by rfl) ⟨893561, by rfl⟩ : syracuseStep 1191415 = 1787123) B1787123
theorem B1060343 : Blo 1056613 1060343 := bstep (se 1 (by rfl) ⟨795257, by rfl⟩ : syracuseStep 1060343 = 1590515) B1590515
theorem B1060363 : Blo 1056613 1060363 := bstep (se 1 (by rfl) ⟨795272, by rfl⟩ : syracuseStep 1060363 = 1590545) B1590545
theorem B4075031 : Blo 1056613 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B1060375 : Blo 1056613 1060375 := bstep (se 1 (by rfl) ⟨795281, by rfl⟩ : syracuseStep 1060375 = 1590563) B1590563
theorem B1060395 : Blo 1056613 1060395 := bstep (se 1 (by rfl) ⟨795296, by rfl⟩ : syracuseStep 1060395 = 1590593) B1590593
theorem B1060407 : Blo 1056613 1060407 := bstep (se 1 (by rfl) ⟨795305, by rfl⟩ : syracuseStep 1060407 = 1590611) B1590611
theorem B1060427 : Blo 1056613 1060427 := bstep (se 1 (by rfl) ⟨795320, by rfl⟩ : syracuseStep 1060427 = 1590641) B1590641
theorem B1060439 : Blo 1056613 1060439 := bstep (se 1 (by rfl) ⟨795329, by rfl⟩ : syracuseStep 1060439 = 1590659) B1590659
theorem B1060459 : Blo 1056613 1060459 := bstep (se 1 (by rfl) ⟨795344, by rfl⟩ : syracuseStep 1060459 = 1590689) B1590689
theorem B1060471 : Blo 1056613 1060471 := bstep (se 1 (by rfl) ⟨795353, by rfl⟩ : syracuseStep 1060471 = 1590707) B1590707
theorem B1060491 : Blo 1056613 1060491 := bstep (se 1 (by rfl) ⟨795368, by rfl⟩ : syracuseStep 1060491 = 1590737) B1590737
theorem B1060503 : Blo 1056613 1060503 := bstep (se 1 (by rfl) ⟨795377, by rfl⟩ : syracuseStep 1060503 = 1590755) B1590755
theorem B1191595 : Blo 1056613 1191595 := bstep (se 1 (by rfl) ⟨893696, by rfl⟩ : syracuseStep 1191595 = 1787393) B1787393
theorem B1060523 : Blo 1056613 1060523 := bstep (se 1 (by rfl) ⟨795392, by rfl⟩ : syracuseStep 1060523 = 1590785) B1590785
theorem B1060535 : Blo 1056613 1060535 := bstep (se 1 (by rfl) ⟨795401, by rfl⟩ : syracuseStep 1060535 = 1590803) B1590803
theorem B1060555 : Blo 1056613 1060555 := bstep (se 1 (by rfl) ⟨795416, by rfl⟩ : syracuseStep 1060555 = 1590833) B1590833
theorem B1060567 : Blo 1056613 1060567 := bstep (se 1 (by rfl) ⟨795425, by rfl⟩ : syracuseStep 1060567 = 1590851) B1590851
theorem B1060587 : Blo 1056613 1060587 := bstep (se 1 (by rfl) ⟨795440, by rfl⟩ : syracuseStep 1060587 = 1590881) B1590881
theorem B1060599 : Blo 1056613 1060599 := bstep (se 1 (by rfl) ⟨795449, by rfl⟩ : syracuseStep 1060599 = 1590899) B1590899
theorem B13577989 : Blo 1056613 13577989 := bstep (se 4 (by rfl) ⟨1272936, by rfl⟩ : syracuseStep 13577989 = 2545873) B2545873
theorem B1191703 : Blo 1056613 1191703 := bstep (se 1 (by rfl) ⟨893777, by rfl⟩ : syracuseStep 1191703 = 1787555) B1787555
theorem B1584971 : Blo 1056613 1584971 := bstep (se 1 (by rfl) ⟨1188728, by rfl⟩ : syracuseStep 1584971 = 2377457) B2377457
theorem B1584983 : Blo 1056613 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B1585049 : Blo 1056613 1585049 := bstep (se 2 (by rfl) ⟨594393, by rfl⟩ : syracuseStep 1585049 = 1188787) B1188787
theorem B1191883 : Blo 1056613 1191883 := bstep (se 1 (by rfl) ⟨893912, by rfl⟩ : syracuseStep 1191883 = 1787825) B1787825
theorem B12857305 : Blo 1056613 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B1585163 : Blo 1056613 1585163 := bstep (se 1 (by rfl) ⟨1188872, by rfl⟩ : syracuseStep 1585163 = 2377745) B2377745
theorem B1585175 : Blo 1056613 1585175 := bstep (se 1 (by rfl) ⟨1188881, by rfl⟩ : syracuseStep 1585175 = 2377763) B2377763
theorem B2011159 : Blo 1056613 2011159 := bstep (se 1 (by rfl) ⟨1508369, by rfl⟩ : syracuseStep 2011159 = 3016739) B3016739
theorem B1191991 : Blo 1056613 1191991 := bstep (se 1 (by rfl) ⟨893993, by rfl⟩ : syracuseStep 1191991 = 1787987) B1787987
theorem B1585241 : Blo 1056613 1585241 := bstep (se 2 (by rfl) ⟨594465, by rfl⟩ : syracuseStep 1585241 = 1188931) B1188931
theorem B1585355 : Blo 1056613 1585355 := bstep (se 1 (by rfl) ⟨1189016, by rfl⟩ : syracuseStep 1585355 = 2378033) B2378033
theorem B1585367 : Blo 1056613 1585367 := bstep (se 1 (by rfl) ⟨1189025, by rfl⟩ : syracuseStep 1585367 = 2378051) B2378051
theorem B1192171 : Blo 1056613 1192171 := bstep (se 1 (by rfl) ⟨894128, by rfl⟩ : syracuseStep 1192171 = 1788257) B1788257
theorem B1585433 : Blo 1056613 1585433 := bstep (se 2 (by rfl) ⟨594537, by rfl⟩ : syracuseStep 1585433 = 1189075) B1189075
theorem B1192279 : Blo 1056613 1192279 := bstep (se 1 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 1192279 = 1788419) B1788419
theorem B3223901 : Blo 1056613 3223901 := bstep (se 3 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 3223901 = 1208963) B1208963
theorem B1585547 : Blo 1056613 1585547 := bstep (se 1 (by rfl) ⟨1189160, by rfl⟩ : syracuseStep 1585547 = 2378321) B2378321
theorem B1585559 : Blo 1056613 1585559 := bstep (se 1 (by rfl) ⟨1189169, by rfl⟩ : syracuseStep 1585559 = 2378339) B2378339
theorem B1585625 : Blo 1056613 1585625 := bstep (se 2 (by rfl) ⟨594609, by rfl⟩ : syracuseStep 1585625 = 1189219) B1189219
theorem B1192459 : Blo 1056613 1192459 := bstep (se 1 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 1192459 = 1788689) B1788689
theorem B2863667 : Blo 1056613 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B1585739 : Blo 1056613 1585739 := bstep (se 1 (by rfl) ⟨1189304, by rfl⟩ : syracuseStep 1585739 = 2378609) B2378609
theorem B1585751 : Blo 1056613 1585751 := bstep (se 1 (by rfl) ⟨1189313, by rfl⟩ : syracuseStep 1585751 = 2378627) B2378627
theorem B1192567 : Blo 1056613 1192567 := bstep (se 1 (by rfl) ⟨894425, by rfl⟩ : syracuseStep 1192567 = 1788851) B1788851
theorem B1585817 : Blo 1056613 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B1585931 : Blo 1056613 1585931 := bstep (se 1 (by rfl) ⟨1189448, by rfl⟩ : syracuseStep 1585931 = 2378897) B2378897
theorem B1585943 : Blo 1056613 1585943 := bstep (se 1 (by rfl) ⟨1189457, by rfl⟩ : syracuseStep 1585943 = 2378915) B2378915
theorem B4829975 : Blo 1056613 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B1192747 : Blo 1056613 1192747 := bstep (se 1 (by rfl) ⟨894560, by rfl⟩ : syracuseStep 1192747 = 1789121) B1789121
theorem B2011979 : Blo 1056613 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B1586009 : Blo 1056613 1586009 := bstep (se 2 (by rfl) ⟨594753, by rfl⟩ : syracuseStep 1586009 = 1189507) B1189507
theorem B2012033 : Blo 1056613 2012033 := bstep (se 2 (by rfl) ⟨754512, by rfl⟩ : syracuseStep 2012033 = 1509025) B1509025
theorem B5092247 : Blo 1056613 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B1192855 : Blo 1056613 1192855 := bstep (se 1 (by rfl) ⟨894641, by rfl⟩ : syracuseStep 1192855 = 1789283) B1789283
theorem B2864065 : Blo 1056613 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1586123 : Blo 1056613 1586123 := bstep (se 1 (by rfl) ⟨1189592, by rfl⟩ : syracuseStep 1586123 = 2379185) B2379185
theorem B1586135 : Blo 1056613 1586135 := bstep (se 1 (by rfl) ⟨1189601, by rfl⟩ : syracuseStep 1586135 = 2379203) B2379203
theorem B2176001 : Blo 1056613 2176001 := bstep (se 2 (by rfl) ⟨816000, by rfl⟩ : syracuseStep 2176001 = 1632001) B1632001
theorem B1586201 : Blo 1056613 1586201 := bstep (se 2 (by rfl) ⟨594825, by rfl⟩ : syracuseStep 1586201 = 1189651) B1189651
theorem B1193035 : Blo 1056613 1193035 := bstep (se 1 (by rfl) ⟨894776, by rfl⟩ : syracuseStep 1193035 = 1789553) B1789553
theorem B1586315 : Blo 1056613 1586315 := bstep (se 1 (by rfl) ⟨1189736, by rfl⟩ : syracuseStep 1586315 = 2379473) B2379473
theorem B1586327 : Blo 1056613 1586327 := bstep (se 1 (by rfl) ⟨1189745, by rfl⟩ : syracuseStep 1586327 = 2379491) B2379491
theorem B3814573 : Blo 1056613 3814573 := bstep (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) B1430465
theorem B1193143 : Blo 1056613 1193143 := bstep (se 1 (by rfl) ⟨894857, by rfl⟩ : syracuseStep 1193143 = 1789715) B1789715
theorem B1586393 : Blo 1056613 1586393 := bstep (se 2 (by rfl) ⟨594897, by rfl⟩ : syracuseStep 1586393 = 1189795) B1189795
theorem B1586507 : Blo 1056613 1586507 := bstep (se 1 (by rfl) ⟨1189880, by rfl⟩ : syracuseStep 1586507 = 2379761) B2379761
theorem B1783127 : Blo 1056613 1783127 := bstep (se 1 (by rfl) ⟨1337345, by rfl⟩ : syracuseStep 1783127 = 2674691) B2674691
theorem B1586519 : Blo 1056613 1586519 := bstep (se 1 (by rfl) ⟨1189889, by rfl⟩ : syracuseStep 1586519 = 2379779) B2379779
theorem B1586585 : Blo 1056613 1586585 := bstep (se 2 (by rfl) ⟨594969, by rfl⟩ : syracuseStep 1586585 = 1189939) B1189939
theorem B1783255 : Blo 1056613 1783255 := bstep (se 1 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 1783255 = 2674883) B2674883
theorem B1586699 : Blo 1056613 1586699 := bstep (se 1 (by rfl) ⟨1190024, by rfl⟩ : syracuseStep 1586699 = 2380049) B2380049
theorem B1586711 : Blo 1056613 1586711 := bstep (se 1 (by rfl) ⟨1190033, by rfl⟩ : syracuseStep 1586711 = 2380067) B2380067
theorem B1586777 : Blo 1056613 1586777 := bstep (se 2 (by rfl) ⟨595041, by rfl⟩ : syracuseStep 1586777 = 1190083) B1190083
theorem B3815063 : Blo 1056613 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B1586891 : Blo 1056613 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B1586903 : Blo 1056613 1586903 := bstep (se 1 (by rfl) ⟨1190177, by rfl⟩ : syracuseStep 1586903 = 2380355) B2380355
theorem B2012951 : Blo 1056613 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B1586969 : Blo 1056613 1586969 := bstep (se 2 (by rfl) ⟨595113, by rfl⟩ : syracuseStep 1586969 = 1190227) B1190227
theorem B4011869 : Blo 1056613 4011869 := bstep (se 3 (by rfl) ⟨752225, by rfl⟩ : syracuseStep 4011869 = 1504451) B1504451
theorem B5355395 : Blo 1056613 5355395 := bstep (se 1 (by rfl) ⟨4016546, by rfl⟩ : syracuseStep 5355395 = 8033093) B8033093
theorem B1587083 : Blo 1056613 1587083 := bstep (se 1 (by rfl) ⟨1190312, by rfl⟩ : syracuseStep 1587083 = 2380625) B2380625
theorem B1587095 : Blo 1056613 1587095 := bstep (se 1 (by rfl) ⟨1190321, by rfl⟩ : syracuseStep 1587095 = 2380643) B2380643
theorem B3094451 : Blo 1056613 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1587161 : Blo 1056613 1587161 := bstep (se 2 (by rfl) ⟨595185, by rfl⟩ : syracuseStep 1587161 = 1190371) B1190371
theorem B1783883 : Blo 1056613 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B32553035 : Blo 1056613 32553035 := bstep (se 1 (by rfl) ⟨24414776, by rfl⟩ : syracuseStep 32553035 = 48829553) B48829553
theorem B1587275 : Blo 1056613 1587275 := bstep (se 1 (by rfl) ⟨1190456, by rfl⟩ : syracuseStep 1587275 = 2380913) B2380913
theorem B1587287 : Blo 1056613 1587287 := bstep (se 1 (by rfl) ⟨1190465, by rfl⟩ : syracuseStep 1587287 = 2380931) B2380931
theorem B16300163 : Blo 1056613 16300163 := bstep (se 1 (by rfl) ⟨12225122, by rfl⟩ : syracuseStep 16300163 = 24450245) B24450245
theorem B1587353 : Blo 1056613 1587353 := bstep (se 2 (by rfl) ⟨595257, by rfl⟩ : syracuseStep 1587353 = 1190515) B1190515
theorem B1784011 : Blo 1056613 1784011 := bstep (se 1 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 1784011 = 2676017) B2676017
theorem B2144513 : Blo 1056613 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B1587467 : Blo 1056613 1587467 := bstep (se 1 (by rfl) ⟨1190600, by rfl⟩ : syracuseStep 1587467 = 2381201) B2381201
theorem B1587479 : Blo 1056613 1587479 := bstep (se 1 (by rfl) ⟨1190609, by rfl⟩ : syracuseStep 1587479 = 2381219) B2381219
theorem B2013491 : Blo 1056613 2013491 := bstep (se 1 (by rfl) ⟨1510118, by rfl⟩ : syracuseStep 2013491 = 3020237) B3020237
theorem B1784153 : Blo 1056613 1784153 := bstep (se 2 (by rfl) ⟨669057, by rfl⟩ : syracuseStep 1784153 = 1338115) B1338115
theorem B1587545 : Blo 1056613 1587545 := bstep (se 2 (by rfl) ⟨595329, by rfl⟩ : syracuseStep 1587545 = 1190659) B1190659
theorem B7616861 : Blo 1056613 7616861 := bstep (se 3 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 7616861 = 2856323) B2856323
theorem B1587659 : Blo 1056613 1587659 := bstep (se 1 (by rfl) ⟨1190744, by rfl⟩ : syracuseStep 1587659 = 2381489) B2381489
theorem B1587671 : Blo 1056613 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B1718743 : Blo 1056613 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B1784281 : Blo 1056613 1784281 := bstep (se 2 (by rfl) ⟨669105, by rfl⟩ : syracuseStep 1784281 = 1338211) B1338211
theorem B1587737 : Blo 1056613 1587737 := bstep (se 2 (by rfl) ⟨595401, by rfl⟩ : syracuseStep 1587737 = 1190803) B1190803
theorem B1587851 : Blo 1056613 1587851 := bstep (se 1 (by rfl) ⟨1190888, by rfl⟩ : syracuseStep 1587851 = 2381777) B2381777
theorem B1587863 : Blo 1056613 1587863 := bstep (se 1 (by rfl) ⟨1190897, by rfl⟩ : syracuseStep 1587863 = 2381795) B2381795
theorem B1587929 : Blo 1056613 1587929 := bstep (se 2 (by rfl) ⟨595473, by rfl⟩ : syracuseStep 1587929 = 1190947) B1190947
theorem B25770737 : Blo 1056613 25770737 := bstep (se 2 (by rfl) ⟨9664026, by rfl⟩ : syracuseStep 25770737 = 19328053) B19328053
theorem B8043299 : Blo 1056613 8043299 := bstep (se 1 (by rfl) ⟨6032474, by rfl⟩ : syracuseStep 8043299 = 12064949) B12064949
theorem B1588043 : Blo 1056613 1588043 := bstep (se 1 (by rfl) ⟨1191032, by rfl⟩ : syracuseStep 1588043 = 2382065) B2382065
theorem B1588055 : Blo 1056613 1588055 := bstep (se 1 (by rfl) ⟨1191041, by rfl⟩ : syracuseStep 1588055 = 2382083) B2382083
theorem B1588121 : Blo 1056613 1588121 := bstep (se 2 (by rfl) ⟨595545, by rfl⟩ : syracuseStep 1588121 = 1191091) B1191091
theorem B2866141 : Blo 1056613 2866141 := bstep (se 3 (by rfl) ⟨537401, by rfl⟩ : syracuseStep 2866141 = 1074803) B1074803
theorem B1129483 : Blo 1056613 1129483 := bstep (se 1 (by rfl) ⟨847112, by rfl⟩ : syracuseStep 1129483 = 1694225) B1694225
theorem B1588235 : Blo 1056613 1588235 := bstep (se 1 (by rfl) ⟨1191176, by rfl⟩ : syracuseStep 1588235 = 2382353) B2382353
theorem B1784855 : Blo 1056613 1784855 := bstep (se 1 (by rfl) ⟨1338641, by rfl⟩ : syracuseStep 1784855 = 2677283) B2677283
theorem B1588247 : Blo 1056613 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B1588313 : Blo 1056613 1588313 := bstep (se 2 (by rfl) ⟨595617, by rfl⟩ : syracuseStep 1588313 = 1191235) B1191235
theorem B5717143 : Blo 1056613 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B1784983 : Blo 1056613 1784983 := bstep (se 1 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 1784983 = 2677475) B2677475
theorem B3619991 : Blo 1056613 3619991 := bstep (se 1 (by rfl) ⟨2714993, by rfl⟩ : syracuseStep 3619991 = 5429987) B5429987
theorem B1588427 : Blo 1056613 1588427 := bstep (se 1 (by rfl) ⟨1191320, by rfl⟩ : syracuseStep 1588427 = 2382641) B2382641
theorem B1588439 : Blo 1056613 1588439 := bstep (se 1 (by rfl) ⟨1191329, by rfl⟩ : syracuseStep 1588439 = 2382659) B2382659
theorem B1588505 : Blo 1056613 1588505 := bstep (se 2 (by rfl) ⟨595689, by rfl⟩ : syracuseStep 1588505 = 1191379) B1191379
theorem B1588619 : Blo 1056613 1588619 := bstep (se 1 (by rfl) ⟨1191464, by rfl⟩ : syracuseStep 1588619 = 2382929) B2382929
theorem B1588631 : Blo 1056613 1588631 := bstep (se 1 (by rfl) ⟨1191473, by rfl⟩ : syracuseStep 1588631 = 2382947) B2382947
theorem B1588697 : Blo 1056613 1588697 := bstep (se 2 (by rfl) ⟨595761, by rfl⟩ : syracuseStep 1588697 = 1191523) B1191523
theorem B1588811 : Blo 1056613 1588811 := bstep (se 1 (by rfl) ⟨1191608, by rfl⟩ : syracuseStep 1588811 = 2383217) B2383217
theorem B1588823 : Blo 1056613 1588823 := bstep (se 1 (by rfl) ⟨1191617, by rfl⟩ : syracuseStep 1588823 = 2383235) B2383235
theorem B1588889 : Blo 1056613 1588889 := bstep (se 2 (by rfl) ⟨595833, by rfl⟩ : syracuseStep 1588889 = 1191667) B1191667
theorem B1130231 : Blo 1056613 1130231 := bstep (se 1 (by rfl) ⟨847673, by rfl⟩ : syracuseStep 1130231 = 1695347) B1695347
theorem B1785611 : Blo 1056613 1785611 := bstep (se 1 (by rfl) ⟨1339208, by rfl⟩ : syracuseStep 1785611 = 2678417) B2678417
theorem B1589003 : Blo 1056613 1589003 := bstep (se 1 (by rfl) ⟨1191752, by rfl⟩ : syracuseStep 1589003 = 2383505) B2383505
theorem B1589015 : Blo 1056613 1589015 := bstep (se 1 (by rfl) ⟨1191761, by rfl⟩ : syracuseStep 1589015 = 2383523) B2383523
theorem B1359703 : Blo 1056613 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B1589081 : Blo 1056613 1589081 := bstep (se 2 (by rfl) ⟨595905, by rfl⟩ : syracuseStep 1589081 = 1191811) B1191811
theorem B1785739 : Blo 1056613 1785739 := bstep (se 1 (by rfl) ⟨1339304, by rfl⟩ : syracuseStep 1785739 = 2678609) B2678609
theorem B2539415 : Blo 1056613 2539415 := bstep (se 1 (by rfl) ⟨1904561, by rfl⟩ : syracuseStep 2539415 = 3809123) B3809123
theorem B1589195 : Blo 1056613 1589195 := bstep (se 1 (by rfl) ⟨1191896, by rfl⟩ : syracuseStep 1589195 = 2383793) B2383793
theorem B1589207 : Blo 1056613 1589207 := bstep (se 1 (by rfl) ⟨1191905, by rfl⟩ : syracuseStep 1589207 = 2383811) B2383811
theorem B2146265 : Blo 1056613 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B1785881 : Blo 1056613 1785881 := bstep (se 2 (by rfl) ⟨669705, by rfl⟩ : syracuseStep 1785881 = 1339411) B1339411
theorem B1589273 : Blo 1056613 1589273 := bstep (se 2 (by rfl) ⟨595977, by rfl⟩ : syracuseStep 1589273 = 1191955) B1191955
theorem B3391577 : Blo 1056613 3391577 := bstep (se 2 (by rfl) ⟨1271841, by rfl⟩ : syracuseStep 3391577 = 2543683) B2543683
theorem B1589387 : Blo 1056613 1589387 := bstep (se 1 (by rfl) ⟨1192040, by rfl⟩ : syracuseStep 1589387 = 2384081) B2384081
theorem B1589399 : Blo 1056613 1589399 := bstep (se 1 (by rfl) ⟨1192049, by rfl⟩ : syracuseStep 1589399 = 2384099) B2384099
theorem B1786009 : Blo 1056613 1786009 := bstep (se 2 (by rfl) ⟨669753, by rfl⟩ : syracuseStep 1786009 = 1339507) B1339507
theorem B1589465 : Blo 1056613 1589465 := bstep (se 2 (by rfl) ⟨596049, by rfl⟩ : syracuseStep 1589465 = 1192099) B1192099
theorem B1589579 : Blo 1056613 1589579 := bstep (se 1 (by rfl) ⟨1192184, by rfl⟩ : syracuseStep 1589579 = 2384369) B2384369
theorem B1589591 : Blo 1056613 1589591 := bstep (se 1 (by rfl) ⟨1192193, by rfl⟩ : syracuseStep 1589591 = 2384387) B2384387
theorem B4014467 : Blo 1056613 4014467 := bstep (se 1 (by rfl) ⟨3010850, by rfl⟩ : syracuseStep 4014467 = 6021701) B6021701
theorem B4014481 : Blo 1056613 4014481 := bstep (se 2 (by rfl) ⟨1505430, by rfl⟩ : syracuseStep 4014481 = 3010861) B3010861
theorem B1589657 : Blo 1056613 1589657 := bstep (se 2 (by rfl) ⟨596121, by rfl⟩ : syracuseStep 1589657 = 1192243) B1192243
theorem B1589771 : Blo 1056613 1589771 := bstep (se 1 (by rfl) ⟨1192328, by rfl⟩ : syracuseStep 1589771 = 2384657) B2384657
theorem B1589783 : Blo 1056613 1589783 := bstep (se 1 (by rfl) ⟨1192337, by rfl⟩ : syracuseStep 1589783 = 2384675) B2384675
theorem B2540107 : Blo 1056613 2540107 := bstep (se 1 (by rfl) ⟨1905080, by rfl⟩ : syracuseStep 2540107 = 3810161) B3810161
theorem B1589849 : Blo 1056613 1589849 := bstep (se 2 (by rfl) ⟨596193, by rfl⟩ : syracuseStep 1589849 = 1192387) B1192387
theorem B4014785 : Blo 1056613 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B1589963 : Blo 1056613 1589963 := bstep (se 1 (by rfl) ⟨1192472, by rfl⟩ : syracuseStep 1589963 = 2384945) B2384945
theorem B27509453 : Blo 1056613 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B1786583 : Blo 1056613 1786583 := bstep (se 1 (by rfl) ⟨1339937, by rfl⟩ : syracuseStep 1786583 = 2679875) B2679875
theorem B1589975 : Blo 1056613 1589975 := bstep (se 1 (by rfl) ⟨1192481, by rfl⟩ : syracuseStep 1589975 = 2384963) B2384963
theorem B1590041 : Blo 1056613 1590041 := bstep (se 2 (by rfl) ⟨596265, by rfl⟩ : syracuseStep 1590041 = 1192531) B1192531
theorem B1786711 : Blo 1056613 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B1590155 : Blo 1056613 1590155 := bstep (se 1 (by rfl) ⟨1192616, by rfl⟩ : syracuseStep 1590155 = 2385233) B2385233
theorem B1590167 : Blo 1056613 1590167 := bstep (se 1 (by rfl) ⟨1192625, by rfl⟩ : syracuseStep 1590167 = 2385251) B2385251
theorem B13583321 : Blo 1056613 13583321 := bstep (se 2 (by rfl) ⟨5093745, by rfl⟩ : syracuseStep 13583321 = 10187491) B10187491
theorem B1590233 : Blo 1056613 1590233 := bstep (se 2 (by rfl) ⟨596337, by rfl⟩ : syracuseStep 1590233 = 1192675) B1192675
theorem B7619629 : Blo 1056613 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B1590347 : Blo 1056613 1590347 := bstep (se 1 (by rfl) ⟨1192760, by rfl⟩ : syracuseStep 1590347 = 2385521) B2385521
theorem B1590359 : Blo 1056613 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B2147467 : Blo 1056613 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B1590425 : Blo 1056613 1590425 := bstep (se 2 (by rfl) ⟨596409, by rfl⟩ : syracuseStep 1590425 = 1192819) B1192819
theorem B3392705 : Blo 1056613 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B1590539 : Blo 1056613 1590539 := bstep (se 1 (by rfl) ⟨1192904, by rfl⟩ : syracuseStep 1590539 = 2385809) B2385809
theorem B1590551 : Blo 1056613 1590551 := bstep (se 1 (by rfl) ⟨1192913, by rfl⟩ : syracuseStep 1590551 = 2385827) B2385827
theorem B3392857 : Blo 1056613 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B1590617 : Blo 1056613 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B4015453 : Blo 1056613 4015453 := bstep (se 3 (by rfl) ⟨752897, by rfl⟩ : syracuseStep 4015453 = 1505795) B1505795
theorem B1787339 : Blo 1056613 1787339 := bstep (se 1 (by rfl) ⟨1340504, by rfl⟩ : syracuseStep 1787339 = 2681009) B2681009
theorem B1590731 : Blo 1056613 1590731 := bstep (se 1 (by rfl) ⟨1193048, by rfl⟩ : syracuseStep 1590731 = 2386097) B2386097
theorem B1590743 : Blo 1056613 1590743 := bstep (se 1 (by rfl) ⟨1193057, by rfl⟩ : syracuseStep 1590743 = 2386115) B2386115
theorem B5359121 : Blo 1056613 5359121 := bstep (se 2 (by rfl) ⟨2009670, by rfl⟩ : syracuseStep 5359121 = 4019341) B4019341
theorem B1590809 : Blo 1056613 1590809 := bstep (se 2 (by rfl) ⟨596553, by rfl⟩ : syracuseStep 1590809 = 1193107) B1193107
theorem B2541107 : Blo 1056613 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B1787467 : Blo 1056613 1787467 := bstep (se 1 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 1787467 = 2681201) B2681201
theorem B5359283 : Blo 1056613 5359283 := bstep (se 1 (by rfl) ⟨4019462, by rfl⟩ : syracuseStep 5359283 = 8038925) B8038925
theorem B1787609 : Blo 1056613 1787609 := bstep (se 2 (by rfl) ⟨670353, by rfl⟩ : syracuseStep 1787609 = 1340707) B1340707
theorem B5719825 : Blo 1056613 5719825 := bstep (se 2 (by rfl) ⟨2144934, by rfl⟩ : syracuseStep 5719825 = 4289869) B4289869
theorem B4835095 : Blo 1056613 4835095 := bstep (se 1 (by rfl) ⟨3626321, by rfl⟩ : syracuseStep 4835095 = 7252643) B7252643
theorem B2377547 : Blo 1056613 2377547 := bstep (se 1 (by rfl) ⟨1783160, by rfl⟩ : syracuseStep 2377547 = 3566321) B3566321
theorem B1787737 : Blo 1056613 1787737 := bstep (se 2 (by rfl) ⟨670401, by rfl⟩ : syracuseStep 1787737 = 1340803) B1340803
theorem B2148211 : Blo 1056613 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B2377601 : Blo 1056613 2377601 := bstep (se 2 (by rfl) ⟨891600, by rfl⟩ : syracuseStep 2377601 = 1783201) B1783201
theorem B1132439 : Blo 1056613 1132439 := bstep (se 1 (by rfl) ⟨849329, by rfl⟩ : syracuseStep 1132439 = 1698659) B1698659
theorem B2377817 : Blo 1056613 2377817 := bstep (se 2 (by rfl) ⟨891681, by rfl⟩ : syracuseStep 2377817 = 1783363) B1783363
theorem B2377907 : Blo 1056613 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B2377943 : Blo 1056613 2377943 := bstep (se 1 (by rfl) ⟨1783457, by rfl⟩ : syracuseStep 2377943 = 3566915) B3566915
theorem B2541875 : Blo 1056613 2541875 := bstep (se 1 (by rfl) ⟨1906406, by rfl⟩ : syracuseStep 2541875 = 3812813) B3812813
theorem B2378123 : Blo 1056613 2378123 := bstep (se 1 (by rfl) ⟨1783592, by rfl⟩ : syracuseStep 2378123 = 3567185) B3567185
theorem B1788311 : Blo 1056613 1788311 := bstep (se 1 (by rfl) ⟨1341233, by rfl⟩ : syracuseStep 1788311 = 2682467) B2682467
theorem B2378177 : Blo 1056613 2378177 := bstep (se 2 (by rfl) ⟨891816, by rfl⟩ : syracuseStep 2378177 = 1783633) B1783633
theorem B2148811 : Blo 1056613 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B1788439 : Blo 1056613 1788439 := bstep (se 1 (by rfl) ⟨1341329, by rfl⟩ : syracuseStep 1788439 = 2682659) B2682659
theorem B4016729 : Blo 1056613 4016729 := bstep (se 2 (by rfl) ⟨1506273, by rfl⟩ : syracuseStep 4016729 = 3012547) B3012547
theorem B2378393 : Blo 1056613 2378393 := bstep (se 2 (by rfl) ⟨891897, by rfl⟩ : syracuseStep 2378393 = 1783795) B1783795
theorem B2378483 : Blo 1056613 2378483 := bstep (se 1 (by rfl) ⟨1783862, by rfl⟩ : syracuseStep 2378483 = 3567725) B3567725
theorem B2378519 : Blo 1056613 2378519 := bstep (se 1 (by rfl) ⟨1783889, by rfl⟩ : syracuseStep 2378519 = 3567779) B3567779
theorem B2149249 : Blo 1056613 2149249 := bstep (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) B1611937
theorem B2378699 : Blo 1056613 2378699 := bstep (se 1 (by rfl) ⟨1784024, by rfl⟩ : syracuseStep 2378699 = 3568049) B3568049
theorem B2378753 : Blo 1056613 2378753 := bstep (se 2 (by rfl) ⟨892032, by rfl⟩ : syracuseStep 2378753 = 1784065) B1784065
theorem B1789067 : Blo 1056613 1789067 := bstep (se 1 (by rfl) ⟨1341800, by rfl⟩ : syracuseStep 1789067 = 2683601) B2683601
theorem B2378969 : Blo 1056613 2378969 := bstep (se 2 (by rfl) ⟨892113, by rfl⟩ : syracuseStep 2378969 = 1784227) B1784227
theorem B1789195 : Blo 1056613 1789195 := bstep (se 1 (by rfl) ⟨1341896, by rfl⟩ : syracuseStep 1789195 = 2683793) B2683793
theorem B2379059 : Blo 1056613 2379059 := bstep (se 1 (by rfl) ⟨1784294, by rfl⟩ : syracuseStep 2379059 = 3568589) B3568589
theorem B2379095 : Blo 1056613 2379095 := bstep (se 1 (by rfl) ⟨1784321, by rfl⟩ : syracuseStep 2379095 = 3568643) B3568643
theorem B9031013 : Blo 1056613 9031013 := bstep (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) B1693315
theorem B1789337 : Blo 1056613 1789337 := bstep (se 2 (by rfl) ⟨671001, by rfl⟩ : syracuseStep 1789337 = 1342003) B1342003
theorem B2379275 : Blo 1056613 2379275 := bstep (se 1 (by rfl) ⟨1784456, by rfl⟩ : syracuseStep 2379275 = 3568913) B3568913
theorem B1789465 : Blo 1056613 1789465 := bstep (se 2 (by rfl) ⟨671049, by rfl⟩ : syracuseStep 1789465 = 1342099) B1342099
theorem B2379329 : Blo 1056613 2379329 := bstep (se 2 (by rfl) ⟨892248, by rfl⟩ : syracuseStep 2379329 = 1784497) B1784497
theorem B5361227 : Blo 1056613 5361227 := bstep (se 1 (by rfl) ⟨4020920, by rfl⟩ : syracuseStep 5361227 = 8041841) B8041841
theorem B2379545 : Blo 1056613 2379545 := bstep (se 2 (by rfl) ⟨892329, by rfl⟩ : syracuseStep 2379545 = 1784659) B1784659
theorem B2379635 : Blo 1056613 2379635 := bstep (se 1 (by rfl) ⟨1784726, by rfl⟩ : syracuseStep 2379635 = 3569453) B3569453
theorem B2379671 : Blo 1056613 2379671 := bstep (se 1 (by rfl) ⟨1784753, by rfl⟩ : syracuseStep 2379671 = 3569507) B3569507
theorem B8048645 : Blo 1056613 8048645 := bstep (se 4 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 8048645 = 1509121) B1509121
theorem B2412569 : Blo 1056613 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B2379851 : Blo 1056613 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B3395677 : Blo 1056613 3395677 := bstep (se 3 (by rfl) ⟨636689, by rfl⟩ : syracuseStep 3395677 = 1273379) B1273379
theorem B2379905 : Blo 1056613 2379905 := bstep (se 2 (by rfl) ⟨892464, by rfl⟩ : syracuseStep 2379905 = 1784929) B1784929
theorem B4018355 : Blo 1056613 4018355 := bstep (se 1 (by rfl) ⟨3013766, by rfl⟩ : syracuseStep 4018355 = 6027533) B6027533
theorem B4018369 : Blo 1056613 4018369 := bstep (se 2 (by rfl) ⟨1506888, by rfl⟩ : syracuseStep 4018369 = 3013777) B3013777
theorem B2380121 : Blo 1056613 2380121 := bstep (se 2 (by rfl) ⟨892545, by rfl⟩ : syracuseStep 2380121 = 1785091) B1785091
theorem B3395933 : Blo 1056613 3395933 := bstep (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) B1273475
theorem B2380211 : Blo 1056613 2380211 := bstep (se 1 (by rfl) ⟨1785158, by rfl⟩ : syracuseStep 2380211 = 3570317) B3570317
theorem B2380247 : Blo 1056613 2380247 := bstep (se 1 (by rfl) ⟨1785185, by rfl⟩ : syracuseStep 2380247 = 3570371) B3570371
theorem B2413081 : Blo 1056613 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B2544203 : Blo 1056613 2544203 := bstep (se 1 (by rfl) ⟨1908152, by rfl⟩ : syracuseStep 2544203 = 3816305) B3816305
theorem B3822155 : Blo 1056613 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B2904665 : Blo 1056613 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B2380427 : Blo 1056613 2380427 := bstep (se 1 (by rfl) ⟨1785320, by rfl⟩ : syracuseStep 2380427 = 3570641) B3570641
theorem B2380481 : Blo 1056613 2380481 := bstep (se 2 (by rfl) ⟨892680, by rfl⟩ : syracuseStep 2380481 = 1785361) B1785361
theorem B3134173 : Blo 1056613 3134173 := bstep (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) B1175315
theorem B2675531 : Blo 1056613 2675531 := bstep (se 1 (by rfl) ⟨2006648, by rfl⟩ : syracuseStep 2675531 = 4013297) B4013297
theorem B2380697 : Blo 1056613 2380697 := bstep (se 2 (by rfl) ⟨892761, by rfl⟩ : syracuseStep 2380697 = 1785523) B1785523
theorem B2544587 : Blo 1056613 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B2380787 : Blo 1056613 2380787 := bstep (se 1 (by rfl) ⟨1785590, by rfl⟩ : syracuseStep 2380787 = 3571181) B3571181
theorem B2380823 : Blo 1056613 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B12047453 : Blo 1056613 12047453 := bstep (se 3 (by rfl) ⟨2258897, by rfl⟩ : syracuseStep 12047453 = 4517795) B4517795
theorem B2381003 : Blo 1056613 2381003 := bstep (se 1 (by rfl) ⟨1785752, by rfl⟩ : syracuseStep 2381003 = 3571505) B3571505
theorem B2381057 : Blo 1056613 2381057 := bstep (se 2 (by rfl) ⟨892896, by rfl⟩ : syracuseStep 2381057 = 1785793) B1785793
theorem B5363009 : Blo 1056613 5363009 := bstep (se 2 (by rfl) ⟨2011128, by rfl⟩ : syracuseStep 5363009 = 4022257) B4022257
theorem B3265885 : Blo 1056613 3265885 := bstep (se 3 (by rfl) ⟨612353, by rfl⟩ : syracuseStep 3265885 = 1224707) B1224707
theorem B2381273 : Blo 1056613 2381273 := bstep (se 2 (by rfl) ⟨892977, by rfl⟩ : syracuseStep 2381273 = 1785955) B1785955
theorem B9655853 : Blo 1056613 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B2381363 : Blo 1056613 2381363 := bstep (se 1 (by rfl) ⟨1786022, by rfl⟩ : syracuseStep 2381363 = 3572045) B3572045
theorem B2381399 : Blo 1056613 2381399 := bstep (se 1 (by rfl) ⟨1786049, by rfl⟩ : syracuseStep 2381399 = 3572099) B3572099
theorem B1693399 : Blo 1056613 1693399 := bstep (se 1 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 1693399 = 2540099) B2540099
theorem B27481841 : Blo 1056613 27481841 := bstep (se 2 (by rfl) ⟨10305690, by rfl⟩ : syracuseStep 27481841 = 20611381) B20611381
theorem B2381579 : Blo 1056613 2381579 := bstep (se 1 (by rfl) ⟨1786184, by rfl⟩ : syracuseStep 2381579 = 3572369) B3572369
theorem B2676503 : Blo 1056613 2676503 := bstep (se 1 (by rfl) ⟨2007377, by rfl⟩ : syracuseStep 2676503 = 4014755) B4014755
theorem B2381633 : Blo 1056613 2381633 := bstep (se 2 (by rfl) ⟨893112, by rfl⟩ : syracuseStep 2381633 = 1786225) B1786225
theorem B10180417 : Blo 1056613 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B9033677 : Blo 1056613 9033677 := bstep (se 3 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 9033677 = 3387629) B3387629
theorem B2381849 : Blo 1056613 2381849 := bstep (se 2 (by rfl) ⟨893193, by rfl⟩ : syracuseStep 2381849 = 1786387) B1786387
theorem B4773953 : Blo 1056613 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B4020299 : Blo 1056613 4020299 := bstep (se 1 (by rfl) ⟨3015224, by rfl⟩ : syracuseStep 4020299 = 6030449) B6030449
theorem B4020313 : Blo 1056613 4020313 := bstep (se 2 (by rfl) ⟨1507617, by rfl⟩ : syracuseStep 4020313 = 3015235) B3015235
theorem B2381939 : Blo 1056613 2381939 := bstep (se 1 (by rfl) ⟨1786454, by rfl⟩ : syracuseStep 2381939 = 3572909) B3572909
theorem B2381975 : Blo 1056613 2381975 := bstep (se 1 (by rfl) ⟨1786481, by rfl⟩ : syracuseStep 2381975 = 3572963) B3572963
theorem B1693963 : Blo 1056613 1693963 := bstep (se 1 (by rfl) ⟨1270472, by rfl⟩ : syracuseStep 1693963 = 2540945) B2540945
theorem B6773057 : Blo 1056613 6773057 := bstep (se 2 (by rfl) ⟨2539896, by rfl⟩ : syracuseStep 6773057 = 5079793) B5079793
theorem B2382155 : Blo 1056613 2382155 := bstep (se 1 (by rfl) ⟨1786616, by rfl⟩ : syracuseStep 2382155 = 3573233) B3573233
theorem B2382209 : Blo 1056613 2382209 := bstep (se 2 (by rfl) ⟨893328, by rfl⟩ : syracuseStep 2382209 = 1786657) B1786657
theorem B8051075 : Blo 1056613 8051075 := bstep (se 1 (by rfl) ⟨6038306, by rfl⟩ : syracuseStep 8051075 = 12076613) B12076613
theorem B2677171 : Blo 1056613 2677171 := bstep (se 1 (by rfl) ⟨2007878, by rfl⟩ : syracuseStep 2677171 = 4015757) B4015757
theorem B2677313 : Blo 1056613 2677313 := bstep (se 2 (by rfl) ⟨1003992, by rfl⟩ : syracuseStep 2677313 = 2007985) B2007985
theorem B2382425 : Blo 1056613 2382425 := bstep (se 2 (by rfl) ⟨893409, by rfl⟩ : syracuseStep 2382425 = 1786819) B1786819
theorem B2382515 : Blo 1056613 2382515 := bstep (se 1 (by rfl) ⟨1786886, by rfl⟩ : syracuseStep 2382515 = 3573773) B3573773
theorem B2382551 : Blo 1056613 2382551 := bstep (se 1 (by rfl) ⟨1786913, by rfl⟩ : syracuseStep 2382551 = 3573827) B3573827
theorem B2382731 : Blo 1056613 2382731 := bstep (se 1 (by rfl) ⟨1787048, by rfl⟩ : syracuseStep 2382731 = 3574097) B3574097
theorem B6019991 : Blo 1056613 6019991 := bstep (se 1 (by rfl) ⟨4514993, by rfl⟩ : syracuseStep 6019991 = 9029987) B9029987
theorem B2382785 : Blo 1056613 2382785 := bstep (se 2 (by rfl) ⟨893544, by rfl⟩ : syracuseStep 2382785 = 1787089) B1787089
theorem B4021271 : Blo 1056613 4021271 := bstep (se 1 (by rfl) ⟨3015953, by rfl⟩ : syracuseStep 4021271 = 6031907) B6031907
theorem B2546711 : Blo 1056613 2546711 := bstep (se 1 (by rfl) ⟨1910033, by rfl⟩ : syracuseStep 2546711 = 3820067) B3820067
theorem B2383001 : Blo 1056613 2383001 := bstep (se 2 (by rfl) ⟨893625, by rfl⟩ : syracuseStep 2383001 = 1787251) B1787251
theorem B5364953 : Blo 1056613 5364953 := bstep (se 2 (by rfl) ⟨2011857, by rfl⟩ : syracuseStep 5364953 = 4023715) B4023715
theorem B2383091 : Blo 1056613 2383091 := bstep (se 1 (by rfl) ⟨1787318, by rfl⟩ : syracuseStep 2383091 = 3574637) B3574637
theorem B23223557 : Blo 1056613 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B2383127 : Blo 1056613 2383127 := bstep (se 1 (by rfl) ⟨1787345, by rfl⟩ : syracuseStep 2383127 = 3574691) B3574691
theorem B4578605 : Blo 1056613 4578605 := bstep (se 3 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 4578605 = 1716977) B1716977
theorem B2383307 : Blo 1056613 2383307 := bstep (se 1 (by rfl) ⟨1787480, by rfl⟩ : syracuseStep 2383307 = 3574961) B3574961
theorem B2383361 : Blo 1056613 2383361 := bstep (se 2 (by rfl) ⟨893760, by rfl⟩ : syracuseStep 2383361 = 1787521) B1787521
theorem B5791297 : Blo 1056613 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B1695449 : Blo 1056613 1695449 := bstep (se 2 (by rfl) ⟨635793, by rfl⟩ : syracuseStep 1695449 = 1271587) B1271587
theorem B2383577 : Blo 1056613 2383577 := bstep (se 2 (by rfl) ⟨893841, by rfl⟩ : syracuseStep 2383577 = 1787683) B1787683
theorem B2678579 : Blo 1056613 2678579 := bstep (se 1 (by rfl) ⟨2008934, by rfl⟩ : syracuseStep 2678579 = 4017869) B4017869
theorem B2383667 : Blo 1056613 2383667 := bstep (se 1 (by rfl) ⟨1787750, by rfl⟩ : syracuseStep 2383667 = 3575501) B3575501
theorem B2383703 : Blo 1056613 2383703 := bstep (se 1 (by rfl) ⟨1787777, by rfl⟩ : syracuseStep 2383703 = 3575555) B3575555
theorem B2416537 : Blo 1056613 2416537 := bstep (se 2 (by rfl) ⟨906201, by rfl⟩ : syracuseStep 2416537 = 1812403) B1812403
theorem B2711513 : Blo 1056613 2711513 := bstep (se 2 (by rfl) ⟨1016817, by rfl⟩ : syracuseStep 2711513 = 2033635) B2033635
theorem B2383883 : Blo 1056613 2383883 := bstep (se 1 (by rfl) ⟨1787912, by rfl⟩ : syracuseStep 2383883 = 3575825) B3575825
theorem B2383937 : Blo 1056613 2383937 := bstep (se 2 (by rfl) ⟨893976, by rfl⟩ : syracuseStep 2383937 = 1787953) B1787953
theorem B2547787 : Blo 1056613 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B88072343 : Blo 1056613 88072343 := bstep (se 1 (by rfl) ⟨66054257, by rfl⟩ : syracuseStep 88072343 = 132108515) B132108515
theorem B2416883 : Blo 1056613 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B4022531 : Blo 1056613 4022531 := bstep (se 1 (by rfl) ⟨3016898, by rfl⟩ : syracuseStep 4022531 = 6033797) B6033797
theorem B2384153 : Blo 1056613 2384153 := bstep (se 2 (by rfl) ⟨894057, by rfl⟩ : syracuseStep 2384153 = 1788115) B1788115
theorem B10314029 : Blo 1056613 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B2679115 : Blo 1056613 2679115 := bstep (se 1 (by rfl) ⟨2009336, by rfl⟩ : syracuseStep 2679115 = 4018673) B4018673
theorem B2384243 : Blo 1056613 2384243 := bstep (se 1 (by rfl) ⟨1788182, by rfl⟩ : syracuseStep 2384243 = 3576365) B3576365
theorem B4579715 : Blo 1056613 4579715 := bstep (se 1 (by rfl) ⟨3434786, by rfl⟩ : syracuseStep 4579715 = 6869573) B6869573
theorem B2384279 : Blo 1056613 2384279 := bstep (se 1 (by rfl) ⟨1788209, by rfl⟩ : syracuseStep 2384279 = 3576419) B3576419
theorem B4284875 : Blo 1056613 4284875 := bstep (se 1 (by rfl) ⟨3213656, by rfl⟩ : syracuseStep 4284875 = 6427313) B6427313
theorem B2679257 : Blo 1056613 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B2384459 : Blo 1056613 2384459 := bstep (se 1 (by rfl) ⟨1788344, by rfl⟩ : syracuseStep 2384459 = 3576689) B3576689
theorem B2384513 : Blo 1056613 2384513 := bstep (se 2 (by rfl) ⟨894192, by rfl⟩ : syracuseStep 2384513 = 1788385) B1788385
theorem B5366573 : Blo 1056613 5366573 := bstep (se 3 (by rfl) ⟨1006232, by rfl⟩ : syracuseStep 5366573 = 2012465) B2012465
theorem B2384729 : Blo 1056613 2384729 := bstep (se 2 (by rfl) ⟨894273, by rfl⟩ : syracuseStep 2384729 = 1788547) B1788547
theorem B2384819 : Blo 1056613 2384819 := bstep (se 1 (by rfl) ⟨1788614, by rfl⟩ : syracuseStep 2384819 = 3577229) B3577229
theorem B2384855 : Blo 1056613 2384855 := bstep (se 1 (by rfl) ⟨1788641, by rfl⟩ : syracuseStep 2384855 = 3577283) B3577283
theorem B2385035 : Blo 1056613 2385035 := bstep (se 1 (by rfl) ⟨1788776, by rfl⟩ : syracuseStep 2385035 = 3577553) B3577553
theorem B2385089 : Blo 1056613 2385089 := bstep (se 2 (by rfl) ⟨894408, by rfl⟩ : syracuseStep 2385089 = 1788817) B1788817
theorem B1271063 : Blo 1056613 1271063 := bstep (se 1 (by rfl) ⟨953297, by rfl⟩ : syracuseStep 1271063 = 1906595) B1906595
theorem B2680087 : Blo 1056613 2680087 := bstep (se 1 (by rfl) ⟨2010065, by rfl⟩ : syracuseStep 2680087 = 4020131) B4020131
theorem B2385305 : Blo 1056613 2385305 := bstep (se 2 (by rfl) ⟨894489, by rfl⟩ : syracuseStep 2385305 = 1788979) B1788979
theorem B2385395 : Blo 1056613 2385395 := bstep (se 1 (by rfl) ⟨1789046, by rfl⟩ : syracuseStep 2385395 = 3578093) B3578093
theorem B2385431 : Blo 1056613 2385431 := bstep (se 1 (by rfl) ⟨1789073, by rfl⟩ : syracuseStep 2385431 = 3578147) B3578147
theorem B1271371 : Blo 1056613 1271371 := bstep (se 1 (by rfl) ⟨953528, by rfl⟩ : syracuseStep 1271371 = 1907057) B1907057
theorem B2680523 : Blo 1056613 2680523 := bstep (se 1 (by rfl) ⟨2010392, by rfl⟩ : syracuseStep 2680523 = 4020785) B4020785
theorem B2385611 : Blo 1056613 2385611 := bstep (se 1 (by rfl) ⟨1789208, by rfl⟩ : syracuseStep 2385611 = 3578417) B3578417
theorem B2385665 : Blo 1056613 2385665 := bstep (se 2 (by rfl) ⟨894624, by rfl⟩ : syracuseStep 2385665 = 1789249) B1789249
theorem B6448913 : Blo 1056613 6448913 := bstep (se 2 (by rfl) ⟨2418342, by rfl⟩ : syracuseStep 6448913 = 4836685) B4836685
theorem B20309939 : Blo 1056613 20309939 := bstep (se 1 (by rfl) ⟨15232454, by rfl⟩ : syracuseStep 20309939 = 30464909) B30464909
theorem B2385881 : Blo 1056613 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B2385971 : Blo 1056613 2385971 := bstep (se 1 (by rfl) ⟨1789478, by rfl⟩ : syracuseStep 2385971 = 3578957) B3578957
theorem B2680897 : Blo 1056613 2680897 := bstep (se 2 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 2680897 = 2010673) B2010673
theorem B2386007 : Blo 1056613 2386007 := bstep (se 1 (by rfl) ⟨1789505, by rfl⟩ : syracuseStep 2386007 = 3579011) B3579011
theorem B4516019 : Blo 1056613 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B2287883 : Blo 1056613 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B2386187 : Blo 1056613 2386187 := bstep (se 1 (by rfl) ⟨1789640, by rfl⟩ : syracuseStep 2386187 = 3579281) B3579281
theorem B2386241 : Blo 1056613 2386241 := bstep (se 2 (by rfl) ⟨894840, by rfl⟩ : syracuseStep 2386241 = 1789681) B1789681
theorem B1632599 : Blo 1056613 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B2681495 : Blo 1056613 2681495 := bstep (se 1 (by rfl) ⟨2011121, by rfl⟩ : syracuseStep 2681495 = 4022243) B4022243
theorem B1338059 : Blo 1056613 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B3566429 : Blo 1056613 3566429 := bstep (se 3 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 3566429 = 1337411) B1337411
theorem B3009757 : Blo 1056613 3009757 := bstep (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) B1128659
theorem B4025645 : Blo 1056613 4025645 := bstep (se 3 (by rfl) ⟨754808, by rfl⟩ : syracuseStep 4025645 = 1509617) B1509617
theorem B1338763 : Blo 1056613 1338763 := bstep (se 1 (by rfl) ⟨1004072, by rfl⟩ : syracuseStep 1338763 = 2008145) B2008145
theorem B2682305 : Blo 1056613 2682305 := bstep (se 2 (by rfl) ⟨1005864, by rfl⟩ : syracuseStep 2682305 = 2011729) B2011729
theorem B5729753 : Blo 1056613 5729753 := bstep (se 2 (by rfl) ⟨2148657, by rfl⟩ : syracuseStep 5729753 = 4297315) B4297315
theorem B1339031 : Blo 1056613 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B1273495 : Blo 1056613 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2256779 : Blo 1056613 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B3567563 : Blo 1056613 3567563 := bstep (se 1 (by rfl) ⟨2675672, by rfl⟩ : syracuseStep 3567563 = 5351345) B5351345
theorem B2682841 : Blo 1056613 2682841 := bstep (se 2 (by rfl) ⟨1006065, by rfl⟩ : syracuseStep 2682841 = 2012131) B2012131
theorem B4026419 : Blo 1056613 4026419 := bstep (se 1 (by rfl) ⟨3019814, by rfl⟩ : syracuseStep 4026419 = 6039629) B6039629
theorem B7336037 : Blo 1056613 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B6025367 : Blo 1056613 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B3567833 : Blo 1056613 3567833 := bstep (se 2 (by rfl) ⟨1337937, by rfl⟩ : syracuseStep 3567833 = 2675875) B2675875
theorem B2257139 : Blo 1056613 2257139 := bstep (se 1 (by rfl) ⟨1692854, by rfl⟩ : syracuseStep 2257139 = 3385709) B3385709
theorem B6779153 : Blo 1056613 6779153 := bstep (se 2 (by rfl) ⟨2542182, by rfl⟩ : syracuseStep 6779153 = 5084365) B5084365
theorem B1339735 : Blo 1056613 1339735 := bstep (se 1 (by rfl) ⟨1004801, by rfl⟩ : syracuseStep 1339735 = 2009603) B2009603
theorem B3011033 : Blo 1056613 3011033 := bstep (se 2 (by rfl) ⟨1129137, by rfl⟩ : syracuseStep 3011033 = 2258275) B2258275
theorem B4518787 : Blo 1056613 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B3568535 : Blo 1056613 3568535 := bstep (se 1 (by rfl) ⟨2676401, by rfl⟩ : syracuseStep 3568535 = 5352803) B5352803
theorem B2683955 : Blo 1056613 2683955 := bstep (se 1 (by rfl) ⟨2012966, by rfl⟩ : syracuseStep 2683955 = 4025933) B4025933
theorem B1209463 : Blo 1056613 1209463 := bstep (se 1 (by rfl) ⟨907097, by rfl⟩ : syracuseStep 1209463 = 1814195) B1814195
theorem B2684249 : Blo 1056613 2684249 := bstep (se 2 (by rfl) ⟨1006593, by rfl⟩ : syracuseStep 2684249 = 2013187) B2013187
theorem B1504651 : Blo 1056613 1504651 := bstep (se 1 (by rfl) ⟨1128488, by rfl⟩ : syracuseStep 1504651 = 2256977) B2256977
theorem B3569075 : Blo 1056613 3569075 := bstep (se 1 (by rfl) ⟨2676806, by rfl⟩ : syracuseStep 3569075 = 5353613) B5353613
theorem B8713763 : Blo 1056613 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B3569345 : Blo 1056613 3569345 := bstep (se 2 (by rfl) ⟨1338504, by rfl⟩ : syracuseStep 3569345 = 2677009) B2677009
theorem B15267629 : Blo 1056613 15267629 := bstep (se 3 (by rfl) ⟨2862680, by rfl⟩ : syracuseStep 15267629 = 5725361) B5725361
theorem B4519745 : Blo 1056613 4519745 := bstep (se 2 (by rfl) ⟨1694904, by rfl⟩ : syracuseStep 4519745 = 3389809) B3389809
theorem B18315109 : Blo 1056613 18315109 := bstep (se 4 (by rfl) ⟨1717041, by rfl⟩ : syracuseStep 18315109 = 3434083) B3434083
theorem B17200997 : Blo 1056613 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B1341451 : Blo 1056613 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B6027281 : Blo 1056613 6027281 := bstep (se 2 (by rfl) ⟨2260230, by rfl⟩ : syracuseStep 6027281 = 4520461) B4520461
theorem B4290583 : Blo 1056613 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B3012673 : Blo 1056613 3012673 := bstep (se 2 (by rfl) ⟨1129752, by rfl⟩ : syracuseStep 3012673 = 2259505) B2259505
theorem B11434115 : Blo 1056613 11434115 := bstep (se 1 (by rfl) ⟨8575586, by rfl⟩ : syracuseStep 11434115 = 17151173) B17151173
theorem B8026289 : Blo 1056613 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B2259137 : Blo 1056613 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B3569885 : Blo 1056613 3569885 := bstep (se 3 (by rfl) ⟨669353, by rfl⟩ : syracuseStep 3569885 = 1338707) B1338707
theorem B10877285 : Blo 1056613 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B1505881 : Blo 1056613 1505881 := bstep (se 2 (by rfl) ⟨564705, by rfl⟩ : syracuseStep 1505881 = 1129411) B1129411
theorem B8026775 : Blo 1056613 8026775 := bstep (se 1 (by rfl) ⟨6020081, by rfl⟩ : syracuseStep 8026775 = 12040163) B12040163
theorem B20380517 : Blo 1056613 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B11598709 : Blo 1056613 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B2259991 : Blo 1056613 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B15465653 : Blo 1056613 15465653 := bstep (se 5 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 15465653 = 1449905) B1449905
theorem B3571019 : Blo 1056613 3571019 := bstep (se 1 (by rfl) ⟨2678264, by rfl⟩ : syracuseStep 3571019 = 5356529) B5356529
theorem B4521419 : Blo 1056613 4521419 := bstep (se 1 (by rfl) ⟨3391064, by rfl⟩ : syracuseStep 4521419 = 6782129) B6782129
theorem B1506775 : Blo 1056613 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B3571289 : Blo 1056613 3571289 := bstep (se 2 (by rfl) ⟨1339233, by rfl⟩ : syracuseStep 3571289 = 2678467) B2678467
theorem B5078659 : Blo 1056613 5078659 := bstep (se 1 (by rfl) ⟨3808994, by rfl⟩ : syracuseStep 5078659 = 7617989) B7617989
theorem B3014347 : Blo 1056613 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B5439449 : Blo 1056613 5439449 := bstep (se 2 (by rfl) ⟨2039793, by rfl⟩ : syracuseStep 5439449 = 4079587) B4079587
theorem B3014621 : Blo 1056613 3014621 := bstep (se 3 (by rfl) ⟨565241, by rfl⟩ : syracuseStep 3014621 = 1130483) B1130483
theorem B2261051 : Blo 1056613 2261051 := bstep (se 1 (by rfl) ⟨1695788, by rfl⟩ : syracuseStep 2261051 = 3391577) B3391577
theorem B1507447 : Blo 1056613 1507447 := bstep (se 1 (by rfl) ⟨1130585, by rfl⟩ : syracuseStep 1507447 = 2261171) B2261171
theorem B3572153 : Blo 1056613 3572153 := bstep (se 2 (by rfl) ⟨1339557, by rfl⟩ : syracuseStep 3572153 = 2679115) B2679115
theorem B5079581 : Blo 1056613 5079581 := bstep (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) B1904843
theorem B2261803 : Blo 1056613 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B1508267 : Blo 1056613 1508267 := bstep (se 1 (by rfl) ⟨1131200, by rfl⟩ : syracuseStep 1508267 = 2262401) B2262401
theorem B3572747 : Blo 1056613 3572747 := bstep (se 1 (by rfl) ⟨2679560, by rfl⟩ : syracuseStep 3572747 = 5359121) B5359121
theorem B3572855 : Blo 1056613 3572855 := bstep (se 1 (by rfl) ⟨2679641, by rfl⟩ : syracuseStep 3572855 = 5359283) B5359283
theorem B3016055 : Blo 1056613 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B10159505 : Blo 1056613 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B4294073 : Blo 1056613 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B3573449 : Blo 1056613 3573449 := bstep (se 2 (by rfl) ⟨1340043, by rfl⟩ : syracuseStep 3573449 = 2680087) B2680087
theorem B3672125 : Blo 1056613 3672125 := bstep (se 3 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 3672125 = 1377047) B1377047
theorem B4524119 : Blo 1056613 4524119 := bstep (se 1 (by rfl) ⟨3393089, by rfl⟩ : syracuseStep 4524119 = 6786179) B6786179
theorem B1509691 : Blo 1056613 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B3017047 : Blo 1056613 3017047 := bstep (se 1 (by rfl) ⟨2262785, by rfl⟩ : syracuseStep 3017047 = 4525571) B4525571
theorem B3574151 : Blo 1056613 3574151 := bstep (se 1 (by rfl) ⟨2680613, by rfl⟩ : syracuseStep 3574151 = 5361227) B5361227
theorem B1608379 : Blo 1056613 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B3574529 : Blo 1056613 3574529 := bstep (se 2 (by rfl) ⟨1340448, by rfl⟩ : syracuseStep 3574529 = 2680897) B2680897
theorem B9046799 : Blo 1056613 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B2263955 : Blo 1056613 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B5082041 : Blo 1056613 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B10161197 : Blo 1056613 10161197 := bstep (se 3 (by rfl) ⟨1905224, by rfl⟩ : syracuseStep 10161197 = 3810449) B3810449
theorem B8031635 : Blo 1056613 8031635 := bstep (se 1 (by rfl) ⟨6023726, by rfl⟩ : syracuseStep 8031635 = 12047453) B12047453
theorem B3575339 : Blo 1056613 3575339 := bstep (se 1 (by rfl) ⟨2681504, by rfl⟩ : syracuseStep 3575339 = 5363009) B5363009
theorem B3018539 : Blo 1056613 3018539 := bstep (se 1 (by rfl) ⟨2263904, by rfl⟩ : syracuseStep 3018539 = 4527809) B4527809
theorem B18321227 : Blo 1056613 18321227 := bstep (se 1 (by rfl) ⟨13740920, by rfl⟩ : syracuseStep 18321227 = 27481841) B27481841
theorem B1904519 : Blo 1056613 1904519 := bstep (se 1 (by rfl) ⟨1428389, by rfl⟩ : syracuseStep 1904519 = 2856779) B2856779
theorem B3182635 : Blo 1056613 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B4296941 : Blo 1056613 4296941 := bstep (se 3 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 4296941 = 1611353) B1611353
theorem B6427025 : Blo 1056613 6427025 := bstep (se 2 (by rfl) ⟨2410134, by rfl⟩ : syracuseStep 6427025 = 4820269) B4820269
theorem B10162579 : Blo 1056613 10162579 := bstep (se 1 (by rfl) ⟨7621934, by rfl⟩ : syracuseStep 10162579 = 15243869) B15243869
theorem B4133267 : Blo 1056613 4133267 := bstep (se 1 (by rfl) ⟨3099950, by rfl⟩ : syracuseStep 4133267 = 6199901) B6199901
theorem B1905211 : Blo 1056613 1905211 := bstep (se 1 (by rfl) ⟨1428908, by rfl⟩ : syracuseStep 1905211 = 2857817) B2857817
theorem B3576635 : Blo 1056613 3576635 := bstep (se 1 (by rfl) ⟨2682476, by rfl⟩ : syracuseStep 3576635 = 5364953) B5364953
theorem B3052403 : Blo 1056613 3052403 := bstep (se 1 (by rfl) ⟨2289302, by rfl⟩ : syracuseStep 3052403 = 4578605) B4578605
theorem B3019655 : Blo 1056613 3019655 := bstep (se 1 (by rfl) ⟨2264741, by rfl⟩ : syracuseStep 3019655 = 4529483) B4529483
theorem B3019837 : Blo 1056613 3019837 := bstep (se 3 (by rfl) ⟨566219, by rfl⟩ : syracuseStep 3019837 = 1132439) B1132439
theorem B17143073 : Blo 1056613 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B3577121 : Blo 1056613 3577121 := bstep (se 2 (by rfl) ⟨1341420, by rfl⟩ : syracuseStep 3577121 = 2682841) B2682841
theorem B6034823 : Blo 1056613 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B3020179 : Blo 1056613 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B6428089 : Blo 1056613 6428089 := bstep (se 2 (by rfl) ⟨2410533, by rfl⟩ : syracuseStep 6428089 = 4821067) B4821067
theorem B4527569 : Blo 1056613 4527569 := bstep (se 2 (by rfl) ⟨1697838, by rfl⟩ : syracuseStep 4527569 = 3395677) B3395677
theorem B3216955 : Blo 1056613 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B3053143 : Blo 1056613 3053143 := bstep (se 1 (by rfl) ⟨2289857, by rfl⟩ : syracuseStep 3053143 = 4579715) B4579715
theorem B2856583 : Blo 1056613 2856583 := bstep (se 1 (by rfl) ⟨2142437, by rfl⟩ : syracuseStep 2856583 = 4284875) B4284875
theorem B3577715 : Blo 1056613 3577715 := bstep (se 1 (by rfl) ⟨2683286, by rfl⟩ : syracuseStep 3577715 = 5366573) B5366573
theorem B6101021 : Blo 1056613 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B29006093 : Blo 1056613 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B4299275 : Blo 1056613 4299275 := bstep (se 1 (by rfl) ⟨3224456, by rfl⟩ : syracuseStep 4299275 = 6448913) B6448913
theorem B6036029 : Blo 1056613 6036029 := bstep (se 3 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 6036029 = 2263511) B2263511
theorem B8591939 : Blo 1056613 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B13539959 : Blo 1056613 13539959 := bstep (se 1 (by rfl) ⟨10154969, by rfl⟩ : syracuseStep 13539959 = 20309939) B20309939
theorem B1088399 : Blo 1056613 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B5086097 : Blo 1056613 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B18095237 : Blo 1056613 18095237 := bstep (se 4 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 18095237 = 3392857) B3392857
theorem B2006201 : Blo 1056613 2006201 := bstep (se 2 (by rfl) ⟨752325, by rfl⟩ : syracuseStep 2006201 = 1504651) B1504651
theorem B68721965 : Blo 1056613 68721965 := bstep (se 3 (by rfl) ⟨12885368, by rfl⟩ : syracuseStep 68721965 = 25770737) B25770737
theorem B13573889 : Blo 1056613 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B24420145 : Blo 1056613 24420145 := bstep (se 2 (by rfl) ⟨9157554, by rfl⟩ : syracuseStep 24420145 = 18315109) B18315109
theorem B1056647 : Blo 1056613 1056647 := bstep (se 1 (by rfl) ⟨792485, by rfl⟩ : syracuseStep 1056647 = 1584971) B1584971
theorem B1056655 : Blo 1056613 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B1056699 : Blo 1056613 1056699 := bstep (se 1 (by rfl) ⟨792524, by rfl⟩ : syracuseStep 1056699 = 1585049) B1585049
theorem B1056775 : Blo 1056613 1056775 := bstep (se 1 (by rfl) ⟨792581, by rfl⟩ : syracuseStep 1056775 = 1585163) B1585163
theorem B1056783 : Blo 1056613 1056783 := bstep (se 1 (by rfl) ⟨792587, by rfl⟩ : syracuseStep 1056783 = 1585175) B1585175
theorem B1056827 : Blo 1056613 1056827 := bstep (se 1 (by rfl) ⟨792620, by rfl⟩ : syracuseStep 1056827 = 1585241) B1585241
theorem B4890691 : Blo 1056613 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B1056903 : Blo 1056613 1056903 := bstep (se 1 (by rfl) ⟨792677, by rfl⟩ : syracuseStep 1056903 = 1585355) B1585355
theorem B1056911 : Blo 1056613 1056911 := bstep (se 1 (by rfl) ⟨792683, by rfl⟩ : syracuseStep 1056911 = 1585367) B1585367
theorem B1056955 : Blo 1056613 1056955 := bstep (se 1 (by rfl) ⟨792716, by rfl⟩ : syracuseStep 1056955 = 1585433) B1585433
theorem B1057031 : Blo 1056613 1057031 := bstep (se 1 (by rfl) ⟨792773, by rfl⟩ : syracuseStep 1057031 = 1585547) B1585547
theorem B1057039 : Blo 1056613 1057039 := bstep (se 1 (by rfl) ⟨792779, by rfl⟩ : syracuseStep 1057039 = 1585559) B1585559
theorem B1057083 : Blo 1056613 1057083 := bstep (se 1 (by rfl) ⟨792812, by rfl⟩ : syracuseStep 1057083 = 1585625) B1585625
theorem B2007355 : Blo 1056613 2007355 := bstep (se 1 (by rfl) ⟨1505516, by rfl⟩ : syracuseStep 2007355 = 3011033) B3011033
theorem B1909111 : Blo 1056613 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B1057159 : Blo 1056613 1057159 := bstep (se 1 (by rfl) ⟨792869, by rfl⟩ : syracuseStep 1057159 = 1585739) B1585739
theorem B1057167 : Blo 1056613 1057167 := bstep (se 1 (by rfl) ⟨792875, by rfl⟩ : syracuseStep 1057167 = 1585751) B1585751
theorem B1057211 : Blo 1056613 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B1057287 : Blo 1056613 1057287 := bstep (se 1 (by rfl) ⟨792965, by rfl⟩ : syracuseStep 1057287 = 1585931) B1585931
theorem B1057295 : Blo 1056613 1057295 := bstep (se 1 (by rfl) ⟨792971, by rfl⟩ : syracuseStep 1057295 = 1585943) B1585943
theorem B3219983 : Blo 1056613 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B1057339 : Blo 1056613 1057339 := bstep (se 1 (by rfl) ⟨793004, by rfl⟩ : syracuseStep 1057339 = 1586009) B1586009
theorem B1057415 : Blo 1056613 1057415 := bstep (se 1 (by rfl) ⟨793061, by rfl⟩ : syracuseStep 1057415 = 1586123) B1586123
theorem B1057423 : Blo 1056613 1057423 := bstep (se 1 (by rfl) ⟨793067, by rfl⟩ : syracuseStep 1057423 = 1586135) B1586135
theorem B1450667 : Blo 1056613 1450667 := bstep (se 1 (by rfl) ⟨1088000, by rfl⟩ : syracuseStep 1450667 = 2176001) B2176001
theorem B1057467 : Blo 1056613 1057467 := bstep (se 1 (by rfl) ⟨793100, by rfl⟩ : syracuseStep 1057467 = 1586201) B1586201
theorem B9642725 : Blo 1056613 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B1057543 : Blo 1056613 1057543 := bstep (se 1 (by rfl) ⟨793157, by rfl⟩ : syracuseStep 1057543 = 1586315) B1586315
theorem B1057551 : Blo 1056613 1057551 := bstep (se 1 (by rfl) ⟨793163, by rfl⟩ : syracuseStep 1057551 = 1586327) B1586327
theorem B2007841 : Blo 1056613 2007841 := bstep (se 2 (by rfl) ⟨752940, by rfl⟩ : syracuseStep 2007841 = 1505881) B1505881
theorem B1057595 : Blo 1056613 1057595 := bstep (se 1 (by rfl) ⟨793196, by rfl⟩ : syracuseStep 1057595 = 1586393) B1586393
theorem B1057671 : Blo 1056613 1057671 := bstep (se 1 (by rfl) ⟨793253, by rfl⟩ : syracuseStep 1057671 = 1586507) B1586507
theorem B1188751 : Blo 1056613 1188751 := bstep (se 1 (by rfl) ⟨891563, by rfl⟩ : syracuseStep 1188751 = 1783127) B1783127
theorem B1057679 : Blo 1056613 1057679 := bstep (se 1 (by rfl) ⟨793259, by rfl⟩ : syracuseStep 1057679 = 1586519) B1586519
theorem B1057723 : Blo 1056613 1057723 := bstep (se 1 (by rfl) ⟨793292, by rfl⟩ : syracuseStep 1057723 = 1586585) B1586585
theorem B1057799 : Blo 1056613 1057799 := bstep (se 1 (by rfl) ⟨793349, by rfl⟩ : syracuseStep 1057799 = 1586699) B1586699
theorem B1057807 : Blo 1056613 1057807 := bstep (se 1 (by rfl) ⟨793355, by rfl⟩ : syracuseStep 1057807 = 1586711) B1586711
theorem B5809175 : Blo 1056613 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B1057851 : Blo 1056613 1057851 := bstep (se 1 (by rfl) ⟨793388, by rfl⟩ : syracuseStep 1057851 = 1586777) B1586777
theorem B1057927 : Blo 1056613 1057927 := bstep (se 1 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 1057927 = 1586891) B1586891
theorem B1057935 : Blo 1056613 1057935 := bstep (se 1 (by rfl) ⟨793451, by rfl⟩ : syracuseStep 1057935 = 1586903) B1586903
theorem B1057979 : Blo 1056613 1057979 := bstep (se 1 (by rfl) ⟨793484, by rfl⟩ : syracuseStep 1057979 = 1586969) B1586969
theorem B1058055 : Blo 1056613 1058055 := bstep (se 1 (by rfl) ⟨793541, by rfl⟩ : syracuseStep 1058055 = 1587083) B1587083
theorem B1058063 : Blo 1056613 1058063 := bstep (se 1 (by rfl) ⟨793547, by rfl⟩ : syracuseStep 1058063 = 1587095) B1587095
theorem B1058107 : Blo 1056613 1058107 := bstep (se 1 (by rfl) ⟨793580, by rfl⟩ : syracuseStep 1058107 = 1587161) B1587161
theorem B1189255 : Blo 1056613 1189255 := bstep (se 1 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 1189255 = 1783883) B1783883
theorem B21702023 : Blo 1056613 21702023 := bstep (se 1 (by rfl) ⟨16276517, by rfl⟩ : syracuseStep 21702023 = 32553035) B32553035
theorem B1058183 : Blo 1056613 1058183 := bstep (se 1 (by rfl) ⟨793637, by rfl⟩ : syracuseStep 1058183 = 1587275) B1587275
theorem B1058191 : Blo 1056613 1058191 := bstep (se 1 (by rfl) ⟨793643, by rfl⟩ : syracuseStep 1058191 = 1587287) B1587287
theorem B1058235 : Blo 1056613 1058235 := bstep (se 1 (by rfl) ⟨793676, by rfl⟩ : syracuseStep 1058235 = 1587353) B1587353
theorem B5350859 : Blo 1056613 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B1058311 : Blo 1056613 1058311 := bstep (se 1 (by rfl) ⟨793733, by rfl⟩ : syracuseStep 1058311 = 1587467) B1587467
theorem B1058319 : Blo 1056613 1058319 := bstep (se 1 (by rfl) ⟨793739, by rfl⟩ : syracuseStep 1058319 = 1587479) B1587479
theorem B1189435 : Blo 1056613 1189435 := bstep (se 1 (by rfl) ⟨892076, by rfl⟩ : syracuseStep 1189435 = 1784153) B1784153
theorem B1058363 : Blo 1056613 1058363 := bstep (se 1 (by rfl) ⟨793772, by rfl⟩ : syracuseStep 1058363 = 1587545) B1587545
theorem B1058439 : Blo 1056613 1058439 := bstep (se 1 (by rfl) ⟨793829, by rfl⟩ : syracuseStep 1058439 = 1587659) B1587659
theorem B1058447 : Blo 1056613 1058447 := bstep (se 1 (by rfl) ⟨793835, by rfl⟩ : syracuseStep 1058447 = 1587671) B1587671
theorem B1058491 : Blo 1056613 1058491 := bstep (se 1 (by rfl) ⟨793868, by rfl⟩ : syracuseStep 1058491 = 1587737) B1587737
theorem B1058567 : Blo 1056613 1058567 := bstep (se 1 (by rfl) ⟨793925, by rfl⟩ : syracuseStep 1058567 = 1587851) B1587851
theorem B5351183 : Blo 1056613 5351183 := bstep (se 1 (by rfl) ⟨4013387, by rfl⟩ : syracuseStep 5351183 = 8026775) B8026775
theorem B1058575 : Blo 1056613 1058575 := bstep (se 1 (by rfl) ⟨793931, by rfl⟩ : syracuseStep 1058575 = 1587863) B1587863
theorem B1058619 : Blo 1056613 1058619 := bstep (se 1 (by rfl) ⟨793964, by rfl⟩ : syracuseStep 1058619 = 1587929) B1587929
theorem B1058695 : Blo 1056613 1058695 := bstep (se 1 (by rfl) ⟨794021, by rfl⟩ : syracuseStep 1058695 = 1588043) B1588043
theorem B1058703 : Blo 1056613 1058703 := bstep (se 1 (by rfl) ⟨794027, by rfl⟩ : syracuseStep 1058703 = 1588055) B1588055
theorem B1058747 : Blo 1056613 1058747 := bstep (se 1 (by rfl) ⟨794060, by rfl⟩ : syracuseStep 1058747 = 1588121) B1588121
theorem B2009033 : Blo 1056613 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B1058823 : Blo 1056613 1058823 := bstep (se 1 (by rfl) ⟨794117, by rfl⟩ : syracuseStep 1058823 = 1588235) B1588235
theorem B1189903 : Blo 1056613 1189903 := bstep (se 1 (by rfl) ⟨892427, by rfl⟩ : syracuseStep 1189903 = 1784855) B1784855
theorem B1058831 : Blo 1056613 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B1058875 : Blo 1056613 1058875 := bstep (se 1 (by rfl) ⟨794156, by rfl⟩ : syracuseStep 1058875 = 1588313) B1588313
theorem B12888197 : Blo 1056613 12888197 := bstep (se 4 (by rfl) ⟨1208268, by rfl⟩ : syracuseStep 12888197 = 2416537) B2416537
theorem B1058951 : Blo 1056613 1058951 := bstep (se 1 (by rfl) ⟨794213, by rfl⟩ : syracuseStep 1058951 = 1588427) B1588427
theorem B1058959 : Blo 1056613 1058959 := bstep (se 1 (by rfl) ⟨794219, by rfl⟩ : syracuseStep 1058959 = 1588439) B1588439
theorem B1059003 : Blo 1056613 1059003 := bstep (se 1 (by rfl) ⟨794252, by rfl⟩ : syracuseStep 1059003 = 1588505) B1588505
theorem B1059079 : Blo 1056613 1059079 := bstep (se 1 (by rfl) ⟨794309, by rfl⟩ : syracuseStep 1059079 = 1588619) B1588619
theorem B1059087 : Blo 1056613 1059087 := bstep (se 1 (by rfl) ⟨794315, by rfl⟩ : syracuseStep 1059087 = 1588631) B1588631
theorem B1059131 : Blo 1056613 1059131 := bstep (se 1 (by rfl) ⟨794348, by rfl⟩ : syracuseStep 1059131 = 1588697) B1588697
theorem B1059207 : Blo 1056613 1059207 := bstep (se 1 (by rfl) ⟨794405, by rfl⟩ : syracuseStep 1059207 = 1588811) B1588811
theorem B1059215 : Blo 1056613 1059215 := bstep (se 1 (by rfl) ⟨794411, by rfl⟩ : syracuseStep 1059215 = 1588823) B1588823
theorem B1059259 : Blo 1056613 1059259 := bstep (se 1 (by rfl) ⟨794444, by rfl⟩ : syracuseStep 1059259 = 1588889) B1588889
theorem B1812937 : Blo 1056613 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B1190407 : Blo 1056613 1190407 := bstep (se 1 (by rfl) ⟨892805, by rfl⟩ : syracuseStep 1190407 = 1785611) B1785611
theorem B1059335 : Blo 1056613 1059335 := bstep (se 1 (by rfl) ⟨794501, by rfl⟩ : syracuseStep 1059335 = 1589003) B1589003
theorem B1059343 : Blo 1056613 1059343 := bstep (se 1 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 1059343 = 1589015) B1589015
theorem B1059387 : Blo 1056613 1059387 := bstep (se 1 (by rfl) ⟨794540, by rfl⟩ : syracuseStep 1059387 = 1589081) B1589081
theorem B1059463 : Blo 1056613 1059463 := bstep (se 1 (by rfl) ⟨794597, by rfl⟩ : syracuseStep 1059463 = 1589195) B1589195
theorem B1059471 : Blo 1056613 1059471 := bstep (se 1 (by rfl) ⟨794603, by rfl⟩ : syracuseStep 1059471 = 1589207) B1589207
theorem B2009747 : Blo 1056613 2009747 := bstep (se 1 (by rfl) ⟨1507310, by rfl⟩ : syracuseStep 2009747 = 3014621) B3014621
theorem B2009785 : Blo 1056613 2009785 := bstep (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) B1507339
theorem B1190587 : Blo 1056613 1190587 := bstep (se 1 (by rfl) ⟨892940, by rfl⟩ : syracuseStep 1190587 = 1785881) B1785881
theorem B1059515 : Blo 1056613 1059515 := bstep (se 1 (by rfl) ⟨794636, by rfl⟩ : syracuseStep 1059515 = 1589273) B1589273
theorem B1059591 : Blo 1056613 1059591 := bstep (se 1 (by rfl) ⟨794693, by rfl⟩ : syracuseStep 1059591 = 1589387) B1589387
theorem B1059599 : Blo 1056613 1059599 := bstep (se 1 (by rfl) ⟨794699, by rfl⟩ : syracuseStep 1059599 = 1589399) B1589399
theorem B69708559 : Blo 1056613 69708559 := bstep (se 1 (by rfl) ⟨52281419, by rfl⟩ : syracuseStep 69708559 = 104562839) B104562839
theorem B12888881 : Blo 1056613 12888881 := bstep (se 2 (by rfl) ⟨4833330, by rfl⟩ : syracuseStep 12888881 = 9666661) B9666661
theorem B1059643 : Blo 1056613 1059643 := bstep (se 1 (by rfl) ⟨794732, by rfl⟩ : syracuseStep 1059643 = 1589465) B1589465
theorem B1059719 : Blo 1056613 1059719 := bstep (se 1 (by rfl) ⟨794789, by rfl⟩ : syracuseStep 1059719 = 1589579) B1589579
theorem B1059727 : Blo 1056613 1059727 := bstep (se 1 (by rfl) ⟨794795, by rfl⟩ : syracuseStep 1059727 = 1589591) B1589591
theorem B1059771 : Blo 1056613 1059771 := bstep (se 1 (by rfl) ⟨794828, by rfl⟩ : syracuseStep 1059771 = 1589657) B1589657
theorem B1059847 : Blo 1056613 1059847 := bstep (se 1 (by rfl) ⟨794885, by rfl⟩ : syracuseStep 1059847 = 1589771) B1589771
theorem B1059855 : Blo 1056613 1059855 := bstep (se 1 (by rfl) ⟨794891, by rfl⟩ : syracuseStep 1059855 = 1589783) B1589783
theorem B1059899 : Blo 1056613 1059899 := bstep (se 1 (by rfl) ⟨794924, by rfl⟩ : syracuseStep 1059899 = 1589849) B1589849
theorem B1059975 : Blo 1056613 1059975 := bstep (se 1 (by rfl) ⟨794981, by rfl⟩ : syracuseStep 1059975 = 1589963) B1589963
theorem B1191055 : Blo 1056613 1191055 := bstep (se 1 (by rfl) ⟨893291, by rfl⟩ : syracuseStep 1191055 = 1786583) B1786583
theorem B1059983 : Blo 1056613 1059983 := bstep (se 1 (by rfl) ⟨794987, by rfl⟩ : syracuseStep 1059983 = 1589975) B1589975
theorem B1060027 : Blo 1056613 1060027 := bstep (se 1 (by rfl) ⟨795020, by rfl⟩ : syracuseStep 1060027 = 1590041) B1590041
theorem B5352641 : Blo 1056613 5352641 := bstep (se 2 (by rfl) ⟨2007240, by rfl⟩ : syracuseStep 5352641 = 4014481) B4014481
theorem B1060103 : Blo 1056613 1060103 := bstep (se 1 (by rfl) ⟨795077, by rfl⟩ : syracuseStep 1060103 = 1590155) B1590155
theorem B1060111 : Blo 1056613 1060111 := bstep (se 1 (by rfl) ⟨795083, by rfl⟩ : syracuseStep 1060111 = 1590167) B1590167
theorem B3058987 : Blo 1056613 3058987 := bstep (se 1 (by rfl) ⟨2294240, by rfl⟩ : syracuseStep 3058987 = 4588481) B4588481
theorem B9055547 : Blo 1056613 9055547 := bstep (se 1 (by rfl) ⟨6791660, by rfl⟩ : syracuseStep 9055547 = 13583321) B13583321
theorem B1060155 : Blo 1056613 1060155 := bstep (se 1 (by rfl) ⟨795116, by rfl⟩ : syracuseStep 1060155 = 1590233) B1590233
theorem B1060231 : Blo 1056613 1060231 := bstep (se 1 (by rfl) ⟨795173, by rfl⟩ : syracuseStep 1060231 = 1590347) B1590347
theorem B1060239 : Blo 1056613 1060239 := bstep (se 1 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 1060239 = 1590359) B1590359
theorem B3386809 : Blo 1056613 3386809 := bstep (se 2 (by rfl) ⟨1270053, by rfl⟩ : syracuseStep 3386809 = 2540107) B2540107
theorem B1060283 : Blo 1056613 1060283 := bstep (se 1 (by rfl) ⟨795212, by rfl⟩ : syracuseStep 1060283 = 1590425) B1590425
theorem B1060359 : Blo 1056613 1060359 := bstep (se 1 (by rfl) ⟨795269, by rfl⟩ : syracuseStep 1060359 = 1590539) B1590539
theorem B1060367 : Blo 1056613 1060367 := bstep (se 1 (by rfl) ⟨795275, by rfl⟩ : syracuseStep 1060367 = 1590551) B1590551
theorem B1060411 : Blo 1056613 1060411 := bstep (se 1 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 1060411 = 1590617) B1590617
theorem B1191559 : Blo 1056613 1191559 := bstep (se 1 (by rfl) ⟨893669, by rfl⟩ : syracuseStep 1191559 = 1787339) B1787339
theorem B1060487 : Blo 1056613 1060487 := bstep (se 1 (by rfl) ⟨795365, by rfl⟩ : syracuseStep 1060487 = 1590731) B1590731
theorem B1060495 : Blo 1056613 1060495 := bstep (se 1 (by rfl) ⟨795371, by rfl⟩ : syracuseStep 1060495 = 1590743) B1590743
theorem B1060539 : Blo 1056613 1060539 := bstep (se 1 (by rfl) ⟨795404, by rfl⟩ : syracuseStep 1060539 = 1590809) B1590809
theorem B1584953 : Blo 1056613 1584953 := bstep (se 2 (by rfl) ⟨594357, by rfl⟩ : syracuseStep 1584953 = 1188715) B1188715
theorem B1191739 : Blo 1056613 1191739 := bstep (se 1 (by rfl) ⟨893804, by rfl⟩ : syracuseStep 1191739 = 1787609) B1787609
theorem B5091131 : Blo 1056613 5091131 := bstep (se 1 (by rfl) ⟨3818348, by rfl⟩ : syracuseStep 5091131 = 7636697) B7636697
theorem B1585031 : Blo 1056613 1585031 := bstep (se 1 (by rfl) ⟨1188773, by rfl⟩ : syracuseStep 1585031 = 2377547) B2377547
theorem B3387271 : Blo 1056613 3387271 := bstep (se 1 (by rfl) ⟨2540453, by rfl⟩ : syracuseStep 3387271 = 5080907) B5080907
theorem B1585067 : Blo 1056613 1585067 := bstep (se 1 (by rfl) ⟨1188800, by rfl⟩ : syracuseStep 1585067 = 2377601) B2377601
theorem B1585097 : Blo 1056613 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B70660117 : Blo 1056613 70660117 := bstep (se 6 (by rfl) ⟨1656096, by rfl⟩ : syracuseStep 70660117 = 3312193) B3312193
theorem B1585211 : Blo 1056613 1585211 := bstep (se 1 (by rfl) ⟨1188908, by rfl⟩ : syracuseStep 1585211 = 2377817) B2377817
theorem B1585271 : Blo 1056613 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B1585295 : Blo 1056613 1585295 := bstep (se 1 (by rfl) ⟨1188971, by rfl⟩ : syracuseStep 1585295 = 2377943) B2377943
theorem B1585337 : Blo 1056613 1585337 := bstep (se 2 (by rfl) ⟨594501, by rfl⟩ : syracuseStep 1585337 = 1189003) B1189003
theorem B2863289 : Blo 1056613 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B6435073 : Blo 1056613 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B6205697 : Blo 1056613 6205697 := bstep (se 2 (by rfl) ⟨2327136, by rfl⟩ : syracuseStep 6205697 = 4654273) B4654273
theorem B1585415 : Blo 1056613 1585415 := bstep (se 1 (by rfl) ⟨1189061, by rfl⟩ : syracuseStep 1585415 = 2378123) B2378123
theorem B1192207 : Blo 1056613 1192207 := bstep (se 1 (by rfl) ⟨894155, by rfl⟩ : syracuseStep 1192207 = 1788311) B1788311
theorem B1585451 : Blo 1056613 1585451 := bstep (se 1 (by rfl) ⟨1189088, by rfl⟩ : syracuseStep 1585451 = 2378177) B2378177
theorem B1585481 : Blo 1056613 1585481 := bstep (se 2 (by rfl) ⟨594555, by rfl⟩ : syracuseStep 1585481 = 1189111) B1189111
theorem B5091731 : Blo 1056613 5091731 := bstep (se 1 (by rfl) ⟨3818798, by rfl⟩ : syracuseStep 5091731 = 7637597) B7637597
theorem B1585595 : Blo 1056613 1585595 := bstep (se 1 (by rfl) ⟨1189196, by rfl⟩ : syracuseStep 1585595 = 2378393) B2378393
theorem B5353937 : Blo 1056613 5353937 := bstep (se 2 (by rfl) ⟨2007726, by rfl⟩ : syracuseStep 5353937 = 4015453) B4015453
theorem B1585655 : Blo 1056613 1585655 := bstep (se 1 (by rfl) ⟨1189241, by rfl⟩ : syracuseStep 1585655 = 2378483) B2378483
theorem B1585679 : Blo 1056613 1585679 := bstep (se 1 (by rfl) ⟨1189259, by rfl⟩ : syracuseStep 1585679 = 2378519) B2378519
theorem B2011691 : Blo 1056613 2011691 := bstep (se 1 (by rfl) ⟨1508768, by rfl⟩ : syracuseStep 2011691 = 3017537) B3017537
theorem B1585721 : Blo 1056613 1585721 := bstep (se 2 (by rfl) ⟨594645, by rfl⟩ : syracuseStep 1585721 = 1189291) B1189291
theorem B1585799 : Blo 1056613 1585799 := bstep (se 1 (by rfl) ⟨1189349, by rfl⟩ : syracuseStep 1585799 = 2378699) B2378699
theorem B1585835 : Blo 1056613 1585835 := bstep (se 1 (by rfl) ⟨1189376, by rfl⟩ : syracuseStep 1585835 = 2378753) B2378753
theorem B1585865 : Blo 1056613 1585865 := bstep (se 2 (by rfl) ⟨594699, by rfl⟩ : syracuseStep 1585865 = 1189399) B1189399
theorem B1192711 : Blo 1056613 1192711 := bstep (se 1 (by rfl) ⟨894533, by rfl⟩ : syracuseStep 1192711 = 1789067) B1789067
theorem B1585979 : Blo 1056613 1585979 := bstep (se 1 (by rfl) ⟨1189484, by rfl⟩ : syracuseStep 1585979 = 2378969) B2378969
theorem B1586039 : Blo 1056613 1586039 := bstep (se 1 (by rfl) ⟨1189529, by rfl⟩ : syracuseStep 1586039 = 2379059) B2379059
theorem B1586063 : Blo 1056613 1586063 := bstep (se 1 (by rfl) ⟨1189547, by rfl⟩ : syracuseStep 1586063 = 2379095) B2379095
theorem B1586105 : Blo 1056613 1586105 := bstep (se 2 (by rfl) ⟨594789, by rfl⟩ : syracuseStep 1586105 = 1189579) B1189579
theorem B1192891 : Blo 1056613 1192891 := bstep (se 1 (by rfl) ⟨894668, by rfl⟩ : syracuseStep 1192891 = 1789337) B1789337
theorem B1586183 : Blo 1056613 1586183 := bstep (se 1 (by rfl) ⟨1189637, by rfl⟩ : syracuseStep 1586183 = 2379275) B2379275
theorem B1586219 : Blo 1056613 1586219 := bstep (se 1 (by rfl) ⟨1189664, by rfl⟩ : syracuseStep 1586219 = 2379329) B2379329
theorem B13579325 : Blo 1056613 13579325 := bstep (se 3 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 13579325 = 5092247) B5092247
theorem B1586249 : Blo 1056613 1586249 := bstep (se 2 (by rfl) ⟨594843, by rfl⟩ : syracuseStep 1586249 = 1189687) B1189687
theorem B25801877 : Blo 1056613 25801877 := bstep (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) B1209463
theorem B1586363 : Blo 1056613 1586363 := bstep (se 1 (by rfl) ⟨1189772, by rfl⟩ : syracuseStep 1586363 = 2379545) B2379545
theorem B1586423 : Blo 1056613 1586423 := bstep (se 1 (by rfl) ⟨1189817, by rfl⟩ : syracuseStep 1586423 = 2379635) B2379635
theorem B1586447 : Blo 1056613 1586447 := bstep (se 1 (by rfl) ⟨1189835, by rfl⟩ : syracuseStep 1586447 = 2379671) B2379671
theorem B1586489 : Blo 1056613 1586489 := bstep (se 2 (by rfl) ⟨594933, by rfl⟩ : syracuseStep 1586489 = 1189867) B1189867
theorem B1586567 : Blo 1056613 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B1586603 : Blo 1056613 1586603 := bstep (se 1 (by rfl) ⟨1189952, by rfl⟩ : syracuseStep 1586603 = 2379905) B2379905
theorem B1586633 : Blo 1056613 1586633 := bstep (se 2 (by rfl) ⟨594987, by rfl⟩ : syracuseStep 1586633 = 1189975) B1189975
theorem B2012617 : Blo 1056613 2012617 := bstep (se 2 (by rfl) ⟨754731, by rfl⟩ : syracuseStep 2012617 = 1509463) B1509463
theorem B1586747 : Blo 1056613 1586747 := bstep (se 1 (by rfl) ⟨1190060, by rfl⟩ : syracuseStep 1586747 = 2380121) B2380121
theorem B1586807 : Blo 1056613 1586807 := bstep (se 1 (by rfl) ⟨1190105, by rfl⟩ : syracuseStep 1586807 = 2380211) B2380211
theorem B1586831 : Blo 1056613 1586831 := bstep (se 1 (by rfl) ⟨1190123, by rfl⟩ : syracuseStep 1586831 = 2380247) B2380247
theorem B1586873 : Blo 1056613 1586873 := bstep (se 2 (by rfl) ⟨595077, by rfl⟩ : syracuseStep 1586873 = 1190155) B1190155
theorem B1586951 : Blo 1056613 1586951 := bstep (se 1 (by rfl) ⟨1190213, by rfl⟩ : syracuseStep 1586951 = 2380427) B2380427
theorem B1586987 : Blo 1056613 1586987 := bstep (se 1 (by rfl) ⟨1190240, by rfl⟩ : syracuseStep 1586987 = 2380481) B2380481
theorem B1587017 : Blo 1056613 1587017 := bstep (se 2 (by rfl) ⟨595131, by rfl⟩ : syracuseStep 1587017 = 1190263) B1190263
theorem B1783687 : Blo 1056613 1783687 := bstep (se 1 (by rfl) ⟨1337765, by rfl⟩ : syracuseStep 1783687 = 2675531) B2675531
theorem B1587131 : Blo 1056613 1587131 := bstep (se 1 (by rfl) ⟨1190348, by rfl⟩ : syracuseStep 1587131 = 2380697) B2380697
theorem B18331595 : Blo 1056613 18331595 := bstep (se 1 (by rfl) ⟨13748696, by rfl⟩ : syracuseStep 18331595 = 27497393) B27497393
theorem B1587191 : Blo 1056613 1587191 := bstep (se 1 (by rfl) ⟨1190393, by rfl⟩ : syracuseStep 1587191 = 2380787) B2380787
theorem B1587215 : Blo 1056613 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B1587257 : Blo 1056613 1587257 := bstep (se 2 (by rfl) ⟨595221, by rfl⟩ : syracuseStep 1587257 = 1190443) B1190443
theorem B3389501 : Blo 1056613 3389501 := bstep (se 3 (by rfl) ⟨635531, by rfl⟩ : syracuseStep 3389501 = 1271063) B1271063
theorem B1587335 : Blo 1056613 1587335 := bstep (se 1 (by rfl) ⟨1190501, by rfl⟩ : syracuseStep 1587335 = 2381003) B2381003
theorem B2013331 : Blo 1056613 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B1587371 : Blo 1056613 1587371 := bstep (se 1 (by rfl) ⟨1190528, by rfl⟩ : syracuseStep 1587371 = 2381057) B2381057
theorem B1587401 : Blo 1056613 1587401 := bstep (se 2 (by rfl) ⟨595275, by rfl⟩ : syracuseStep 1587401 = 1190551) B1190551
theorem B12859681 : Blo 1056613 12859681 := bstep (se 2 (by rfl) ⟨4822380, by rfl⟩ : syracuseStep 12859681 = 9644761) B9644761
theorem B1587515 : Blo 1056613 1587515 := bstep (se 1 (by rfl) ⟨1190636, by rfl⟩ : syracuseStep 1587515 = 2381273) B2381273
theorem B1587575 : Blo 1056613 1587575 := bstep (se 1 (by rfl) ⟨1190681, by rfl⟩ : syracuseStep 1587575 = 2381363) B2381363
theorem B1587599 : Blo 1056613 1587599 := bstep (se 1 (by rfl) ⟨1190699, by rfl⟩ : syracuseStep 1587599 = 2381399) B2381399
theorem B1587641 : Blo 1056613 1587641 := bstep (se 2 (by rfl) ⟨595365, by rfl⟩ : syracuseStep 1587641 = 1190731) B1190731
theorem B2865665 : Blo 1056613 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B1587719 : Blo 1056613 1587719 := bstep (se 1 (by rfl) ⟨1190789, by rfl⟩ : syracuseStep 1587719 = 2381579) B2381579
theorem B5356043 : Blo 1056613 5356043 := bstep (se 1 (by rfl) ⟨4017032, by rfl⟩ : syracuseStep 5356043 = 8034065) B8034065
theorem B1784335 : Blo 1056613 1784335 := bstep (se 1 (by rfl) ⟨1338251, by rfl⟩ : syracuseStep 1784335 = 2676503) B2676503
theorem B1587755 : Blo 1056613 1587755 := bstep (se 1 (by rfl) ⟨1190816, by rfl⟩ : syracuseStep 1587755 = 2381633) B2381633
theorem B1587785 : Blo 1056613 1587785 := bstep (se 2 (by rfl) ⟨595419, by rfl⟩ : syracuseStep 1587785 = 1190839) B1190839
theorem B5356205 : Blo 1056613 5356205 := bstep (se 3 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 5356205 = 2008577) B2008577
theorem B1587899 : Blo 1056613 1587899 := bstep (se 1 (by rfl) ⟨1190924, by rfl⟩ : syracuseStep 1587899 = 2381849) B2381849
theorem B1587959 : Blo 1056613 1587959 := bstep (se 1 (by rfl) ⟨1190969, by rfl⟩ : syracuseStep 1587959 = 2381939) B2381939
theorem B1587983 : Blo 1056613 1587983 := bstep (se 1 (by rfl) ⟨1190987, by rfl⟩ : syracuseStep 1587983 = 2381975) B2381975
theorem B1588025 : Blo 1056613 1588025 := bstep (se 2 (by rfl) ⟨595509, by rfl⟩ : syracuseStep 1588025 = 1191019) B1191019
theorem B1588103 : Blo 1056613 1588103 := bstep (se 1 (by rfl) ⟨1191077, by rfl⟩ : syracuseStep 1588103 = 2382155) B2382155
theorem B1588139 : Blo 1056613 1588139 := bstep (se 1 (by rfl) ⟨1191104, by rfl⟩ : syracuseStep 1588139 = 2382209) B2382209
theorem B1588169 : Blo 1056613 1588169 := bstep (se 2 (by rfl) ⟨595563, by rfl⟩ : syracuseStep 1588169 = 1191127) B1191127
theorem B4013009 : Blo 1056613 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B1784875 : Blo 1056613 1784875 := bstep (se 1 (by rfl) ⟨1338656, by rfl⟩ : syracuseStep 1784875 = 2677313) B2677313
theorem B1588283 : Blo 1056613 1588283 := bstep (se 1 (by rfl) ⟨1191212, by rfl⟩ : syracuseStep 1588283 = 2382425) B2382425
theorem B1588343 : Blo 1056613 1588343 := bstep (se 1 (by rfl) ⟨1191257, by rfl⟩ : syracuseStep 1588343 = 2382515) B2382515
theorem B1588367 : Blo 1056613 1588367 := bstep (se 1 (by rfl) ⟨1191275, by rfl⟩ : syracuseStep 1588367 = 2382551) B2382551
theorem B1785017 : Blo 1056613 1785017 := bstep (se 2 (by rfl) ⟨669381, by rfl⟩ : syracuseStep 1785017 = 1338763) B1338763
theorem B1588409 : Blo 1056613 1588409 := bstep (se 2 (by rfl) ⟨595653, by rfl⟩ : syracuseStep 1588409 = 1191307) B1191307
theorem B3816649 : Blo 1056613 3816649 := bstep (se 2 (by rfl) ⟨1431243, by rfl⟩ : syracuseStep 3816649 = 2862487) B2862487
theorem B1588487 : Blo 1056613 1588487 := bstep (se 1 (by rfl) ⟨1191365, by rfl⟩ : syracuseStep 1588487 = 2382731) B2382731
theorem B4013327 : Blo 1056613 4013327 := bstep (se 1 (by rfl) ⟨3009995, by rfl⟩ : syracuseStep 4013327 = 6019991) B6019991
theorem B1588523 : Blo 1056613 1588523 := bstep (se 1 (by rfl) ⟨1191392, by rfl⟩ : syracuseStep 1588523 = 2382785) B2382785
theorem B1588553 : Blo 1056613 1588553 := bstep (se 2 (by rfl) ⟨595707, by rfl⟩ : syracuseStep 1588553 = 1191415) B1191415
theorem B1588667 : Blo 1056613 1588667 := bstep (se 1 (by rfl) ⟨1191500, by rfl⟩ : syracuseStep 1588667 = 2383001) B2383001
theorem B1588727 : Blo 1056613 1588727 := bstep (se 1 (by rfl) ⟨1191545, by rfl⟩ : syracuseStep 1588727 = 2383091) B2383091
theorem B1588751 : Blo 1056613 1588751 := bstep (se 1 (by rfl) ⟨1191563, by rfl⟩ : syracuseStep 1588751 = 2383127) B2383127
theorem B1588793 : Blo 1056613 1588793 := bstep (se 2 (by rfl) ⟨595797, by rfl⟩ : syracuseStep 1588793 = 1191595) B1191595
theorem B2866747 : Blo 1056613 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1588871 : Blo 1056613 1588871 := bstep (se 1 (by rfl) ⟨1191653, by rfl⟩ : syracuseStep 1588871 = 2383307) B2383307
theorem B1588907 : Blo 1056613 1588907 := bstep (se 1 (by rfl) ⟨1191680, by rfl⟩ : syracuseStep 1588907 = 2383361) B2383361
theorem B18103985 : Blo 1056613 18103985 := bstep (se 2 (by rfl) ⟨6788994, by rfl⟩ : syracuseStep 18103985 = 13577989) B13577989
theorem B1588937 : Blo 1056613 1588937 := bstep (se 2 (by rfl) ⟨595851, by rfl⟩ : syracuseStep 1588937 = 1191703) B1191703
theorem B1589051 : Blo 1056613 1589051 := bstep (se 1 (by rfl) ⟨1191788, by rfl⟩ : syracuseStep 1589051 = 2383577) B2383577
theorem B1785719 : Blo 1056613 1785719 := bstep (se 1 (by rfl) ⟨1339289, by rfl⟩ : syracuseStep 1785719 = 2678579) B2678579
theorem B1589111 : Blo 1056613 1589111 := bstep (se 1 (by rfl) ⟨1191833, by rfl⟩ : syracuseStep 1589111 = 2383667) B2383667
theorem B1589135 : Blo 1056613 1589135 := bstep (se 1 (by rfl) ⟨1191851, by rfl⟩ : syracuseStep 1589135 = 2383703) B2383703
theorem B1589177 : Blo 1056613 1589177 := bstep (se 2 (by rfl) ⟨595941, by rfl⟩ : syracuseStep 1589177 = 1191883) B1191883
theorem B22921163 : Blo 1056613 22921163 := bstep (se 1 (by rfl) ⟨17190872, by rfl⟩ : syracuseStep 22921163 = 34381745) B34381745
theorem B1589255 : Blo 1056613 1589255 := bstep (se 1 (by rfl) ⟨1191941, by rfl⟩ : syracuseStep 1589255 = 2383883) B2383883
theorem B1589291 : Blo 1056613 1589291 := bstep (se 1 (by rfl) ⟨1191968, by rfl⟩ : syracuseStep 1589291 = 2383937) B2383937
theorem B1589321 : Blo 1056613 1589321 := bstep (se 2 (by rfl) ⟨595995, by rfl⟩ : syracuseStep 1589321 = 1191991) B1191991
theorem B11452589 : Blo 1056613 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B1589435 : Blo 1056613 1589435 := bstep (se 1 (by rfl) ⟨1192076, by rfl⟩ : syracuseStep 1589435 = 2384153) B2384153
theorem B1589495 : Blo 1056613 1589495 := bstep (se 1 (by rfl) ⟨1192121, by rfl⟩ : syracuseStep 1589495 = 2384243) B2384243
theorem B5357825 : Blo 1056613 5357825 := bstep (se 2 (by rfl) ⟨2009184, by rfl⟩ : syracuseStep 5357825 = 4018369) B4018369
theorem B1589519 : Blo 1056613 1589519 := bstep (se 1 (by rfl) ⟨1192139, by rfl⟩ : syracuseStep 1589519 = 2384279) B2384279
theorem B1589561 : Blo 1056613 1589561 := bstep (se 2 (by rfl) ⟨596085, by rfl⟩ : syracuseStep 1589561 = 1192171) B1192171
theorem B1786171 : Blo 1056613 1786171 := bstep (se 1 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 1786171 = 2679257) B2679257
theorem B43467101 : Blo 1056613 43467101 := bstep (se 3 (by rfl) ⟨8150081, by rfl⟩ : syracuseStep 43467101 = 16300163) B16300163
theorem B1589639 : Blo 1056613 1589639 := bstep (se 1 (by rfl) ⟨1192229, by rfl⟩ : syracuseStep 1589639 = 2384459) B2384459
theorem B1589675 : Blo 1056613 1589675 := bstep (se 1 (by rfl) ⟨1192256, by rfl⟩ : syracuseStep 1589675 = 2384513) B2384513
theorem B1786313 : Blo 1056613 1786313 := bstep (se 2 (by rfl) ⟨669867, by rfl⟩ : syracuseStep 1786313 = 1339735) B1339735
theorem B1589705 : Blo 1056613 1589705 := bstep (se 2 (by rfl) ⟨596139, by rfl⟩ : syracuseStep 1589705 = 1192279) B1192279
theorem B12894673 : Blo 1056613 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B1589819 : Blo 1056613 1589819 := bstep (se 1 (by rfl) ⟨1192364, by rfl⟩ : syracuseStep 1589819 = 2384729) B2384729
theorem B1589879 : Blo 1056613 1589879 := bstep (se 1 (by rfl) ⟨1192409, by rfl⟩ : syracuseStep 1589879 = 2384819) B2384819
theorem B1360519 : Blo 1056613 1360519 := bstep (se 1 (by rfl) ⟨1020389, by rfl⟩ : syracuseStep 1360519 = 2040779) B2040779
theorem B1589903 : Blo 1056613 1589903 := bstep (se 1 (by rfl) ⟨1192427, by rfl⟩ : syracuseStep 1589903 = 2384855) B2384855
theorem B5718701 : Blo 1056613 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B1589945 : Blo 1056613 1589945 := bstep (se 2 (by rfl) ⟨596229, by rfl⟩ : syracuseStep 1589945 = 1192459) B1192459
theorem B1590023 : Blo 1056613 1590023 := bstep (se 1 (by rfl) ⟨1192517, by rfl⟩ : syracuseStep 1590023 = 2385035) B2385035
theorem B1590059 : Blo 1056613 1590059 := bstep (se 1 (by rfl) ⟨1192544, by rfl⟩ : syracuseStep 1590059 = 2385089) B2385089
theorem B1590089 : Blo 1056613 1590089 := bstep (se 2 (by rfl) ⟨596283, by rfl⟩ : syracuseStep 1590089 = 1192567) B1192567
theorem B3392371 : Blo 1056613 3392371 := bstep (se 1 (by rfl) ⟨2544278, by rfl⟩ : syracuseStep 3392371 = 5088557) B5088557
theorem B30983093 : Blo 1056613 30983093 := bstep (se 5 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 30983093 = 2904665) B2904665
theorem B1590203 : Blo 1056613 1590203 := bstep (se 1 (by rfl) ⟨1192652, by rfl⟩ : syracuseStep 1590203 = 2385305) B2385305
theorem B4178897 : Blo 1056613 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B1590263 : Blo 1056613 1590263 := bstep (se 1 (by rfl) ⟨1192697, by rfl⟩ : syracuseStep 1590263 = 2385395) B2385395
theorem B1590287 : Blo 1056613 1590287 := bstep (se 1 (by rfl) ⟨1192715, by rfl⟩ : syracuseStep 1590287 = 2385431) B2385431
theorem B5358635 : Blo 1056613 5358635 := bstep (se 1 (by rfl) ⟨4018976, by rfl⟩ : syracuseStep 5358635 = 8037953) B8037953
theorem B1590329 : Blo 1056613 1590329 := bstep (se 2 (by rfl) ⟨596373, by rfl⟩ : syracuseStep 1590329 = 1192747) B1192747
theorem B1787015 : Blo 1056613 1787015 := bstep (se 1 (by rfl) ⟨1340261, by rfl⟩ : syracuseStep 1787015 = 2680523) B2680523
theorem B1590407 : Blo 1056613 1590407 := bstep (se 1 (by rfl) ⟨1192805, by rfl⟩ : syracuseStep 1590407 = 2385611) B2385611
theorem B1590443 : Blo 1056613 1590443 := bstep (se 1 (by rfl) ⟨1192832, by rfl⟩ : syracuseStep 1590443 = 2385665) B2385665
theorem B1590473 : Blo 1056613 1590473 := bstep (se 2 (by rfl) ⟨596427, by rfl⟩ : syracuseStep 1590473 = 1192855) B1192855
theorem B3818753 : Blo 1056613 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1590587 : Blo 1056613 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B1590647 : Blo 1056613 1590647 := bstep (se 1 (by rfl) ⟨1192985, by rfl⟩ : syracuseStep 1590647 = 2385971) B2385971
theorem B1590671 : Blo 1056613 1590671 := bstep (se 1 (by rfl) ⟨1193003, by rfl⟩ : syracuseStep 1590671 = 2386007) B2386007
theorem B1590713 : Blo 1056613 1590713 := bstep (se 2 (by rfl) ⟨596517, by rfl⟩ : syracuseStep 1590713 = 1193035) B1193035
theorem B1590791 : Blo 1056613 1590791 := bstep (se 1 (by rfl) ⟨1193093, by rfl⟩ : syracuseStep 1590791 = 2386187) B2386187
theorem B1590827 : Blo 1056613 1590827 := bstep (se 1 (by rfl) ⟨1193120, by rfl⟩ : syracuseStep 1590827 = 2386241) B2386241
theorem B1590857 : Blo 1056613 1590857 := bstep (se 2 (by rfl) ⟨596571, by rfl⟩ : syracuseStep 1590857 = 1193143) B1193143
theorem B1787663 : Blo 1056613 1787663 := bstep (se 1 (by rfl) ⟨1340747, by rfl⟩ : syracuseStep 1787663 = 2681495) B2681495
theorem B17418053 : Blo 1056613 17418053 := bstep (se 4 (by rfl) ⟨1632942, by rfl⟩ : syracuseStep 17418053 = 3265885) B3265885
theorem B2377619 : Blo 1056613 2377619 := bstep (se 1 (by rfl) ⟨1783214, by rfl⟩ : syracuseStep 2377619 = 3566429) B3566429
theorem B2377673 : Blo 1056613 2377673 := bstep (se 2 (by rfl) ⟨891627, by rfl⟩ : syracuseStep 2377673 = 1783255) B1783255
theorem B1788203 : Blo 1056613 1788203 := bstep (se 1 (by rfl) ⟨1341152, by rfl⟩ : syracuseStep 1788203 = 2682305) B2682305
theorem B5359931 : Blo 1056613 5359931 := bstep (se 1 (by rfl) ⟨4019948, by rfl⟩ : syracuseStep 5359931 = 8039897) B8039897
theorem B3819835 : Blo 1056613 3819835 := bstep (se 1 (by rfl) ⟨2864876, by rfl⟩ : syracuseStep 3819835 = 5729753) B5729753
theorem B5360093 : Blo 1056613 5360093 := bstep (se 3 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 5360093 = 2010035) B2010035
theorem B2378375 : Blo 1056613 2378375 := bstep (se 1 (by rfl) ⟨1783781, by rfl⟩ : syracuseStep 2378375 = 3567563) B3567563
theorem B1788601 : Blo 1056613 1788601 := bstep (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) B1341451
theorem B5720777 : Blo 1056613 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B4016897 : Blo 1056613 4016897 := bstep (se 2 (by rfl) ⟨1506336, by rfl⟩ : syracuseStep 4016897 = 3012673) B3012673
theorem B2542337 : Blo 1056613 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B4016911 : Blo 1056613 4016911 := bstep (se 1 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 4016911 = 6025367) B6025367
theorem B5360417 : Blo 1056613 5360417 := bstep (se 2 (by rfl) ⟨2010156, by rfl⟩ : syracuseStep 5360417 = 4020313) B4020313
theorem B2378555 : Blo 1056613 2378555 := bstep (se 1 (by rfl) ⟨1783916, by rfl⟩ : syracuseStep 2378555 = 3567833) B3567833
theorem B2149267 : Blo 1056613 2149267 := bstep (se 1 (by rfl) ⟨1611950, by rfl⟩ : syracuseStep 2149267 = 3223901) B3223901
theorem B2378681 : Blo 1056613 2378681 := bstep (se 2 (by rfl) ⟨892005, by rfl⟩ : syracuseStep 2378681 = 1784011) B1784011
theorem B2379023 : Blo 1056613 2379023 := bstep (se 1 (by rfl) ⟨1784267, by rfl⟩ : syracuseStep 2379023 = 3568535) B3568535
theorem B2379041 : Blo 1056613 2379041 := bstep (se 2 (by rfl) ⟨892140, by rfl⟩ : syracuseStep 2379041 = 1784281) B1784281
theorem B1789303 : Blo 1056613 1789303 := bstep (se 1 (by rfl) ⟨1341977, by rfl⟩ : syracuseStep 1789303 = 2683955) B2683955
theorem B13553081 : Blo 1056613 13553081 := bstep (se 2 (by rfl) ⟨5082405, by rfl⟩ : syracuseStep 13553081 = 10164811) B10164811
theorem B1789499 : Blo 1056613 1789499 := bstep (se 1 (by rfl) ⟨1342124, by rfl⟩ : syracuseStep 1789499 = 2684249) B2684249
theorem B2379383 : Blo 1056613 2379383 := bstep (se 1 (by rfl) ⟨1784537, by rfl⟩ : syracuseStep 2379383 = 3569075) B3569075
theorem B5361389 : Blo 1056613 5361389 := bstep (se 3 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 5361389 = 2010521) B2010521
theorem B2543375 : Blo 1056613 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B2379563 : Blo 1056613 2379563 := bstep (se 1 (by rfl) ⟨1784672, by rfl⟩ : syracuseStep 2379563 = 3569345) B3569345
theorem B10178419 : Blo 1056613 10178419 := bstep (se 1 (by rfl) ⟨7633814, by rfl⟩ : syracuseStep 10178419 = 15267629) B15267629
theorem B2674579 : Blo 1056613 2674579 := bstep (se 1 (by rfl) ⟨2005934, by rfl⟩ : syracuseStep 2674579 = 4011869) B4011869
theorem B3821521 : Blo 1056613 3821521 := bstep (se 2 (by rfl) ⟨1433070, by rfl⟩ : syracuseStep 3821521 = 2866141) B2866141
theorem B4018187 : Blo 1056613 4018187 := bstep (se 1 (by rfl) ⟨3013640, by rfl⟩ : syracuseStep 4018187 = 6027281) B6027281
theorem B2674721 : Blo 1056613 2674721 := bstep (se 2 (by rfl) ⟨1003020, by rfl⟩ : syracuseStep 2674721 = 2006041) B2006041
theorem B7622743 : Blo 1056613 7622743 := bstep (se 1 (by rfl) ⟨5717057, by rfl⟩ : syracuseStep 7622743 = 11434115) B11434115
theorem B2379923 : Blo 1056613 2379923 := bstep (se 1 (by rfl) ⟨1784942, by rfl⟩ : syracuseStep 2379923 = 3569885) B3569885
theorem B7622857 : Blo 1056613 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B2379977 : Blo 1056613 2379977 := bstep (se 2 (by rfl) ⟨892491, by rfl⟩ : syracuseStep 2379977 = 1784983) B1784983
theorem B5362199 : Blo 1056613 5362199 := bstep (se 1 (by rfl) ⟨4021649, by rfl⟩ : syracuseStep 5362199 = 8043299) B8043299
theorem B13587011 : Blo 1056613 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B11457125 : Blo 1056613 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B7721729 : Blo 1056613 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B2413327 : Blo 1056613 2413327 := bstep (se 1 (by rfl) ⟨1809995, by rfl⟩ : syracuseStep 2413327 = 3619991) B3619991
theorem B10310435 : Blo 1056613 10310435 := bstep (se 1 (by rfl) ⟨7732826, by rfl⟩ : syracuseStep 10310435 = 15465653) B15465653
theorem B6771545 : Blo 1056613 6771545 := bstep (se 2 (by rfl) ⟨2539329, by rfl⟩ : syracuseStep 6771545 = 5078659) B5078659
theorem B2380679 : Blo 1056613 2380679 := bstep (se 1 (by rfl) ⟨1785509, by rfl⟩ : syracuseStep 2380679 = 3571019) B3571019
theorem B4019129 : Blo 1056613 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B2675713 : Blo 1056613 2675713 := bstep (se 2 (by rfl) ⟨1003392, by rfl⟩ : syracuseStep 2675713 = 2006785) B2006785
theorem B6018077 : Blo 1056613 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B2413601 : Blo 1056613 2413601 := bstep (se 2 (by rfl) ⟨905100, by rfl⟩ : syracuseStep 2413601 = 1810201) B1810201
theorem B2380859 : Blo 1056613 2380859 := bstep (se 1 (by rfl) ⟨1785644, by rfl⟩ : syracuseStep 2380859 = 3571289) B3571289
theorem B2380985 : Blo 1056613 2380985 := bstep (se 2 (by rfl) ⟨892869, by rfl⟩ : syracuseStep 2380985 = 1785739) B1785739
theorem B7230701 : Blo 1056613 7230701 := bstep (se 3 (by rfl) ⟨1355756, by rfl⟩ : syracuseStep 7230701 = 2711513) B2711513
theorem B1692943 : Blo 1056613 1692943 := bstep (se 1 (by rfl) ⟨1269707, by rfl⟩ : syracuseStep 1692943 = 2539415) B2539415
theorem B1430843 : Blo 1056613 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B3626299 : Blo 1056613 3626299 := bstep (se 1 (by rfl) ⟨2719724, by rfl⟩ : syracuseStep 3626299 = 5439449) B5439449
theorem B3397049 : Blo 1056613 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B2381327 : Blo 1056613 2381327 := bstep (se 1 (by rfl) ⟨1785995, by rfl⟩ : syracuseStep 2381327 = 3571991) B3571991
theorem B2381345 : Blo 1056613 2381345 := bstep (se 2 (by rfl) ⟨893004, by rfl⟩ : syracuseStep 2381345 = 1786009) B1786009
theorem B2676311 : Blo 1056613 2676311 := bstep (se 1 (by rfl) ⟨2007233, by rfl⟩ : syracuseStep 2676311 = 4014467) B4014467
theorem B2676523 : Blo 1056613 2676523 := bstep (se 1 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 2676523 = 4014785) B4014785
theorem B18339635 : Blo 1056613 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B2381687 : Blo 1056613 2381687 := bstep (se 1 (by rfl) ⟨1786265, by rfl⟩ : syracuseStep 2381687 = 3572531) B3572531
theorem B2676665 : Blo 1056613 2676665 := bstep (se 2 (by rfl) ⟨1003749, by rfl⟩ : syracuseStep 2676665 = 2007499) B2007499
theorem B6445021 : Blo 1056613 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B2381867 : Blo 1056613 2381867 := bstep (se 1 (by rfl) ⟨1786400, by rfl⟩ : syracuseStep 2381867 = 3572801) B3572801
theorem B18077741 : Blo 1056613 18077741 := bstep (se 3 (by rfl) ⟨3389576, by rfl⟩ : syracuseStep 18077741 = 6779153) B6779153
theorem B1694071 : Blo 1056613 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B2382227 : Blo 1056613 2382227 := bstep (se 1 (by rfl) ⟨1786670, by rfl⟩ : syracuseStep 2382227 = 3573341) B3573341
theorem B2382281 : Blo 1056613 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B2677657 : Blo 1056613 2677657 := bstep (se 2 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 2677657 = 2008243) B2008243
theorem B2677819 : Blo 1056613 2677819 := bstep (se 1 (by rfl) ⟨2008364, by rfl⟩ : syracuseStep 2677819 = 4016729) B4016729
theorem B2382983 : Blo 1056613 2382983 := bstep (se 1 (by rfl) ⟨1787237, by rfl⟩ : syracuseStep 2382983 = 3574475) B3574475
theorem B2677961 : Blo 1056613 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B2383163 : Blo 1056613 2383163 := bstep (se 1 (by rfl) ⟨1787372, by rfl⟩ : syracuseStep 2383163 = 3574745) B3574745
theorem B1695161 : Blo 1056613 1695161 := bstep (se 2 (by rfl) ⟨635685, by rfl⟩ : syracuseStep 1695161 = 1271371) B1271371
theorem B21192121 : Blo 1056613 21192121 := bstep (se 2 (by rfl) ⟨7947045, by rfl⟩ : syracuseStep 21192121 = 15894091) B15894091
theorem B2383289 : Blo 1056613 2383289 := bstep (se 2 (by rfl) ⟨893733, by rfl⟩ : syracuseStep 2383289 = 1787467) B1787467
theorem B4021771 : Blo 1056613 4021771 := bstep (se 1 (by rfl) ⟨3016328, by rfl⟩ : syracuseStep 4021771 = 6032657) B6032657
theorem B5365277 : Blo 1056613 5365277 := bstep (se 3 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 5365277 = 2011979) B2011979
theorem B2678305 : Blo 1056613 2678305 := bstep (se 2 (by rfl) ⟨1004364, by rfl⟩ : syracuseStep 2678305 = 2008729) B2008729
theorem B6020675 : Blo 1056613 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B11460325 : Blo 1056613 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B2383631 : Blo 1056613 2383631 := bstep (se 1 (by rfl) ⟨1787723, by rfl⟩ : syracuseStep 2383631 = 3575447) B3575447
theorem B2383649 : Blo 1056613 2383649 := bstep (se 2 (by rfl) ⟨893868, by rfl⟩ : syracuseStep 2383649 = 1787737) B1787737
theorem B5726011 : Blo 1056613 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B4022075 : Blo 1056613 4022075 := bstep (se 1 (by rfl) ⟨3016556, by rfl⟩ : syracuseStep 4022075 = 6033113) B6033113
theorem B5365763 : Blo 1056613 5365763 := bstep (se 1 (by rfl) ⟨4024322, by rfl⟩ : syracuseStep 5365763 = 8048645) B8048645
theorem B2678903 : Blo 1056613 2678903 := bstep (se 1 (by rfl) ⟨2009177, by rfl⟩ : syracuseStep 2678903 = 4018355) B4018355
theorem B2383991 : Blo 1056613 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B12869765 : Blo 1056613 12869765 := bstep (se 4 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 12869765 = 2413081) B2413081
theorem B4022561 : Blo 1056613 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B2384171 : Blo 1056613 2384171 := bstep (se 1 (by rfl) ⟨1788128, by rfl⟩ : syracuseStep 2384171 = 3576257) B3576257
theorem B1696135 : Blo 1056613 1696135 := bstep (se 1 (by rfl) ⟨1272101, by rfl⟩ : syracuseStep 1696135 = 2544203) B2544203
theorem B2548103 : Blo 1056613 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B1696391 : Blo 1056613 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B2384531 : Blo 1056613 2384531 := bstep (se 1 (by rfl) ⟨1788398, by rfl⟩ : syracuseStep 2384531 = 3576797) B3576797
theorem B2384585 : Blo 1056613 2384585 := bstep (se 2 (by rfl) ⟨894219, by rfl⟩ : syracuseStep 2384585 = 1788439) B1788439
theorem B8053505 : Blo 1056613 8053505 := bstep (se 2 (by rfl) ⟨3020064, by rfl⟩ : syracuseStep 8053505 = 6040129) B6040129
theorem B4285199 : Blo 1056613 4285199 := bstep (se 1 (by rfl) ⟨3213899, by rfl⟩ : syracuseStep 4285199 = 6427799) B6427799
theorem B4023533 : Blo 1056613 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B6022451 : Blo 1056613 6022451 := bstep (se 1 (by rfl) ⟨4516838, by rfl⟩ : syracuseStep 6022451 = 9033677) B9033677
theorem B2680199 : Blo 1056613 2680199 := bstep (se 1 (by rfl) ⟨2010149, by rfl⟩ : syracuseStep 2680199 = 4020299) B4020299
theorem B2385287 : Blo 1056613 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B2680249 : Blo 1056613 2680249 := bstep (se 2 (by rfl) ⟨1005093, by rfl⟩ : syracuseStep 2680249 = 2010187) B2010187
theorem B25748941 : Blo 1056613 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B4515371 : Blo 1056613 4515371 := bstep (se 1 (by rfl) ⟨3386528, by rfl⟩ : syracuseStep 4515371 = 6773057) B6773057
theorem B2450987 : Blo 1056613 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B2385467 : Blo 1056613 2385467 := bstep (se 1 (by rfl) ⟨1789100, by rfl⟩ : syracuseStep 2385467 = 3578201) B3578201
theorem B5367383 : Blo 1056613 5367383 := bstep (se 1 (by rfl) ⟨4025537, by rfl⟩ : syracuseStep 5367383 = 8051075) B8051075
theorem B2385593 : Blo 1056613 2385593 := bstep (se 2 (by rfl) ⟨894597, by rfl⟩ : syracuseStep 2385593 = 1789195) B1789195
theorem B2680847 : Blo 1056613 2680847 := bstep (se 1 (by rfl) ⟨2010635, by rfl⟩ : syracuseStep 2680847 = 4021271) B4021271
theorem B1697807 : Blo 1056613 1697807 := bstep (se 1 (by rfl) ⟨1273355, by rfl⟩ : syracuseStep 1697807 = 2546711) B2546711
theorem B2385935 : Blo 1056613 2385935 := bstep (se 1 (by rfl) ⟨1789451, by rfl⟩ : syracuseStep 2385935 = 3578903) B3578903
theorem B2385953 : Blo 1056613 2385953 := bstep (se 2 (by rfl) ⟨894732, by rfl⟩ : syracuseStep 2385953 = 1789465) B1789465
theorem B5367869 : Blo 1056613 5367869 := bstep (se 3 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 5367869 = 2012951) B2012951
theorem B1697993 : Blo 1056613 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B2386295 : Blo 1056613 2386295 := bstep (se 1 (by rfl) ⟨1789721, by rfl⟩ : syracuseStep 2386295 = 3579443) B3579443
theorem B1337735 : Blo 1056613 1337735 := bstep (se 1 (by rfl) ⟨1003301, by rfl⟩ : syracuseStep 1337735 = 2006603) B2006603
theorem B2681545 : Blo 1056613 2681545 := bstep (se 2 (by rfl) ⟨1005579, by rfl⟩ : syracuseStep 2681545 = 2011159) B2011159
theorem B6023909 : Blo 1056613 6023909 := bstep (se 4 (by rfl) ⟨564741, by rfl⟩ : syracuseStep 6023909 = 1129483) B1129483
theorem B58714895 : Blo 1056613 58714895 := bstep (se 1 (by rfl) ⟨44036171, by rfl⟩ : syracuseStep 58714895 = 88072343) B88072343
theorem B12053285 : Blo 1056613 12053285 := bstep (se 4 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 12053285 = 2259991) B2259991
theorem B2681687 : Blo 1056613 2681687 := bstep (se 1 (by rfl) ⟨2011265, by rfl⟩ : syracuseStep 2681687 = 4022531) B4022531
theorem B6876019 : Blo 1056613 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B3566483 : Blo 1056613 3566483 := bstep (se 1 (by rfl) ⟨2674862, by rfl⟩ : syracuseStep 3566483 = 5349725) B5349725
theorem B1338383 : Blo 1056613 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B6024365 : Blo 1056613 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B4025659 : Blo 1056613 4025659 := bstep (se 1 (by rfl) ⟨3019244, by rfl⟩ : syracuseStep 4025659 = 6038489) B6038489
theorem B6778333 : Blo 1056613 6778333 := bstep (se 3 (by rfl) ⟨1270937, by rfl⟩ : syracuseStep 6778333 = 2541875) B2541875
theorem B4026145 : Blo 1056613 4026145 := bstep (se 2 (by rfl) ⟨1509804, by rfl⟩ : syracuseStep 4026145 = 3019609) B3019609
theorem B8023859 : Blo 1056613 8023859 := bstep (se 1 (by rfl) ⟨6017894, by rfl⟩ : syracuseStep 8023859 = 12035789) B12035789
theorem B6025049 : Blo 1056613 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B3010679 : Blo 1056613 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B3567887 : Blo 1056613 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B2650411 : Blo 1056613 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B3568157 : Blo 1056613 3568157 := bstep (se 3 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 3568157 = 1338059) B1338059
theorem B3863069 : Blo 1056613 3863069 := bstep (se 3 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 3863069 = 1448651) B1448651
theorem B2683763 : Blo 1056613 2683763 := bstep (se 1 (by rfl) ⟨2012822, by rfl⟩ : syracuseStep 2683763 = 4025645) B4025645
theorem B2257865 : Blo 1056613 2257865 := bstep (se 2 (by rfl) ⟨846699, by rfl⟩ : syracuseStep 2257865 = 1693399) B1693399
theorem B2716687 : Blo 1056613 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B2684279 : Blo 1056613 2684279 := bstep (se 1 (by rfl) ⟨2013209, by rfl⟩ : syracuseStep 2684279 = 4026419) B4026419
theorem B1504759 : Blo 1056613 1504759 := bstep (se 1 (by rfl) ⟨1128569, by rfl⟩ : syracuseStep 1504759 = 2257139) B2257139
theorem B2258617 : Blo 1056613 2258617 := bstep (se 2 (by rfl) ⟨846981, by rfl⟩ : syracuseStep 2258617 = 1693963) B1693963
theorem B3569561 : Blo 1056613 3569561 := bstep (se 2 (by rfl) ⟨1338585, by rfl⟩ : syracuseStep 3569561 = 2677171) B2677171
theorem B1341355 : Blo 1056613 1341355 := bstep (se 1 (by rfl) ⟨1006016, by rfl⟩ : syracuseStep 1341355 = 2012033) B2012033
theorem B2291657 : Blo 1056613 2291657 := bstep (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) B1718743
theorem B61929485 : Blo 1056613 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B15464945 : Blo 1056613 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B3013163 : Blo 1056613 3013163 := bstep (se 1 (by rfl) ⟨2259872, by rfl⟩ : syracuseStep 3013163 = 4519745) B4519745
theorem B11467331 : Blo 1056613 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B3570263 : Blo 1056613 3570263 := bstep (se 1 (by rfl) ⟨2677697, by rfl⟩ : syracuseStep 3570263 = 5355395) B5355395
theorem B2062967 : Blo 1056613 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B30505733 : Blo 1056613 30505733 := bstep (se 4 (by rfl) ⟨2859912, by rfl⟩ : syracuseStep 30505733 = 5719825) B5719825
theorem B25787173 : Blo 1056613 25787173 := bstep (se 4 (by rfl) ⟨2417547, by rfl⟩ : syracuseStep 25787173 = 4835095) B4835095
theorem B1342327 : Blo 1056613 1342327 := bstep (se 1 (by rfl) ⟨1006745, by rfl⟩ : syracuseStep 1342327 = 2013491) B2013491
theorem B5077907 : Blo 1056613 5077907 := bstep (se 1 (by rfl) ⟨3808430, by rfl⟩ : syracuseStep 5077907 = 7616861) B7616861
theorem B3570749 : Blo 1056613 3570749 := bstep (se 3 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 3570749 = 1339031) B1339031
theorem B4521197 : Blo 1056613 4521197 := bstep (se 3 (by rfl) ⟨847724, by rfl⟩ : syracuseStep 4521197 = 1695449) B1695449
theorem B3013949 : Blo 1056613 3013949 := bstep (se 3 (by rfl) ⟨565115, by rfl⟩ : syracuseStep 3013949 = 1130231) B1130231
theorem B3014279 : Blo 1056613 3014279 := bstep (se 1 (by rfl) ⟨2260709, by rfl⟩ : syracuseStep 3014279 = 4521419) B4521419
theorem B1507367 : Blo 1056613 1507367 := bstep (se 1 (by rfl) ⟨1130525, by rfl⟩ : syracuseStep 1507367 = 2261051) B2261051
theorem B7635059 : Blo 1056613 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B3571883 : Blo 1056613 3571883 := bstep (se 1 (by rfl) ⟨2678912, by rfl⟩ : syracuseStep 3571883 = 5357825) B5357825
theorem B26083685 : Blo 1056613 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B2261513 : Blo 1056613 2261513 := bstep (se 2 (by rfl) ⟨848067, by rfl⟩ : syracuseStep 2261513 = 1696135) B1696135
theorem B2785931 : Blo 1056613 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B3572423 : Blo 1056613 3572423 := bstep (se 1 (by rfl) ⟨2679317, by rfl⟩ : syracuseStep 3572423 = 5358635) B5358635
theorem B3015737 : Blo 1056613 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B4523161 : Blo 1056613 4523161 := bstep (se 2 (by rfl) ⟨1696185, by rfl⟩ : syracuseStep 4523161 = 3392371) B3392371
theorem B3016079 : Blo 1056613 3016079 := bstep (se 1 (by rfl) ⟨2262059, by rfl⟩ : syracuseStep 3016079 = 4524119) B4524119
theorem B3573287 : Blo 1056613 3573287 := bstep (se 1 (by rfl) ⟨2679965, by rfl⟩ : syracuseStep 3573287 = 5359931) B5359931
theorem B3573395 : Blo 1056613 3573395 := bstep (se 1 (by rfl) ⟨2680046, by rfl⟩ : syracuseStep 3573395 = 5360093) B5360093
theorem B3868445 : Blo 1056613 3868445 := bstep (se 3 (by rfl) ⟨725333, by rfl⟩ : syracuseStep 3868445 = 1450667) B1450667
theorem B6031199 : Blo 1056613 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B3573611 : Blo 1056613 3573611 := bstep (se 1 (by rfl) ⟨2680208, by rfl⟩ : syracuseStep 3573611 = 5360417) B5360417
theorem B3573665 : Blo 1056613 3573665 := bstep (se 2 (by rfl) ⟨1340124, by rfl⟩ : syracuseStep 3573665 = 2680249) B2680249
theorem B3574259 : Blo 1056613 3574259 := bstep (se 1 (by rfl) ⟨2680694, by rfl⟩ : syracuseStep 3574259 = 5361389) B5361389
theorem B2755511 : Blo 1056613 2755511 := bstep (se 1 (by rfl) ⟨2066633, by rfl⟩ : syracuseStep 2755511 = 4133267) B4133267
theorem B3574799 : Blo 1056613 3574799 := bstep (se 1 (by rfl) ⟨2681099, by rfl⟩ : syracuseStep 3574799 = 5362199) B5362199
theorem B7638083 : Blo 1056613 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B5147819 : Blo 1056613 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B2034935 : Blo 1056613 2034935 := bstep (se 1 (by rfl) ⟨1526201, by rfl⟩ : syracuseStep 2034935 = 3052403) B3052403
theorem B1609067 : Blo 1056613 1609067 := bstep (se 1 (by rfl) ⟨1206800, by rfl⟩ : syracuseStep 1609067 = 2413601) B2413601
theorem B4820467 : Blo 1056613 4820467 := bstep (se 1 (by rfl) ⟨3615350, by rfl⟩ : syracuseStep 4820467 = 7230701) B7230701
theorem B3575393 : Blo 1056613 3575393 := bstep (se 2 (by rfl) ⟨1340772, by rfl⟩ : syracuseStep 3575393 = 2681545) B2681545
theorem B2264699 : Blo 1056613 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B3018379 : Blo 1056613 3018379 := bstep (se 1 (by rfl) ⟨2263784, by rfl⟩ : syracuseStep 3018379 = 4527569) B4527569
theorem B34312085 : Blo 1056613 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B4067347 : Blo 1056613 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B19337395 : Blo 1056613 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B12063491 : Blo 1056613 12063491 := bstep (se 1 (by rfl) ⟨9047618, by rfl⟩ : syracuseStep 12063491 = 18095237) B18095237
theorem B45814643 : Blo 1056613 45814643 := bstep (se 1 (by rfl) ⟨34360982, by rfl⟩ : syracuseStep 45814643 = 68721965) B68721965
theorem B3576851 : Blo 1056613 3576851 := bstep (se 1 (by rfl) ⟨2682638, by rfl⟩ : syracuseStep 3576851 = 5365277) B5365277
theorem B13571225 : Blo 1056613 13571225 := bstep (se 2 (by rfl) ⟨5089209, by rfl⟩ : syracuseStep 13571225 = 10178419) B10178419
theorem B9049259 : Blo 1056613 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B3577175 : Blo 1056613 3577175 := bstep (se 1 (by rfl) ⟨2682881, by rfl⟩ : syracuseStep 3577175 = 5365763) B5365763
theorem B94213489 : Blo 1056613 94213489 := bstep (se 2 (by rfl) ⟨35330058, by rfl⟩ : syracuseStep 94213489 = 70660117) B70660117
theorem B4527485 : Blo 1056613 4527485 := bstep (se 3 (by rfl) ⟨848903, by rfl⟩ : syracuseStep 4527485 = 1697807) B1697807
theorem B10163657 : Blo 1056613 10163657 := bstep (se 2 (by rfl) ⟨3811371, by rfl⟩ : syracuseStep 10163657 = 7622743) B7622743
theorem B10163809 : Blo 1056613 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B6428483 : Blo 1056613 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B2856799 : Blo 1056613 2856799 := bstep (se 1 (by rfl) ⟨2142599, by rfl⟩ : syracuseStep 2856799 = 4285199) B4285199
theorem B3872783 : Blo 1056613 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B3217769 : Blo 1056613 3217769 := bstep (se 2 (by rfl) ⟨1206663, by rfl⟩ : syracuseStep 3217769 = 2413327) B2413327
theorem B3578255 : Blo 1056613 3578255 := bstep (se 1 (by rfl) ⟨2683691, by rfl⟩ : syracuseStep 3578255 = 5367383) B5367383
theorem B7641773 : Blo 1056613 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B3578579 : Blo 1056613 3578579 := bstep (se 1 (by rfl) ⟨2683934, by rfl⟩ : syracuseStep 3578579 = 5367869) B5367869
theorem B8592131 : Blo 1056613 8592131 := bstep (se 1 (by rfl) ⟨6444098, by rfl⟩ : syracuseStep 8592131 = 12888197) B12888197
theorem B8035523 : Blo 1056613 8035523 := bstep (se 1 (by rfl) ⟨6026642, by rfl⟩ : syracuseStep 8035523 = 12053285) B12053285
theorem B8592587 : Blo 1056613 8592587 := bstep (se 1 (by rfl) ⟨6444440, by rfl⟩ : syracuseStep 8592587 = 12888881) B12888881
theorem B2006345 : Blo 1056613 2006345 := bstep (se 2 (by rfl) ⟨752379, by rfl⟩ : syracuseStep 2006345 = 1504759) B1504759
theorem B4070857 : Blo 1056613 4070857 := bstep (se 2 (by rfl) ⟨1526571, by rfl⟩ : syracuseStep 4070857 = 3053143) B3053143
theorem B3808777 : Blo 1056613 3808777 := bstep (se 2 (by rfl) ⟨1428291, by rfl⟩ : syracuseStep 3808777 = 2856583) B2856583
theorem B6037031 : Blo 1056613 6037031 := bstep (se 1 (by rfl) ⟨4527773, by rfl⟩ : syracuseStep 6037031 = 9055547) B9055547
theorem B6037213 : Blo 1056613 6037213 := bstep (se 3 (by rfl) ⟨1131977, by rfl⟩ : syracuseStep 6037213 = 2263955) B2263955
theorem B5349239 : Blo 1056613 5349239 := bstep (se 1 (by rfl) ⟨4011929, by rfl⟩ : syracuseStep 5349239 = 8023859) B8023859
theorem B1056635 : Blo 1056613 1056635 := bstep (se 1 (by rfl) ⟨792476, by rfl⟩ : syracuseStep 1056635 = 1584953) B1584953
theorem B1056687 : Blo 1056613 1056687 := bstep (se 1 (by rfl) ⟨792515, by rfl⟩ : syracuseStep 1056687 = 1585031) B1585031
theorem B1056711 : Blo 1056613 1056711 := bstep (se 1 (by rfl) ⟨792533, by rfl⟩ : syracuseStep 1056711 = 1585067) B1585067
theorem B8593361 : Blo 1056613 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B1056731 : Blo 1056613 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B1056807 : Blo 1056613 1056807 := bstep (se 1 (by rfl) ⟨792605, by rfl⟩ : syracuseStep 1056807 = 1585211) B1585211
theorem B1056847 : Blo 1056613 1056847 := bstep (se 1 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 1056847 = 1585271) B1585271
theorem B2007119 : Blo 1056613 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B1056863 : Blo 1056613 1056863 := bstep (se 1 (by rfl) ⟨792647, by rfl⟩ : syracuseStep 1056863 = 1585295) B1585295
theorem B1056891 : Blo 1056613 1056891 := bstep (se 1 (by rfl) ⟨792668, by rfl⟩ : syracuseStep 1056891 = 1585337) B1585337
theorem B1908859 : Blo 1056613 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B4137131 : Blo 1056613 4137131 := bstep (se 1 (by rfl) ⟨3102848, by rfl⟩ : syracuseStep 4137131 = 6205697) B6205697
theorem B1056943 : Blo 1056613 1056943 := bstep (se 1 (by rfl) ⟨792707, by rfl⟩ : syracuseStep 1056943 = 1585415) B1585415
theorem B1056967 : Blo 1056613 1056967 := bstep (se 1 (by rfl) ⟨792725, by rfl⟩ : syracuseStep 1056967 = 1585451) B1585451
theorem B1056987 : Blo 1056613 1056987 := bstep (se 1 (by rfl) ⟨792740, by rfl⟩ : syracuseStep 1056987 = 1585481) B1585481
theorem B1057063 : Blo 1056613 1057063 := bstep (se 1 (by rfl) ⟨792797, by rfl⟩ : syracuseStep 1057063 = 1585595) B1585595
theorem B1057103 : Blo 1056613 1057103 := bstep (se 1 (by rfl) ⟨792827, by rfl⟩ : syracuseStep 1057103 = 1585655) B1585655
theorem B1057119 : Blo 1056613 1057119 := bstep (se 1 (by rfl) ⟨792839, by rfl⟩ : syracuseStep 1057119 = 1585679) B1585679
theorem B1057147 : Blo 1056613 1057147 := bstep (se 1 (by rfl) ⟨792860, by rfl⟩ : syracuseStep 1057147 = 1585721) B1585721
theorem B17146241 : Blo 1056613 17146241 := bstep (se 2 (by rfl) ⟨6429840, by rfl⟩ : syracuseStep 17146241 = 12859681) B12859681
theorem B1057199 : Blo 1056613 1057199 := bstep (se 1 (by rfl) ⟨792899, by rfl⟩ : syracuseStep 1057199 = 1585799) B1585799
theorem B1057223 : Blo 1056613 1057223 := bstep (se 1 (by rfl) ⟨792917, by rfl⟩ : syracuseStep 1057223 = 1585835) B1585835
theorem B1057243 : Blo 1056613 1057243 := bstep (se 1 (by rfl) ⟨792932, by rfl⟩ : syracuseStep 1057243 = 1585865) B1585865
theorem B1057319 : Blo 1056613 1057319 := bstep (se 1 (by rfl) ⟨792989, by rfl⟩ : syracuseStep 1057319 = 1585979) B1585979
theorem B1057359 : Blo 1056613 1057359 := bstep (se 1 (by rfl) ⟨793019, by rfl⟩ : syracuseStep 1057359 = 1586039) B1586039
theorem B1057375 : Blo 1056613 1057375 := bstep (se 1 (by rfl) ⟨793031, by rfl⟩ : syracuseStep 1057375 = 1586063) B1586063
theorem B1057403 : Blo 1056613 1057403 := bstep (se 1 (by rfl) ⟨793052, by rfl⟩ : syracuseStep 1057403 = 1586105) B1586105
theorem B1057455 : Blo 1056613 1057455 := bstep (se 1 (by rfl) ⟨793091, by rfl⟩ : syracuseStep 1057455 = 1586183) B1586183
theorem B1057479 : Blo 1056613 1057479 := bstep (se 1 (by rfl) ⟨793109, by rfl⟩ : syracuseStep 1057479 = 1586219) B1586219
theorem B9052883 : Blo 1056613 9052883 := bstep (se 1 (by rfl) ⟨6789662, by rfl⟩ : syracuseStep 9052883 = 13579325) B13579325
theorem B1057499 : Blo 1056613 1057499 := bstep (se 1 (by rfl) ⟨793124, by rfl⟩ : syracuseStep 1057499 = 1586249) B1586249
theorem B1057575 : Blo 1056613 1057575 := bstep (se 1 (by rfl) ⟨793181, by rfl⟩ : syracuseStep 1057575 = 1586363) B1586363
theorem B1057615 : Blo 1056613 1057615 := bstep (se 1 (by rfl) ⟨793211, by rfl⟩ : syracuseStep 1057615 = 1586423) B1586423
theorem B1057631 : Blo 1056613 1057631 := bstep (se 1 (by rfl) ⟨793223, by rfl⟩ : syracuseStep 1057631 = 1586447) B1586447
theorem B1057659 : Blo 1056613 1057659 := bstep (se 1 (by rfl) ⟨793244, by rfl⟩ : syracuseStep 1057659 = 1586489) B1586489
theorem B1057711 : Blo 1056613 1057711 := bstep (se 1 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 1057711 = 1586567) B1586567
theorem B1057735 : Blo 1056613 1057735 := bstep (se 1 (by rfl) ⟨793301, by rfl⟩ : syracuseStep 1057735 = 1586603) B1586603
theorem B1057755 : Blo 1056613 1057755 := bstep (se 1 (by rfl) ⟨793316, by rfl⟩ : syracuseStep 1057755 = 1586633) B1586633
theorem B1057831 : Blo 1056613 1057831 := bstep (se 1 (by rfl) ⟨793373, by rfl⟩ : syracuseStep 1057831 = 1586747) B1586747
theorem B34382897 : Blo 1056613 34382897 := bstep (se 2 (by rfl) ⟨12893586, by rfl⟩ : syracuseStep 34382897 = 25787173) B25787173
theorem B1057871 : Blo 1056613 1057871 := bstep (se 1 (by rfl) ⟨793403, by rfl⟩ : syracuseStep 1057871 = 1586807) B1586807
theorem B1057887 : Blo 1056613 1057887 := bstep (se 1 (by rfl) ⟨793415, by rfl⟩ : syracuseStep 1057887 = 1586831) B1586831
theorem B1057915 : Blo 1056613 1057915 := bstep (se 1 (by rfl) ⟨793436, by rfl⟩ : syracuseStep 1057915 = 1586873) B1586873
theorem B1057967 : Blo 1056613 1057967 := bstep (se 1 (by rfl) ⟨793475, by rfl⟩ : syracuseStep 1057967 = 1586951) B1586951
theorem B1057991 : Blo 1056613 1057991 := bstep (se 1 (by rfl) ⟨793493, by rfl⟩ : syracuseStep 1057991 = 1586987) B1586987
theorem B1058011 : Blo 1056613 1058011 := bstep (se 1 (by rfl) ⟨793508, by rfl⟩ : syracuseStep 1058011 = 1587017) B1587017
theorem B1058087 : Blo 1056613 1058087 := bstep (se 1 (by rfl) ⟨793565, by rfl⟩ : syracuseStep 1058087 = 1587131) B1587131
theorem B1058127 : Blo 1056613 1058127 := bstep (se 1 (by rfl) ⟨793595, by rfl⟩ : syracuseStep 1058127 = 1587191) B1587191
theorem B1058143 : Blo 1056613 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B1058171 : Blo 1056613 1058171 := bstep (se 1 (by rfl) ⟨793628, by rfl⟩ : syracuseStep 1058171 = 1587257) B1587257
theorem B1058223 : Blo 1056613 1058223 := bstep (se 1 (by rfl) ⟨793667, by rfl⟩ : syracuseStep 1058223 = 1587335) B1587335
theorem B1058247 : Blo 1056613 1058247 := bstep (se 1 (by rfl) ⟨793685, by rfl⟩ : syracuseStep 1058247 = 1587371) B1587371
theorem B1058267 : Blo 1056613 1058267 := bstep (se 1 (by rfl) ⟨793700, by rfl⟩ : syracuseStep 1058267 = 1587401) B1587401
theorem B1058343 : Blo 1056613 1058343 := bstep (se 1 (by rfl) ⟨793757, by rfl⟩ : syracuseStep 1058343 = 1587515) B1587515
theorem B1058383 : Blo 1056613 1058383 := bstep (se 1 (by rfl) ⟨793787, by rfl⟩ : syracuseStep 1058383 = 1587575) B1587575
theorem B1058399 : Blo 1056613 1058399 := bstep (se 1 (by rfl) ⟨793799, by rfl⟩ : syracuseStep 1058399 = 1587599) B1587599
theorem B5088865 : Blo 1056613 5088865 := bstep (se 2 (by rfl) ⟨1908324, by rfl⟩ : syracuseStep 5088865 = 3816649) B3816649
theorem B1058427 : Blo 1056613 1058427 := bstep (se 1 (by rfl) ⟨793820, by rfl⟩ : syracuseStep 1058427 = 1587641) B1587641
theorem B1058479 : Blo 1056613 1058479 := bstep (se 1 (by rfl) ⟨793859, by rfl⟩ : syracuseStep 1058479 = 1587719) B1587719
theorem B2008775 : Blo 1056613 2008775 := bstep (se 1 (by rfl) ⟨1506581, by rfl⟩ : syracuseStep 2008775 = 3013163) B3013163
theorem B1058503 : Blo 1056613 1058503 := bstep (se 1 (by rfl) ⟨793877, by rfl⟩ : syracuseStep 1058503 = 1587755) B1587755
theorem B7644887 : Blo 1056613 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B1058523 : Blo 1056613 1058523 := bstep (se 1 (by rfl) ⟨793892, by rfl⟩ : syracuseStep 1058523 = 1587785) B1587785
theorem B1058599 : Blo 1056613 1058599 := bstep (se 1 (by rfl) ⟨793949, by rfl⟩ : syracuseStep 1058599 = 1587899) B1587899
theorem B1058639 : Blo 1056613 1058639 := bstep (se 1 (by rfl) ⟨793979, by rfl⟩ : syracuseStep 1058639 = 1587959) B1587959
theorem B1058655 : Blo 1056613 1058655 := bstep (se 1 (by rfl) ⟨793991, by rfl⟩ : syracuseStep 1058655 = 1587983) B1587983
theorem B1058683 : Blo 1056613 1058683 := bstep (se 1 (by rfl) ⟨794012, by rfl⟩ : syracuseStep 1058683 = 1588025) B1588025
theorem B28256161 : Blo 1056613 28256161 := bstep (se 2 (by rfl) ⟨10596060, by rfl⟩ : syracuseStep 28256161 = 21192121) B21192121
theorem B1058735 : Blo 1056613 1058735 := bstep (se 1 (by rfl) ⟨794051, by rfl⟩ : syracuseStep 1058735 = 1588103) B1588103
theorem B3385271 : Blo 1056613 3385271 := bstep (se 1 (by rfl) ⟨2538953, by rfl⟩ : syracuseStep 3385271 = 5077907) B5077907
theorem B1058759 : Blo 1056613 1058759 := bstep (se 1 (by rfl) ⟨794069, by rfl⟩ : syracuseStep 1058759 = 1588139) B1588139
theorem B1058779 : Blo 1056613 1058779 := bstep (se 1 (by rfl) ⟨794084, by rfl⟩ : syracuseStep 1058779 = 1588169) B1588169
theorem B1058855 : Blo 1056613 1058855 := bstep (se 1 (by rfl) ⟨794141, by rfl⟩ : syracuseStep 1058855 = 1588283) B1588283
theorem B1058895 : Blo 1056613 1058895 := bstep (se 1 (by rfl) ⟨794171, by rfl⟩ : syracuseStep 1058895 = 1588343) B1588343
theorem B1058911 : Blo 1056613 1058911 := bstep (se 1 (by rfl) ⟨794183, by rfl⟩ : syracuseStep 1058911 = 1588367) B1588367
theorem B1190011 : Blo 1056613 1190011 := bstep (se 1 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 1190011 = 1785017) B1785017
theorem B1058939 : Blo 1056613 1058939 := bstep (se 1 (by rfl) ⟨794204, by rfl⟩ : syracuseStep 1058939 = 1588409) B1588409
theorem B13576349 : Blo 1056613 13576349 := bstep (se 3 (by rfl) ⟨2545565, by rfl⟩ : syracuseStep 13576349 = 5091131) B5091131
theorem B1058991 : Blo 1056613 1058991 := bstep (se 1 (by rfl) ⟨794243, by rfl⟩ : syracuseStep 1058991 = 1588487) B1588487
theorem B1059015 : Blo 1056613 1059015 := bstep (se 1 (by rfl) ⟨794261, by rfl⟩ : syracuseStep 1059015 = 1588523) B1588523
theorem B2009299 : Blo 1056613 2009299 := bstep (se 1 (by rfl) ⟨1506974, by rfl⟩ : syracuseStep 2009299 = 3013949) B3013949
theorem B1059035 : Blo 1056613 1059035 := bstep (se 1 (by rfl) ⟨794276, by rfl⟩ : syracuseStep 1059035 = 1588553) B1588553
theorem B1059111 : Blo 1056613 1059111 := bstep (se 1 (by rfl) ⟨794333, by rfl⟩ : syracuseStep 1059111 = 1588667) B1588667
theorem B15280433 : Blo 1056613 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B1059151 : Blo 1056613 1059151 := bstep (se 1 (by rfl) ⟨794363, by rfl⟩ : syracuseStep 1059151 = 1588727) B1588727
theorem B1059167 : Blo 1056613 1059167 := bstep (se 1 (by rfl) ⟨794375, by rfl⟩ : syracuseStep 1059167 = 1588751) B1588751
theorem B1059195 : Blo 1056613 1059195 := bstep (se 1 (by rfl) ⟨794396, by rfl⟩ : syracuseStep 1059195 = 1588793) B1588793
theorem B2009519 : Blo 1056613 2009519 := bstep (se 1 (by rfl) ⟨1507139, by rfl⟩ : syracuseStep 2009519 = 3014279) B3014279
theorem B1059247 : Blo 1056613 1059247 := bstep (se 1 (by rfl) ⟨794435, by rfl⟩ : syracuseStep 1059247 = 1588871) B1588871
theorem B1059271 : Blo 1056613 1059271 := bstep (se 1 (by rfl) ⟨794453, by rfl⟩ : syracuseStep 1059271 = 1588907) B1588907
theorem B12069323 : Blo 1056613 12069323 := bstep (se 1 (by rfl) ⟨9051992, by rfl⟩ : syracuseStep 12069323 = 18103985) B18103985
theorem B1059291 : Blo 1056613 1059291 := bstep (se 1 (by rfl) ⟨794468, by rfl⟩ : syracuseStep 1059291 = 1588937) B1588937
theorem B1059367 : Blo 1056613 1059367 := bstep (se 1 (by rfl) ⟨794525, by rfl⟩ : syracuseStep 1059367 = 1589051) B1589051
theorem B1190479 : Blo 1056613 1190479 := bstep (se 1 (by rfl) ⟨892859, by rfl⟩ : syracuseStep 1190479 = 1785719) B1785719
theorem B1059407 : Blo 1056613 1059407 := bstep (se 1 (by rfl) ⟨794555, by rfl⟩ : syracuseStep 1059407 = 1589111) B1589111
theorem B1059423 : Blo 1056613 1059423 := bstep (se 1 (by rfl) ⟨794567, by rfl⟩ : syracuseStep 1059423 = 1589135) B1589135
theorem B1059451 : Blo 1056613 1059451 := bstep (se 1 (by rfl) ⟨794588, by rfl⟩ : syracuseStep 1059451 = 1589177) B1589177
theorem B15280775 : Blo 1056613 15280775 := bstep (se 1 (by rfl) ⟨11460581, by rfl⟩ : syracuseStep 15280775 = 22921163) B22921163
theorem B1059503 : Blo 1056613 1059503 := bstep (se 1 (by rfl) ⟨794627, by rfl⟩ : syracuseStep 1059503 = 1589255) B1589255
theorem B1059527 : Blo 1056613 1059527 := bstep (se 1 (by rfl) ⟨794645, by rfl⟩ : syracuseStep 1059527 = 1589291) B1589291
theorem B1059547 : Blo 1056613 1059547 := bstep (se 1 (by rfl) ⟨794660, by rfl⟩ : syracuseStep 1059547 = 1589321) B1589321
theorem B1059623 : Blo 1056613 1059623 := bstep (se 1 (by rfl) ⟨794717, by rfl⟩ : syracuseStep 1059623 = 1589435) B1589435
theorem B2009929 : Blo 1056613 2009929 := bstep (se 2 (by rfl) ⟨753723, by rfl⟩ : syracuseStep 2009929 = 1507447) B1507447
theorem B1059663 : Blo 1056613 1059663 := bstep (se 1 (by rfl) ⟨794747, by rfl⟩ : syracuseStep 1059663 = 1589495) B1589495
theorem B1059679 : Blo 1056613 1059679 := bstep (se 1 (by rfl) ⟨794759, by rfl⟩ : syracuseStep 1059679 = 1589519) B1589519
theorem B1059707 : Blo 1056613 1059707 := bstep (se 1 (by rfl) ⟨794780, by rfl⟩ : syracuseStep 1059707 = 1589561) B1589561
theorem B28978067 : Blo 1056613 28978067 := bstep (se 1 (by rfl) ⟨21733550, by rfl⟩ : syracuseStep 28978067 = 43467101) B43467101
theorem B1059759 : Blo 1056613 1059759 := bstep (se 1 (by rfl) ⟨794819, by rfl⟩ : syracuseStep 1059759 = 1589639) B1589639
theorem B1059783 : Blo 1056613 1059783 := bstep (se 1 (by rfl) ⟨794837, by rfl⟩ : syracuseStep 1059783 = 1589675) B1589675
theorem B1190875 : Blo 1056613 1190875 := bstep (se 1 (by rfl) ⟨893156, by rfl⟩ : syracuseStep 1190875 = 1786313) B1786313
theorem B1059803 : Blo 1056613 1059803 := bstep (se 1 (by rfl) ⟨794852, by rfl⟩ : syracuseStep 1059803 = 1589705) B1589705
theorem B3386387 : Blo 1056613 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B1059879 : Blo 1056613 1059879 := bstep (se 1 (by rfl) ⟨794909, by rfl⟩ : syracuseStep 1059879 = 1589819) B1589819
theorem B1059919 : Blo 1056613 1059919 := bstep (se 1 (by rfl) ⟨794939, by rfl⟩ : syracuseStep 1059919 = 1589879) B1589879
theorem B1059935 : Blo 1056613 1059935 := bstep (se 1 (by rfl) ⟨794951, by rfl⟩ : syracuseStep 1059935 = 1589903) B1589903
theorem B1059963 : Blo 1056613 1059963 := bstep (se 1 (by rfl) ⟨794972, by rfl⟩ : syracuseStep 1059963 = 1589945) B1589945
theorem B1060015 : Blo 1056613 1060015 := bstep (se 1 (by rfl) ⟨795011, by rfl⟩ : syracuseStep 1060015 = 1590023) B1590023
theorem B1060039 : Blo 1056613 1060039 := bstep (se 1 (by rfl) ⟨795029, by rfl⟩ : syracuseStep 1060039 = 1590059) B1590059
theorem B1060059 : Blo 1056613 1060059 := bstep (se 1 (by rfl) ⟨795044, by rfl⟩ : syracuseStep 1060059 = 1590089) B1590089
theorem B20655395 : Blo 1056613 20655395 := bstep (se 1 (by rfl) ⟨15491546, by rfl⟩ : syracuseStep 20655395 = 30983093) B30983093
theorem B1060135 : Blo 1056613 1060135 := bstep (se 1 (by rfl) ⟨795101, by rfl⟩ : syracuseStep 1060135 = 1590203) B1590203
theorem B1060175 : Blo 1056613 1060175 := bstep (se 1 (by rfl) ⟨795131, by rfl⟩ : syracuseStep 1060175 = 1590263) B1590263
theorem B1060191 : Blo 1056613 1060191 := bstep (se 1 (by rfl) ⟨795143, by rfl⟩ : syracuseStep 1060191 = 1590287) B1590287
theorem B1060219 : Blo 1056613 1060219 := bstep (se 1 (by rfl) ⟨795164, by rfl⟩ : syracuseStep 1060219 = 1590329) B1590329
theorem B1191343 : Blo 1056613 1191343 := bstep (se 1 (by rfl) ⟨893507, by rfl⟩ : syracuseStep 1191343 = 1787015) B1787015
theorem B1060271 : Blo 1056613 1060271 := bstep (se 1 (by rfl) ⟨795203, by rfl⟩ : syracuseStep 1060271 = 1590407) B1590407
theorem B1060295 : Blo 1056613 1060295 := bstep (se 1 (by rfl) ⟨795221, by rfl⟩ : syracuseStep 1060295 = 1590443) B1590443
theorem B1060315 : Blo 1056613 1060315 := bstep (se 1 (by rfl) ⟨795236, by rfl⟩ : syracuseStep 1060315 = 1590473) B1590473
theorem B1060391 : Blo 1056613 1060391 := bstep (se 1 (by rfl) ⟨795293, by rfl⟩ : syracuseStep 1060391 = 1590587) B1590587
theorem B1060431 : Blo 1056613 1060431 := bstep (se 1 (by rfl) ⟨795323, by rfl⟩ : syracuseStep 1060431 = 1590647) B1590647
theorem B1060447 : Blo 1056613 1060447 := bstep (se 1 (by rfl) ⟨795335, by rfl⟩ : syracuseStep 1060447 = 1590671) B1590671
theorem B2862715 : Blo 1056613 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B1060475 : Blo 1056613 1060475 := bstep (se 1 (by rfl) ⟨795356, by rfl⟩ : syracuseStep 1060475 = 1590713) B1590713
theorem B1060527 : Blo 1056613 1060527 := bstep (se 1 (by rfl) ⟨795395, by rfl⟩ : syracuseStep 1060527 = 1590791) B1590791
theorem B6794941 : Blo 1056613 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B1060551 : Blo 1056613 1060551 := bstep (se 1 (by rfl) ⟨795413, by rfl⟩ : syracuseStep 1060551 = 1590827) B1590827
theorem B1060571 : Blo 1056613 1060571 := bstep (se 1 (by rfl) ⟨795428, by rfl⟩ : syracuseStep 1060571 = 1590857) B1590857
theorem B1191775 : Blo 1056613 1191775 := bstep (se 1 (by rfl) ⟨893831, by rfl⟩ : syracuseStep 1191775 = 1787663) B1787663
theorem B1585001 : Blo 1056613 1585001 := bstep (se 2 (by rfl) ⟨594375, by rfl⟩ : syracuseStep 1585001 = 1188751) B1188751
theorem B11612035 : Blo 1056613 11612035 := bstep (se 1 (by rfl) ⟨8709026, by rfl⟩ : syracuseStep 11612035 = 17418053) B17418053
theorem B1585079 : Blo 1056613 1585079 := bstep (se 1 (by rfl) ⟨1188809, by rfl⟩ : syracuseStep 1585079 = 2377619) B2377619
theorem B1585115 : Blo 1056613 1585115 := bstep (se 1 (by rfl) ⟨1188836, by rfl⟩ : syracuseStep 1585115 = 2377673) B2377673
theorem B1192135 : Blo 1056613 1192135 := bstep (se 1 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 1192135 = 1788203) B1788203
theorem B1585583 : Blo 1056613 1585583 := bstep (se 1 (by rfl) ⟨1189187, by rfl⟩ : syracuseStep 1585583 = 2378375) B2378375
theorem B15249869 : Blo 1056613 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B3813851 : Blo 1056613 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B1585673 : Blo 1056613 1585673 := bstep (se 2 (by rfl) ⟨594627, by rfl⟩ : syracuseStep 1585673 = 1189255) B1189255
theorem B1585703 : Blo 1056613 1585703 := bstep (se 1 (by rfl) ⟨1189277, by rfl⟩ : syracuseStep 1585703 = 2378555) B2378555
theorem B1585787 : Blo 1056613 1585787 := bstep (se 1 (by rfl) ⟨1189340, by rfl⟩ : syracuseStep 1585787 = 2378681) B2378681
theorem B1585913 : Blo 1056613 1585913 := bstep (se 2 (by rfl) ⟨594717, by rfl⟩ : syracuseStep 1585913 = 1189435) B1189435
theorem B1586015 : Blo 1056613 1586015 := bstep (se 1 (by rfl) ⟨1189511, by rfl⟩ : syracuseStep 1586015 = 2379023) B2379023
theorem B1586027 : Blo 1056613 1586027 := bstep (se 1 (by rfl) ⟨1189520, by rfl⟩ : syracuseStep 1586027 = 2379041) B2379041
theorem B5354423 : Blo 1056613 5354423 := bstep (se 1 (by rfl) ⟨4015817, by rfl⟩ : syracuseStep 5354423 = 8031635) B8031635
theorem B1192999 : Blo 1056613 1192999 := bstep (se 1 (by rfl) ⟨894749, by rfl⟩ : syracuseStep 1192999 = 1789499) B1789499
theorem B1586255 : Blo 1056613 1586255 := bstep (se 1 (by rfl) ⟨1189691, by rfl⟩ : syracuseStep 1586255 = 2379383) B2379383
theorem B1586375 : Blo 1056613 1586375 := bstep (se 1 (by rfl) ⟨1189781, by rfl⟩ : syracuseStep 1586375 = 2379563) B2379563
theorem B2012359 : Blo 1056613 2012359 := bstep (se 1 (by rfl) ⟨1509269, by rfl⟩ : syracuseStep 2012359 = 3018539) B3018539
theorem B1586537 : Blo 1056613 1586537 := bstep (se 2 (by rfl) ⟨594951, by rfl⟩ : syracuseStep 1586537 = 1189903) B1189903
theorem B1783147 : Blo 1056613 1783147 := bstep (se 1 (by rfl) ⟨1337360, by rfl⟩ : syracuseStep 1783147 = 2674721) B2674721
theorem B1586615 : Blo 1056613 1586615 := bstep (se 1 (by rfl) ⟨1189961, by rfl⟩ : syracuseStep 1586615 = 2379923) B2379923
theorem B1586651 : Blo 1056613 1586651 := bstep (se 1 (by rfl) ⟨1189988, by rfl⟩ : syracuseStep 1586651 = 2379977) B2379977
theorem B2864627 : Blo 1056613 2864627 := bstep (se 1 (by rfl) ⟨2148470, by rfl⟩ : syracuseStep 2864627 = 4296941) B4296941
theorem B9058007 : Blo 1056613 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B5093113 : Blo 1056613 5093113 := bstep (se 2 (by rfl) ⟨1909917, by rfl⟩ : syracuseStep 5093113 = 3819835) B3819835
theorem B2012921 : Blo 1056613 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B1587119 : Blo 1056613 1587119 := bstep (se 1 (by rfl) ⟨1190339, by rfl⟩ : syracuseStep 1587119 = 2380679) B2380679
theorem B2013103 : Blo 1056613 2013103 := bstep (se 1 (by rfl) ⟨1509827, by rfl⟩ : syracuseStep 2013103 = 3019655) B3019655
theorem B1587209 : Blo 1056613 1587209 := bstep (se 2 (by rfl) ⟨595203, by rfl⟩ : syracuseStep 1587209 = 1190407) B1190407
theorem B4012051 : Blo 1056613 4012051 := bstep (se 1 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 4012051 = 6018077) B6018077
theorem B7256101 : Blo 1056613 7256101 := bstep (se 4 (by rfl) ⟨680259, by rfl⟩ : syracuseStep 7256101 = 1360519) B1360519
theorem B1587239 : Blo 1056613 1587239 := bstep (se 1 (by rfl) ⟨1190429, by rfl⟩ : syracuseStep 1587239 = 2380859) B2380859
theorem B1587323 : Blo 1056613 1587323 := bstep (se 1 (by rfl) ⟨1190492, by rfl⟩ : syracuseStep 1587323 = 2380985) B2380985
theorem B3815581 : Blo 1056613 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B1587449 : Blo 1056613 1587449 := bstep (se 2 (by rfl) ⟨595293, by rfl⟩ : syracuseStep 1587449 = 1190587) B1190587
theorem B8042813 : Blo 1056613 8042813 := bstep (se 3 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 8042813 = 3016055) B3016055
theorem B1587551 : Blo 1056613 1587551 := bstep (se 1 (by rfl) ⟨1190663, by rfl⟩ : syracuseStep 1587551 = 2381327) B2381327
theorem B5355881 : Blo 1056613 5355881 := bstep (se 2 (by rfl) ⟨2008455, by rfl⟩ : syracuseStep 5355881 = 4016911) B4016911
theorem B92944745 : Blo 1056613 92944745 := bstep (se 2 (by rfl) ⟨34854279, by rfl⟩ : syracuseStep 92944745 = 69708559) B69708559
theorem B1587563 : Blo 1056613 1587563 := bstep (se 1 (by rfl) ⟨1190672, by rfl⟩ : syracuseStep 1587563 = 2381345) B2381345
theorem B1784207 : Blo 1056613 1784207 := bstep (se 1 (by rfl) ⟨1338155, by rfl⟩ : syracuseStep 1784207 = 2676311) B2676311
theorem B2865689 : Blo 1056613 2865689 := bstep (se 2 (by rfl) ⟨1074633, by rfl⟩ : syracuseStep 2865689 = 2149267) B2149267
theorem B1587791 : Blo 1056613 1587791 := bstep (se 1 (by rfl) ⟨1190843, by rfl⟩ : syracuseStep 1587791 = 2381687) B2381687
theorem B1784443 : Blo 1056613 1784443 := bstep (se 1 (by rfl) ⟨1338332, by rfl⟩ : syracuseStep 1784443 = 2676665) B2676665
theorem B1587911 : Blo 1056613 1587911 := bstep (se 1 (by rfl) ⟨1190933, by rfl⟩ : syracuseStep 1587911 = 2381867) B2381867
theorem B1588073 : Blo 1056613 1588073 := bstep (se 2 (by rfl) ⟨595527, by rfl⟩ : syracuseStep 1588073 = 1191055) B1191055
theorem B1588151 : Blo 1056613 1588151 := bstep (se 1 (by rfl) ⟨1191113, by rfl⟩ : syracuseStep 1588151 = 2382227) B2382227
theorem B1588187 : Blo 1056613 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B4078649 : Blo 1056613 4078649 := bstep (se 2 (by rfl) ⟨1529493, by rfl⟩ : syracuseStep 4078649 = 3058987) B3058987
theorem B9026639 : Blo 1056613 9026639 := bstep (se 1 (by rfl) ⟨6769979, by rfl⟩ : syracuseStep 9026639 = 13539959) B13539959
theorem B3390731 : Blo 1056613 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B1588655 : Blo 1056613 1588655 := bstep (se 1 (by rfl) ⟨1191491, by rfl⟩ : syracuseStep 1588655 = 2382983) B2382983
theorem B1785307 : Blo 1056613 1785307 := bstep (se 1 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 1785307 = 2677961) B2677961
theorem B48905693 : Blo 1056613 48905693 := bstep (se 3 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 48905693 = 18339635) B18339635
theorem B1588745 : Blo 1056613 1588745 := bstep (se 2 (by rfl) ⟨595779, by rfl⟩ : syracuseStep 1588745 = 1191559) B1191559
theorem B1588775 : Blo 1056613 1588775 := bstep (se 1 (by rfl) ⟨1191581, by rfl⟩ : syracuseStep 1588775 = 2383163) B2383163
theorem B1130107 : Blo 1056613 1130107 := bstep (se 1 (by rfl) ⟨847580, by rfl⟩ : syracuseStep 1130107 = 1695161) B1695161
theorem B1588859 : Blo 1056613 1588859 := bstep (se 1 (by rfl) ⟨1191644, by rfl⟩ : syracuseStep 1588859 = 2383289) B2383289
theorem B4013783 : Blo 1056613 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B1588985 : Blo 1056613 1588985 := bstep (se 2 (by rfl) ⟨595869, by rfl⟩ : syracuseStep 1588985 = 1191739) B1191739
theorem B1589087 : Blo 1056613 1589087 := bstep (se 1 (by rfl) ⟨1191815, by rfl⟩ : syracuseStep 1589087 = 2383631) B2383631
theorem B1589099 : Blo 1056613 1589099 := bstep (se 1 (by rfl) ⟨1191824, by rfl⟩ : syracuseStep 1589099 = 2383649) B2383649
theorem B5095361 : Blo 1056613 5095361 := bstep (se 2 (by rfl) ⟨1910760, by rfl⟩ : syracuseStep 5095361 = 3821521) B3821521
theorem B4243513 : Blo 1056613 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B1785935 : Blo 1056613 1785935 := bstep (se 1 (by rfl) ⟨1339451, by rfl⟩ : syracuseStep 1785935 = 2678903) B2678903
theorem B1589327 : Blo 1056613 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B1589447 : Blo 1056613 1589447 := bstep (se 1 (by rfl) ⟨1192085, by rfl⟩ : syracuseStep 1589447 = 2384171) B2384171
theorem B2146655 : Blo 1056613 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B1589609 : Blo 1056613 1589609 := bstep (se 2 (by rfl) ⟨596103, by rfl⟩ : syracuseStep 1589609 = 1192207) B1192207
theorem B1130927 : Blo 1056613 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B1589687 : Blo 1056613 1589687 := bstep (se 1 (by rfl) ⟨1192265, by rfl⟩ : syracuseStep 1589687 = 2384531) B2384531
theorem B1589723 : Blo 1056613 1589723 := bstep (se 1 (by rfl) ⟨1192292, by rfl⟩ : syracuseStep 1589723 = 2384585) B2384585
theorem B13550105 : Blo 1056613 13550105 := bstep (se 2 (by rfl) ⟨5081289, by rfl⟩ : syracuseStep 13550105 = 10162579) B10162579
theorem B2540281 : Blo 1056613 2540281 := bstep (se 2 (by rfl) ⟨952605, by rfl⟩ : syracuseStep 2540281 = 1905211) B1905211
theorem B4014967 : Blo 1056613 4014967 := bstep (se 1 (by rfl) ⟨3011225, by rfl⟩ : syracuseStep 4014967 = 6022451) B6022451
theorem B14468015 : Blo 1056613 14468015 := bstep (se 1 (by rfl) ⟨10851011, by rfl⟩ : syracuseStep 14468015 = 21702023) B21702023
theorem B1786799 : Blo 1056613 1786799 := bstep (se 1 (by rfl) ⟨1340099, by rfl⟩ : syracuseStep 1786799 = 2680199) B2680199
theorem B1590191 : Blo 1056613 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B1590281 : Blo 1056613 1590281 := bstep (se 2 (by rfl) ⟨596355, by rfl⟩ : syracuseStep 1590281 = 1192711) B1192711
theorem B1590311 : Blo 1056613 1590311 := bstep (se 1 (by rfl) ⟨1192733, by rfl⟩ : syracuseStep 1590311 = 2385467) B2385467
theorem B1590395 : Blo 1056613 1590395 := bstep (se 1 (by rfl) ⟨1192796, by rfl⟩ : syracuseStep 1590395 = 2385593) B2385593
theorem B1590521 : Blo 1056613 1590521 := bstep (se 2 (by rfl) ⟨596445, by rfl⟩ : syracuseStep 1590521 = 1192891) B1192891
theorem B1787231 : Blo 1056613 1787231 := bstep (se 1 (by rfl) ⟨1340423, by rfl⟩ : syracuseStep 1787231 = 2680847) B2680847
theorem B1590623 : Blo 1056613 1590623 := bstep (se 1 (by rfl) ⟨1192967, by rfl⟩ : syracuseStep 1590623 = 2385935) B2385935
theorem B3622249 : Blo 1056613 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B1590635 : Blo 1056613 1590635 := bstep (se 1 (by rfl) ⟨1192976, by rfl⟩ : syracuseStep 1590635 = 2385953) B2385953
theorem B9029029 : Blo 1056613 9029029 := bstep (se 4 (by rfl) ⟨846471, by rfl⟩ : syracuseStep 9029029 = 1692943) B1692943
theorem B1131995 : Blo 1056613 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B1590863 : Blo 1056613 1590863 := bstep (se 1 (by rfl) ⟨1193147, by rfl⟩ : syracuseStep 1590863 = 2386295) B2386295
theorem B4835065 : Blo 1056613 4835065 := bstep (se 2 (by rfl) ⟨1813149, by rfl⟩ : syracuseStep 4835065 = 3626299) B3626299
theorem B4015939 : Blo 1056613 4015939 := bstep (se 1 (by rfl) ⟨3011954, by rfl⟩ : syracuseStep 4015939 = 6023909) B6023909
theorem B39143263 : Blo 1056613 39143263 := bstep (se 1 (by rfl) ⟨29357447, by rfl⟩ : syracuseStep 39143263 = 58714895) B58714895
theorem B1787791 : Blo 1056613 1787791 := bstep (se 1 (by rfl) ⟨1340843, by rfl⟩ : syracuseStep 1787791 = 2681687) B2681687
theorem B8570785 : Blo 1056613 8570785 := bstep (se 2 (by rfl) ⟨3214044, by rfl⟩ : syracuseStep 8570785 = 6428089) B6428089
theorem B2377655 : Blo 1056613 2377655 := bstep (se 1 (by rfl) ⟨1783241, by rfl⟩ : syracuseStep 2377655 = 3566483) B3566483
theorem B4016243 : Blo 1056613 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B2902397 : Blo 1056613 2902397 := bstep (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) B1088399
theorem B13552109 : Blo 1056613 13552109 := bstep (se 3 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 13552109 = 5082041) B5082041
theorem B2378249 : Blo 1056613 2378249 := bstep (se 2 (by rfl) ⟨891843, by rfl⟩ : syracuseStep 2378249 = 1783687) B1783687
theorem B1788473 : Blo 1056613 1788473 := bstep (se 2 (by rfl) ⟨670677, by rfl⟩ : syracuseStep 1788473 = 1341355) B1341355
theorem B4016699 : Blo 1056613 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B2378591 : Blo 1056613 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B3394487 : Blo 1056613 3394487 := bstep (se 1 (by rfl) ⟨2545865, by rfl⟩ : syracuseStep 3394487 = 5091731) B5091731
theorem B2378771 : Blo 1056613 2378771 := bstep (se 1 (by rfl) ⟨1784078, by rfl⟩ : syracuseStep 2378771 = 3568157) B3568157
theorem B2575379 : Blo 1056613 2575379 := bstep (se 1 (by rfl) ⟨1931534, by rfl⟩ : syracuseStep 2575379 = 3863069) B3863069
theorem B1789175 : Blo 1056613 1789175 := bstep (se 1 (by rfl) ⟨1341881, by rfl⟩ : syracuseStep 1789175 = 2683763) B2683763
theorem B2379113 : Blo 1056613 2379113 := bstep (se 2 (by rfl) ⟨892167, by rfl⟩ : syracuseStep 2379113 = 1784335) B1784335
theorem B1789519 : Blo 1056613 1789519 := bstep (se 1 (by rfl) ⟨1342139, by rfl⟩ : syracuseStep 1789519 = 2684279) B2684279
theorem B1789769 : Blo 1056613 1789769 := bstep (se 2 (by rfl) ⟨671163, by rfl⟩ : syracuseStep 1789769 = 1342327) B1342327
theorem B2379707 : Blo 1056613 2379707 := bstep (se 1 (by rfl) ⟨1784780, by rfl⟩ : syracuseStep 2379707 = 3569561) B3569561
theorem B2379833 : Blo 1056613 2379833 := bstep (se 2 (by rfl) ⟨892437, by rfl⟩ : syracuseStep 2379833 = 1784875) B1784875
theorem B10309963 : Blo 1056613 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B2380175 : Blo 1056613 2380175 := bstep (se 1 (by rfl) ⟨1785131, by rfl⟩ : syracuseStep 2380175 = 3570263) B3570263
theorem B20337155 : Blo 1056613 20337155 := bstep (se 1 (by rfl) ⟨15252866, by rfl⟩ : syracuseStep 20337155 = 30505733) B30505733
theorem B2675339 : Blo 1056613 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B5362361 : Blo 1056613 5362361 := bstep (se 2 (by rfl) ⟨2010885, by rfl⟩ : syracuseStep 5362361 = 4021771) B4021771
theorem B2380499 : Blo 1056613 2380499 := bstep (se 1 (by rfl) ⟨1785374, by rfl⟩ : syracuseStep 2380499 = 3570749) B3570749
theorem B3822329 : Blo 1056613 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B2675551 : Blo 1056613 2675551 := bstep (se 1 (by rfl) ⟨2006663, by rfl⟩ : syracuseStep 2675551 = 4013327) B4013327
theorem B32560193 : Blo 1056613 32560193 := bstep (se 2 (by rfl) ⟨12210072, by rfl⟩ : syracuseStep 32560193 = 24420145) B24420145
theorem B2381435 : Blo 1056613 2381435 := bstep (se 1 (by rfl) ⟨1786076, by rfl⟩ : syracuseStep 2381435 = 3572153) B3572153
theorem B2676473 : Blo 1056613 2676473 := bstep (se 2 (by rfl) ⟨1003677, by rfl⟩ : syracuseStep 2676473 = 2007355) B2007355
theorem B2381561 : Blo 1056613 2381561 := bstep (se 2 (by rfl) ⟨893085, by rfl⟩ : syracuseStep 2381561 = 1786171) B1786171
theorem B2545481 : Blo 1056613 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B17192897 : Blo 1056613 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B2381831 : Blo 1056613 2381831 := bstep (se 1 (by rfl) ⟨1786373, by rfl⟩ : syracuseStep 2381831 = 3572747) B3572747
theorem B2381903 : Blo 1056613 2381903 := bstep (se 1 (by rfl) ⟨1786427, by rfl⟩ : syracuseStep 2381903 = 3572855) B3572855
theorem B2545835 : Blo 1056613 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B6773003 : Blo 1056613 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B2677121 : Blo 1056613 2677121 := bstep (se 2 (by rfl) ⟨1003920, by rfl⟩ : syracuseStep 2677121 = 2007841) B2007841
theorem B2382299 : Blo 1056613 2382299 := bstep (se 1 (by rfl) ⟨1786724, by rfl⟩ : syracuseStep 2382299 = 3573449) B3573449
theorem B2448083 : Blo 1056613 2448083 := bstep (se 1 (by rfl) ⟨1836062, by rfl⟩ : syracuseStep 2448083 = 3672125) B3672125
theorem B2382767 : Blo 1056613 2382767 := bstep (se 1 (by rfl) ⟨1787075, by rfl⟩ : syracuseStep 2382767 = 3574151) B3574151
theorem B2677931 : Blo 1056613 2677931 := bstep (se 1 (by rfl) ⟨2008448, by rfl⟩ : syracuseStep 2677931 = 4016897) B4016897
theorem B1694891 : Blo 1056613 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B2383019 : Blo 1056613 2383019 := bstep (se 1 (by rfl) ⟨1787264, by rfl⟩ : syracuseStep 2383019 = 3574529) B3574529
theorem B34331921 : Blo 1056613 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B6774131 : Blo 1056613 6774131 := bstep (se 1 (by rfl) ⟨5080598, by rfl⟩ : syracuseStep 6774131 = 10161197) B10161197
theorem B9035387 : Blo 1056613 9035387 := bstep (se 1 (by rfl) ⟨6776540, by rfl⟩ : syracuseStep 9035387 = 13553081) B13553081
theorem B2383559 : Blo 1056613 2383559 := bstep (se 1 (by rfl) ⟨1787669, by rfl⟩ : syracuseStep 2383559 = 3575339) B3575339
theorem B4022045 : Blo 1056613 4022045 := bstep (se 3 (by rfl) ⟨754133, by rfl⟩ : syracuseStep 4022045 = 1508267) B1508267
theorem B1695583 : Blo 1056613 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B12214151 : Blo 1056613 12214151 := bstep (se 1 (by rfl) ⟨9160613, by rfl⟩ : syracuseStep 12214151 = 18321227) B18321227
theorem B1269679 : Blo 1056613 1269679 := bstep (se 1 (by rfl) ⟨952259, by rfl⟩ : syracuseStep 1269679 = 1904519) B1904519
theorem B2678791 : Blo 1056613 2678791 := bstep (se 1 (by rfl) ⟨2009093, by rfl⟩ : syracuseStep 2678791 = 4018187) B4018187
theorem B4284683 : Blo 1056613 4284683 := bstep (se 1 (by rfl) ⟨3213512, by rfl⟩ : syracuseStep 4284683 = 6427025) B6427025
theorem B4022729 : Blo 1056613 4022729 := bstep (se 2 (by rfl) ⟨1508523, by rfl⟩ : syracuseStep 4022729 = 3017047) B3017047
theorem B6873623 : Blo 1056613 6873623 := bstep (se 1 (by rfl) ⟨5155217, by rfl⟩ : syracuseStep 6873623 = 10310435) B10310435
theorem B2384423 : Blo 1056613 2384423 := bstep (se 1 (by rfl) ⟨1788317, by rfl⟩ : syracuseStep 2384423 = 3576635) B3576635
theorem B4514363 : Blo 1056613 4514363 := bstep (se 1 (by rfl) ⟨3385772, by rfl⟩ : syracuseStep 4514363 = 6771545) B6771545
theorem B2417249 : Blo 1056613 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B2679419 : Blo 1056613 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B11428715 : Blo 1056613 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B2384747 : Blo 1056613 2384747 := bstep (se 1 (by rfl) ⟨1788560, by rfl⟩ : syracuseStep 2384747 = 3577121) B3577121
theorem B2679713 : Blo 1056613 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B2384801 : Blo 1056613 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B4023215 : Blo 1056613 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B9168025 : Blo 1056613 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B2385143 : Blo 1056613 2385143 := bstep (se 1 (by rfl) ⟨1788857, by rfl⟩ : syracuseStep 2385143 = 3577715) B3577715
theorem B12051827 : Blo 1056613 12051827 := bstep (se 1 (by rfl) ⟨9038870, by rfl⟩ : syracuseStep 12051827 = 18077741) B18077741
theorem B4024019 : Blo 1056613 4024019 := bstep (se 1 (by rfl) ⟨3018014, by rfl⟩ : syracuseStep 4024019 = 6036029) B6036029
theorem B5727959 : Blo 1056613 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B5367545 : Blo 1056613 5367545 := bstep (se 2 (by rfl) ⟨2012829, by rfl⟩ : syracuseStep 5367545 = 4025659) B4025659
theorem B2385737 : Blo 1056613 2385737 := bstep (se 2 (by rfl) ⟨894651, by rfl⟩ : syracuseStep 2385737 = 1789303) B1789303
theorem B4515745 : Blo 1056613 4515745 := bstep (se 2 (by rfl) ⟨1693404, by rfl⟩ : syracuseStep 4515745 = 3386809) B3386809
theorem B9037777 : Blo 1056613 9037777 := bstep (se 2 (by rfl) ⟨3389166, by rfl⟩ : syracuseStep 9037777 = 6778333) B6778333
theorem B1337467 : Blo 1056613 1337467 := bstep (se 1 (by rfl) ⟨1003100, by rfl⟩ : syracuseStep 1337467 = 2006201) B2006201
theorem B5368193 : Blo 1056613 5368193 := bstep (se 2 (by rfl) ⟨2013072, by rfl⟩ : syracuseStep 5368193 = 4026145) B4026145
theorem B4516361 : Blo 1056613 4516361 := bstep (se 2 (by rfl) ⟨1693635, by rfl⟩ : syracuseStep 4516361 = 3387271) B3387271
theorem B3566105 : Blo 1056613 3566105 := bstep (se 2 (by rfl) ⟨1337289, by rfl⟩ : syracuseStep 3566105 = 2674579) B2674579
theorem B2681383 : Blo 1056613 2681383 := bstep (se 1 (by rfl) ⟨2011037, by rfl⟩ : syracuseStep 2681383 = 4022075) B4022075
theorem B8579843 : Blo 1056613 8579843 := bstep (se 1 (by rfl) ⟨6434882, by rfl⟩ : syracuseStep 8579843 = 12869765) B12869765
theorem B2681707 : Blo 1056613 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B8580097 : Blo 1056613 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B3533881 : Blo 1056613 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B5369003 : Blo 1056613 5369003 := bstep (se 1 (by rfl) ⟨4026752, by rfl⟩ : syracuseStep 5369003 = 8053505) B8053505
theorem B2682355 : Blo 1056613 2682355 := bstep (se 1 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 2682355 = 4023533) B4023533
theorem B3567239 : Blo 1056613 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B3567293 : Blo 1056613 3567293 := bstep (se 3 (by rfl) ⟨668867, by rfl⟩ : syracuseStep 3567293 = 1337735) B1337735
theorem B3010247 : Blo 1056613 3010247 := bstep (se 1 (by rfl) ⟨2257685, by rfl⟩ : syracuseStep 3010247 = 4515371) B4515371
theorem B1633991 : Blo 1056613 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B3567455 : Blo 1056613 3567455 := bstep (se 1 (by rfl) ⟨2675591, by rfl⟩ : syracuseStep 3567455 = 5351183) B5351183
theorem B1339355 : Blo 1056613 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B3567617 : Blo 1056613 3567617 := bstep (se 2 (by rfl) ⟨1337856, by rfl⟩ : syracuseStep 3567617 = 2675713) B2675713
theorem B11464733 : Blo 1056613 11464733 := bstep (se 3 (by rfl) ⟨2149637, by rfl⟩ : syracuseStep 11464733 = 4299275) B4299275
theorem B4026449 : Blo 1056613 4026449 := bstep (se 2 (by rfl) ⟨1509918, by rfl⟩ : syracuseStep 4026449 = 3019837) B3019837
theorem B5501245 : Blo 1056613 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B1339831 : Blo 1056613 1339831 := bstep (se 1 (by rfl) ⟨1004873, by rfl⟩ : syracuseStep 1339831 = 2009747) B2009747
theorem B4026905 : Blo 1056613 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B2683489 : Blo 1056613 2683489 := bstep (se 2 (by rfl) ⟨1006308, by rfl⟩ : syracuseStep 2683489 = 2012617) B2012617
theorem B4289273 : Blo 1056613 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B3568427 : Blo 1056613 3568427 := bstep (se 1 (by rfl) ⟨2676320, by rfl⟩ : syracuseStep 3568427 = 5352641) B5352641
theorem B3011489 : Blo 1056613 3011489 := bstep (se 2 (by rfl) ⟨1129308, by rfl⟩ : syracuseStep 3011489 = 2258617) B2258617
theorem B3568697 : Blo 1056613 3568697 := bstep (se 2 (by rfl) ⟨1338261, by rfl⟩ : syracuseStep 3568697 = 2676523) B2676523
theorem B3569021 : Blo 1056613 3569021 := bstep (se 3 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 3569021 = 1338383) B1338383
theorem B2684441 : Blo 1056613 2684441 := bstep (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) B2013331
theorem B3569291 : Blo 1056613 3569291 := bstep (se 1 (by rfl) ⟨2676968, by rfl⟩ : syracuseStep 3569291 = 5353937) B5353937
theorem B1341127 : Blo 1056613 1341127 := bstep (se 1 (by rfl) ⟨1005845, by rfl⟩ : syracuseStep 1341127 = 2011691) B2011691
theorem B2258761 : Blo 1056613 2258761 := bstep (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) B1694071
theorem B1505243 : Blo 1056613 1505243 := bstep (se 1 (by rfl) ⟨1128932, by rfl⟩ : syracuseStep 1505243 = 2257865) B2257865
theorem B17201251 : Blo 1056613 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B3570209 : Blo 1056613 3570209 := bstep (se 2 (by rfl) ⟨1338828, by rfl⟩ : syracuseStep 3570209 = 2677657) B2677657
theorem B12221063 : Blo 1056613 12221063 := bstep (se 1 (by rfl) ⟨9165797, by rfl⟩ : syracuseStep 12221063 = 18331595) B18331595
theorem B41286323 : Blo 1056613 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B2259667 : Blo 1056613 2259667 := bstep (se 1 (by rfl) ⟨1694750, by rfl⟩ : syracuseStep 2259667 = 3389501) B3389501
theorem B3570425 : Blo 1056613 3570425 := bstep (se 2 (by rfl) ⟨1338909, by rfl⟩ : syracuseStep 3570425 = 2677819) B2677819
theorem B3570695 : Blo 1056613 3570695 := bstep (se 1 (by rfl) ⟨2678021, by rfl⟩ : syracuseStep 3570695 = 5356043) B5356043
theorem B3570803 : Blo 1056613 3570803 := bstep (se 1 (by rfl) ⟨2678102, by rfl⟩ : syracuseStep 3570803 = 5356205) B5356205
theorem B3571073 : Blo 1056613 3571073 := bstep (se 2 (by rfl) ⟨1339152, by rfl⟩ : syracuseStep 3571073 = 2678305) B2678305
theorem B24444341 : Blo 1056613 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B3014131 : Blo 1056613 3014131 := bstep (se 1 (by rfl) ⟨2260598, by rfl⟩ : syracuseStep 3014131 = 4521197) B4521197
theorem B7634681 : Blo 1056613 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B3571721 : Blo 1056613 3571721 := bstep (se 2 (by rfl) ⟨1339395, by rfl⟩ : syracuseStep 3571721 = 2678791) B2678791
theorem B1507675 : Blo 1056613 1507675 := bstep (se 1 (by rfl) ⟨1130756, by rfl⟩ : syracuseStep 1507675 = 2261513) B2261513
theorem B3015805 : Blo 1056613 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B12224033 : Blo 1056613 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B6030881 : Blo 1056613 6030881 := bstep (se 2 (by rfl) ⟨2261580, by rfl⟩ : syracuseStep 6030881 = 4523161) B4523161
theorem B1837007 : Blo 1056613 1837007 := bstep (se 1 (by rfl) ⟨1377755, by rfl⟩ : syracuseStep 1837007 = 2755511) B2755511
theorem B2262991 : Blo 1056613 2262991 := bstep (se 1 (by rfl) ⟨1697243, by rfl⟩ : syracuseStep 2262991 = 3394487) B3394487
theorem B10192877 : Blo 1056613 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B6785153 : Blo 1056613 6785153 := bstep (se 2 (by rfl) ⟨2544432, by rfl⟩ : syracuseStep 6785153 = 5088865) B5088865
theorem B22874723 : Blo 1056613 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B3574907 : Blo 1056613 3574907 := bstep (se 1 (by rfl) ⟨2681180, by rfl⟩ : syracuseStep 3574907 = 5362361) B5362361
theorem B30543095 : Blo 1056613 30543095 := bstep (se 1 (by rfl) ⟨22907321, by rfl⟩ : syracuseStep 30543095 = 45814643) B45814643
theorem B3575177 : Blo 1056613 3575177 := bstep (se 2 (by rfl) ⟨1340691, by rfl⟩ : syracuseStep 3575177 = 2681383) B2681383
theorem B9047483 : Blo 1056613 9047483 := bstep (se 1 (by rfl) ⟨6785612, by rfl⟩ : syracuseStep 9047483 = 13571225) B13571225
theorem B6032839 : Blo 1056613 6032839 := bstep (se 1 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 6032839 = 9049259) B9049259
theorem B3018323 : Blo 1056613 3018323 := bstep (se 1 (by rfl) ⟨2263742, by rfl⟩ : syracuseStep 3018323 = 4527485) B4527485
theorem B3575609 : Blo 1056613 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B3018653 : Blo 1056613 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B11440129 : Blo 1056613 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B6427289 : Blo 1056613 6427289 := bstep (se 2 (by rfl) ⟨2410233, by rfl⟩ : syracuseStep 6427289 = 4820467) B4820467
theorem B3576473 : Blo 1056613 3576473 := bstep (se 2 (by rfl) ⟨1341177, by rfl⟩ : syracuseStep 3576473 = 2682355) B2682355
theorem B10327421 : Blo 1056613 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B2758087 : Blo 1056613 2758087 := bstep (se 1 (by rfl) ⟨2068565, by rfl⟩ : syracuseStep 2758087 = 4137131) B4137131
theorem B2856455 : Blo 1056613 2856455 := bstep (se 1 (by rfl) ⟨2142341, by rfl⟩ : syracuseStep 2856455 = 4284683) B4284683
theorem B1611499 : Blo 1056613 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B6788893 : Blo 1056613 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B6035255 : Blo 1056613 6035255 := bstep (se 1 (by rfl) ⟨4526441, by rfl⟩ : syracuseStep 6035255 = 9052883) B9052883
theorem B3577985 : Blo 1056613 3577985 := bstep (se 2 (by rfl) ⟨1341744, by rfl⟩ : syracuseStep 3577985 = 2683489) B2683489
theorem B8034551 : Blo 1056613 8034551 := bstep (se 1 (by rfl) ⟨6025913, by rfl⟩ : syracuseStep 8034551 = 12051827) B12051827
theorem B7739725 : Blo 1056613 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B3578363 : Blo 1056613 3578363 := bstep (se 1 (by rfl) ⟨2683772, by rfl⟩ : syracuseStep 3578363 = 5367545) B5367545
theorem B9050899 : Blo 1056613 9050899 := bstep (se 1 (by rfl) ⟨6788174, by rfl⟩ : syracuseStep 9050899 = 13576349) B13576349
theorem B3578795 : Blo 1056613 3578795 := bstep (se 1 (by rfl) ⟨2684096, by rfl⟩ : syracuseStep 3578795 = 5368193) B5368193
theorem B6528221 : Blo 1056613 6528221 := bstep (se 3 (by rfl) ⟨1224041, by rfl⟩ : syracuseStep 6528221 = 2448083) B2448083
theorem B3579335 : Blo 1056613 3579335 := bstep (se 1 (by rfl) ⟨2684501, by rfl⟩ : syracuseStep 3579335 = 5369003) B5369003
theorem B13770263 : Blo 1056613 13770263 := bstep (se 1 (by rfl) ⟨10327697, by rfl⟩ : syracuseStep 13770263 = 20655395) B20655395
theorem B6790817 : Blo 1056613 6790817 := bstep (se 2 (by rfl) ⟨2546556, by rfl⟩ : syracuseStep 6790817 = 5093113) B5093113
theorem B2006831 : Blo 1056613 2006831 := bstep (se 1 (by rfl) ⟨1505123, by rfl⟩ : syracuseStep 2006831 = 3010247) B3010247
theorem B1056667 : Blo 1056613 1056667 := bstep (se 1 (by rfl) ⟨792500, by rfl⟩ : syracuseStep 1056667 = 1585001) B1585001
theorem B1056719 : Blo 1056613 1056719 := bstep (se 1 (by rfl) ⟨792539, by rfl⟩ : syracuseStep 1056719 = 1585079) B1585079
theorem B1056743 : Blo 1056613 1056743 := bstep (se 1 (by rfl) ⟨792557, by rfl⟩ : syracuseStep 1056743 = 1585115) B1585115
theorem B7643155 : Blo 1056613 7643155 := bstep (se 1 (by rfl) ⟨5732366, by rfl⟩ : syracuseStep 7643155 = 11464733) B11464733
theorem B5349401 : Blo 1056613 5349401 := bstep (se 2 (by rfl) ⟨2006025, by rfl⟩ : syracuseStep 5349401 = 4012051) B4012051
theorem B9674801 : Blo 1056613 9674801 := bstep (se 2 (by rfl) ⟨3628050, by rfl⟩ : syracuseStep 9674801 = 7256101) B7256101
theorem B5087441 : Blo 1056613 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B1057055 : Blo 1056613 1057055 := bstep (se 1 (by rfl) ⟨792791, by rfl⟩ : syracuseStep 1057055 = 1585583) B1585583
theorem B10166579 : Blo 1056613 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B1057115 : Blo 1056613 1057115 := bstep (se 1 (by rfl) ⟨792836, by rfl⟩ : syracuseStep 1057115 = 1585673) B1585673
theorem B1057135 : Blo 1056613 1057135 := bstep (se 1 (by rfl) ⟨792851, by rfl⟩ : syracuseStep 1057135 = 1585703) B1585703
theorem B1057191 : Blo 1056613 1057191 := bstep (se 1 (by rfl) ⟨792893, by rfl⟩ : syracuseStep 1057191 = 1585787) B1585787
theorem B1057275 : Blo 1056613 1057275 := bstep (se 1 (by rfl) ⟨792956, by rfl⟩ : syracuseStep 1057275 = 1585913) B1585913
theorem B2859515 : Blo 1056613 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B1057343 : Blo 1056613 1057343 := bstep (se 1 (by rfl) ⟨793007, by rfl⟩ : syracuseStep 1057343 = 1586015) B1586015
theorem B1057351 : Blo 1056613 1057351 := bstep (se 1 (by rfl) ⟨793013, by rfl⟩ : syracuseStep 1057351 = 1586027) B1586027
theorem B2007659 : Blo 1056613 2007659 := bstep (se 1 (by rfl) ⟨1505744, by rfl⟩ : syracuseStep 2007659 = 3011489) B3011489
theorem B1057503 : Blo 1056613 1057503 := bstep (se 1 (by rfl) ⟨793127, by rfl⟩ : syracuseStep 1057503 = 1586255) B1586255
theorem B1057583 : Blo 1056613 1057583 := bstep (se 1 (by rfl) ⟨793187, by rfl⟩ : syracuseStep 1057583 = 1586375) B1586375
theorem B1057691 : Blo 1056613 1057691 := bstep (se 1 (by rfl) ⟨793268, by rfl⟩ : syracuseStep 1057691 = 1586537) B1586537
theorem B1057743 : Blo 1056613 1057743 := bstep (se 1 (by rfl) ⟨793307, by rfl⟩ : syracuseStep 1057743 = 1586615) B1586615
theorem B1057767 : Blo 1056613 1057767 := bstep (se 1 (by rfl) ⟨793325, by rfl⟩ : syracuseStep 1057767 = 1586651) B1586651
theorem B1909751 : Blo 1056613 1909751 := bstep (se 1 (by rfl) ⟨1432313, by rfl⟩ : syracuseStep 1909751 = 2864627) B2864627
theorem B6038671 : Blo 1056613 6038671 := bstep (se 1 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 6038671 = 9058007) B9058007
theorem B1058079 : Blo 1056613 1058079 := bstep (se 1 (by rfl) ⟨793559, by rfl⟩ : syracuseStep 1058079 = 1587119) B1587119
theorem B1058139 : Blo 1056613 1058139 := bstep (se 1 (by rfl) ⟨793604, by rfl⟩ : syracuseStep 1058139 = 1587209) B1587209
theorem B1058159 : Blo 1056613 1058159 := bstep (se 1 (by rfl) ⟨793619, by rfl⟩ : syracuseStep 1058159 = 1587239) B1587239
theorem B1058215 : Blo 1056613 1058215 := bstep (se 1 (by rfl) ⟨793661, by rfl⟩ : syracuseStep 1058215 = 1587323) B1587323
theorem B1058299 : Blo 1056613 1058299 := bstep (se 1 (by rfl) ⟨793724, by rfl⟩ : syracuseStep 1058299 = 1587449) B1587449
theorem B1058367 : Blo 1056613 1058367 := bstep (se 1 (by rfl) ⟨793775, by rfl⟩ : syracuseStep 1058367 = 1587551) B1587551
theorem B1058375 : Blo 1056613 1058375 := bstep (se 1 (by rfl) ⟨793781, by rfl⟩ : syracuseStep 1058375 = 1587563) B1587563
theorem B1189471 : Blo 1056613 1189471 := bstep (se 1 (by rfl) ⟨892103, by rfl⟩ : syracuseStep 1189471 = 1784207) B1784207
theorem B6039197 : Blo 1056613 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B1910459 : Blo 1056613 1910459 := bstep (se 1 (by rfl) ⟨1432844, by rfl⟩ : syracuseStep 1910459 = 2865689) B2865689
theorem B1058527 : Blo 1056613 1058527 := bstep (se 1 (by rfl) ⟨793895, by rfl⟩ : syracuseStep 1058527 = 1587791) B1587791
theorem B1058607 : Blo 1056613 1058607 := bstep (se 1 (by rfl) ⟨793955, by rfl⟩ : syracuseStep 1058607 = 1587911) B1587911
theorem B1058715 : Blo 1056613 1058715 := bstep (se 1 (by rfl) ⟨794036, by rfl⟩ : syracuseStep 1058715 = 1588073) B1588073
theorem B1058767 : Blo 1056613 1058767 := bstep (se 1 (by rfl) ⟨794075, by rfl⟩ : syracuseStep 1058767 = 1588151) B1588151
theorem B1058791 : Blo 1056613 1058791 := bstep (se 1 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 1058791 = 1588187) B1588187
theorem B1059103 : Blo 1056613 1059103 := bstep (se 1 (by rfl) ⟨794327, by rfl⟩ : syracuseStep 1059103 = 1588655) B1588655
theorem B16296227 : Blo 1056613 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B1059163 : Blo 1056613 1059163 := bstep (se 1 (by rfl) ⟨794372, by rfl⟩ : syracuseStep 1059163 = 1588745) B1588745
theorem B1059183 : Blo 1056613 1059183 := bstep (se 1 (by rfl) ⟨794387, by rfl⟩ : syracuseStep 1059183 = 1588775) B1588775
theorem B1059239 : Blo 1056613 1059239 := bstep (se 1 (by rfl) ⟨794429, by rfl⟩ : syracuseStep 1059239 = 1588859) B1588859
theorem B5089787 : Blo 1056613 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B1059323 : Blo 1056613 1059323 := bstep (se 1 (by rfl) ⟨794492, by rfl⟩ : syracuseStep 1059323 = 1588985) B1588985
theorem B1059391 : Blo 1056613 1059391 := bstep (se 1 (by rfl) ⟨794543, by rfl⟩ : syracuseStep 1059391 = 1589087) B1589087
theorem B1059399 : Blo 1056613 1059399 := bstep (se 1 (by rfl) ⟨794549, by rfl⟩ : syracuseStep 1059399 = 1589099) B1589099
theorem B1190623 : Blo 1056613 1190623 := bstep (se 1 (by rfl) ⟨892967, by rfl⟩ : syracuseStep 1190623 = 1785935) B1785935
theorem B1059551 : Blo 1056613 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B5090039 : Blo 1056613 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B1059631 : Blo 1056613 1059631 := bstep (se 1 (by rfl) ⟨794723, by rfl⟩ : syracuseStep 1059631 = 1589447) B1589447
theorem B5352317 : Blo 1056613 5352317 := bstep (se 3 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 5352317 = 2007119) B2007119
theorem B1059739 : Blo 1056613 1059739 := bstep (se 1 (by rfl) ⟨794804, by rfl⟩ : syracuseStep 1059739 = 1589609) B1589609
theorem B1059791 : Blo 1056613 1059791 := bstep (se 1 (by rfl) ⟨794843, by rfl⟩ : syracuseStep 1059791 = 1589687) B1589687
theorem B1059815 : Blo 1056613 1059815 := bstep (se 1 (by rfl) ⟨794861, by rfl⟩ : syracuseStep 1059815 = 1589723) B1589723
theorem B1191199 : Blo 1056613 1191199 := bstep (se 1 (by rfl) ⟨893399, by rfl⟩ : syracuseStep 1191199 = 1786799) B1786799
theorem B1060127 : Blo 1056613 1060127 := bstep (se 1 (by rfl) ⟨795095, by rfl⟩ : syracuseStep 1060127 = 1590191) B1590191
theorem B1060187 : Blo 1056613 1060187 := bstep (se 1 (by rfl) ⟨795140, by rfl⟩ : syracuseStep 1060187 = 1590281) B1590281
theorem B1060207 : Blo 1056613 1060207 := bstep (se 1 (by rfl) ⟨795155, by rfl⟩ : syracuseStep 1060207 = 1590311) B1590311
theorem B2010491 : Blo 1056613 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B1060263 : Blo 1056613 1060263 := bstep (se 1 (by rfl) ⟨795197, by rfl⟩ : syracuseStep 1060263 = 1590395) B1590395
theorem B1060347 : Blo 1056613 1060347 := bstep (se 1 (by rfl) ⟨795260, by rfl⟩ : syracuseStep 1060347 = 1590521) B1590521
theorem B1191487 : Blo 1056613 1191487 := bstep (se 1 (by rfl) ⟨893615, by rfl⟩ : syracuseStep 1191487 = 1787231) B1787231
theorem B1060415 : Blo 1056613 1060415 := bstep (se 1 (by rfl) ⟨795311, by rfl⟩ : syracuseStep 1060415 = 1590623) B1590623
theorem B1060423 : Blo 1056613 1060423 := bstep (se 1 (by rfl) ⟨795317, by rfl⟩ : syracuseStep 1060423 = 1590635) B1590635
theorem B2010719 : Blo 1056613 2010719 := bstep (se 1 (by rfl) ⟨1508039, by rfl⟩ : syracuseStep 2010719 = 3016079) B3016079
theorem B3387041 : Blo 1056613 3387041 := bstep (se 2 (by rfl) ⟨1270140, by rfl⟩ : syracuseStep 3387041 = 2540281) B2540281
theorem B1060575 : Blo 1056613 1060575 := bstep (se 1 (by rfl) ⟨795431, by rfl⟩ : syracuseStep 1060575 = 1590863) B1590863
theorem B5353289 : Blo 1056613 5353289 := bstep (se 2 (by rfl) ⟨2007483, by rfl⟩ : syracuseStep 5353289 = 4014967) B4014967
theorem B10170269 : Blo 1056613 10170269 := bstep (se 3 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 10170269 = 3813851) B3813851
theorem B1585103 : Blo 1056613 1585103 := bstep (se 1 (by rfl) ⟨1188827, by rfl⟩ : syracuseStep 1585103 = 2377655) B2377655
theorem B1585499 : Blo 1056613 1585499 := bstep (se 1 (by rfl) ⟨1189124, by rfl⟩ : syracuseStep 1585499 = 2378249) B2378249
theorem B1192315 : Blo 1056613 1192315 := bstep (se 1 (by rfl) ⟨894236, by rfl⟩ : syracuseStep 1192315 = 1788473) B1788473
theorem B12038705 : Blo 1056613 12038705 := bstep (se 2 (by rfl) ⟨4514514, by rfl⟩ : syracuseStep 12038705 = 9029029) B9029029
theorem B1585727 : Blo 1056613 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B1585847 : Blo 1056613 1585847 := bstep (se 1 (by rfl) ⟨1189385, by rfl⟩ : syracuseStep 1585847 = 2378771) B2378771
theorem B1716919 : Blo 1056613 1716919 := bstep (se 1 (by rfl) ⟨1287689, by rfl⟩ : syracuseStep 1716919 = 2575379) B2575379
theorem B5092055 : Blo 1056613 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B1356623 : Blo 1056613 1356623 := bstep (se 1 (by rfl) ⟨1017467, by rfl⟩ : syracuseStep 1356623 = 2034935) B2034935
theorem B1192783 : Blo 1056613 1192783 := bstep (se 1 (by rfl) ⟨894587, by rfl⟩ : syracuseStep 1192783 = 1789175) B1789175
theorem B1586075 : Blo 1056613 1586075 := bstep (se 1 (by rfl) ⟨1189556, by rfl⟩ : syracuseStep 1586075 = 2379113) B2379113
theorem B5354585 : Blo 1056613 5354585 := bstep (se 2 (by rfl) ⟨2007969, by rfl⟩ : syracuseStep 5354585 = 4015939) B4015939
theorem B38581373 : Blo 1056613 38581373 := bstep (se 3 (by rfl) ⟨7234007, by rfl⟩ : syracuseStep 38581373 = 14468015) B14468015
theorem B1193179 : Blo 1056613 1193179 := bstep (se 1 (by rfl) ⟨894884, by rfl⟩ : syracuseStep 1193179 = 1789769) B1789769
theorem B1586471 : Blo 1056613 1586471 := bstep (se 1 (by rfl) ⟨1189853, by rfl⟩ : syracuseStep 1586471 = 2379707) B2379707
theorem B1586555 : Blo 1056613 1586555 := bstep (se 1 (by rfl) ⟨1189916, by rfl⟩ : syracuseStep 1586555 = 2379833) B2379833
theorem B1783289 : Blo 1056613 1783289 := bstep (se 2 (by rfl) ⟨668733, by rfl⟩ : syracuseStep 1783289 = 1337467) B1337467
theorem B1586681 : Blo 1056613 1586681 := bstep (se 2 (by rfl) ⟨595005, by rfl⟩ : syracuseStep 1586681 = 1190011) B1190011
theorem B1586783 : Blo 1056613 1586783 := bstep (se 1 (by rfl) ⟨1190087, by rfl⟩ : syracuseStep 1586783 = 2380175) B2380175
theorem B1783559 : Blo 1056613 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B1586999 : Blo 1056613 1586999 := bstep (se 1 (by rfl) ⟨1190249, by rfl⟩ : syracuseStep 1586999 = 2380499) B2380499
theorem B8042327 : Blo 1056613 8042327 := bstep (se 1 (by rfl) ⟨6031745, by rfl⟩ : syracuseStep 8042327 = 12063491) B12063491
theorem B21706795 : Blo 1056613 21706795 := bstep (se 1 (by rfl) ⟨16280096, by rfl⟩ : syracuseStep 21706795 = 32560193) B32560193
theorem B1587305 : Blo 1056613 1587305 := bstep (se 2 (by rfl) ⟨595239, by rfl⟩ : syracuseStep 1587305 = 1190479) B1190479
theorem B1587623 : Blo 1056613 1587623 := bstep (se 1 (by rfl) ⟨1190717, by rfl⟩ : syracuseStep 1587623 = 2381435) B2381435
theorem B1784315 : Blo 1056613 1784315 := bstep (se 1 (by rfl) ⟨1338236, by rfl⟩ : syracuseStep 1784315 = 2676473) B2676473
theorem B1587707 : Blo 1056613 1587707 := bstep (se 1 (by rfl) ⟨1190780, by rfl⟩ : syracuseStep 1587707 = 2381561) B2381561
theorem B1587833 : Blo 1056613 1587833 := bstep (se 2 (by rfl) ⟨595437, by rfl⟩ : syracuseStep 1587833 = 1190875) B1190875
theorem B1587887 : Blo 1056613 1587887 := bstep (se 1 (by rfl) ⟨1190915, by rfl⟩ : syracuseStep 1587887 = 2381831) B2381831
theorem B1587935 : Blo 1056613 1587935 := bstep (se 1 (by rfl) ⟨1190951, by rfl⟩ : syracuseStep 1587935 = 2381903) B2381903
theorem B2145179 : Blo 1056613 2145179 := bstep (se 1 (by rfl) ⟨1608884, by rfl⟩ : syracuseStep 2145179 = 3217769) B3217769
theorem B1784747 : Blo 1056613 1784747 := bstep (se 1 (by rfl) ⟨1338560, by rfl⟩ : syracuseStep 1784747 = 2677121) B2677121
theorem B1588199 : Blo 1056613 1588199 := bstep (se 1 (by rfl) ⟨1191149, by rfl⟩ : syracuseStep 1588199 = 2382299) B2382299
theorem B5094515 : Blo 1056613 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B1588457 : Blo 1056613 1588457 := bstep (se 2 (by rfl) ⟨595671, by rfl⟩ : syracuseStep 1588457 = 1191343) B1191343
theorem B1588511 : Blo 1056613 1588511 := bstep (se 1 (by rfl) ⟨1191383, by rfl⟩ : syracuseStep 1588511 = 2382767) B2382767
theorem B1785287 : Blo 1056613 1785287 := bstep (se 1 (by rfl) ⟨1338965, by rfl⟩ : syracuseStep 1785287 = 2677931) B2677931
theorem B1588679 : Blo 1056613 1588679 := bstep (se 1 (by rfl) ⟨1191509, by rfl⟩ : syracuseStep 1588679 = 2383019) B2383019
theorem B5357015 : Blo 1056613 5357015 := bstep (se 1 (by rfl) ⟨4017761, by rfl⟩ : syracuseStep 5357015 = 8035523) B8035523
theorem B3816953 : Blo 1056613 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B22887947 : Blo 1056613 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B9059921 : Blo 1056613 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B1589033 : Blo 1056613 1589033 := bstep (se 2 (by rfl) ⟨595887, by rfl⟩ : syracuseStep 1589033 = 1191775) B1191775
theorem B1589039 : Blo 1056613 1589039 := bstep (se 1 (by rfl) ⟨1191779, by rfl⟩ : syracuseStep 1589039 = 2383559) B2383559
theorem B9027389 : Blo 1056613 9027389 := bstep (se 3 (by rfl) ⟨1692635, by rfl⟩ : syracuseStep 9027389 = 3385271) B3385271
theorem B15482713 : Blo 1056613 15482713 := bstep (se 2 (by rfl) ⟨5806017, by rfl⟩ : syracuseStep 15482713 = 11612035) B11612035
theorem B4013981 : Blo 1056613 4013981 := bstep (se 3 (by rfl) ⟨752621, by rfl⟩ : syracuseStep 4013981 = 1505243) B1505243
theorem B8142767 : Blo 1056613 8142767 := bstep (se 1 (by rfl) ⟨6107075, by rfl⟩ : syracuseStep 8142767 = 12214151) B12214151
theorem B5423129 : Blo 1056613 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B1589513 : Blo 1056613 1589513 := bstep (se 2 (by rfl) ⟨596067, by rfl⟩ : syracuseStep 1589513 = 1192135) B1192135
theorem B1589615 : Blo 1056613 1589615 := bstep (se 1 (by rfl) ⟨1192211, by rfl⟩ : syracuseStep 1589615 = 2384423) B2384423
theorem B1786279 : Blo 1056613 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B13746617 : Blo 1056613 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B7619143 : Blo 1056613 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B1589831 : Blo 1056613 1589831 := bstep (se 1 (by rfl) ⟨1192373, by rfl⟩ : syracuseStep 1589831 = 2384747) B2384747
theorem B1786441 : Blo 1056613 1786441 := bstep (se 2 (by rfl) ⟨669915, by rfl⟩ : syracuseStep 1786441 = 1339831) B1339831
theorem B1786475 : Blo 1056613 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B1589867 : Blo 1056613 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B22921931 : Blo 1056613 22921931 := bstep (se 1 (by rfl) ⟨17191448, by rfl⟩ : syracuseStep 22921931 = 34382897) B34382897
theorem B1590095 : Blo 1056613 1590095 := bstep (se 1 (by rfl) ⟨1192571, by rfl⟩ : syracuseStep 1590095 = 2385143) B2385143
theorem B3818639 : Blo 1056613 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B5096591 : Blo 1056613 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B1590491 : Blo 1056613 1590491 := bstep (se 1 (by rfl) ⟨1192868, by rfl⟩ : syracuseStep 1590491 = 2385737) B2385737
theorem B1590665 : Blo 1056613 1590665 := bstep (se 2 (by rfl) ⟨596499, by rfl⟩ : syracuseStep 1590665 = 1192999) B1192999
theorem B8046215 : Blo 1056613 8046215 := bstep (se 1 (by rfl) ⟨6034661, by rfl⟩ : syracuseStep 8046215 = 12069323) B12069323
theorem B2377403 : Blo 1056613 2377403 := bstep (se 1 (by rfl) ⟨1783052, by rfl⟩ : syracuseStep 2377403 = 3566105) B3566105
theorem B2377529 : Blo 1056613 2377529 := bstep (se 2 (by rfl) ⟨891573, by rfl⟩ : syracuseStep 2377529 = 1783147) B1783147
theorem B125617985 : Blo 1056613 125617985 := bstep (se 2 (by rfl) ⟨47106744, by rfl⟩ : syracuseStep 125617985 = 94213489) B94213489
theorem B5719895 : Blo 1056613 5719895 := bstep (se 1 (by rfl) ⟨4289921, by rfl⟩ : syracuseStep 5719895 = 8579843) B8579843
theorem B19318661 : Blo 1056613 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B19318711 : Blo 1056613 19318711 := bstep (se 1 (by rfl) ⟨14489033, by rfl⟩ : syracuseStep 19318711 = 28978067) B28978067
theorem B13551745 : Blo 1056613 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B1788169 : Blo 1056613 1788169 := bstep (se 2 (by rfl) ⟨670563, by rfl⟩ : syracuseStep 1788169 = 1341127) B1341127
theorem B2378159 : Blo 1056613 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B2378195 : Blo 1056613 2378195 := bstep (se 1 (by rfl) ⟨1783646, by rfl⟩ : syracuseStep 2378195 = 3567293) B3567293
theorem B2378303 : Blo 1056613 2378303 := bstep (se 1 (by rfl) ⟨1783727, by rfl⟩ : syracuseStep 2378303 = 3567455) B3567455
theorem B2378411 : Blo 1056613 2378411 := bstep (se 1 (by rfl) ⟨1783808, by rfl⟩ : syracuseStep 2378411 = 3567617) B3567617
theorem B9030365 : Blo 1056613 9030365 := bstep (se 3 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 9030365 = 3386387) B3386387
theorem B2378951 : Blo 1056613 2378951 := bstep (se 1 (by rfl) ⟨1784213, by rfl⟩ : syracuseStep 2378951 = 3568427) B3568427
theorem B2379131 : Blo 1056613 2379131 := bstep (se 1 (by rfl) ⟨1784348, by rfl⟩ : syracuseStep 2379131 = 3568697) B3568697
theorem B2379257 : Blo 1056613 2379257 := bstep (se 2 (by rfl) ⟨892221, by rfl⟩ : syracuseStep 2379257 = 1784443) B1784443
theorem B2379347 : Blo 1056613 2379347 := bstep (se 1 (by rfl) ⟨1784510, by rfl⟩ : syracuseStep 2379347 = 3569021) B3569021
theorem B1789627 : Blo 1056613 1789627 := bstep (se 1 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 1789627 = 2684441) B2684441
theorem B2379527 : Blo 1056613 2379527 := bstep (se 1 (by rfl) ⟨1784645, by rfl⟩ : syracuseStep 2379527 = 3569291) B3569291
theorem B5361875 : Blo 1056613 5361875 := bstep (se 1 (by rfl) ⟨4021406, by rfl⟩ : syracuseStep 5361875 = 8042813) B8042813
theorem B2380139 : Blo 1056613 2380139 := bstep (se 1 (by rfl) ⟨1785104, by rfl⟩ : syracuseStep 2380139 = 3570209) B3570209
theorem B8147375 : Blo 1056613 8147375 := bstep (se 1 (by rfl) ⟨6110531, by rfl⟩ : syracuseStep 8147375 = 12221063) B12221063
theorem B2380283 : Blo 1056613 2380283 := bstep (se 1 (by rfl) ⟨1785212, by rfl⟩ : syracuseStep 2380283 = 3570425) B3570425
theorem B5427809 : Blo 1056613 5427809 := bstep (se 2 (by rfl) ⟨2035428, by rfl⟩ : syracuseStep 5427809 = 4070857) B4070857
theorem B2380409 : Blo 1056613 2380409 := bstep (se 2 (by rfl) ⟨892653, by rfl⟩ : syracuseStep 2380409 = 1785307) B1785307
theorem B4018841 : Blo 1056613 4018841 := bstep (se 2 (by rfl) ⟨1507065, by rfl⟩ : syracuseStep 4018841 = 3014131) B3014131
theorem B2380463 : Blo 1056613 2380463 := bstep (se 1 (by rfl) ⟨1785347, by rfl⟩ : syracuseStep 2380463 = 3570695) B3570695
theorem B6017759 : Blo 1056613 6017759 := bstep (se 1 (by rfl) ⟨4513319, by rfl⟩ : syracuseStep 6017759 = 9026639) B9026639
theorem B2380535 : Blo 1056613 2380535 := bstep (se 1 (by rfl) ⟨1785401, by rfl⟩ : syracuseStep 2380535 = 3570803) B3570803
theorem B2380715 : Blo 1056613 2380715 := bstep (se 1 (by rfl) ⟨1785536, by rfl⟩ : syracuseStep 2380715 = 3571073) B3571073
theorem B8049617 : Blo 1056613 8049617 := bstep (se 2 (by rfl) ⟨3018606, by rfl⟩ : syracuseStep 8049617 = 6037213) B6037213
theorem B2675855 : Blo 1056613 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B1692905 : Blo 1056613 1692905 := bstep (se 2 (by rfl) ⟨634839, by rfl⟩ : syracuseStep 1692905 = 1269679) B1269679
theorem B3396907 : Blo 1056613 3396907 := bstep (se 1 (by rfl) ⟨2547680, by rfl⟩ : syracuseStep 3396907 = 5095361) B5095361
theorem B5658017 : Blo 1056613 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B4019645 : Blo 1056613 4019645 := bstep (se 3 (by rfl) ⟨753683, by rfl⟩ : syracuseStep 4019645 = 1507367) B1507367
theorem B2381255 : Blo 1056613 2381255 := bstep (se 1 (by rfl) ⟨1785941, by rfl⟩ : syracuseStep 2381255 = 3571883) B3571883
theorem B2545145 : Blo 1056613 2545145 := bstep (se 2 (by rfl) ⟨954429, by rfl⟩ : syracuseStep 2545145 = 1908859) B1908859
theorem B1431103 : Blo 1056613 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B9033403 : Blo 1056613 9033403 := bstep (se 1 (by rfl) ⟨6775052, by rfl⟩ : syracuseStep 9033403 = 13550105) B13550105
theorem B1857287 : Blo 1056613 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B2381615 : Blo 1056613 2381615 := bstep (se 1 (by rfl) ⟨1786211, by rfl⟩ : syracuseStep 2381615 = 3572423) B3572423
theorem B69556493 : Blo 1056613 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B2382191 : Blo 1056613 2382191 := bstep (se 1 (by rfl) ⟨1786643, by rfl⟩ : syracuseStep 2382191 = 3573287) B3573287
theorem B2382263 : Blo 1056613 2382263 := bstep (se 1 (by rfl) ⟨1786697, by rfl⟩ : syracuseStep 2382263 = 3573395) B3573395
theorem B2578963 : Blo 1056613 2578963 := bstep (se 1 (by rfl) ⟨1934222, by rfl⟩ : syracuseStep 2578963 = 3868445) B3868445
theorem B4020799 : Blo 1056613 4020799 := bstep (se 1 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 4020799 = 6031199) B6031199
theorem B2382407 : Blo 1056613 2382407 := bstep (se 1 (by rfl) ⟨1786805, by rfl⟩ : syracuseStep 2382407 = 3573611) B3573611
theorem B2382443 : Blo 1056613 2382443 := bstep (se 1 (by rfl) ⟨1786832, by rfl⟩ : syracuseStep 2382443 = 3573665) B3573665
theorem B2677495 : Blo 1056613 2677495 := bstep (se 1 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 2677495 = 4016243) B4016243
theorem B9034739 : Blo 1056613 9034739 := bstep (se 1 (by rfl) ⟨6776054, by rfl⟩ : syracuseStep 9034739 = 13552109) B13552109
theorem B2382839 : Blo 1056613 2382839 := bstep (se 1 (by rfl) ⟨1787129, by rfl⟩ : syracuseStep 2382839 = 3574259) B3574259
theorem B2677799 : Blo 1056613 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B2383199 : Blo 1056613 2383199 := bstep (se 1 (by rfl) ⟨1787399, by rfl⟩ : syracuseStep 2383199 = 3574799) B3574799
theorem B3431879 : Blo 1056613 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B1072711 : Blo 1056613 1072711 := bstep (se 1 (by rfl) ⟨804533, by rfl⟩ : syracuseStep 1072711 = 1609067) B1609067
theorem B6446753 : Blo 1056613 6446753 := bstep (se 2 (by rfl) ⟨2417532, by rfl⟩ : syracuseStep 6446753 = 4835065) B4835065
theorem B2383595 : Blo 1056613 2383595 := bstep (se 1 (by rfl) ⟨1787696, by rfl⟩ : syracuseStep 2383595 = 3575393) B3575393
theorem B52191017 : Blo 1056613 52191017 := bstep (se 2 (by rfl) ⟨19571631, by rfl⟩ : syracuseStep 52191017 = 39143263) B39143263
theorem B2383721 : Blo 1056613 2383721 := bstep (se 2 (by rfl) ⟨893895, by rfl⟩ : syracuseStep 2383721 = 1787791) B1787791
theorem B11427713 : Blo 1056613 11427713 := bstep (se 2 (by rfl) ⟨4285392, by rfl⟩ : syracuseStep 11427713 = 8570785) B8570785
theorem B6020993 : Blo 1056613 6020993 := bstep (se 2 (by rfl) ⟨2257872, by rfl⟩ : syracuseStep 6020993 = 4515745) B4515745
theorem B37674881 : Blo 1056613 37674881 := bstep (se 2 (by rfl) ⟨14128080, by rfl⟩ : syracuseStep 37674881 = 28256161) B28256161
theorem B12050369 : Blo 1056613 12050369 := bstep (se 2 (by rfl) ⟨4518888, by rfl⟩ : syracuseStep 12050369 = 9037777) B9037777
theorem B2679065 : Blo 1056613 2679065 := bstep (se 2 (by rfl) ⟨1004649, by rfl⟩ : syracuseStep 2679065 = 2009299) B2009299
theorem B13558103 : Blo 1056613 13558103 := bstep (se 1 (by rfl) ⟨10168577, by rfl⟩ : syracuseStep 13558103 = 20337155) B20337155
theorem B2384567 : Blo 1056613 2384567 := bstep (se 1 (by rfl) ⟨1788425, by rfl⟩ : syracuseStep 2384567 = 3576851) B3576851
theorem B2384783 : Blo 1056613 2384783 := bstep (se 1 (by rfl) ⟨1788587, by rfl⟩ : syracuseStep 2384783 = 3577175) B3577175
theorem B6775771 : Blo 1056613 6775771 := bstep (se 1 (by rfl) ⟨5081828, by rfl⟩ : syracuseStep 6775771 = 10163657) B10163657
theorem B2679905 : Blo 1056613 2679905 := bstep (se 2 (by rfl) ⟨1004964, by rfl⟩ : syracuseStep 2679905 = 2009929) B2009929
theorem B4285655 : Blo 1056613 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B1696987 : Blo 1056613 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B11461931 : Blo 1056613 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B4711841 : Blo 1056613 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B4515335 : Blo 1056613 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B2385503 : Blo 1056613 2385503 := bstep (se 1 (by rfl) ⟨1789127, by rfl⟩ : syracuseStep 2385503 = 3578255) B3578255
theorem B2385719 : Blo 1056613 2385719 := bstep (se 1 (by rfl) ⟨1789289, by rfl⟩ : syracuseStep 2385719 = 3578579) B3578579
theorem B5728087 : Blo 1056613 5728087 := bstep (se 1 (by rfl) ⟨4296065, by rfl⟩ : syracuseStep 5728087 = 8592131) B8592131
theorem B2386025 : Blo 1056613 2386025 := bstep (se 2 (by rfl) ⟨894759, by rfl⟩ : syracuseStep 2386025 = 1789519) B1789519
theorem B5728391 : Blo 1056613 5728391 := bstep (se 1 (by rfl) ⟨4296293, by rfl⟩ : syracuseStep 5728391 = 8592587) B8592587
theorem B4024505 : Blo 1056613 4024505 := bstep (se 2 (by rfl) ⟨1509189, by rfl⟩ : syracuseStep 4024505 = 3018379) B3018379
theorem B1337563 : Blo 1056613 1337563 := bstep (se 1 (by rfl) ⟨1003172, by rfl⟩ : syracuseStep 1337563 = 2006345) B2006345
theorem B4516087 : Blo 1056613 4516087 := bstep (se 1 (by rfl) ⟨3387065, by rfl⟩ : syracuseStep 4516087 = 6774131) B6774131
theorem B4024687 : Blo 1056613 4024687 := bstep (se 1 (by rfl) ⟨3018515, by rfl⟩ : syracuseStep 4024687 = 6037031) B6037031
theorem B6023591 : Blo 1056613 6023591 := bstep (se 1 (by rfl) ⟨4517693, by rfl⟩ : syracuseStep 6023591 = 9035387) B9035387
theorem B2681363 : Blo 1056613 2681363 := bstep (se 1 (by rfl) ⟨2011022, by rfl⟩ : syracuseStep 2681363 = 4022045) B4022045
theorem B3566159 : Blo 1056613 3566159 := bstep (se 1 (by rfl) ⟨2674619, by rfl⟩ : syracuseStep 3566159 = 5349239) B5349239
theorem B5728907 : Blo 1056613 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B25783193 : Blo 1056613 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B11430827 : Blo 1056613 11430827 := bstep (se 1 (by rfl) ⟨8573120, by rfl⟩ : syracuseStep 11430827 = 17146241) B17146241
theorem B2681819 : Blo 1056613 2681819 := bstep (se 1 (by rfl) ⟨2011364, by rfl⟩ : syracuseStep 2681819 = 4022729) B4022729
theorem B4582415 : Blo 1056613 4582415 := bstep (se 1 (by rfl) ⟨3436811, by rfl⟩ : syracuseStep 4582415 = 6873623) B6873623
theorem B3009575 : Blo 1056613 3009575 := bstep (se 1 (by rfl) ⟨2257181, by rfl⟩ : syracuseStep 3009575 = 4514363) B4514363
theorem B7334993 : Blo 1056613 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B2682143 : Blo 1056613 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B3567401 : Blo 1056613 3567401 := bstep (se 2 (by rfl) ⟨1337775, by rfl⟩ : syracuseStep 3567401 = 2675551) B2675551
theorem B1339183 : Blo 1056613 1339183 := bstep (se 1 (by rfl) ⟨1004387, by rfl⟩ : syracuseStep 1339183 = 2008775) B2008775
theorem B2682679 : Blo 1056613 2682679 := bstep (se 1 (by rfl) ⟨2012009, by rfl⟩ : syracuseStep 2682679 = 4024019) B4024019
theorem B10186955 : Blo 1056613 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B2683145 : Blo 1056613 2683145 := bstep (se 2 (by rfl) ⟨1006179, by rfl⟩ : syracuseStep 2683145 = 2012359) B2012359
theorem B1339679 : Blo 1056613 1339679 := bstep (se 1 (by rfl) ⟨1004759, by rfl⟩ : syracuseStep 1339679 = 2009519) B2009519
theorem B3010907 : Blo 1056613 3010907 := bstep (se 1 (by rfl) ⟨2258180, by rfl⟩ : syracuseStep 3010907 = 4516361) B4516361
theorem B10187183 : Blo 1056613 10187183 := bstep (se 1 (by rfl) ⟨7640387, by rfl⟩ : syracuseStep 10187183 = 15280775) B15280775
theorem B3011681 : Blo 1056613 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B2684137 : Blo 1056613 2684137 := bstep (se 2 (by rfl) ⟨1006551, by rfl⟩ : syracuseStep 2684137 = 2013103) B2013103
theorem B2684299 : Blo 1056613 2684299 := bstep (se 1 (by rfl) ⟨2013224, by rfl⟩ : syracuseStep 2684299 = 4026449) B4026449
theorem B22935001 : Blo 1056613 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B2684603 : Blo 1056613 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B4519709 : Blo 1056613 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B3569615 : Blo 1056613 3569615 := bstep (se 1 (by rfl) ⟨2677211, by rfl⟩ : syracuseStep 3569615 = 5354423) B5354423
theorem B3012889 : Blo 1056613 3012889 := bstep (se 2 (by rfl) ⟨1129833, by rfl⟩ : syracuseStep 3012889 = 2259667) B2259667
theorem B1341947 : Blo 1056613 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B3570587 : Blo 1056613 3570587 := bstep (se 1 (by rfl) ⟨2677940, by rfl⟩ : syracuseStep 3570587 = 5355881) B5355881
theorem B61963163 : Blo 1056613 61963163 := bstep (se 1 (by rfl) ⟨46472372, by rfl⟩ : syracuseStep 61963163 = 92944745) B92944745
theorem B27524215 : Blo 1056613 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B15236261 : Blo 1056613 15236261 := bstep (se 4 (by rfl) ⟨1428399, by rfl⟩ : syracuseStep 15236261 = 2856799) B2856799
theorem B9043109 : Blo 1056613 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B4357309 : Blo 1056613 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B5078369 : Blo 1056613 5078369 := bstep (se 2 (by rfl) ⟨1904388, by rfl⟩ : syracuseStep 5078369 = 3808777) B3808777
theorem B2719099 : Blo 1056613 2719099 := bstep (se 1 (by rfl) ⟨2039324, by rfl⟩ : syracuseStep 2719099 = 4078649) B4078649
theorem B1506809 : Blo 1056613 1506809 := bstep (se 2 (by rfl) ⟨565053, by rfl⟩ : syracuseStep 1506809 = 1130107) B1130107
theorem B2260487 : Blo 1056613 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B32603795 : Blo 1056613 32603795 := bstep (se 1 (by rfl) ⟨24452846, by rfl⟩ : syracuseStep 32603795 = 48905693) B48905693
theorem B3571613 : Blo 1056613 3571613 := bstep (se 3 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 3571613 = 1339355) B1339355
theorem B10190873 : Blo 1056613 10190873 := bstep (se 2 (by rfl) ⟨3821577, by rfl⟩ : syracuseStep 10190873 = 7643155) B7643155
theorem B3572477 : Blo 1056613 3572477 := bstep (se 3 (by rfl) ⟨669839, by rfl⟩ : syracuseStep 3572477 = 1339679) B1339679
theorem B10158857 : Blo 1056613 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B12879107 : Blo 1056613 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B4523435 : Blo 1056613 4523435 := bstep (se 1 (by rfl) ⟨3392576, by rfl⟩ : syracuseStep 4523435 = 6785153) B6785153
theorem B2262649 : Blo 1056613 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B17139437 : Blo 1056613 17139437 := bstep (se 3 (by rfl) ⟨3213644, by rfl⟩ : syracuseStep 17139437 = 6427289) B6427289
theorem B6031655 : Blo 1056613 6031655 := bstep (se 1 (by rfl) ⟨4523741, by rfl⟩ : syracuseStep 6031655 = 9047483) B9047483
theorem B7637449 : Blo 1056613 7637449 := bstep (se 2 (by rfl) ⟨2864043, by rfl⟩ : syracuseStep 7637449 = 5728087) B5728087
theorem B25758281 : Blo 1056613 25758281 := bstep (se 2 (by rfl) ⟨9659355, by rfl⟩ : syracuseStep 25758281 = 19318711) B19318711
theorem B3017321 : Blo 1056613 3017321 := bstep (se 2 (by rfl) ⟨1131495, by rfl⟩ : syracuseStep 3017321 = 2262991) B2262991
theorem B3574583 : Blo 1056613 3574583 := bstep (se 1 (by rfl) ⟨2680937, by rfl⟩ : syracuseStep 3574583 = 5361875) B5361875
theorem B8031149 : Blo 1056613 8031149 := bstep (se 3 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 8031149 = 3011681) B3011681
theorem B6884947 : Blo 1056613 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B1904303 : Blo 1056613 1904303 := bstep (se 1 (by rfl) ⟨1428227, by rfl⟩ : syracuseStep 1904303 = 2856455) B2856455
theorem B4952765 : Blo 1056613 4952765 := bstep (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) B1857287
theorem B3576905 : Blo 1056613 3576905 := bstep (se 2 (by rfl) ⟨1341339, by rfl⟩ : syracuseStep 3576905 = 2682679) B2682679
theorem B4527211 : Blo 1056613 4527211 := bstep (se 1 (by rfl) ⟨3395408, by rfl⟩ : syracuseStep 4527211 = 6790817) B6790817
theorem B4297835 : Blo 1056613 4297835 := bstep (se 1 (by rfl) ⟨3223376, by rfl⟩ : syracuseStep 4297835 = 6446753) B6446753
theorem B8033579 : Blo 1056613 8033579 := bstep (se 1 (by rfl) ⟨6025184, by rfl⟩ : syracuseStep 8033579 = 12050369) B12050369
theorem B1906343 : Blo 1056613 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B2857103 : Blo 1056613 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B7641287 : Blo 1056613 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B3578525 : Blo 1056613 3578525 := bstep (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) B1341947
theorem B3578849 : Blo 1056613 3578849 := bstep (se 2 (by rfl) ⟨1342068, by rfl⟩ : syracuseStep 3578849 = 2684137) B2684137
theorem B15277085 : Blo 1056613 15277085 := bstep (se 3 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 15277085 = 5728907) B5728907
theorem B4529209 : Blo 1056613 4529209 := bstep (se 2 (by rfl) ⟨1698453, by rfl⟩ : syracuseStep 4529209 = 3396907) B3396907
theorem B3579065 : Blo 1056613 3579065 := bstep (se 2 (by rfl) ⟨1342149, by rfl⟩ : syracuseStep 3579065 = 2684299) B2684299
theorem B3677449 : Blo 1056613 3677449 := bstep (se 2 (by rfl) ⟨1379043, by rfl⟩ : syracuseStep 3677449 = 2758087) B2758087
theorem B30580001 : Blo 1056613 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B3054943 : Blo 1056613 3054943 := bstep (se 1 (by rfl) ⟨2291207, by rfl⟩ : syracuseStep 3054943 = 4582415) B4582415
theorem B2006383 : Blo 1056613 2006383 := bstep (se 1 (by rfl) ⟨1504787, by rfl⟩ : syracuseStep 2006383 = 3009575) B3009575
theorem B1908137 : Blo 1056613 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B9051857 : Blo 1056613 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B1056735 : Blo 1056613 1056735 := bstep (se 1 (by rfl) ⟨792551, by rfl⟩ : syracuseStep 1056735 = 1585103) B1585103
theorem B28942393 : Blo 1056613 28942393 := bstep (se 2 (by rfl) ⟨10853397, by rfl⟩ : syracuseStep 28942393 = 21706795) B21706795
theorem B6791303 : Blo 1056613 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B1056999 : Blo 1056613 1056999 := bstep (se 1 (by rfl) ⟨792749, by rfl⟩ : syracuseStep 1056999 = 1585499) B1585499
theorem B2007271 : Blo 1056613 2007271 := bstep (se 1 (by rfl) ⟨1505453, by rfl⟩ : syracuseStep 2007271 = 3010907) B3010907
theorem B6791455 : Blo 1056613 6791455 := bstep (se 1 (by rfl) ⟨5093591, by rfl⟩ : syracuseStep 6791455 = 10187183) B10187183
theorem B1057151 : Blo 1056613 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B1057231 : Blo 1056613 1057231 := bstep (se 1 (by rfl) ⟨792923, by rfl⟩ : syracuseStep 1057231 = 1585847) B1585847
theorem B1057383 : Blo 1056613 1057383 := bstep (se 1 (by rfl) ⟨793037, by rfl⟩ : syracuseStep 1057383 = 1586075) B1586075
theorem B1057647 : Blo 1056613 1057647 := bstep (se 1 (by rfl) ⟨793235, by rfl⟩ : syracuseStep 1057647 = 1586471) B1586471
theorem B1057703 : Blo 1056613 1057703 := bstep (se 1 (by rfl) ⟨793277, by rfl⟩ : syracuseStep 1057703 = 1586555) B1586555
theorem B1188859 : Blo 1056613 1188859 := bstep (se 1 (by rfl) ⟨891644, by rfl⟩ : syracuseStep 1188859 = 1783289) B1783289
theorem B1057787 : Blo 1056613 1057787 := bstep (se 1 (by rfl) ⟨793340, by rfl⟩ : syracuseStep 1057787 = 1586681) B1586681
theorem B12067865 : Blo 1056613 12067865 := bstep (se 2 (by rfl) ⟨4525449, by rfl⟩ : syracuseStep 12067865 = 9050899) B9050899
theorem B1057855 : Blo 1056613 1057855 := bstep (se 1 (by rfl) ⟨793391, by rfl⟩ : syracuseStep 1057855 = 1586783) B1586783
theorem B1189039 : Blo 1056613 1189039 := bstep (se 1 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 1189039 = 1783559) B1783559
theorem B1057999 : Blo 1056613 1057999 := bstep (se 1 (by rfl) ⟨793499, by rfl⟩ : syracuseStep 1057999 = 1586999) B1586999
theorem B1058203 : Blo 1056613 1058203 := bstep (se 1 (by rfl) ⟨793652, by rfl⟩ : syracuseStep 1058203 = 1587305) B1587305
theorem B5809745 : Blo 1056613 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B1058415 : Blo 1056613 1058415 := bstep (se 1 (by rfl) ⟨793811, by rfl⟩ : syracuseStep 1058415 = 1587623) B1587623
theorem B1189543 : Blo 1056613 1189543 := bstep (se 1 (by rfl) ⟨892157, by rfl⟩ : syracuseStep 1189543 = 1784315) B1784315
theorem B1058471 : Blo 1056613 1058471 := bstep (se 1 (by rfl) ⟨793853, by rfl⟩ : syracuseStep 1058471 = 1587707) B1587707
theorem B1058555 : Blo 1056613 1058555 := bstep (se 1 (by rfl) ⟨793916, by rfl⟩ : syracuseStep 1058555 = 1587833) B1587833
theorem B1058591 : Blo 1056613 1058591 := bstep (se 1 (by rfl) ⟨793943, by rfl⟩ : syracuseStep 1058591 = 1587887) B1587887
theorem B1058623 : Blo 1056613 1058623 := bstep (se 1 (by rfl) ⟨793967, by rfl⟩ : syracuseStep 1058623 = 1587935) B1587935
theorem B1189831 : Blo 1056613 1189831 := bstep (se 1 (by rfl) ⟨892373, by rfl⟩ : syracuseStep 1189831 = 1784747) B1784747
theorem B1058799 : Blo 1056613 1058799 := bstep (se 1 (by rfl) ⟨794099, by rfl⟩ : syracuseStep 1058799 = 1588199) B1588199
theorem B1058971 : Blo 1056613 1058971 := bstep (se 1 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 1058971 = 1588457) B1588457
theorem B1059007 : Blo 1056613 1059007 := bstep (se 1 (by rfl) ⟨794255, by rfl⟩ : syracuseStep 1059007 = 1588511) B1588511
theorem B3385579 : Blo 1056613 3385579 := bstep (se 1 (by rfl) ⟨2539184, by rfl⟩ : syracuseStep 3385579 = 5078369) B5078369
theorem B1190191 : Blo 1056613 1190191 := bstep (se 1 (by rfl) ⟨892643, by rfl⟩ : syracuseStep 1190191 = 1785287) B1785287
theorem B1059119 : Blo 1056613 1059119 := bstep (se 1 (by rfl) ⟨794339, by rfl⟩ : syracuseStep 1059119 = 1588679) B1588679
theorem B6039947 : Blo 1056613 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B21735863 : Blo 1056613 21735863 := bstep (se 1 (by rfl) ⟨16301897, by rfl⟩ : syracuseStep 21735863 = 32603795) B32603795
theorem B1059355 : Blo 1056613 1059355 := bstep (se 1 (by rfl) ⟨794516, by rfl⟩ : syracuseStep 1059355 = 1589033) B1589033
theorem B1059359 : Blo 1056613 1059359 := bstep (se 1 (by rfl) ⟨794519, by rfl⟩ : syracuseStep 1059359 = 1589039) B1589039
theorem B3615419 : Blo 1056613 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B1059675 : Blo 1056613 1059675 := bstep (se 1 (by rfl) ⟨794756, by rfl⟩ : syracuseStep 1059675 = 1589513) B1589513
theorem B1059743 : Blo 1056613 1059743 := bstep (se 1 (by rfl) ⟨794807, by rfl⟩ : syracuseStep 1059743 = 1589615) B1589615
theorem B1059887 : Blo 1056613 1059887 := bstep (se 1 (by rfl) ⟨794915, by rfl⟩ : syracuseStep 1059887 = 1589831) B1589831
theorem B1190983 : Blo 1056613 1190983 := bstep (se 1 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 1190983 = 1786475) B1786475
theorem B1059911 : Blo 1056613 1059911 := bstep (se 1 (by rfl) ⟨794933, by rfl⟩ : syracuseStep 1059911 = 1589867) B1589867
theorem B2010233 : Blo 1056613 2010233 := bstep (se 2 (by rfl) ⟨753837, by rfl⟩ : syracuseStep 2010233 = 1507675) B1507675
theorem B15281287 : Blo 1056613 15281287 := bstep (se 1 (by rfl) ⟨11460965, by rfl⟩ : syracuseStep 15281287 = 22921931) B22921931
theorem B1060063 : Blo 1056613 1060063 := bstep (se 1 (by rfl) ⟨795047, by rfl⟩ : syracuseStep 1060063 = 1590095) B1590095
theorem B1060327 : Blo 1056613 1060327 := bstep (se 1 (by rfl) ⟨795245, by rfl⟩ : syracuseStep 1060327 = 1590491) B1590491
theorem B1060443 : Blo 1056613 1060443 := bstep (se 1 (by rfl) ⟨795332, by rfl⟩ : syracuseStep 1060443 = 1590665) B1590665
theorem B1584935 : Blo 1056613 1584935 := bstep (se 1 (by rfl) ⟨1188701, by rfl⟩ : syracuseStep 1584935 = 2377403) B2377403
theorem B1585019 : Blo 1056613 1585019 := bstep (se 1 (by rfl) ⟨1188764, by rfl⟩ : syracuseStep 1585019 = 2377529) B2377529
theorem B3813263 : Blo 1056613 3813263 := bstep (se 1 (by rfl) ⟨2859947, by rfl⟩ : syracuseStep 3813263 = 5719895) B5719895
theorem B1224671 : Blo 1056613 1224671 := bstep (se 1 (by rfl) ⟨918503, by rfl⟩ : syracuseStep 1224671 = 1837007) B1837007
theorem B6795251 : Blo 1056613 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1585439 : Blo 1056613 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B1585463 : Blo 1056613 1585463 := bstep (se 1 (by rfl) ⟨1189097, by rfl⟩ : syracuseStep 1585463 = 2378195) B2378195
theorem B1585535 : Blo 1056613 1585535 := bstep (se 1 (by rfl) ⟨1189151, by rfl⟩ : syracuseStep 1585535 = 2378303) B2378303
theorem B15249815 : Blo 1056613 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B1585607 : Blo 1056613 1585607 := bstep (se 1 (by rfl) ⟨1189205, by rfl⟩ : syracuseStep 1585607 = 2378411) B2378411
theorem B1585961 : Blo 1056613 1585961 := bstep (se 2 (by rfl) ⟨594735, by rfl⟩ : syracuseStep 1585961 = 1189471) B1189471
theorem B1585967 : Blo 1056613 1585967 := bstep (se 1 (by rfl) ⟨1189475, by rfl⟩ : syracuseStep 1585967 = 2378951) B2378951
theorem B20362063 : Blo 1056613 20362063 := bstep (se 1 (by rfl) ⟨15271547, by rfl⟩ : syracuseStep 20362063 = 30543095) B30543095
theorem B1586087 : Blo 1056613 1586087 := bstep (se 1 (by rfl) ⟨1189565, by rfl⟩ : syracuseStep 1586087 = 2379131) B2379131
theorem B1586171 : Blo 1056613 1586171 := bstep (se 1 (by rfl) ⟨1189628, by rfl⟩ : syracuseStep 1586171 = 2379257) B2379257
theorem B1586231 : Blo 1056613 1586231 := bstep (se 1 (by rfl) ⟨1189673, by rfl⟩ : syracuseStep 1586231 = 2379347) B2379347
theorem B2012215 : Blo 1056613 2012215 := bstep (se 1 (by rfl) ⟨1509161, by rfl⟩ : syracuseStep 2012215 = 3018323) B3018323
theorem B1586351 : Blo 1056613 1586351 := bstep (se 1 (by rfl) ⟨1189763, by rfl⟩ : syracuseStep 1586351 = 2379527) B2379527
theorem B2012435 : Blo 1056613 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B5092669 : Blo 1056613 5092669 := bstep (se 3 (by rfl) ⟨954875, by rfl⟩ : syracuseStep 5092669 = 1909751) B1909751
theorem B18068993 : Blo 1056613 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B1586759 : Blo 1056613 1586759 := bstep (se 1 (by rfl) ⟨1190069, by rfl⟩ : syracuseStep 1586759 = 2380139) B2380139
theorem B1783417 : Blo 1056613 1783417 := bstep (se 2 (by rfl) ⟨668781, by rfl⟩ : syracuseStep 1783417 = 1337563) B1337563
theorem B1586855 : Blo 1056613 1586855 := bstep (se 1 (by rfl) ⟨1190141, by rfl⟩ : syracuseStep 1586855 = 2380283) B2380283
theorem B3618539 : Blo 1056613 3618539 := bstep (se 1 (by rfl) ⟨2713904, by rfl⟩ : syracuseStep 3618539 = 5427809) B5427809
theorem B1586939 : Blo 1056613 1586939 := bstep (se 1 (by rfl) ⟨1190204, by rfl⟩ : syracuseStep 1586939 = 2380409) B2380409
theorem B1586975 : Blo 1056613 1586975 := bstep (se 1 (by rfl) ⟨1190231, by rfl⟩ : syracuseStep 1586975 = 2380463) B2380463
theorem B4011839 : Blo 1056613 4011839 := bstep (se 1 (by rfl) ⟨3008879, by rfl⟩ : syracuseStep 4011839 = 6017759) B6017759
theorem B1587023 : Blo 1056613 1587023 := bstep (se 1 (by rfl) ⟨1190267, by rfl⟩ : syracuseStep 1587023 = 2380535) B2380535
theorem B1587143 : Blo 1056613 1587143 := bstep (se 1 (by rfl) ⟨1190357, by rfl⟩ : syracuseStep 1587143 = 2380715) B2380715
theorem B1783903 : Blo 1056613 1783903 := bstep (se 1 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 1783903 = 2675855) B2675855
theorem B9156901 : Blo 1056613 9156901 := bstep (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) B1716919
theorem B1587497 : Blo 1056613 1587497 := bstep (se 2 (by rfl) ⟨595311, by rfl⟩ : syracuseStep 1587497 = 1190623) B1190623
theorem B1587503 : Blo 1056613 1587503 := bstep (se 1 (by rfl) ⟨1190627, by rfl⟩ : syracuseStep 1587503 = 2381255) B2381255
theorem B15088045 : Blo 1056613 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B1587743 : Blo 1056613 1587743 := bstep (se 1 (by rfl) ⟨1190807, by rfl⟩ : syracuseStep 1587743 = 2381615) B2381615
theorem B5356367 : Blo 1056613 5356367 := bstep (se 1 (by rfl) ⟨4017275, by rfl⟩ : syracuseStep 5356367 = 8034551) B8034551
theorem B1588127 : Blo 1056613 1588127 := bstep (se 1 (by rfl) ⟨1191095, by rfl⟩ : syracuseStep 1588127 = 2382191) B2382191
theorem B1588175 : Blo 1056613 1588175 := bstep (se 1 (by rfl) ⟨1191131, by rfl⟩ : syracuseStep 1588175 = 2382263) B2382263
theorem B1588265 : Blo 1056613 1588265 := bstep (se 2 (by rfl) ⟨595599, by rfl⟩ : syracuseStep 1588265 = 1191199) B1191199
theorem B1588271 : Blo 1056613 1588271 := bstep (se 1 (by rfl) ⟨1191203, by rfl⟩ : syracuseStep 1588271 = 2382407) B2382407
theorem B1588295 : Blo 1056613 1588295 := bstep (se 1 (by rfl) ⟨1191221, by rfl⟩ : syracuseStep 1588295 = 2382443) B2382443
theorem B8043785 : Blo 1056613 8043785 := bstep (se 2 (by rfl) ⟨3016419, by rfl⟩ : syracuseStep 8043785 = 6032839) B6032839
theorem B1588559 : Blo 1056613 1588559 := bstep (se 1 (by rfl) ⟨1191419, by rfl⟩ : syracuseStep 1588559 = 2382839) B2382839
theorem B1785199 : Blo 1056613 1785199 := bstep (se 1 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 1785199 = 2677799) B2677799
theorem B1588649 : Blo 1056613 1588649 := bstep (se 2 (by rfl) ⟨595743, by rfl⟩ : syracuseStep 1588649 = 1191487) B1191487
theorem B1588799 : Blo 1056613 1588799 := bstep (se 1 (by rfl) ⟨1191599, by rfl⟩ : syracuseStep 1588799 = 2383199) B2383199
theorem B1785577 : Blo 1056613 1785577 := bstep (se 2 (by rfl) ⟨669591, by rfl⟩ : syracuseStep 1785577 = 1339183) B1339183
theorem B1589063 : Blo 1056613 1589063 := bstep (se 1 (by rfl) ⟨1191797, by rfl⟩ : syracuseStep 1589063 = 2383595) B2383595
theorem B1589147 : Blo 1056613 1589147 := bstep (se 1 (by rfl) ⟨1191860, by rfl⟩ : syracuseStep 1589147 = 2383721) B2383721
theorem B4013995 : Blo 1056613 4013995 := bstep (se 1 (by rfl) ⟨3010496, by rfl⟩ : syracuseStep 4013995 = 6020993) B6020993
theorem B7618475 : Blo 1056613 7618475 := bstep (se 1 (by rfl) ⟨5713856, by rfl⟩ : syracuseStep 7618475 = 11427713) B11427713
theorem B25116587 : Blo 1056613 25116587 := bstep (se 1 (by rfl) ⟨18837440, by rfl⟩ : syracuseStep 25116587 = 37674881) B37674881
theorem B15253505 : Blo 1056613 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B3391627 : Blo 1056613 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B1786043 : Blo 1056613 1786043 := bstep (se 1 (by rfl) ⟨1339532, by rfl⟩ : syracuseStep 1786043 = 2679065) B2679065
theorem B1589711 : Blo 1056613 1589711 := bstep (se 1 (by rfl) ⟨1192283, by rfl⟩ : syracuseStep 1589711 = 2384567) B2384567
theorem B1589753 : Blo 1056613 1589753 := bstep (se 2 (by rfl) ⟨596157, by rfl⟩ : syracuseStep 1589753 = 1192315) B1192315
theorem B1589855 : Blo 1056613 1589855 := bstep (se 1 (by rfl) ⟨1192391, by rfl⟩ : syracuseStep 1589855 = 2384783) B2384783
theorem B185483981 : Blo 1056613 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B1786603 : Blo 1056613 1786603 := bstep (se 1 (by rfl) ⟨1339952, by rfl⟩ : syracuseStep 1786603 = 2679905) B2679905
theorem B1590335 : Blo 1056613 1590335 := bstep (se 1 (by rfl) ⟨1192751, by rfl⟩ : syracuseStep 1590335 = 2385503) B2385503
theorem B1590377 : Blo 1056613 1590377 := bstep (se 2 (by rfl) ⟨596391, by rfl⟩ : syracuseStep 1590377 = 1192783) B1192783
theorem B1590479 : Blo 1056613 1590479 := bstep (se 1 (by rfl) ⟨1192859, by rfl⟩ : syracuseStep 1590479 = 2385719) B2385719
theorem B1590683 : Blo 1056613 1590683 := bstep (se 1 (by rfl) ⟨1193012, by rfl⟩ : syracuseStep 1590683 = 2386025) B2386025
theorem B3818927 : Blo 1056613 3818927 := bstep (se 1 (by rfl) ⟨2864195, by rfl⟩ : syracuseStep 3818927 = 5728391) B5728391
theorem B10864151 : Blo 1056613 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B4015727 : Blo 1056613 4015727 := bstep (se 1 (by rfl) ⟨3011795, by rfl⟩ : syracuseStep 4015727 = 6023591) B6023591
theorem B1590905 : Blo 1056613 1590905 := bstep (se 2 (by rfl) ⟨596589, by rfl⟩ : syracuseStep 1590905 = 1193179) B1193179
theorem B3393191 : Blo 1056613 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B1787575 : Blo 1056613 1787575 := bstep (se 1 (by rfl) ⟨1340681, by rfl⟩ : syracuseStep 1787575 = 2681363) B2681363
theorem B2377439 : Blo 1056613 2377439 := bstep (se 1 (by rfl) ⟨1783079, by rfl⟩ : syracuseStep 2377439 = 3566159) B3566159
theorem B3393359 : Blo 1056613 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B17188795 : Blo 1056613 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B7620551 : Blo 1056613 7620551 := bstep (se 1 (by rfl) ⟨5715413, by rfl⟩ : syracuseStep 7620551 = 11430827) B11430827
theorem B14501861 : Blo 1056613 14501861 := bstep (se 4 (by rfl) ⟨1359549, by rfl⟩ : syracuseStep 14501861 = 2719099) B2719099
theorem B1787879 : Blo 1056613 1787879 := bstep (se 1 (by rfl) ⟨1340909, by rfl⟩ : syracuseStep 1787879 = 2681819) B2681819
theorem B1788095 : Blo 1056613 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B12044537 : Blo 1056613 12044537 := bstep (se 2 (by rfl) ⟨4516701, by rfl⟩ : syracuseStep 12044537 = 9033403) B9033403
theorem B2148665 : Blo 1056613 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B2378267 : Blo 1056613 2378267 := bstep (se 1 (by rfl) ⟨1783700, by rfl⟩ : syracuseStep 2378267 = 3567401) B3567401
theorem B1788763 : Blo 1056613 1788763 := bstep (se 1 (by rfl) ⟨1341572, by rfl⟩ : syracuseStep 1788763 = 2683145) B2683145
theorem B4017185 : Blo 1056613 4017185 := bstep (se 2 (by rfl) ⟨1506444, by rfl⟩ : syracuseStep 4017185 = 3012889) B3012889
theorem B3394703 : Blo 1056613 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B5361065 : Blo 1056613 5361065 := bstep (se 2 (by rfl) ⟨2010399, by rfl⟩ : syracuseStep 5361065 = 4020799) B4020799
theorem B14470645 : Blo 1056613 14470645 := bstep (se 5 (by rfl) ⟨678311, by rfl⟩ : syracuseStep 14470645 = 1356623) B1356623
theorem B1789735 : Blo 1056613 1789735 := bstep (se 1 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 1789735 = 2684603) B2684603
theorem B5361551 : Blo 1056613 5361551 := bstep (se 1 (by rfl) ⟨4021163, by rfl⟩ : syracuseStep 5361551 = 8042327) B8042327
theorem B2379743 : Blo 1056613 2379743 := bstep (se 1 (by rfl) ⟨1784807, by rfl⟩ : syracuseStep 2379743 = 3569615) B3569615
theorem B4018157 : Blo 1056613 4018157 := bstep (se 3 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 4018157 = 1506809) B1506809
theorem B36720701 : Blo 1056613 36720701 := bstep (se 3 (by rfl) ⟨6885131, by rfl⟩ : syracuseStep 36720701 = 13770263) B13770263
theorem B2380391 : Blo 1056613 2380391 := bstep (se 1 (by rfl) ⟨1785293, by rfl⟩ : syracuseStep 2380391 = 3570587) B3570587
theorem B1430119 : Blo 1056613 1430119 := bstep (se 1 (by rfl) ⟨1072589, by rfl⟩ : syracuseStep 1430119 = 2145179) B2145179
theorem B41308775 : Blo 1056613 41308775 := bstep (se 1 (by rfl) ⟨30981581, by rfl⟩ : syracuseStep 41308775 = 61963163) B61963163
theorem B3396343 : Blo 1056613 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B1430281 : Blo 1056613 1430281 := bstep (se 2 (by rfl) ⟨536355, by rfl⟩ : syracuseStep 1430281 = 1072711) B1072711
theorem B2544635 : Blo 1056613 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B15258631 : Blo 1056613 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B6018259 : Blo 1056613 6018259 := bstep (se 1 (by rfl) ⟨4513694, by rfl⟩ : syracuseStep 6018259 = 9027389) B9027389
theorem B2675987 : Blo 1056613 2675987 := bstep (se 1 (by rfl) ⟨2006990, by rfl⟩ : syracuseStep 2675987 = 4013981) B4013981
theorem B2381075 : Blo 1056613 2381075 := bstep (se 1 (by rfl) ⟨1785806, by rfl⟩ : syracuseStep 2381075 = 3571613) B3571613
theorem B5428511 : Blo 1056613 5428511 := bstep (se 1 (by rfl) ⟨4071383, by rfl⟩ : syracuseStep 5428511 = 8142767) B8142767
theorem B2381147 : Blo 1056613 2381147 := bstep (se 1 (by rfl) ⟨1785860, by rfl⟩ : syracuseStep 2381147 = 3571721) B3571721
theorem B9164411 : Blo 1056613 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B2381705 : Blo 1056613 2381705 := bstep (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) B1786279
theorem B2545759 : Blo 1056613 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B3397727 : Blo 1056613 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B2381921 : Blo 1056613 2381921 := bstep (se 2 (by rfl) ⟨893220, by rfl⟩ : syracuseStep 2381921 = 1786441) B1786441
theorem B8149355 : Blo 1056613 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B4020587 : Blo 1056613 4020587 := bstep (se 1 (by rfl) ⟨3015440, by rfl⟩ : syracuseStep 4020587 = 6030881) B6030881
theorem B5364143 : Blo 1056613 5364143 := bstep (se 1 (by rfl) ⟨4023107, by rfl⟩ : syracuseStep 5364143 = 8046215) B8046215
theorem B83745323 : Blo 1056613 83745323 := bstep (se 1 (by rfl) ⟨62808992, by rfl⟩ : syracuseStep 83745323 = 125617985) B125617985
theorem B9034361 : Blo 1056613 9034361 := bstep (se 2 (by rfl) ⟨3387885, by rfl⟩ : syracuseStep 9034361 = 6775771) B6775771
theorem B4021073 : Blo 1056613 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B8051561 : Blo 1056613 8051561 := bstep (se 2 (by rfl) ⟨3019335, by rfl⟩ : syracuseStep 8051561 = 6038671) B6038671
theorem B6020243 : Blo 1056613 6020243 := bstep (se 1 (by rfl) ⟨4515182, by rfl⟩ : syracuseStep 6020243 = 9030365) B9030365
theorem B2383271 : Blo 1056613 2383271 := bstep (se 1 (by rfl) ⟨1787453, by rfl⟩ : syracuseStep 2383271 = 3574907) B3574907
theorem B2383451 : Blo 1056613 2383451 := bstep (se 1 (by rfl) ⟨1787588, by rfl⟩ : syracuseStep 2383451 = 3575177) B3575177
theorem B2383739 : Blo 1056613 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B5431583 : Blo 1056613 5431583 := bstep (se 1 (by rfl) ⟨4073687, by rfl⟩ : syracuseStep 5431583 = 8147375) B8147375
theorem B6021449 : Blo 1056613 6021449 := bstep (se 2 (by rfl) ⟨2258043, by rfl⟩ : syracuseStep 6021449 = 4516087) B4516087
theorem B2384225 : Blo 1056613 2384225 := bstep (se 2 (by rfl) ⟨894084, by rfl⟩ : syracuseStep 2384225 = 1788169) B1788169
theorem B2679227 : Blo 1056613 2679227 := bstep (se 1 (by rfl) ⟨2009420, by rfl⟩ : syracuseStep 2679227 = 4018841) B4018841
theorem B2384315 : Blo 1056613 2384315 := bstep (se 1 (by rfl) ⟨1788236, by rfl⟩ : syracuseStep 2384315 = 3576473) B3576473
theorem B5366249 : Blo 1056613 5366249 := bstep (se 2 (by rfl) ⟨2012343, by rfl⟩ : syracuseStep 5366249 = 4024687) B4024687
theorem B4514413 : Blo 1056613 4514413 := bstep (se 3 (by rfl) ⟨846452, by rfl⟩ : syracuseStep 4514413 = 1692905) B1692905
theorem B5366411 : Blo 1056613 5366411 := bstep (se 1 (by rfl) ⟨4024808, by rfl⟩ : syracuseStep 5366411 = 8049617) B8049617
theorem B2679763 : Blo 1056613 2679763 := bstep (se 1 (by rfl) ⟨2009822, by rfl⟩ : syracuseStep 2679763 = 4019645) B4019645
theorem B1696763 : Blo 1056613 1696763 := bstep (se 1 (by rfl) ⟨1272572, by rfl⟩ : syracuseStep 1696763 = 2545145) B2545145
theorem B4023503 : Blo 1056613 4023503 := bstep (se 1 (by rfl) ⟨3017627, by rfl⟩ : syracuseStep 4023503 = 6035255) B6035255
theorem B2385323 : Blo 1056613 2385323 := bstep (se 1 (by rfl) ⟨1788992, by rfl⟩ : syracuseStep 2385323 = 3577985) B3577985
theorem B2385575 : Blo 1056613 2385575 := bstep (se 1 (by rfl) ⟨1789181, by rfl⟩ : syracuseStep 2385575 = 3578363) B3578363
theorem B2385863 : Blo 1056613 2385863 := bstep (se 1 (by rfl) ⟨1789397, by rfl⟩ : syracuseStep 2385863 = 3578795) B3578795
theorem B6023159 : Blo 1056613 6023159 := bstep (se 1 (by rfl) ⟨4517369, by rfl⟩ : syracuseStep 6023159 = 9034739) B9034739
theorem B4352147 : Blo 1056613 4352147 := bstep (se 1 (by rfl) ⟨3264110, by rfl⟩ : syracuseStep 4352147 = 6528221) B6528221
theorem B2386169 : Blo 1056613 2386169 := bstep (se 2 (by rfl) ⟨894813, by rfl⟩ : syracuseStep 2386169 = 1789627) B1789627
theorem B2287919 : Blo 1056613 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B2386223 : Blo 1056613 2386223 := bstep (se 1 (by rfl) ⟨1789667, by rfl⟩ : syracuseStep 2386223 = 3579335) B3579335
theorem B34794011 : Blo 1056613 34794011 := bstep (se 1 (by rfl) ⟨26095508, by rfl⟩ : syracuseStep 34794011 = 52191017) B52191017
theorem B1337887 : Blo 1056613 1337887 := bstep (se 1 (by rfl) ⟨1003415, by rfl⟩ : syracuseStep 1337887 = 2006831) B2006831
theorem B3566267 : Blo 1056613 3566267 := bstep (se 1 (by rfl) ⟨2674700, by rfl⟩ : syracuseStep 3566267 = 5349401) B5349401
theorem B6449867 : Blo 1056613 6449867 := bstep (se 1 (by rfl) ⟨4837400, by rfl⟩ : syracuseStep 6449867 = 9674801) B9674801
theorem B6777719 : Blo 1056613 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B9038735 : Blo 1056613 9038735 := bstep (se 1 (by rfl) ⟨6779051, by rfl⟩ : syracuseStep 9038735 = 13558103) B13558103
theorem B1338439 : Blo 1056613 1338439 := bstep (se 1 (by rfl) ⟨1003829, by rfl⟩ : syracuseStep 1338439 = 2007659) B2007659
theorem B146795813 : Blo 1056613 146795813 := bstep (se 4 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 146795813 = 27524215) B27524215
theorem B3141227 : Blo 1056613 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B3010223 : Blo 1056613 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B4026131 : Blo 1056613 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B1273639 : Blo 1056613 1273639 := bstep (se 1 (by rfl) ⟨955229, by rfl⟩ : syracuseStep 1273639 = 1910459) B1910459
theorem B2683003 : Blo 1056613 2683003 := bstep (se 1 (by rfl) ⟨2012252, by rfl⟩ : syracuseStep 2683003 = 4024505) B4024505
theorem B3568211 : Blo 1056613 3568211 := bstep (se 1 (by rfl) ⟨2676158, by rfl⟩ : syracuseStep 3568211 = 5352317) B5352317
theorem B1340327 : Blo 1056613 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B1340479 : Blo 1056613 1340479 := bstep (se 1 (by rfl) ⟨1005359, by rfl⟩ : syracuseStep 1340479 = 2010719) B2010719
theorem B2258027 : Blo 1056613 2258027 := bstep (se 1 (by rfl) ⟨1693520, by rfl⟩ : syracuseStep 2258027 = 3387041) B3387041
theorem B3568859 : Blo 1056613 3568859 := bstep (se 1 (by rfl) ⟨2676644, by rfl⟩ : syracuseStep 3568859 = 5353289) B5353289
theorem B6780179 : Blo 1056613 6780179 := bstep (se 1 (by rfl) ⟨5085134, by rfl⟩ : syracuseStep 6780179 = 10170269) B10170269
theorem B19559981 : Blo 1056613 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B8025803 : Blo 1056613 8025803 := bstep (se 1 (by rfl) ⟨6019352, by rfl⟩ : syracuseStep 8025803 = 12038705) B12038705
theorem B10319633 : Blo 1056613 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B3438617 : Blo 1056613 3438617 := bstep (se 2 (by rfl) ⟨1289481, by rfl⟩ : syracuseStep 3438617 = 2578963) B2578963
theorem B3569723 : Blo 1056613 3569723 := bstep (se 1 (by rfl) ⟨2677292, by rfl⟩ : syracuseStep 3569723 = 5354585) B5354585
theorem B25720915 : Blo 1056613 25720915 := bstep (se 1 (by rfl) ⟨19290686, by rfl⟩ : syracuseStep 25720915 = 38581373) B38581373
theorem B3569993 : Blo 1056613 3569993 := bstep (se 2 (by rfl) ⟨1338747, by rfl⟩ : syracuseStep 3569993 = 2677495) B2677495
theorem B3013139 : Blo 1056613 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B6027965 : Blo 1056613 6027965 := bstep (se 3 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 6027965 = 2260487) B2260487
theorem B10157507 : Blo 1056613 10157507 := bstep (se 1 (by rfl) ⟨7618130, by rfl⟩ : syracuseStep 10157507 = 15236261) B15236261
theorem B6028739 : Blo 1056613 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B3571343 : Blo 1056613 3571343 := bstep (se 1 (by rfl) ⟨2678507, by rfl⟩ : syracuseStep 3571343 = 5357015) B5357015
theorem B20643617 : Blo 1056613 20643617 := bstep (se 2 (by rfl) ⟨7741356, by rfl⟩ : syracuseStep 20643617 = 15482713) B15482713
theorem B4522169 : Blo 1056613 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B14484221 : Blo 1056613 14484221 := bstep (se 3 (by rfl) ⟨2715791, by rfl⟩ : syracuseStep 14484221 = 5431583) B5431583
theorem B8586071 : Blo 1056613 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B3015623 : Blo 1056613 3015623 := bstep (se 1 (by rfl) ⟨2261717, by rfl⟩ : syracuseStep 3015623 = 4523435) B4523435
theorem B7242767 : Blo 1056613 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B2262239 : Blo 1056613 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B3573017 : Blo 1056613 3573017 := bstep (se 2 (by rfl) ⟨1339881, by rfl⟩ : syracuseStep 3573017 = 2679763) B2679763
theorem B5080367 : Blo 1056613 5080367 := bstep (se 1 (by rfl) ⟨3810275, by rfl⟩ : syracuseStep 5080367 = 7620551) B7620551
theorem B9667907 : Blo 1056613 9667907 := bstep (se 1 (by rfl) ⟨7250930, by rfl⟩ : syracuseStep 9667907 = 14501861) B14501861
theorem B8029691 : Blo 1056613 8029691 := bstep (se 1 (by rfl) ⟨6022268, by rfl⟩ : syracuseStep 8029691 = 12044537) B12044537
theorem B2263135 : Blo 1056613 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B3016865 : Blo 1056613 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B3574043 : Blo 1056613 3574043 := bstep (se 1 (by rfl) ⟨2680532, by rfl⟩ : syracuseStep 3574043 = 5361065) B5361065
theorem B3574205 : Blo 1056613 3574205 := bstep (se 3 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 3574205 = 1340327) B1340327
theorem B3574367 : Blo 1056613 3574367 := bstep (se 1 (by rfl) ⟨2680775, by rfl⟩ : syracuseStep 3574367 = 5361551) B5361551
theorem B6785693 : Blo 1056613 6785693 := bstep (se 3 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 6785693 = 2544635) B2544635
theorem B24480467 : Blo 1056613 24480467 := bstep (se 1 (by rfl) ⟨18360350, by rfl⟩ : syracuseStep 24480467 = 36720701) B36720701
theorem B1904735 : Blo 1056613 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B3576095 : Blo 1056613 3576095 := bstep (se 1 (by rfl) ⟨2682071, by rfl⟩ : syracuseStep 3576095 = 5364143) B5364143
theorem B9048509 : Blo 1056613 9048509 := bstep (se 3 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 9048509 = 3393191) B3393191
theorem B9179929 : Blo 1056613 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B20386667 : Blo 1056613 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B6034571 : Blo 1056613 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B4527535 : Blo 1056613 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B3577337 : Blo 1056613 3577337 := bstep (se 2 (by rfl) ⟨1341501, by rfl⟩ : syracuseStep 3577337 = 2683003) B2683003
theorem B3577499 : Blo 1056613 3577499 := bstep (se 1 (by rfl) ⟨2683124, by rfl⟩ : syracuseStep 3577499 = 5366249) B5366249
theorem B3577607 : Blo 1056613 3577607 := bstep (se 1 (by rfl) ⟨2683205, by rfl⟩ : syracuseStep 3577607 = 5366411) B5366411
theorem B81500197 : Blo 1056613 81500197 := bstep (se 4 (by rfl) ⟨7640643, by rfl⟩ : syracuseStep 81500197 = 15281287) B15281287
theorem B1906825 : Blo 1056613 1906825 := bstep (se 2 (by rfl) ⟨715059, by rfl⟩ : syracuseStep 1906825 = 1430119) B1430119
theorem B4528457 : Blo 1056613 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B8035037 : Blo 1056613 8035037 := bstep (se 3 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 8035037 = 3013139) B3013139
theorem B6036281 : Blo 1056613 6036281 := bstep (se 2 (by rfl) ⟨2263605, by rfl⟩ : syracuseStep 6036281 = 4527211) B4527211
theorem B68688749 : Blo 1056613 68688749 := bstep (se 3 (by rfl) ⟨12879140, by rfl⟩ : syracuseStep 68688749 = 25758281) B25758281
theorem B14490575 : Blo 1056613 14490575 := bstep (se 1 (by rfl) ⟨10867931, by rfl⟩ : syracuseStep 14490575 = 21735863) B21735863
theorem B6790225 : Blo 1056613 6790225 := bstep (se 2 (by rfl) ⟨2546334, by rfl⟩ : syracuseStep 6790225 = 5092669) B5092669
theorem B4299911 : Blo 1056613 4299911 := bstep (se 1 (by rfl) ⟨3224933, by rfl⟩ : syracuseStep 4299911 = 6449867) B6449867
theorem B1056623 : Blo 1056613 1056623 := bstep (se 1 (by rfl) ⟨792467, by rfl⟩ : syracuseStep 1056623 = 1584935) B1584935
theorem B1056679 : Blo 1056613 1056679 := bstep (se 1 (by rfl) ⟨792509, by rfl⟩ : syracuseStep 1056679 = 1585019) B1585019
theorem B4530167 : Blo 1056613 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B1056959 : Blo 1056613 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B1056975 : Blo 1056613 1056975 := bstep (se 1 (by rfl) ⟨792731, by rfl⟩ : syracuseStep 1056975 = 1585463) B1585463
theorem B1057023 : Blo 1056613 1057023 := bstep (se 1 (by rfl) ⟨792767, by rfl⟩ : syracuseStep 1057023 = 1585535) B1585535
theorem B10166543 : Blo 1056613 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B1057071 : Blo 1056613 1057071 := bstep (se 1 (by rfl) ⟨792803, by rfl⟩ : syracuseStep 1057071 = 1585607) B1585607
theorem B1057307 : Blo 1056613 1057307 := bstep (se 1 (by rfl) ⟨792980, by rfl⟩ : syracuseStep 1057307 = 1585961) B1585961
theorem B1057311 : Blo 1056613 1057311 := bstep (se 1 (by rfl) ⟨792983, by rfl⟩ : syracuseStep 1057311 = 1585967) B1585967
theorem B1057391 : Blo 1056613 1057391 := bstep (se 1 (by rfl) ⟨793043, by rfl⟩ : syracuseStep 1057391 = 1586087) B1586087
theorem B1057447 : Blo 1056613 1057447 := bstep (se 1 (by rfl) ⟨793085, by rfl⟩ : syracuseStep 1057447 = 1586171) B1586171
theorem B1057487 : Blo 1056613 1057487 := bstep (se 1 (by rfl) ⟨793115, by rfl⟩ : syracuseStep 1057487 = 1586231) B1586231
theorem B1057567 : Blo 1056613 1057567 := bstep (se 1 (by rfl) ⟨793175, by rfl⟩ : syracuseStep 1057567 = 1586351) B1586351
theorem B1057839 : Blo 1056613 1057839 := bstep (se 1 (by rfl) ⟨793379, by rfl⟩ : syracuseStep 1057839 = 1586759) B1586759
theorem B5088365 : Blo 1056613 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B1057903 : Blo 1056613 1057903 := bstep (se 1 (by rfl) ⟨793427, by rfl⟩ : syracuseStep 1057903 = 1586855) B1586855
theorem B5350535 : Blo 1056613 5350535 := bstep (se 1 (by rfl) ⟨4012901, by rfl⟩ : syracuseStep 5350535 = 8025803) B8025803
theorem B1057959 : Blo 1056613 1057959 := bstep (se 1 (by rfl) ⟨793469, by rfl⟩ : syracuseStep 1057959 = 1586939) B1586939
theorem B1057983 : Blo 1056613 1057983 := bstep (se 1 (by rfl) ⟨793487, by rfl⟩ : syracuseStep 1057983 = 1586975) B1586975
theorem B1058015 : Blo 1056613 1058015 := bstep (se 1 (by rfl) ⟨793511, by rfl⟩ : syracuseStep 1058015 = 1587023) B1587023
theorem B1058095 : Blo 1056613 1058095 := bstep (se 1 (by rfl) ⟨793571, by rfl⟩ : syracuseStep 1058095 = 1587143) B1587143
theorem B6038945 : Blo 1056613 6038945 := bstep (se 2 (by rfl) ⟨2264604, by rfl⟩ : syracuseStep 6038945 = 4529209) B4529209
theorem B1058331 : Blo 1056613 1058331 := bstep (se 1 (by rfl) ⟨793748, by rfl⟩ : syracuseStep 1058331 = 1587497) B1587497
theorem B1058335 : Blo 1056613 1058335 := bstep (se 1 (by rfl) ⟨793751, by rfl⟩ : syracuseStep 1058335 = 1587503) B1587503
theorem B1058495 : Blo 1056613 1058495 := bstep (se 1 (by rfl) ⟨793871, by rfl⟩ : syracuseStep 1058495 = 1587743) B1587743
theorem B4073257 : Blo 1056613 4073257 := bstep (se 2 (by rfl) ⟨1527471, by rfl⟩ : syracuseStep 4073257 = 3054943) B3054943
theorem B1058751 : Blo 1056613 1058751 := bstep (se 1 (by rfl) ⟨794063, by rfl⟩ : syracuseStep 1058751 = 1588127) B1588127
theorem B1058783 : Blo 1056613 1058783 := bstep (se 1 (by rfl) ⟨794087, by rfl⟩ : syracuseStep 1058783 = 1588175) B1588175
theorem B1058843 : Blo 1056613 1058843 := bstep (se 1 (by rfl) ⟨794132, by rfl⟩ : syracuseStep 1058843 = 1588265) B1588265
theorem B1058847 : Blo 1056613 1058847 := bstep (se 1 (by rfl) ⟨794135, by rfl⟩ : syracuseStep 1058847 = 1588271) B1588271
theorem B1058863 : Blo 1056613 1058863 := bstep (se 1 (by rfl) ⟨794147, by rfl⟩ : syracuseStep 1058863 = 1588295) B1588295
theorem B1059039 : Blo 1056613 1059039 := bstep (se 1 (by rfl) ⟨794279, by rfl⟩ : syracuseStep 1059039 = 1588559) B1588559
theorem B1059099 : Blo 1056613 1059099 := bstep (se 1 (by rfl) ⟨794324, by rfl⟩ : syracuseStep 1059099 = 1588649) B1588649
theorem B1059199 : Blo 1056613 1059199 := bstep (se 1 (by rfl) ⟨794399, by rfl⟩ : syracuseStep 1059199 = 1588799) B1588799
theorem B1059375 : Blo 1056613 1059375 := bstep (se 1 (by rfl) ⟨794531, by rfl⟩ : syracuseStep 1059375 = 1589063) B1589063
theorem B5351993 : Blo 1056613 5351993 := bstep (se 2 (by rfl) ⟨2006997, by rfl⟩ : syracuseStep 5351993 = 4013995) B4013995
theorem B1059431 : Blo 1056613 1059431 := bstep (se 1 (by rfl) ⟨794573, by rfl⟩ : syracuseStep 1059431 = 1589147) B1589147
theorem B10169003 : Blo 1056613 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B27175661 : Blo 1056613 27175661 := bstep (se 3 (by rfl) ⟨5095436, by rfl⟩ : syracuseStep 27175661 = 10190873) B10190873
theorem B1190695 : Blo 1056613 1190695 := bstep (se 1 (by rfl) ⟨893021, by rfl⟩ : syracuseStep 1190695 = 1786043) B1786043
theorem B36678581 : Blo 1056613 36678581 := bstep (se 5 (by rfl) ⟨1719308, by rfl⟩ : syracuseStep 36678581 = 3438617) B3438617
theorem B1059807 : Blo 1056613 1059807 := bstep (se 1 (by rfl) ⟨794855, by rfl⟩ : syracuseStep 1059807 = 1589711) B1589711
theorem B1059835 : Blo 1056613 1059835 := bstep (se 1 (by rfl) ⟨794876, by rfl⟩ : syracuseStep 1059835 = 1589753) B1589753
theorem B9055273 : Blo 1056613 9055273 := bstep (se 2 (by rfl) ⟨3395727, by rfl⟩ : syracuseStep 9055273 = 6791455) B6791455
theorem B1059903 : Blo 1056613 1059903 := bstep (se 1 (by rfl) ⟨794927, by rfl⟩ : syracuseStep 1059903 = 1589855) B1589855
theorem B1060223 : Blo 1056613 1060223 := bstep (se 1 (by rfl) ⟨795167, by rfl⟩ : syracuseStep 1060223 = 1590335) B1590335
theorem B1060251 : Blo 1056613 1060251 := bstep (se 1 (by rfl) ⟨795188, by rfl⟩ : syracuseStep 1060251 = 1590377) B1590377
theorem B1060319 : Blo 1056613 1060319 := bstep (se 1 (by rfl) ⟨795239, by rfl⟩ : syracuseStep 1060319 = 1590479) B1590479
theorem B1060455 : Blo 1056613 1060455 := bstep (se 1 (by rfl) ⟨795341, by rfl⟩ : syracuseStep 1060455 = 1590683) B1590683
theorem B1060603 : Blo 1056613 1060603 := bstep (se 1 (by rfl) ⟨795452, by rfl⟩ : syracuseStep 1060603 = 1590905) B1590905
theorem B1584959 : Blo 1056613 1584959 := bstep (se 1 (by rfl) ⟨1188719, by rfl⟩ : syracuseStep 1584959 = 2377439) B2377439
theorem B1191919 : Blo 1056613 1191919 := bstep (se 1 (by rfl) ⟨893939, by rfl⟩ : syracuseStep 1191919 = 1787879) B1787879
theorem B1585145 : Blo 1056613 1585145 := bstep (se 2 (by rfl) ⟨594429, by rfl⟩ : syracuseStep 1585145 = 1188859) B1188859
theorem B1192063 : Blo 1056613 1192063 := bstep (se 1 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 1192063 = 1788095) B1788095
theorem B1585385 : Blo 1056613 1585385 := bstep (se 2 (by rfl) ⟨594519, by rfl⟩ : syracuseStep 1585385 = 1189039) B1189039
theorem B1585511 : Blo 1056613 1585511 := bstep (se 1 (by rfl) ⟨1189133, by rfl⟩ : syracuseStep 1585511 = 2378267) B2378267
theorem B2011547 : Blo 1056613 2011547 := bstep (se 1 (by rfl) ⟨1508660, by rfl⟩ : syracuseStep 2011547 = 3017321) B3017321
theorem B5354099 : Blo 1056613 5354099 := bstep (se 1 (by rfl) ⟨4015574, by rfl⟩ : syracuseStep 5354099 = 8031149) B8031149
theorem B1586057 : Blo 1056613 1586057 := bstep (se 2 (by rfl) ⟨594771, by rfl⟩ : syracuseStep 1586057 = 1189543) B1189543
theorem B22918393 : Blo 1056613 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B1586441 : Blo 1056613 1586441 := bstep (se 2 (by rfl) ⟨594915, by rfl⟩ : syracuseStep 1586441 = 1189831) B1189831
theorem B1586495 : Blo 1056613 1586495 := bstep (se 1 (by rfl) ⟨1189871, by rfl⟩ : syracuseStep 1586495 = 2379743) B2379743
theorem B1586921 : Blo 1056613 1586921 := bstep (se 2 (by rfl) ⟨595095, by rfl⟩ : syracuseStep 1586921 = 1190191) B1190191
theorem B1586927 : Blo 1056613 1586927 := bstep (se 1 (by rfl) ⟨1190195, by rfl⟩ : syracuseStep 1586927 = 2380391) B2380391
theorem B27539183 : Blo 1056613 27539183 := bstep (se 1 (by rfl) ⟨20654387, by rfl⟩ : syracuseStep 27539183 = 41308775) B41308775
theorem B1783849 : Blo 1056613 1783849 := bstep (se 2 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 1783849 = 1337887) B1337887
theorem B2865223 : Blo 1056613 2865223 := bstep (se 1 (by rfl) ⟨2148917, by rfl⟩ : syracuseStep 2865223 = 4297835) B4297835
theorem B1783991 : Blo 1056613 1783991 := bstep (se 1 (by rfl) ⟨1337993, by rfl⟩ : syracuseStep 1783991 = 2675987) B2675987
theorem B1587383 : Blo 1056613 1587383 := bstep (se 1 (by rfl) ⟨1190537, by rfl⟩ : syracuseStep 1587383 = 2381075) B2381075
theorem B3619007 : Blo 1056613 3619007 := bstep (se 1 (by rfl) ⟨2714255, by rfl⟩ : syracuseStep 3619007 = 5428511) B5428511
theorem B5355719 : Blo 1056613 5355719 := bstep (se 1 (by rfl) ⟨4016789, by rfl⟩ : syracuseStep 5355719 = 8033579) B8033579
theorem B1587431 : Blo 1056613 1587431 := bstep (se 1 (by rfl) ⟨1190573, by rfl⟩ : syracuseStep 1587431 = 2381147) B2381147
theorem B6109607 : Blo 1056613 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1587803 : Blo 1056613 1587803 := bstep (se 1 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 1587803 = 2381705) B2381705
theorem B1587947 : Blo 1056613 1587947 := bstep (se 1 (by rfl) ⟨1190960, by rfl⟩ : syracuseStep 1587947 = 2381921) B2381921
theorem B1784585 : Blo 1056613 1784585 := bstep (se 2 (by rfl) ⟨669219, by rfl⟩ : syracuseStep 1784585 = 1338439) B1338439
theorem B1587977 : Blo 1056613 1587977 := bstep (se 2 (by rfl) ⟨595491, by rfl⟩ : syracuseStep 1587977 = 1190983) B1190983
theorem B5094191 : Blo 1056613 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B4013495 : Blo 1056613 4013495 := bstep (se 1 (by rfl) ⟨3010121, by rfl⟩ : syracuseStep 4013495 = 6020243) B6020243
theorem B1588847 : Blo 1056613 1588847 := bstep (se 1 (by rfl) ⟨1191635, by rfl⟩ : syracuseStep 1588847 = 2383271) B2383271
theorem B1588967 : Blo 1056613 1588967 := bstep (se 1 (by rfl) ⟨1191725, by rfl⟩ : syracuseStep 1588967 = 2383451) B2383451
theorem B1589159 : Blo 1056613 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B4014299 : Blo 1056613 4014299 := bstep (se 1 (by rfl) ⟨3010724, by rfl⟩ : syracuseStep 4014299 = 6021449) B6021449
theorem B1589483 : Blo 1056613 1589483 := bstep (se 1 (by rfl) ⟨1192112, by rfl⟩ : syracuseStep 1589483 = 2384225) B2384225
theorem B9060605 : Blo 1056613 9060605 := bstep (se 3 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 9060605 = 3397727) B3397727
theorem B1786151 : Blo 1056613 1786151 := bstep (se 1 (by rfl) ⟨1339613, by rfl⟩ : syracuseStep 1786151 = 2679227) B2679227
theorem B1589543 : Blo 1056613 1589543 := bstep (se 1 (by rfl) ⟨1192157, by rfl⟩ : syracuseStep 1589543 = 2384315) B2384315
theorem B1131175 : Blo 1056613 1131175 := bstep (se 1 (by rfl) ⟨848381, by rfl⟩ : syracuseStep 1131175 = 1696763) B1696763
theorem B8045243 : Blo 1056613 8045243 := bstep (se 1 (by rfl) ⟨6033932, by rfl⟩ : syracuseStep 8045243 = 12067865) B12067865
theorem B1590215 : Blo 1056613 1590215 := bstep (se 1 (by rfl) ⟨1192661, by rfl⟩ : syracuseStep 1590215 = 2385323) B2385323
theorem B27149417 : Blo 1056613 27149417 := bstep (se 2 (by rfl) ⟨10181031, by rfl⟩ : syracuseStep 27149417 = 20362063) B20362063
theorem B1590383 : Blo 1056613 1590383 := bstep (se 1 (by rfl) ⟨1192787, by rfl⟩ : syracuseStep 1590383 = 2385575) B2385575
theorem B1590575 : Blo 1056613 1590575 := bstep (se 1 (by rfl) ⟨1192931, by rfl⟩ : syracuseStep 1590575 = 2385863) B2385863
theorem B4015439 : Blo 1056613 4015439 := bstep (se 1 (by rfl) ⟨3011579, by rfl⟩ : syracuseStep 4015439 = 6023159) B6023159
theorem B1787305 : Blo 1056613 1787305 := bstep (se 2 (by rfl) ⟨670239, by rfl⟩ : syracuseStep 1787305 = 1340479) B1340479
theorem B2901431 : Blo 1056613 2901431 := bstep (se 1 (by rfl) ⟨2176073, by rfl⟩ : syracuseStep 2901431 = 4352147) B4352147
theorem B1590779 : Blo 1056613 1590779 := bstep (se 1 (by rfl) ⟨1193084, by rfl⟩ : syracuseStep 1590779 = 2386169) B2386169
theorem B1525279 : Blo 1056613 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B1590815 : Blo 1056613 1590815 := bstep (se 1 (by rfl) ⟨1193111, by rfl⟩ : syracuseStep 1590815 = 2386223) B2386223
theorem B2377511 : Blo 1056613 2377511 := bstep (se 1 (by rfl) ⟨1783133, by rfl⟩ : syracuseStep 2377511 = 3566267) B3566267
theorem B2410279 : Blo 1056613 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B2377889 : Blo 1056613 2377889 := bstep (se 2 (by rfl) ⟨891708, by rfl⟩ : syracuseStep 2377889 = 1783417) B1783417
theorem B97863875 : Blo 1056613 97863875 := bstep (se 1 (by rfl) ⟨73397906, by rfl⟩ : syracuseStep 97863875 = 146795813) B146795813
theorem B2542175 : Blo 1056613 2542175 := bstep (se 1 (by rfl) ⟨1906631, by rfl⟩ : syracuseStep 2542175 = 3813263) B3813263
theorem B34294553 : Blo 1056613 34294553 := bstep (se 2 (by rfl) ⟨12860457, by rfl⟩ : syracuseStep 34294553 = 25720915) B25720915
theorem B2378537 : Blo 1056613 2378537 := bstep (se 2 (by rfl) ⟨891951, by rfl⟩ : syracuseStep 2378537 = 1783903) B1783903
theorem B3394345 : Blo 1056613 3394345 := bstep (se 2 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 3394345 = 2545759) B2545759
theorem B12209201 : Blo 1056613 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B2378807 : Blo 1056613 2378807 := bstep (se 1 (by rfl) ⟨1784105, by rfl⟩ : syracuseStep 2378807 = 3568211) B3568211
theorem B2379239 : Blo 1056613 2379239 := bstep (se 1 (by rfl) ⟨1784429, by rfl⟩ : syracuseStep 2379239 = 3568859) B3568859
theorem B12045995 : Blo 1056613 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B2412359 : Blo 1056613 2412359 := bstep (se 1 (by rfl) ⟨1809269, by rfl⟩ : syracuseStep 2412359 = 3618539) B3618539
theorem B2674559 : Blo 1056613 2674559 := bstep (se 1 (by rfl) ⟨2005919, by rfl⟩ : syracuseStep 2674559 = 4011839) B4011839
theorem B2379815 : Blo 1056613 2379815 := bstep (se 1 (by rfl) ⟨1784861, by rfl⟩ : syracuseStep 2379815 = 3569723) B3569723
theorem B2379995 : Blo 1056613 2379995 := bstep (se 1 (by rfl) ⟨1784996, by rfl⟩ : syracuseStep 2379995 = 3569993) B3569993
theorem B8376605 : Blo 1056613 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B4903265 : Blo 1056613 4903265 := bstep (se 2 (by rfl) ⟨1838724, by rfl⟩ : syracuseStep 4903265 = 3677449) B3677449
theorem B4018643 : Blo 1056613 4018643 := bstep (se 1 (by rfl) ⟨3013982, by rfl⟩ : syracuseStep 4018643 = 6027965) B6027965
theorem B2675177 : Blo 1056613 2675177 := bstep (se 2 (by rfl) ⟨1003191, by rfl⟩ : syracuseStep 2675177 = 2006383) B2006383
theorem B2380265 : Blo 1056613 2380265 := bstep (se 2 (by rfl) ⟨892599, by rfl⟩ : syracuseStep 2380265 = 1785199) B1785199
theorem B5362523 : Blo 1056613 5362523 := bstep (se 1 (by rfl) ⟨4021892, by rfl⟩ : syracuseStep 5362523 = 8043785) B8043785
theorem B6771671 : Blo 1056613 6771671 := bstep (se 1 (by rfl) ⟨5078753, by rfl⟩ : syracuseStep 6771671 = 10157507) B10157507
theorem B4019159 : Blo 1056613 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B2380769 : Blo 1056613 2380769 := bstep (se 2 (by rfl) ⟨892788, by rfl⟩ : syracuseStep 2380769 = 1785577) B1785577
theorem B13063157 : Blo 1056613 13063157 := bstep (se 5 (by rfl) ⟨612335, by rfl⟩ : syracuseStep 13063157 = 1224671) B1224671
theorem B2380895 : Blo 1056613 2380895 := bstep (se 1 (by rfl) ⟨1785671, by rfl⟩ : syracuseStep 2380895 = 3571343) B3571343
theorem B38589857 : Blo 1056613 38589857 := bstep (se 2 (by rfl) ⟨14471196, by rfl⟩ : syracuseStep 38589857 = 28942393) B28942393
theorem B2676361 : Blo 1056613 2676361 := bstep (se 2 (by rfl) ⟨1003635, by rfl⟩ : syracuseStep 2676361 = 2007271) B2007271
theorem B123655987 : Blo 1056613 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B2381651 : Blo 1056613 2381651 := bstep (se 1 (by rfl) ⟨1786238, by rfl⟩ : syracuseStep 2381651 = 3572477) B3572477
theorem B6772571 : Blo 1056613 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B6019217 : Blo 1056613 6019217 := bstep (se 2 (by rfl) ⟨2257206, by rfl⟩ : syracuseStep 6019217 = 4514413) B4514413
theorem B2545951 : Blo 1056613 2545951 := bstep (se 1 (by rfl) ⟨1909463, by rfl⟩ : syracuseStep 2545951 = 3818927) B3818927
theorem B2382137 : Blo 1056613 2382137 := bstep (se 2 (by rfl) ⟨893301, by rfl⟩ : syracuseStep 2382137 = 1786603) B1786603
theorem B2677151 : Blo 1056613 2677151 := bstep (se 1 (by rfl) ⟨2007863, by rfl⟩ : syracuseStep 2677151 = 4015727) B4015727
theorem B11426291 : Blo 1056613 11426291 := bstep (se 1 (by rfl) ⟨8569718, by rfl⟩ : syracuseStep 11426291 = 17139437) B17139437
theorem B4021103 : Blo 1056613 4021103 := bstep (se 1 (by rfl) ⟨3015827, by rfl⟩ : syracuseStep 4021103 = 6031655) B6031655
theorem B2383055 : Blo 1056613 2383055 := bstep (se 1 (by rfl) ⟨1787291, by rfl⟩ : syracuseStep 2383055 = 3574583) B3574583
theorem B2678123 : Blo 1056613 2678123 := bstep (se 1 (by rfl) ⟨2008592, by rfl⟩ : syracuseStep 2678123 = 4017185) B4017185
theorem B2383433 : Blo 1056613 2383433 := bstep (se 2 (by rfl) ⟨893787, by rfl⟩ : syracuseStep 2383433 = 1787575) B1787575
theorem B1269535 : Blo 1056613 1269535 := bstep (se 1 (by rfl) ⟨952151, by rfl⟩ : syracuseStep 1269535 = 1904303) B1904303
theorem B2678771 : Blo 1056613 2678771 := bstep (se 1 (by rfl) ⟨2009078, by rfl⟩ : syracuseStep 2678771 = 4018157) B4018157
theorem B4514105 : Blo 1056613 4514105 := bstep (se 2 (by rfl) ⟨1692789, by rfl⟩ : syracuseStep 4514105 = 3385579) B3385579
theorem B3301843 : Blo 1056613 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B10183265 : Blo 1056613 10183265 := bstep (se 2 (by rfl) ⟨3818724, by rfl⟩ : syracuseStep 10183265 = 7637449) B7637449
theorem B2384603 : Blo 1056613 2384603 := bstep (se 1 (by rfl) ⟨1788452, by rfl⟩ : syracuseStep 2384603 = 3576905) B3576905
theorem B1270895 : Blo 1056613 1270895 := bstep (se 1 (by rfl) ⟨953171, by rfl⟩ : syracuseStep 1270895 = 1906343) B1906343
theorem B2385017 : Blo 1056613 2385017 := bstep (se 2 (by rfl) ⟨894381, by rfl⟩ : syracuseStep 2385017 = 1788763) B1788763
theorem B7628165 : Blo 1056613 7628165 := bstep (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) B1430281
theorem B52159949 : Blo 1056613 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B15492653 : Blo 1056613 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B5432903 : Blo 1056613 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B2680391 : Blo 1056613 2680391 := bstep (se 1 (by rfl) ⟨2010293, by rfl⟩ : syracuseStep 2680391 = 4020587) B4020587
theorem B55830215 : Blo 1056613 55830215 := bstep (se 1 (by rfl) ⟨41872661, by rfl⟩ : syracuseStep 55830215 = 83745323) B83745323
theorem B6022907 : Blo 1056613 6022907 := bstep (se 1 (by rfl) ⟨4517180, by rfl⟩ : syracuseStep 6022907 = 9034361) B9034361
theorem B2385683 : Blo 1056613 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B2680715 : Blo 1056613 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B5367707 : Blo 1056613 5367707 := bstep (se 1 (by rfl) ⟨4025780, by rfl⟩ : syracuseStep 5367707 = 8051561) B8051561
theorem B2385899 : Blo 1056613 2385899 := bstep (se 1 (by rfl) ⟨1789424, by rfl⟩ : syracuseStep 2385899 = 3578849) B3578849
theorem B19294193 : Blo 1056613 19294193 := bstep (se 2 (by rfl) ⟨7235322, by rfl⟩ : syracuseStep 19294193 = 14470645) B14470645
theorem B10184723 : Blo 1056613 10184723 := bstep (se 1 (by rfl) ⟨7638542, by rfl⟩ : syracuseStep 10184723 = 15277085) B15277085
theorem B2386043 : Blo 1056613 2386043 := bstep (se 1 (by rfl) ⟨1789532, by rfl⟩ : syracuseStep 2386043 = 3579065) B3579065
theorem B1698185 : Blo 1056613 1698185 := bstep (se 2 (by rfl) ⟨636819, by rfl⟩ : syracuseStep 1698185 = 1273639) B1273639
theorem B2386313 : Blo 1056613 2386313 := bstep (se 2 (by rfl) ⟨894867, by rfl⟩ : syracuseStep 2386313 = 1789735) B1789735
theorem B2682335 : Blo 1056613 2682335 := bstep (se 1 (by rfl) ⟨2011751, by rfl⟩ : syracuseStep 2682335 = 4023503) B4023503
theorem B5729773 : Blo 1056613 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B20344841 : Blo 1056613 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B2682953 : Blo 1056613 2682953 := bstep (se 2 (by rfl) ⟨1006107, by rfl⟩ : syracuseStep 2682953 = 2012215) B2012215
theorem B4026631 : Blo 1056613 4026631 := bstep (se 1 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 4026631 = 6039947) B6039947
theorem B8024345 : Blo 1056613 8024345 := bstep (se 2 (by rfl) ⟨3009129, by rfl⟩ : syracuseStep 8024345 = 6018259) B6018259
theorem B23196007 : Blo 1056613 23196007 := bstep (se 1 (by rfl) ⟨17397005, by rfl⟩ : syracuseStep 23196007 = 34794011) B34794011
theorem B4518479 : Blo 1056613 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B6025823 : Blo 1056613 6025823 := bstep (se 1 (by rfl) ⟨4519367, by rfl⟩ : syracuseStep 6025823 = 9038735) B9038735
theorem B1340155 : Blo 1056613 1340155 := bstep (se 1 (by rfl) ⟨1005116, by rfl⟩ : syracuseStep 1340155 = 2010233) B2010233
theorem B2684087 : Blo 1056613 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B20117393 : Blo 1056613 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B1505351 : Blo 1056613 1505351 := bstep (se 1 (by rfl) ⟨1129013, by rfl⟩ : syracuseStep 1505351 = 2258027) B2258027
theorem B4520119 : Blo 1056613 4520119 := bstep (se 1 (by rfl) ⟨3390089, by rfl⟩ : syracuseStep 4520119 = 6780179) B6780179
theorem B1341623 : Blo 1056613 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B6879755 : Blo 1056613 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B8027261 : Blo 1056613 8027261 := bstep (se 3 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 8027261 = 3010223) B3010223
theorem B3570911 : Blo 1056613 3570911 := bstep (se 1 (by rfl) ⟨2678183, by rfl⟩ : syracuseStep 3570911 = 5356367) B5356367
theorem B55049645 : Blo 1056613 55049645 := bstep (se 3 (by rfl) ⟨10321808, by rfl⟩ : syracuseStep 55049645 = 20643617) B20643617
theorem B20315933 : Blo 1056613 20315933 := bstep (se 3 (by rfl) ⟨3809237, by rfl⟩ : syracuseStep 20315933 = 7618475) B7618475
theorem B16744391 : Blo 1056613 16744391 := bstep (se 1 (by rfl) ⟨12558293, by rfl⟩ : syracuseStep 16744391 = 25116587) B25116587
theorem B5079293 : Blo 1056613 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B12059117 : Blo 1056613 12059117 := bstep (se 3 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 12059117 = 4522169) B4522169
theorem B1508159 : Blo 1056613 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B1508233 : Blo 1056613 1508233 := bstep (se 2 (by rfl) ⟨565587, by rfl⟩ : syracuseStep 1508233 = 1131175) B1131175
theorem B13075373 : Blo 1056613 13075373 := bstep (se 3 (by rfl) ⟨2451632, by rfl⟩ : syracuseStep 13075373 = 4903265) B4903265
theorem B1934287 : Blo 1056613 1934287 := bstep (se 1 (by rfl) ⟨1450715, by rfl⟩ : syracuseStep 1934287 = 2901431) B2901431
theorem B65242583 : Blo 1056613 65242583 := bstep (se 1 (by rfl) ⟨48931937, by rfl⟩ : syracuseStep 65242583 = 97863875) B97863875
theorem B4523795 : Blo 1056613 4523795 := bstep (se 1 (by rfl) ⟨3392846, by rfl⟩ : syracuseStep 4523795 = 6785693) B6785693
theorem B16320311 : Blo 1056613 16320311 := bstep (se 1 (by rfl) ⟨12240233, by rfl⟩ : syracuseStep 16320311 = 24480467) B24480467
theorem B2033705 : Blo 1056613 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B8030663 : Blo 1056613 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B1608239 : Blo 1056613 1608239 := bstep (se 1 (by rfl) ⟨1206179, by rfl⟩ : syracuseStep 1608239 = 2412359) B2412359
theorem B3017513 : Blo 1056613 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B6032339 : Blo 1056613 6032339 := bstep (se 1 (by rfl) ⟨4524254, by rfl⟩ : syracuseStep 6032339 = 9048509) B9048509
theorem B3575015 : Blo 1056613 3575015 := bstep (se 1 (by rfl) ⟨2681261, by rfl⟩ : syracuseStep 3575015 = 5362523) B5362523
theorem B25726571 : Blo 1056613 25726571 := bstep (se 1 (by rfl) ⟨19294928, by rfl⟩ : syracuseStep 25726571 = 38589857) B38589857
theorem B4525793 : Blo 1056613 4525793 := bstep (se 2 (by rfl) ⟨1697172, by rfl⟩ : syracuseStep 4525793 = 3394345) B3394345
theorem B3018971 : Blo 1056613 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B7639697 : Blo 1056613 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B3020111 : Blo 1056613 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B6788843 : Blo 1056613 6788843 := bstep (se 1 (by rfl) ⟨5091632, by rfl⟩ : syracuseStep 6788843 = 10183265) B10183265
theorem B3577661 : Blo 1056613 3577661 := bstep (se 3 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 3577661 = 1341623) B1341623
theorem B5085443 : Blo 1056613 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B34773299 : Blo 1056613 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B4528493 : Blo 1056613 4528493 := bstep (se 3 (by rfl) ⟨849092, by rfl⟩ : syracuseStep 4528493 = 1698185) B1698185
theorem B10328435 : Blo 1056613 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B16292285 : Blo 1056613 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B3578471 : Blo 1056613 3578471 := bstep (se 1 (by rfl) ⟨2683853, by rfl⟩ : syracuseStep 3578471 = 5367707) B5367707
theorem B6789815 : Blo 1056613 6789815 := bstep (se 1 (by rfl) ⟨5092361, by rfl⟩ : syracuseStep 6789815 = 10184723) B10184723
theorem B6036713 : Blo 1056613 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B24452387 : Blo 1056613 24452387 := bstep (se 1 (by rfl) ⟨18339290, by rfl⟩ : syracuseStep 24452387 = 36678581) B36678581
theorem B1056639 : Blo 1056613 1056639 := bstep (se 1 (by rfl) ⟨792479, by rfl⟩ : syracuseStep 1056639 = 1584959) B1584959
theorem B1056763 : Blo 1056613 1056763 := bstep (se 1 (by rfl) ⟨792572, by rfl⟩ : syracuseStep 1056763 = 1585145) B1585145
theorem B108666929 : Blo 1056613 108666929 := bstep (se 2 (by rfl) ⟨40750098, by rfl⟩ : syracuseStep 108666929 = 81500197) B81500197
theorem B1056923 : Blo 1056613 1056923 := bstep (se 1 (by rfl) ⟨792692, by rfl⟩ : syracuseStep 1056923 = 1585385) B1585385
theorem B5349563 : Blo 1056613 5349563 := bstep (se 1 (by rfl) ⟨4012172, by rfl⟩ : syracuseStep 5349563 = 8024345) B8024345
theorem B1057007 : Blo 1056613 1057007 := bstep (se 1 (by rfl) ⟨792755, by rfl⟩ : syracuseStep 1057007 = 1585511) B1585511
theorem B1057371 : Blo 1056613 1057371 := bstep (se 1 (by rfl) ⟨793028, by rfl⟩ : syracuseStep 1057371 = 1586057) B1586057
theorem B1057627 : Blo 1056613 1057627 := bstep (se 1 (by rfl) ⟨793220, by rfl⟩ : syracuseStep 1057627 = 1586441) B1586441
theorem B1057663 : Blo 1056613 1057663 := bstep (se 1 (by rfl) ⟨793247, by rfl⟩ : syracuseStep 1057663 = 1586495) B1586495
theorem B1057947 : Blo 1056613 1057947 := bstep (se 1 (by rfl) ⟨793460, by rfl⟩ : syracuseStep 1057947 = 1586921) B1586921
theorem B1057951 : Blo 1056613 1057951 := bstep (se 1 (by rfl) ⟨793463, by rfl⟩ : syracuseStep 1057951 = 1586927) B1586927
theorem B18359455 : Blo 1056613 18359455 := bstep (se 1 (by rfl) ⟨13769591, by rfl⟩ : syracuseStep 18359455 = 27539183) B27539183
theorem B13411595 : Blo 1056613 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B9053633 : Blo 1056613 9053633 := bstep (se 2 (by rfl) ⟨3395112, by rfl⟩ : syracuseStep 9053633 = 6790225) B6790225
theorem B1189327 : Blo 1056613 1189327 := bstep (se 1 (by rfl) ⟨891995, by rfl⟩ : syracuseStep 1189327 = 1783991) B1783991
theorem B1058255 : Blo 1056613 1058255 := bstep (se 1 (by rfl) ⟨793691, by rfl⟩ : syracuseStep 1058255 = 1587383) B1587383
theorem B1058287 : Blo 1056613 1058287 := bstep (se 1 (by rfl) ⟨793715, by rfl⟩ : syracuseStep 1058287 = 1587431) B1587431
theorem B12854821 : Blo 1056613 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B1058535 : Blo 1056613 1058535 := bstep (se 1 (by rfl) ⟨793901, by rfl⟩ : syracuseStep 1058535 = 1587803) B1587803
theorem B1058631 : Blo 1056613 1058631 := bstep (se 1 (by rfl) ⟨793973, by rfl⟩ : syracuseStep 1058631 = 1587947) B1587947
theorem B1189723 : Blo 1056613 1189723 := bstep (se 1 (by rfl) ⟨892292, by rfl⟩ : syracuseStep 1189723 = 1784585) B1784585
theorem B1058651 : Blo 1056613 1058651 := bstep (se 1 (by rfl) ⟨793988, by rfl⟩ : syracuseStep 1058651 = 1587977) B1587977
theorem B5351507 : Blo 1056613 5351507 := bstep (se 1 (by rfl) ⟨4013630, by rfl⟩ : syracuseStep 5351507 = 8027261) B8027261
theorem B1059231 : Blo 1056613 1059231 := bstep (se 1 (by rfl) ⟨794423, by rfl⟩ : syracuseStep 1059231 = 1588847) B1588847
theorem B1059311 : Blo 1056613 1059311 := bstep (se 1 (by rfl) ⟨794483, by rfl⟩ : syracuseStep 1059311 = 1588967) B1588967
theorem B13543955 : Blo 1056613 13543955 := bstep (se 1 (by rfl) ⟨10157966, by rfl⟩ : syracuseStep 13543955 = 20315933) B20315933
theorem B1059439 : Blo 1056613 1059439 := bstep (se 1 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 1059439 = 1589159) B1589159
theorem B1059655 : Blo 1056613 1059655 := bstep (se 1 (by rfl) ⟨794741, by rfl⟩ : syracuseStep 1059655 = 1589483) B1589483
theorem B6040403 : Blo 1056613 6040403 := bstep (se 1 (by rfl) ⟨4530302, by rfl⟩ : syracuseStep 6040403 = 9060605) B9060605
theorem B1190767 : Blo 1056613 1190767 := bstep (se 1 (by rfl) ⟨893075, by rfl⟩ : syracuseStep 1190767 = 1786151) B1786151
theorem B1059695 : Blo 1056613 1059695 := bstep (se 1 (by rfl) ⟨794771, by rfl⟩ : syracuseStep 1059695 = 1589543) B1589543
theorem B4402457 : Blo 1056613 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B2010415 : Blo 1056613 2010415 := bstep (se 1 (by rfl) ⟨1507811, by rfl⟩ : syracuseStep 2010415 = 3015623) B3015623
theorem B1060143 : Blo 1056613 1060143 := bstep (se 1 (by rfl) ⟨795107, by rfl⟩ : syracuseStep 1060143 = 1590215) B1590215
theorem B4828511 : Blo 1056613 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B18099611 : Blo 1056613 18099611 := bstep (se 1 (by rfl) ⟨13574708, by rfl⟩ : syracuseStep 18099611 = 27149417) B27149417
theorem B1060255 : Blo 1056613 1060255 := bstep (se 1 (by rfl) ⟨795191, by rfl⟩ : syracuseStep 1060255 = 1590383) B1590383
theorem B1060383 : Blo 1056613 1060383 := bstep (se 1 (by rfl) ⟨795287, by rfl⟩ : syracuseStep 1060383 = 1590575) B1590575
theorem B5353127 : Blo 1056613 5353127 := bstep (se 1 (by rfl) ⟨4014845, by rfl⟩ : syracuseStep 5353127 = 8029691) B8029691
theorem B1060519 : Blo 1056613 1060519 := bstep (se 1 (by rfl) ⟨795389, by rfl⟩ : syracuseStep 1060519 = 1590779) B1590779
theorem B1060543 : Blo 1056613 1060543 := bstep (se 1 (by rfl) ⟨795407, by rfl⟩ : syracuseStep 1060543 = 1590815) B1590815
theorem B1585007 : Blo 1056613 1585007 := bstep (se 1 (by rfl) ⟨1188755, by rfl⟩ : syracuseStep 1585007 = 2377511) B2377511
theorem B1585259 : Blo 1056613 1585259 := bstep (se 1 (by rfl) ⟨1188944, by rfl⟩ : syracuseStep 1585259 = 2377889) B2377889
theorem B2011243 : Blo 1056613 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B1585691 : Blo 1056613 1585691 := bstep (se 1 (by rfl) ⟨1189268, by rfl⟩ : syracuseStep 1585691 = 2378537) B2378537
theorem B8139467 : Blo 1056613 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B1585871 : Blo 1056613 1585871 := bstep (se 1 (by rfl) ⟨1189403, by rfl⟩ : syracuseStep 1585871 = 2378807) B2378807
theorem B1586159 : Blo 1056613 1586159 := bstep (se 1 (by rfl) ⟨1189619, by rfl⟩ : syracuseStep 1586159 = 2379239) B2379239
theorem B1783039 : Blo 1056613 1783039 := bstep (se 1 (by rfl) ⟨1337279, by rfl⟩ : syracuseStep 1783039 = 2674559) B2674559
theorem B1586543 : Blo 1056613 1586543 := bstep (se 1 (by rfl) ⟨1189907, by rfl⟩ : syracuseStep 1586543 = 2379815) B2379815
theorem B1586663 : Blo 1056613 1586663 := bstep (se 1 (by rfl) ⟨1189997, by rfl⟩ : syracuseStep 1586663 = 2379995) B2379995
theorem B5584403 : Blo 1056613 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B3389053 : Blo 1056613 3389053 := bstep (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) B1270895
theorem B1783451 : Blo 1056613 1783451 := bstep (se 1 (by rfl) ⟨1337588, by rfl⟩ : syracuseStep 1783451 = 2675177) B2675177
theorem B1586843 : Blo 1056613 1586843 := bstep (se 1 (by rfl) ⟨1190132, by rfl⟩ : syracuseStep 1586843 = 2380265) B2380265
theorem B1587179 : Blo 1056613 1587179 := bstep (se 1 (by rfl) ⟨1190384, by rfl⟩ : syracuseStep 1587179 = 2380769) B2380769
theorem B1587263 : Blo 1056613 1587263 := bstep (se 1 (by rfl) ⟨1190447, by rfl⟩ : syracuseStep 1587263 = 2380895) B2380895
theorem B13547645 : Blo 1056613 13547645 := bstep (se 3 (by rfl) ⟨2540183, by rfl⟩ : syracuseStep 13547645 = 5080367) B5080367
theorem B1587593 : Blo 1056613 1587593 := bstep (se 2 (by rfl) ⟨595347, by rfl⟩ : syracuseStep 1587593 = 1190695) B1190695
theorem B1587767 : Blo 1056613 1587767 := bstep (se 1 (by rfl) ⟨1190825, by rfl⟩ : syracuseStep 1587767 = 2381651) B2381651
theorem B12073697 : Blo 1056613 12073697 := bstep (se 2 (by rfl) ⟨4527636, by rfl⟩ : syracuseStep 12073697 = 9055273) B9055273
theorem B4012811 : Blo 1056613 4012811 := bstep (se 1 (by rfl) ⟨3009608, by rfl⟩ : syracuseStep 4012811 = 6019217) B6019217
theorem B1588091 : Blo 1056613 1588091 := bstep (se 1 (by rfl) ⟨1191068, by rfl⟩ : syracuseStep 1588091 = 2382137) B2382137
theorem B1784767 : Blo 1056613 1784767 := bstep (se 1 (by rfl) ⟨1338575, by rfl⟩ : syracuseStep 1784767 = 2677151) B2677151
theorem B7617527 : Blo 1056613 7617527 := bstep (se 1 (by rfl) ⟨5713145, by rfl⟩ : syracuseStep 7617527 = 11426291) B11426291
theorem B5356691 : Blo 1056613 5356691 := bstep (se 1 (by rfl) ⟨4017518, by rfl⟩ : syracuseStep 5356691 = 8035037) B8035037
theorem B45792499 : Blo 1056613 45792499 := bstep (se 1 (by rfl) ⟨34344374, by rfl⟩ : syracuseStep 45792499 = 68688749) B68688749
theorem B2866607 : Blo 1056613 2866607 := bstep (se 1 (by rfl) ⟨2149955, by rfl⟩ : syracuseStep 2866607 = 4299911) B4299911
theorem B1588703 : Blo 1056613 1588703 := bstep (se 1 (by rfl) ⟨1191527, by rfl⟩ : syracuseStep 1588703 = 2383055) B2383055
theorem B1785415 : Blo 1056613 1785415 := bstep (se 1 (by rfl) ⟨1339061, by rfl⟩ : syracuseStep 1785415 = 2678123) B2678123
theorem B1588955 : Blo 1056613 1588955 := bstep (se 1 (by rfl) ⟨1191716, by rfl⟩ : syracuseStep 1588955 = 2383433) B2383433
theorem B1589225 : Blo 1056613 1589225 := bstep (se 2 (by rfl) ⟨595959, by rfl⟩ : syracuseStep 1589225 = 1191919) B1191919
theorem B1785847 : Blo 1056613 1785847 := bstep (se 1 (by rfl) ⟨1339385, by rfl⟩ : syracuseStep 1785847 = 2678771) B2678771
theorem B1589417 : Blo 1056613 1589417 := bstep (se 2 (by rfl) ⟨596031, by rfl⟩ : syracuseStep 1589417 = 1192063) B1192063
theorem B4014269 : Blo 1056613 4014269 := bstep (se 3 (by rfl) ⟨752675, by rfl⟩ : syracuseStep 4014269 = 1505351) B1505351
theorem B1589735 : Blo 1056613 1589735 := bstep (se 1 (by rfl) ⟨1192301, by rfl⟩ : syracuseStep 1589735 = 2384603) B2384603
theorem B3392243 : Blo 1056613 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B1590011 : Blo 1056613 1590011 := bstep (se 1 (by rfl) ⟨1192508, by rfl⟩ : syracuseStep 1590011 = 2385017) B2385017
theorem B1786873 : Blo 1056613 1786873 := bstep (se 2 (by rfl) ⟨670077, by rfl⟩ : syracuseStep 1786873 = 1340155) B1340155
theorem B12239905 : Blo 1056613 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B3621935 : Blo 1056613 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B1786927 : Blo 1056613 1786927 := bstep (se 1 (by rfl) ⟨1340195, by rfl⟩ : syracuseStep 1786927 = 2680391) B2680391
theorem B4015271 : Blo 1056613 4015271 := bstep (se 1 (by rfl) ⟨3011453, by rfl⟩ : syracuseStep 4015271 = 6022907) B6022907
theorem B1590455 : Blo 1056613 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B1787143 : Blo 1056613 1787143 := bstep (se 1 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 1787143 = 2680715) B2680715
theorem B1590599 : Blo 1056613 1590599 := bstep (se 1 (by rfl) ⟨1192949, by rfl⟩ : syracuseStep 1590599 = 2385899) B2385899
theorem B12862795 : Blo 1056613 12862795 := bstep (se 1 (by rfl) ⟨9647096, by rfl⟩ : syracuseStep 12862795 = 19294193) B19294193
theorem B1590695 : Blo 1056613 1590695 := bstep (se 1 (by rfl) ⟨1193021, by rfl⟩ : syracuseStep 1590695 = 2386043) B2386043
theorem B1590875 : Blo 1056613 1590875 := bstep (se 1 (by rfl) ⟨1193156, by rfl⟩ : syracuseStep 1590875 = 2386313) B2386313
theorem B30557857 : Blo 1056613 30557857 := bstep (se 2 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 30557857 = 22918393) B22918393
theorem B1788223 : Blo 1056613 1788223 := bstep (se 1 (by rfl) ⟨1341167, by rfl⟩ : syracuseStep 1788223 = 2682335) B2682335
theorem B164874649 : Blo 1056613 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B1788635 : Blo 1056613 1788635 := bstep (se 1 (by rfl) ⟨1341476, by rfl⟩ : syracuseStep 1788635 = 2682953) B2682953
theorem B2378465 : Blo 1056613 2378465 := bstep (se 2 (by rfl) ⟨891924, by rfl⟩ : syracuseStep 2378465 = 1783849) B1783849
theorem B3820297 : Blo 1056613 3820297 := bstep (se 2 (by rfl) ⟨1432611, by rfl⟩ : syracuseStep 3820297 = 2865223) B2865223
theorem B2542433 : Blo 1056613 2542433 := bstep (se 2 (by rfl) ⟨953412, by rfl⟩ : syracuseStep 2542433 = 1906825) B1906825
theorem B3394601 : Blo 1056613 3394601 := bstep (se 2 (by rfl) ⟨1272975, by rfl⟩ : syracuseStep 3394601 = 2545951) B2545951
theorem B4017215 : Blo 1056613 4017215 := bstep (se 1 (by rfl) ⟨3012911, by rfl⟩ : syracuseStep 4017215 = 6025823) B6025823
theorem B1789391 : Blo 1056613 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B2412671 : Blo 1056613 2412671 := bstep (se 1 (by rfl) ⟨1809503, by rfl⟩ : syracuseStep 2412671 = 3619007) B3619007
theorem B3396127 : Blo 1056613 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B2380607 : Blo 1056613 2380607 := bstep (se 1 (by rfl) ⟨1785455, by rfl⟩ : syracuseStep 2380607 = 3570911) B3570911
theorem B2675663 : Blo 1056613 2675663 := bstep (se 1 (by rfl) ⟨2006747, by rfl⟩ : syracuseStep 2675663 = 4013495) B4013495
theorem B1692713 : Blo 1056613 1692713 := bstep (se 2 (by rfl) ⟨634767, by rfl⟩ : syracuseStep 1692713 = 1269535) B1269535
theorem B11162927 : Blo 1056613 11162927 := bstep (se 1 (by rfl) ⟨8372195, by rfl⟩ : syracuseStep 11162927 = 16744391) B16744391
theorem B2676199 : Blo 1056613 2676199 := bstep (se 1 (by rfl) ⟨2007149, by rfl⟩ : syracuseStep 2676199 = 4014299) B4014299
theorem B5363495 : Blo 1056613 5363495 := bstep (se 1 (by rfl) ⟨4022621, by rfl⟩ : syracuseStep 5363495 = 8045243) B8045243
theorem B9656147 : Blo 1056613 9656147 := bstep (se 1 (by rfl) ⟨7242110, by rfl⟩ : syracuseStep 9656147 = 14484221) B14484221
theorem B5724047 : Blo 1056613 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B2382011 : Blo 1056613 2382011 := bstep (se 1 (by rfl) ⟨1786508, by rfl⟩ : syracuseStep 2382011 = 3573017) B3573017
theorem B6445271 : Blo 1056613 6445271 := bstep (se 1 (by rfl) ⟨4833953, by rfl⟩ : syracuseStep 6445271 = 9667907) B9667907
theorem B2676959 : Blo 1056613 2676959 := bstep (se 1 (by rfl) ⟨2007719, by rfl⟩ : syracuseStep 2676959 = 4015439) B4015439
theorem B2382695 : Blo 1056613 2382695 := bstep (se 1 (by rfl) ⟨1787021, by rfl⟩ : syracuseStep 2382695 = 3574043) B3574043
theorem B2382803 : Blo 1056613 2382803 := bstep (se 1 (by rfl) ⟨1787102, by rfl⟩ : syracuseStep 2382803 = 3574205) B3574205
theorem B1694783 : Blo 1056613 1694783 := bstep (se 1 (by rfl) ⟨1271087, by rfl⟩ : syracuseStep 1694783 = 2542175) B2542175
theorem B2382911 : Blo 1056613 2382911 := bstep (se 1 (by rfl) ⟨1787183, by rfl⟩ : syracuseStep 2382911 = 3574367) B3574367
theorem B22863035 : Blo 1056613 22863035 := bstep (se 1 (by rfl) ⟨17147276, by rfl⟩ : syracuseStep 22863035 = 34294553) B34294553
theorem B2383073 : Blo 1056613 2383073 := bstep (se 2 (by rfl) ⟨893652, by rfl⟩ : syracuseStep 2383073 = 1787305) B1787305
theorem B2384063 : Blo 1056613 2384063 := bstep (se 1 (by rfl) ⟨1788047, by rfl⟩ : syracuseStep 2384063 = 3576095) B3576095
theorem B2679095 : Blo 1056613 2679095 := bstep (se 1 (by rfl) ⟨2009321, by rfl⟩ : syracuseStep 2679095 = 4018643) B4018643
theorem B13591111 : Blo 1056613 13591111 := bstep (se 1 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 13591111 = 20386667) B20386667
theorem B4514447 : Blo 1056613 4514447 := bstep (se 1 (by rfl) ⟨3385835, by rfl⟩ : syracuseStep 4514447 = 6771671) B6771671
theorem B2679439 : Blo 1056613 2679439 := bstep (se 1 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 2679439 = 4019159) B4019159
theorem B8708771 : Blo 1056613 8708771 := bstep (se 1 (by rfl) ⟨6531578, by rfl⟩ : syracuseStep 8708771 = 13063157) B13063157
theorem B4023047 : Blo 1056613 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B2384891 : Blo 1056613 2384891 := bstep (se 1 (by rfl) ⟨1788668, by rfl⟩ : syracuseStep 2384891 = 3577337) B3577337
theorem B2384999 : Blo 1056613 2384999 := bstep (se 1 (by rfl) ⟨1788749, by rfl⟩ : syracuseStep 2384999 = 3577499) B3577499
theorem B2385071 : Blo 1056613 2385071 := bstep (se 1 (by rfl) ⟨1788803, by rfl⟩ : syracuseStep 2385071 = 3577607) B3577607
theorem B4515047 : Blo 1056613 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B4024187 : Blo 1056613 4024187 := bstep (se 1 (by rfl) ⟨3018140, by rfl⟩ : syracuseStep 4024187 = 6036281) B6036281
theorem B2680735 : Blo 1056613 2680735 := bstep (se 1 (by rfl) ⟨2010551, by rfl⟩ : syracuseStep 2680735 = 4021103) B4021103
theorem B9660383 : Blo 1056613 9660383 := bstep (se 1 (by rfl) ⟨7245287, by rfl⟩ : syracuseStep 9660383 = 14490575) B14490575
theorem B6777695 : Blo 1056613 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B3009403 : Blo 1056613 3009403 := bstep (se 1 (by rfl) ⟨2257052, by rfl⟩ : syracuseStep 3009403 = 4514105) B4514105
theorem B5368841 : Blo 1056613 5368841 := bstep (se 2 (by rfl) ⟨2013315, by rfl⟩ : syracuseStep 5368841 = 4026631) B4026631
theorem B30928009 : Blo 1056613 30928009 := bstep (se 2 (by rfl) ⟨11598003, by rfl⟩ : syracuseStep 30928009 = 23196007) B23196007
theorem B3567023 : Blo 1056613 3567023 := bstep (se 1 (by rfl) ⟨2675267, by rfl⟩ : syracuseStep 3567023 = 5350535) B5350535
theorem B4025963 : Blo 1056613 4025963 := bstep (se 1 (by rfl) ⟨3019472, by rfl⟩ : syracuseStep 4025963 = 6038945) B6038945
theorem B37220143 : Blo 1056613 37220143 := bstep (se 1 (by rfl) ⟨27915107, by rfl⟩ : syracuseStep 37220143 = 55830215) B55830215
theorem B18346013 : Blo 1056613 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B3567995 : Blo 1056613 3567995 := bstep (se 1 (by rfl) ⟨2675996, by rfl⟩ : syracuseStep 3567995 = 5351993) B5351993
theorem B6779335 : Blo 1056613 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B18117107 : Blo 1056613 18117107 := bstep (se 1 (by rfl) ⟨13587830, by rfl⟩ : syracuseStep 18117107 = 27175661) B27175661
theorem B3568481 : Blo 1056613 3568481 := bstep (se 2 (by rfl) ⟨1338180, by rfl⟩ : syracuseStep 3568481 = 2676361) B2676361
theorem B13563227 : Blo 1056613 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B6026825 : Blo 1056613 6026825 := bstep (se 2 (by rfl) ⟨2260059, by rfl⟩ : syracuseStep 6026825 = 4520119) B4520119
theorem B1341031 : Blo 1056613 1341031 := bstep (se 1 (by rfl) ⟨1005773, by rfl⟩ : syracuseStep 1341031 = 2011547) B2011547
theorem B3012319 : Blo 1056613 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B3569399 : Blo 1056613 3569399 := bstep (se 1 (by rfl) ⟨2677049, by rfl⟩ : syracuseStep 3569399 = 5354099) B5354099
theorem B3570479 : Blo 1056613 3570479 := bstep (se 1 (by rfl) ⟨2677859, by rfl⟩ : syracuseStep 3570479 = 5355719) B5355719
theorem B21724037 : Blo 1056613 21724037 := bstep (se 4 (by rfl) ⟨2036628, by rfl⟩ : syracuseStep 21724037 = 4073257) B4073257
theorem B36699763 : Blo 1056613 36699763 := bstep (se 1 (by rfl) ⟨27524822, by rfl⟩ : syracuseStep 36699763 = 55049645) B55049645
theorem B2261495 : Blo 1056613 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B8716915 : Blo 1056613 8716915 := bstep (se 1 (by rfl) ⟨6537686, by rfl⟩ : syracuseStep 8716915 = 13075373) B13075373
theorem B18121481 : Blo 1056613 18121481 := bstep (se 2 (by rfl) ⟨6795555, by rfl⟩ : syracuseStep 18121481 = 13591111) B13591111
theorem B3572585 : Blo 1056613 3572585 := bstep (se 2 (by rfl) ⟨1339719, by rfl⟩ : syracuseStep 3572585 = 2679439) B2679439
theorem B3015863 : Blo 1056613 3015863 := bstep (se 1 (by rfl) ⟨2261897, by rfl⟩ : syracuseStep 3015863 = 4523795) B4523795
theorem B10880207 : Blo 1056613 10880207 := bstep (se 1 (by rfl) ⟨8160155, by rfl⟩ : syracuseStep 10880207 = 16320311) B16320311
theorem B16319873 : Blo 1056613 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B24479273 : Blo 1056613 24479273 := bstep (se 2 (by rfl) ⟨9179727, by rfl⟩ : syracuseStep 24479273 = 18359455) B18359455
theorem B2263067 : Blo 1056613 2263067 := bstep (se 1 (by rfl) ⟨1697300, by rfl⟩ : syracuseStep 2263067 = 3394601) B3394601
theorem B17139761 : Blo 1056613 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B3017195 : Blo 1056613 3017195 := bstep (se 1 (by rfl) ⟨2262896, by rfl⟩ : syracuseStep 3017195 = 4525793) B4525793
theorem B3574313 : Blo 1056613 3574313 := bstep (se 2 (by rfl) ⟨1340367, by rfl⟩ : syracuseStep 3574313 = 2680735) B2680735
theorem B7441951 : Blo 1056613 7441951 := bstep (se 1 (by rfl) ⟨5581463, by rfl⟩ : syracuseStep 7441951 = 11162927) B11162927
theorem B4525895 : Blo 1056613 4525895 := bstep (se 1 (by rfl) ⟨3394421, by rfl⟩ : syracuseStep 4525895 = 6788843) B6788843
theorem B3575663 : Blo 1056613 3575663 := bstep (se 1 (by rfl) ⟨2681747, by rfl⟩ : syracuseStep 3575663 = 5363495) B5363495
theorem B4296847 : Blo 1056613 4296847 := bstep (se 1 (by rfl) ⟨3222635, by rfl⟩ : syracuseStep 4296847 = 6445271) B6445271
theorem B3018995 : Blo 1056613 3018995 := bstep (se 1 (by rfl) ⟨2264246, by rfl⟩ : syracuseStep 3018995 = 4528493) B4528493
theorem B6885623 : Blo 1056613 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B4526543 : Blo 1056613 4526543 := bstep (se 1 (by rfl) ⟨3394907, by rfl⟩ : syracuseStep 4526543 = 6789815) B6789815
theorem B15242023 : Blo 1056613 15242023 := bstep (se 1 (by rfl) ⟨11431517, by rfl⟩ : syracuseStep 15242023 = 22863035) B22863035
theorem B5805847 : Blo 1056613 5805847 := bstep (se 1 (by rfl) ⟨4354385, by rfl⟩ : syracuseStep 5805847 = 8708771) B8708771
theorem B4528169 : Blo 1056613 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B6035755 : Blo 1056613 6035755 := bstep (se 1 (by rfl) ⟨4526816, by rfl⟩ : syracuseStep 6035755 = 9053633) B9053633
theorem B3579227 : Blo 1056613 3579227 := bstep (se 1 (by rfl) ⟨2684420, by rfl⟩ : syracuseStep 3579227 = 5368841) B5368841
theorem B12066407 : Blo 1056613 12066407 := bstep (se 1 (by rfl) ⟨9049805, by rfl⟩ : syracuseStep 12066407 = 18099611) B18099611
theorem B1056671 : Blo 1056613 1056671 := bstep (se 1 (by rfl) ⟨792503, by rfl⟩ : syracuseStep 1056671 = 1585007) B1585007
theorem B12230675 : Blo 1056613 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B1056839 : Blo 1056613 1056839 := bstep (se 1 (by rfl) ⟨792629, by rfl⟩ : syracuseStep 1056839 = 1585259) B1585259
theorem B1057127 : Blo 1056613 1057127 := bstep (se 1 (by rfl) ⟨792845, by rfl⟩ : syracuseStep 1057127 = 1585691) B1585691
theorem B1057247 : Blo 1056613 1057247 := bstep (se 1 (by rfl) ⟨792935, by rfl⟩ : syracuseStep 1057247 = 1585871) B1585871
theorem B1057439 : Blo 1056613 1057439 := bstep (se 1 (by rfl) ⟨793079, by rfl⟩ : syracuseStep 1057439 = 1586159) B1586159
theorem B1057695 : Blo 1056613 1057695 := bstep (se 1 (by rfl) ⟨793271, by rfl⟩ : syracuseStep 1057695 = 1586543) B1586543
theorem B1057775 : Blo 1056613 1057775 := bstep (se 1 (by rfl) ⟨793331, by rfl⟩ : syracuseStep 1057775 = 1586663) B1586663
theorem B1188967 : Blo 1056613 1188967 := bstep (se 1 (by rfl) ⟨891725, by rfl⟩ : syracuseStep 1188967 = 1783451) B1783451
theorem B1057895 : Blo 1056613 1057895 := bstep (se 1 (by rfl) ⟨793421, by rfl⟩ : syracuseStep 1057895 = 1586843) B1586843
theorem B1058119 : Blo 1056613 1058119 := bstep (se 1 (by rfl) ⟨793589, by rfl⟩ : syracuseStep 1058119 = 1587179) B1587179
theorem B1058175 : Blo 1056613 1058175 := bstep (se 1 (by rfl) ⟨793631, by rfl⟩ : syracuseStep 1058175 = 1587263) B1587263
theorem B1058395 : Blo 1056613 1058395 := bstep (se 1 (by rfl) ⟨793796, by rfl⟩ : syracuseStep 1058395 = 1587593) B1587593
theorem B61056665 : Blo 1056613 61056665 := bstep (se 2 (by rfl) ⟨22896249, by rfl⟩ : syracuseStep 61056665 = 45792499) B45792499
theorem B1058511 : Blo 1056613 1058511 := bstep (se 1 (by rfl) ⟨793883, by rfl⟩ : syracuseStep 1058511 = 1587767) B1587767
theorem B1058727 : Blo 1056613 1058727 := bstep (se 1 (by rfl) ⟨794045, by rfl⟩ : syracuseStep 1058727 = 1588091) B1588091
theorem B48933017 : Blo 1056613 48933017 := bstep (se 2 (by rfl) ⟨18349881, by rfl⟩ : syracuseStep 48933017 = 36699763) B36699763
theorem B1911071 : Blo 1056613 1911071 := bstep (se 1 (by rfl) ⟨1433303, by rfl⟩ : syracuseStep 1911071 = 2866607) B2866607
theorem B1059135 : Blo 1056613 1059135 := bstep (se 1 (by rfl) ⟨794351, by rfl⟩ : syracuseStep 1059135 = 1588703) B1588703
theorem B1059303 : Blo 1056613 1059303 := bstep (se 1 (by rfl) ⟨794477, by rfl⟩ : syracuseStep 1059303 = 1588955) B1588955
theorem B1059483 : Blo 1056613 1059483 := bstep (se 1 (by rfl) ⟨794612, by rfl⟩ : syracuseStep 1059483 = 1589225) B1589225
theorem B1059611 : Blo 1056613 1059611 := bstep (se 1 (by rfl) ⟨794708, by rfl⟩ : syracuseStep 1059611 = 1589417) B1589417
theorem B3386195 : Blo 1056613 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B1059823 : Blo 1056613 1059823 := bstep (se 1 (by rfl) ⟨794867, by rfl⟩ : syracuseStep 1059823 = 1589735) B1589735
theorem B8039411 : Blo 1056613 8039411 := bstep (se 1 (by rfl) ⟨6029558, by rfl⟩ : syracuseStep 8039411 = 12059117) B12059117
theorem B6433789 : Blo 1056613 6433789 := bstep (se 3 (by rfl) ⟨1206335, by rfl⟩ : syracuseStep 6433789 = 2412671) B2412671
theorem B1060007 : Blo 1056613 1060007 := bstep (se 1 (by rfl) ⟨795005, by rfl⟩ : syracuseStep 1060007 = 1590011) B1590011
theorem B1060303 : Blo 1056613 1060303 := bstep (se 1 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 1060303 = 1590455) B1590455
theorem B1060399 : Blo 1056613 1060399 := bstep (se 1 (by rfl) ⟨795299, by rfl⟩ : syracuseStep 1060399 = 1590599) B1590599
theorem B1060463 : Blo 1056613 1060463 := bstep (se 1 (by rfl) ⟨795347, by rfl⟩ : syracuseStep 1060463 = 1590695) B1590695
theorem B43495055 : Blo 1056613 43495055 := bstep (se 1 (by rfl) ⟨32621291, by rfl⟩ : syracuseStep 43495055 = 65242583) B65242583
theorem B1060583 : Blo 1056613 1060583 := bstep (se 1 (by rfl) ⟨795437, by rfl⟩ : syracuseStep 1060583 = 1590875) B1590875
theorem B2010977 : Blo 1056613 2010977 := bstep (se 2 (by rfl) ⟨754116, by rfl⟩ : syracuseStep 2010977 = 1508233) B1508233
theorem B5353775 : Blo 1056613 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B17150393 : Blo 1056613 17150393 := bstep (se 2 (by rfl) ⟨6431397, by rfl⟩ : syracuseStep 17150393 = 12862795) B12862795
theorem B1192423 : Blo 1056613 1192423 := bstep (se 1 (by rfl) ⟨894317, by rfl⟩ : syracuseStep 1192423 = 1788635) B1788635
theorem B1585643 : Blo 1056613 1585643 := bstep (se 1 (by rfl) ⟨1189232, by rfl⟩ : syracuseStep 1585643 = 2378465) B2378465
theorem B21705245 : Blo 1056613 21705245 := bstep (se 3 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 21705245 = 8139467) B8139467
theorem B1585769 : Blo 1056613 1585769 := bstep (se 2 (by rfl) ⟨594663, by rfl⟩ : syracuseStep 1585769 = 1189327) B1189327
theorem B40743809 : Blo 1056613 40743809 := bstep (se 2 (by rfl) ⟨15278928, by rfl⟩ : syracuseStep 40743809 = 30557857) B30557857
theorem B1192927 : Blo 1056613 1192927 := bstep (se 1 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 1192927 = 1789391) B1789391
theorem B17151047 : Blo 1056613 17151047 := bstep (se 1 (by rfl) ⟨12863285, by rfl⟩ : syracuseStep 17151047 = 25726571) B25726571
theorem B1586297 : Blo 1056613 1586297 := bstep (se 2 (by rfl) ⟨594861, by rfl⟩ : syracuseStep 1586297 = 1189723) B1189723
theorem B5093131 : Blo 1056613 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B1587071 : Blo 1056613 1587071 := bstep (se 1 (by rfl) ⟨1190303, by rfl⟩ : syracuseStep 1587071 = 2380607) B2380607
theorem B1783775 : Blo 1056613 1783775 := bstep (se 1 (by rfl) ⟨1337831, by rfl⟩ : syracuseStep 1783775 = 2675663) B2675663
theorem B1128475 : Blo 1056613 1128475 := bstep (se 1 (by rfl) ⟨846356, by rfl⟩ : syracuseStep 1128475 = 1692713) B1692713
theorem B35764253 : Blo 1056613 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B2013407 : Blo 1056613 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B5093729 : Blo 1056613 5093729 := bstep (se 2 (by rfl) ⟨1910148, by rfl⟩ : syracuseStep 5093729 = 3820297) B3820297
theorem B1587689 : Blo 1056613 1587689 := bstep (se 2 (by rfl) ⟨595383, by rfl⟩ : syracuseStep 1587689 = 1190767) B1190767
theorem B4012537 : Blo 1056613 4012537 := bstep (se 2 (by rfl) ⟨1504701, by rfl⟩ : syracuseStep 4012537 = 3009403) B3009403
theorem B6437431 : Blo 1056613 6437431 := bstep (se 1 (by rfl) ⟨4828073, by rfl⟩ : syracuseStep 6437431 = 9656147) B9656147
theorem B3816031 : Blo 1056613 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B1588007 : Blo 1056613 1588007 := bstep (se 1 (by rfl) ⟨1191005, by rfl⟩ : syracuseStep 1588007 = 2382011) B2382011
theorem B1784639 : Blo 1056613 1784639 := bstep (se 1 (by rfl) ⟨1338479, by rfl⟩ : syracuseStep 1784639 = 2676959) B2676959
theorem B3390295 : Blo 1056613 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B41237345 : Blo 1056613 41237345 := bstep (se 2 (by rfl) ⟨15464004, by rfl⟩ : syracuseStep 41237345 = 30928009) B30928009
theorem B23182199 : Blo 1056613 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B10861523 : Blo 1056613 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B1588463 : Blo 1056613 1588463 := bstep (se 1 (by rfl) ⟨1191347, by rfl⟩ : syracuseStep 1588463 = 2382695) B2382695
theorem B1588535 : Blo 1056613 1588535 := bstep (se 1 (by rfl) ⟨1191401, by rfl⟩ : syracuseStep 1588535 = 2382803) B2382803
theorem B1588607 : Blo 1056613 1588607 := bstep (se 1 (by rfl) ⟨1191455, by rfl⟩ : syracuseStep 1588607 = 2382911) B2382911
theorem B1588715 : Blo 1056613 1588715 := bstep (se 1 (by rfl) ⟨1191536, by rfl⟩ : syracuseStep 1588715 = 2383073) B2383073
theorem B16301591 : Blo 1056613 16301591 := bstep (se 1 (by rfl) ⟨12226193, by rfl⟩ : syracuseStep 16301591 = 24452387) B24452387
theorem B49626857 : Blo 1056613 49626857 := bstep (se 2 (by rfl) ⟨18610071, by rfl⟩ : syracuseStep 49626857 = 37220143) B37220143
theorem B5423213 : Blo 1056613 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B1589375 : Blo 1056613 1589375 := bstep (se 1 (by rfl) ⟨1192031, by rfl⟩ : syracuseStep 1589375 = 2384063) B2384063
theorem B1786063 : Blo 1056613 1786063 := bstep (se 1 (by rfl) ⟨1339547, by rfl⟩ : syracuseStep 1786063 = 2679095) B2679095
theorem B1589927 : Blo 1056613 1589927 := bstep (se 1 (by rfl) ⟨1192445, by rfl⟩ : syracuseStep 1589927 = 2384891) B2384891
theorem B1589999 : Blo 1056613 1589999 := bstep (se 1 (by rfl) ⟨1192499, by rfl⟩ : syracuseStep 1589999 = 2384999) B2384999
theorem B1590047 : Blo 1056613 1590047 := bstep (se 1 (by rfl) ⟨1192535, by rfl⟩ : syracuseStep 1590047 = 2385071) B2385071
theorem B6440255 : Blo 1056613 6440255 := bstep (se 1 (by rfl) ⟨4830191, by rfl⟩ : syracuseStep 6440255 = 9660383) B9660383
theorem B2377385 : Blo 1056613 2377385 := bstep (se 2 (by rfl) ⟨891519, by rfl⟩ : syracuseStep 2377385 = 1783039) B1783039
theorem B9029303 : Blo 1056613 9029303 := bstep (se 1 (by rfl) ⟨6771977, by rfl⟩ : syracuseStep 9029303 = 13543955) B13543955
theorem B8046701 : Blo 1056613 8046701 := bstep (se 3 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 8046701 = 3017513) B3017513
theorem B1788041 : Blo 1056613 1788041 := bstep (se 2 (by rfl) ⟨670515, by rfl⟩ : syracuseStep 1788041 = 1341031) B1341031
theorem B2934971 : Blo 1056613 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B2378015 : Blo 1056613 2378015 := bstep (se 1 (by rfl) ⟨1783511, by rfl⟩ : syracuseStep 2378015 = 3567023) B3567023
theorem B4016425 : Blo 1056613 4016425 := bstep (se 2 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 4016425 = 3012319) B3012319
theorem B2378663 : Blo 1056613 2378663 := bstep (se 1 (by rfl) ⟨1783997, by rfl⟩ : syracuseStep 2378663 = 3567995) B3567995
theorem B12078071 : Blo 1056613 12078071 := bstep (se 1 (by rfl) ⟨9058553, by rfl⟩ : syracuseStep 12078071 = 18117107) B18117107
theorem B2378987 : Blo 1056613 2378987 := bstep (se 1 (by rfl) ⟨1784240, by rfl⟩ : syracuseStep 2378987 = 3568481) B3568481
theorem B3722935 : Blo 1056613 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B4017883 : Blo 1056613 4017883 := bstep (se 1 (by rfl) ⟨3013412, by rfl⟩ : syracuseStep 4017883 = 6026825) B6026825
theorem B2379599 : Blo 1056613 2379599 := bstep (se 1 (by rfl) ⟨1784699, by rfl⟩ : syracuseStep 2379599 = 3569399) B3569399
theorem B2379689 : Blo 1056613 2379689 := bstep (se 2 (by rfl) ⟨892383, by rfl⟩ : syracuseStep 2379689 = 1784767) B1784767
theorem B9031763 : Blo 1056613 9031763 := bstep (se 1 (by rfl) ⟨6773822, by rfl⟩ : syracuseStep 9031763 = 13547645) B13547645
theorem B8049131 : Blo 1056613 8049131 := bstep (se 1 (by rfl) ⟨6036848, by rfl⟩ : syracuseStep 8049131 = 12073697) B12073697
theorem B2675207 : Blo 1056613 2675207 := bstep (se 1 (by rfl) ⟨2006405, by rfl⟩ : syracuseStep 2675207 = 4012811) B4012811
theorem B2380319 : Blo 1056613 2380319 := bstep (se 1 (by rfl) ⟨1785239, by rfl⟩ : syracuseStep 2380319 = 3570479) B3570479
theorem B2380553 : Blo 1056613 2380553 := bstep (se 2 (by rfl) ⟨892707, by rfl⟩ : syracuseStep 2380553 = 1785415) B1785415
theorem B2381129 : Blo 1056613 2381129 := bstep (se 2 (by rfl) ⟨892923, by rfl⟩ : syracuseStep 2381129 = 1785847) B1785847
theorem B2676179 : Blo 1056613 2676179 := bstep (se 1 (by rfl) ⟨2007134, by rfl⟩ : syracuseStep 2676179 = 4014269) B4014269
theorem B8050589 : Blo 1056613 8050589 := bstep (se 3 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 8050589 = 3018971) B3018971
theorem B2414623 : Blo 1056613 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B2676847 : Blo 1056613 2676847 := bstep (se 1 (by rfl) ⟨2007635, by rfl⟩ : syracuseStep 2676847 = 4015271) B4015271
theorem B2382497 : Blo 1056613 2382497 := bstep (se 2 (by rfl) ⟨893436, by rfl⟩ : syracuseStep 2382497 = 1786873) B1786873
theorem B2382569 : Blo 1056613 2382569 := bstep (se 2 (by rfl) ⟨893463, by rfl⟩ : syracuseStep 2382569 = 1786927) B1786927
theorem B2382857 : Blo 1056613 2382857 := bstep (se 2 (by rfl) ⟨893571, by rfl⟩ : syracuseStep 2382857 = 1787143) B1787143
theorem B1072159 : Blo 1056613 1072159 := bstep (se 1 (by rfl) ⟨804119, by rfl⟩ : syracuseStep 1072159 = 1608239) B1608239
theorem B4021559 : Blo 1056613 4021559 := bstep (se 1 (by rfl) ⟨3016169, by rfl⟩ : syracuseStep 4021559 = 6032339) B6032339
theorem B2678143 : Blo 1056613 2678143 := bstep (se 1 (by rfl) ⟨2008607, by rfl⟩ : syracuseStep 2678143 = 4017215) B4017215
theorem B2383343 : Blo 1056613 2383343 := bstep (se 1 (by rfl) ⟨1787507, by rfl⟩ : syracuseStep 2383343 = 3575015) B3575015
theorem B4021757 : Blo 1056613 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B2384297 : Blo 1056613 2384297 := bstep (se 2 (by rfl) ⟨894111, by rfl⟩ : syracuseStep 2384297 = 1788223) B1788223
theorem B219832865 : Blo 1056613 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B2385107 : Blo 1056613 2385107 := bstep (se 1 (by rfl) ⟨1788830, by rfl⟩ : syracuseStep 2385107 = 3577661) B3577661
theorem B2680553 : Blo 1056613 2680553 := bstep (se 2 (by rfl) ⟨1005207, by rfl⟩ : syracuseStep 2680553 = 2010415) B2010415
theorem B2385647 : Blo 1056613 2385647 := bstep (se 1 (by rfl) ⟨1789235, by rfl⟩ : syracuseStep 2385647 = 3578471) B3578471
theorem B4024475 : Blo 1056613 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B10316197 : Blo 1056613 10316197 := bstep (se 4 (by rfl) ⟨967143, by rfl⟩ : syracuseStep 10316197 = 1934287) B1934287
theorem B72444619 : Blo 1056613 72444619 := bstep (se 1 (by rfl) ⟨54333464, by rfl⟩ : syracuseStep 72444619 = 108666929) B108666929
theorem B3566375 : Blo 1056613 3566375 := bstep (se 1 (by rfl) ⟨2674781, by rfl⟩ : syracuseStep 3566375 = 5349563) B5349563
theorem B2681657 : Blo 1056613 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B3009631 : Blo 1056613 3009631 := bstep (se 1 (by rfl) ⟨2257223, by rfl⟩ : syracuseStep 3009631 = 4514447) B4514447
theorem B2682031 : Blo 1056613 2682031 := bstep (se 1 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 2682031 = 4023047) B4023047
theorem B9039113 : Blo 1056613 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B3010031 : Blo 1056613 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B2682791 : Blo 1056613 2682791 := bstep (se 1 (by rfl) ⟨2012093, by rfl⟩ : syracuseStep 2682791 = 4024187) B4024187
theorem B3567671 : Blo 1056613 3567671 := bstep (se 1 (by rfl) ⟨2675753, by rfl⟩ : syracuseStep 3567671 = 5351507) B5351507
theorem B4026935 : Blo 1056613 4026935 := bstep (se 1 (by rfl) ⟨3020201, by rfl⟩ : syracuseStep 4026935 = 6040403) B6040403
theorem B4518463 : Blo 1056613 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B3568265 : Blo 1056613 3568265 := bstep (se 2 (by rfl) ⟨1338099, by rfl⟩ : syracuseStep 3568265 = 2676199) B2676199
theorem B4518737 : Blo 1056613 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B6779821 : Blo 1056613 6779821 := bstep (se 3 (by rfl) ⟨1271216, by rfl⟩ : syracuseStep 6779821 = 2542433) B2542433
theorem B2683975 : Blo 1056613 2683975 := bstep (se 1 (by rfl) ⟨2012981, by rfl⟩ : syracuseStep 2683975 = 4025963) B4025963
theorem B3568751 : Blo 1056613 3568751 := bstep (se 1 (by rfl) ⟨2676563, by rfl⟩ : syracuseStep 3568751 = 5353127) B5353127
theorem B4519421 : Blo 1056613 4519421 := bstep (se 3 (by rfl) ⟨847391, by rfl⟩ : syracuseStep 4519421 = 1694783) B1694783
theorem B9042151 : Blo 1056613 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B12876029 : Blo 1056613 12876029 := bstep (se 3 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 12876029 = 4828511) B4828511
theorem B14482691 : Blo 1056613 14482691 := bstep (se 1 (by rfl) ⟨10862018, by rfl⟩ : syracuseStep 14482691 = 21724037) B21724037
theorem B5078351 : Blo 1056613 5078351 := bstep (se 1 (by rfl) ⟨3808763, by rfl⟩ : syracuseStep 5078351 = 7617527) B7617527
theorem B3571127 : Blo 1056613 3571127 := bstep (se 1 (by rfl) ⟨2678345, by rfl⟩ : syracuseStep 3571127 = 5356691) B5356691
theorem B1507663 : Blo 1056613 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B22872725 : Blo 1056613 22872725 := bstep (se 6 (by rfl) ⟨536079, by rfl⟩ : syracuseStep 22872725 = 1072159) B1072159
theorem B4293503 : Blo 1056613 4293503 := bstep (se 1 (by rfl) ⟨3220127, by rfl⟩ : syracuseStep 4293503 = 6440255) B6440255
theorem B10879915 : Blo 1056613 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B16319515 : Blo 1056613 16319515 := bstep (se 1 (by rfl) ⟨12239636, by rfl⟩ : syracuseStep 16319515 = 24479273) B24479273
theorem B1508711 : Blo 1056613 1508711 := bstep (se 1 (by rfl) ⟨1131533, by rfl⟩ : syracuseStep 1508711 = 2263067) B2263067
theorem B3017263 : Blo 1056613 3017263 := bstep (se 1 (by rfl) ⟨2262947, by rfl⟩ : syracuseStep 3017263 = 4525895) B4525895
theorem B4590415 : Blo 1056613 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B3018779 : Blo 1056613 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B3576041 : Blo 1056613 3576041 := bstep (se 2 (by rfl) ⟨1341015, by rfl⟩ : syracuseStep 3576041 = 2682031) B2682031
theorem B20322697 : Blo 1056613 20322697 := bstep (se 2 (by rfl) ⟨7621011, by rfl⟩ : syracuseStep 20322697 = 15242023) B15242023
theorem B40704443 : Blo 1056613 40704443 := bstep (se 1 (by rfl) ⟨30528332, by rfl⟩ : syracuseStep 40704443 = 61056665) B61056665
theorem B3578633 : Blo 1056613 3578633 := bstep (se 2 (by rfl) ⟨1341987, by rfl⟩ : syracuseStep 3578633 = 2683975) B2683975
theorem B2006687 : Blo 1056613 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B6790841 : Blo 1056613 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B3219497 : Blo 1056613 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B1057095 : Blo 1056613 1057095 := bstep (se 1 (by rfl) ⟨792821, by rfl⟩ : syracuseStep 1057095 = 1585643) B1585643
theorem B1057179 : Blo 1056613 1057179 := bstep (se 1 (by rfl) ⟨792884, by rfl⟩ : syracuseStep 1057179 = 1585769) B1585769
theorem B5350049 : Blo 1056613 5350049 := bstep (se 2 (by rfl) ⟨2006268, by rfl⟩ : syracuseStep 5350049 = 4012537) B4012537
theorem B1057531 : Blo 1056613 1057531 := bstep (se 1 (by rfl) ⟨793148, by rfl⟩ : syracuseStep 1057531 = 1586297) B1586297
theorem B5088041 : Blo 1056613 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B1058047 : Blo 1056613 1058047 := bstep (se 1 (by rfl) ⟨793535, by rfl⟩ : syracuseStep 1058047 = 1587071) B1587071
theorem B1189183 : Blo 1056613 1189183 := bstep (se 1 (by rfl) ⟨891887, by rfl⟩ : syracuseStep 1189183 = 1783775) B1783775
theorem B1058459 : Blo 1056613 1058459 := bstep (se 1 (by rfl) ⟨793844, by rfl⟩ : syracuseStep 1058459 = 1587689) B1587689
theorem B1058671 : Blo 1056613 1058671 := bstep (se 1 (by rfl) ⟨794003, by rfl⟩ : syracuseStep 1058671 = 1588007) B1588007
theorem B1189759 : Blo 1056613 1189759 := bstep (se 1 (by rfl) ⟨892319, by rfl⟩ : syracuseStep 1189759 = 1784639) B1784639
theorem B1058975 : Blo 1056613 1058975 := bstep (se 1 (by rfl) ⟨794231, by rfl⟩ : syracuseStep 1058975 = 1588463) B1588463
theorem B1059023 : Blo 1056613 1059023 := bstep (se 1 (by rfl) ⟨794267, by rfl⟩ : syracuseStep 1059023 = 1588535) B1588535
theorem B3385567 : Blo 1056613 3385567 := bstep (se 1 (by rfl) ⟨2539175, by rfl⟩ : syracuseStep 3385567 = 5078351) B5078351
theorem B1059071 : Blo 1056613 1059071 := bstep (se 1 (by rfl) ⟨794303, by rfl⟩ : syracuseStep 1059071 = 1588607) B1588607
theorem B1059143 : Blo 1056613 1059143 := bstep (se 1 (by rfl) ⟨794357, by rfl⟩ : syracuseStep 1059143 = 1588715) B1588715
theorem B1059583 : Blo 1056613 1059583 := bstep (se 1 (by rfl) ⟨794687, by rfl⟩ : syracuseStep 1059583 = 1589375) B1589375
theorem B14461901 : Blo 1056613 14461901 := bstep (se 3 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 14461901 = 5423213) B5423213
theorem B1059951 : Blo 1056613 1059951 := bstep (se 1 (by rfl) ⟨794963, by rfl⟩ : syracuseStep 1059951 = 1589927) B1589927
theorem B1059999 : Blo 1056613 1059999 := bstep (se 1 (by rfl) ⟨794999, by rfl⟩ : syracuseStep 1059999 = 1589999) B1589999
theorem B1060031 : Blo 1056613 1060031 := bstep (se 1 (by rfl) ⟨795023, by rfl⟩ : syracuseStep 1060031 = 1590047) B1590047
theorem B2010575 : Blo 1056613 2010575 := bstep (se 1 (by rfl) ⟨1507931, by rfl⟩ : syracuseStep 2010575 = 3015863) B3015863
theorem B7253471 : Blo 1056613 7253471 := bstep (se 1 (by rfl) ⟨5440103, by rfl⟩ : syracuseStep 7253471 = 10880207) B10880207
theorem B1584923 : Blo 1056613 1584923 := bstep (se 1 (by rfl) ⟨1188692, by rfl⟩ : syracuseStep 1584923 = 2377385) B2377385
theorem B12070781 : Blo 1056613 12070781 := bstep (se 3 (by rfl) ⟨2263271, by rfl⟩ : syracuseStep 12070781 = 4526543) B4526543
theorem B1192027 : Blo 1056613 1192027 := bstep (se 1 (by rfl) ⟨894020, by rfl⟩ : syracuseStep 1192027 = 1788041) B1788041
theorem B1585289 : Blo 1056613 1585289 := bstep (se 2 (by rfl) ⟨594483, by rfl⟩ : syracuseStep 1585289 = 1188967) B1188967
theorem B1585343 : Blo 1056613 1585343 := bstep (se 1 (by rfl) ⟨1189007, by rfl⟩ : syracuseStep 1585343 = 2378015) B2378015
theorem B2011463 : Blo 1056613 2011463 := bstep (se 1 (by rfl) ⟨1508597, by rfl⟩ : syracuseStep 2011463 = 3017195) B3017195
theorem B1585775 : Blo 1056613 1585775 := bstep (se 1 (by rfl) ⟨1189331, by rfl⟩ : syracuseStep 1585775 = 2378663) B2378663
theorem B31306357 : Blo 1056613 31306357 := bstep (se 5 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 31306357 = 2934971) B2934971
theorem B1585991 : Blo 1056613 1585991 := bstep (se 1 (by rfl) ⟨1189493, by rfl⟩ : syracuseStep 1585991 = 2378987) B2378987
theorem B1586399 : Blo 1056613 1586399 := bstep (se 1 (by rfl) ⟨1189799, by rfl⟩ : syracuseStep 1586399 = 2379599) B2379599
theorem B1586459 : Blo 1056613 1586459 := bstep (se 1 (by rfl) ⟨1189844, by rfl⟩ : syracuseStep 1586459 = 2379689) B2379689
theorem B2012663 : Blo 1056613 2012663 := bstep (se 1 (by rfl) ⟨1509497, by rfl⟩ : syracuseStep 2012663 = 3018995) B3018995
theorem B1783471 : Blo 1056613 1783471 := bstep (se 1 (by rfl) ⟨1337603, by rfl⟩ : syracuseStep 1783471 = 2675207) B2675207
theorem B1586879 : Blo 1056613 1586879 := bstep (se 1 (by rfl) ⟨1190159, by rfl⟩ : syracuseStep 1586879 = 2380319) B2380319
theorem B5355233 : Blo 1056613 5355233 := bstep (se 2 (by rfl) ⟨2008212, by rfl⟩ : syracuseStep 5355233 = 4016425) B4016425
theorem B1587035 : Blo 1056613 1587035 := bstep (se 1 (by rfl) ⟨1190276, by rfl⟩ : syracuseStep 1587035 = 2380553) B2380553
theorem B1587419 : Blo 1056613 1587419 := bstep (se 1 (by rfl) ⟨1190564, by rfl⟩ : syracuseStep 1587419 = 2381129) B2381129
theorem B1784119 : Blo 1056613 1784119 := bstep (se 1 (by rfl) ⟨1338089, by rfl⟩ : syracuseStep 1784119 = 2676179) B2676179
theorem B4012841 : Blo 1056613 4012841 := bstep (se 2 (by rfl) ⟨1504815, by rfl⟩ : syracuseStep 4012841 = 3009631) B3009631
theorem B1588331 : Blo 1056613 1588331 := bstep (se 1 (by rfl) ⟨1191248, by rfl⟩ : syracuseStep 1588331 = 2382497) B2382497
theorem B1588379 : Blo 1056613 1588379 := bstep (se 1 (by rfl) ⟨1191284, by rfl⟩ : syracuseStep 1588379 = 2382569) B2382569
theorem B1588571 : Blo 1056613 1588571 := bstep (se 1 (by rfl) ⟨1191428, by rfl⟩ : syracuseStep 1588571 = 2382857) B2382857
theorem B4963913 : Blo 1056613 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B5357177 : Blo 1056613 5357177 := bstep (se 2 (by rfl) ⟨2008941, by rfl⟩ : syracuseStep 5357177 = 4017883) B4017883
theorem B1588895 : Blo 1056613 1588895 := bstep (se 1 (by rfl) ⟨1191671, by rfl⟩ : syracuseStep 1588895 = 2383343) B2383343
theorem B8044271 : Blo 1056613 8044271 := bstep (se 1 (by rfl) ⟨6033203, by rfl⟩ : syracuseStep 8044271 = 12066407) B12066407
theorem B1589531 : Blo 1056613 1589531 := bstep (se 1 (by rfl) ⟨1192148, by rfl⟩ : syracuseStep 1589531 = 2384297) B2384297
theorem B146555243 : Blo 1056613 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B1589897 : Blo 1056613 1589897 := bstep (se 2 (by rfl) ⟨596211, by rfl⟩ : syracuseStep 1589897 = 1192423) B1192423
theorem B5096189 : Blo 1056613 5096189 := bstep (se 3 (by rfl) ⟨955535, by rfl⟩ : syracuseStep 5096189 = 1911071) B1911071
theorem B1590071 : Blo 1056613 1590071 := bstep (se 1 (by rfl) ⟨1192553, by rfl⟩ : syracuseStep 1590071 = 2385107) B2385107
theorem B1787035 : Blo 1056613 1787035 := bstep (se 1 (by rfl) ⟨1340276, by rfl⟩ : syracuseStep 1787035 = 2680553) B2680553
theorem B1590431 : Blo 1056613 1590431 := bstep (se 1 (by rfl) ⟨1192823, by rfl⟩ : syracuseStep 1590431 = 2385647) B2385647
theorem B1590569 : Blo 1056613 1590569 := bstep (se 2 (by rfl) ⟨596463, by rfl⟩ : syracuseStep 1590569 = 1192927) B1192927
theorem B32622011 : Blo 1056613 32622011 := bstep (se 1 (by rfl) ⟨24466508, by rfl⟩ : syracuseStep 32622011 = 48933017) B48933017
theorem B2377583 : Blo 1056613 2377583 := bstep (se 1 (by rfl) ⟨1783187, by rfl⟩ : syracuseStep 2377583 = 3566375) B3566375
theorem B1787771 : Blo 1056613 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B5359607 : Blo 1056613 5359607 := bstep (se 1 (by rfl) ⟨4019705, by rfl⟩ : syracuseStep 5359607 = 8039411) B8039411
theorem B1788527 : Blo 1056613 1788527 := bstep (se 1 (by rfl) ⟨1341395, by rfl⟩ : syracuseStep 1788527 = 2682791) B2682791
theorem B2378447 : Blo 1056613 2378447 := bstep (se 1 (by rfl) ⟨1783835, by rfl⟩ : syracuseStep 2378447 = 3567671) B3567671
theorem B14470163 : Blo 1056613 14470163 := bstep (se 1 (by rfl) ⟨10852622, by rfl⟩ : syracuseStep 14470163 = 21705245) B21705245
theorem B8047673 : Blo 1056613 8047673 := bstep (se 2 (by rfl) ⟨3017877, by rfl⟩ : syracuseStep 8047673 = 6035755) B6035755
theorem B2378843 : Blo 1056613 2378843 := bstep (se 1 (by rfl) ⟨1784132, by rfl⟩ : syracuseStep 2378843 = 3568265) B3568265
theorem B2379167 : Blo 1056613 2379167 := bstep (se 1 (by rfl) ⟨1784375, by rfl⟩ : syracuseStep 2379167 = 3568751) B3568751
theorem B23842835 : Blo 1056613 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B3395819 : Blo 1056613 3395819 := bstep (se 1 (by rfl) ⟨2546864, by rfl⟩ : syracuseStep 3395819 = 5093729) B5093729
theorem B15454799 : Blo 1056613 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B9655127 : Blo 1056613 9655127 := bstep (se 1 (by rfl) ⟨7241345, by rfl⟩ : syracuseStep 9655127 = 14482691) B14482691
theorem B2380751 : Blo 1056613 2380751 := bstep (se 1 (by rfl) ⟨1785563, by rfl⟩ : syracuseStep 2380751 = 3571127) B3571127
theorem B10867727 : Blo 1056613 10867727 := bstep (se 1 (by rfl) ⟨8150795, by rfl⟩ : syracuseStep 10867727 = 16301591) B16301591
theorem B33084571 : Blo 1056613 33084571 := bstep (se 1 (by rfl) ⟨24813428, by rfl⟩ : syracuseStep 33084571 = 49626857) B49626857
theorem B6018533 : Blo 1056613 6018533 := bstep (se 4 (by rfl) ⟨564237, by rfl⟩ : syracuseStep 6018533 = 1128475) B1128475
theorem B2381417 : Blo 1056613 2381417 := bstep (se 2 (by rfl) ⟨893031, by rfl⟩ : syracuseStep 2381417 = 1786063) B1786063
theorem B12080987 : Blo 1056613 12080987 := bstep (se 1 (by rfl) ⟨9060740, by rfl⟩ : syracuseStep 12080987 = 18121481) B18121481
theorem B2381723 : Blo 1056613 2381723 := bstep (se 1 (by rfl) ⟨1786292, by rfl⟩ : syracuseStep 2381723 = 3572585) B3572585
theorem B6019535 : Blo 1056613 6019535 := bstep (se 1 (by rfl) ⟨4514651, by rfl⟩ : syracuseStep 6019535 = 9029303) B9029303
theorem B11426507 : Blo 1056613 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B5364467 : Blo 1056613 5364467 := bstep (se 1 (by rfl) ⟨4023350, by rfl⟩ : syracuseStep 5364467 = 8046701) B8046701
theorem B2382875 : Blo 1056613 2382875 := bstep (se 1 (by rfl) ⟨1787156, by rfl⟩ : syracuseStep 2382875 = 3574313) B3574313
theorem B8052047 : Blo 1056613 8052047 := bstep (se 1 (by rfl) ⟨6039035, by rfl⟩ : syracuseStep 8052047 = 12078071) B12078071
theorem B2383775 : Blo 1056613 2383775 := bstep (se 1 (by rfl) ⟨1787831, by rfl⟩ : syracuseStep 2383775 = 3575663) B3575663
theorem B6021175 : Blo 1056613 6021175 := bstep (se 1 (by rfl) ⟨4515881, by rfl⟩ : syracuseStep 6021175 = 9031763) B9031763
theorem B5366087 : Blo 1056613 5366087 := bstep (se 1 (by rfl) ⟨4024565, by rfl⟩ : syracuseStep 5366087 = 8049131) B8049131
theorem B13754929 : Blo 1056613 13754929 := bstep (se 2 (by rfl) ⟨5158098, by rfl⟩ : syracuseStep 13754929 = 10316197) B10316197
theorem B46490213 : Blo 1056613 46490213 := bstep (se 4 (by rfl) ⟨4358457, by rfl⟩ : syracuseStep 46490213 = 8716915) B8716915
theorem B96592825 : Blo 1056613 96592825 := bstep (se 2 (by rfl) ⟨36222309, by rfl⟩ : syracuseStep 96592825 = 72444619) B72444619
theorem B5367059 : Blo 1056613 5367059 := bstep (se 1 (by rfl) ⟨4025294, by rfl⟩ : syracuseStep 5367059 = 8050589) B8050589
theorem B8578385 : Blo 1056613 8578385 := bstep (se 2 (by rfl) ⟨3216894, by rfl⟩ : syracuseStep 8578385 = 6433789) B6433789
theorem B9922601 : Blo 1056613 9922601 := bstep (se 2 (by rfl) ⟨3720975, by rfl⟩ : syracuseStep 9922601 = 7441951) B7441951
theorem B2681039 : Blo 1056613 2681039 := bstep (se 1 (by rfl) ⟨2010779, by rfl⟩ : syracuseStep 2681039 = 4021559) B4021559
theorem B2386151 : Blo 1056613 2386151 := bstep (se 1 (by rfl) ⟨1789613, by rfl⟩ : syracuseStep 2386151 = 3579227) B3579227
theorem B2681171 : Blo 1056613 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B8153783 : Blo 1056613 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B5729129 : Blo 1056613 5729129 := bstep (se 2 (by rfl) ⟨2148423, by rfl⟩ : syracuseStep 5729129 = 4296847) B4296847
theorem B6024617 : Blo 1056613 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B9039761 : Blo 1056613 9039761 := bstep (se 2 (by rfl) ⟨3389910, by rfl⟩ : syracuseStep 9039761 = 6779821) B6779821
theorem B2682983 : Blo 1056613 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B2257463 : Blo 1056613 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B6026075 : Blo 1056613 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B28996703 : Blo 1056613 28996703 := bstep (se 1 (by rfl) ⟨21747527, by rfl⟩ : syracuseStep 28996703 = 43495055) B43495055
theorem B1340651 : Blo 1056613 1340651 := bstep (se 1 (by rfl) ⟨1005488, by rfl⟩ : syracuseStep 1340651 = 2010977) B2010977
theorem B3569129 : Blo 1056613 3569129 := bstep (se 2 (by rfl) ⟨1338423, by rfl⟩ : syracuseStep 3569129 = 2676847) B2676847
theorem B3569183 : Blo 1056613 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B11433595 : Blo 1056613 11433595 := bstep (se 1 (by rfl) ⟨8575196, by rfl⟩ : syracuseStep 11433595 = 17150393) B17150393
theorem B12056201 : Blo 1056613 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B2684623 : Blo 1056613 2684623 := bstep (se 1 (by rfl) ⟨2013467, by rfl⟩ : syracuseStep 2684623 = 4026935) B4026935
theorem B3012491 : Blo 1056613 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B27162539 : Blo 1056613 27162539 := bstep (se 1 (by rfl) ⟨20371904, by rfl⟩ : syracuseStep 27162539 = 40743809) B40743809
theorem B11434031 : Blo 1056613 11434031 := bstep (se 1 (by rfl) ⟨8575523, by rfl⟩ : syracuseStep 11434031 = 17151047) B17151047
theorem B8583241 : Blo 1056613 8583241 := bstep (se 2 (by rfl) ⟨3218715, by rfl⟩ : syracuseStep 8583241 = 6437431) B6437431
theorem B3012947 : Blo 1056613 3012947 := bstep (se 1 (by rfl) ⟨2259710, by rfl⟩ : syracuseStep 3012947 = 4519421) B4519421
theorem B4520393 : Blo 1056613 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B30964517 : Blo 1056613 30964517 := bstep (se 4 (by rfl) ⟨2902923, by rfl⟩ : syracuseStep 30964517 = 5805847) B5805847
theorem B1342271 : Blo 1056613 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B8584019 : Blo 1056613 8584019 := bstep (se 1 (by rfl) ⟨6438014, by rfl⟩ : syracuseStep 8584019 = 12876029) B12876029
theorem B3570857 : Blo 1056613 3570857 := bstep (se 2 (by rfl) ⟨1339071, by rfl⟩ : syracuseStep 3570857 = 2678143) B2678143
theorem B27491563 : Blo 1056613 27491563 := bstep (se 1 (by rfl) ⟨20618672, by rfl⟩ : syracuseStep 27491563 = 41237345) B41237345
theorem B7241015 : Blo 1056613 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B8028233 : Blo 1056613 8028233 := bstep (se 2 (by rfl) ⟨3010587, by rfl⟩ : syracuseStep 8028233 = 6021175) B6021175
theorem B3573071 : Blo 1056613 3573071 := bstep (se 1 (by rfl) ⟨2679803, by rfl⟩ : syracuseStep 3573071 = 5359607) B5359607
theorem B21759353 : Blo 1056613 21759353 := bstep (se 2 (by rfl) ⟨8159757, by rfl⟩ : syracuseStep 21759353 = 16319515) B16319515
theorem B15895223 : Blo 1056613 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B2263879 : Blo 1056613 2263879 := bstep (se 1 (by rfl) ⟨1697909, by rfl⟩ : syracuseStep 2263879 = 3395819) B3395819
theorem B3575069 : Blo 1056613 3575069 := bstep (se 3 (by rfl) ⟨670325, by rfl⟩ : syracuseStep 3575069 = 1340651) B1340651
theorem B27136295 : Blo 1056613 27136295 := bstep (se 1 (by rfl) ⟨20352221, by rfl⟩ : syracuseStep 27136295 = 40704443) B40704443
theorem B24482213 : Blo 1056613 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B3576311 : Blo 1056613 3576311 := bstep (se 1 (by rfl) ⟨2682233, by rfl⟩ : syracuseStep 3576311 = 5364467) B5364467
theorem B4527227 : Blo 1056613 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B3577391 : Blo 1056613 3577391 := bstep (se 1 (by rfl) ⟨2683043, by rfl⟩ : syracuseStep 3577391 = 5366087) B5366087
theorem B3578039 : Blo 1056613 3578039 := bstep (se 1 (by rfl) ⟨2683529, by rfl⟩ : syracuseStep 3578039 = 5367059) B5367059
theorem B44112761 : Blo 1056613 44112761 := bstep (se 2 (by rfl) ⟨16542285, by rfl⟩ : syracuseStep 44112761 = 33084571) B33084571
theorem B9641267 : Blo 1056613 9641267 := bstep (se 1 (by rfl) ⟨7230950, by rfl⟩ : syracuseStep 9641267 = 14461901) B14461901
theorem B15244793 : Blo 1056613 15244793 := bstep (se 2 (by rfl) ⟨5716797, by rfl⟩ : syracuseStep 15244793 = 11433595) B11433595
theorem B3579389 : Blo 1056613 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B3579497 : Blo 1056613 3579497 := bstep (se 2 (by rfl) ⟨1342311, by rfl⟩ : syracuseStep 3579497 = 2684623) B2684623
theorem B1056615 : Blo 1056613 1056615 := bstep (se 1 (by rfl) ⟨792461, by rfl⟩ : syracuseStep 1056615 = 1584923) B1584923
theorem B1056859 : Blo 1056613 1056859 := bstep (se 1 (by rfl) ⟨792644, by rfl⟩ : syracuseStep 1056859 = 1585289) B1585289
theorem B11444321 : Blo 1056613 11444321 := bstep (se 2 (by rfl) ⟨4291620, by rfl⟩ : syracuseStep 11444321 = 8583241) B8583241
theorem B1056895 : Blo 1056613 1056895 := bstep (se 1 (by rfl) ⟨792671, by rfl⟩ : syracuseStep 1056895 = 1585343) B1585343
theorem B1057183 : Blo 1056613 1057183 := bstep (se 1 (by rfl) ⟨792887, by rfl⟩ : syracuseStep 1057183 = 1585775) B1585775
theorem B1057327 : Blo 1056613 1057327 := bstep (se 1 (by rfl) ⟨792995, by rfl⟩ : syracuseStep 1057327 = 1585991) B1585991
theorem B19309373 : Blo 1056613 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B1057599 : Blo 1056613 1057599 := bstep (se 1 (by rfl) ⟨793199, by rfl⟩ : syracuseStep 1057599 = 1586399) B1586399
theorem B1057639 : Blo 1056613 1057639 := bstep (se 1 (by rfl) ⟨793229, by rfl⟩ : syracuseStep 1057639 = 1586459) B1586459
theorem B8037467 : Blo 1056613 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B1057919 : Blo 1056613 1057919 := bstep (se 1 (by rfl) ⟨793439, by rfl⟩ : syracuseStep 1057919 = 1586879) B1586879
theorem B1058023 : Blo 1056613 1058023 := bstep (se 1 (by rfl) ⟨793517, by rfl⟩ : syracuseStep 1058023 = 1587035) B1587035
theorem B2008327 : Blo 1056613 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B1058279 : Blo 1056613 1058279 := bstep (se 1 (by rfl) ⟨793709, by rfl⟩ : syracuseStep 1058279 = 1587419) B1587419
theorem B2008631 : Blo 1056613 2008631 := bstep (se 1 (by rfl) ⟨1506473, by rfl⟩ : syracuseStep 2008631 = 3012947) B3012947
theorem B1058887 : Blo 1056613 1058887 := bstep (se 1 (by rfl) ⟨794165, by rfl⟩ : syracuseStep 1058887 = 1588331) B1588331
theorem B1058919 : Blo 1056613 1058919 := bstep (se 1 (by rfl) ⟨794189, by rfl⟩ : syracuseStep 1058919 = 1588379) B1588379
theorem B1059047 : Blo 1056613 1059047 := bstep (se 1 (by rfl) ⟨794285, by rfl⟩ : syracuseStep 1059047 = 1588571) B1588571
theorem B1059263 : Blo 1056613 1059263 := bstep (se 1 (by rfl) ⟨794447, by rfl⟩ : syracuseStep 1059263 = 1588895) B1588895
theorem B1059687 : Blo 1056613 1059687 := bstep (se 1 (by rfl) ⟨794765, by rfl⟩ : syracuseStep 1059687 = 1589531) B1589531
theorem B1059931 : Blo 1056613 1059931 := bstep (se 1 (by rfl) ⟨794948, by rfl⟩ : syracuseStep 1059931 = 1589897) B1589897
theorem B15248483 : Blo 1056613 15248483 := bstep (se 1 (by rfl) ⟨11436362, by rfl⟩ : syracuseStep 15248483 = 22872725) B22872725
theorem B1060047 : Blo 1056613 1060047 := bstep (se 1 (by rfl) ⟨795035, by rfl⟩ : syracuseStep 1060047 = 1590071) B1590071
theorem B2862335 : Blo 1056613 2862335 := bstep (se 1 (by rfl) ⟨2146751, by rfl⟩ : syracuseStep 2862335 = 4293503) B4293503
theorem B1060287 : Blo 1056613 1060287 := bstep (se 1 (by rfl) ⟨795215, by rfl⟩ : syracuseStep 1060287 = 1590431) B1590431
theorem B1060379 : Blo 1056613 1060379 := bstep (se 1 (by rfl) ⟨795284, by rfl⟩ : syracuseStep 1060379 = 1590569) B1590569
theorem B1585055 : Blo 1056613 1585055 := bstep (se 1 (by rfl) ⟨1188791, by rfl⟩ : syracuseStep 1585055 = 2377583) B2377583
theorem B128790433 : Blo 1056613 128790433 := bstep (se 2 (by rfl) ⟨48296412, by rfl⟩ : syracuseStep 128790433 = 96592825) B96592825
theorem B1191847 : Blo 1056613 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B123973901 : Blo 1056613 123973901 := bstep (se 3 (by rfl) ⟨23245106, by rfl⟩ : syracuseStep 123973901 = 46490213) B46490213
theorem B1192351 : Blo 1056613 1192351 := bstep (se 1 (by rfl) ⟨894263, by rfl⟩ : syracuseStep 1192351 = 1788527) B1788527
theorem B8040869 : Blo 1056613 8040869 := bstep (se 4 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 8040869 = 1507663) B1507663
theorem B1585577 : Blo 1056613 1585577 := bstep (se 2 (by rfl) ⟨594591, by rfl⟩ : syracuseStep 1585577 = 1189183) B1189183
theorem B1585631 : Blo 1056613 1585631 := bstep (se 1 (by rfl) ⟨1189223, by rfl⟩ : syracuseStep 1585631 = 2378447) B2378447
theorem B9646775 : Blo 1056613 9646775 := bstep (se 1 (by rfl) ⟨7235081, by rfl⟩ : syracuseStep 9646775 = 14470163) B14470163
theorem B1585895 : Blo 1056613 1585895 := bstep (se 1 (by rfl) ⟨1189421, by rfl⟩ : syracuseStep 1585895 = 2378843) B2378843
theorem B1586111 : Blo 1056613 1586111 := bstep (se 1 (by rfl) ⟨1189583, by rfl⟩ : syracuseStep 1586111 = 2379167) B2379167
theorem B1586345 : Blo 1056613 1586345 := bstep (se 2 (by rfl) ⟨594879, by rfl⟩ : syracuseStep 1586345 = 1189759) B1189759
theorem B2012519 : Blo 1056613 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B28980605 : Blo 1056613 28980605 := bstep (se 3 (by rfl) ⟨5433863, by rfl⟩ : syracuseStep 28980605 = 10867727) B10867727
theorem B10303199 : Blo 1056613 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B6436751 : Blo 1056613 6436751 := bstep (se 1 (by rfl) ⟨4827563, by rfl⟩ : syracuseStep 6436751 = 9655127) B9655127
theorem B166967237 : Blo 1056613 166967237 := bstep (se 4 (by rfl) ⟨15653178, by rfl⟩ : syracuseStep 166967237 = 31306357) B31306357
theorem B1587167 : Blo 1056613 1587167 := bstep (se 1 (by rfl) ⟨1190375, by rfl⟩ : syracuseStep 1587167 = 2380751) B2380751
theorem B4012355 : Blo 1056613 4012355 := bstep (se 1 (by rfl) ⟨3009266, by rfl⟩ : syracuseStep 4012355 = 6018533) B6018533
theorem B1587611 : Blo 1056613 1587611 := bstep (se 1 (by rfl) ⟨1190708, by rfl⟩ : syracuseStep 1587611 = 2381417) B2381417
theorem B1587815 : Blo 1056613 1587815 := bstep (se 1 (by rfl) ⟨1190861, by rfl⟩ : syracuseStep 1587815 = 2381723) B2381723
theorem B4013023 : Blo 1056613 4013023 := bstep (se 1 (by rfl) ⟨3009767, by rfl⟩ : syracuseStep 4013023 = 6019535) B6019535
theorem B7617671 : Blo 1056613 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B1588583 : Blo 1056613 1588583 := bstep (se 1 (by rfl) ⟨1191437, by rfl⟩ : syracuseStep 1588583 = 2382875) B2382875
theorem B1589183 : Blo 1056613 1589183 := bstep (se 1 (by rfl) ⟨1191887, by rfl⟩ : syracuseStep 1589183 = 2383775) B2383775
theorem B2146331 : Blo 1056613 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B1589369 : Blo 1056613 1589369 := bstep (se 2 (by rfl) ⟨596013, by rfl⟩ : syracuseStep 1589369 = 1192027) B1192027
theorem B3392027 : Blo 1056613 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B5718923 : Blo 1056613 5718923 := bstep (se 1 (by rfl) ⟨4289192, by rfl⟩ : syracuseStep 5718923 = 8578385) B8578385
theorem B1787359 : Blo 1056613 1787359 := bstep (se 1 (by rfl) ⟨1340519, by rfl⟩ : syracuseStep 1787359 = 2681039) B2681039
theorem B1590767 : Blo 1056613 1590767 := bstep (se 1 (by rfl) ⟨1193075, by rfl⟩ : syracuseStep 1590767 = 2386151) B2386151
theorem B1787447 : Blo 1056613 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B3819419 : Blo 1056613 3819419 := bstep (se 1 (by rfl) ⟨2864564, by rfl⟩ : syracuseStep 3819419 = 5729129) B5729129
theorem B2377961 : Blo 1056613 2377961 := bstep (se 2 (by rfl) ⟨891735, by rfl⟩ : syracuseStep 2377961 = 1783471) B1783471
theorem B4016411 : Blo 1056613 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B4835647 : Blo 1056613 4835647 := bstep (se 1 (by rfl) ⟨3626735, by rfl⟩ : syracuseStep 4835647 = 7253471) B7253471
theorem B8047187 : Blo 1056613 8047187 := bstep (se 1 (by rfl) ⟨6035390, by rfl⟩ : syracuseStep 8047187 = 12070781) B12070781
theorem B1788655 : Blo 1056613 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B2378825 : Blo 1056613 2378825 := bstep (se 2 (by rfl) ⟨892059, by rfl⟩ : syracuseStep 2378825 = 1784119) B1784119
theorem B4017383 : Blo 1056613 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B2379419 : Blo 1056613 2379419 := bstep (se 1 (by rfl) ⟨1784564, by rfl⟩ : syracuseStep 2379419 = 3569129) B3569129
theorem B2379455 : Blo 1056613 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B18108359 : Blo 1056613 18108359 := bstep (se 1 (by rfl) ⟨13581269, by rfl⟩ : syracuseStep 18108359 = 27162539) B27162539
theorem B7622687 : Blo 1056613 7622687 := bstep (se 1 (by rfl) ⟨5717015, by rfl⟩ : syracuseStep 7622687 = 11434031) B11434031
theorem B36655417 : Blo 1056613 36655417 := bstep (se 2 (by rfl) ⟨13745781, by rfl⟩ : syracuseStep 36655417 = 27491563) B27491563
theorem B2675227 : Blo 1056613 2675227 := bstep (se 1 (by rfl) ⟨2006420, by rfl⟩ : syracuseStep 2675227 = 4012841) B4012841
theorem B5722679 : Blo 1056613 5722679 := bstep (se 1 (by rfl) ⟨4292009, by rfl⟩ : syracuseStep 5722679 = 8584019) B8584019
theorem B2380571 : Blo 1056613 2380571 := bstep (se 1 (by rfl) ⟨1785428, by rfl⟩ : syracuseStep 2380571 = 3570857) B3570857
theorem B5362847 : Blo 1056613 5362847 := bstep (se 1 (by rfl) ⟨4022135, by rfl⟩ : syracuseStep 5362847 = 8044271) B8044271
theorem B97703495 : Blo 1056613 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B3397459 : Blo 1056613 3397459 := bstep (se 1 (by rfl) ⟨2548094, by rfl⟩ : syracuseStep 3397459 = 5096189) B5096189
theorem B18339905 : Blo 1056613 18339905 := bstep (se 2 (by rfl) ⟨6877464, by rfl⟩ : syracuseStep 18339905 = 13754929) B13754929
theorem B21748007 : Blo 1056613 21748007 := bstep (se 1 (by rfl) ⟨16311005, by rfl⟩ : syracuseStep 21748007 = 32622011) B32622011
theorem B14506553 : Blo 1056613 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B2382713 : Blo 1056613 2382713 := bstep (se 2 (by rfl) ⟨893517, by rfl⟩ : syracuseStep 2382713 = 1787035) B1787035
theorem B5365115 : Blo 1056613 5365115 := bstep (se 1 (by rfl) ⟨4023836, by rfl⟩ : syracuseStep 5365115 = 8047673) B8047673
theorem B2384027 : Blo 1056613 2384027 := bstep (se 1 (by rfl) ⟨1788020, by rfl⟩ : syracuseStep 2384027 = 3576041) B3576041
theorem B4514089 : Blo 1056613 4514089 := bstep (se 2 (by rfl) ⟨1692783, by rfl⟩ : syracuseStep 4514089 = 3385567) B3385567
theorem B4023017 : Blo 1056613 4023017 := bstep (se 2 (by rfl) ⟨1508631, by rfl⟩ : syracuseStep 4023017 = 3017263) B3017263
theorem B4023229 : Blo 1056613 4023229 := bstep (se 3 (by rfl) ⟨754355, by rfl⟩ : syracuseStep 4023229 = 1508711) B1508711
theorem B8053991 : Blo 1056613 8053991 := bstep (se 1 (by rfl) ⟨6040493, by rfl⟩ : syracuseStep 8053991 = 12080987) B12080987
theorem B2385755 : Blo 1056613 2385755 := bstep (se 1 (by rfl) ⟨1789316, by rfl⟩ : syracuseStep 2385755 = 3578633) B3578633
theorem B5368031 : Blo 1056613 5368031 := bstep (se 1 (by rfl) ⟨4026023, by rfl⟩ : syracuseStep 5368031 = 8052047) B8052047
theorem B1337791 : Blo 1056613 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B3566699 : Blo 1056613 3566699 := bstep (se 1 (by rfl) ⟨2675024, by rfl⟩ : syracuseStep 3566699 = 5350049) B5350049
theorem B6615067 : Blo 1056613 6615067 := bstep (se 1 (by rfl) ⟨4961300, by rfl⟩ : syracuseStep 6615067 = 9922601) B9922601
theorem B5435855 : Blo 1056613 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B1340383 : Blo 1056613 1340383 := bstep (se 1 (by rfl) ⟨1005287, by rfl⟩ : syracuseStep 1340383 = 2010575) B2010575
theorem B6026507 : Blo 1056613 6026507 := bstep (se 1 (by rfl) ⟨4519880, by rfl⟩ : syracuseStep 6026507 = 9039761) B9039761
theorem B1340975 : Blo 1056613 1340975 := bstep (se 1 (by rfl) ⟨1005731, by rfl⟩ : syracuseStep 1340975 = 2011463) B2011463
theorem B1504975 : Blo 1056613 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B27096929 : Blo 1056613 27096929 := bstep (se 2 (by rfl) ⟨10161348, by rfl⟩ : syracuseStep 27096929 = 20322697) B20322697
theorem B19331135 : Blo 1056613 19331135 := bstep (se 1 (by rfl) ⟨14498351, by rfl⟩ : syracuseStep 19331135 = 28996703) B28996703
theorem B1341775 : Blo 1056613 1341775 := bstep (se 1 (by rfl) ⟨1006331, by rfl⟩ : syracuseStep 1341775 = 2012663) B2012663
theorem B3570155 : Blo 1056613 3570155 := bstep (se 1 (by rfl) ⟨2677616, by rfl⟩ : syracuseStep 3570155 = 5355233) B5355233
theorem B3013595 : Blo 1056613 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B20643011 : Blo 1056613 20643011 := bstep (se 1 (by rfl) ⟨15482258, by rfl⟩ : syracuseStep 20643011 = 30964517) B30964517
theorem B3309275 : Blo 1056613 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B3571451 : Blo 1056613 3571451 := bstep (se 1 (by rfl) ⟨2678588, by rfl⟩ : syracuseStep 3571451 = 5357177) B5357177
theorem B2261351 : Blo 1056613 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B5081791 : Blo 1056613 5081791 := bstep (se 1 (by rfl) ⟨3811343, by rfl⟩ : syracuseStep 5081791 = 7622687) B7622687
theorem B18090863 : Blo 1056613 18090863 := bstep (se 1 (by rfl) ⟨13568147, by rfl⟩ : syracuseStep 18090863 = 27136295) B27136295
theorem B16321475 : Blo 1056613 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B3018151 : Blo 1056613 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B3575231 : Blo 1056613 3575231 := bstep (se 1 (by rfl) ⟨2681423, by rfl⟩ : syracuseStep 3575231 = 5362847) B5362847
theorem B3018505 : Blo 1056613 3018505 := bstep (se 2 (by rfl) ⟨1131939, by rfl⟩ : syracuseStep 3018505 = 2263879) B2263879
theorem B3575933 : Blo 1056613 3575933 := bstep (se 3 (by rfl) ⟨670487, by rfl⟩ : syracuseStep 3575933 = 1340975) B1340975
theorem B9671035 : Blo 1056613 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B6427511 : Blo 1056613 6427511 := bstep (se 1 (by rfl) ⟨4820633, by rfl⟩ : syracuseStep 6427511 = 9641267) B9641267
theorem B3576743 : Blo 1056613 3576743 := bstep (se 1 (by rfl) ⟨2682557, by rfl⟩ : syracuseStep 3576743 = 5365115) B5365115
theorem B10163195 : Blo 1056613 10163195 := bstep (se 1 (by rfl) ⟨7622396, by rfl⟩ : syracuseStep 10163195 = 15244793) B15244793
theorem B8820089 : Blo 1056613 8820089 := bstep (se 2 (by rfl) ⟨3307533, by rfl⟩ : syracuseStep 8820089 = 6615067) B6615067
theorem B3578687 : Blo 1056613 3578687 := bstep (se 1 (by rfl) ⟨2684015, by rfl⟩ : syracuseStep 3578687 = 5368031) B5368031
theorem B10165655 : Blo 1056613 10165655 := bstep (se 1 (by rfl) ⟨7624241, by rfl⟩ : syracuseStep 10165655 = 15248483) B15248483
theorem B2006633 : Blo 1056613 2006633 := bstep (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) B1504975
theorem B4529945 : Blo 1056613 4529945 := bstep (se 2 (by rfl) ⟨1698729, by rfl⟩ : syracuseStep 4529945 = 3397459) B3397459
theorem B1056703 : Blo 1056613 1056703 := bstep (se 1 (by rfl) ⟨792527, by rfl⟩ : syracuseStep 1056703 = 1585055) B1585055
theorem B82649267 : Blo 1056613 82649267 := bstep (se 1 (by rfl) ⟨61986950, by rfl⟩ : syracuseStep 82649267 = 123973901) B123973901
theorem B1057051 : Blo 1056613 1057051 := bstep (se 1 (by rfl) ⟨792788, by rfl⟩ : syracuseStep 1057051 = 1585577) B1585577
theorem B1057087 : Blo 1056613 1057087 := bstep (se 1 (by rfl) ⟨792815, by rfl⟩ : syracuseStep 1057087 = 1585631) B1585631
theorem B6431183 : Blo 1056613 6431183 := bstep (se 1 (by rfl) ⟨4823387, by rfl⟩ : syracuseStep 6431183 = 9646775) B9646775
theorem B1057263 : Blo 1056613 1057263 := bstep (se 1 (by rfl) ⟨792947, by rfl⟩ : syracuseStep 1057263 = 1585895) B1585895
theorem B1057407 : Blo 1056613 1057407 := bstep (se 1 (by rfl) ⟨793055, by rfl⟩ : syracuseStep 1057407 = 1586111) B1586111
theorem B1057563 : Blo 1056613 1057563 := bstep (se 1 (by rfl) ⟨793172, by rfl⟩ : syracuseStep 1057563 = 1586345) B1586345
theorem B18064619 : Blo 1056613 18064619 := bstep (se 1 (by rfl) ⟨13548464, by rfl⟩ : syracuseStep 18064619 = 27096929) B27096929
theorem B5350697 : Blo 1056613 5350697 := bstep (se 2 (by rfl) ⟨2006511, by rfl⟩ : syracuseStep 5350697 = 4013023) B4013023
theorem B1058111 : Blo 1056613 1058111 := bstep (se 1 (by rfl) ⟨793583, by rfl⟩ : syracuseStep 1058111 = 1587167) B1587167
theorem B12887423 : Blo 1056613 12887423 := bstep (se 1 (by rfl) ⟨9665567, by rfl⟩ : syracuseStep 12887423 = 19331135) B19331135
theorem B1058407 : Blo 1056613 1058407 := bstep (se 1 (by rfl) ⟨793805, by rfl⟩ : syracuseStep 1058407 = 1587611) B1587611
theorem B1058543 : Blo 1056613 1058543 := bstep (se 1 (by rfl) ⟨793907, by rfl⟩ : syracuseStep 1058543 = 1587815) B1587815
theorem B8824733 : Blo 1056613 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B2009063 : Blo 1056613 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B1059055 : Blo 1056613 1059055 := bstep (se 1 (by rfl) ⟨794291, by rfl⟩ : syracuseStep 1059055 = 1588583) B1588583
theorem B1059455 : Blo 1056613 1059455 := bstep (se 1 (by rfl) ⟨794591, by rfl⟩ : syracuseStep 1059455 = 1589183) B1589183
theorem B5352155 : Blo 1056613 5352155 := bstep (se 1 (by rfl) ⟨4014116, by rfl⟩ : syracuseStep 5352155 = 8028233) B8028233
theorem B1059579 : Blo 1056613 1059579 := bstep (se 1 (by rfl) ⟨794684, by rfl⟩ : syracuseStep 1059579 = 1589369) B1589369
theorem B3812615 : Blo 1056613 3812615 := bstep (se 1 (by rfl) ⟨2859461, by rfl⟩ : syracuseStep 3812615 = 5718923) B5718923
theorem B1060511 : Blo 1056613 1060511 := bstep (se 1 (by rfl) ⟨795383, by rfl⟩ : syracuseStep 1060511 = 1590767) B1590767
theorem B1191631 : Blo 1056613 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B1585307 : Blo 1056613 1585307 := bstep (se 1 (by rfl) ⟨1188980, by rfl⟩ : syracuseStep 1585307 = 2377961) B2377961
theorem B10596815 : Blo 1056613 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B1585883 : Blo 1056613 1585883 := bstep (se 1 (by rfl) ⟨1189412, by rfl⟩ : syracuseStep 1585883 = 2378825) B2378825
theorem B1586279 : Blo 1056613 1586279 := bstep (se 1 (by rfl) ⟨1189709, by rfl⟩ : syracuseStep 1586279 = 2379419) B2379419
theorem B1586303 : Blo 1056613 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B12072239 : Blo 1056613 12072239 := bstep (se 1 (by rfl) ⟨9054179, by rfl⟩ : syracuseStep 12072239 = 18108359) B18108359
theorem B3815119 : Blo 1056613 3815119 := bstep (se 1 (by rfl) ⟨2861339, by rfl⟩ : syracuseStep 3815119 = 5722679) B5722679
theorem B1587047 : Blo 1056613 1587047 := bstep (se 1 (by rfl) ⟨1190285, by rfl⟩ : syracuseStep 1587047 = 2380571) B2380571
theorem B1783721 : Blo 1056613 1783721 := bstep (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) B1337791
theorem B14498671 : Blo 1056613 14498671 := bstep (se 1 (by rfl) ⟨10874003, by rfl⟩ : syracuseStep 14498671 = 21748007) B21748007
theorem B1588475 : Blo 1056613 1588475 := bstep (se 1 (by rfl) ⟨1191356, by rfl⟩ : syracuseStep 1588475 = 2382713) B2382713
theorem B29408507 : Blo 1056613 29408507 := bstep (se 1 (by rfl) ⟨22056380, by rfl⟩ : syracuseStep 29408507 = 44112761) B44112761
theorem B171720577 : Blo 1056613 171720577 := bstep (se 2 (by rfl) ⟨64395216, by rfl⟩ : syracuseStep 171720577 = 128790433) B128790433
theorem B1589129 : Blo 1056613 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B1589351 : Blo 1056613 1589351 := bstep (se 1 (by rfl) ⟨1192013, by rfl⟩ : syracuseStep 1589351 = 2384027) B2384027
theorem B48906413 : Blo 1056613 48906413 := bstep (se 3 (by rfl) ⟨9169952, by rfl⟩ : syracuseStep 48906413 = 18339905) B18339905
theorem B48873889 : Blo 1056613 48873889 := bstep (se 2 (by rfl) ⟨18327708, by rfl⟩ : syracuseStep 48873889 = 36655417) B36655417
theorem B1589801 : Blo 1056613 1589801 := bstep (se 2 (by rfl) ⟨596175, by rfl⟩ : syracuseStep 1589801 = 1192351) B1192351
theorem B5358311 : Blo 1056613 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B1590503 : Blo 1056613 1590503 := bstep (se 1 (by rfl) ⟨1192877, by rfl⟩ : syracuseStep 1590503 = 2385755) B2385755
theorem B1787177 : Blo 1056613 1787177 := bstep (se 2 (by rfl) ⟨670191, by rfl⟩ : syracuseStep 1787177 = 1340383) B1340383
theorem B2377799 : Blo 1056613 2377799 := bstep (se 1 (by rfl) ⟨1783349, by rfl⟩ : syracuseStep 2377799 = 3566699) B3566699
theorem B5360579 : Blo 1056613 5360579 := bstep (se 1 (by rfl) ⟨4020434, by rfl⟩ : syracuseStep 5360579 = 8040869) B8040869
theorem B3623903 : Blo 1056613 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B1789033 : Blo 1056613 1789033 := bstep (se 2 (by rfl) ⟨670887, by rfl⟩ : syracuseStep 1789033 = 1341775) B1341775
theorem B4017671 : Blo 1056613 4017671 := bstep (se 1 (by rfl) ⟨3013253, by rfl⟩ : syracuseStep 4017671 = 6026507) B6026507
theorem B19320403 : Blo 1056613 19320403 := bstep (se 1 (by rfl) ⟨14490302, by rfl⟩ : syracuseStep 19320403 = 28980605) B28980605
theorem B6868799 : Blo 1056613 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B2674903 : Blo 1056613 2674903 := bstep (se 1 (by rfl) ⟨2006177, by rfl⟩ : syracuseStep 2674903 = 4012355) B4012355
theorem B2380103 : Blo 1056613 2380103 := bstep (se 1 (by rfl) ⟨1785077, by rfl⟩ : syracuseStep 2380103 = 3570155) B3570155
theorem B2380967 : Blo 1056613 2380967 := bstep (se 1 (by rfl) ⟨1785725, by rfl⟩ : syracuseStep 2380967 = 3571451) B3571451
theorem B1430887 : Blo 1056613 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B6018785 : Blo 1056613 6018785 := bstep (se 2 (by rfl) ⟨2257044, by rfl⟩ : syracuseStep 6018785 = 4514089) B4514089
theorem B2382047 : Blo 1056613 2382047 := bstep (se 1 (by rfl) ⟨1786535, by rfl⟩ : syracuseStep 2382047 = 3573071) B3573071
theorem B14506235 : Blo 1056613 14506235 := bstep (se 1 (by rfl) ⟨10879676, by rfl⟩ : syracuseStep 14506235 = 21759353) B21759353
theorem B5364305 : Blo 1056613 5364305 := bstep (se 2 (by rfl) ⟨2011614, by rfl⟩ : syracuseStep 5364305 = 4023229) B4023229
theorem B2546279 : Blo 1056613 2546279 := bstep (se 1 (by rfl) ⟨1909709, by rfl⟩ : syracuseStep 2546279 = 3819419) B3819419
theorem B2677607 : Blo 1056613 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B2677769 : Blo 1056613 2677769 := bstep (se 2 (by rfl) ⟨1004163, by rfl⟩ : syracuseStep 2677769 = 2008327) B2008327
theorem B5364791 : Blo 1056613 5364791 := bstep (se 1 (by rfl) ⟨4023593, by rfl⟩ : syracuseStep 5364791 = 8047187) B8047187
theorem B2383145 : Blo 1056613 2383145 := bstep (se 2 (by rfl) ⟨893679, by rfl⟩ : syracuseStep 2383145 = 1787359) B1787359
theorem B2678255 : Blo 1056613 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B2383379 : Blo 1056613 2383379 := bstep (se 1 (by rfl) ⟨1787534, by rfl⟩ : syracuseStep 2383379 = 3575069) B3575069
theorem B2384207 : Blo 1056613 2384207 := bstep (se 1 (by rfl) ⟨1788155, by rfl⟩ : syracuseStep 2384207 = 3576311) B3576311
theorem B6447529 : Blo 1056613 6447529 := bstep (se 2 (by rfl) ⟨2417823, by rfl⟩ : syracuseStep 6447529 = 4835647) B4835647
theorem B2384873 : Blo 1056613 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B2384927 : Blo 1056613 2384927 := bstep (se 1 (by rfl) ⟨1788695, by rfl⟩ : syracuseStep 2384927 = 3577391) B3577391
theorem B65135663 : Blo 1056613 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B2385359 : Blo 1056613 2385359 := bstep (se 1 (by rfl) ⟨1789019, by rfl⟩ : syracuseStep 2385359 = 3578039) B3578039
theorem B2386259 : Blo 1056613 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B17164669 : Blo 1056613 17164669 := bstep (se 3 (by rfl) ⟨3218375, by rfl⟩ : syracuseStep 17164669 = 6436751) B6436751
theorem B2386331 : Blo 1056613 2386331 := bstep (se 1 (by rfl) ⟨1789748, by rfl⟩ : syracuseStep 2386331 = 3579497) B3579497
theorem B445245965 : Blo 1056613 445245965 := bstep (se 3 (by rfl) ⟨83483618, by rfl⟩ : syracuseStep 445245965 = 166967237) B166967237
theorem B7629547 : Blo 1056613 7629547 := bstep (se 1 (by rfl) ⟨5722160, by rfl⟩ : syracuseStep 7629547 = 11444321) B11444321
theorem B2682011 : Blo 1056613 2682011 := bstep (se 1 (by rfl) ⟨2011508, by rfl⟩ : syracuseStep 2682011 = 4023017) B4023017
theorem B12872915 : Blo 1056613 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B3566969 : Blo 1056613 3566969 := bstep (se 2 (by rfl) ⟨1337613, by rfl⟩ : syracuseStep 3566969 = 2675227) B2675227
theorem B5369327 : Blo 1056613 5369327 := bstep (se 1 (by rfl) ⟨4026995, by rfl⟩ : syracuseStep 5369327 = 8053991) B8053991
theorem B1339087 : Blo 1056613 1339087 := bstep (se 1 (by rfl) ⟨1004315, by rfl⟩ : syracuseStep 1339087 = 2008631) B2008631
theorem B7632893 : Blo 1056613 7632893 := bstep (se 3 (by rfl) ⟨1431167, by rfl⟩ : syracuseStep 7632893 = 2862335) B2862335
theorem B1341679 : Blo 1056613 1341679 := bstep (se 1 (by rfl) ⟨1006259, by rfl⟩ : syracuseStep 1341679 = 2012519) B2012519
theorem B5078447 : Blo 1056613 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B13762007 : Blo 1056613 13762007 := bstep (se 1 (by rfl) ⟨10321505, by rfl⟩ : syracuseStep 13762007 = 20643011) B20643011
theorem B32604275 : Blo 1056613 32604275 := bstep (se 1 (by rfl) ⟨24453206, by rfl⟩ : syracuseStep 32604275 = 48906413) B48906413
theorem B1507567 : Blo 1056613 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B3572207 : Blo 1056613 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B12060575 : Blo 1056613 12060575 := bstep (se 1 (by rfl) ⟨9045431, by rfl⟩ : syracuseStep 12060575 = 18090863) B18090863
theorem B3573719 : Blo 1056613 3573719 := bstep (se 1 (by rfl) ⟨2680289, by rfl⟩ : syracuseStep 3573719 = 5360579) B5360579
theorem B10880983 : Blo 1056613 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B9670823 : Blo 1056613 9670823 := bstep (se 1 (by rfl) ⟨7253117, by rfl⟩ : syracuseStep 9670823 = 14506235) B14506235
theorem B3576203 : Blo 1056613 3576203 := bstep (se 1 (by rfl) ⟨2682152, by rfl⟩ : syracuseStep 3576203 = 5364305) B5364305
theorem B3576527 : Blo 1056613 3576527 := bstep (se 1 (by rfl) ⟨2682395, by rfl⟩ : syracuseStep 3576527 = 5364791) B5364791
theorem B25760537 : Blo 1056613 25760537 := bstep (se 2 (by rfl) ⟨9660201, by rfl⟩ : syracuseStep 25760537 = 19320403) B19320403
theorem B3019963 : Blo 1056613 3019963 := bstep (se 1 (by rfl) ⟨2264972, by rfl⟩ : syracuseStep 3019963 = 4529945) B4529945
theorem B43423775 : Blo 1056613 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B8591615 : Blo 1056613 8591615 := bstep (se 1 (by rfl) ⟨6443711, by rfl⟩ : syracuseStep 8591615 = 12887423) B12887423
theorem B1907849 : Blo 1056613 1907849 := bstep (se 2 (by rfl) ⟨715443, by rfl⟩ : syracuseStep 1907849 = 1430887) B1430887
theorem B3579551 : Blo 1056613 3579551 := bstep (se 1 (by rfl) ⟨2684663, by rfl⟩ : syracuseStep 3579551 = 5369327) B5369327
theorem B1056871 : Blo 1056613 1056871 := bstep (se 1 (by rfl) ⟨792653, by rfl⟩ : syracuseStep 1056871 = 1585307) B1585307
theorem B1057255 : Blo 1056613 1057255 := bstep (se 1 (by rfl) ⟨792941, by rfl⟩ : syracuseStep 1057255 = 1585883) B1585883
theorem B1057519 : Blo 1056613 1057519 := bstep (se 1 (by rfl) ⟨793139, by rfl⟩ : syracuseStep 1057519 = 1586279) B1586279
theorem B1057535 : Blo 1056613 1057535 := bstep (se 1 (by rfl) ⟨793151, by rfl⟩ : syracuseStep 1057535 = 1586303) B1586303
theorem B1058031 : Blo 1056613 1058031 := bstep (se 1 (by rfl) ⟨793523, by rfl⟩ : syracuseStep 1058031 = 1587047) B1587047
theorem B1189147 : Blo 1056613 1189147 := bstep (se 1 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 1189147 = 1783721) B1783721
theorem B5088595 : Blo 1056613 5088595 := bstep (se 1 (by rfl) ⟨3816446, by rfl⟩ : syracuseStep 5088595 = 7632893) B7632893
theorem B5351021 : Blo 1056613 5351021 := bstep (se 3 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 5351021 = 2006633) B2006633
theorem B1058983 : Blo 1056613 1058983 := bstep (se 1 (by rfl) ⟨794237, by rfl⟩ : syracuseStep 1058983 = 1588475) B1588475
theorem B19605671 : Blo 1056613 19605671 := bstep (se 1 (by rfl) ⟨14704253, by rfl⟩ : syracuseStep 19605671 = 29408507) B29408507
theorem B3385631 : Blo 1056613 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B228960769 : Blo 1056613 228960769 := bstep (se 2 (by rfl) ⟨85860288, by rfl⟩ : syracuseStep 228960769 = 171720577) B171720577
theorem B1059419 : Blo 1056613 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B1059567 : Blo 1056613 1059567 := bstep (se 1 (by rfl) ⟨794675, by rfl⟩ : syracuseStep 1059567 = 1589351) B1589351
theorem B1059867 : Blo 1056613 1059867 := bstep (se 1 (by rfl) ⟨794900, by rfl⟩ : syracuseStep 1059867 = 1589801) B1589801
theorem B18997161173 : Blo 1056613 18997161173 := bstep (se 7 (by rfl) ⟨222622982, by rfl⟩ : syracuseStep 18997161173 = 445245965) B445245965
theorem B8596705 : Blo 1056613 8596705 := bstep (se 2 (by rfl) ⟨3223764, by rfl⟩ : syracuseStep 8596705 = 6447529) B6447529
theorem B1060335 : Blo 1056613 1060335 := bstep (se 1 (by rfl) ⟨795251, by rfl⟩ : syracuseStep 1060335 = 1590503) B1590503
theorem B1191451 : Blo 1056613 1191451 := bstep (se 1 (by rfl) ⟨893588, by rfl⟩ : syracuseStep 1191451 = 1787177) B1787177
theorem B1585199 : Blo 1056613 1585199 := bstep (se 1 (by rfl) ⟨1188899, by rfl⟩ : syracuseStep 1585199 = 2377799) B2377799
theorem B1586735 : Blo 1056613 1586735 := bstep (se 1 (by rfl) ⟨1190051, by rfl⟩ : syracuseStep 1586735 = 2380103) B2380103
theorem B22886225 : Blo 1056613 22886225 := bstep (se 2 (by rfl) ⟨8582334, by rfl⟩ : syracuseStep 22886225 = 17164669) B17164669
theorem B1587311 : Blo 1056613 1587311 := bstep (se 1 (by rfl) ⟨1190483, by rfl⟩ : syracuseStep 1587311 = 2380967) B2380967
theorem B5880059 : Blo 1056613 5880059 := bstep (se 1 (by rfl) ⟨4410044, by rfl⟩ : syracuseStep 5880059 = 8820089) B8820089
theorem B10172729 : Blo 1056613 10172729 := bstep (se 2 (by rfl) ⟨3814773, by rfl⟩ : syracuseStep 10172729 = 7629547) B7629547
theorem B4012523 : Blo 1056613 4012523 := bstep (se 1 (by rfl) ⟨3009392, by rfl⟩ : syracuseStep 4012523 = 6018785) B6018785
theorem B1588031 : Blo 1056613 1588031 := bstep (se 1 (by rfl) ⟨1191023, by rfl⟩ : syracuseStep 1588031 = 2382047) B2382047
theorem B1785071 : Blo 1056613 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B1785179 : Blo 1056613 1785179 := bstep (se 1 (by rfl) ⟨1338884, by rfl⟩ : syracuseStep 1785179 = 2677769) B2677769
theorem B1588763 : Blo 1056613 1588763 := bstep (se 1 (by rfl) ⟨1191572, by rfl⟩ : syracuseStep 1588763 = 2383145) B2383145
theorem B1785449 : Blo 1056613 1785449 := bstep (se 2 (by rfl) ⟨669543, by rfl⟩ : syracuseStep 1785449 = 1339087) B1339087
theorem B1588841 : Blo 1056613 1588841 := bstep (se 2 (by rfl) ⟨595815, by rfl⟩ : syracuseStep 1588841 = 1191631) B1191631
theorem B1785503 : Blo 1056613 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B1588919 : Blo 1056613 1588919 := bstep (se 1 (by rfl) ⟨1191689, by rfl⟩ : syracuseStep 1588919 = 2383379) B2383379
theorem B5357501 : Blo 1056613 5357501 := bstep (se 3 (by rfl) ⟨1004531, by rfl⟩ : syracuseStep 5357501 = 2009063) B2009063
theorem B55099511 : Blo 1056613 55099511 := bstep (se 1 (by rfl) ⟨41324633, by rfl⟩ : syracuseStep 55099511 = 82649267) B82649267
theorem B1589471 : Blo 1056613 1589471 := bstep (se 1 (by rfl) ⟨1192103, by rfl⟩ : syracuseStep 1589471 = 2384207) B2384207
theorem B12894713 : Blo 1056613 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B1589915 : Blo 1056613 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B1589951 : Blo 1056613 1589951 := bstep (se 1 (by rfl) ⟨1192463, by rfl⟩ : syracuseStep 1589951 = 2384927) B2384927
theorem B12043079 : Blo 1056613 12043079 := bstep (se 1 (by rfl) ⟨9032309, by rfl⟩ : syracuseStep 12043079 = 18064619) B18064619
theorem B1590239 : Blo 1056613 1590239 := bstep (se 1 (by rfl) ⟨1192679, by rfl⟩ : syracuseStep 1590239 = 2385359) B2385359
theorem B5883155 : Blo 1056613 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B1590839 : Blo 1056613 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1590887 : Blo 1056613 1590887 := bstep (se 1 (by rfl) ⟨1193165, by rfl⟩ : syracuseStep 1590887 = 2386331) B2386331
theorem B1788007 : Blo 1056613 1788007 := bstep (se 1 (by rfl) ⟨1341005, by rfl⟩ : syracuseStep 1788007 = 2682011) B2682011
theorem B2541743 : Blo 1056613 2541743 := bstep (se 1 (by rfl) ⟨1906307, by rfl⟩ : syracuseStep 2541743 = 3812615) B3812615
theorem B2377979 : Blo 1056613 2377979 := bstep (se 1 (by rfl) ⟨1783484, by rfl⟩ : syracuseStep 2377979 = 3566969) B3566969
theorem B7064543 : Blo 1056613 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B1788905 : Blo 1056613 1788905 := bstep (se 2 (by rfl) ⟨670839, by rfl⟩ : syracuseStep 1788905 = 1341679) B1341679
theorem B8048159 : Blo 1056613 8048159 := bstep (se 1 (by rfl) ⟨6036119, by rfl⟩ : syracuseStep 8048159 = 12072239) B12072239
theorem B65165185 : Blo 1056613 65165185 := bstep (se 2 (by rfl) ⟨24436944, by rfl⟩ : syracuseStep 65165185 = 48873889) B48873889
theorem B2415935 : Blo 1056613 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B2383487 : Blo 1056613 2383487 := bstep (se 1 (by rfl) ⟨1787615, by rfl⟩ : syracuseStep 2383487 = 3575231) B3575231
theorem B2678447 : Blo 1056613 2678447 := bstep (se 1 (by rfl) ⟨2008835, by rfl⟩ : syracuseStep 2678447 = 4017671) B4017671
theorem B4579199 : Blo 1056613 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2383955 : Blo 1056613 2383955 := bstep (se 1 (by rfl) ⟨1787966, by rfl⟩ : syracuseStep 2383955 = 3575933) B3575933
theorem B4285007 : Blo 1056613 4285007 := bstep (se 1 (by rfl) ⟨3213755, by rfl⟩ : syracuseStep 4285007 = 6427511) B6427511
theorem B2384495 : Blo 1056613 2384495 := bstep (se 1 (by rfl) ⟨1788371, by rfl⟩ : syracuseStep 2384495 = 3576743) B3576743
theorem B6775463 : Blo 1056613 6775463 := bstep (se 1 (by rfl) ⟨5081597, by rfl⟩ : syracuseStep 6775463 = 10163195) B10163195
theorem B6775721 : Blo 1056613 6775721 := bstep (se 2 (by rfl) ⟨2540895, by rfl⟩ : syracuseStep 6775721 = 5081791) B5081791
theorem B2385377 : Blo 1056613 2385377 := bstep (se 2 (by rfl) ⟨894516, by rfl⟩ : syracuseStep 2385377 = 1789033) B1789033
theorem B1697519 : Blo 1056613 1697519 := bstep (se 1 (by rfl) ⟨1273139, by rfl⟩ : syracuseStep 1697519 = 2546279) B2546279
theorem B2385791 : Blo 1056613 2385791 := bstep (se 1 (by rfl) ⟨1789343, by rfl⟩ : syracuseStep 2385791 = 3578687) B3578687
theorem B4024201 : Blo 1056613 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B6777103 : Blo 1056613 6777103 := bstep (se 1 (by rfl) ⟨5082827, by rfl⟩ : syracuseStep 6777103 = 10165655) B10165655
theorem B4024673 : Blo 1056613 4024673 := bstep (se 2 (by rfl) ⟨1509252, by rfl⟩ : syracuseStep 4024673 = 3018505) B3018505
theorem B3566537 : Blo 1056613 3566537 := bstep (se 2 (by rfl) ⟨1337451, by rfl⟩ : syracuseStep 3566537 = 2674903) B2674903
theorem B4287455 : Blo 1056613 4287455 := bstep (se 1 (by rfl) ⟨3215591, by rfl⟩ : syracuseStep 4287455 = 6431183) B6431183
theorem B3567131 : Blo 1056613 3567131 := bstep (se 1 (by rfl) ⟨2675348, by rfl⟩ : syracuseStep 3567131 = 5350697) B5350697
theorem B3568103 : Blo 1056613 3568103 := bstep (se 1 (by rfl) ⟨2676077, by rfl⟩ : syracuseStep 3568103 = 5352155) B5352155
theorem B8581943 : Blo 1056613 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B20347301 : Blo 1056613 20347301 := bstep (se 4 (by rfl) ⟨1907559, by rfl⟩ : syracuseStep 20347301 = 3815119) B3815119
theorem B19331561 : Blo 1056613 19331561 := bstep (se 2 (by rfl) ⟨7249335, by rfl⟩ : syracuseStep 19331561 = 14498671) B14498671
theorem B9174671 : Blo 1056613 9174671 := bstep (se 1 (by rfl) ⟨6881003, by rfl⟩ : syracuseStep 9174671 = 13762007) B13762007
theorem B36733007 : Blo 1056613 36733007 := bstep (se 1 (by rfl) ⟨27549755, by rfl⟩ : syracuseStep 36733007 = 55099511) B55099511
theorem B8028719 : Blo 1056613 8028719 := bstep (se 1 (by rfl) ⟨6021539, by rfl⟩ : syracuseStep 8028719 = 12043079) B12043079
theorem B6784793 : Blo 1056613 6784793 := bstep (se 2 (by rfl) ⟨2544297, by rfl⟩ : syracuseStep 6784793 = 5088595) B5088595
theorem B17173691 : Blo 1056613 17173691 := bstep (se 1 (by rfl) ⟨12880268, by rfl⟩ : syracuseStep 17173691 = 25760537) B25760537
theorem B1610623 : Blo 1056613 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B3052799 : Blo 1056613 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B2856671 : Blo 1056613 2856671 := bstep (se 1 (by rfl) ⟨2142503, by rfl⟩ : syracuseStep 2856671 = 4285007) B4285007
theorem B2858303 : Blo 1056613 2858303 := bstep (se 1 (by rfl) ⟨2143727, by rfl⟩ : syracuseStep 2858303 = 4287455) B4287455
theorem B12664774115 : Blo 1056613 12664774115 := bstep (se 1 (by rfl) ⟨9498580586, by rfl⟩ : syracuseStep 12664774115 = 18997161173) B18997161173
theorem B1056799 : Blo 1056613 1056799 := bstep (se 1 (by rfl) ⟨792599, by rfl⟩ : syracuseStep 1056799 = 1585199) B1585199
theorem B1057823 : Blo 1056613 1057823 := bstep (se 1 (by rfl) ⟨793367, by rfl⟩ : syracuseStep 1057823 = 1586735) B1586735
theorem B1058207 : Blo 1056613 1058207 := bstep (se 1 (by rfl) ⟨793655, by rfl⟩ : syracuseStep 1058207 = 1587311) B1587311
theorem B12887707 : Blo 1056613 12887707 := bstep (se 1 (by rfl) ⟨9665780, by rfl⟩ : syracuseStep 12887707 = 19331561) B19331561
theorem B1058687 : Blo 1056613 1058687 := bstep (se 1 (by rfl) ⟨794015, by rfl⟩ : syracuseStep 1058687 = 1588031) B1588031
theorem B1190047 : Blo 1056613 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B1190119 : Blo 1056613 1190119 := bstep (se 1 (by rfl) ⟨892589, by rfl⟩ : syracuseStep 1190119 = 1785179) B1785179
theorem B1059175 : Blo 1056613 1059175 := bstep (se 1 (by rfl) ⟨794381, by rfl⟩ : syracuseStep 1059175 = 1588763) B1588763
theorem B1190299 : Blo 1056613 1190299 := bstep (se 1 (by rfl) ⟨892724, by rfl⟩ : syracuseStep 1190299 = 1785449) B1785449
theorem B1059227 : Blo 1056613 1059227 := bstep (se 1 (by rfl) ⟨794420, by rfl⟩ : syracuseStep 1059227 = 1588841) B1588841
theorem B1190335 : Blo 1056613 1190335 := bstep (se 1 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 1190335 = 1785503) B1785503
theorem B1059279 : Blo 1056613 1059279 := bstep (se 1 (by rfl) ⟨794459, by rfl⟩ : syracuseStep 1059279 = 1588919) B1588919
theorem B21736183 : Blo 1056613 21736183 := bstep (se 1 (by rfl) ⟨16302137, by rfl⟩ : syracuseStep 21736183 = 32604275) B32604275
theorem B1059647 : Blo 1056613 1059647 := bstep (se 1 (by rfl) ⟨794735, by rfl⟩ : syracuseStep 1059647 = 1589471) B1589471
theorem B2010089 : Blo 1056613 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B8596475 : Blo 1056613 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B1059943 : Blo 1056613 1059943 := bstep (se 1 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 1059943 = 1589915) B1589915
theorem B1059967 : Blo 1056613 1059967 := bstep (se 1 (by rfl) ⟨794975, by rfl⟩ : syracuseStep 1059967 = 1589951) B1589951
theorem B1060159 : Blo 1056613 1060159 := bstep (se 1 (by rfl) ⟨795119, by rfl⟩ : syracuseStep 1060159 = 1590239) B1590239
theorem B1060559 : Blo 1056613 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1060591 : Blo 1056613 1060591 := bstep (se 1 (by rfl) ⟨795443, by rfl⟩ : syracuseStep 1060591 = 1590887) B1590887
theorem B8040383 : Blo 1056613 8040383 := bstep (se 1 (by rfl) ⟨6030287, by rfl⟩ : syracuseStep 8040383 = 12060575) B12060575
theorem B1585319 : Blo 1056613 1585319 := bstep (se 1 (by rfl) ⟨1188989, by rfl⟩ : syracuseStep 1585319 = 2377979) B2377979
theorem B1585529 : Blo 1056613 1585529 := bstep (se 2 (by rfl) ⟨594573, by rfl⟩ : syracuseStep 1585529 = 1189147) B1189147
theorem B1192603 : Blo 1056613 1192603 := bstep (se 1 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 1192603 = 1788905) B1788905
theorem B305281025 : Blo 1056613 305281025 := bstep (se 2 (by rfl) ⟨114480384, by rfl⟩ : syracuseStep 305281025 = 228960769) B228960769
theorem B28949183 : Blo 1056613 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B1588601 : Blo 1056613 1588601 := bstep (se 2 (by rfl) ⟨595725, by rfl⟩ : syracuseStep 1588601 = 1191451) B1191451
theorem B1588991 : Blo 1056613 1588991 := bstep (se 1 (by rfl) ⟨1191743, by rfl⟩ : syracuseStep 1588991 = 2383487) B2383487
theorem B1785631 : Blo 1056613 1785631 := bstep (se 1 (by rfl) ⟨1339223, by rfl⟩ : syracuseStep 1785631 = 2678447) B2678447
theorem B1589303 : Blo 1056613 1589303 := bstep (se 1 (by rfl) ⟨1191977, by rfl⟩ : syracuseStep 1589303 = 2383955) B2383955
theorem B1589663 : Blo 1056613 1589663 := bstep (se 1 (by rfl) ⟨1192247, by rfl⟩ : syracuseStep 1589663 = 2384495) B2384495
theorem B1590251 : Blo 1056613 1590251 := bstep (se 1 (by rfl) ⟨1192688, by rfl⟩ : syracuseStep 1590251 = 2385377) B2385377
theorem B1131679 : Blo 1056613 1131679 := bstep (se 1 (by rfl) ⟨848759, by rfl⟩ : syracuseStep 1131679 = 1697519) B1697519
theorem B1590527 : Blo 1056613 1590527 := bstep (se 1 (by rfl) ⟨1192895, by rfl⟩ : syracuseStep 1590527 = 2385791) B2385791
theorem B2377691 : Blo 1056613 2377691 := bstep (se 1 (by rfl) ⟨1783268, by rfl⟩ : syracuseStep 2377691 = 3566537) B3566537
theorem B2378087 : Blo 1056613 2378087 := bstep (se 1 (by rfl) ⟨1783565, by rfl⟩ : syracuseStep 2378087 = 3567131) B3567131
theorem B86886913 : Blo 1056613 86886913 := bstep (se 2 (by rfl) ⟨32582592, by rfl⟩ : syracuseStep 86886913 = 65165185) B65165185
theorem B2378735 : Blo 1056613 2378735 := bstep (se 1 (by rfl) ⟨1784051, by rfl⟩ : syracuseStep 2378735 = 3568103) B3568103
theorem B5721295 : Blo 1056613 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B15257483 : Blo 1056613 15257483 := bstep (se 1 (by rfl) ⟨11443112, by rfl⟩ : syracuseStep 15257483 = 22886225) B22886225
theorem B3920039 : Blo 1056613 3920039 := bstep (se 1 (by rfl) ⟨2940029, by rfl⟩ : syracuseStep 3920039 = 5880059) B5880059
theorem B2675015 : Blo 1056613 2675015 := bstep (se 1 (by rfl) ⟨2006261, by rfl⟩ : syracuseStep 2675015 = 4012523) B4012523
theorem B6116447 : Blo 1056613 6116447 := bstep (se 1 (by rfl) ⟨4587335, by rfl⟩ : syracuseStep 6116447 = 9174671) B9174671
theorem B2381471 : Blo 1056613 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B3922103 : Blo 1056613 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B2382479 : Blo 1056613 2382479 := bstep (se 1 (by rfl) ⟨1786859, by rfl⟩ : syracuseStep 2382479 = 3573719) B3573719
theorem B1694495 : Blo 1056613 1694495 := bstep (se 1 (by rfl) ⟨1270871, by rfl⟩ : syracuseStep 1694495 = 2541743) B2541743
theorem B5365439 : Blo 1056613 5365439 := bstep (se 1 (by rfl) ⟨4024079, by rfl⟩ : syracuseStep 5365439 = 8048159) B8048159
theorem B5365601 : Blo 1056613 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B6447215 : Blo 1056613 6447215 := bstep (se 1 (by rfl) ⟨4835411, by rfl⟩ : syracuseStep 6447215 = 9670823) B9670823
theorem B2384009 : Blo 1056613 2384009 := bstep (se 2 (by rfl) ⟨894003, by rfl⟩ : syracuseStep 2384009 = 1788007) B1788007
theorem B2384135 : Blo 1056613 2384135 := bstep (se 1 (by rfl) ⟨1788101, by rfl⟩ : syracuseStep 2384135 = 3576203) B3576203
theorem B9036137 : Blo 1056613 9036137 := bstep (se 2 (by rfl) ⟨3388551, by rfl⟩ : syracuseStep 9036137 = 6777103) B6777103
theorem B2384351 : Blo 1056613 2384351 := bstep (se 1 (by rfl) ⟨1788263, by rfl⟩ : syracuseStep 2384351 = 3576527) B3576527
theorem B5727743 : Blo 1056613 5727743 := bstep (se 1 (by rfl) ⟨4295807, by rfl⟩ : syracuseStep 5727743 = 8591615) B8591615
theorem B11462273 : Blo 1056613 11462273 := bstep (se 2 (by rfl) ⟨4298352, by rfl⟩ : syracuseStep 11462273 = 8596705) B8596705
theorem B1271899 : Blo 1056613 1271899 := bstep (se 1 (by rfl) ⟨953924, by rfl⟩ : syracuseStep 1271899 = 1907849) B1907849
theorem B2386367 : Blo 1056613 2386367 := bstep (se 1 (by rfl) ⟨1789775, by rfl⟩ : syracuseStep 2386367 = 3579551) B3579551
theorem B4516975 : Blo 1056613 4516975 := bstep (se 1 (by rfl) ⟨3387731, by rfl⟩ : syracuseStep 4516975 = 6775463) B6775463
theorem B4517147 : Blo 1056613 4517147 := bstep (se 1 (by rfl) ⟨3387860, by rfl⟩ : syracuseStep 4517147 = 6775721) B6775721
theorem B3567347 : Blo 1056613 3567347 := bstep (se 1 (by rfl) ⟨2675510, by rfl⟩ : syracuseStep 3567347 = 5351021) B5351021
theorem B13070447 : Blo 1056613 13070447 := bstep (se 1 (by rfl) ⟨9802835, by rfl⟩ : syracuseStep 13070447 = 19605671) B19605671
theorem B2257087 : Blo 1056613 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B2683115 : Blo 1056613 2683115 := bstep (se 1 (by rfl) ⟨2012336, by rfl⟩ : syracuseStep 2683115 = 4024673) B4024673
theorem B4026617 : Blo 1056613 4026617 := bstep (se 2 (by rfl) ⟨1509981, by rfl⟩ : syracuseStep 4026617 = 3019963) B3019963
theorem B18838781 : Blo 1056613 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B6781819 : Blo 1056613 6781819 := bstep (se 1 (by rfl) ⟨5086364, by rfl⟩ : syracuseStep 6781819 = 10172729) B10172729
theorem B13564867 : Blo 1056613 13564867 := bstep (se 1 (by rfl) ⟨10173650, by rfl⟩ : syracuseStep 13564867 = 20347301) B20347301
theorem B58031909 : Blo 1056613 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B3571667 : Blo 1056613 3571667 := bstep (se 1 (by rfl) ⟨2678750, by rfl⟩ : syracuseStep 3571667 = 5357501) B5357501
theorem B4523195 : Blo 1056613 4523195 := bstep (se 1 (by rfl) ⟨3392396, by rfl⟩ : syracuseStep 4523195 = 6784793) B6784793
theorem B1508905 : Blo 1056613 1508905 := bstep (se 2 (by rfl) ⟨565839, by rfl⟩ : syracuseStep 1508905 = 1131679) B1131679
theorem B2035199 : Blo 1056613 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B1904447 : Blo 1056613 1904447 := bstep (se 1 (by rfl) ⟨1428335, by rfl⟩ : syracuseStep 1904447 = 2856671) B2856671
theorem B8589989 : Blo 1056613 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B1905535 : Blo 1056613 1905535 := bstep (se 1 (by rfl) ⟨1429151, by rfl⟩ : syracuseStep 1905535 = 2858303) B2858303
theorem B3576959 : Blo 1056613 3576959 := bstep (se 1 (by rfl) ⟨2682719, by rfl⟩ : syracuseStep 3576959 = 5365439) B5365439
theorem B3577067 : Blo 1056613 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B4298143 : Blo 1056613 4298143 := bstep (se 1 (by rfl) ⟨3223607, by rfl⟩ : syracuseStep 4298143 = 6447215) B6447215
theorem B7641515 : Blo 1056613 7641515 := bstep (se 1 (by rfl) ⟨5731136, by rfl⟩ : syracuseStep 7641515 = 11462273) B11462273
theorem B1056879 : Blo 1056613 1056879 := bstep (se 1 (by rfl) ⟨792659, by rfl⟩ : syracuseStep 1056879 = 1585319) B1585319
theorem B1057019 : Blo 1056613 1057019 := bstep (se 1 (by rfl) ⟨792764, by rfl⟩ : syracuseStep 1057019 = 1585529) B1585529
theorem B12559187 : Blo 1056613 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B1059067 : Blo 1056613 1059067 := bstep (se 1 (by rfl) ⟨794300, by rfl⟩ : syracuseStep 1059067 = 1588601) B1588601
theorem B1059327 : Blo 1056613 1059327 := bstep (se 1 (by rfl) ⟨794495, by rfl⟩ : syracuseStep 1059327 = 1588991) B1588991
theorem B1059535 : Blo 1056613 1059535 := bstep (se 1 (by rfl) ⟨794651, by rfl⟩ : syracuseStep 1059535 = 1589303) B1589303
theorem B24488671 : Blo 1056613 24488671 := bstep (se 1 (by rfl) ⟨18366503, by rfl⟩ : syracuseStep 24488671 = 36733007) B36733007
theorem B1059775 : Blo 1056613 1059775 := bstep (se 1 (by rfl) ⟨794831, by rfl⟩ : syracuseStep 1059775 = 1589663) B1589663
theorem B5352479 : Blo 1056613 5352479 := bstep (se 1 (by rfl) ⟨4014359, by rfl⟩ : syracuseStep 5352479 = 8028719) B8028719
theorem B1060167 : Blo 1056613 1060167 := bstep (se 1 (by rfl) ⟨795125, by rfl⟩ : syracuseStep 1060167 = 1590251) B1590251
theorem B1060351 : Blo 1056613 1060351 := bstep (se 1 (by rfl) ⟨795263, by rfl⟩ : syracuseStep 1060351 = 1590527) B1590527
theorem B1585127 : Blo 1056613 1585127 := bstep (se 1 (by rfl) ⟨1188845, by rfl⟩ : syracuseStep 1585127 = 2377691) B2377691
theorem B1585391 : Blo 1056613 1585391 := bstep (se 1 (by rfl) ⟨1189043, by rfl⟩ : syracuseStep 1585391 = 2378087) B2378087
theorem B1585823 : Blo 1056613 1585823 := bstep (se 1 (by rfl) ⟨1189367, by rfl⟩ : syracuseStep 1585823 = 2378735) B2378735
theorem B11449127 : Blo 1056613 11449127 := bstep (se 1 (by rfl) ⟨8586845, by rfl⟩ : syracuseStep 11449127 = 17173691) B17173691
theorem B17183609 : Blo 1056613 17183609 := bstep (se 2 (by rfl) ⟨6443853, by rfl⟩ : syracuseStep 17183609 = 12887707) B12887707
theorem B10171655 : Blo 1056613 10171655 := bstep (se 1 (by rfl) ⟨7628741, by rfl⟩ : syracuseStep 10171655 = 15257483) B15257483
theorem B1586729 : Blo 1056613 1586729 := bstep (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) B1190047
theorem B1783343 : Blo 1056613 1783343 := bstep (se 1 (by rfl) ⟨1337507, by rfl⟩ : syracuseStep 1783343 = 2675015) B2675015
theorem B1586825 : Blo 1056613 1586825 := bstep (se 2 (by rfl) ⟨595059, by rfl⟩ : syracuseStep 1586825 = 1190119) B1190119
theorem B1587065 : Blo 1056613 1587065 := bstep (se 2 (by rfl) ⟨595149, by rfl⟩ : syracuseStep 1587065 = 1190299) B1190299
theorem B1587113 : Blo 1056613 1587113 := bstep (se 2 (by rfl) ⟨595167, by rfl⟩ : syracuseStep 1587113 = 1190335) B1190335
theorem B115849217 : Blo 1056613 115849217 := bstep (se 2 (by rfl) ⟨43443456, by rfl⟩ : syracuseStep 115849217 = 86886913) B86886913
theorem B4077631 : Blo 1056613 4077631 := bstep (se 1 (by rfl) ⟨3058223, by rfl⟩ : syracuseStep 4077631 = 6116447) B6116447
theorem B28981577 : Blo 1056613 28981577 := bstep (se 2 (by rfl) ⟨10868091, by rfl⟩ : syracuseStep 28981577 = 21736183) B21736183
theorem B1587647 : Blo 1056613 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B1588319 : Blo 1056613 1588319 := bstep (se 1 (by rfl) ⟨1191239, by rfl⟩ : syracuseStep 1588319 = 2382479) B2382479
theorem B1129663 : Blo 1056613 1129663 := bstep (se 1 (by rfl) ⟨847247, by rfl⟩ : syracuseStep 1129663 = 1694495) B1694495
theorem B8443182743 : Blo 1056613 8443182743 := bstep (se 1 (by rfl) ⟨6332387057, by rfl⟩ : syracuseStep 8443182743 = 12664774115) B12664774115
theorem B1589339 : Blo 1056613 1589339 := bstep (se 1 (by rfl) ⟨1192004, by rfl⟩ : syracuseStep 1589339 = 2384009) B2384009
theorem B1589423 : Blo 1056613 1589423 := bstep (se 1 (by rfl) ⟨1192067, by rfl⟩ : syracuseStep 1589423 = 2384135) B2384135
theorem B1589567 : Blo 1056613 1589567 := bstep (se 1 (by rfl) ⟨1192175, by rfl⟩ : syracuseStep 1589567 = 2384351) B2384351
theorem B1590137 : Blo 1056613 1590137 := bstep (se 2 (by rfl) ⟨596301, by rfl⟩ : syracuseStep 1590137 = 1192603) B1192603
theorem B3818495 : Blo 1056613 3818495 := bstep (se 1 (by rfl) ⟨2863871, by rfl⟩ : syracuseStep 3818495 = 5727743) B5727743
theorem B1590911 : Blo 1056613 1590911 := bstep (se 1 (by rfl) ⟨1193183, by rfl⟩ : syracuseStep 1590911 = 2386367) B2386367
theorem B2378231 : Blo 1056613 2378231 := bstep (se 1 (by rfl) ⟨1783673, by rfl⟩ : syracuseStep 2378231 = 3567347) B3567347
theorem B5360255 : Blo 1056613 5360255 := bstep (se 1 (by rfl) ⟨4020191, by rfl⟩ : syracuseStep 5360255 = 8040383) B8040383
theorem B1788743 : Blo 1056613 1788743 := bstep (se 1 (by rfl) ⟨1341557, by rfl⟩ : syracuseStep 1788743 = 2683115) B2683115
theorem B2380841 : Blo 1056613 2380841 := bstep (se 2 (by rfl) ⟨892815, by rfl⟩ : syracuseStep 2380841 = 1785631) B1785631
theorem B38687939 : Blo 1056613 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B2381111 : Blo 1056613 2381111 := bstep (se 1 (by rfl) ⟨1785833, by rfl⟩ : syracuseStep 2381111 = 3571667) B3571667
theorem B2613359 : Blo 1056613 2613359 := bstep (se 1 (by rfl) ⟨1960019, by rfl⟩ : syracuseStep 2613359 = 3920039) B3920039
theorem B1695865 : Blo 1056613 1695865 := bstep (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) B1271899
theorem B2614735 : Blo 1056613 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B6022633 : Blo 1056613 6022633 := bstep (se 2 (by rfl) ⟨2258487, by rfl⟩ : syracuseStep 6022633 = 4516975) B4516975
theorem B7628393 : Blo 1056613 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B6024091 : Blo 1056613 6024091 := bstep (se 1 (by rfl) ⟨4518068, by rfl⟩ : syracuseStep 6024091 = 9036137) B9036137
theorem B3009449 : Blo 1056613 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B1340059 : Blo 1056613 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B5730983 : Blo 1056613 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B3011431 : Blo 1056613 3011431 := bstep (se 1 (by rfl) ⟨2258573, by rfl⟩ : syracuseStep 3011431 = 4517147) B4517147
theorem B8713631 : Blo 1056613 8713631 := bstep (se 1 (by rfl) ⟨6535223, by rfl⟩ : syracuseStep 8713631 = 13070447) B13070447
theorem B2684411 : Blo 1056613 2684411 := bstep (se 1 (by rfl) ⟨2013308, by rfl⟩ : syracuseStep 2684411 = 4026617) B4026617
theorem B9042425 : Blo 1056613 9042425 := bstep (se 2 (by rfl) ⟨3390909, by rfl⟩ : syracuseStep 9042425 = 6781819) B6781819
theorem B18086489 : Blo 1056613 18086489 := bstep (se 2 (by rfl) ⟨6782433, by rfl⟩ : syracuseStep 18086489 = 13564867) B13564867
theorem B203520683 : Blo 1056613 203520683 := bstep (se 1 (by rfl) ⟨152640512, by rfl⟩ : syracuseStep 203520683 = 305281025) B305281025
theorem B19299455 : Blo 1056613 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B2261153 : Blo 1056613 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B3015463 : Blo 1056613 3015463 := bstep (se 1 (by rfl) ⟨2261597, by rfl⟩ : syracuseStep 3015463 = 4523195) B4523195
theorem B3573503 : Blo 1056613 3573503 := bstep (se 1 (by rfl) ⟨2680127, by rfl⟩ : syracuseStep 3573503 = 5360255) B5360255
theorem B22906637 : Blo 1056613 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B8030177 : Blo 1056613 8030177 := bstep (se 2 (by rfl) ⟨3011316, by rfl⟩ : syracuseStep 8030177 = 6022633) B6022633
theorem B25791959 : Blo 1056613 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B8032121 : Blo 1056613 8032121 := bstep (se 2 (by rfl) ⟨3012045, by rfl⟩ : syracuseStep 8032121 = 6024091) B6024091
theorem B10162853 : Blo 1056613 10162853 := bstep (se 4 (by rfl) ⟨952767, by rfl⟩ : syracuseStep 10162853 = 1905535) B1905535
theorem B1742239 : Blo 1056613 1742239 := bstep (se 1 (by rfl) ⟨1306679, by rfl⟩ : syracuseStep 1742239 = 2613359) B2613359
theorem B5085595 : Blo 1056613 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B2006299 : Blo 1056613 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B1056751 : Blo 1056613 1056751 := bstep (se 1 (by rfl) ⟨792563, by rfl⟩ : syracuseStep 1056751 = 1585127) B1585127
theorem B1056927 : Blo 1056613 1056927 := bstep (se 1 (by rfl) ⟨792695, by rfl⟩ : syracuseStep 1056927 = 1585391) B1585391
theorem B1057215 : Blo 1056613 1057215 := bstep (se 1 (by rfl) ⟨792911, by rfl⟩ : syracuseStep 1057215 = 1585823) B1585823
theorem B5809087 : Blo 1056613 5809087 := bstep (se 1 (by rfl) ⟨4356815, by rfl⟩ : syracuseStep 5809087 = 8713631) B8713631
theorem B1057819 : Blo 1056613 1057819 := bstep (se 1 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 1057819 = 1586729) B1586729
theorem B1188895 : Blo 1056613 1188895 := bstep (se 1 (by rfl) ⟨891671, by rfl⟩ : syracuseStep 1188895 = 1783343) B1783343
theorem B1057883 : Blo 1056613 1057883 := bstep (se 1 (by rfl) ⟨793412, by rfl⟩ : syracuseStep 1057883 = 1586825) B1586825
theorem B1058043 : Blo 1056613 1058043 := bstep (se 1 (by rfl) ⟨793532, by rfl⟩ : syracuseStep 1058043 = 1587065) B1587065
theorem B1058075 : Blo 1056613 1058075 := bstep (se 1 (by rfl) ⟨793556, by rfl⟩ : syracuseStep 1058075 = 1587113) B1587113
theorem B1058431 : Blo 1056613 1058431 := bstep (se 1 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 1058431 = 1587647) B1587647
theorem B1058879 : Blo 1056613 1058879 := bstep (se 1 (by rfl) ⟨794159, by rfl⟩ : syracuseStep 1058879 = 1588319) B1588319
theorem B1059559 : Blo 1056613 1059559 := bstep (se 1 (by rfl) ⟨794669, by rfl⟩ : syracuseStep 1059559 = 1589339) B1589339
theorem B1059615 : Blo 1056613 1059615 := bstep (se 1 (by rfl) ⟨794711, by rfl⟩ : syracuseStep 1059615 = 1589423) B1589423
theorem B1059711 : Blo 1056613 1059711 := bstep (se 1 (by rfl) ⟨794783, by rfl⟩ : syracuseStep 1059711 = 1589567) B1589567
theorem B1060091 : Blo 1056613 1060091 := bstep (se 1 (by rfl) ⟨795068, by rfl⟩ : syracuseStep 1060091 = 1590137) B1590137
theorem B1060607 : Blo 1056613 1060607 := bstep (se 1 (by rfl) ⟨795455, by rfl⟩ : syracuseStep 1060607 = 1590911) B1590911
theorem B1585487 : Blo 1056613 1585487 := bstep (se 1 (by rfl) ⟨1189115, by rfl⟩ : syracuseStep 1585487 = 2378231) B2378231
theorem B1192495 : Blo 1056613 1192495 := bstep (se 1 (by rfl) ⟨894371, by rfl⟩ : syracuseStep 1192495 = 1788743) B1788743
theorem B3486313 : Blo 1056613 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B2011873 : Blo 1056613 2011873 := bstep (se 2 (by rfl) ⟨754452, by rfl⟩ : syracuseStep 2011873 = 1508905) B1508905
theorem B1356799 : Blo 1056613 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B1587227 : Blo 1056613 1587227 := bstep (se 1 (by rfl) ⟨1190420, by rfl⟩ : syracuseStep 1587227 = 2380841) B2380841
theorem B1587407 : Blo 1056613 1587407 := bstep (se 1 (by rfl) ⟨1190555, by rfl⟩ : syracuseStep 1587407 = 2381111) B2381111
theorem B32651561 : Blo 1056613 32651561 := bstep (se 2 (by rfl) ⟨12244335, by rfl⟩ : syracuseStep 32651561 = 24488671) B24488671
theorem B5094343 : Blo 1056613 5094343 := bstep (se 1 (by rfl) ⟨3820757, by rfl⟩ : syracuseStep 5094343 = 7641515) B7641515
theorem B8372791 : Blo 1056613 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B1786745 : Blo 1056613 1786745 := bstep (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) B1340059
theorem B4015241 : Blo 1056613 4015241 := bstep (se 2 (by rfl) ⟨1505715, by rfl⟩ : syracuseStep 4015241 = 3011431) B3011431
theorem B3820655 : Blo 1056613 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B11455739 : Blo 1056613 11455739 := bstep (se 1 (by rfl) ⟨8591804, by rfl⟩ : syracuseStep 11455739 = 17183609) B17183609
theorem B1789607 : Blo 1056613 1789607 := bstep (se 1 (by rfl) ⟨1342205, by rfl⟩ : syracuseStep 1789607 = 2684411) B2684411
theorem B19321051 : Blo 1056613 19321051 := bstep (se 1 (by rfl) ⟨14490788, by rfl⟩ : syracuseStep 19321051 = 28981577) B28981577
theorem B135680455 : Blo 1056613 135680455 := bstep (se 1 (by rfl) ⟨101760341, by rfl⟩ : syracuseStep 135680455 = 203520683) B203520683
theorem B12866303 : Blo 1056613 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B2545663 : Blo 1056613 2545663 := bstep (se 1 (by rfl) ⟨1909247, by rfl⟩ : syracuseStep 2545663 = 3818495) B3818495
theorem B1269631 : Blo 1056613 1269631 := bstep (se 1 (by rfl) ⟨952223, by rfl⟩ : syracuseStep 1269631 = 1904447) B1904447
theorem B2384639 : Blo 1056613 2384639 := bstep (se 1 (by rfl) ⟨1788479, by rfl⟩ : syracuseStep 2384639 = 3576959) B3576959
theorem B2384711 : Blo 1056613 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B5730857 : Blo 1056613 5730857 := bstep (se 2 (by rfl) ⟨2149071, by rfl⟩ : syracuseStep 5730857 = 4298143) B4298143
theorem B3568319 : Blo 1056613 3568319 := bstep (se 1 (by rfl) ⟨2676239, by rfl⟩ : syracuseStep 3568319 = 5352479) B5352479
theorem B5436841 : Blo 1056613 5436841 := bstep (se 2 (by rfl) ⟨2038815, by rfl⟩ : syracuseStep 5436841 = 4077631) B4077631
theorem B7632751 : Blo 1056613 7632751 := bstep (se 1 (by rfl) ⟨5724563, by rfl⟩ : syracuseStep 7632751 = 11449127) B11449127
theorem B6781103 : Blo 1056613 6781103 := bstep (se 1 (by rfl) ⟨5085827, by rfl⟩ : syracuseStep 6781103 = 10171655) B10171655
theorem B77232811 : Blo 1056613 77232811 := bstep (se 1 (by rfl) ⟨57924608, by rfl⟩ : syracuseStep 77232811 = 115849217) B115849217
theorem B1506217 : Blo 1056613 1506217 := bstep (se 2 (by rfl) ⟨564831, by rfl⟩ : syracuseStep 1506217 = 1129663) B1129663
theorem B6028283 : Blo 1056613 6028283 := bstep (se 1 (by rfl) ⟨4521212, by rfl⟩ : syracuseStep 6028283 = 9042425) B9042425
theorem B12057659 : Blo 1056613 12057659 := bstep (se 1 (by rfl) ⟨9043244, by rfl⟩ : syracuseStep 12057659 = 18086489) B18086489
theorem B5628788495 : Blo 1056613 5628788495 := bstep (se 1 (by rfl) ⟨4221591371, by rfl⟩ : syracuseStep 5628788495 = 8443182743) B8443182743
theorem B6029741 : Blo 1056613 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B15271091 : Blo 1056613 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B7637159 : Blo 1056613 7637159 := bstep (se 1 (by rfl) ⟨5727869, by rfl⟩ : syracuseStep 7637159 = 11455739) B11455739
theorem B25761401 : Blo 1056613 25761401 := bstep (se 2 (by rfl) ⟨9660525, by rfl⟩ : syracuseStep 25761401 = 19321051) B19321051
theorem B1809065 : Blo 1056613 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B7249121 : Blo 1056613 7249121 := bstep (se 2 (by rfl) ⟨2718420, by rfl⟩ : syracuseStep 7249121 = 5436841) B5436841
theorem B1056991 : Blo 1056613 1056991 := bstep (se 1 (by rfl) ⟨792743, by rfl⟩ : syracuseStep 1056991 = 1585487) B1585487
theorem B2008289 : Blo 1056613 2008289 := bstep (se 2 (by rfl) ⟨753108, by rfl⟩ : syracuseStep 2008289 = 1506217) B1506217
theorem B6792457 : Blo 1056613 6792457 := bstep (se 2 (by rfl) ⟨2547171, by rfl⟩ : syracuseStep 6792457 = 5094343) B5094343
theorem B1058151 : Blo 1056613 1058151 := bstep (se 1 (by rfl) ⟨793613, by rfl⟩ : syracuseStep 1058151 = 1587227) B1587227
theorem B1058271 : Blo 1056613 1058271 := bstep (se 1 (by rfl) ⟨793703, by rfl⟩ : syracuseStep 1058271 = 1587407) B1587407
theorem B21767707 : Blo 1056613 21767707 := bstep (se 1 (by rfl) ⟨16325780, by rfl⟩ : syracuseStep 21767707 = 32651561) B32651561
theorem B8038439 : Blo 1056613 8038439 := bstep (se 1 (by rfl) ⟨6028829, by rfl⟩ : syracuseStep 8038439 = 12057659) B12057659
theorem B1191163 : Blo 1056613 1191163 := bstep (se 1 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 1191163 = 1786745) B1786745
theorem B7745449 : Blo 1056613 7745449 := bstep (se 2 (by rfl) ⟨2904543, by rfl⟩ : syracuseStep 7745449 = 5809087) B5809087
theorem B5353451 : Blo 1056613 5353451 := bstep (se 1 (by rfl) ⟨4015088, by rfl⟩ : syracuseStep 5353451 = 8030177) B8030177
theorem B1585193 : Blo 1056613 1585193 := bstep (se 2 (by rfl) ⟨594447, by rfl⟩ : syracuseStep 1585193 = 1188895) B1188895
theorem B1193071 : Blo 1056613 1193071 := bstep (se 1 (by rfl) ⟨894803, by rfl⟩ : syracuseStep 1193071 = 1789607) B1789607
theorem B5354747 : Blo 1056613 5354747 := bstep (se 1 (by rfl) ⟨4016060, by rfl⟩ : syracuseStep 5354747 = 8032121) B8032121
theorem B1589759 : Blo 1056613 1589759 := bstep (se 1 (by rfl) ⟨1192319, by rfl⟩ : syracuseStep 1589759 = 2384639) B2384639
theorem B1589807 : Blo 1056613 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B1589993 : Blo 1056613 1589993 := bstep (se 2 (by rfl) ⟨596247, by rfl⟩ : syracuseStep 1589993 = 1192495) B1192495
theorem B9291941 : Blo 1056613 9291941 := bstep (se 4 (by rfl) ⟨871119, by rfl⟩ : syracuseStep 9291941 = 1742239) B1742239
theorem B10177001 : Blo 1056613 10177001 := bstep (se 2 (by rfl) ⟨3816375, by rfl⟩ : syracuseStep 10177001 = 7632751) B7632751
theorem B3394217 : Blo 1056613 3394217 := bstep (se 2 (by rfl) ⟨1272831, by rfl⟩ : syracuseStep 3394217 = 2545663) B2545663
theorem B3820571 : Blo 1056613 3820571 := bstep (se 1 (by rfl) ⟨2865428, by rfl⟩ : syracuseStep 3820571 = 5730857) B5730857
theorem B2378879 : Blo 1056613 2378879 := bstep (se 1 (by rfl) ⟨1784159, by rfl⟩ : syracuseStep 2378879 = 3568319) B3568319
theorem B102977081 : Blo 1056613 102977081 := bstep (se 2 (by rfl) ⟨38616405, by rfl⟩ : syracuseStep 102977081 = 77232811) B77232811
theorem B2675065 : Blo 1056613 2675065 := bstep (se 2 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 2675065 = 2006299) B2006299
theorem B4018855 : Blo 1056613 4018855 := bstep (se 1 (by rfl) ⟨3014141, by rfl⟩ : syracuseStep 4018855 = 6028283) B6028283
theorem B1692841 : Blo 1056613 1692841 := bstep (se 2 (by rfl) ⟨634815, by rfl⟩ : syracuseStep 1692841 = 1269631) B1269631
theorem B2676827 : Blo 1056613 2676827 := bstep (se 1 (by rfl) ⟨2007620, by rfl⟩ : syracuseStep 2676827 = 4015241) B4015241
theorem B4020617 : Blo 1056613 4020617 := bstep (se 2 (by rfl) ⟨1507731, by rfl⟩ : syracuseStep 4020617 = 3015463) B3015463
theorem B2382335 : Blo 1056613 2382335 := bstep (se 1 (by rfl) ⟨1786751, by rfl⟩ : syracuseStep 2382335 = 3573503) B3573503
theorem B27123173 : Blo 1056613 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B17194639 : Blo 1056613 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B44654885 : Blo 1056613 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B6775235 : Blo 1056613 6775235 := bstep (se 1 (by rfl) ⟨5081426, by rfl⟩ : syracuseStep 6775235 = 10162853) B10162853
theorem B8577535 : Blo 1056613 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B180907273 : Blo 1056613 180907273 := bstep (se 2 (by rfl) ⟨67840227, by rfl⟩ : syracuseStep 180907273 = 135680455) B135680455
theorem B4648417 : Blo 1056613 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B2682497 : Blo 1056613 2682497 := bstep (se 2 (by rfl) ⟨1005936, by rfl⟩ : syracuseStep 2682497 = 2011873) B2011873
theorem B10188413 : Blo 1056613 10188413 := bstep (se 3 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 10188413 = 3820655) B3820655
theorem B4520735 : Blo 1056613 4520735 := bstep (se 1 (by rfl) ⟨3390551, by rfl⟩ : syracuseStep 4520735 = 6781103) B6781103
theorem B3752525663 : Blo 1056613 3752525663 := bstep (se 1 (by rfl) ⟨2814394247, by rfl⟩ : syracuseStep 3752525663 = 5628788495) B5628788495
theorem B11436713 : Blo 1056613 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B6194627 : Blo 1056613 6194627 := bstep (se 1 (by rfl) ⟨4645970, by rfl⟩ : syracuseStep 6194627 = 9291941) B9291941
theorem B6784667 : Blo 1056613 6784667 := bstep (se 1 (by rfl) ⟨5088500, by rfl⟩ : syracuseStep 6784667 = 10177001) B10177001
theorem B2262811 : Blo 1056613 2262811 := bstep (se 1 (by rfl) ⟨1697108, by rfl⟩ : syracuseStep 2262811 = 3394217) B3394217
theorem B68651387 : Blo 1056613 68651387 := bstep (se 1 (by rfl) ⟨51488540, by rfl⟩ : syracuseStep 68651387 = 102977081) B102977081
theorem B17174267 : Blo 1056613 17174267 := bstep (se 1 (by rfl) ⟨12880700, by rfl⟩ : syracuseStep 17174267 = 25761401) B25761401
theorem B241209697 : Blo 1056613 241209697 := bstep (se 2 (by rfl) ⟨90453636, by rfl⟩ : syracuseStep 241209697 = 180907273) B180907273
theorem B10327265 : Blo 1056613 10327265 := bstep (se 2 (by rfl) ⟨3872724, by rfl⟩ : syracuseStep 10327265 = 7745449) B7745449
theorem B4824173 : Blo 1056613 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B1056795 : Blo 1056613 1056795 := bstep (se 1 (by rfl) ⟨792596, by rfl⟩ : syracuseStep 1056795 = 1585193) B1585193
theorem B6792275 : Blo 1056613 6792275 := bstep (se 1 (by rfl) ⟨5094206, by rfl⟩ : syracuseStep 6792275 = 10188413) B10188413
theorem B2501683775 : Blo 1056613 2501683775 := bstep (se 1 (by rfl) ⟨1876262831, by rfl⟩ : syracuseStep 2501683775 = 3752525663) B3752525663
theorem B1059839 : Blo 1056613 1059839 := bstep (se 1 (by rfl) ⟨794879, by rfl⟩ : syracuseStep 1059839 = 1589759) B1589759
theorem B1059871 : Blo 1056613 1059871 := bstep (se 1 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 1059871 = 1589807) B1589807
theorem B1059995 : Blo 1056613 1059995 := bstep (se 1 (by rfl) ⟨794996, by rfl⟩ : syracuseStep 1059995 = 1589993) B1589993
theorem B5091439 : Blo 1056613 5091439 := bstep (se 1 (by rfl) ⟨3818579, by rfl⟩ : syracuseStep 5091439 = 7637159) B7637159
theorem B9056609 : Blo 1056613 9056609 := bstep (se 2 (by rfl) ⟨3396228, by rfl⟩ : syracuseStep 9056609 = 6792457) B6792457
theorem B1585919 : Blo 1056613 1585919 := bstep (se 1 (by rfl) ⟨1189439, by rfl⟩ : syracuseStep 1585919 = 2378879) B2378879
theorem B1784551 : Blo 1056613 1784551 := bstep (se 1 (by rfl) ⟨1338413, by rfl⟩ : syracuseStep 1784551 = 2676827) B2676827
theorem B1588217 : Blo 1056613 1588217 := bstep (se 2 (by rfl) ⟨595581, by rfl⟩ : syracuseStep 1588217 = 1191163) B1191163
theorem B1588223 : Blo 1056613 1588223 := bstep (se 1 (by rfl) ⟨1191167, by rfl⟩ : syracuseStep 1588223 = 2382335) B2382335
theorem B4832747 : Blo 1056613 4832747 := bstep (se 1 (by rfl) ⟨3624560, by rfl⟩ : syracuseStep 4832747 = 7249121) B7249121
theorem B29769923 : Blo 1056613 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B5358473 : Blo 1056613 5358473 := bstep (se 2 (by rfl) ⟨2009427, by rfl⟩ : syracuseStep 5358473 = 4018855) B4018855
theorem B5358959 : Blo 1056613 5358959 := bstep (se 1 (by rfl) ⟨4019219, by rfl⟩ : syracuseStep 5358959 = 8038439) B8038439
theorem B1590761 : Blo 1056613 1590761 := bstep (se 2 (by rfl) ⟨596535, by rfl⟩ : syracuseStep 1590761 = 1193071) B1193071
theorem B1788331 : Blo 1056613 1788331 := bstep (se 1 (by rfl) ⟨1341248, by rfl⟩ : syracuseStep 1788331 = 2682497) B2682497
theorem B24791557 : Blo 1056613 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B22926185 : Blo 1056613 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B4019827 : Blo 1056613 4019827 := bstep (se 1 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 4019827 = 6029741) B6029741
theorem B10180727 : Blo 1056613 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B2547047 : Blo 1056613 2547047 := bstep (se 1 (by rfl) ⟨1910285, by rfl⟩ : syracuseStep 2547047 = 3820571) B3820571
theorem B29023609 : Blo 1056613 29023609 := bstep (se 2 (by rfl) ⟨10883853, by rfl⟩ : syracuseStep 29023609 = 21767707) B21767707
theorem B2680411 : Blo 1056613 2680411 := bstep (se 1 (by rfl) ⟨2010308, by rfl⟩ : syracuseStep 2680411 = 4020617) B4020617
theorem B18082115 : Blo 1056613 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B4516823 : Blo 1056613 4516823 := bstep (se 1 (by rfl) ⟨3387617, by rfl⟩ : syracuseStep 4516823 = 6775235) B6775235
theorem B3566753 : Blo 1056613 3566753 := bstep (se 2 (by rfl) ⟨1337532, by rfl⟩ : syracuseStep 3566753 = 2675065) B2675065
theorem B1338859 : Blo 1056613 1338859 := bstep (se 1 (by rfl) ⟨1004144, by rfl⟩ : syracuseStep 1338859 = 2008289) B2008289
theorem B2257121 : Blo 1056613 2257121 := bstep (se 2 (by rfl) ⟨846420, by rfl⟩ : syracuseStep 2257121 = 1692841) B1692841
theorem B3568967 : Blo 1056613 3568967 := bstep (se 1 (by rfl) ⟨2676725, by rfl⟩ : syracuseStep 3568967 = 5353451) B5353451
theorem B3569831 : Blo 1056613 3569831 := bstep (se 1 (by rfl) ⟨2677373, by rfl⟩ : syracuseStep 3569831 = 5354747) B5354747
theorem B3013823 : Blo 1056613 3013823 := bstep (se 1 (by rfl) ⟨2260367, by rfl⟩ : syracuseStep 3013823 = 4520735) B4520735
theorem B3572315 : Blo 1056613 3572315 := bstep (se 1 (by rfl) ⟨2679236, by rfl⟩ : syracuseStep 3572315 = 5358473) B5358473
theorem B3572639 : Blo 1056613 3572639 := bstep (se 1 (by rfl) ⟨2679479, by rfl⟩ : syracuseStep 3572639 = 5358959) B5358959
theorem B4129751 : Blo 1056613 4129751 := bstep (se 1 (by rfl) ⟨3097313, by rfl⟩ : syracuseStep 4129751 = 6194627) B6194627
theorem B4523111 : Blo 1056613 4523111 := bstep (se 1 (by rfl) ⟨3392333, by rfl⟩ : syracuseStep 4523111 = 6784667) B6784667
theorem B3573881 : Blo 1056613 3573881 := bstep (se 2 (by rfl) ⟨1340205, by rfl⟩ : syracuseStep 3573881 = 2680411) B2680411
theorem B3017081 : Blo 1056613 3017081 := bstep (se 2 (by rfl) ⟨1131405, by rfl⟩ : syracuseStep 3017081 = 2262811) B2262811
theorem B6884843 : Blo 1056613 6884843 := bstep (se 1 (by rfl) ⟨5163632, by rfl⟩ : syracuseStep 6884843 = 10327265) B10327265
theorem B6787151 : Blo 1056613 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B3216115 : Blo 1056613 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B6788585 : Blo 1056613 6788585 := bstep (se 2 (by rfl) ⟨2545719, by rfl⟩ : syracuseStep 6788585 = 5091439) B5091439
theorem B6037739 : Blo 1056613 6037739 := bstep (se 1 (by rfl) ⟨4528304, by rfl⟩ : syracuseStep 6037739 = 9056609) B9056609
theorem B1057279 : Blo 1056613 1057279 := bstep (se 1 (by rfl) ⟨792959, by rfl⟩ : syracuseStep 1057279 = 1585919) B1585919
theorem B1058811 : Blo 1056613 1058811 := bstep (se 1 (by rfl) ⟨794108, by rfl⟩ : syracuseStep 1058811 = 1588217) B1588217
theorem B1058815 : Blo 1056613 1058815 := bstep (se 1 (by rfl) ⟨794111, by rfl⟩ : syracuseStep 1058815 = 1588223) B1588223
theorem B2009215 : Blo 1056613 2009215 := bstep (se 1 (by rfl) ⟨1506911, by rfl⟩ : syracuseStep 2009215 = 3013823) B3013823
theorem B3221831 : Blo 1056613 3221831 := bstep (se 1 (by rfl) ⟨2416373, by rfl⟩ : syracuseStep 3221831 = 4832747) B4832747
theorem B1060507 : Blo 1056613 1060507 := bstep (se 1 (by rfl) ⟨795380, by rfl⟩ : syracuseStep 1060507 = 1590761) B1590761
theorem B11449511 : Blo 1056613 11449511 := bstep (se 1 (by rfl) ⟨8587133, by rfl⟩ : syracuseStep 11449511 = 17174267) B17174267
theorem B15284123 : Blo 1056613 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B1785145 : Blo 1056613 1785145 := bstep (se 2 (by rfl) ⟨669429, by rfl⟩ : syracuseStep 1785145 = 1338859) B1338859
theorem B2377835 : Blo 1056613 2377835 := bstep (se 1 (by rfl) ⟨1783376, by rfl⟩ : syracuseStep 2377835 = 3566753) B3566753
theorem B5359769 : Blo 1056613 5359769 := bstep (se 2 (by rfl) ⟨2009913, by rfl⟩ : syracuseStep 5359769 = 4019827) B4019827
theorem B2379311 : Blo 1056613 2379311 := bstep (se 1 (by rfl) ⟨1784483, by rfl⟩ : syracuseStep 2379311 = 3568967) B3568967
theorem B2379401 : Blo 1056613 2379401 := bstep (se 2 (by rfl) ⟨892275, by rfl⟩ : syracuseStep 2379401 = 1784551) B1784551
theorem B2379887 : Blo 1056613 2379887 := bstep (se 1 (by rfl) ⟨1784915, by rfl⟩ : syracuseStep 2379887 = 3569831) B3569831
theorem B19846615 : Blo 1056613 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B7624475 : Blo 1056613 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B45767591 : Blo 1056613 45767591 := bstep (se 1 (by rfl) ⟨34325693, by rfl⟩ : syracuseStep 45767591 = 68651387) B68651387
theorem B18112733 : Blo 1056613 18112733 := bstep (se 3 (by rfl) ⟨3396137, by rfl⟩ : syracuseStep 18112733 = 6792275) B6792275
theorem B2384441 : Blo 1056613 2384441 := bstep (se 2 (by rfl) ⟨894165, by rfl⟩ : syracuseStep 2384441 = 1788331) B1788331
theorem B33055409 : Blo 1056613 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B1698031 : Blo 1056613 1698031 := bstep (se 1 (by rfl) ⟨1273523, by rfl⟩ : syracuseStep 1698031 = 2547047) B2547047
theorem B321612929 : Blo 1056613 321612929 := bstep (se 2 (by rfl) ⟨120604848, by rfl⟩ : syracuseStep 321612929 = 241209697) B241209697
theorem B12054743 : Blo 1056613 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B1667789183 : Blo 1056613 1667789183 := bstep (se 1 (by rfl) ⟨1250841887, by rfl⟩ : syracuseStep 1667789183 = 2501683775) B2501683775
theorem B3011215 : Blo 1056613 3011215 := bstep (se 1 (by rfl) ⟨2258411, by rfl⟩ : syracuseStep 3011215 = 4516823) B4516823
theorem B1504747 : Blo 1056613 1504747 := bstep (se 1 (by rfl) ⟨1128560, by rfl⟩ : syracuseStep 1504747 = 2257121) B2257121
theorem B38698145 : Blo 1056613 38698145 := bstep (se 2 (by rfl) ⟨14511804, by rfl⟩ : syracuseStep 38698145 = 29023609) B29023609
theorem B2753167 : Blo 1056613 2753167 := bstep (se 1 (by rfl) ⟨2064875, by rfl⟩ : syracuseStep 2753167 = 4129751) B4129751
theorem B3015407 : Blo 1056613 3015407 := bstep (se 1 (by rfl) ⟨2261555, by rfl⟩ : syracuseStep 3015407 = 4523111) B4523111
theorem B3573179 : Blo 1056613 3573179 := bstep (se 1 (by rfl) ⟨2679884, by rfl⟩ : syracuseStep 3573179 = 5359769) B5359769
theorem B88147757 : Blo 1056613 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B4524767 : Blo 1056613 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B2264041 : Blo 1056613 2264041 := bstep (se 2 (by rfl) ⟨849015, by rfl⟩ : syracuseStep 2264041 = 1698031) B1698031
theorem B4525723 : Blo 1056613 4525723 := bstep (se 1 (by rfl) ⟨3394292, by rfl⟩ : syracuseStep 4525723 = 6788585) B6788585
theorem B5082983 : Blo 1056613 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B30511727 : Blo 1056613 30511727 := bstep (se 1 (by rfl) ⟨22883795, by rfl⟩ : syracuseStep 30511727 = 45767591) B45767591
theorem B214408619 : Blo 1056613 214408619 := bstep (se 1 (by rfl) ⟨160806464, by rfl⟩ : syracuseStep 214408619 = 321612929) B321612929
theorem B8036495 : Blo 1056613 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B1111859455 : Blo 1056613 1111859455 := bstep (se 1 (by rfl) ⟨833894591, by rfl⟩ : syracuseStep 1111859455 = 1667789183) B1667789183
theorem B18359581 : Blo 1056613 18359581 := bstep (se 3 (by rfl) ⟨3442421, by rfl⟩ : syracuseStep 18359581 = 6884843) B6884843
theorem B25798763 : Blo 1056613 25798763 := bstep (se 1 (by rfl) ⟨19349072, by rfl⟩ : syracuseStep 25798763 = 38698145) B38698145
theorem B1585223 : Blo 1056613 1585223 := bstep (se 1 (by rfl) ⟨1188917, by rfl⟩ : syracuseStep 1585223 = 2377835) B2377835
theorem B2011387 : Blo 1056613 2011387 := bstep (se 1 (by rfl) ⟨1508540, by rfl⟩ : syracuseStep 2011387 = 3017081) B3017081
theorem B1586207 : Blo 1056613 1586207 := bstep (se 1 (by rfl) ⟨1189655, by rfl⟩ : syracuseStep 1586207 = 2379311) B2379311
theorem B1586267 : Blo 1056613 1586267 := bstep (se 1 (by rfl) ⟨1189700, by rfl⟩ : syracuseStep 1586267 = 2379401) B2379401
theorem B1586591 : Blo 1056613 1586591 := bstep (se 1 (by rfl) ⟨1189943, by rfl⟩ : syracuseStep 1586591 = 2379887) B2379887
theorem B12075155 : Blo 1056613 12075155 := bstep (se 1 (by rfl) ⟨9056366, by rfl⟩ : syracuseStep 12075155 = 18112733) B18112733
theorem B1589627 : Blo 1056613 1589627 := bstep (se 1 (by rfl) ⟨1192220, by rfl⟩ : syracuseStep 1589627 = 2384441) B2384441
theorem B4014953 : Blo 1056613 4014953 := bstep (se 2 (by rfl) ⟨1505607, by rfl⟩ : syracuseStep 4014953 = 3011215) B3011215
theorem B2147887 : Blo 1056613 2147887 := bstep (se 1 (by rfl) ⟨1610915, by rfl⟩ : syracuseStep 2147887 = 3221831) B3221831
theorem B26462153 : Blo 1056613 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B2380193 : Blo 1056613 2380193 := bstep (se 2 (by rfl) ⟨892572, by rfl⟩ : syracuseStep 2380193 = 1785145) B1785145
theorem B2381543 : Blo 1056613 2381543 := bstep (se 1 (by rfl) ⟨1786157, by rfl⟩ : syracuseStep 2381543 = 3572315) B3572315
theorem B2381759 : Blo 1056613 2381759 := bstep (se 1 (by rfl) ⟨1786319, by rfl⟩ : syracuseStep 2381759 = 3572639) B3572639
theorem B2382587 : Blo 1056613 2382587 := bstep (se 1 (by rfl) ⟨1786940, by rfl⟩ : syracuseStep 2382587 = 3573881) B3573881
theorem B2678953 : Blo 1056613 2678953 := bstep (se 2 (by rfl) ⟨1004607, by rfl⟩ : syracuseStep 2678953 = 2009215) B2009215
theorem B4025159 : Blo 1056613 4025159 := bstep (se 1 (by rfl) ⟨3018869, by rfl⟩ : syracuseStep 4025159 = 6037739) B6037739
theorem B4288153 : Blo 1056613 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B8025317 : Blo 1056613 8025317 := bstep (se 4 (by rfl) ⟨752373, by rfl⟩ : syracuseStep 8025317 = 1504747) B1504747
theorem B7633007 : Blo 1056613 7633007 := bstep (se 1 (by rfl) ⟨5724755, by rfl⟩ : syracuseStep 7633007 = 11449511) B11449511
theorem B10189415 : Blo 1056613 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B3571937 : Blo 1056613 3571937 := bstep (se 2 (by rfl) ⟨1339476, by rfl⟩ : syracuseStep 3571937 = 2678953) B2678953
theorem B3670889 : Blo 1056613 3670889 := bstep (se 2 (by rfl) ⟨1376583, by rfl⟩ : syracuseStep 3670889 = 2753167) B2753167
theorem B24479441 : Blo 1056613 24479441 := bstep (se 2 (by rfl) ⟨9179790, by rfl⟩ : syracuseStep 24479441 = 18359581) B18359581
theorem B3016511 : Blo 1056613 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B3018721 : Blo 1056613 3018721 := bstep (se 2 (by rfl) ⟨1132020, by rfl⟩ : syracuseStep 3018721 = 2264041) B2264041
theorem B6034297 : Blo 1056613 6034297 := bstep (se 2 (by rfl) ⟨2262861, by rfl⟩ : syracuseStep 6034297 = 4525723) B4525723
theorem B142939079 : Blo 1056613 142939079 := bstep (se 1 (by rfl) ⟨107204309, by rfl⟩ : syracuseStep 142939079 = 214408619) B214408619
theorem B1056815 : Blo 1056613 1056815 := bstep (se 1 (by rfl) ⟨792611, by rfl⟩ : syracuseStep 1056815 = 1585223) B1585223
theorem B1057471 : Blo 1056613 1057471 := bstep (se 1 (by rfl) ⟨793103, by rfl⟩ : syracuseStep 1057471 = 1586207) B1586207
theorem B1057511 : Blo 1056613 1057511 := bstep (se 1 (by rfl) ⟨793133, by rfl⟩ : syracuseStep 1057511 = 1586267) B1586267
theorem B5350211 : Blo 1056613 5350211 := bstep (se 1 (by rfl) ⟨4012658, by rfl⟩ : syracuseStep 5350211 = 8025317) B8025317
theorem B1057727 : Blo 1056613 1057727 := bstep (se 1 (by rfl) ⟨793295, by rfl⟩ : syracuseStep 1057727 = 1586591) B1586591
theorem B5088671 : Blo 1056613 5088671 := bstep (se 1 (by rfl) ⟨3816503, by rfl⟩ : syracuseStep 5088671 = 7633007) B7633007
theorem B6792943 : Blo 1056613 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B1059751 : Blo 1056613 1059751 := bstep (se 1 (by rfl) ⟨794813, by rfl⟩ : syracuseStep 1059751 = 1589627) B1589627
theorem B2010271 : Blo 1056613 2010271 := bstep (se 1 (by rfl) ⟨1507703, by rfl⟩ : syracuseStep 2010271 = 3015407) B3015407
theorem B58765171 : Blo 1056613 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B2863849 : Blo 1056613 2863849 := bstep (se 2 (by rfl) ⟨1073943, by rfl⟩ : syracuseStep 2863849 = 2147887) B2147887
theorem B3388655 : Blo 1056613 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B1586795 : Blo 1056613 1586795 := bstep (se 1 (by rfl) ⟨1190096, by rfl⟩ : syracuseStep 1586795 = 2380193) B2380193
theorem B1587695 : Blo 1056613 1587695 := bstep (se 1 (by rfl) ⟨1190771, by rfl⟩ : syracuseStep 1587695 = 2381543) B2381543
theorem B1587839 : Blo 1056613 1587839 := bstep (se 1 (by rfl) ⟨1190879, by rfl⟩ : syracuseStep 1587839 = 2381759) B2381759
theorem B1588391 : Blo 1056613 1588391 := bstep (se 1 (by rfl) ⟨1191293, by rfl⟩ : syracuseStep 1588391 = 2382587) B2382587
theorem B5717537 : Blo 1056613 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B70565741 : Blo 1056613 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B5357663 : Blo 1056613 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B68796701 : Blo 1056613 68796701 := bstep (se 3 (by rfl) ⟨12899381, by rfl⟩ : syracuseStep 68796701 = 25798763) B25798763
theorem B8050103 : Blo 1056613 8050103 := bstep (se 1 (by rfl) ⟨6037577, by rfl⟩ : syracuseStep 8050103 = 12075155) B12075155
theorem B1482479273 : Blo 1056613 1482479273 := bstep (se 2 (by rfl) ⟨555929727, by rfl⟩ : syracuseStep 1482479273 = 1111859455) B1111859455
theorem B2676635 : Blo 1056613 2676635 := bstep (se 1 (by rfl) ⟨2007476, by rfl⟩ : syracuseStep 2676635 = 4014953) B4014953
theorem B2382119 : Blo 1056613 2382119 := bstep (se 1 (by rfl) ⟨1786589, by rfl⟩ : syracuseStep 2382119 = 3573179) B3573179
theorem B20341151 : Blo 1056613 20341151 := bstep (se 1 (by rfl) ⟨15255863, by rfl⟩ : syracuseStep 20341151 = 30511727) B30511727
theorem B2681849 : Blo 1056613 2681849 := bstep (se 2 (by rfl) ⟨1005693, by rfl⟩ : syracuseStep 2681849 = 2011387) B2011387
theorem B2683439 : Blo 1056613 2683439 := bstep (se 1 (by rfl) ⟨2012579, by rfl⟩ : syracuseStep 2683439 = 4025159) B4025159
theorem B3571775 : Blo 1056613 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B16319627 : Blo 1056613 16319627 := bstep (se 1 (by rfl) ⟨12239720, by rfl⟩ : syracuseStep 16319627 = 24479441) B24479441
theorem B95292719 : Blo 1056613 95292719 := bstep (se 1 (by rfl) ⟨71469539, by rfl⟩ : syracuseStep 95292719 = 142939079) B142939079
theorem B988319515 : Blo 1056613 988319515 := bstep (se 1 (by rfl) ⟨741239636, by rfl⟩ : syracuseStep 988319515 = 1482479273) B1482479273
theorem B78353561 : Blo 1056613 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B1057863 : Blo 1056613 1057863 := bstep (se 1 (by rfl) ⟨793397, by rfl⟩ : syracuseStep 1057863 = 1586795) B1586795
theorem B1058463 : Blo 1056613 1058463 := bstep (se 1 (by rfl) ⟨793847, by rfl⟩ : syracuseStep 1058463 = 1587695) B1587695
theorem B1058559 : Blo 1056613 1058559 := bstep (se 1 (by rfl) ⟨793919, by rfl⟩ : syracuseStep 1058559 = 1587839) B1587839
theorem B1058927 : Blo 1056613 1058927 := bstep (se 1 (by rfl) ⟨794195, by rfl⟩ : syracuseStep 1058927 = 1588391) B1588391
theorem B3811691 : Blo 1056613 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B2011007 : Blo 1056613 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B9057257 : Blo 1056613 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B1784423 : Blo 1056613 1784423 := bstep (se 1 (by rfl) ⟨1338317, by rfl⟩ : syracuseStep 1784423 = 2676635) B2676635
theorem B1588079 : Blo 1056613 1588079 := bstep (se 1 (by rfl) ⟨1191059, by rfl⟩ : syracuseStep 1588079 = 2382119) B2382119
theorem B3392447 : Blo 1056613 3392447 := bstep (se 1 (by rfl) ⟨2544335, by rfl⟩ : syracuseStep 3392447 = 5088671) B5088671
theorem B3818465 : Blo 1056613 3818465 := bstep (se 2 (by rfl) ⟨1431924, by rfl⟩ : syracuseStep 3818465 = 2863849) B2863849
theorem B8045729 : Blo 1056613 8045729 := bstep (se 2 (by rfl) ⟨3017148, by rfl⟩ : syracuseStep 8045729 = 6034297) B6034297
theorem B1787899 : Blo 1056613 1787899 := bstep (se 1 (by rfl) ⟨1340924, by rfl⟩ : syracuseStep 1787899 = 2681849) B2681849
theorem B1788959 : Blo 1056613 1788959 := bstep (se 1 (by rfl) ⟨1341719, by rfl⟩ : syracuseStep 1788959 = 2683439) B2683439
theorem B47043827 : Blo 1056613 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B2381291 : Blo 1056613 2381291 := bstep (se 1 (by rfl) ⟨1785968, by rfl⟩ : syracuseStep 2381291 = 3571937) B3571937
theorem B45864467 : Blo 1056613 45864467 := bstep (se 1 (by rfl) ⟨34398350, by rfl⟩ : syracuseStep 45864467 = 68796701) B68796701
theorem B5366735 : Blo 1056613 5366735 := bstep (se 1 (by rfl) ⟨4025051, by rfl⟩ : syracuseStep 5366735 = 8050103) B8050103
theorem B2680361 : Blo 1056613 2680361 := bstep (se 2 (by rfl) ⟨1005135, by rfl⟩ : syracuseStep 2680361 = 2010271) B2010271
theorem B4024961 : Blo 1056613 4024961 := bstep (se 2 (by rfl) ⟨1509360, by rfl⟩ : syracuseStep 4024961 = 3018721) B3018721
theorem B13560767 : Blo 1056613 13560767 := bstep (se 1 (by rfl) ⟨10170575, by rfl⟩ : syracuseStep 13560767 = 20341151) B20341151
theorem B3566807 : Blo 1056613 3566807 := bstep (se 1 (by rfl) ⟨2675105, by rfl⟩ : syracuseStep 3566807 = 5350211) B5350211
theorem B2259103 : Blo 1056613 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B39156149 : Blo 1056613 39156149 := bstep (se 5 (by rfl) ⟨1835444, by rfl⟩ : syracuseStep 39156149 = 3670889) B3670889
theorem B10879751 : Blo 1056613 10879751 := bstep (se 1 (by rfl) ⟨8159813, by rfl⟩ : syracuseStep 10879751 = 16319627) B16319627
theorem B9046525 : Blo 1056613 9046525 := bstep (se 3 (by rfl) ⟨1696223, by rfl⟩ : syracuseStep 9046525 = 3392447) B3392447
theorem B52235707 : Blo 1056613 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B31362551 : Blo 1056613 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B30576311 : Blo 1056613 30576311 := bstep (se 1 (by rfl) ⟨22932233, by rfl⟩ : syracuseStep 30576311 = 45864467) B45864467
theorem B3577823 : Blo 1056613 3577823 := bstep (se 1 (by rfl) ⟨2683367, by rfl⟩ : syracuseStep 3577823 = 5366735) B5366735
theorem B6038171 : Blo 1056613 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B1189615 : Blo 1056613 1189615 := bstep (se 1 (by rfl) ⟨892211, by rfl⟩ : syracuseStep 1189615 = 1784423) B1784423
theorem B1058719 : Blo 1056613 1058719 := bstep (se 1 (by rfl) ⟨794039, by rfl⟩ : syracuseStep 1058719 = 1588079) B1588079
theorem B1192639 : Blo 1056613 1192639 := bstep (se 1 (by rfl) ⟨894479, by rfl⟩ : syracuseStep 1192639 = 1788959) B1788959
theorem B1587527 : Blo 1056613 1587527 := bstep (se 1 (by rfl) ⟨1190645, by rfl⟩ : syracuseStep 1587527 = 2381291) B2381291
theorem B1786907 : Blo 1056613 1786907 := bstep (se 1 (by rfl) ⟨1340180, by rfl⟩ : syracuseStep 1786907 = 2680361) B2680361
theorem B2541127 : Blo 1056613 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B2377871 : Blo 1056613 2377871 := bstep (se 1 (by rfl) ⟨1783403, by rfl⟩ : syracuseStep 2377871 = 3566807) B3566807
theorem B26104099 : Blo 1056613 26104099 := bstep (se 1 (by rfl) ⟨19578074, by rfl⟩ : syracuseStep 26104099 = 39156149) B39156149
theorem B5362685 : Blo 1056613 5362685 := bstep (se 3 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 5362685 = 2011007) B2011007
theorem B2381183 : Blo 1056613 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B2545643 : Blo 1056613 2545643 := bstep (se 1 (by rfl) ⟨1909232, by rfl⟩ : syracuseStep 2545643 = 3818465) B3818465
theorem B5363819 : Blo 1056613 5363819 := bstep (se 1 (by rfl) ⟨4022864, by rfl⟩ : syracuseStep 5363819 = 8045729) B8045729
theorem B63528479 : Blo 1056613 63528479 := bstep (se 1 (by rfl) ⟨47646359, by rfl⟩ : syracuseStep 63528479 = 95292719) B95292719
theorem B2383865 : Blo 1056613 2383865 := bstep (se 2 (by rfl) ⟨893949, by rfl⟩ : syracuseStep 2383865 = 1787899) B1787899
theorem B1317759353 : Blo 1056613 1317759353 := bstep (se 2 (by rfl) ⟨494159757, by rfl⟩ : syracuseStep 1317759353 = 988319515) B988319515
theorem B2683307 : Blo 1056613 2683307 := bstep (se 1 (by rfl) ⟨2012480, by rfl⟩ : syracuseStep 2683307 = 4024961) B4024961
theorem B9040511 : Blo 1056613 9040511 := bstep (se 1 (by rfl) ⟨6780383, by rfl⟩ : syracuseStep 9040511 = 13560767) B13560767
theorem B3012137 : Blo 1056613 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B20908367 : Blo 1056613 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B20384207 : Blo 1056613 20384207 := bstep (se 1 (by rfl) ⟨15288155, by rfl⟩ : syracuseStep 20384207 = 30576311) B30576311
theorem B12062033 : Blo 1056613 12062033 := bstep (se 2 (by rfl) ⟨4523262, by rfl⟩ : syracuseStep 12062033 = 9046525) B9046525
theorem B3575123 : Blo 1056613 3575123 := bstep (se 1 (by rfl) ⟨2681342, by rfl⟩ : syracuseStep 3575123 = 5362685) B5362685
theorem B3575879 : Blo 1056613 3575879 := bstep (se 1 (by rfl) ⟨2681909, by rfl⟩ : syracuseStep 3575879 = 5363819) B5363819
theorem B34805465 : Blo 1056613 34805465 := bstep (se 2 (by rfl) ⟨13052049, by rfl⟩ : syracuseStep 34805465 = 26104099) B26104099
theorem B2008091 : Blo 1056613 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B1058351 : Blo 1056613 1058351 := bstep (se 1 (by rfl) ⟨793763, by rfl⟩ : syracuseStep 1058351 = 1587527) B1587527
theorem B7253167 : Blo 1056613 7253167 := bstep (se 1 (by rfl) ⟨5439875, by rfl⟩ : syracuseStep 7253167 = 10879751) B10879751
theorem B1191271 : Blo 1056613 1191271 := bstep (se 1 (by rfl) ⟨893453, by rfl⟩ : syracuseStep 1191271 = 1786907) B1786907
theorem B1585247 : Blo 1056613 1585247 := bstep (se 1 (by rfl) ⟨1188935, by rfl⟩ : syracuseStep 1585247 = 2377871) B2377871
theorem B3388169 : Blo 1056613 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B1586153 : Blo 1056613 1586153 := bstep (se 2 (by rfl) ⟨594807, by rfl⟩ : syracuseStep 1586153 = 1189615) B1189615
theorem B1587455 : Blo 1056613 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B69647609 : Blo 1056613 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B42352319 : Blo 1056613 42352319 := bstep (se 1 (by rfl) ⟨31764239, by rfl⟩ : syracuseStep 42352319 = 63528479) B63528479
theorem B1589243 : Blo 1056613 1589243 := bstep (se 1 (by rfl) ⟨1191932, by rfl⟩ : syracuseStep 1589243 = 2383865) B2383865
theorem B1590185 : Blo 1056613 1590185 := bstep (se 2 (by rfl) ⟨596319, by rfl⟩ : syracuseStep 1590185 = 1192639) B1192639
theorem B1788871 : Blo 1056613 1788871 := bstep (se 1 (by rfl) ⟨1341653, by rfl⟩ : syracuseStep 1788871 = 2683307) B2683307
theorem B2385215 : Blo 1056613 2385215 := bstep (se 1 (by rfl) ⟨1788911, by rfl⟩ : syracuseStep 2385215 = 3577823) B3577823
theorem B1697095 : Blo 1056613 1697095 := bstep (se 1 (by rfl) ⟨1272821, by rfl⟩ : syracuseStep 1697095 = 2545643) B2545643
theorem B4025447 : Blo 1056613 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B878506235 : Blo 1056613 878506235 := bstep (se 1 (by rfl) ⟨658879676, by rfl⟩ : syracuseStep 878506235 = 1317759353) B1317759353
theorem B6027007 : Blo 1056613 6027007 := bstep (se 1 (by rfl) ⟨4520255, by rfl⟩ : syracuseStep 6027007 = 9040511) B9040511
theorem B23203643 : Blo 1056613 23203643 := bstep (se 1 (by rfl) ⟨17402732, by rfl⟩ : syracuseStep 23203643 = 34805465) B34805465
theorem B9670889 : Blo 1056613 9670889 := bstep (se 2 (by rfl) ⟨3626583, by rfl⟩ : syracuseStep 9670889 = 7253167) B7253167
theorem B9051173 : Blo 1056613 9051173 := bstep (se 4 (by rfl) ⟨848547, by rfl⟩ : syracuseStep 9051173 = 1697095) B1697095
theorem B8036009 : Blo 1056613 8036009 := bstep (se 2 (by rfl) ⟨3013503, by rfl⟩ : syracuseStep 8036009 = 6027007) B6027007
theorem B1056831 : Blo 1056613 1056831 := bstep (se 1 (by rfl) ⟨792623, by rfl⟩ : syracuseStep 1056831 = 1585247) B1585247
theorem B585670823 : Blo 1056613 585670823 := bstep (se 1 (by rfl) ⟨439253117, by rfl⟩ : syracuseStep 585670823 = 878506235) B878506235
theorem B1057435 : Blo 1056613 1057435 := bstep (se 1 (by rfl) ⟨793076, by rfl⟩ : syracuseStep 1057435 = 1586153) B1586153
theorem B1058303 : Blo 1056613 1058303 := bstep (se 1 (by rfl) ⟨793727, by rfl⟩ : syracuseStep 1058303 = 1587455) B1587455
theorem B1059495 : Blo 1056613 1059495 := bstep (se 1 (by rfl) ⟨794621, by rfl⟩ : syracuseStep 1059495 = 1589243) B1589243
theorem B1060123 : Blo 1056613 1060123 := bstep (se 1 (by rfl) ⟨795092, by rfl⟩ : syracuseStep 1060123 = 1590185) B1590185
theorem B13938911 : Blo 1056613 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B8041355 : Blo 1056613 8041355 := bstep (se 1 (by rfl) ⟨6031016, by rfl⟩ : syracuseStep 8041355 = 12062033) B12062033
theorem B5354909 : Blo 1056613 5354909 := bstep (se 3 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 5354909 = 2008091) B2008091
theorem B1588361 : Blo 1056613 1588361 := bstep (se 2 (by rfl) ⟨595635, by rfl⟩ : syracuseStep 1588361 = 1191271) B1191271
theorem B1590143 : Blo 1056613 1590143 := bstep (se 1 (by rfl) ⟨1192607, by rfl⟩ : syracuseStep 1590143 = 2385215) B2385215
theorem B112939517 : Blo 1056613 112939517 := bstep (se 3 (by rfl) ⟨21176159, by rfl⟩ : syracuseStep 112939517 = 42352319) B42352319
theorem B13589471 : Blo 1056613 13589471 := bstep (se 1 (by rfl) ⟨10192103, by rfl⟩ : syracuseStep 13589471 = 20384207) B20384207
theorem B2383415 : Blo 1056613 2383415 := bstep (se 1 (by rfl) ⟨1787561, by rfl⟩ : syracuseStep 2383415 = 3575123) B3575123
theorem B2383919 : Blo 1056613 2383919 := bstep (se 1 (by rfl) ⟨1787939, by rfl⟩ : syracuseStep 2383919 = 3575879) B3575879
theorem B2385161 : Blo 1056613 2385161 := bstep (se 2 (by rfl) ⟨894435, by rfl⟩ : syracuseStep 2385161 = 1788871) B1788871
theorem B2683631 : Blo 1056613 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B2258779 : Blo 1056613 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B46431739 : Blo 1056613 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B6034115 : Blo 1056613 6034115 := bstep (se 1 (by rfl) ⟨4525586, by rfl⟩ : syracuseStep 6034115 = 9051173) B9051173
theorem B61908985 : Blo 1056613 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B1058907 : Blo 1056613 1058907 := bstep (se 1 (by rfl) ⟨794180, by rfl⟩ : syracuseStep 1058907 = 1588361) B1588361
theorem B61876381 : Blo 1056613 61876381 := bstep (se 3 (by rfl) ⟨11601821, by rfl⟩ : syracuseStep 61876381 = 23203643) B23203643
theorem B1060095 : Blo 1056613 1060095 := bstep (se 1 (by rfl) ⟨795071, by rfl⟩ : syracuseStep 1060095 = 1590143) B1590143
theorem B9059647 : Blo 1056613 9059647 := bstep (se 1 (by rfl) ⟨6794735, by rfl⟩ : syracuseStep 9059647 = 13589471) B13589471
theorem B1588943 : Blo 1056613 1588943 := bstep (se 1 (by rfl) ⟨1191707, by rfl⟩ : syracuseStep 1588943 = 2383415) B2383415
theorem B5357339 : Blo 1056613 5357339 := bstep (se 1 (by rfl) ⟨4018004, by rfl⟩ : syracuseStep 5357339 = 8036009) B8036009
theorem B1589279 : Blo 1056613 1589279 := bstep (se 1 (by rfl) ⟨1191959, by rfl⟩ : syracuseStep 1589279 = 2383919) B2383919
theorem B390447215 : Blo 1056613 390447215 := bstep (se 1 (by rfl) ⟨292835411, by rfl⟩ : syracuseStep 390447215 = 585670823) B585670823
theorem B1590107 : Blo 1056613 1590107 := bstep (se 1 (by rfl) ⟨1192580, by rfl⟩ : syracuseStep 1590107 = 2385161) B2385161
theorem B9292607 : Blo 1056613 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B1789087 : Blo 1056613 1789087 := bstep (se 1 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 1789087 = 2683631) B2683631
theorem B5360903 : Blo 1056613 5360903 := bstep (se 1 (by rfl) ⟨4020677, by rfl⟩ : syracuseStep 5360903 = 8041355) B8041355
theorem B6447259 : Blo 1056613 6447259 := bstep (se 1 (by rfl) ⟨4835444, by rfl⟩ : syracuseStep 6447259 = 9670889) B9670889
theorem B75293011 : Blo 1056613 75293011 := bstep (se 1 (by rfl) ⟨56469758, by rfl⟩ : syracuseStep 75293011 = 112939517) B112939517
theorem B3011705 : Blo 1056613 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B3569939 : Blo 1056613 3569939 := bstep (se 1 (by rfl) ⟨2677454, by rfl⟩ : syracuseStep 3569939 = 5354909) B5354909
theorem B6195071 : Blo 1056613 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B3573935 : Blo 1056613 3573935 := bstep (se 1 (by rfl) ⟨2680451, by rfl⟩ : syracuseStep 3573935 = 5360903) B5360903
theorem B82545313 : Blo 1056613 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B2007803 : Blo 1056613 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B1059295 : Blo 1056613 1059295 := bstep (se 1 (by rfl) ⟨794471, by rfl⟩ : syracuseStep 1059295 = 1588943) B1588943
theorem B1059519 : Blo 1056613 1059519 := bstep (se 1 (by rfl) ⟨794639, by rfl⟩ : syracuseStep 1059519 = 1589279) B1589279
theorem B1060071 : Blo 1056613 1060071 := bstep (se 1 (by rfl) ⟨795053, by rfl⟩ : syracuseStep 1060071 = 1590107) B1590107
theorem B34385381 : Blo 1056613 34385381 := bstep (se 4 (by rfl) ⟨3223629, by rfl⟩ : syracuseStep 34385381 = 6447259) B6447259
theorem B2379959 : Blo 1056613 2379959 := bstep (se 1 (by rfl) ⟨1784969, by rfl⟩ : syracuseStep 2379959 = 3569939) B3569939
theorem B12079529 : Blo 1056613 12079529 := bstep (se 2 (by rfl) ⟨4529823, by rfl⟩ : syracuseStep 12079529 = 9059647) B9059647
theorem B260298143 : Blo 1056613 260298143 := bstep (se 1 (by rfl) ⟨195223607, by rfl⟩ : syracuseStep 260298143 = 390447215) B390447215
theorem B100390681 : Blo 1056613 100390681 := bstep (se 2 (by rfl) ⟨37646505, by rfl⟩ : syracuseStep 100390681 = 75293011) B75293011
theorem B82501841 : Blo 1056613 82501841 := bstep (se 2 (by rfl) ⟨30938190, by rfl⟩ : syracuseStep 82501841 = 61876381) B61876381
theorem B4022743 : Blo 1056613 4022743 := bstep (se 1 (by rfl) ⟨3017057, by rfl⟩ : syracuseStep 4022743 = 6034115) B6034115
theorem B2385449 : Blo 1056613 2385449 := bstep (se 2 (by rfl) ⟨894543, by rfl⟩ : syracuseStep 2385449 = 1789087) B1789087
theorem B3571559 : Blo 1056613 3571559 := bstep (se 1 (by rfl) ⟨2678669, by rfl⟩ : syracuseStep 3571559 = 5357339) B5357339
theorem B220004909 : Blo 1056613 220004909 := bstep (se 3 (by rfl) ⟨41250920, by rfl⟩ : syracuseStep 220004909 = 82501841) B82501841
theorem B4130047 : Blo 1056613 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B1586639 : Blo 1056613 1586639 := bstep (se 1 (by rfl) ⟨1189979, by rfl⟩ : syracuseStep 1586639 = 2379959) B2379959
theorem B1590299 : Blo 1056613 1590299 := bstep (se 1 (by rfl) ⟨1192724, by rfl⟩ : syracuseStep 1590299 = 2385449) B2385449
theorem B22923587 : Blo 1056613 22923587 := bstep (se 1 (by rfl) ⟨17192690, by rfl⟩ : syracuseStep 22923587 = 34385381) B34385381
theorem B2381039 : Blo 1056613 2381039 := bstep (se 1 (by rfl) ⟨1785779, by rfl⟩ : syracuseStep 2381039 = 3571559) B3571559
theorem B5363657 : Blo 1056613 5363657 := bstep (se 2 (by rfl) ⟨2011371, by rfl⟩ : syracuseStep 5363657 = 4022743) B4022743
theorem B2382623 : Blo 1056613 2382623 := bstep (se 1 (by rfl) ⟨1786967, by rfl⟩ : syracuseStep 2382623 = 3573935) B3573935
theorem B8053019 : Blo 1056613 8053019 := bstep (se 1 (by rfl) ⟨6039764, by rfl⟩ : syracuseStep 8053019 = 12079529) B12079529
theorem B110060417 : Blo 1056613 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B173532095 : Blo 1056613 173532095 := bstep (se 1 (by rfl) ⟨130149071, by rfl⟩ : syracuseStep 173532095 = 260298143) B260298143
theorem B1338535 : Blo 1056613 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B133854241 : Blo 1056613 133854241 := bstep (se 2 (by rfl) ⟨50195340, by rfl⟩ : syracuseStep 133854241 = 100390681) B100390681
theorem B146669939 : Blo 1056613 146669939 := bstep (se 1 (by rfl) ⟨110002454, by rfl⟩ : syracuseStep 146669939 = 220004909) B220004909
theorem B3575771 : Blo 1056613 3575771 := bstep (se 1 (by rfl) ⟨2681828, by rfl⟩ : syracuseStep 3575771 = 5363657) B5363657
theorem B73373611 : Blo 1056613 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B22026917 : Blo 1056613 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B1057759 : Blo 1056613 1057759 := bstep (se 1 (by rfl) ⟨793319, by rfl⟩ : syracuseStep 1057759 = 1586639) B1586639
theorem B1060199 : Blo 1056613 1060199 := bstep (se 1 (by rfl) ⟨795149, by rfl⟩ : syracuseStep 1060199 = 1590299) B1590299
theorem B15282391 : Blo 1056613 15282391 := bstep (se 1 (by rfl) ⟨11461793, by rfl⟩ : syracuseStep 15282391 = 22923587) B22923587
theorem B1587359 : Blo 1056613 1587359 := bstep (se 1 (by rfl) ⟨1190519, by rfl⟩ : syracuseStep 1587359 = 2381039) B2381039
theorem B1784713 : Blo 1056613 1784713 := bstep (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) B1338535
theorem B1588415 : Blo 1056613 1588415 := bstep (se 1 (by rfl) ⟨1191311, by rfl⟩ : syracuseStep 1588415 = 2382623) B2382623
theorem B115688063 : Blo 1056613 115688063 := bstep (se 1 (by rfl) ⟨86766047, by rfl⟩ : syracuseStep 115688063 = 173532095) B173532095
theorem B178472321 : Blo 1056613 178472321 := bstep (se 2 (by rfl) ⟨66927120, by rfl⟩ : syracuseStep 178472321 = 133854241) B133854241
theorem B5368679 : Blo 1056613 5368679 := bstep (se 1 (by rfl) ⟨4026509, by rfl⟩ : syracuseStep 5368679 = 8053019) B8053019
theorem B97779959 : Blo 1056613 97779959 := bstep (se 1 (by rfl) ⟨73334969, by rfl⟩ : syracuseStep 97779959 = 146669939) B146669939
theorem B118981547 : Blo 1056613 118981547 := bstep (se 1 (by rfl) ⟨89236160, by rfl⟩ : syracuseStep 118981547 = 178472321) B178472321
theorem B14684611 : Blo 1056613 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B3579119 : Blo 1056613 3579119 := bstep (se 1 (by rfl) ⟨2684339, by rfl⟩ : syracuseStep 3579119 = 5368679) B5368679
theorem B1058239 : Blo 1056613 1058239 := bstep (se 1 (by rfl) ⟨793679, by rfl⟩ : syracuseStep 1058239 = 1587359) B1587359
theorem B1058943 : Blo 1056613 1058943 := bstep (se 1 (by rfl) ⟨794207, by rfl⟩ : syracuseStep 1058943 = 1588415) B1588415
theorem B97831481 : Blo 1056613 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B2379617 : Blo 1056613 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B77125375 : Blo 1056613 77125375 := bstep (se 1 (by rfl) ⟨57844031, by rfl⟩ : syracuseStep 77125375 = 115688063) B115688063
theorem B2383847 : Blo 1056613 2383847 := bstep (se 1 (by rfl) ⟨1787885, by rfl⟩ : syracuseStep 2383847 = 3575771) B3575771
theorem B20376521 : Blo 1056613 20376521 := bstep (se 2 (by rfl) ⟨7641195, by rfl⟩ : syracuseStep 20376521 = 15282391) B15282391
theorem B1043535797 : Blo 1056613 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B102833833 : Blo 1056613 102833833 := bstep (se 2 (by rfl) ⟨38562687, by rfl⟩ : syracuseStep 102833833 = 77125375) B77125375
theorem B65186639 : Blo 1056613 65186639 := bstep (se 1 (by rfl) ⟨48889979, by rfl⟩ : syracuseStep 65186639 = 97779959) B97779959
theorem B1586411 : Blo 1056613 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B1589231 : Blo 1056613 1589231 := bstep (se 1 (by rfl) ⟨1191923, by rfl⟩ : syracuseStep 1589231 = 2383847) B2383847
theorem B19579481 : Blo 1056613 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B13584347 : Blo 1056613 13584347 := bstep (se 1 (by rfl) ⟨10188260, by rfl⟩ : syracuseStep 13584347 = 20376521) B20376521
theorem B79321031 : Blo 1056613 79321031 := bstep (se 1 (by rfl) ⟨59490773, by rfl⟩ : syracuseStep 79321031 = 118981547) B118981547
theorem B2386079 : Blo 1056613 2386079 := bstep (se 1 (by rfl) ⟨1789559, by rfl⟩ : syracuseStep 2386079 = 3579119) B3579119
theorem B43457759 : Blo 1056613 43457759 := bstep (se 1 (by rfl) ⟨32593319, by rfl⟩ : syracuseStep 43457759 = 65186639) B65186639
theorem B1057607 : Blo 1056613 1057607 := bstep (se 1 (by rfl) ⟨793205, by rfl⟩ : syracuseStep 1057607 = 1586411) B1586411
theorem B137111777 : Blo 1056613 137111777 := bstep (se 2 (by rfl) ⟨51416916, by rfl⟩ : syracuseStep 137111777 = 102833833) B102833833
theorem B1059487 : Blo 1056613 1059487 := bstep (se 1 (by rfl) ⟨794615, by rfl⟩ : syracuseStep 1059487 = 1589231) B1589231
theorem B13052987 : Blo 1056613 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B9056231 : Blo 1056613 9056231 := bstep (se 1 (by rfl) ⟨6792173, by rfl⟩ : syracuseStep 9056231 = 13584347) B13584347
theorem B1590719 : Blo 1056613 1590719 := bstep (se 1 (by rfl) ⟨1193039, by rfl⟩ : syracuseStep 1590719 = 2386079) B2386079
theorem B695690531 : Blo 1056613 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B52880687 : Blo 1056613 52880687 := bstep (se 1 (by rfl) ⟨39660515, by rfl⟩ : syracuseStep 52880687 = 79321031) B79321031
theorem B28971839 : Blo 1056613 28971839 := bstep (se 1 (by rfl) ⟨21728879, by rfl⟩ : syracuseStep 28971839 = 43457759) B43457759
theorem B6037487 : Blo 1056613 6037487 := bstep (se 1 (by rfl) ⟨4528115, by rfl⟩ : syracuseStep 6037487 = 9056231) B9056231
theorem B1060479 : Blo 1056613 1060479 := bstep (se 1 (by rfl) ⟨795359, by rfl⟩ : syracuseStep 1060479 = 1590719) B1590719
theorem B91407851 : Blo 1056613 91407851 := bstep (se 1 (by rfl) ⟨68555888, by rfl⟩ : syracuseStep 91407851 = 137111777) B137111777
theorem B8701991 : Blo 1056613 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B463793687 : Blo 1056613 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B35253791 : Blo 1056613 35253791 := bstep (se 1 (by rfl) ⟨26440343, by rfl⟩ : syracuseStep 35253791 = 52880687) B52880687
theorem B5801327 : Blo 1056613 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B23502527 : Blo 1056613 23502527 := bstep (se 1 (by rfl) ⟨17626895, by rfl⟩ : syracuseStep 23502527 = 35253791) B35253791
theorem B19314559 : Blo 1056613 19314559 := bstep (se 1 (by rfl) ⟨14485919, by rfl⟩ : syracuseStep 19314559 = 28971839) B28971839
theorem B60938567 : Blo 1056613 60938567 := bstep (se 1 (by rfl) ⟨45703925, by rfl⟩ : syracuseStep 60938567 = 91407851) B91407851
theorem B4024991 : Blo 1056613 4024991 := bstep (se 1 (by rfl) ⟨3018743, by rfl⟩ : syracuseStep 4024991 = 6037487) B6037487
theorem B309195791 : Blo 1056613 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B3867551 : Blo 1056613 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B15668351 : Blo 1056613 15668351 := bstep (se 1 (by rfl) ⟨11751263, by rfl⟩ : syracuseStep 15668351 = 23502527) B23502527
theorem B206130527 : Blo 1056613 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B40625711 : Blo 1056613 40625711 := bstep (se 1 (by rfl) ⟨30469283, by rfl⟩ : syracuseStep 40625711 = 60938567) B60938567
theorem B2683327 : Blo 1056613 2683327 := bstep (se 1 (by rfl) ⟨2012495, by rfl⟩ : syracuseStep 2683327 = 4024991) B4024991
theorem B25752745 : Blo 1056613 25752745 := bstep (se 2 (by rfl) ⟨9657279, by rfl⟩ : syracuseStep 25752745 = 19314559) B19314559
theorem B3577769 : Blo 1056613 3577769 := bstep (se 2 (by rfl) ⟨1341663, by rfl⟩ : syracuseStep 3577769 = 2683327) B2683327
theorem B27083807 : Blo 1056613 27083807 := bstep (se 1 (by rfl) ⟨20312855, by rfl⟩ : syracuseStep 27083807 = 40625711) B40625711
theorem B137420351 : Blo 1056613 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B10445567 : Blo 1056613 10445567 := bstep (se 1 (by rfl) ⟨7834175, by rfl⟩ : syracuseStep 10445567 = 15668351) B15668351
theorem B34336993 : Blo 1056613 34336993 := bstep (se 2 (by rfl) ⟨12876372, by rfl⟩ : syracuseStep 34336993 = 25752745) B25752745
theorem B41253877 : Blo 1056613 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B18055871 : Blo 1056613 18055871 := bstep (se 1 (by rfl) ⟨13541903, by rfl⟩ : syracuseStep 18055871 = 27083807) B27083807
theorem B45782657 : Blo 1056613 45782657 := bstep (se 2 (by rfl) ⟨17168496, by rfl⟩ : syracuseStep 45782657 = 34336993) B34336993
theorem B111419381 : Blo 1056613 111419381 := bstep (se 5 (by rfl) ⟨5222783, by rfl⟩ : syracuseStep 111419381 = 10445567) B10445567
theorem B55005169 : Blo 1056613 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B2385179 : Blo 1056613 2385179 := bstep (se 1 (by rfl) ⟨1788884, by rfl⟩ : syracuseStep 2385179 = 3577769) B3577769
theorem B91613567 : Blo 1056613 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B73340225 : Blo 1056613 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B12037247 : Blo 1056613 12037247 := bstep (se 1 (by rfl) ⟨9027935, by rfl⟩ : syracuseStep 12037247 = 18055871) B18055871
theorem B30521771 : Blo 1056613 30521771 := bstep (se 1 (by rfl) ⟨22891328, by rfl⟩ : syracuseStep 30521771 = 45782657) B45782657
theorem B1590119 : Blo 1056613 1590119 := bstep (se 1 (by rfl) ⟨1192589, by rfl⟩ : syracuseStep 1590119 = 2385179) B2385179
theorem B74279587 : Blo 1056613 74279587 := bstep (se 1 (by rfl) ⟨55709690, by rfl⟩ : syracuseStep 74279587 = 111419381) B111419381
theorem B61075711 : Blo 1056613 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B48893483 : Blo 1056613 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B81434281 : Blo 1056613 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B1060079 : Blo 1056613 1060079 := bstep (se 1 (by rfl) ⟨795059, by rfl⟩ : syracuseStep 1060079 = 1590119) B1590119
theorem B99039449 : Blo 1056613 99039449 := bstep (se 2 (by rfl) ⟨37139793, by rfl⟩ : syracuseStep 99039449 = 74279587) B74279587
theorem B8024831 : Blo 1056613 8024831 := bstep (se 1 (by rfl) ⟨6018623, by rfl⟩ : syracuseStep 8024831 = 12037247) B12037247
theorem B20347847 : Blo 1056613 20347847 := bstep (se 1 (by rfl) ⟨15260885, by rfl⟩ : syracuseStep 20347847 = 30521771) B30521771
theorem B5349887 : Blo 1056613 5349887 := bstep (se 1 (by rfl) ⟨4012415, by rfl⟩ : syracuseStep 5349887 = 8024831) B8024831
theorem B108579041 : Blo 1056613 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B264105197 : Blo 1056613 264105197 := bstep (se 3 (by rfl) ⟨49519724, by rfl⟩ : syracuseStep 264105197 = 99039449) B99039449
theorem B130382621 : Blo 1056613 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B13565231 : Blo 1056613 13565231 := bstep (se 1 (by rfl) ⟨10173923, by rfl⟩ : syracuseStep 13565231 = 20347847) B20347847
theorem B72386027 : Blo 1056613 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B176070131 : Blo 1056613 176070131 := bstep (se 1 (by rfl) ⟨132052598, by rfl⟩ : syracuseStep 176070131 = 264105197) B264105197
theorem B86921747 : Blo 1056613 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B3566591 : Blo 1056613 3566591 := bstep (se 1 (by rfl) ⟨2674943, by rfl⟩ : syracuseStep 3566591 = 5349887) B5349887
theorem B9043487 : Blo 1056613 9043487 := bstep (se 1 (by rfl) ⟨6782615, by rfl⟩ : syracuseStep 9043487 = 13565231) B13565231
theorem B117380087 : Blo 1056613 117380087 := bstep (se 1 (by rfl) ⟨88035065, by rfl⟩ : syracuseStep 117380087 = 176070131) B176070131
theorem B57947831 : Blo 1056613 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B2377727 : Blo 1056613 2377727 := bstep (se 1 (by rfl) ⟨1783295, by rfl⟩ : syracuseStep 2377727 = 3566591) B3566591
theorem B48257351 : Blo 1056613 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B6028991 : Blo 1056613 6028991 := bstep (se 1 (by rfl) ⟨4521743, by rfl⟩ : syracuseStep 6028991 = 9043487) B9043487
theorem B78253391 : Blo 1056613 78253391 := bstep (se 1 (by rfl) ⟨58690043, by rfl⟩ : syracuseStep 78253391 = 117380087) B117380087
theorem B1585151 : Blo 1056613 1585151 := bstep (se 1 (by rfl) ⟨1188863, by rfl⟩ : syracuseStep 1585151 = 2377727) B2377727
theorem B4019327 : Blo 1056613 4019327 := bstep (se 1 (by rfl) ⟨3014495, by rfl⟩ : syracuseStep 4019327 = 6028991) B6028991
theorem B32171567 : Blo 1056613 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B38631887 : Blo 1056613 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B85790845 : Blo 1056613 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B1056767 : Blo 1056613 1056767 := bstep (se 1 (by rfl) ⟨792575, by rfl⟩ : syracuseStep 1056767 = 1585151) B1585151
theorem B208675709 : Blo 1056613 208675709 := bstep (se 3 (by rfl) ⟨39126695, by rfl⟩ : syracuseStep 208675709 = 78253391) B78253391
theorem B2679551 : Blo 1056613 2679551 := bstep (se 1 (by rfl) ⟨2009663, by rfl⟩ : syracuseStep 2679551 = 4019327) B4019327
theorem B25754591 : Blo 1056613 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B457551173 : Blo 1056613 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B1786367 : Blo 1056613 1786367 := bstep (se 1 (by rfl) ⟨1339775, by rfl⟩ : syracuseStep 1786367 = 2679551) B2679551
theorem B139117139 : Blo 1056613 139117139 := bstep (se 1 (by rfl) ⟨104337854, by rfl⟩ : syracuseStep 139117139 = 208675709) B208675709
theorem B17169727 : Blo 1056613 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B1190911 : Blo 1056613 1190911 := bstep (se 1 (by rfl) ⟨893183, by rfl⟩ : syracuseStep 1190911 = 1786367) B1786367
theorem B92744759 : Blo 1056613 92744759 := bstep (se 1 (by rfl) ⟨69558569, by rfl⟩ : syracuseStep 92744759 = 139117139) B139117139
theorem B22892969 : Blo 1056613 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B305034115 : Blo 1056613 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B1587881 : Blo 1056613 1587881 := bstep (se 2 (by rfl) ⟨595455, by rfl⟩ : syracuseStep 1587881 = 1190911) B1190911
theorem B15261979 : Blo 1056613 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B406712153 : Blo 1056613 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B61829839 : Blo 1056613 61829839 := bstep (se 1 (by rfl) ⟨46372379, by rfl⟩ : syracuseStep 61829839 = 92744759) B92744759
theorem B20349305 : Blo 1056613 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B1058587 : Blo 1056613 1058587 := bstep (se 1 (by rfl) ⟨793940, by rfl⟩ : syracuseStep 1058587 = 1587881) B1587881
theorem B271141435 : Blo 1056613 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B82439785 : Blo 1056613 82439785 := bstep (se 2 (by rfl) ⟨30914919, by rfl⟩ : syracuseStep 82439785 = 61829839) B61829839
theorem B13566203 : Blo 1056613 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B1446087653 : Blo 1056613 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B109919713 : Blo 1056613 109919713 := bstep (se 2 (by rfl) ⟨41219892, by rfl⟩ : syracuseStep 109919713 = 82439785) B82439785
theorem B9044135 : Blo 1056613 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B146559617 : Blo 1056613 146559617 := bstep (se 2 (by rfl) ⟨54959856, by rfl⟩ : syracuseStep 146559617 = 109919713) B109919713
theorem B964058435 : Blo 1056613 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B6029423 : Blo 1056613 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B97706411 : Blo 1056613 97706411 := bstep (se 1 (by rfl) ⟨73279808, by rfl⟩ : syracuseStep 97706411 = 146559617) B146559617
theorem B642705623 : Blo 1056613 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B4019615 : Blo 1056613 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B65137607 : Blo 1056613 65137607 := bstep (se 1 (by rfl) ⟨48853205, by rfl⟩ : syracuseStep 65137607 = 97706411) B97706411
theorem B428470415 : Blo 1056613 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B43425071 : Blo 1056613 43425071 := bstep (se 1 (by rfl) ⟨32568803, by rfl⟩ : syracuseStep 43425071 = 65137607) B65137607
theorem B285646943 : Blo 1056613 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B2679743 : Blo 1056613 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B761725181 : Blo 1056613 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B28950047 : Blo 1056613 28950047 := bstep (se 1 (by rfl) ⟨21712535, by rfl⟩ : syracuseStep 28950047 = 43425071) B43425071
theorem B1786495 : Blo 1056613 1786495 := bstep (se 1 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 1786495 = 2679743) B2679743
theorem B507816787 : Blo 1056613 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B2381993 : Blo 1056613 2381993 := bstep (se 2 (by rfl) ⟨893247, by rfl⟩ : syracuseStep 2381993 = 1786495) B1786495
theorem B19300031 : Blo 1056613 19300031 := bstep (se 1 (by rfl) ⟨14475023, by rfl⟩ : syracuseStep 19300031 = 28950047) B28950047
theorem B677089049 : Blo 1056613 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1587995 : Blo 1056613 1587995 := bstep (se 1 (by rfl) ⟨1190996, by rfl⟩ : syracuseStep 1587995 = 2381993) B2381993
theorem B12866687 : Blo 1056613 12866687 := bstep (se 1 (by rfl) ⟨9650015, by rfl⟩ : syracuseStep 12866687 = 19300031) B19300031
theorem B1058663 : Blo 1056613 1058663 := bstep (se 1 (by rfl) ⟨793997, by rfl⟩ : syracuseStep 1058663 = 1587995) B1587995
theorem B1805570797 : Blo 1056613 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B8577791 : Blo 1056613 8577791 := bstep (se 1 (by rfl) ⟨6433343, by rfl⟩ : syracuseStep 8577791 = 12866687) B12866687
theorem B5718527 : Blo 1056613 5718527 := bstep (se 1 (by rfl) ⟨4288895, by rfl⟩ : syracuseStep 5718527 = 8577791) B8577791
theorem B2407427729 : Blo 1056613 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 1056613 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B3812351 : Blo 1056613 3812351 := bstep (se 1 (by rfl) ⟨2859263, by rfl⟩ : syracuseStep 3812351 = 5718527) B5718527
theorem B1069967879 : Blo 1056613 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B40665077 : Blo 1056613 40665077 := bstep (se 5 (by rfl) ⟨1906175, by rfl⟩ : syracuseStep 40665077 = 3812351) B3812351
theorem B27110051 : Blo 1056613 27110051 := bstep (se 1 (by rfl) ⟨20332538, by rfl⟩ : syracuseStep 27110051 = 40665077) B40665077
theorem B713311919 : Blo 1056613 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 1056613 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B18073367 : Blo 1056613 18073367 := bstep (se 1 (by rfl) ⟨13555025, by rfl⟩ : syracuseStep 18073367 = 27110051) B27110051
theorem B12048911 : Blo 1056613 12048911 := bstep (se 1 (by rfl) ⟨9036683, by rfl⟩ : syracuseStep 12048911 = 18073367) B18073367
theorem B317027519 : Blo 1056613 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B8032607 : Blo 1056613 8032607 := bstep (se 1 (by rfl) ⟨6024455, by rfl⟩ : syracuseStep 8032607 = 12048911) B12048911
theorem B211351679 : Blo 1056613 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B5355071 : Blo 1056613 5355071 := bstep (se 1 (by rfl) ⟨4016303, by rfl⟩ : syracuseStep 5355071 = 8032607) B8032607
theorem B140901119 : Blo 1056613 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 1056613 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B3570047 : Blo 1056613 3570047 := bstep (se 1 (by rfl) ⟨2677535, by rfl⟩ : syracuseStep 3570047 = 5355071) B5355071
theorem B62622719 : Blo 1056613 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B2380031 : Blo 1056613 2380031 := bstep (se 1 (by rfl) ⟨1785023, by rfl⟩ : syracuseStep 2380031 = 3570047) B3570047
theorem B41748479 : Blo 1056613 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B1586687 : Blo 1056613 1586687 := bstep (se 1 (by rfl) ⟨1190015, by rfl⟩ : syracuseStep 1586687 = 2380031) B2380031
theorem B1057791 : Blo 1056613 1057791 := bstep (se 1 (by rfl) ⟨793343, by rfl⟩ : syracuseStep 1057791 = 1586687) B1586687
theorem B27832319 : Blo 1056613 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 1056613 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 1056613 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 1056613 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 1056613 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 1056613 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 1056613 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 1056613 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 1056613 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 1056613 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 1056613 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 1056613 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 1056613 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 1056613 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 1056613 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 1056613 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 1056613 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 1056613 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 1056613 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 1056613 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 1056613 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 1056613 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 1056613 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 1056613 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 1056613 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 1056613 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 1056613 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 1056613 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 1056613 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B1783579 : Blo 1056613 1783579 := bstep (se 1 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 1783579 = 2675369) B2675369
theorem B2378105 : Blo 1056613 2378105 := bstep (se 2 (by rfl) ⟨891789, by rfl⟩ : syracuseStep 2378105 = 1783579) B1783579
theorem B1585403 : Blo 1056613 1585403 := bstep (se 1 (by rfl) ⟨1189052, by rfl⟩ : syracuseStep 1585403 = 2378105) B2378105
theorem B1056935 : Blo 1056613 1056935 := bstep (se 1 (by rfl) ⟨792701, by rfl⟩ : syracuseStep 1056935 = 1585403) B1585403

theorem C0 (j : ℕ) (h1 : 264153 ≤ j) (h2 : j ≤ 264852) : Blo 1056613 (4 * j + 3) := by
  interval_cases j
  · exact B1056615
  · exact B1056619
  · exact B1056623
  · exact B1056627
  · exact B1056631
  · exact B1056635
  · exact B1056639
  · exact B1056643
  · exact B1056647
  · exact B1056651
  · exact B1056655
  · exact B1056659
  · exact B1056663
  · exact B1056667
  · exact B1056671
  · exact B1056675
  · exact B1056679
  · exact B1056683
  · exact B1056687
  · exact B1056691
  · exact B1056695
  · exact B1056699
  · exact B1056703
  · exact B1056707
  · exact B1056711
  · exact B1056715
  · exact B1056719
  · exact B1056723
  · exact B1056727
  · exact B1056731
  · exact B1056735
  · exact B1056739
  · exact B1056743
  · exact B1056747
  · exact B1056751
  · exact B1056755
  · exact B1056759
  · exact B1056763
  · exact B1056767
  · exact B1056771
  · exact B1056775
  · exact B1056779
  · exact B1056783
  · exact B1056787
  · exact B1056791
  · exact B1056795
  · exact B1056799
  · exact B1056803
  · exact B1056807
  · exact B1056811
  · exact B1056815
  · exact B1056819
  · exact B1056823
  · exact B1056827
  · exact B1056831
  · exact B1056835
  · exact B1056839
  · exact B1056843
  · exact B1056847
  · exact B1056851
  · exact B1056855
  · exact B1056859
  · exact B1056863
  · exact B1056867
  · exact B1056871
  · exact B1056875
  · exact B1056879
  · exact B1056883
  · exact B1056887
  · exact B1056891
  · exact B1056895
  · exact B1056899
  · exact B1056903
  · exact B1056907
  · exact B1056911
  · exact B1056915
  · exact B1056919
  · exact B1056923
  · exact B1056927
  · exact B1056931
  · exact B1056935
  · exact B1056939
  · exact B1056943
  · exact B1056947
  · exact B1056951
  · exact B1056955
  · exact B1056959
  · exact B1056963
  · exact B1056967
  · exact B1056971
  · exact B1056975
  · exact B1056979
  · exact B1056983
  · exact B1056987
  · exact B1056991
  · exact B1056995
  · exact B1056999
  · exact B1057003
  · exact B1057007
  · exact B1057011
  · exact B1057015
  · exact B1057019
  · exact B1057023
  · exact B1057027
  · exact B1057031
  · exact B1057035
  · exact B1057039
  · exact B1057043
  · exact B1057047
  · exact B1057051
  · exact B1057055
  · exact B1057059
  · exact B1057063
  · exact B1057067
  · exact B1057071
  · exact B1057075
  · exact B1057079
  · exact B1057083
  · exact B1057087
  · exact B1057091
  · exact B1057095
  · exact B1057099
  · exact B1057103
  · exact B1057107
  · exact B1057111
  · exact B1057115
  · exact B1057119
  · exact B1057123
  · exact B1057127
  · exact B1057131
  · exact B1057135
  · exact B1057139
  · exact B1057143
  · exact B1057147
  · exact B1057151
  · exact B1057155
  · exact B1057159
  · exact B1057163
  · exact B1057167
  · exact B1057171
  · exact B1057175
  · exact B1057179
  · exact B1057183
  · exact B1057187
  · exact B1057191
  · exact B1057195
  · exact B1057199
  · exact B1057203
  · exact B1057207
  · exact B1057211
  · exact B1057215
  · exact B1057219
  · exact B1057223
  · exact B1057227
  · exact B1057231
  · exact B1057235
  · exact B1057239
  · exact B1057243
  · exact B1057247
  · exact B1057251
  · exact B1057255
  · exact B1057259
  · exact B1057263
  · exact B1057267
  · exact B1057271
  · exact B1057275
  · exact B1057279
  · exact B1057283
  · exact B1057287
  · exact B1057291
  · exact B1057295
  · exact B1057299
  · exact B1057303
  · exact B1057307
  · exact B1057311
  · exact B1057315
  · exact B1057319
  · exact B1057323
  · exact B1057327
  · exact B1057331
  · exact B1057335
  · exact B1057339
  · exact B1057343
  · exact B1057347
  · exact B1057351
  · exact B1057355
  · exact B1057359
  · exact B1057363
  · exact B1057367
  · exact B1057371
  · exact B1057375
  · exact B1057379
  · exact B1057383
  · exact B1057387
  · exact B1057391
  · exact B1057395
  · exact B1057399
  · exact B1057403
  · exact B1057407
  · exact B1057411
  · exact B1057415
  · exact B1057419
  · exact B1057423
  · exact B1057427
  · exact B1057431
  · exact B1057435
  · exact B1057439
  · exact B1057443
  · exact B1057447
  · exact B1057451
  · exact B1057455
  · exact B1057459
  · exact B1057463
  · exact B1057467
  · exact B1057471
  · exact B1057475
  · exact B1057479
  · exact B1057483
  · exact B1057487
  · exact B1057491
  · exact B1057495
  · exact B1057499
  · exact B1057503
  · exact B1057507
  · exact B1057511
  · exact B1057515
  · exact B1057519
  · exact B1057523
  · exact B1057527
  · exact B1057531
  · exact B1057535
  · exact B1057539
  · exact B1057543
  · exact B1057547
  · exact B1057551
  · exact B1057555
  · exact B1057559
  · exact B1057563
  · exact B1057567
  · exact B1057571
  · exact B1057575
  · exact B1057579
  · exact B1057583
  · exact B1057587
  · exact B1057591
  · exact B1057595
  · exact B1057599
  · exact B1057603
  · exact B1057607
  · exact B1057611
  · exact B1057615
  · exact B1057619
  · exact B1057623
  · exact B1057627
  · exact B1057631
  · exact B1057635
  · exact B1057639
  · exact B1057643
  · exact B1057647
  · exact B1057651
  · exact B1057655
  · exact B1057659
  · exact B1057663
  · exact B1057667
  · exact B1057671
  · exact B1057675
  · exact B1057679
  · exact B1057683
  · exact B1057687
  · exact B1057691
  · exact B1057695
  · exact B1057699
  · exact B1057703
  · exact B1057707
  · exact B1057711
  · exact B1057715
  · exact B1057719
  · exact B1057723
  · exact B1057727
  · exact B1057731
  · exact B1057735
  · exact B1057739
  · exact B1057743
  · exact B1057747
  · exact B1057751
  · exact B1057755
  · exact B1057759
  · exact B1057763
  · exact B1057767
  · exact B1057771
  · exact B1057775
  · exact B1057779
  · exact B1057783
  · exact B1057787
  · exact B1057791
  · exact B1057795
  · exact B1057799
  · exact B1057803
  · exact B1057807
  · exact B1057811
  · exact B1057815
  · exact B1057819
  · exact B1057823
  · exact B1057827
  · exact B1057831
  · exact B1057835
  · exact B1057839
  · exact B1057843
  · exact B1057847
  · exact B1057851
  · exact B1057855
  · exact B1057859
  · exact B1057863
  · exact B1057867
  · exact B1057871
  · exact B1057875
  · exact B1057879
  · exact B1057883
  · exact B1057887
  · exact B1057891
  · exact B1057895
  · exact B1057899
  · exact B1057903
  · exact B1057907
  · exact B1057911
  · exact B1057915
  · exact B1057919
  · exact B1057923
  · exact B1057927
  · exact B1057931
  · exact B1057935
  · exact B1057939
  · exact B1057943
  · exact B1057947
  · exact B1057951
  · exact B1057955
  · exact B1057959
  · exact B1057963
  · exact B1057967
  · exact B1057971
  · exact B1057975
  · exact B1057979
  · exact B1057983
  · exact B1057987
  · exact B1057991
  · exact B1057995
  · exact B1057999
  · exact B1058003
  · exact B1058007
  · exact B1058011
  · exact B1058015
  · exact B1058019
  · exact B1058023
  · exact B1058027
  · exact B1058031
  · exact B1058035
  · exact B1058039
  · exact B1058043
  · exact B1058047
  · exact B1058051
  · exact B1058055
  · exact B1058059
  · exact B1058063
  · exact B1058067
  · exact B1058071
  · exact B1058075
  · exact B1058079
  · exact B1058083
  · exact B1058087
  · exact B1058091
  · exact B1058095
  · exact B1058099
  · exact B1058103
  · exact B1058107
  · exact B1058111
  · exact B1058115
  · exact B1058119
  · exact B1058123
  · exact B1058127
  · exact B1058131
  · exact B1058135
  · exact B1058139
  · exact B1058143
  · exact B1058147
  · exact B1058151
  · exact B1058155
  · exact B1058159
  · exact B1058163
  · exact B1058167
  · exact B1058171
  · exact B1058175
  · exact B1058179
  · exact B1058183
  · exact B1058187
  · exact B1058191
  · exact B1058195
  · exact B1058199
  · exact B1058203
  · exact B1058207
  · exact B1058211
  · exact B1058215
  · exact B1058219
  · exact B1058223
  · exact B1058227
  · exact B1058231
  · exact B1058235
  · exact B1058239
  · exact B1058243
  · exact B1058247
  · exact B1058251
  · exact B1058255
  · exact B1058259
  · exact B1058263
  · exact B1058267
  · exact B1058271
  · exact B1058275
  · exact B1058279
  · exact B1058283
  · exact B1058287
  · exact B1058291
  · exact B1058295
  · exact B1058299
  · exact B1058303
  · exact B1058307
  · exact B1058311
  · exact B1058315
  · exact B1058319
  · exact B1058323
  · exact B1058327
  · exact B1058331
  · exact B1058335
  · exact B1058339
  · exact B1058343
  · exact B1058347
  · exact B1058351
  · exact B1058355
  · exact B1058359
  · exact B1058363
  · exact B1058367
  · exact B1058371
  · exact B1058375
  · exact B1058379
  · exact B1058383
  · exact B1058387
  · exact B1058391
  · exact B1058395
  · exact B1058399
  · exact B1058403
  · exact B1058407
  · exact B1058411
  · exact B1058415
  · exact B1058419
  · exact B1058423
  · exact B1058427
  · exact B1058431
  · exact B1058435
  · exact B1058439
  · exact B1058443
  · exact B1058447
  · exact B1058451
  · exact B1058455
  · exact B1058459
  · exact B1058463
  · exact B1058467
  · exact B1058471
  · exact B1058475
  · exact B1058479
  · exact B1058483
  · exact B1058487
  · exact B1058491
  · exact B1058495
  · exact B1058499
  · exact B1058503
  · exact B1058507
  · exact B1058511
  · exact B1058515
  · exact B1058519
  · exact B1058523
  · exact B1058527
  · exact B1058531
  · exact B1058535
  · exact B1058539
  · exact B1058543
  · exact B1058547
  · exact B1058551
  · exact B1058555
  · exact B1058559
  · exact B1058563
  · exact B1058567
  · exact B1058571
  · exact B1058575
  · exact B1058579
  · exact B1058583
  · exact B1058587
  · exact B1058591
  · exact B1058595
  · exact B1058599
  · exact B1058603
  · exact B1058607
  · exact B1058611
  · exact B1058615
  · exact B1058619
  · exact B1058623
  · exact B1058627
  · exact B1058631
  · exact B1058635
  · exact B1058639
  · exact B1058643
  · exact B1058647
  · exact B1058651
  · exact B1058655
  · exact B1058659
  · exact B1058663
  · exact B1058667
  · exact B1058671
  · exact B1058675
  · exact B1058679
  · exact B1058683
  · exact B1058687
  · exact B1058691
  · exact B1058695
  · exact B1058699
  · exact B1058703
  · exact B1058707
  · exact B1058711
  · exact B1058715
  · exact B1058719
  · exact B1058723
  · exact B1058727
  · exact B1058731
  · exact B1058735
  · exact B1058739
  · exact B1058743
  · exact B1058747
  · exact B1058751
  · exact B1058755
  · exact B1058759
  · exact B1058763
  · exact B1058767
  · exact B1058771
  · exact B1058775
  · exact B1058779
  · exact B1058783
  · exact B1058787
  · exact B1058791
  · exact B1058795
  · exact B1058799
  · exact B1058803
  · exact B1058807
  · exact B1058811
  · exact B1058815
  · exact B1058819
  · exact B1058823
  · exact B1058827
  · exact B1058831
  · exact B1058835
  · exact B1058839
  · exact B1058843
  · exact B1058847
  · exact B1058851
  · exact B1058855
  · exact B1058859
  · exact B1058863
  · exact B1058867
  · exact B1058871
  · exact B1058875
  · exact B1058879
  · exact B1058883
  · exact B1058887
  · exact B1058891
  · exact B1058895
  · exact B1058899
  · exact B1058903
  · exact B1058907
  · exact B1058911
  · exact B1058915
  · exact B1058919
  · exact B1058923
  · exact B1058927
  · exact B1058931
  · exact B1058935
  · exact B1058939
  · exact B1058943
  · exact B1058947
  · exact B1058951
  · exact B1058955
  · exact B1058959
  · exact B1058963
  · exact B1058967
  · exact B1058971
  · exact B1058975
  · exact B1058979
  · exact B1058983
  · exact B1058987
  · exact B1058991
  · exact B1058995
  · exact B1058999
  · exact B1059003
  · exact B1059007
  · exact B1059011
  · exact B1059015
  · exact B1059019
  · exact B1059023
  · exact B1059027
  · exact B1059031
  · exact B1059035
  · exact B1059039
  · exact B1059043
  · exact B1059047
  · exact B1059051
  · exact B1059055
  · exact B1059059
  · exact B1059063
  · exact B1059067
  · exact B1059071
  · exact B1059075
  · exact B1059079
  · exact B1059083
  · exact B1059087
  · exact B1059091
  · exact B1059095
  · exact B1059099
  · exact B1059103
  · exact B1059107
  · exact B1059111
  · exact B1059115
  · exact B1059119
  · exact B1059123
  · exact B1059127
  · exact B1059131
  · exact B1059135
  · exact B1059139
  · exact B1059143
  · exact B1059147
  · exact B1059151
  · exact B1059155
  · exact B1059159
  · exact B1059163
  · exact B1059167
  · exact B1059171
  · exact B1059175
  · exact B1059179
  · exact B1059183
  · exact B1059187
  · exact B1059191
  · exact B1059195
  · exact B1059199
  · exact B1059203
  · exact B1059207
  · exact B1059211
  · exact B1059215
  · exact B1059219
  · exact B1059223
  · exact B1059227
  · exact B1059231
  · exact B1059235
  · exact B1059239
  · exact B1059243
  · exact B1059247
  · exact B1059251
  · exact B1059255
  · exact B1059259
  · exact B1059263
  · exact B1059267
  · exact B1059271
  · exact B1059275
  · exact B1059279
  · exact B1059283
  · exact B1059287
  · exact B1059291
  · exact B1059295
  · exact B1059299
  · exact B1059303
  · exact B1059307
  · exact B1059311
  · exact B1059315
  · exact B1059319
  · exact B1059323
  · exact B1059327
  · exact B1059331
  · exact B1059335
  · exact B1059339
  · exact B1059343
  · exact B1059347
  · exact B1059351
  · exact B1059355
  · exact B1059359
  · exact B1059363
  · exact B1059367
  · exact B1059371
  · exact B1059375
  · exact B1059379
  · exact B1059383
  · exact B1059387
  · exact B1059391
  · exact B1059395
  · exact B1059399
  · exact B1059403
  · exact B1059407
  · exact B1059411

theorem C1 (j : ℕ) (h1 : 264853 ≤ j) (h2 : j ≤ 265152) : Blo 1056613 (4 * j + 3) := by
  interval_cases j
  · exact B1059415
  · exact B1059419
  · exact B1059423
  · exact B1059427
  · exact B1059431
  · exact B1059435
  · exact B1059439
  · exact B1059443
  · exact B1059447
  · exact B1059451
  · exact B1059455
  · exact B1059459
  · exact B1059463
  · exact B1059467
  · exact B1059471
  · exact B1059475
  · exact B1059479
  · exact B1059483
  · exact B1059487
  · exact B1059491
  · exact B1059495
  · exact B1059499
  · exact B1059503
  · exact B1059507
  · exact B1059511
  · exact B1059515
  · exact B1059519
  · exact B1059523
  · exact B1059527
  · exact B1059531
  · exact B1059535
  · exact B1059539
  · exact B1059543
  · exact B1059547
  · exact B1059551
  · exact B1059555
  · exact B1059559
  · exact B1059563
  · exact B1059567
  · exact B1059571
  · exact B1059575
  · exact B1059579
  · exact B1059583
  · exact B1059587
  · exact B1059591
  · exact B1059595
  · exact B1059599
  · exact B1059603
  · exact B1059607
  · exact B1059611
  · exact B1059615
  · exact B1059619
  · exact B1059623
  · exact B1059627
  · exact B1059631
  · exact B1059635
  · exact B1059639
  · exact B1059643
  · exact B1059647
  · exact B1059651
  · exact B1059655
  · exact B1059659
  · exact B1059663
  · exact B1059667
  · exact B1059671
  · exact B1059675
  · exact B1059679
  · exact B1059683
  · exact B1059687
  · exact B1059691
  · exact B1059695
  · exact B1059699
  · exact B1059703
  · exact B1059707
  · exact B1059711
  · exact B1059715
  · exact B1059719
  · exact B1059723
  · exact B1059727
  · exact B1059731
  · exact B1059735
  · exact B1059739
  · exact B1059743
  · exact B1059747
  · exact B1059751
  · exact B1059755
  · exact B1059759
  · exact B1059763
  · exact B1059767
  · exact B1059771
  · exact B1059775
  · exact B1059779
  · exact B1059783
  · exact B1059787
  · exact B1059791
  · exact B1059795
  · exact B1059799
  · exact B1059803
  · exact B1059807
  · exact B1059811
  · exact B1059815
  · exact B1059819
  · exact B1059823
  · exact B1059827
  · exact B1059831
  · exact B1059835
  · exact B1059839
  · exact B1059843
  · exact B1059847
  · exact B1059851
  · exact B1059855
  · exact B1059859
  · exact B1059863
  · exact B1059867
  · exact B1059871
  · exact B1059875
  · exact B1059879
  · exact B1059883
  · exact B1059887
  · exact B1059891
  · exact B1059895
  · exact B1059899
  · exact B1059903
  · exact B1059907
  · exact B1059911
  · exact B1059915
  · exact B1059919
  · exact B1059923
  · exact B1059927
  · exact B1059931
  · exact B1059935
  · exact B1059939
  · exact B1059943
  · exact B1059947
  · exact B1059951
  · exact B1059955
  · exact B1059959
  · exact B1059963
  · exact B1059967
  · exact B1059971
  · exact B1059975
  · exact B1059979
  · exact B1059983
  · exact B1059987
  · exact B1059991
  · exact B1059995
  · exact B1059999
  · exact B1060003
  · exact B1060007
  · exact B1060011
  · exact B1060015
  · exact B1060019
  · exact B1060023
  · exact B1060027
  · exact B1060031
  · exact B1060035
  · exact B1060039
  · exact B1060043
  · exact B1060047
  · exact B1060051
  · exact B1060055
  · exact B1060059
  · exact B1060063
  · exact B1060067
  · exact B1060071
  · exact B1060075
  · exact B1060079
  · exact B1060083
  · exact B1060087
  · exact B1060091
  · exact B1060095
  · exact B1060099
  · exact B1060103
  · exact B1060107
  · exact B1060111
  · exact B1060115
  · exact B1060119
  · exact B1060123
  · exact B1060127
  · exact B1060131
  · exact B1060135
  · exact B1060139
  · exact B1060143
  · exact B1060147
  · exact B1060151
  · exact B1060155
  · exact B1060159
  · exact B1060163
  · exact B1060167
  · exact B1060171
  · exact B1060175
  · exact B1060179
  · exact B1060183
  · exact B1060187
  · exact B1060191
  · exact B1060195
  · exact B1060199
  · exact B1060203
  · exact B1060207
  · exact B1060211
  · exact B1060215
  · exact B1060219
  · exact B1060223
  · exact B1060227
  · exact B1060231
  · exact B1060235
  · exact B1060239
  · exact B1060243
  · exact B1060247
  · exact B1060251
  · exact B1060255
  · exact B1060259
  · exact B1060263
  · exact B1060267
  · exact B1060271
  · exact B1060275
  · exact B1060279
  · exact B1060283
  · exact B1060287
  · exact B1060291
  · exact B1060295
  · exact B1060299
  · exact B1060303
  · exact B1060307
  · exact B1060311
  · exact B1060315
  · exact B1060319
  · exact B1060323
  · exact B1060327
  · exact B1060331
  · exact B1060335
  · exact B1060339
  · exact B1060343
  · exact B1060347
  · exact B1060351
  · exact B1060355
  · exact B1060359
  · exact B1060363
  · exact B1060367
  · exact B1060371
  · exact B1060375
  · exact B1060379
  · exact B1060383
  · exact B1060387
  · exact B1060391
  · exact B1060395
  · exact B1060399
  · exact B1060403
  · exact B1060407
  · exact B1060411
  · exact B1060415
  · exact B1060419
  · exact B1060423
  · exact B1060427
  · exact B1060431
  · exact B1060435
  · exact B1060439
  · exact B1060443
  · exact B1060447
  · exact B1060451
  · exact B1060455
  · exact B1060459
  · exact B1060463
  · exact B1060467
  · exact B1060471
  · exact B1060475
  · exact B1060479
  · exact B1060483
  · exact B1060487
  · exact B1060491
  · exact B1060495
  · exact B1060499
  · exact B1060503
  · exact B1060507
  · exact B1060511
  · exact B1060515
  · exact B1060519
  · exact B1060523
  · exact B1060527
  · exact B1060531
  · exact B1060535
  · exact B1060539
  · exact B1060543
  · exact B1060547
  · exact B1060551
  · exact B1060555
  · exact B1060559
  · exact B1060563
  · exact B1060567
  · exact B1060571
  · exact B1060575
  · exact B1060579
  · exact B1060583
  · exact B1060587
  · exact B1060591
  · exact B1060595
  · exact B1060599
  · exact B1060603
  · exact B1060607
  · exact B1060611

theorem solution (m : ℕ) (hlo : 1056613 ≤ m) (hhi : m ≤ 1060613) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 264153 ≤ j := by omega
    have hj2 : j ≤ 265152 := by omega
    have hb : Blo 1056613 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 264853 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
