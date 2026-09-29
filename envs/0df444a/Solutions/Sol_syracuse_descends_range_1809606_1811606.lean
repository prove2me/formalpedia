-- Prove2me | solution 1 for syracuse_descends_range_1809606_1811606
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:53:09.153282+00:00
-- url     : https://prove2.me/submissions/a5fd1045-2146-42ee-a052-3965e3f09a38

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


theorem B3055637 : Blo 1809606 3055637 := bbase (se 6 (by rfl) ⟨71616, by rfl⟩ : syracuseStep 3055637 = 143233) (by norm_num)
theorem B3973213 : Blo 1809606 3973213 := bbase (se 3 (by rfl) ⟨744977, by rfl⟩ : syracuseStep 3973213 = 1489955) (by norm_num)
theorem B3096677 : Blo 1809606 3096677 := bbase (se 4 (by rfl) ⟨290313, by rfl⟩ : syracuseStep 3096677 = 580627) (by norm_num)
theorem B3055765 : Blo 1809606 3055765 := bbase (se 6 (by rfl) ⟨71619, by rfl⟩ : syracuseStep 3055765 = 143239) (by norm_num)
theorem B1933513 : Blo 1809606 1933513 := bbase (se 2 (by rfl) ⟨725067, by rfl⟩ : syracuseStep 1933513 = 1450135) (by norm_num)
theorem B1859809 : Blo 1809606 1859809 := bbase (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) (by norm_num)
theorem B4071653 : Blo 1809606 4071653 := bbase (se 4 (by rfl) ⟨381717, by rfl⟩ : syracuseStep 4071653 = 763435) (by norm_num)
theorem B3055853 : Blo 1809606 3055853 := bbase (se 3 (by rfl) ⟨572972, by rfl⟩ : syracuseStep 3055853 = 1145945) (by norm_num)
theorem B2900213 : Blo 1809606 2900213 := bbase (se 5 (by rfl) ⟨135947, by rfl⟩ : syracuseStep 2900213 = 271895) (by norm_num)
theorem B9167093 : Blo 1809606 9167093 := bbase (se 5 (by rfl) ⟨429707, by rfl⟩ : syracuseStep 9167093 = 859415) (by norm_num)
theorem B4071725 : Blo 1809606 4071725 := bbase (se 3 (by rfl) ⟨763448, by rfl⟩ : syracuseStep 4071725 = 1526897) (by norm_num)
theorem B1933633 : Blo 1809606 1933633 := bbase (se 2 (by rfl) ⟨725112, by rfl⟩ : syracuseStep 1933633 = 1450225) (by norm_num)
theorem B6111557 : Blo 1809606 6111557 := bbase (se 4 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 6111557 = 1145917) (by norm_num)
theorem B3055981 : Blo 1809606 3055981 := bbase (se 3 (by rfl) ⟨572996, by rfl⟩ : syracuseStep 3055981 = 1145993) (by norm_num)
theorem B4071797 : Blo 1809606 4071797 := bbase (se 5 (by rfl) ⟨190865, by rfl⟩ : syracuseStep 4071797 = 381731) (by norm_num)
theorem B3867061 : Blo 1809606 3867061 := bbase (se 5 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 3867061 = 362537) (by norm_num)
theorem B4071869 : Blo 1809606 4071869 := bbase (se 3 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 4071869 = 1526951) (by norm_num)
theorem B3056069 : Blo 1809606 3056069 := bbase (se 4 (by rfl) ⟨286506, by rfl⟩ : syracuseStep 3056069 = 573013) (by norm_num)
theorem B3670525 : Blo 1809606 3670525 := bbase (se 3 (by rfl) ⟨688223, by rfl⟩ : syracuseStep 3670525 = 1376447) (by norm_num)
theorem B4071941 : Blo 1809606 4071941 := bbase (se 4 (by rfl) ⟨381744, by rfl⟩ : syracuseStep 4071941 = 763489) (by norm_num)
theorem B6873605 : Blo 1809606 6873605 := bbase (se 4 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 6873605 = 1288801) (by norm_num)
theorem B1933885 : Blo 1809606 1933885 := bbase (se 3 (by rfl) ⟨362603, by rfl⟩ : syracuseStep 1933885 = 725207) (by norm_num)
theorem B1933889 : Blo 1809606 1933889 := bbase (se 2 (by rfl) ⟨725208, by rfl⟩ : syracuseStep 1933889 = 1450417) (by norm_num)
theorem B3056197 : Blo 1809606 3056197 := bbase (se 4 (by rfl) ⟨286518, by rfl⟩ : syracuseStep 3056197 = 573037) (by norm_num)
theorem B4072013 : Blo 1809606 4072013 := bbase (se 3 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 4072013 = 1527005) (by norm_num)
theorem B7340645 : Blo 1809606 7340645 := bbase (se 4 (by rfl) ⟨688185, by rfl⟩ : syracuseStep 7340645 = 1376371) (by norm_num)
theorem B4072085 : Blo 1809606 4072085 := bbase (se 6 (by rfl) ⟨95439, by rfl⟩ : syracuseStep 4072085 = 190879) (by norm_num)
theorem B3056285 : Blo 1809606 3056285 := bbase (se 3 (by rfl) ⟨573053, by rfl⟩ : syracuseStep 3056285 = 1146107) (by norm_num)
theorem B3261125 : Blo 1809606 3261125 := bbase (se 4 (by rfl) ⟨305730, by rfl⟩ : syracuseStep 3261125 = 611461) (by norm_num)
theorem B4072157 : Blo 1809606 4072157 := bbase (se 3 (by rfl) ⟨763529, by rfl⟩ : syracuseStep 4072157 = 1527059) (by norm_num)
theorem B6111989 : Blo 1809606 6111989 := bbase (se 5 (by rfl) ⟨286499, by rfl⟩ : syracuseStep 6111989 = 572999) (by norm_num)
theorem B10314485 : Blo 1809606 10314485 := bbase (se 5 (by rfl) ⟨483491, by rfl⟩ : syracuseStep 10314485 = 966983) (by norm_num)
theorem B3097349 : Blo 1809606 3097349 := bbase (se 4 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 3097349 = 580753) (by norm_num)
theorem B18588437 : Blo 1809606 18588437 := bbase (se 6 (by rfl) ⟨435666, by rfl⟩ : syracuseStep 18588437 = 871333) (by norm_num)
theorem B3056413 : Blo 1809606 3056413 := bbase (se 3 (by rfl) ⟨573077, by rfl⟩ : syracuseStep 3056413 = 1146155) (by norm_num)
theorem B4072229 : Blo 1809606 4072229 := bbase (se 4 (by rfl) ⟨381771, by rfl⟩ : syracuseStep 4072229 = 763543) (by norm_num)
theorem B6873893 : Blo 1809606 6873893 := bbase (se 4 (by rfl) ⟨644427, by rfl⟩ : syracuseStep 6873893 = 1288855) (by norm_num)
theorem B8373061 : Blo 1809606 8373061 := bbase (se 4 (by rfl) ⟨784974, by rfl⟩ : syracuseStep 8373061 = 1569949) (by norm_num)
theorem B4072301 : Blo 1809606 4072301 := bbase (se 3 (by rfl) ⟨763556, by rfl⟩ : syracuseStep 4072301 = 1527113) (by norm_num)
theorem B3056501 : Blo 1809606 3056501 := bbase (se 5 (by rfl) ⟨143273, by rfl⟩ : syracuseStep 3056501 = 286547) (by norm_num)
theorem B4072373 : Blo 1809606 4072373 := bbase (se 5 (by rfl) ⟨190892, by rfl⟩ : syracuseStep 4072373 = 381785) (by norm_num)
theorem B4645829 : Blo 1809606 4645829 := bbase (se 4 (by rfl) ⟨435546, by rfl⟩ : syracuseStep 4645829 = 871093) (by norm_num)
theorem B26108885 : Blo 1809606 26108885 := bbase (se 7 (by rfl) ⟨305963, by rfl⟩ : syracuseStep 26108885 = 611927) (by norm_num)
theorem B3056629 : Blo 1809606 3056629 := bbase (se 5 (by rfl) ⟨143279, by rfl⟩ : syracuseStep 3056629 = 286559) (by norm_num)
theorem B4072445 : Blo 1809606 4072445 := bbase (se 3 (by rfl) ⟨763583, by rfl⟩ : syracuseStep 4072445 = 1527167) (by norm_num)
theorem B8700965 : Blo 1809606 8700965 := bbase (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) (by norm_num)
theorem B4072517 : Blo 1809606 4072517 := bbase (se 4 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 4072517 = 763597) (by norm_num)
theorem B3056717 : Blo 1809606 3056717 := bbase (se 3 (by rfl) ⟨573134, by rfl⟩ : syracuseStep 3056717 = 1146269) (by norm_num)
theorem B1934453 : Blo 1809606 1934453 := bbase (se 5 (by rfl) ⟨90677, by rfl⟩ : syracuseStep 1934453 = 181355) (by norm_num)
theorem B3671173 : Blo 1809606 3671173 := bbase (se 4 (by rfl) ⟨344172, by rfl⟩ : syracuseStep 3671173 = 688345) (by norm_num)
theorem B4072589 : Blo 1809606 4072589 := bbase (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) (by norm_num)
theorem B4351117 : Blo 1809606 4351117 := bbase (se 3 (by rfl) ⟨815834, by rfl⟩ : syracuseStep 4351117 = 1631669) (by norm_num)
theorem B6112421 : Blo 1809606 6112421 := bbase (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) (by norm_num)
theorem B3056845 : Blo 1809606 3056845 := bbase (se 3 (by rfl) ⟨573158, by rfl⟩ : syracuseStep 3056845 = 1146317) (by norm_num)
theorem B4072661 : Blo 1809606 4072661 := bbase (se 7 (by rfl) ⟨47726, by rfl⟩ : syracuseStep 4072661 = 95453) (by norm_num)
theorem B4580621 : Blo 1809606 4580621 := bbase (se 3 (by rfl) ⟨858866, by rfl⟩ : syracuseStep 4580621 = 1717733) (by norm_num)
theorem B8824085 : Blo 1809606 8824085 := bbase (se 6 (by rfl) ⟨206814, by rfl⟩ : syracuseStep 8824085 = 413629) (by norm_num)
theorem B4072733 : Blo 1809606 4072733 := bbase (se 3 (by rfl) ⟨763637, by rfl⟩ : syracuseStep 4072733 = 1527275) (by norm_num)
theorem B3056933 : Blo 1809606 3056933 := bbase (se 4 (by rfl) ⟨286587, by rfl⟩ : syracuseStep 3056933 = 573175) (by norm_num)
theorem B3867949 : Blo 1809606 3867949 := bbase (se 3 (by rfl) ⟨725240, by rfl⟩ : syracuseStep 3867949 = 1450481) (by norm_num)
theorem B2065729 : Blo 1809606 2065729 := bbase (se 2 (by rfl) ⟨774648, by rfl⟩ : syracuseStep 2065729 = 1549297) (by norm_num)
theorem B8701253 : Blo 1809606 8701253 := bbase (se 4 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 8701253 = 1631485) (by norm_num)
theorem B2901341 : Blo 1809606 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B4072805 : Blo 1809606 4072805 := bbase (se 4 (by rfl) ⟨381825, by rfl⟩ : syracuseStep 4072805 = 763651) (by norm_num)
theorem B1860989 : Blo 1809606 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B11011477 : Blo 1809606 11011477 := bbase (se 6 (by rfl) ⟨258081, by rfl⟩ : syracuseStep 11011477 = 516163) (by norm_num)
theorem B3868069 : Blo 1809606 3868069 := bbase (se 4 (by rfl) ⟨362631, by rfl⟩ : syracuseStep 3868069 = 725263) (by norm_num)
theorem B3057061 : Blo 1809606 3057061 := bbase (se 4 (by rfl) ⟨286599, by rfl⟩ : syracuseStep 3057061 = 573199) (by norm_num)
theorem B4072877 : Blo 1809606 4072877 := bbase (se 3 (by rfl) ⟨763664, by rfl⟩ : syracuseStep 4072877 = 1527329) (by norm_num)
theorem B4580813 : Blo 1809606 4580813 := bbase (se 3 (by rfl) ⟨858902, by rfl⟩ : syracuseStep 4580813 = 1717805) (by norm_num)
theorem B5154293 : Blo 1809606 5154293 := bbase (se 5 (by rfl) ⟨241607, by rfl⟩ : syracuseStep 5154293 = 483215) (by norm_num)
theorem B4072949 : Blo 1809606 4072949 := bbase (se 5 (by rfl) ⟨190919, by rfl⟩ : syracuseStep 4072949 = 381839) (by norm_num)
theorem B3098101 : Blo 1809606 3098101 := bbase (se 5 (by rfl) ⟨145223, by rfl⟩ : syracuseStep 3098101 = 290447) (by norm_num)
theorem B9168389 : Blo 1809606 9168389 := bbase (se 4 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 9168389 = 1719073) (by norm_num)
theorem B4646413 : Blo 1809606 4646413 := bbase (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) (by norm_num)
theorem B4073021 : Blo 1809606 4073021 := bbase (se 3 (by rfl) ⟨763691, by rfl⟩ : syracuseStep 4073021 = 1527383) (by norm_num)
theorem B1959509 : Blo 1809606 1959509 := bbase (se 8 (by rfl) ⟨11481, by rfl⟩ : syracuseStep 1959509 = 22963) (by norm_num)
theorem B6112853 : Blo 1809606 6112853 := bbase (se 8 (by rfl) ⟨35817, by rfl⟩ : syracuseStep 6112853 = 71635) (by norm_num)
theorem B4073093 : Blo 1809606 4073093 := bbase (se 4 (by rfl) ⟨381852, by rfl⟩ : syracuseStep 4073093 = 763705) (by norm_num)
theorem B3868325 : Blo 1809606 3868325 := bbase (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) (by norm_num)
theorem B4073165 : Blo 1809606 4073165 := bbase (se 3 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 4073165 = 1527437) (by norm_num)
theorem B2041573 : Blo 1809606 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B4073237 : Blo 1809606 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B4581157 : Blo 1809606 4581157 := bbase (se 4 (by rfl) ⟨429483, by rfl⟩ : syracuseStep 4581157 = 858967) (by norm_num)
theorem B4351781 : Blo 1809606 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B3262285 : Blo 1809606 3262285 := bbase (se 3 (by rfl) ⟨611678, by rfl⟩ : syracuseStep 3262285 = 1223357) (by norm_num)
theorem B4073309 : Blo 1809606 4073309 := bbase (se 3 (by rfl) ⟨763745, by rfl⟩ : syracuseStep 4073309 = 1527491) (by norm_num)
theorem B5801861 : Blo 1809606 5801861 := bbase (se 4 (by rfl) ⟨543924, by rfl⟩ : syracuseStep 5801861 = 1087849) (by norm_num)
theorem B4581269 : Blo 1809606 4581269 := bbase (se 6 (by rfl) ⟨107373, by rfl⟩ : syracuseStep 4581269 = 214747) (by norm_num)
theorem B4073381 : Blo 1809606 4073381 := bbase (se 4 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 4073381 = 763759) (by norm_num)
theorem B6875077 : Blo 1809606 6875077 := bbase (se 4 (by rfl) ⟨644538, by rfl⟩ : syracuseStep 6875077 = 1289077) (by norm_num)
theorem B4073453 : Blo 1809606 4073453 := bbase (se 3 (by rfl) ⟨763772, by rfl⟩ : syracuseStep 4073453 = 1527545) (by norm_num)
theorem B6113285 : Blo 1809606 6113285 := bbase (se 4 (by rfl) ⟨573120, by rfl⟩ : syracuseStep 6113285 = 1146241) (by norm_num)
theorem B4073525 : Blo 1809606 4073525 := bbase (se 5 (by rfl) ⟨190946, by rfl⟩ : syracuseStep 4073525 = 381893) (by norm_num)
theorem B4581461 : Blo 1809606 4581461 := bbase (se 8 (by rfl) ⟨26844, by rfl⟩ : syracuseStep 4581461 = 53689) (by norm_num)
theorem B6613109 : Blo 1809606 6613109 := bbase (se 5 (by rfl) ⟨309989, by rfl⟩ : syracuseStep 6613109 = 619979) (by norm_num)
theorem B4073597 : Blo 1809606 4073597 := bbase (se 3 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 4073597 = 1527599) (by norm_num)
theorem B3262589 : Blo 1809606 3262589 := bbase (se 3 (by rfl) ⟨611735, by rfl⟩ : syracuseStep 3262589 = 1223471) (by norm_num)
theorem B6523013 : Blo 1809606 6523013 := bbase (se 4 (by rfl) ⟨611532, by rfl⟩ : syracuseStep 6523013 = 1223065) (by norm_num)
theorem B5154965 : Blo 1809606 5154965 := bbase (se 6 (by rfl) ⟨120819, by rfl⟩ : syracuseStep 5154965 = 241639) (by norm_num)
theorem B4073669 : Blo 1809606 4073669 := bbase (se 4 (by rfl) ⟨381906, by rfl⟩ : syracuseStep 4073669 = 763813) (by norm_num)
theorem B1960133 : Blo 1809606 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B6875381 : Blo 1809606 6875381 := bbase (se 5 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 6875381 = 644567) (by norm_num)
theorem B4073741 : Blo 1809606 4073741 := bbase (se 3 (by rfl) ⟨763826, by rfl⟩ : syracuseStep 4073741 = 1527653) (by norm_num)
theorem B3672341 : Blo 1809606 3672341 := bbase (se 6 (by rfl) ⟨86070, by rfl⟩ : syracuseStep 3672341 = 172141) (by norm_num)
theorem B27871573 : Blo 1809606 27871573 := bbase (se 10 (by rfl) ⟨40827, by rfl⟩ : syracuseStep 27871573 = 81655) (by norm_num)
theorem B4073813 : Blo 1809606 4073813 := bbase (se 10 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 4073813 = 11935) (by norm_num)
theorem B4073885 : Blo 1809606 4073885 := bbase (se 3 (by rfl) ⟨763853, by rfl⟩ : syracuseStep 4073885 = 1527707) (by norm_num)
theorem B4581805 : Blo 1809606 4581805 := bbase (se 3 (by rfl) ⟨859088, by rfl⟩ : syracuseStep 4581805 = 1718177) (by norm_num)
theorem B6113717 : Blo 1809606 6113717 := bbase (se 5 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 6113717 = 573161) (by norm_num)
theorem B4073957 : Blo 1809606 4073957 := bbase (se 4 (by rfl) ⟨381933, by rfl⟩ : syracuseStep 4073957 = 763867) (by norm_num)
theorem B4581917 : Blo 1809606 4581917 := bbase (se 3 (by rfl) ⟨859109, by rfl⟩ : syracuseStep 4581917 = 1718219) (by norm_num)
theorem B4074029 : Blo 1809606 4074029 := bbase (se 3 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 4074029 = 1527761) (by norm_num)
theorem B5155397 : Blo 1809606 5155397 := bbase (se 4 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 5155397 = 966637) (by norm_num)
theorem B4074101 : Blo 1809606 4074101 := bbase (se 5 (by rfl) ⟨190973, by rfl⟩ : syracuseStep 4074101 = 381947) (by norm_num)
theorem B6965909 : Blo 1809606 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B4074173 : Blo 1809606 4074173 := bbase (se 3 (by rfl) ⟨763907, by rfl⟩ : syracuseStep 4074173 = 1527815) (by norm_num)
theorem B4582109 : Blo 1809606 4582109 := bbase (se 3 (by rfl) ⟨859145, by rfl⟩ : syracuseStep 4582109 = 1718291) (by norm_num)
theorem B4074245 : Blo 1809606 4074245 := bbase (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) (by norm_num)
theorem B5958421 : Blo 1809606 5958421 := bbase (se 6 (by rfl) ⟨139650, by rfl⟩ : syracuseStep 5958421 = 279301) (by norm_num)
theorem B9169685 : Blo 1809606 9169685 := bbase (se 6 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 9169685 = 429829) (by norm_num)
theorem B2714429 : Blo 1809606 2714429 := bbase (se 3 (by rfl) ⟨508955, by rfl⟩ : syracuseStep 2714429 = 1017911) (by norm_num)
theorem B4074317 : Blo 1809606 4074317 := bbase (se 3 (by rfl) ⟨763934, by rfl⟩ : syracuseStep 4074317 = 1527869) (by norm_num)
theorem B2714453 : Blo 1809606 2714453 := bbase (se 9 (by rfl) ⟨7952, by rfl⟩ : syracuseStep 2714453 = 15905) (by norm_num)
theorem B6114149 : Blo 1809606 6114149 := bbase (se 4 (by rfl) ⟨573201, by rfl⟩ : syracuseStep 6114149 = 1146403) (by norm_num)
theorem B2714477 : Blo 1809606 2714477 := bbase (se 3 (by rfl) ⟨508964, by rfl⟩ : syracuseStep 2714477 = 1017929) (by norm_num)
theorem B2714501 : Blo 1809606 2714501 := bbase (se 4 (by rfl) ⟨254484, by rfl⟩ : syracuseStep 2714501 = 508969) (by norm_num)
theorem B31771541 : Blo 1809606 31771541 := bbase (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) (by norm_num)
theorem B4074389 : Blo 1809606 4074389 := bbase (se 6 (by rfl) ⟨95493, by rfl⟩ : syracuseStep 4074389 = 190987) (by norm_num)
theorem B2714525 : Blo 1809606 2714525 := bbase (se 3 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 2714525 = 1017947) (by norm_num)
theorem B2714549 : Blo 1809606 2714549 := bbase (se 5 (by rfl) ⟨127244, by rfl⟩ : syracuseStep 2714549 = 254489) (by norm_num)
theorem B2714573 : Blo 1809606 2714573 := bbase (se 3 (by rfl) ⟨508982, by rfl⟩ : syracuseStep 2714573 = 1017965) (by norm_num)
theorem B23202773 : Blo 1809606 23202773 := bbase (se 7 (by rfl) ⟨271907, by rfl⟩ : syracuseStep 23202773 = 543815) (by norm_num)
theorem B4074461 : Blo 1809606 4074461 := bbase (se 3 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 4074461 = 1527923) (by norm_num)
theorem B2714597 : Blo 1809606 2714597 := bbase (se 4 (by rfl) ⟨254493, by rfl⟩ : syracuseStep 2714597 = 508987) (by norm_num)
theorem B7736309 : Blo 1809606 7736309 := bbase (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) (by norm_num)
theorem B2714621 : Blo 1809606 2714621 := bbase (se 3 (by rfl) ⟨508991, by rfl⟩ : syracuseStep 2714621 = 1017983) (by norm_num)
theorem B2714645 : Blo 1809606 2714645 := bbase (se 6 (by rfl) ⟨63624, by rfl⟩ : syracuseStep 2714645 = 127249) (by norm_num)
theorem B4074533 : Blo 1809606 4074533 := bbase (se 4 (by rfl) ⟨381987, by rfl⟩ : syracuseStep 4074533 = 763975) (by norm_num)
theorem B2714669 : Blo 1809606 2714669 := bbase (se 3 (by rfl) ⟨509000, by rfl⟩ : syracuseStep 2714669 = 1018001) (by norm_num)
theorem B4582453 : Blo 1809606 4582453 := bbase (se 5 (by rfl) ⟨214802, by rfl⟩ : syracuseStep 4582453 = 429605) (by norm_num)
theorem B2714693 : Blo 1809606 2714693 := bbase (se 4 (by rfl) ⟨254502, by rfl⟩ : syracuseStep 2714693 = 509005) (by norm_num)
theorem B7539797 : Blo 1809606 7539797 := bbase (se 8 (by rfl) ⟨44178, by rfl⟩ : syracuseStep 7539797 = 88357) (by norm_num)
theorem B2174045 : Blo 1809606 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B2714717 : Blo 1809606 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B4074605 : Blo 1809606 4074605 := bbase (se 3 (by rfl) ⟨763988, by rfl⟩ : syracuseStep 4074605 = 1527977) (by norm_num)
theorem B2714741 : Blo 1809606 2714741 := bbase (se 5 (by rfl) ⟨127253, by rfl⟩ : syracuseStep 2714741 = 254507) (by norm_num)
theorem B2714765 : Blo 1809606 2714765 := bbase (se 3 (by rfl) ⟨509018, by rfl⟩ : syracuseStep 2714765 = 1018037) (by norm_num)
theorem B2714789 : Blo 1809606 2714789 := bbase (se 4 (by rfl) ⟨254511, by rfl⟩ : syracuseStep 2714789 = 509023) (by norm_num)
theorem B4582565 : Blo 1809606 4582565 := bbase (se 4 (by rfl) ⟨429615, by rfl⟩ : syracuseStep 4582565 = 859231) (by norm_num)
theorem B9161909 : Blo 1809606 9161909 := bbase (se 5 (by rfl) ⟨429464, by rfl⟩ : syracuseStep 9161909 = 858929) (by norm_num)
theorem B4074677 : Blo 1809606 4074677 := bbase (se 5 (by rfl) ⟨191000, by rfl⟩ : syracuseStep 4074677 = 382001) (by norm_num)
theorem B3263669 : Blo 1809606 3263669 := bbase (se 5 (by rfl) ⟨152984, by rfl⟩ : syracuseStep 3263669 = 305969) (by norm_num)
theorem B3435709 : Blo 1809606 3435709 := bbase (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) (by norm_num)
theorem B2714813 : Blo 1809606 2714813 := bbase (se 3 (by rfl) ⟨509027, by rfl⟩ : syracuseStep 2714813 = 1018055) (by norm_num)
theorem B6196421 : Blo 1809606 6196421 := bbase (se 4 (by rfl) ⟨580914, by rfl⟩ : syracuseStep 6196421 = 1161829) (by norm_num)
theorem B2714837 : Blo 1809606 2714837 := bbase (se 7 (by rfl) ⟨31814, by rfl⟩ : syracuseStep 2714837 = 63629) (by norm_num)
theorem B2714861 : Blo 1809606 2714861 := bbase (se 3 (by rfl) ⟨509036, by rfl⟩ : syracuseStep 2714861 = 1018073) (by norm_num)
theorem B4074749 : Blo 1809606 4074749 := bbase (se 3 (by rfl) ⟨764015, by rfl⟩ : syracuseStep 4074749 = 1528031) (by norm_num)
theorem B2714885 : Blo 1809606 2714885 := bbase (se 4 (by rfl) ⟨254520, by rfl⟩ : syracuseStep 2714885 = 509041) (by norm_num)
theorem B2714909 : Blo 1809606 2714909 := bbase (se 3 (by rfl) ⟨509045, by rfl⟩ : syracuseStep 2714909 = 1018091) (by norm_num)
theorem B13045045 : Blo 1809606 13045045 := bbase (se 5 (by rfl) ⟨611486, by rfl⟩ : syracuseStep 13045045 = 1222973) (by norm_num)
theorem B2714933 : Blo 1809606 2714933 := bbase (se 5 (by rfl) ⟨127262, by rfl⟩ : syracuseStep 2714933 = 254525) (by norm_num)
theorem B5156149 : Blo 1809606 5156149 := bbase (se 5 (by rfl) ⟨241694, by rfl⟩ : syracuseStep 5156149 = 483389) (by norm_num)
theorem B4074821 : Blo 1809606 4074821 := bbase (se 4 (by rfl) ⟨382014, by rfl⟩ : syracuseStep 4074821 = 764029) (by norm_num)
theorem B3435853 : Blo 1809606 3435853 := bbase (se 3 (by rfl) ⟨644222, by rfl⟩ : syracuseStep 3435853 = 1288445) (by norm_num)
theorem B2714957 : Blo 1809606 2714957 := bbase (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) (by norm_num)
theorem B2714981 : Blo 1809606 2714981 := bbase (se 4 (by rfl) ⟨254529, by rfl⟩ : syracuseStep 2714981 = 509059) (by norm_num)
theorem B4582757 : Blo 1809606 4582757 := bbase (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) (by norm_num)
theorem B2715005 : Blo 1809606 2715005 := bbase (se 3 (by rfl) ⟨509063, by rfl⟩ : syracuseStep 2715005 = 1018127) (by norm_num)
theorem B4074893 : Blo 1809606 4074893 := bbase (se 3 (by rfl) ⟨764042, by rfl⟩ : syracuseStep 4074893 = 1528085) (by norm_num)
theorem B2715029 : Blo 1809606 2715029 := bbase (se 6 (by rfl) ⟨63633, by rfl⟩ : syracuseStep 2715029 = 127267) (by norm_num)
theorem B19582357 : Blo 1809606 19582357 := bbase (se 6 (by rfl) ⟨458961, by rfl⟩ : syracuseStep 19582357 = 917923) (by norm_num)
theorem B2715053 : Blo 1809606 2715053 := bbase (se 3 (by rfl) ⟨509072, by rfl⟩ : syracuseStep 2715053 = 1018145) (by norm_num)
theorem B9293237 : Blo 1809606 9293237 := bbase (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) (by norm_num)
theorem B2715077 : Blo 1809606 2715077 := bbase (se 4 (by rfl) ⟨254538, by rfl⟩ : syracuseStep 2715077 = 509077) (by norm_num)
theorem B3182029 : Blo 1809606 3182029 := bbase (se 3 (by rfl) ⟨596630, by rfl⟩ : syracuseStep 3182029 = 1193261) (by norm_num)
theorem B4074965 : Blo 1809606 4074965 := bbase (se 7 (by rfl) ⟨47753, by rfl⟩ : syracuseStep 4074965 = 95507) (by norm_num)
theorem B2715101 : Blo 1809606 2715101 := bbase (se 3 (by rfl) ⟨509081, by rfl⟩ : syracuseStep 2715101 = 1018163) (by norm_num)
theorem B3436013 : Blo 1809606 3436013 := bbase (se 3 (by rfl) ⟨644252, by rfl⟩ : syracuseStep 3436013 = 1288505) (by norm_num)
theorem B2715125 : Blo 1809606 2715125 := bbase (se 5 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 2715125 = 254543) (by norm_num)
theorem B2715149 : Blo 1809606 2715149 := bbase (se 3 (by rfl) ⟨509090, by rfl⟩ : syracuseStep 2715149 = 1018181) (by norm_num)
theorem B4075037 : Blo 1809606 4075037 := bbase (se 3 (by rfl) ⟨764069, by rfl⟩ : syracuseStep 4075037 = 1528139) (by norm_num)
theorem B2715173 : Blo 1809606 2715173 := bbase (se 4 (by rfl) ⟨254547, by rfl⟩ : syracuseStep 2715173 = 509095) (by norm_num)
theorem B2715197 : Blo 1809606 2715197 := bbase (se 3 (by rfl) ⟨509099, by rfl⟩ : syracuseStep 2715197 = 1018199) (by norm_num)
theorem B12381781 : Blo 1809606 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B2715221 : Blo 1809606 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B4075109 : Blo 1809606 4075109 := bbase (se 4 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 4075109 = 764083) (by norm_num)
theorem B2715245 : Blo 1809606 2715245 := bbase (se 3 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 2715245 = 1018217) (by norm_num)
theorem B3436157 : Blo 1809606 3436157 := bbase (se 3 (by rfl) ⟨644279, by rfl⟩ : syracuseStep 3436157 = 1288559) (by norm_num)
theorem B2715269 : Blo 1809606 2715269 := bbase (se 4 (by rfl) ⟨254556, by rfl⟩ : syracuseStep 2715269 = 509113) (by norm_num)
theorem B3485317 : Blo 1809606 3485317 := bbase (se 4 (by rfl) ⟨326748, by rfl⟩ : syracuseStep 3485317 = 653497) (by norm_num)
theorem B2715293 : Blo 1809606 2715293 := bbase (se 3 (by rfl) ⟨509117, by rfl⟩ : syracuseStep 2715293 = 1018235) (by norm_num)
theorem B4075181 : Blo 1809606 4075181 := bbase (se 3 (by rfl) ⟨764096, by rfl⟩ : syracuseStep 4075181 = 1528193) (by norm_num)
theorem B2174645 : Blo 1809606 2174645 := bbase (se 5 (by rfl) ⟨101936, by rfl⟩ : syracuseStep 2174645 = 203873) (by norm_num)
theorem B2715317 : Blo 1809606 2715317 := bbase (se 5 (by rfl) ⟨127280, by rfl⟩ : syracuseStep 2715317 = 254561) (by norm_num)
theorem B4583101 : Blo 1809606 4583101 := bbase (se 3 (by rfl) ⟨859331, by rfl⟩ : syracuseStep 4583101 = 1718663) (by norm_num)
theorem B2715341 : Blo 1809606 2715341 := bbase (se 3 (by rfl) ⟨509126, by rfl⟩ : syracuseStep 2715341 = 1018253) (by norm_num)
theorem B2715365 : Blo 1809606 2715365 := bbase (se 4 (by rfl) ⟨254565, by rfl⟩ : syracuseStep 2715365 = 509131) (by norm_num)
theorem B4075253 : Blo 1809606 4075253 := bbase (se 5 (by rfl) ⟨191027, by rfl⟩ : syracuseStep 4075253 = 382055) (by norm_num)
theorem B2715389 : Blo 1809606 2715389 := bbase (se 3 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 2715389 = 1018271) (by norm_num)
theorem B2715413 : Blo 1809606 2715413 := bbase (se 6 (by rfl) ⟨63642, by rfl⟩ : syracuseStep 2715413 = 127285) (by norm_num)
theorem B2789149 : Blo 1809606 2789149 := bbase (se 3 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 2789149 = 1045931) (by norm_num)
theorem B5508901 : Blo 1809606 5508901 := bbase (se 4 (by rfl) ⟨516459, by rfl⟩ : syracuseStep 5508901 = 1032919) (by norm_num)
theorem B2715437 : Blo 1809606 2715437 := bbase (se 3 (by rfl) ⟨509144, by rfl⟩ : syracuseStep 2715437 = 1018289) (by norm_num)
theorem B4583213 : Blo 1809606 4583213 := bbase (se 3 (by rfl) ⟨859352, by rfl⟩ : syracuseStep 4583213 = 1718705) (by norm_num)
theorem B4075325 : Blo 1809606 4075325 := bbase (se 3 (by rfl) ⟨764123, by rfl⟩ : syracuseStep 4075325 = 1528247) (by norm_num)
theorem B2715461 : Blo 1809606 2715461 := bbase (se 4 (by rfl) ⟨254574, by rfl⟩ : syracuseStep 2715461 = 509149) (by norm_num)
theorem B2715485 : Blo 1809606 2715485 := bbase (se 3 (by rfl) ⟨509153, by rfl⟩ : syracuseStep 2715485 = 1018307) (by norm_num)
theorem B2715509 : Blo 1809606 2715509 := bbase (se 5 (by rfl) ⟨127289, by rfl⟩ : syracuseStep 2715509 = 254579) (by norm_num)
theorem B4075397 : Blo 1809606 4075397 := bbase (se 4 (by rfl) ⟨382068, by rfl⟩ : syracuseStep 4075397 = 764137) (by norm_num)
theorem B2715533 : Blo 1809606 2715533 := bbase (se 3 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 2715533 = 1018325) (by norm_num)
theorem B3436445 : Blo 1809606 3436445 := bbase (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) (by norm_num)
theorem B2715557 : Blo 1809606 2715557 := bbase (se 4 (by rfl) ⟨254583, by rfl⟩ : syracuseStep 2715557 = 509167) (by norm_num)
theorem B2715581 : Blo 1809606 2715581 := bbase (se 3 (by rfl) ⟨509171, by rfl⟩ : syracuseStep 2715581 = 1018343) (by norm_num)
theorem B4894661 : Blo 1809606 4894661 := bbase (se 4 (by rfl) ⟨458874, by rfl⟩ : syracuseStep 4894661 = 917749) (by norm_num)
theorem B4075469 : Blo 1809606 4075469 := bbase (se 3 (by rfl) ⟨764150, by rfl⟩ : syracuseStep 4075469 = 1528301) (by norm_num)
theorem B2715605 : Blo 1809606 2715605 := bbase (se 7 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 2715605 = 63647) (by norm_num)
theorem B2174953 : Blo 1809606 2174953 := bbase (se 2 (by rfl) ⟨815607, by rfl⟩ : syracuseStep 2174953 = 1631215) (by norm_num)
theorem B2715629 : Blo 1809606 2715629 := bbase (se 3 (by rfl) ⟨509180, by rfl⟩ : syracuseStep 2715629 = 1018361) (by norm_num)
theorem B4583405 : Blo 1809606 4583405 := bbase (se 3 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 4583405 = 1718777) (by norm_num)
theorem B2715653 : Blo 1809606 2715653 := bbase (se 4 (by rfl) ⟨254592, by rfl⟩ : syracuseStep 2715653 = 509185) (by norm_num)
theorem B4075541 : Blo 1809606 4075541 := bbase (se 6 (by rfl) ⟨95520, by rfl⟩ : syracuseStep 4075541 = 191041) (by norm_num)
theorem B2715677 : Blo 1809606 2715677 := bbase (se 3 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 2715677 = 1018379) (by norm_num)
theorem B9170981 : Blo 1809606 9170981 := bbase (se 4 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 9170981 = 1719559) (by norm_num)
theorem B3436597 : Blo 1809606 3436597 := bbase (se 5 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 3436597 = 322181) (by norm_num)
theorem B2715701 : Blo 1809606 2715701 := bbase (se 5 (by rfl) ⟨127298, by rfl⟩ : syracuseStep 2715701 = 254597) (by norm_num)
theorem B2175049 : Blo 1809606 2175049 := bbase (se 2 (by rfl) ⟨815643, by rfl⟩ : syracuseStep 2175049 = 1631287) (by norm_num)
theorem B2715725 : Blo 1809606 2715725 := bbase (se 3 (by rfl) ⟨509198, by rfl⟩ : syracuseStep 2715725 = 1018397) (by norm_num)
theorem B4075613 : Blo 1809606 4075613 := bbase (se 3 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 4075613 = 1528355) (by norm_num)
theorem B2035813 : Blo 1809606 2035813 := bbase (se 4 (by rfl) ⟨190857, by rfl⟩ : syracuseStep 2035813 = 381715) (by norm_num)
theorem B2715749 : Blo 1809606 2715749 := bbase (se 4 (by rfl) ⟨254601, by rfl⟩ : syracuseStep 2715749 = 509203) (by norm_num)
theorem B2175097 : Blo 1809606 2175097 := bbase (se 2 (by rfl) ⟨815661, by rfl⟩ : syracuseStep 2175097 = 1631323) (by norm_num)
theorem B2715773 : Blo 1809606 2715773 := bbase (se 3 (by rfl) ⟨509207, by rfl⟩ : syracuseStep 2715773 = 1018415) (by norm_num)
theorem B2035849 : Blo 1809606 2035849 := bbase (se 2 (by rfl) ⟨763443, by rfl⟩ : syracuseStep 2035849 = 1526887) (by norm_num)
theorem B2715797 : Blo 1809606 2715797 := bbase (se 6 (by rfl) ⟨63651, by rfl⟩ : syracuseStep 2715797 = 127303) (by norm_num)
theorem B4075685 : Blo 1809606 4075685 := bbase (se 4 (by rfl) ⟨382095, by rfl⟩ : syracuseStep 4075685 = 764191) (by norm_num)
theorem B2035885 : Blo 1809606 2035885 := bbase (se 3 (by rfl) ⟨381728, by rfl⟩ : syracuseStep 2035885 = 763457) (by norm_num)
theorem B2715821 : Blo 1809606 2715821 := bbase (se 3 (by rfl) ⟨509216, by rfl⟩ : syracuseStep 2715821 = 1018433) (by norm_num)
theorem B2715845 : Blo 1809606 2715845 := bbase (se 4 (by rfl) ⟨254610, by rfl⟩ : syracuseStep 2715845 = 509221) (by norm_num)
theorem B2035921 : Blo 1809606 2035921 := bbase (se 2 (by rfl) ⟨763470, by rfl⟩ : syracuseStep 2035921 = 1526941) (by norm_num)
theorem B30937301 : Blo 1809606 30937301 := bbase (se 7 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 30937301 = 725093) (by norm_num)
theorem B2576605 : Blo 1809606 2576605 := bbase (se 3 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 2576605 = 966227) (by norm_num)
theorem B2715869 : Blo 1809606 2715869 := bbase (se 3 (by rfl) ⟨509225, by rfl⟩ : syracuseStep 2715869 = 1018451) (by norm_num)
theorem B4075757 : Blo 1809606 4075757 := bbase (se 3 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 4075757 = 1528409) (by norm_num)
theorem B2035957 : Blo 1809606 2035957 := bbase (se 5 (by rfl) ⟨95435, by rfl⟩ : syracuseStep 2035957 = 190871) (by norm_num)
theorem B2715893 : Blo 1809606 2715893 := bbase (se 5 (by rfl) ⟨127307, by rfl⟩ : syracuseStep 2715893 = 254615) (by norm_num)
theorem B2715917 : Blo 1809606 2715917 := bbase (se 3 (by rfl) ⟨509234, by rfl⟩ : syracuseStep 2715917 = 1018469) (by norm_num)
theorem B2035993 : Blo 1809606 2035993 := bbase (se 2 (by rfl) ⟨763497, by rfl⟩ : syracuseStep 2035993 = 1526995) (by norm_num)
theorem B2715941 : Blo 1809606 2715941 := bbase (se 4 (by rfl) ⟨254619, by rfl⟩ : syracuseStep 2715941 = 509239) (by norm_num)
theorem B6877493 : Blo 1809606 6877493 := bbase (se 5 (by rfl) ⟨322382, by rfl⟩ : syracuseStep 6877493 = 644765) (by norm_num)
theorem B4075829 : Blo 1809606 4075829 := bbase (se 5 (by rfl) ⟨191054, by rfl⟩ : syracuseStep 4075829 = 382109) (by norm_num)
theorem B2036029 : Blo 1809606 2036029 := bbase (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) (by norm_num)
theorem B2715965 : Blo 1809606 2715965 := bbase (se 3 (by rfl) ⟨509243, by rfl⟩ : syracuseStep 2715965 = 1018487) (by norm_num)
theorem B4583749 : Blo 1809606 4583749 := bbase (se 4 (by rfl) ⟨429726, by rfl⟩ : syracuseStep 4583749 = 859453) (by norm_num)
theorem B2715989 : Blo 1809606 2715989 := bbase (se 10 (by rfl) ⟨3978, by rfl⟩ : syracuseStep 2715989 = 7957) (by norm_num)
theorem B2036065 : Blo 1809606 2036065 := bbase (se 2 (by rfl) ⟨763524, by rfl⟩ : syracuseStep 2036065 = 1527049) (by norm_num)
theorem B3436901 : Blo 1809606 3436901 := bbase (se 4 (by rfl) ⟨322209, by rfl⟩ : syracuseStep 3436901 = 644419) (by norm_num)
theorem B2716013 : Blo 1809606 2716013 := bbase (se 3 (by rfl) ⟨509252, by rfl⟩ : syracuseStep 2716013 = 1018505) (by norm_num)
theorem B4075901 : Blo 1809606 4075901 := bbase (se 3 (by rfl) ⟨764231, by rfl⟩ : syracuseStep 4075901 = 1528463) (by norm_num)
theorem B2036101 : Blo 1809606 2036101 := bbase (se 4 (by rfl) ⟨190884, by rfl⟩ : syracuseStep 2036101 = 381769) (by norm_num)
theorem B2716037 : Blo 1809606 2716037 := bbase (se 4 (by rfl) ⟨254628, by rfl⟩ : syracuseStep 2716037 = 509257) (by norm_num)
theorem B2716061 : Blo 1809606 2716061 := bbase (se 3 (by rfl) ⟨509261, by rfl⟩ : syracuseStep 2716061 = 1018523) (by norm_num)
theorem B2036137 : Blo 1809606 2036137 := bbase (se 2 (by rfl) ⟨763551, by rfl⟩ : syracuseStep 2036137 = 1527103) (by norm_num)
theorem B2716085 : Blo 1809606 2716085 := bbase (se 5 (by rfl) ⟨127316, by rfl⟩ : syracuseStep 2716085 = 254633) (by norm_num)
theorem B4583861 : Blo 1809606 4583861 := bbase (se 5 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 4583861 = 429737) (by norm_num)
theorem B9163205 : Blo 1809606 9163205 := bbase (se 4 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 9163205 = 1718101) (by norm_num)
theorem B4075973 : Blo 1809606 4075973 := bbase (se 4 (by rfl) ⟨382122, by rfl⟩ : syracuseStep 4075973 = 764245) (by norm_num)
theorem B2036173 : Blo 1809606 2036173 := bbase (se 3 (by rfl) ⟨381782, by rfl⟩ : syracuseStep 2036173 = 763565) (by norm_num)
theorem B2716109 : Blo 1809606 2716109 := bbase (se 3 (by rfl) ⟨509270, by rfl⟩ : syracuseStep 2716109 = 1018541) (by norm_num)
theorem B2716133 : Blo 1809606 2716133 := bbase (se 4 (by rfl) ⟨254637, by rfl⟩ : syracuseStep 2716133 = 509275) (by norm_num)
theorem B2036209 : Blo 1809606 2036209 := bbase (se 2 (by rfl) ⟨763578, by rfl⟩ : syracuseStep 2036209 = 1527157) (by norm_num)
theorem B2716157 : Blo 1809606 2716157 := bbase (se 3 (by rfl) ⟨509279, by rfl⟩ : syracuseStep 2716157 = 1018559) (by norm_num)
theorem B4076045 : Blo 1809606 4076045 := bbase (se 3 (by rfl) ⟨764258, by rfl⟩ : syracuseStep 4076045 = 1528517) (by norm_num)
theorem B6107669 : Blo 1809606 6107669 := bbase (se 6 (by rfl) ⟨143148, by rfl⟩ : syracuseStep 6107669 = 286297) (by norm_num)
theorem B2036245 : Blo 1809606 2036245 := bbase (se 6 (by rfl) ⟨47724, by rfl⟩ : syracuseStep 2036245 = 95449) (by norm_num)
theorem B2716181 : Blo 1809606 2716181 := bbase (se 6 (by rfl) ⟨63660, by rfl⟩ : syracuseStep 2716181 = 127321) (by norm_num)
theorem B2716205 : Blo 1809606 2716205 := bbase (se 3 (by rfl) ⟨509288, by rfl⟩ : syracuseStep 2716205 = 1018577) (by norm_num)
theorem B2036281 : Blo 1809606 2036281 := bbase (se 2 (by rfl) ⟨763605, by rfl⟩ : syracuseStep 2036281 = 1527211) (by norm_num)
theorem B2716229 : Blo 1809606 2716229 := bbase (se 4 (by rfl) ⟨254646, by rfl⟩ : syracuseStep 2716229 = 509293) (by norm_num)
theorem B2576981 : Blo 1809606 2576981 := bbase (se 8 (by rfl) ⟨15099, by rfl⟩ : syracuseStep 2576981 = 30199) (by norm_num)
theorem B6877781 : Blo 1809606 6877781 := bbase (se 8 (by rfl) ⟨40299, by rfl⟩ : syracuseStep 6877781 = 80599) (by norm_num)
theorem B2036317 : Blo 1809606 2036317 := bbase (se 3 (by rfl) ⟨381809, by rfl⟩ : syracuseStep 2036317 = 763619) (by norm_num)
theorem B2716253 : Blo 1809606 2716253 := bbase (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) (by norm_num)
theorem B2290285 : Blo 1809606 2290285 := bbase (se 3 (by rfl) ⟨429428, by rfl⟩ : syracuseStep 2290285 = 858857) (by norm_num)
theorem B2716277 : Blo 1809606 2716277 := bbase (se 5 (by rfl) ⟨127325, by rfl⟩ : syracuseStep 2716277 = 254651) (by norm_num)
theorem B4584053 : Blo 1809606 4584053 := bbase (se 5 (by rfl) ⟨214877, by rfl⟩ : syracuseStep 4584053 = 429755) (by norm_num)
theorem B2036353 : Blo 1809606 2036353 := bbase (se 2 (by rfl) ⟨763632, by rfl⟩ : syracuseStep 2036353 = 1527265) (by norm_num)
theorem B2716301 : Blo 1809606 2716301 := bbase (se 3 (by rfl) ⟨509306, by rfl⟩ : syracuseStep 2716301 = 1018613) (by norm_num)
theorem B6967957 : Blo 1809606 6967957 := bbase (se 6 (by rfl) ⟨163311, by rfl⟩ : syracuseStep 6967957 = 326623) (by norm_num)
theorem B2036389 : Blo 1809606 2036389 := bbase (se 4 (by rfl) ⟨190911, by rfl⟩ : syracuseStep 2036389 = 381823) (by norm_num)
theorem B2716325 : Blo 1809606 2716325 := bbase (se 4 (by rfl) ⟨254655, by rfl⟩ : syracuseStep 2716325 = 509311) (by norm_num)
theorem B2716349 : Blo 1809606 2716349 := bbase (se 3 (by rfl) ⟨509315, by rfl⟩ : syracuseStep 2716349 = 1018631) (by norm_num)
theorem B2036425 : Blo 1809606 2036425 := bbase (se 2 (by rfl) ⟨763659, by rfl⟩ : syracuseStep 2036425 = 1527319) (by norm_num)
theorem B2716373 : Blo 1809606 2716373 := bbase (se 7 (by rfl) ⟨31832, by rfl⟩ : syracuseStep 2716373 = 63665) (by norm_num)
theorem B7738085 : Blo 1809606 7738085 := bbase (se 4 (by rfl) ⟨725445, by rfl⟩ : syracuseStep 7738085 = 1450891) (by norm_num)
theorem B2036461 : Blo 1809606 2036461 := bbase (se 3 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 2036461 = 763673) (by norm_num)
theorem B2716397 : Blo 1809606 2716397 := bbase (se 3 (by rfl) ⟨509324, by rfl⟩ : syracuseStep 2716397 = 1018649) (by norm_num)
theorem B2716421 : Blo 1809606 2716421 := bbase (se 4 (by rfl) ⟨254664, by rfl⟩ : syracuseStep 2716421 = 509329) (by norm_num)
theorem B2036497 : Blo 1809606 2036497 := bbase (se 2 (by rfl) ⟨763686, by rfl⟩ : syracuseStep 2036497 = 1527373) (by norm_num)
theorem B2290457 : Blo 1809606 2290457 := bbase (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) (by norm_num)
theorem B2716445 : Blo 1809606 2716445 := bbase (se 3 (by rfl) ⟨509333, by rfl⟩ : syracuseStep 2716445 = 1018667) (by norm_num)
theorem B2036533 : Blo 1809606 2036533 := bbase (se 5 (by rfl) ⟨95462, by rfl⟩ : syracuseStep 2036533 = 190925) (by norm_num)
theorem B2716469 : Blo 1809606 2716469 := bbase (se 5 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 2716469 = 254669) (by norm_num)
theorem B2716493 : Blo 1809606 2716493 := bbase (se 3 (by rfl) ⟨509342, by rfl⟩ : syracuseStep 2716493 = 1018685) (by norm_num)
theorem B2290513 : Blo 1809606 2290513 := bbase (se 2 (by rfl) ⟨858942, by rfl⟩ : syracuseStep 2290513 = 1717885) (by norm_num)
theorem B2036569 : Blo 1809606 2036569 := bbase (se 2 (by rfl) ⟨763713, by rfl⟩ : syracuseStep 2036569 = 1527427) (by norm_num)
theorem B2716517 : Blo 1809606 2716517 := bbase (se 4 (by rfl) ⟨254673, by rfl⟩ : syracuseStep 2716517 = 509347) (by norm_num)
theorem B2036605 : Blo 1809606 2036605 := bbase (se 3 (by rfl) ⟨381863, by rfl⟩ : syracuseStep 2036605 = 763727) (by norm_num)
theorem B2716541 : Blo 1809606 2716541 := bbase (se 3 (by rfl) ⟨509351, by rfl⟩ : syracuseStep 2716541 = 1018703) (by norm_num)
theorem B2716565 : Blo 1809606 2716565 := bbase (se 6 (by rfl) ⟨63669, by rfl⟩ : syracuseStep 2716565 = 127339) (by norm_num)
theorem B2036641 : Blo 1809606 2036641 := bbase (se 2 (by rfl) ⟨763740, by rfl⟩ : syracuseStep 2036641 = 1527481) (by norm_num)
theorem B2716589 : Blo 1809606 2716589 := bbase (se 3 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 2716589 = 1018721) (by norm_num)
theorem B2290609 : Blo 1809606 2290609 := bbase (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) (by norm_num)
theorem B6108101 : Blo 1809606 6108101 := bbase (se 4 (by rfl) ⟨572634, by rfl⟩ : syracuseStep 6108101 = 1145269) (by norm_num)
theorem B2036677 : Blo 1809606 2036677 := bbase (se 4 (by rfl) ⟨190938, by rfl⟩ : syracuseStep 2036677 = 381877) (by norm_num)
theorem B2716613 : Blo 1809606 2716613 := bbase (se 4 (by rfl) ⟨254682, by rfl⟩ : syracuseStep 2716613 = 509365) (by norm_num)
theorem B4584397 : Blo 1809606 4584397 := bbase (se 3 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 4584397 = 1719149) (by norm_num)
theorem B2716637 : Blo 1809606 2716637 := bbase (se 3 (by rfl) ⟨509369, by rfl⟩ : syracuseStep 2716637 = 1018739) (by norm_num)
theorem B2036713 : Blo 1809606 2036713 := bbase (se 2 (by rfl) ⟨763767, by rfl⟩ : syracuseStep 2036713 = 1527535) (by norm_num)
theorem B2716661 : Blo 1809606 2716661 := bbase (se 5 (by rfl) ⟨127343, by rfl⟩ : syracuseStep 2716661 = 254687) (by norm_num)
theorem B2036749 : Blo 1809606 2036749 := bbase (se 3 (by rfl) ⟨381890, by rfl⟩ : syracuseStep 2036749 = 763781) (by norm_num)
theorem B2716685 : Blo 1809606 2716685 := bbase (se 3 (by rfl) ⟨509378, by rfl⟩ : syracuseStep 2716685 = 1018757) (by norm_num)
theorem B2716709 : Blo 1809606 2716709 := bbase (se 4 (by rfl) ⟨254691, by rfl⟩ : syracuseStep 2716709 = 509383) (by norm_num)
theorem B2036785 : Blo 1809606 2036785 := bbase (se 2 (by rfl) ⟨763794, by rfl⟩ : syracuseStep 2036785 = 1527589) (by norm_num)
theorem B2716733 : Blo 1809606 2716733 := bbase (se 3 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 2716733 = 1018775) (by norm_num)
theorem B4584509 : Blo 1809606 4584509 := bbase (se 3 (by rfl) ⟨859595, by rfl⟩ : syracuseStep 4584509 = 1719191) (by norm_num)
theorem B7730261 : Blo 1809606 7730261 := bbase (se 8 (by rfl) ⟨45294, by rfl⟩ : syracuseStep 7730261 = 90589) (by norm_num)
theorem B52188245 : Blo 1809606 52188245 := bbase (se 8 (by rfl) ⟨305790, by rfl⟩ : syracuseStep 52188245 = 611581) (by norm_num)
theorem B2036821 : Blo 1809606 2036821 := bbase (se 8 (by rfl) ⟨11934, by rfl⟩ : syracuseStep 2036821 = 23869) (by norm_num)
theorem B3437653 : Blo 1809606 3437653 := bbase (se 8 (by rfl) ⟨20142, by rfl⟩ : syracuseStep 3437653 = 40285) (by norm_num)
theorem B2716757 : Blo 1809606 2716757 := bbase (se 8 (by rfl) ⟨15918, by rfl⟩ : syracuseStep 2716757 = 31837) (by norm_num)
theorem B2290781 : Blo 1809606 2290781 := bbase (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) (by norm_num)
theorem B2716781 : Blo 1809606 2716781 := bbase (se 3 (by rfl) ⟨509396, by rfl⟩ : syracuseStep 2716781 = 1018793) (by norm_num)
theorem B2036857 : Blo 1809606 2036857 := bbase (se 2 (by rfl) ⟨763821, by rfl⟩ : syracuseStep 2036857 = 1527643) (by norm_num)
theorem B8696965 : Blo 1809606 8696965 := bbase (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) (by norm_num)
theorem B2716805 : Blo 1809606 2716805 := bbase (se 4 (by rfl) ⟨254700, by rfl⟩ : syracuseStep 2716805 = 509401) (by norm_num)
theorem B2290837 : Blo 1809606 2290837 := bbase (se 6 (by rfl) ⟨53691, by rfl⟩ : syracuseStep 2290837 = 107383) (by norm_num)
theorem B2036893 : Blo 1809606 2036893 := bbase (se 3 (by rfl) ⟨381917, by rfl⟩ : syracuseStep 2036893 = 763835) (by norm_num)
theorem B2716829 : Blo 1809606 2716829 := bbase (se 3 (by rfl) ⟨509405, by rfl⟩ : syracuseStep 2716829 = 1018811) (by norm_num)
theorem B2716853 : Blo 1809606 2716853 := bbase (se 5 (by rfl) ⟨127352, by rfl⟩ : syracuseStep 2716853 = 254705) (by norm_num)
theorem B2036929 : Blo 1809606 2036929 := bbase (se 2 (by rfl) ⟨763848, by rfl⟩ : syracuseStep 2036929 = 1527697) (by norm_num)
theorem B2716877 : Blo 1809606 2716877 := bbase (se 3 (by rfl) ⟨509414, by rfl⟩ : syracuseStep 2716877 = 1018829) (by norm_num)
theorem B2323669 : Blo 1809606 2323669 := bbase (se 7 (by rfl) ⟨27230, by rfl⟩ : syracuseStep 2323669 = 54461) (by norm_num)
theorem B2036965 : Blo 1809606 2036965 := bbase (se 4 (by rfl) ⟨190965, by rfl⟩ : syracuseStep 2036965 = 381931) (by norm_num)
theorem B3437797 : Blo 1809606 3437797 := bbase (se 4 (by rfl) ⟨322293, by rfl⟩ : syracuseStep 3437797 = 644587) (by norm_num)
theorem B2716901 : Blo 1809606 2716901 := bbase (se 4 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 2716901 = 509419) (by norm_num)
theorem B2290933 : Blo 1809606 2290933 := bbase (se 5 (by rfl) ⟨107387, by rfl⟩ : syracuseStep 2290933 = 214775) (by norm_num)
theorem B4584701 : Blo 1809606 4584701 := bbase (se 3 (by rfl) ⟨859631, by rfl⟩ : syracuseStep 4584701 = 1719263) (by norm_num)
theorem B2716925 : Blo 1809606 2716925 := bbase (se 3 (by rfl) ⟨509423, by rfl⟩ : syracuseStep 2716925 = 1018847) (by norm_num)
theorem B2037001 : Blo 1809606 2037001 := bbase (se 2 (by rfl) ⟨763875, by rfl⟩ : syracuseStep 2037001 = 1527751) (by norm_num)
theorem B2716949 : Blo 1809606 2716949 := bbase (se 6 (by rfl) ⟨63678, by rfl⟩ : syracuseStep 2716949 = 127357) (by norm_num)
theorem B2037037 : Blo 1809606 2037037 := bbase (se 3 (by rfl) ⟨381944, by rfl⟩ : syracuseStep 2037037 = 763889) (by norm_num)
theorem B2716973 : Blo 1809606 2716973 := bbase (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) (by norm_num)
theorem B2176313 : Blo 1809606 2176313 := bbase (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) (by norm_num)
theorem B2716997 : Blo 1809606 2716997 := bbase (se 4 (by rfl) ⟨254718, by rfl⟩ : syracuseStep 2716997 = 509437) (by norm_num)
theorem B2037073 : Blo 1809606 2037073 := bbase (se 2 (by rfl) ⟨763902, by rfl⟩ : syracuseStep 2037073 = 1527805) (by norm_num)
theorem B2717021 : Blo 1809606 2717021 := bbase (se 3 (by rfl) ⟨509441, by rfl⟩ : syracuseStep 2717021 = 1018883) (by norm_num)
theorem B6108533 : Blo 1809606 6108533 := bbase (se 5 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 6108533 = 572675) (by norm_num)
theorem B2037109 : Blo 1809606 2037109 := bbase (se 5 (by rfl) ⟨95489, by rfl⟩ : syracuseStep 2037109 = 190979) (by norm_num)
theorem B2717045 : Blo 1809606 2717045 := bbase (se 5 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 2717045 = 254723) (by norm_num)
theorem B3437957 : Blo 1809606 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B2717069 : Blo 1809606 2717069 := bbase (se 3 (by rfl) ⟨509450, by rfl⟩ : syracuseStep 2717069 = 1018901) (by norm_num)
theorem B2037145 : Blo 1809606 2037145 := bbase (se 2 (by rfl) ⟨763929, by rfl⟩ : syracuseStep 2037145 = 1527859) (by norm_num)
theorem B2291105 : Blo 1809606 2291105 := bbase (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) (by norm_num)
theorem B2717093 : Blo 1809606 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B2323885 : Blo 1809606 2323885 := bbase (se 3 (by rfl) ⟨435728, by rfl⟩ : syracuseStep 2323885 = 871457) (by norm_num)
theorem B2037181 : Blo 1809606 2037181 := bbase (se 3 (by rfl) ⟨381971, by rfl⟩ : syracuseStep 2037181 = 763943) (by norm_num)
theorem B2717117 : Blo 1809606 2717117 := bbase (se 3 (by rfl) ⟨509459, by rfl⟩ : syracuseStep 2717117 = 1018919) (by norm_num)
theorem B4896197 : Blo 1809606 4896197 := bbase (se 4 (by rfl) ⟨459018, by rfl⟩ : syracuseStep 4896197 = 918037) (by norm_num)
theorem B2717141 : Blo 1809606 2717141 := bbase (se 7 (by rfl) ⟨31841, by rfl⟩ : syracuseStep 2717141 = 63683) (by norm_num)
theorem B2291161 : Blo 1809606 2291161 := bbase (se 2 (by rfl) ⟨859185, by rfl⟩ : syracuseStep 2291161 = 1718371) (by norm_num)
theorem B2037217 : Blo 1809606 2037217 := bbase (se 2 (by rfl) ⟨763956, by rfl⟩ : syracuseStep 2037217 = 1527913) (by norm_num)
theorem B2717165 : Blo 1809606 2717165 := bbase (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) (by norm_num)
theorem B2037253 : Blo 1809606 2037253 := bbase (se 4 (by rfl) ⟨190992, by rfl⟩ : syracuseStep 2037253 = 381985) (by norm_num)
theorem B2717189 : Blo 1809606 2717189 := bbase (se 4 (by rfl) ⟨254736, by rfl⟩ : syracuseStep 2717189 = 509473) (by norm_num)
theorem B3438101 : Blo 1809606 3438101 := bbase (se 6 (by rfl) ⟨80580, by rfl⟩ : syracuseStep 3438101 = 161161) (by norm_num)
theorem B2717213 : Blo 1809606 2717213 := bbase (se 3 (by rfl) ⟨509477, by rfl⟩ : syracuseStep 2717213 = 1018955) (by norm_num)
theorem B2037289 : Blo 1809606 2037289 := bbase (se 2 (by rfl) ⟨763983, by rfl⟩ : syracuseStep 2037289 = 1527967) (by norm_num)
theorem B2717237 : Blo 1809606 2717237 := bbase (se 5 (by rfl) ⟨127370, by rfl⟩ : syracuseStep 2717237 = 254741) (by norm_num)
theorem B2291257 : Blo 1809606 2291257 := bbase (se 2 (by rfl) ⟨859221, by rfl⟩ : syracuseStep 2291257 = 1718443) (by norm_num)
theorem B2037325 : Blo 1809606 2037325 := bbase (se 3 (by rfl) ⟨381998, by rfl⟩ : syracuseStep 2037325 = 763997) (by norm_num)
theorem B2717261 : Blo 1809606 2717261 := bbase (se 3 (by rfl) ⟨509486, by rfl⟩ : syracuseStep 2717261 = 1018973) (by norm_num)
theorem B11605589 : Blo 1809606 11605589 := bbase (se 8 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 11605589 = 136003) (by norm_num)
theorem B4585045 : Blo 1809606 4585045 := bbase (se 8 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 4585045 = 53731) (by norm_num)
theorem B2717285 : Blo 1809606 2717285 := bbase (se 4 (by rfl) ⟨254745, by rfl⟩ : syracuseStep 2717285 = 509491) (by norm_num)
theorem B2037361 : Blo 1809606 2037361 := bbase (se 2 (by rfl) ⟨764010, by rfl⟩ : syracuseStep 2037361 = 1528021) (by norm_num)
theorem B2479741 : Blo 1809606 2479741 := bbase (se 3 (by rfl) ⟨464951, by rfl⟩ : syracuseStep 2479741 = 929903) (by norm_num)
theorem B2717309 : Blo 1809606 2717309 := bbase (se 3 (by rfl) ⟨509495, by rfl⟩ : syracuseStep 2717309 = 1018991) (by norm_num)
theorem B2037397 : Blo 1809606 2037397 := bbase (se 6 (by rfl) ⟨47751, by rfl⟩ : syracuseStep 2037397 = 95503) (by norm_num)
theorem B2717333 : Blo 1809606 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B2717357 : Blo 1809606 2717357 := bbase (se 3 (by rfl) ⟨509504, by rfl⟩ : syracuseStep 2717357 = 1019009) (by norm_num)
theorem B2037433 : Blo 1809606 2037433 := bbase (se 2 (by rfl) ⟨764037, by rfl⟩ : syracuseStep 2037433 = 1528075) (by norm_num)
theorem B4585157 : Blo 1809606 4585157 := bbase (se 4 (by rfl) ⟨429858, by rfl⟩ : syracuseStep 4585157 = 859717) (by norm_num)
theorem B2717381 : Blo 1809606 2717381 := bbase (se 4 (by rfl) ⟨254754, by rfl⟩ : syracuseStep 2717381 = 509509) (by norm_num)
theorem B9164501 : Blo 1809606 9164501 := bbase (se 7 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 9164501 = 214793) (by norm_num)
theorem B2037469 : Blo 1809606 2037469 := bbase (se 3 (by rfl) ⟨382025, by rfl⟩ : syracuseStep 2037469 = 764051) (by norm_num)
theorem B2717405 : Blo 1809606 2717405 := bbase (se 3 (by rfl) ⟨509513, by rfl⟩ : syracuseStep 2717405 = 1019027) (by norm_num)
theorem B2291429 : Blo 1809606 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B3307261 : Blo 1809606 3307261 := bbase (se 3 (by rfl) ⟨620111, by rfl⟩ : syracuseStep 3307261 = 1240223) (by norm_num)
theorem B2037505 : Blo 1809606 2037505 := bbase (se 2 (by rfl) ⟨764064, by rfl⟩ : syracuseStep 2037505 = 1528129) (by norm_num)
theorem B2291485 : Blo 1809606 2291485 := bbase (se 3 (by rfl) ⟨429653, by rfl⟩ : syracuseStep 2291485 = 859307) (by norm_num)
theorem B5797669 : Blo 1809606 5797669 := bbase (se 4 (by rfl) ⟨543531, by rfl⟩ : syracuseStep 5797669 = 1087063) (by norm_num)
theorem B6108965 : Blo 1809606 6108965 := bbase (se 4 (by rfl) ⟨572715, by rfl⟩ : syracuseStep 6108965 = 1145431) (by norm_num)
theorem B2037541 : Blo 1809606 2037541 := bbase (se 4 (by rfl) ⟨191019, by rfl⟩ : syracuseStep 2037541 = 382039) (by norm_num)
theorem B3438389 : Blo 1809606 3438389 := bbase (se 5 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 3438389 = 322349) (by norm_num)
theorem B2037577 : Blo 1809606 2037577 := bbase (se 2 (by rfl) ⟨764091, by rfl⟩ : syracuseStep 2037577 = 1528183) (by norm_num)
theorem B2037613 : Blo 1809606 2037613 := bbase (se 3 (by rfl) ⟨382052, by rfl⟩ : syracuseStep 2037613 = 764105) (by norm_num)
theorem B17872757 : Blo 1809606 17872757 := bbase (se 5 (by rfl) ⟨837785, by rfl⟩ : syracuseStep 17872757 = 1675571) (by norm_num)
theorem B2291581 : Blo 1809606 2291581 := bbase (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) (by norm_num)
theorem B4585349 : Blo 1809606 4585349 := bbase (se 4 (by rfl) ⟨429876, by rfl⟩ : syracuseStep 4585349 = 859753) (by norm_num)
theorem B2037649 : Blo 1809606 2037649 := bbase (se 2 (by rfl) ⟨764118, by rfl⟩ : syracuseStep 2037649 = 1528237) (by norm_num)
theorem B2037685 : Blo 1809606 2037685 := bbase (se 5 (by rfl) ⟨95516, by rfl⟩ : syracuseStep 2037685 = 191033) (by norm_num)
theorem B3438541 : Blo 1809606 3438541 := bbase (se 3 (by rfl) ⟨644726, by rfl⟩ : syracuseStep 3438541 = 1289453) (by norm_num)
theorem B2037721 : Blo 1809606 2037721 := bbase (se 2 (by rfl) ⟨764145, by rfl⟩ : syracuseStep 2037721 = 1528291) (by norm_num)
theorem B2578405 : Blo 1809606 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B2037757 : Blo 1809606 2037757 := bbase (se 3 (by rfl) ⟨382079, by rfl⟩ : syracuseStep 2037757 = 764159) (by norm_num)
theorem B13752341 : Blo 1809606 13752341 := bbase (se 6 (by rfl) ⟨322320, by rfl⟩ : syracuseStep 13752341 = 644641) (by norm_num)
theorem B2037793 : Blo 1809606 2037793 := bbase (se 2 (by rfl) ⟨764172, by rfl⟩ : syracuseStep 2037793 = 1528345) (by norm_num)
theorem B2291753 : Blo 1809606 2291753 := bbase (se 2 (by rfl) ⟨859407, by rfl⟩ : syracuseStep 2291753 = 1718815) (by norm_num)
theorem B7338053 : Blo 1809606 7338053 := bbase (se 4 (by rfl) ⟨687942, by rfl⟩ : syracuseStep 7338053 = 1375885) (by norm_num)
theorem B2037829 : Blo 1809606 2037829 := bbase (se 4 (by rfl) ⟨191046, by rfl⟩ : syracuseStep 2037829 = 382093) (by norm_num)
theorem B2291809 : Blo 1809606 2291809 := bbase (se 2 (by rfl) ⟨859428, by rfl⟩ : syracuseStep 2291809 = 1718857) (by norm_num)
theorem B2037865 : Blo 1809606 2037865 := bbase (se 2 (by rfl) ⟨764199, by rfl⟩ : syracuseStep 2037865 = 1528399) (by norm_num)
theorem B16750709 : Blo 1809606 16750709 := bbase (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) (by norm_num)
theorem B2037901 : Blo 1809606 2037901 := bbase (se 3 (by rfl) ⟨382106, by rfl⟩ : syracuseStep 2037901 = 764213) (by norm_num)
theorem B6871189 : Blo 1809606 6871189 := bbase (se 6 (by rfl) ⟨161043, by rfl⟩ : syracuseStep 6871189 = 322087) (by norm_num)
theorem B2037937 : Blo 1809606 2037937 := bbase (se 2 (by rfl) ⟨764226, by rfl⟩ : syracuseStep 2037937 = 1528453) (by norm_num)
theorem B2291905 : Blo 1809606 2291905 := bbase (se 2 (by rfl) ⟨859464, by rfl⟩ : syracuseStep 2291905 = 1718929) (by norm_num)
theorem B6109397 : Blo 1809606 6109397 := bbase (se 7 (by rfl) ⟨71594, by rfl⟩ : syracuseStep 6109397 = 143189) (by norm_num)
theorem B2037973 : Blo 1809606 2037973 := bbase (se 7 (by rfl) ⟨23882, by rfl⟩ : syracuseStep 2037973 = 47765) (by norm_num)
theorem B17406197 : Blo 1809606 17406197 := bbase (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) (by norm_num)
theorem B2038009 : Blo 1809606 2038009 := bbase (se 2 (by rfl) ⟨764253, by rfl⟩ : syracuseStep 2038009 = 1528507) (by norm_num)
theorem B3053821 : Blo 1809606 3053821 := bbase (se 3 (by rfl) ⟨572591, by rfl⟩ : syracuseStep 3053821 = 1145183) (by norm_num)
theorem B3438845 : Blo 1809606 3438845 := bbase (se 3 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 3438845 = 1289567) (by norm_num)
theorem B2038045 : Blo 1809606 2038045 := bbase (se 3 (by rfl) ⟨382133, by rfl⟩ : syracuseStep 2038045 = 764267) (by norm_num)
theorem B3053909 : Blo 1809606 3053909 := bbase (se 10 (by rfl) ⟨4473, by rfl⟩ : syracuseStep 3053909 = 8947) (by norm_num)
theorem B3864925 : Blo 1809606 3864925 := bbase (se 3 (by rfl) ⟨724673, by rfl⟩ : syracuseStep 3864925 = 1449347) (by norm_num)
theorem B2292077 : Blo 1809606 2292077 := bbase (se 3 (by rfl) ⟨429764, by rfl⟩ : syracuseStep 2292077 = 859529) (by norm_num)
theorem B2685317 : Blo 1809606 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B2292133 : Blo 1809606 2292133 := bbase (se 4 (by rfl) ⟨214887, by rfl⟩ : syracuseStep 2292133 = 429775) (by norm_num)
theorem B13744565 : Blo 1809606 13744565 := bbase (se 5 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 13744565 = 1288553) (by norm_num)
theorem B6871493 : Blo 1809606 6871493 := bbase (se 4 (by rfl) ⟨644202, by rfl⟩ : syracuseStep 6871493 = 1288405) (by norm_num)
theorem B3054037 : Blo 1809606 3054037 := bbase (se 7 (by rfl) ⟨35789, by rfl⟩ : syracuseStep 3054037 = 71579) (by norm_num)
theorem B2292229 : Blo 1809606 2292229 := bbase (se 4 (by rfl) ⟨214896, by rfl⟩ : syracuseStep 2292229 = 429793) (by norm_num)
theorem B3054125 : Blo 1809606 3054125 := bbase (se 3 (by rfl) ⟨572648, by rfl⟩ : syracuseStep 3054125 = 1145297) (by norm_num)
theorem B2578997 : Blo 1809606 2578997 := bbase (se 5 (by rfl) ⟨120890, by rfl⟩ : syracuseStep 2578997 = 241781) (by norm_num)
theorem B66099797 : Blo 1809606 66099797 := bbase (se 8 (by rfl) ⟨387303, by rfl⟩ : syracuseStep 66099797 = 774607) (by norm_num)
theorem B2611805 : Blo 1809606 2611805 := bbase (se 3 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 2611805 = 979427) (by norm_num)
theorem B6109829 : Blo 1809606 6109829 := bbase (se 4 (by rfl) ⟨572796, by rfl⟩ : syracuseStep 6109829 = 1145593) (by norm_num)
theorem B2579077 : Blo 1809606 2579077 := bbase (se 4 (by rfl) ⟨241788, by rfl⟩ : syracuseStep 2579077 = 483577) (by norm_num)
theorem B3054253 : Blo 1809606 3054253 := bbase (se 3 (by rfl) ⟨572672, by rfl⟩ : syracuseStep 3054253 = 1145345) (by norm_num)
theorem B2292401 : Blo 1809606 2292401 := bbase (se 2 (by rfl) ⟨859650, by rfl⟩ : syracuseStep 2292401 = 1719301) (by norm_num)
theorem B4348637 : Blo 1809606 4348637 := bbase (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) (by norm_num)
theorem B2292457 : Blo 1809606 2292457 := bbase (se 2 (by rfl) ⟨859671, by rfl⟩ : syracuseStep 2292457 = 1719343) (by norm_num)
theorem B2579197 : Blo 1809606 2579197 := bbase (se 3 (by rfl) ⟨483599, by rfl⟩ : syracuseStep 2579197 = 967199) (by norm_num)
theorem B3054341 : Blo 1809606 3054341 := bbase (se 4 (by rfl) ⟨286344, by rfl⟩ : syracuseStep 3054341 = 572689) (by norm_num)
theorem B7732037 : Blo 1809606 7732037 := bbase (se 4 (by rfl) ⟨724878, by rfl⟩ : syracuseStep 7732037 = 1449757) (by norm_num)
theorem B2292553 : Blo 1809606 2292553 := bbase (se 2 (by rfl) ⟨859707, by rfl⟩ : syracuseStep 2292553 = 1719415) (by norm_num)
theorem B3865421 : Blo 1809606 3865421 := bbase (se 3 (by rfl) ⟨724766, by rfl⟩ : syracuseStep 3865421 = 1449533) (by norm_num)
theorem B74316629 : Blo 1809606 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B2579293 : Blo 1809606 2579293 := bbase (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) (by norm_num)
theorem B3054469 : Blo 1809606 3054469 := bbase (se 4 (by rfl) ⟨286356, by rfl⟩ : syracuseStep 3054469 = 572713) (by norm_num)
theorem B20626325 : Blo 1809606 20626325 := bbase (se 6 (by rfl) ⟨483429, by rfl⟩ : syracuseStep 20626325 = 966859) (by norm_num)
theorem B4348829 : Blo 1809606 4348829 := bbase (se 3 (by rfl) ⟨815405, by rfl⟩ : syracuseStep 4348829 = 1630811) (by norm_num)
theorem B27884501 : Blo 1809606 27884501 := bbase (se 7 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 27884501 = 653543) (by norm_num)
theorem B3054557 : Blo 1809606 3054557 := bbase (se 3 (by rfl) ⟨572729, by rfl⟩ : syracuseStep 3054557 = 1145459) (by norm_num)
theorem B9165797 : Blo 1809606 9165797 := bbase (se 4 (by rfl) ⟨859293, by rfl⟩ : syracuseStep 9165797 = 1718587) (by norm_num)
theorem B2292725 : Blo 1809606 2292725 := bbase (se 5 (by rfl) ⟨107471, by rfl⟩ : syracuseStep 2292725 = 214943) (by norm_num)
theorem B4709389 : Blo 1809606 4709389 := bbase (se 3 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 4709389 = 1766021) (by norm_num)
theorem B2292781 : Blo 1809606 2292781 := bbase (se 3 (by rfl) ⟨429896, by rfl⟩ : syracuseStep 2292781 = 859793) (by norm_num)
theorem B6110261 : Blo 1809606 6110261 := bbase (se 5 (by rfl) ⟨286418, by rfl⟩ : syracuseStep 6110261 = 572837) (by norm_num)
theorem B3054685 : Blo 1809606 3054685 := bbase (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) (by norm_num)
theorem B1932437 : Blo 1809606 1932437 := bbase (se 6 (by rfl) ⟨45291, by rfl⟩ : syracuseStep 1932437 = 90583) (by norm_num)
theorem B3054773 : Blo 1809606 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B3669293 : Blo 1809606 3669293 := bbase (se 3 (by rfl) ⟨687992, by rfl⟩ : syracuseStep 3669293 = 1375985) (by norm_num)
theorem B3054901 : Blo 1809606 3054901 := bbase (se 5 (by rfl) ⟨143198, by rfl⟩ : syracuseStep 3054901 = 286397) (by norm_num)
theorem B2899309 : Blo 1809606 2899309 := bbase (se 3 (by rfl) ⟨543620, by rfl⟩ : syracuseStep 2899309 = 1087241) (by norm_num)
theorem B3054989 : Blo 1809606 3054989 := bbase (se 3 (by rfl) ⟨572810, by rfl⟩ : syracuseStep 3054989 = 1145621) (by norm_num)
theorem B8256917 : Blo 1809606 8256917 := bbase (se 6 (by rfl) ⟨193521, by rfl⟩ : syracuseStep 8256917 = 387043) (by norm_num)
theorem B6110693 : Blo 1809606 6110693 := bbase (se 4 (by rfl) ⟨572877, by rfl⟩ : syracuseStep 6110693 = 1145755) (by norm_num)
theorem B3055117 : Blo 1809606 3055117 := bbase (se 3 (by rfl) ⟨572834, by rfl⟩ : syracuseStep 3055117 = 1145669) (by norm_num)
theorem B1932881 : Blo 1809606 1932881 := bbase (se 2 (by rfl) ⟨724830, by rfl⟩ : syracuseStep 1932881 = 1449661) (by norm_num)
theorem B35274325 : Blo 1809606 35274325 := bbase (se 8 (by rfl) ⟨206685, by rfl⟩ : syracuseStep 35274325 = 413371) (by norm_num)
theorem B3055205 : Blo 1809606 3055205 := bbase (se 4 (by rfl) ⟨286425, by rfl⟩ : syracuseStep 3055205 = 572851) (by norm_num)
theorem B1932941 : Blo 1809606 1932941 := bbase (se 3 (by rfl) ⟨362426, by rfl⟩ : syracuseStep 1932941 = 724853) (by norm_num)
theorem B3866309 : Blo 1809606 3866309 := bbase (se 4 (by rfl) ⟨362466, by rfl⟩ : syracuseStep 3866309 = 724933) (by norm_num)
theorem B2752213 : Blo 1809606 2752213 := bbase (se 7 (by rfl) ⟨32252, by rfl⟩ : syracuseStep 2752213 = 64505) (by norm_num)
theorem B3055333 : Blo 1809606 3055333 := bbase (se 4 (by rfl) ⟨286437, by rfl⟩ : syracuseStep 3055333 = 572875) (by norm_num)
theorem B2752237 : Blo 1809606 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B1933069 : Blo 1809606 1933069 := bbase (se 3 (by rfl) ⟨362450, by rfl⟩ : syracuseStep 1933069 = 724901) (by norm_num)
theorem B2899757 : Blo 1809606 2899757 := bbase (se 3 (by rfl) ⟨543704, by rfl⟩ : syracuseStep 2899757 = 1087409) (by norm_num)
theorem B3866429 : Blo 1809606 3866429 := bbase (se 3 (by rfl) ⟨724955, by rfl⟩ : syracuseStep 3866429 = 1449911) (by norm_num)
theorem B3055421 : Blo 1809606 3055421 := bbase (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) (by norm_num)
theorem B88137557 : Blo 1809606 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B6528869 : Blo 1809606 6528869 := bbase (se 4 (by rfl) ⟨612081, by rfl⟩ : syracuseStep 6528869 = 1224163) (by norm_num)
theorem B3669877 : Blo 1809606 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B6111125 : Blo 1809606 6111125 := bbase (se 6 (by rfl) ⟨143229, by rfl⟩ : syracuseStep 6111125 = 286459) (by norm_num)
theorem B3055549 : Blo 1809606 3055549 := bbase (se 3 (by rfl) ⟨572915, by rfl⟩ : syracuseStep 3055549 = 1145831) (by norm_num)
theorem B2899957 : Blo 1809606 2899957 := bbase (se 5 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 2899957 = 271871) (by norm_num)
theorem B1810435 : Blo 1809606 1810435 := bstep (se 1 (by rfl) ⟨1357826, by rfl⟩ : syracuseStep 1810435 = 2715653) B2715653
theorem B1810451 : Blo 1809606 1810451 := bstep (se 1 (by rfl) ⟨1357838, by rfl⟩ : syracuseStep 1810451 = 2715677) B2715677
theorem B1810467 : Blo 1809606 1810467 := bstep (se 1 (by rfl) ⟨1357850, by rfl⟩ : syracuseStep 1810467 = 2715701) B2715701
theorem B1810483 : Blo 1809606 1810483 := bstep (se 1 (by rfl) ⟨1357862, by rfl⟩ : syracuseStep 1810483 = 2715725) B2715725
theorem B1810499 : Blo 1809606 1810499 := bstep (se 1 (by rfl) ⟨1357874, by rfl⟩ : syracuseStep 1810499 = 2715749) B2715749
theorem B1810515 : Blo 1809606 1810515 := bstep (se 1 (by rfl) ⟨1357886, by rfl⟩ : syracuseStep 1810515 = 2715773) B2715773
theorem B2900065 : Blo 1809606 2900065 := bstep (se 2 (by rfl) ⟨1087524, by rfl⟩ : syracuseStep 2900065 = 2175049) B2175049
theorem B1810531 : Blo 1809606 1810531 := bstep (se 1 (by rfl) ⟨1357898, by rfl⟩ : syracuseStep 1810531 = 2715797) B2715797
theorem B6111341 : Blo 1809606 6111341 := bstep (se 3 (by rfl) ⟨1145876, by rfl⟩ : syracuseStep 6111341 = 2291753) B2291753
theorem B1810547 : Blo 1809606 1810547 := bstep (se 1 (by rfl) ⟨1357910, by rfl⟩ : syracuseStep 1810547 = 2715821) B2715821
theorem B3055745 : Blo 1809606 3055745 := bstep (se 2 (by rfl) ⟨1145904, by rfl⟩ : syracuseStep 3055745 = 2291809) B2291809
theorem B1810563 : Blo 1809606 1810563 := bstep (se 1 (by rfl) ⟨1357922, by rfl⟩ : syracuseStep 1810563 = 2715845) B2715845
theorem B1810579 : Blo 1809606 1810579 := bstep (se 1 (by rfl) ⟨1357934, by rfl⟩ : syracuseStep 1810579 = 2715869) B2715869
theorem B2900129 : Blo 1809606 2900129 := bstep (se 2 (by rfl) ⟨1087548, by rfl⟩ : syracuseStep 2900129 = 2175097) B2175097
theorem B1933475 : Blo 1809606 1933475 := bstep (se 1 (by rfl) ⟨1450106, by rfl⟩ : syracuseStep 1933475 = 2900213) B2900213
theorem B1810595 : Blo 1809606 1810595 := bstep (se 1 (by rfl) ⟨1357946, by rfl⟩ : syracuseStep 1810595 = 2715893) B2715893
theorem B6111395 : Blo 1809606 6111395 := bstep (se 1 (by rfl) ⟨4583546, by rfl⟩ : syracuseStep 6111395 = 9167093) B9167093
theorem B1810611 : Blo 1809606 1810611 := bstep (se 1 (by rfl) ⟨1357958, by rfl⟩ : syracuseStep 1810611 = 2715917) B2715917
theorem B1810627 : Blo 1809606 1810627 := bstep (se 1 (by rfl) ⟨1357970, by rfl⟩ : syracuseStep 1810627 = 2715941) B2715941
theorem B1810643 : Blo 1809606 1810643 := bstep (se 1 (by rfl) ⟨1357982, by rfl⟩ : syracuseStep 1810643 = 2715965) B2715965
theorem B1810659 : Blo 1809606 1810659 := bstep (se 1 (by rfl) ⟨1357994, by rfl⟩ : syracuseStep 1810659 = 2715989) B2715989
theorem B1810675 : Blo 1809606 1810675 := bstep (se 1 (by rfl) ⟨1358006, by rfl⟩ : syracuseStep 1810675 = 2716013) B2716013
theorem B3055873 : Blo 1809606 3055873 := bstep (se 2 (by rfl) ⟨1145952, by rfl⟩ : syracuseStep 3055873 = 2291905) B2291905
theorem B1810691 : Blo 1809606 1810691 := bstep (se 1 (by rfl) ⟨1358018, by rfl⟩ : syracuseStep 1810691 = 2716037) B2716037
theorem B8257805 : Blo 1809606 8257805 := bstep (se 3 (by rfl) ⟨1548338, by rfl⟩ : syracuseStep 8257805 = 3096677) B3096677
theorem B1810707 : Blo 1809606 1810707 := bstep (se 1 (by rfl) ⟨1358030, by rfl⟩ : syracuseStep 1810707 = 2716061) B2716061
theorem B1810723 : Blo 1809606 1810723 := bstep (se 1 (by rfl) ⟨1358042, by rfl⟩ : syracuseStep 1810723 = 2716085) B2716085
theorem B3055907 : Blo 1809606 3055907 := bstep (se 1 (by rfl) ⟨2291930, by rfl⟩ : syracuseStep 3055907 = 4583861) B4583861
theorem B1810739 : Blo 1809606 1810739 := bstep (se 1 (by rfl) ⟨1358054, by rfl⟩ : syracuseStep 1810739 = 2716109) B2716109
theorem B1810755 : Blo 1809606 1810755 := bstep (se 1 (by rfl) ⟨1358066, by rfl⟩ : syracuseStep 1810755 = 2716133) B2716133
theorem B10314053 : Blo 1809606 10314053 := bstep (se 4 (by rfl) ⟨966942, by rfl⟩ : syracuseStep 10314053 = 1933885) B1933885
theorem B4071761 : Blo 1809606 4071761 := bstep (se 2 (by rfl) ⟨1526910, by rfl⟩ : syracuseStep 4071761 = 3053821) B3053821
theorem B1810771 : Blo 1809606 1810771 := bstep (se 1 (by rfl) ⟨1358078, by rfl⟩ : syracuseStep 1810771 = 2716157) B2716157
theorem B4071779 : Blo 1809606 4071779 := bstep (se 1 (by rfl) ⟨3053834, by rfl⟩ : syracuseStep 4071779 = 6107669) B6107669
theorem B1810787 : Blo 1809606 1810787 := bstep (se 1 (by rfl) ⟨1358090, by rfl⟩ : syracuseStep 1810787 = 2716181) B2716181
theorem B1810803 : Blo 1809606 1810803 := bstep (se 1 (by rfl) ⟨1358102, by rfl⟩ : syracuseStep 1810803 = 2716205) B2716205
theorem B1810819 : Blo 1809606 1810819 := bstep (se 1 (by rfl) ⟨1358114, by rfl⟩ : syracuseStep 1810819 = 2716229) B2716229
theorem B5153165 : Blo 1809606 5153165 := bstep (se 3 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 5153165 = 1932437) B1932437
theorem B1810835 : Blo 1809606 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B1810851 : Blo 1809606 1810851 := bstep (se 1 (by rfl) ⟨1358138, by rfl⟩ : syracuseStep 1810851 = 2716277) B2716277
theorem B3056035 : Blo 1809606 3056035 := bstep (se 1 (by rfl) ⟨2292026, by rfl⟩ : syracuseStep 3056035 = 4584053) B4584053
theorem B6111665 : Blo 1809606 6111665 := bstep (se 2 (by rfl) ⟨2291874, by rfl⟩ : syracuseStep 6111665 = 4583749) B4583749
theorem B1810867 : Blo 1809606 1810867 := bstep (se 1 (by rfl) ⟨1358150, by rfl⟩ : syracuseStep 1810867 = 2716301) B2716301
theorem B1810883 : Blo 1809606 1810883 := bstep (se 1 (by rfl) ⟨1358162, by rfl⟩ : syracuseStep 1810883 = 2716325) B2716325
theorem B5153233 : Blo 1809606 5153233 := bstep (se 2 (by rfl) ⟨1932462, by rfl⟩ : syracuseStep 5153233 = 3864925) B3864925
theorem B1810899 : Blo 1809606 1810899 := bstep (se 1 (by rfl) ⟨1358174, by rfl⟩ : syracuseStep 1810899 = 2716349) B2716349
theorem B1810915 : Blo 1809606 1810915 := bstep (se 1 (by rfl) ⟨1358186, by rfl⟩ : syracuseStep 1810915 = 2716373) B2716373
theorem B1810931 : Blo 1809606 1810931 := bstep (se 1 (by rfl) ⟨1358198, by rfl⟩ : syracuseStep 1810931 = 2716397) B2716397
theorem B2064899 : Blo 1809606 2064899 := bstep (se 1 (by rfl) ⟨1548674, by rfl⟩ : syracuseStep 2064899 = 3097349) B3097349
theorem B1810947 : Blo 1809606 1810947 := bstep (se 1 (by rfl) ⟨1358210, by rfl⟩ : syracuseStep 1810947 = 2716421) B2716421
theorem B5227021 : Blo 1809606 5227021 := bstep (se 3 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 5227021 = 1960133) B1960133
theorem B1810963 : Blo 1809606 1810963 := bstep (se 1 (by rfl) ⟨1358222, by rfl⟩ : syracuseStep 1810963 = 2716445) B2716445
theorem B1810979 : Blo 1809606 1810979 := bstep (se 1 (by rfl) ⟨1358234, by rfl⟩ : syracuseStep 1810979 = 2716469) B2716469
theorem B3056177 : Blo 1809606 3056177 := bstep (se 2 (by rfl) ⟨1146066, by rfl⟩ : syracuseStep 3056177 = 2292133) B2292133
theorem B1810995 : Blo 1809606 1810995 := bstep (se 1 (by rfl) ⟨1358246, by rfl⟩ : syracuseStep 1810995 = 2716493) B2716493
theorem B1811011 : Blo 1809606 1811011 := bstep (se 1 (by rfl) ⟨1358258, by rfl⟩ : syracuseStep 1811011 = 2716517) B2716517
theorem B1811027 : Blo 1809606 1811027 := bstep (se 1 (by rfl) ⟨1358270, by rfl⟩ : syracuseStep 1811027 = 2716541) B2716541
theorem B1811043 : Blo 1809606 1811043 := bstep (se 1 (by rfl) ⟨1358282, by rfl⟩ : syracuseStep 1811043 = 2716565) B2716565
theorem B4072049 : Blo 1809606 4072049 := bstep (se 2 (by rfl) ⟨1527018, by rfl⟩ : syracuseStep 4072049 = 3054037) B3054037
theorem B1811059 : Blo 1809606 1811059 := bstep (se 1 (by rfl) ⟨1358294, by rfl⟩ : syracuseStep 1811059 = 2716589) B2716589
theorem B4072067 : Blo 1809606 4072067 := bstep (se 1 (by rfl) ⟨3054050, by rfl⟩ : syracuseStep 4072067 = 6108101) B6108101
theorem B3097219 : Blo 1809606 3097219 := bstep (se 1 (by rfl) ⟨2322914, by rfl⟩ : syracuseStep 3097219 = 4645829) B4645829
theorem B1811075 : Blo 1809606 1811075 := bstep (se 1 (by rfl) ⟨1358306, by rfl⟩ : syracuseStep 1811075 = 2716613) B2716613
theorem B1811091 : Blo 1809606 1811091 := bstep (se 1 (by rfl) ⟨1358318, by rfl⟩ : syracuseStep 1811091 = 2716637) B2716637
theorem B1811107 : Blo 1809606 1811107 := bstep (se 1 (by rfl) ⟨1358330, by rfl⟩ : syracuseStep 1811107 = 2716661) B2716661
theorem B3056305 : Blo 1809606 3056305 := bstep (se 2 (by rfl) ⟨1146114, by rfl⟩ : syracuseStep 3056305 = 2292229) B2292229
theorem B1811123 : Blo 1809606 1811123 := bstep (se 1 (by rfl) ⟨1358342, by rfl⟩ : syracuseStep 1811123 = 2716685) B2716685
theorem B5800643 : Blo 1809606 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B1811139 : Blo 1809606 1811139 := bstep (se 1 (by rfl) ⟨1358354, by rfl⟩ : syracuseStep 1811139 = 2716709) B2716709
theorem B19579589 : Blo 1809606 19579589 := bstep (se 4 (by rfl) ⟨1835586, by rfl⟩ : syracuseStep 19579589 = 3671173) B3671173
theorem B1811155 : Blo 1809606 1811155 := bstep (se 1 (by rfl) ⟨1358366, by rfl⟩ : syracuseStep 1811155 = 2716733) B2716733
theorem B3056339 : Blo 1809606 3056339 := bstep (se 1 (by rfl) ⟨2292254, by rfl⟩ : syracuseStep 3056339 = 4584509) B4584509
theorem B5153507 : Blo 1809606 5153507 := bstep (se 1 (by rfl) ⟨3865130, by rfl⟩ : syracuseStep 5153507 = 7730261) B7730261
theorem B34792163 : Blo 1809606 34792163 := bstep (se 1 (by rfl) ⟨26094122, by rfl⟩ : syracuseStep 34792163 = 52188245) B52188245
theorem B1811171 : Blo 1809606 1811171 := bstep (se 1 (by rfl) ⟨1358378, by rfl⟩ : syracuseStep 1811171 = 2716757) B2716757
theorem B1811187 : Blo 1809606 1811187 := bstep (se 1 (by rfl) ⟨1358390, by rfl⟩ : syracuseStep 1811187 = 2716781) B2716781
theorem B1811203 : Blo 1809606 1811203 := bstep (se 1 (by rfl) ⟨1358402, by rfl⟩ : syracuseStep 1811203 = 2716805) B2716805
theorem B1811219 : Blo 1809606 1811219 := bstep (se 1 (by rfl) ⟨1358414, by rfl⟩ : syracuseStep 1811219 = 2716829) B2716829
theorem B1811235 : Blo 1809606 1811235 := bstep (se 1 (by rfl) ⟨1358426, by rfl⟩ : syracuseStep 1811235 = 2716853) B2716853
theorem B1811251 : Blo 1809606 1811251 := bstep (se 1 (by rfl) ⟨1358438, by rfl⟩ : syracuseStep 1811251 = 2716877) B2716877
theorem B1811267 : Blo 1809606 1811267 := bstep (se 1 (by rfl) ⟨1358450, by rfl⟩ : syracuseStep 1811267 = 2716901) B2716901
theorem B3056467 : Blo 1809606 3056467 := bstep (se 1 (by rfl) ⟨2292350, by rfl⟩ : syracuseStep 3056467 = 4584701) B4584701
theorem B1811283 : Blo 1809606 1811283 := bstep (se 1 (by rfl) ⟨1358462, by rfl⟩ : syracuseStep 1811283 = 2716925) B2716925
theorem B1811299 : Blo 1809606 1811299 := bstep (se 1 (by rfl) ⟨1358474, by rfl⟩ : syracuseStep 1811299 = 2716949) B2716949
theorem B5882723 : Blo 1809606 5882723 := bstep (se 1 (by rfl) ⟨4412042, by rfl⟩ : syracuseStep 5882723 = 8824085) B8824085
theorem B9290609 : Blo 1809606 9290609 := bstep (se 2 (by rfl) ⟨3483978, by rfl⟩ : syracuseStep 9290609 = 6967957) B6967957
theorem B1811315 : Blo 1809606 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B5800835 : Blo 1809606 5800835 := bstep (se 1 (by rfl) ⟨4350626, by rfl⟩ : syracuseStep 5800835 = 8701253) B8701253
theorem B1811331 : Blo 1809606 1811331 := bstep (se 1 (by rfl) ⟨1358498, by rfl⟩ : syracuseStep 1811331 = 2716997) B2716997
theorem B4072337 : Blo 1809606 4072337 := bstep (se 2 (by rfl) ⟨1527126, by rfl⟩ : syracuseStep 4072337 = 3054253) B3054253
theorem B1934227 : Blo 1809606 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B1811347 : Blo 1809606 1811347 := bstep (se 1 (by rfl) ⟨1358510, by rfl⟩ : syracuseStep 1811347 = 2717021) B2717021
theorem B4072355 : Blo 1809606 4072355 := bstep (se 1 (by rfl) ⟨3054266, by rfl⟩ : syracuseStep 4072355 = 6108533) B6108533
theorem B1811363 : Blo 1809606 1811363 := bstep (se 1 (by rfl) ⟨1358522, by rfl⟩ : syracuseStep 1811363 = 2717045) B2717045
theorem B1811379 : Blo 1809606 1811379 := bstep (se 1 (by rfl) ⟨1358534, by rfl⟩ : syracuseStep 1811379 = 2717069) B2717069
theorem B1811395 : Blo 1809606 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B6112205 : Blo 1809606 6112205 := bstep (se 3 (by rfl) ⟨1146038, by rfl⟩ : syracuseStep 6112205 = 2292077) B2292077
theorem B1811411 : Blo 1809606 1811411 := bstep (se 1 (by rfl) ⟨1358558, by rfl⟩ : syracuseStep 1811411 = 2717117) B2717117
theorem B3056609 : Blo 1809606 3056609 := bstep (se 2 (by rfl) ⟨1146228, by rfl⟩ : syracuseStep 3056609 = 2292457) B2292457
theorem B1811427 : Blo 1809606 1811427 := bstep (se 1 (by rfl) ⟨1358570, by rfl⟩ : syracuseStep 1811427 = 2717141) B2717141
theorem B1811443 : Blo 1809606 1811443 := bstep (se 1 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 1811443 = 2717165) B2717165
theorem B6112259 : Blo 1809606 6112259 := bstep (se 1 (by rfl) ⟨4584194, by rfl⟩ : syracuseStep 6112259 = 9168389) B9168389
theorem B1811459 : Blo 1809606 1811459 := bstep (se 1 (by rfl) ⟨1358594, by rfl⟩ : syracuseStep 1811459 = 2717189) B2717189
theorem B1811475 : Blo 1809606 1811475 := bstep (se 1 (by rfl) ⟨1358606, by rfl⟩ : syracuseStep 1811475 = 2717213) B2717213
theorem B1811491 : Blo 1809606 1811491 := bstep (se 1 (by rfl) ⟨1358618, by rfl⟩ : syracuseStep 1811491 = 2717237) B2717237
theorem B1811507 : Blo 1809606 1811507 := bstep (se 1 (by rfl) ⟨1358630, by rfl⟩ : syracuseStep 1811507 = 2717261) B2717261
theorem B1811523 : Blo 1809606 1811523 := bstep (se 1 (by rfl) ⟨1358642, by rfl⟩ : syracuseStep 1811523 = 2717285) B2717285
theorem B1811539 : Blo 1809606 1811539 := bstep (se 1 (by rfl) ⟨1358654, by rfl⟩ : syracuseStep 1811539 = 2717309) B2717309
theorem B3056737 : Blo 1809606 3056737 := bstep (se 2 (by rfl) ⟨1146276, by rfl⟩ : syracuseStep 3056737 = 2292553) B2292553
theorem B1811555 : Blo 1809606 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B1811571 : Blo 1809606 1811571 := bstep (se 1 (by rfl) ⟨1358678, by rfl⟩ : syracuseStep 1811571 = 2717357) B2717357
theorem B3056771 : Blo 1809606 3056771 := bstep (se 1 (by rfl) ⟨2292578, by rfl⟩ : syracuseStep 3056771 = 4585157) B4585157
theorem B1811587 : Blo 1809606 1811587 := bstep (se 1 (by rfl) ⟨1358690, by rfl⟩ : syracuseStep 1811587 = 2717381) B2717381
theorem B1811603 : Blo 1809606 1811603 := bstep (se 1 (by rfl) ⟨1358702, by rfl⟩ : syracuseStep 1811603 = 2717405) B2717405
theorem B4072625 : Blo 1809606 4072625 := bstep (se 2 (by rfl) ⟨1527234, by rfl⟩ : syracuseStep 4072625 = 3054469) B3054469
theorem B4072643 : Blo 1809606 4072643 := bstep (se 1 (by rfl) ⟨3054482, by rfl⟩ : syracuseStep 4072643 = 6108965) B6108965
theorem B2901187 : Blo 1809606 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B3867907 : Blo 1809606 3867907 := bstep (se 1 (by rfl) ⟨2900930, by rfl⟩ : syracuseStep 3867907 = 5801861) B5801861
theorem B3056899 : Blo 1809606 3056899 := bstep (se 1 (by rfl) ⟨2292674, by rfl⟩ : syracuseStep 3056899 = 4585349) B4585349
theorem B6112529 : Blo 1809606 6112529 := bstep (se 2 (by rfl) ⟨2292198, by rfl⟩ : syracuseStep 6112529 = 4584397) B4584397
theorem B9168227 : Blo 1809606 9168227 := bstep (se 1 (by rfl) ⟨6876170, by rfl⟩ : syracuseStep 9168227 = 13752341) B13752341
theorem B4892035 : Blo 1809606 4892035 := bstep (se 1 (by rfl) ⟨3669026, by rfl⟩ : syracuseStep 4892035 = 7338053) B7338053
theorem B3057041 : Blo 1809606 3057041 := bstep (se 2 (by rfl) ⟨1146390, by rfl⟩ : syracuseStep 3057041 = 2292781) B2292781
theorem B4408739 : Blo 1809606 4408739 := bstep (se 1 (by rfl) ⟨3306554, by rfl⟩ : syracuseStep 4408739 = 6613109) B6613109
theorem B11167139 : Blo 1809606 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B4072913 : Blo 1809606 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B4072931 : Blo 1809606 4072931 := bstep (se 1 (by rfl) ⟨3054698, by rfl⟩ : syracuseStep 4072931 = 6109397) B6109397
theorem B5801489 : Blo 1809606 5801489 := bstep (se 2 (by rfl) ⟨2175558, by rfl⟩ : syracuseStep 5801489 = 4351117) B4351117
theorem B5154349 : Blo 1809606 5154349 := bstep (se 3 (by rfl) ⟨966440, by rfl⟩ : syracuseStep 5154349 = 1932881) B1932881
theorem B6964813 : Blo 1809606 6964813 := bstep (se 3 (by rfl) ⟨1305902, by rfl⟩ : syracuseStep 6964813 = 2611805) B2611805
theorem B4580945 : Blo 1809606 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B3098225 : Blo 1809606 3098225 := bstep (se 2 (by rfl) ⟨1161834, by rfl⟩ : syracuseStep 3098225 = 2323669) B2323669
theorem B4580995 : Blo 1809606 4580995 := bstep (se 1 (by rfl) ⟨3435746, by rfl⟩ : syracuseStep 4580995 = 6871493) B6871493
theorem B5154509 : Blo 1809606 5154509 := bstep (se 3 (by rfl) ⟨966470, by rfl⟩ : syracuseStep 5154509 = 1932941) B1932941
theorem B44066531 : Blo 1809606 44066531 := bstep (se 1 (by rfl) ⟨33049898, by rfl⟩ : syracuseStep 44066531 = 66099797) B66099797
theorem B17393393 : Blo 1809606 17393393 := bstep (se 2 (by rfl) ⟨6522522, by rfl⟩ : syracuseStep 17393393 = 13045045) B13045045
theorem B4073201 : Blo 1809606 4073201 := bstep (se 2 (by rfl) ⟨1527450, by rfl⟩ : syracuseStep 4073201 = 3054901) B3054901
theorem B6874865 : Blo 1809606 6874865 := bstep (se 2 (by rfl) ⟨2578074, by rfl⟩ : syracuseStep 6874865 = 5156149) B5156149
theorem B2754305 : Blo 1809606 2754305 := bstep (se 2 (by rfl) ⟨1032864, by rfl⟩ : syracuseStep 2754305 = 2065729) B2065729
theorem B4073219 : Blo 1809606 4073219 := bstep (se 1 (by rfl) ⟨3054914, by rfl⟩ : syracuseStep 4073219 = 6109829) B6109829
theorem B4581137 : Blo 1809606 4581137 := bstep (se 2 (by rfl) ⟨1717926, by rfl⟩ : syracuseStep 4581137 = 3435853) B3435853
theorem B6113069 : Blo 1809606 6113069 := bstep (se 3 (by rfl) ⟨1146200, by rfl⟩ : syracuseStep 6113069 = 2292401) B2292401
theorem B13756229 : Blo 1809606 13756229 := bstep (se 4 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 13756229 = 2579293) B2579293
theorem B6113123 : Blo 1809606 6113123 := bstep (se 1 (by rfl) ⟨4584842, by rfl⟩ : syracuseStep 6113123 = 9169685) B9169685
theorem B14681969 : Blo 1809606 14681969 := bstep (se 2 (by rfl) ⟨5505738, by rfl⟩ : syracuseStep 14681969 = 11011477) B11011477
theorem B26109809 : Blo 1809606 26109809 := bstep (se 2 (by rfl) ⟨9791178, by rfl⟩ : syracuseStep 26109809 = 19582357) B19582357
theorem B5154691 : Blo 1809606 5154691 := bstep (se 1 (by rfl) ⟨3866018, by rfl⟩ : syracuseStep 5154691 = 7732037) B7732037
theorem B3098513 : Blo 1809606 3098513 := bstep (se 2 (by rfl) ⟨1161942, by rfl⟩ : syracuseStep 3098513 = 2323885) B2323885
theorem B15468515 : Blo 1809606 15468515 := bstep (se 1 (by rfl) ⟨11601386, by rfl⟩ : syracuseStep 15468515 = 23202773) B23202773
theorem B18589667 : Blo 1809606 18589667 := bstep (se 1 (by rfl) ⟨13942250, by rfl⟩ : syracuseStep 18589667 = 27884501) B27884501
theorem B4130801 : Blo 1809606 4130801 := bstep (se 2 (by rfl) ⟨1549050, by rfl⟩ : syracuseStep 4130801 = 3098101) B3098101
theorem B4073489 : Blo 1809606 4073489 := bstep (se 2 (by rfl) ⟨1527558, by rfl⟩ : syracuseStep 4073489 = 3055117) B3055117
theorem B6195217 : Blo 1809606 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B4073507 : Blo 1809606 4073507 := bstep (se 1 (by rfl) ⟨3055130, by rfl⟩ : syracuseStep 4073507 = 6110261) B6110261
theorem B16509041 : Blo 1809606 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B47032433 : Blo 1809606 47032433 := bstep (se 2 (by rfl) ⟨17637162, by rfl⟩ : syracuseStep 47032433 = 35274325) B35274325
theorem B6113393 : Blo 1809606 6113393 := bstep (se 2 (by rfl) ⟨2292522, by rfl⟩ : syracuseStep 6113393 = 4585045) B4585045
theorem B4130947 : Blo 1809606 4130947 := bstep (se 1 (by rfl) ⟨3098210, by rfl⟩ : syracuseStep 4130947 = 6196421) B6196421
theorem B9169037 : Blo 1809606 9169037 := bstep (se 3 (by rfl) ⟨1719194, by rfl⟩ : syracuseStep 9169037 = 3438389) B3438389
theorem B4647089 : Blo 1809606 4647089 := bstep (se 2 (by rfl) ⟨1742658, by rfl⟩ : syracuseStep 4647089 = 3485317) B3485317
theorem B6195491 : Blo 1809606 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B4073777 : Blo 1809606 4073777 := bstep (se 2 (by rfl) ⟨1527666, by rfl⟩ : syracuseStep 4073777 = 3055333) B3055333
theorem B2722097 : Blo 1809606 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B4073795 : Blo 1809606 4073795 := bstep (se 1 (by rfl) ⟨3055346, by rfl⟩ : syracuseStep 4073795 = 6110693) B6110693
theorem B4409681 : Blo 1809606 4409681 := bstep (se 2 (by rfl) ⟨1653630, by rfl⟩ : syracuseStep 4409681 = 3307261) B3307261
theorem B4893169 : Blo 1809606 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B4352579 : Blo 1809606 4352579 := bstep (se 1 (by rfl) ⟨3264434, by rfl⟩ : syracuseStep 4352579 = 6528869) B6528869
theorem B4074065 : Blo 1809606 4074065 := bstep (se 2 (by rfl) ⟨1527774, by rfl⟩ : syracuseStep 4074065 = 3055549) B3055549
theorem B4074083 : Blo 1809606 4074083 := bstep (se 1 (by rfl) ⟨3055562, by rfl⟩ : syracuseStep 4074083 = 6111125) B6111125
theorem B3263107 : Blo 1809606 3263107 := bstep (se 1 (by rfl) ⟨2447330, by rfl⟩ : syracuseStep 3263107 = 4894661) B4894661
theorem B6113933 : Blo 1809606 6113933 := bstep (se 3 (by rfl) ⟨1146362, by rfl⟩ : syracuseStep 6113933 = 2292725) B2292725
theorem B6113987 : Blo 1809606 6113987 := bstep (se 1 (by rfl) ⟨4585490, by rfl⟩ : syracuseStep 6113987 = 9170981) B9170981
theorem B4582129 : Blo 1809606 4582129 := bstep (se 2 (by rfl) ⟨1718298, by rfl⟩ : syracuseStep 4582129 = 3436597) B3436597
theorem B2714417 : Blo 1809606 2714417 := bstep (se 2 (by rfl) ⟨1017906, by rfl⟩ : syracuseStep 2714417 = 2035813) B2035813
theorem B2714435 : Blo 1809606 2714435 := bstep (se 1 (by rfl) ⟨2035826, by rfl⟩ : syracuseStep 2714435 = 4071653) B4071653
theorem B2714465 : Blo 1809606 2714465 := bstep (se 2 (by rfl) ⟨1017924, by rfl⟩ : syracuseStep 2714465 = 2035849) B2035849
theorem B9161585 : Blo 1809606 9161585 := bstep (se 2 (by rfl) ⟨3435594, by rfl⟩ : syracuseStep 9161585 = 6871189) B6871189
theorem B4074353 : Blo 1809606 4074353 := bstep (se 2 (by rfl) ⟨1527882, by rfl⟩ : syracuseStep 4074353 = 3055765) B3055765
theorem B2714483 : Blo 1809606 2714483 := bstep (se 1 (by rfl) ⟨2035862, by rfl⟩ : syracuseStep 2714483 = 4071725) B4071725
theorem B4074371 : Blo 1809606 4074371 := bstep (se 1 (by rfl) ⟨3055778, by rfl⟩ : syracuseStep 4074371 = 6111557) B6111557
theorem B2714513 : Blo 1809606 2714513 := bstep (se 2 (by rfl) ⟨1017942, by rfl⟩ : syracuseStep 2714513 = 2035885) B2035885
theorem B2714531 : Blo 1809606 2714531 := bstep (se 1 (by rfl) ⟨2035898, by rfl⟩ : syracuseStep 2714531 = 4071797) B4071797
theorem B2714561 : Blo 1809606 2714561 := bstep (se 2 (by rfl) ⟨1017960, by rfl⟩ : syracuseStep 2714561 = 2035921) B2035921
theorem B3435473 : Blo 1809606 3435473 := bstep (se 2 (by rfl) ⟨1288302, by rfl⟩ : syracuseStep 3435473 = 2576605) B2576605
theorem B2714579 : Blo 1809606 2714579 := bstep (se 1 (by rfl) ⟨2035934, by rfl⟩ : syracuseStep 2714579 = 4071869) B4071869
theorem B2714609 : Blo 1809606 2714609 := bstep (se 2 (by rfl) ⟨1017978, by rfl⟩ : syracuseStep 2714609 = 2035957) B2035957
theorem B2714627 : Blo 1809606 2714627 := bstep (se 1 (by rfl) ⟨2035970, by rfl⟩ : syracuseStep 2714627 = 4071941) B4071941
theorem B4582403 : Blo 1809606 4582403 := bstep (se 1 (by rfl) ⟨3436802, by rfl⟩ : syracuseStep 4582403 = 6873605) B6873605
theorem B2714657 : Blo 1809606 2714657 := bstep (se 2 (by rfl) ⟨1017996, by rfl⟩ : syracuseStep 2714657 = 2035993) B2035993
theorem B2714675 : Blo 1809606 2714675 := bstep (se 1 (by rfl) ⟨2036006, by rfl⟩ : syracuseStep 2714675 = 4072013) B4072013
theorem B2714705 : Blo 1809606 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B2714723 : Blo 1809606 2714723 := bstep (se 1 (by rfl) ⟨2036042, by rfl⟩ : syracuseStep 2714723 = 4072085) B4072085
theorem B37162097 : Blo 1809606 37162097 := bstep (se 2 (by rfl) ⟨13935786, by rfl⟩ : syracuseStep 37162097 = 27871573) B27871573
theorem B2714753 : Blo 1809606 2714753 := bstep (se 2 (by rfl) ⟨1018032, by rfl⟩ : syracuseStep 2714753 = 2036065) B2036065
theorem B2174083 : Blo 1809606 2174083 := bstep (se 1 (by rfl) ⟨1630562, by rfl⟩ : syracuseStep 2174083 = 3261125) B3261125
theorem B4074641 : Blo 1809606 4074641 := bstep (se 2 (by rfl) ⟨1527990, by rfl⟩ : syracuseStep 4074641 = 3055981) B3055981
theorem B2714771 : Blo 1809606 2714771 := bstep (se 1 (by rfl) ⟨2036078, by rfl⟩ : syracuseStep 2714771 = 4072157) B4072157
theorem B4074659 : Blo 1809606 4074659 := bstep (se 1 (by rfl) ⟨3055994, by rfl⟩ : syracuseStep 4074659 = 6111989) B6111989
theorem B6876323 : Blo 1809606 6876323 := bstep (se 1 (by rfl) ⟨5157242, by rfl⟩ : syracuseStep 6876323 = 10314485) B10314485
theorem B2714801 : Blo 1809606 2714801 := bstep (se 2 (by rfl) ⟨1018050, by rfl⟩ : syracuseStep 2714801 = 2036101) B2036101
theorem B2714819 : Blo 1809606 2714819 := bstep (se 1 (by rfl) ⟨2036114, by rfl⟩ : syracuseStep 2714819 = 4072229) B4072229
theorem B4582595 : Blo 1809606 4582595 := bstep (se 1 (by rfl) ⟨3436946, by rfl⟩ : syracuseStep 4582595 = 6873893) B6873893
theorem B2714849 : Blo 1809606 2714849 := bstep (se 2 (by rfl) ⟨1018068, by rfl⟩ : syracuseStep 2714849 = 2036137) B2036137
theorem B5156081 : Blo 1809606 5156081 := bstep (se 2 (by rfl) ⟨1933530, by rfl⟩ : syracuseStep 5156081 = 3867061) B3867061
theorem B2714867 : Blo 1809606 2714867 := bstep (se 1 (by rfl) ⟨2036150, by rfl⟩ : syracuseStep 2714867 = 4072301) B4072301
theorem B2714897 : Blo 1809606 2714897 := bstep (se 2 (by rfl) ⟨1018086, by rfl⟩ : syracuseStep 2714897 = 2036173) B2036173
theorem B2714915 : Blo 1809606 2714915 := bstep (se 1 (by rfl) ⟨2036186, by rfl⟩ : syracuseStep 2714915 = 4072373) B4072373
theorem B2714945 : Blo 1809606 2714945 := bstep (se 2 (by rfl) ⟨1018104, by rfl⟩ : syracuseStep 2714945 = 2036209) B2036209
theorem B13225285 : Blo 1809606 13225285 := bstep (se 4 (by rfl) ⟨1239870, by rfl⟩ : syracuseStep 13225285 = 2479741) B2479741
theorem B4894033 : Blo 1809606 4894033 := bstep (se 2 (by rfl) ⟨1835262, by rfl⟩ : syracuseStep 4894033 = 3670525) B3670525
theorem B2714963 : Blo 1809606 2714963 := bstep (se 1 (by rfl) ⟨2036222, by rfl⟩ : syracuseStep 2714963 = 4072445) B4072445
theorem B2714993 : Blo 1809606 2714993 := bstep (se 2 (by rfl) ⟨1018122, by rfl⟩ : syracuseStep 2714993 = 2036245) B2036245
theorem B2715011 : Blo 1809606 2715011 := bstep (se 1 (by rfl) ⟨2036258, by rfl⟩ : syracuseStep 2715011 = 4072517) B4072517
theorem B2715041 : Blo 1809606 2715041 := bstep (se 2 (by rfl) ⟨1018140, by rfl⟩ : syracuseStep 2715041 = 2036281) B2036281
theorem B4074929 : Blo 1809606 4074929 := bstep (se 2 (by rfl) ⟨1528098, by rfl⟩ : syracuseStep 4074929 = 3056197) B3056197
theorem B2715059 : Blo 1809606 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B4074947 : Blo 1809606 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B2715089 : Blo 1809606 2715089 := bstep (se 2 (by rfl) ⟨1018158, by rfl⟩ : syracuseStep 2715089 = 2036317) B2036317
theorem B2715107 : Blo 1809606 2715107 := bstep (se 1 (by rfl) ⟨2036330, by rfl⟩ : syracuseStep 2715107 = 4072661) B4072661
theorem B5803501 : Blo 1809606 5803501 := bstep (se 3 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 5803501 = 2176313) B2176313
theorem B2715137 : Blo 1809606 2715137 := bstep (se 2 (by rfl) ⟨1018176, by rfl⟩ : syracuseStep 2715137 = 2036353) B2036353
theorem B2715155 : Blo 1809606 2715155 := bstep (se 1 (by rfl) ⟨2036366, by rfl⟩ : syracuseStep 2715155 = 4072733) B4072733
theorem B2715185 : Blo 1809606 2715185 := bstep (se 2 (by rfl) ⟨1018194, by rfl⟩ : syracuseStep 2715185 = 2036389) B2036389
theorem B2715203 : Blo 1809606 2715203 := bstep (se 1 (by rfl) ⟨2036402, by rfl⟩ : syracuseStep 2715203 = 4072805) B4072805
theorem B2715233 : Blo 1809606 2715233 := bstep (se 2 (by rfl) ⟨1018212, by rfl⟩ : syracuseStep 2715233 = 2036425) B2036425
theorem B2715251 : Blo 1809606 2715251 := bstep (se 1 (by rfl) ⟨2036438, by rfl⟩ : syracuseStep 2715251 = 4072877) B4072877
theorem B3264131 : Blo 1809606 3264131 := bstep (se 1 (by rfl) ⟨2448098, by rfl⟩ : syracuseStep 3264131 = 4896197) B4896197
theorem B2715281 : Blo 1809606 2715281 := bstep (se 2 (by rfl) ⟨1018230, by rfl⟩ : syracuseStep 2715281 = 2036461) B2036461
theorem B3436195 : Blo 1809606 3436195 := bstep (se 1 (by rfl) ⟨2577146, by rfl⟩ : syracuseStep 3436195 = 5154293) B5154293
theorem B2715299 : Blo 1809606 2715299 := bstep (se 1 (by rfl) ⟨2036474, by rfl⟩ : syracuseStep 2715299 = 4072949) B4072949
theorem B2715329 : Blo 1809606 2715329 := bstep (se 2 (by rfl) ⟨1018248, by rfl⟩ : syracuseStep 2715329 = 2036497) B2036497
theorem B4075217 : Blo 1809606 4075217 := bstep (se 2 (by rfl) ⟨1528206, by rfl⟩ : syracuseStep 4075217 = 3056413) B3056413
theorem B2715347 : Blo 1809606 2715347 := bstep (se 1 (by rfl) ⟨2036510, by rfl⟩ : syracuseStep 2715347 = 4073021) B4073021
theorem B4075235 : Blo 1809606 4075235 := bstep (se 1 (by rfl) ⟨3056426, by rfl⟩ : syracuseStep 4075235 = 6112853) B6112853
theorem B7737059 : Blo 1809606 7737059 := bstep (se 1 (by rfl) ⟨5802794, by rfl⟩ : syracuseStep 7737059 = 11605589) B11605589
theorem B2715377 : Blo 1809606 2715377 := bstep (se 2 (by rfl) ⟨1018266, by rfl⟩ : syracuseStep 2715377 = 2036533) B2036533
theorem B2715395 : Blo 1809606 2715395 := bstep (se 1 (by rfl) ⟨2036546, by rfl⟩ : syracuseStep 2715395 = 4073093) B4073093
theorem B2715425 : Blo 1809606 2715425 := bstep (se 2 (by rfl) ⟨1018284, by rfl⟩ : syracuseStep 2715425 = 2036569) B2036569
theorem B2715443 : Blo 1809606 2715443 := bstep (se 1 (by rfl) ⟨2036582, by rfl⟩ : syracuseStep 2715443 = 4073165) B4073165
theorem B2715473 : Blo 1809606 2715473 := bstep (se 2 (by rfl) ⟨1018302, by rfl⟩ : syracuseStep 2715473 = 2036605) B2036605
theorem B2715491 : Blo 1809606 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B2715521 : Blo 1809606 2715521 := bstep (se 2 (by rfl) ⟨1018320, by rfl⟩ : syracuseStep 2715521 = 2036641) B2036641
theorem B2715539 : Blo 1809606 2715539 := bstep (se 1 (by rfl) ⟨2036654, by rfl⟩ : syracuseStep 2715539 = 4073309) B4073309
theorem B11915171 : Blo 1809606 11915171 := bstep (se 1 (by rfl) ⟨8936378, by rfl⟩ : syracuseStep 11915171 = 17872757) B17872757
theorem B2715569 : Blo 1809606 2715569 := bstep (se 2 (by rfl) ⟨1018338, by rfl⟩ : syracuseStep 2715569 = 2036677) B2036677
theorem B2715587 : Blo 1809606 2715587 := bstep (se 1 (by rfl) ⟨2036690, by rfl⟩ : syracuseStep 2715587 = 4073381) B4073381
theorem B2715617 : Blo 1809606 2715617 := bstep (se 2 (by rfl) ⟨1018356, by rfl⟩ : syracuseStep 2715617 = 2036713) B2036713
theorem B4075505 : Blo 1809606 4075505 := bstep (se 2 (by rfl) ⟨1528314, by rfl⟩ : syracuseStep 4075505 = 3056629) B3056629
theorem B2715635 : Blo 1809606 2715635 := bstep (se 1 (by rfl) ⟨2036726, by rfl⟩ : syracuseStep 2715635 = 4073453) B4073453
theorem B4075523 : Blo 1809606 4075523 := bstep (se 1 (by rfl) ⟨3056642, by rfl⟩ : syracuseStep 4075523 = 6113285) B6113285
theorem B2715665 : Blo 1809606 2715665 := bstep (se 2 (by rfl) ⟨1018374, by rfl⟩ : syracuseStep 2715665 = 2036749) B2036749
theorem B6279185 : Blo 1809606 6279185 := bstep (se 2 (by rfl) ⟨2354694, by rfl⟩ : syracuseStep 6279185 = 4709389) B4709389
theorem B2715683 : Blo 1809606 2715683 := bstep (se 1 (by rfl) ⟨2036762, by rfl⟩ : syracuseStep 2715683 = 4073525) B4073525
theorem B28643381 : Blo 1809606 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B2715713 : Blo 1809606 2715713 := bstep (se 2 (by rfl) ⟨1018392, by rfl⟩ : syracuseStep 2715713 = 2036785) B2036785
theorem B2715731 : Blo 1809606 2715731 := bstep (se 1 (by rfl) ⟨2036798, by rfl⟩ : syracuseStep 2715731 = 4073597) B4073597
theorem B2175059 : Blo 1809606 2175059 := bstep (se 1 (by rfl) ⟨1631294, by rfl⟩ : syracuseStep 2175059 = 3262589) B3262589
theorem B3436643 : Blo 1809606 3436643 := bstep (se 1 (by rfl) ⟨2577482, by rfl⟩ : syracuseStep 3436643 = 5154965) B5154965
theorem B2715761 : Blo 1809606 2715761 := bstep (se 2 (by rfl) ⟨1018410, by rfl⟩ : syracuseStep 2715761 = 2036821) B2036821
theorem B4583537 : Blo 1809606 4583537 := bstep (se 2 (by rfl) ⟨1718826, by rfl⟩ : syracuseStep 4583537 = 3437653) B3437653
theorem B2715779 : Blo 1809606 2715779 := bstep (se 1 (by rfl) ⟨2036834, by rfl⟩ : syracuseStep 2715779 = 4073669) B4073669
theorem B6877325 : Blo 1809606 6877325 := bstep (se 3 (by rfl) ⟨1289498, by rfl⟩ : syracuseStep 6877325 = 2578997) B2578997
theorem B2715809 : Blo 1809606 2715809 := bstep (se 2 (by rfl) ⟨1018428, by rfl⟩ : syracuseStep 2715809 = 2036857) B2036857
theorem B4583587 : Blo 1809606 4583587 := bstep (se 1 (by rfl) ⟨3437690, by rfl⟩ : syracuseStep 4583587 = 6875381) B6875381
theorem B11604131 : Blo 1809606 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B5157037 : Blo 1809606 5157037 := bstep (se 3 (by rfl) ⟨966944, by rfl⟩ : syracuseStep 5157037 = 1933889) B1933889
theorem B11595953 : Blo 1809606 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B2715827 : Blo 1809606 2715827 := bstep (se 1 (by rfl) ⟨2036870, by rfl⟩ : syracuseStep 2715827 = 4073741) B4073741
theorem B2715857 : Blo 1809606 2715857 := bstep (se 2 (by rfl) ⟨1018446, by rfl⟩ : syracuseStep 2715857 = 2036893) B2036893
theorem B2035939 : Blo 1809606 2035939 := bstep (se 1 (by rfl) ⟨1526954, by rfl⟩ : syracuseStep 2035939 = 3053909) B3053909
theorem B2715875 : Blo 1809606 2715875 := bstep (se 1 (by rfl) ⟨2036906, by rfl⟩ : syracuseStep 2715875 = 4073813) B4073813
theorem B2715905 : Blo 1809606 2715905 := bstep (se 2 (by rfl) ⟨1018464, by rfl⟩ : syracuseStep 2715905 = 2036929) B2036929
theorem B19575053 : Blo 1809606 19575053 := bstep (se 3 (by rfl) ⟨3670322, by rfl⟩ : syracuseStep 19575053 = 7340645) B7340645
theorem B4075793 : Blo 1809606 4075793 := bstep (se 2 (by rfl) ⟨1528422, by rfl⟩ : syracuseStep 4075793 = 3056845) B3056845
theorem B2715923 : Blo 1809606 2715923 := bstep (se 1 (by rfl) ⟨2036942, by rfl⟩ : syracuseStep 2715923 = 4073885) B4073885
theorem B67883285 : Blo 1809606 67883285 := bstep (se 6 (by rfl) ⟨1591014, by rfl⟩ : syracuseStep 67883285 = 3182029) B3182029
theorem B9163043 : Blo 1809606 9163043 := bstep (se 1 (by rfl) ⟨6872282, by rfl⟩ : syracuseStep 9163043 = 13744565) B13744565
theorem B4075811 : Blo 1809606 4075811 := bstep (se 1 (by rfl) ⟨3056858, by rfl⟩ : syracuseStep 4075811 = 6113717) B6113717
theorem B2715953 : Blo 1809606 2715953 := bstep (se 2 (by rfl) ⟨1018482, by rfl⟩ : syracuseStep 2715953 = 2036965) B2036965
theorem B4583729 : Blo 1809606 4583729 := bstep (se 2 (by rfl) ⟨1718898, by rfl⟩ : syracuseStep 4583729 = 3437797) B3437797
theorem B2715971 : Blo 1809606 2715971 := bstep (se 1 (by rfl) ⟨2036978, by rfl⟩ : syracuseStep 2715971 = 4073957) B4073957
theorem B2716001 : Blo 1809606 2716001 := bstep (se 2 (by rfl) ⟨1018500, by rfl⟩ : syracuseStep 2716001 = 2037001) B2037001
theorem B2036083 : Blo 1809606 2036083 := bstep (se 1 (by rfl) ⟨1527062, by rfl⟩ : syracuseStep 2036083 = 3054125) B3054125
theorem B2716019 : Blo 1809606 2716019 := bstep (se 1 (by rfl) ⟨2037014, by rfl⟩ : syracuseStep 2716019 = 4074029) B4074029
theorem B3436931 : Blo 1809606 3436931 := bstep (se 1 (by rfl) ⟨2577698, by rfl⟩ : syracuseStep 3436931 = 5155397) B5155397
theorem B2716049 : Blo 1809606 2716049 := bstep (se 2 (by rfl) ⟨1018518, by rfl⟩ : syracuseStep 2716049 = 2037037) B2037037
theorem B5157265 : Blo 1809606 5157265 := bstep (se 2 (by rfl) ⟨1933974, by rfl⟩ : syracuseStep 5157265 = 3867949) B3867949
theorem B2716067 : Blo 1809606 2716067 := bstep (se 1 (by rfl) ⟨2037050, by rfl⟩ : syracuseStep 2716067 = 4074101) B4074101
theorem B2716097 : Blo 1809606 2716097 := bstep (se 2 (by rfl) ⟨1018536, by rfl⟩ : syracuseStep 2716097 = 2037073) B2037073
theorem B2716115 : Blo 1809606 2716115 := bstep (se 1 (by rfl) ⟨2037086, by rfl⟩ : syracuseStep 2716115 = 4074173) B4074173
theorem B2716145 : Blo 1809606 2716145 := bstep (se 2 (by rfl) ⟨1018554, by rfl⟩ : syracuseStep 2716145 = 2037109) B2037109
theorem B2036227 : Blo 1809606 2036227 := bstep (se 1 (by rfl) ⟨1527170, by rfl⟩ : syracuseStep 2036227 = 3054341) B3054341
theorem B2716163 : Blo 1809606 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B2716193 : Blo 1809606 2716193 := bstep (se 2 (by rfl) ⟨1018572, by rfl⟩ : syracuseStep 2716193 = 2037145) B2037145
theorem B5157425 : Blo 1809606 5157425 := bstep (se 2 (by rfl) ⟨1934034, by rfl⟩ : syracuseStep 5157425 = 3868069) B3868069
theorem B4076081 : Blo 1809606 4076081 := bstep (se 2 (by rfl) ⟨1528530, by rfl⟩ : syracuseStep 4076081 = 3057061) B3057061
theorem B2576947 : Blo 1809606 2576947 := bstep (se 1 (by rfl) ⟨1932710, by rfl⟩ : syracuseStep 2576947 = 3865421) B3865421
theorem B2716211 : Blo 1809606 2716211 := bstep (se 1 (by rfl) ⟨2037158, by rfl⟩ : syracuseStep 2716211 = 4074317) B4074317
theorem B4076099 : Blo 1809606 4076099 := bstep (se 1 (by rfl) ⟨3057074, by rfl⟩ : syracuseStep 4076099 = 6114149) B6114149
theorem B2716241 : Blo 1809606 2716241 := bstep (se 2 (by rfl) ⟨1018590, by rfl⟩ : syracuseStep 2716241 = 2037181) B2037181
theorem B21181027 : Blo 1809606 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B13750883 : Blo 1809606 13750883 := bstep (se 1 (by rfl) ⟨10313162, by rfl⟩ : syracuseStep 13750883 = 20626325) B20626325
theorem B2716259 : Blo 1809606 2716259 := bstep (se 1 (by rfl) ⟨2037194, by rfl⟩ : syracuseStep 2716259 = 4074389) B4074389
theorem B2716289 : Blo 1809606 2716289 := bstep (se 2 (by rfl) ⟨1018608, by rfl⟩ : syracuseStep 2716289 = 2037217) B2037217
theorem B2036371 : Blo 1809606 2036371 := bstep (se 1 (by rfl) ⟨1527278, by rfl⟩ : syracuseStep 2036371 = 3054557) B3054557
theorem B2716307 : Blo 1809606 2716307 := bstep (se 1 (by rfl) ⟨2037230, by rfl⟩ : syracuseStep 2716307 = 4074461) B4074461
theorem B5157539 : Blo 1809606 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B2716337 : Blo 1809606 2716337 := bstep (se 2 (by rfl) ⟨1018626, by rfl⟩ : syracuseStep 2716337 = 2037253) B2037253
theorem B2716355 : Blo 1809606 2716355 := bstep (se 1 (by rfl) ⟨2037266, by rfl⟩ : syracuseStep 2716355 = 4074533) B4074533
theorem B2716385 : Blo 1809606 2716385 := bstep (se 2 (by rfl) ⟨1018644, by rfl⟩ : syracuseStep 2716385 = 2037289) B2037289
theorem B5026531 : Blo 1809606 5026531 := bstep (se 1 (by rfl) ⟨3769898, by rfl⟩ : syracuseStep 5026531 = 7539797) B7539797
theorem B6107885 : Blo 1809606 6107885 := bstep (se 3 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 6107885 = 2290457) B2290457
theorem B2716403 : Blo 1809606 2716403 := bstep (se 1 (by rfl) ⟨2037302, by rfl⟩ : syracuseStep 2716403 = 4074605) B4074605
theorem B2716433 : Blo 1809606 2716433 := bstep (se 2 (by rfl) ⟨1018662, by rfl⟩ : syracuseStep 2716433 = 2037325) B2037325
theorem B6107939 : Blo 1809606 6107939 := bstep (se 1 (by rfl) ⟨4580954, by rfl⟩ : syracuseStep 6107939 = 9161909) B9161909
theorem B2036515 : Blo 1809606 2036515 := bstep (se 1 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 2036515 = 3054773) B3054773
theorem B2716451 : Blo 1809606 2716451 := bstep (se 1 (by rfl) ⟨2037338, by rfl⟩ : syracuseStep 2716451 = 4074677) B4074677
theorem B2175779 : Blo 1809606 2175779 := bstep (se 1 (by rfl) ⟨1631834, by rfl⟩ : syracuseStep 2175779 = 3263669) B3263669
theorem B2716481 : Blo 1809606 2716481 := bstep (se 2 (by rfl) ⟨1018680, by rfl⟩ : syracuseStep 2716481 = 2037361) B2037361
theorem B2716499 : Blo 1809606 2716499 := bstep (se 1 (by rfl) ⟨2037374, by rfl⟩ : syracuseStep 2716499 = 4074749) B4074749
theorem B2716529 : Blo 1809606 2716529 := bstep (se 2 (by rfl) ⟨1018698, by rfl⟩ : syracuseStep 2716529 = 2037397) B2037397
theorem B2446195 : Blo 1809606 2446195 := bstep (se 1 (by rfl) ⟨1834646, by rfl⟩ : syracuseStep 2446195 = 3669293) B3669293
theorem B2716547 : Blo 1809606 2716547 := bstep (se 1 (by rfl) ⟨2037410, by rfl⟩ : syracuseStep 2716547 = 4074821) B4074821
theorem B2716577 : Blo 1809606 2716577 := bstep (se 2 (by rfl) ⟨1018716, by rfl⟩ : syracuseStep 2716577 = 2037433) B2037433
theorem B2036659 : Blo 1809606 2036659 := bstep (se 1 (by rfl) ⟨1527494, by rfl⟩ : syracuseStep 2036659 = 3054989) B3054989
theorem B2716595 : Blo 1809606 2716595 := bstep (se 1 (by rfl) ⟨2037446, by rfl⟩ : syracuseStep 2716595 = 4074893) B4074893
theorem B2716625 : Blo 1809606 2716625 := bstep (se 2 (by rfl) ⟨1018734, by rfl⟩ : syracuseStep 2716625 = 2037469) B2037469
theorem B2716643 : Blo 1809606 2716643 := bstep (se 1 (by rfl) ⟨2037482, by rfl⟩ : syracuseStep 2716643 = 4074965) B4074965
theorem B2290675 : Blo 1809606 2290675 := bstep (se 1 (by rfl) ⟨1718006, by rfl⟩ : syracuseStep 2290675 = 3436013) B3436013
theorem B2716673 : Blo 1809606 2716673 := bstep (se 2 (by rfl) ⟨1018752, by rfl⟩ : syracuseStep 2716673 = 2037505) B2037505
theorem B2577425 : Blo 1809606 2577425 := bstep (se 2 (by rfl) ⟨966534, by rfl⟩ : syracuseStep 2577425 = 1933069) B1933069
theorem B2716691 : Blo 1809606 2716691 := bstep (se 1 (by rfl) ⟨2037518, by rfl⟩ : syracuseStep 2716691 = 4075037) B4075037
theorem B7730225 : Blo 1809606 7730225 := bstep (se 2 (by rfl) ⟨2898834, by rfl⟩ : syracuseStep 7730225 = 5797669) B5797669
theorem B6108209 : Blo 1809606 6108209 := bstep (se 2 (by rfl) ⟨2290578, by rfl⟩ : syracuseStep 6108209 = 4581157) B4581157
theorem B2716721 : Blo 1809606 2716721 := bstep (se 2 (by rfl) ⟨1018770, by rfl⟩ : syracuseStep 2716721 = 2037541) B2037541
theorem B7345201 : Blo 1809606 7345201 := bstep (se 2 (by rfl) ⟨2754450, by rfl⟩ : syracuseStep 7345201 = 5508901) B5508901
theorem B2036803 : Blo 1809606 2036803 := bstep (se 1 (by rfl) ⟨1527602, by rfl⟩ : syracuseStep 2036803 = 3055205) B3055205
theorem B2716739 : Blo 1809606 2716739 := bstep (se 1 (by rfl) ⟨2037554, by rfl⟩ : syracuseStep 2716739 = 4075109) B4075109
theorem B11596877 : Blo 1809606 11596877 := bstep (se 3 (by rfl) ⟨2174414, by rfl⟩ : syracuseStep 11596877 = 4348829) B4348829
theorem B9163853 : Blo 1809606 9163853 := bstep (se 3 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 9163853 = 3436445) B3436445
theorem B2290771 : Blo 1809606 2290771 := bstep (se 1 (by rfl) ⟨1718078, by rfl⟩ : syracuseStep 2290771 = 3436157) B3436157
theorem B2716769 : Blo 1809606 2716769 := bstep (se 2 (by rfl) ⟨1018788, by rfl⟩ : syracuseStep 2716769 = 2037577) B2037577
theorem B2716787 : Blo 1809606 2716787 := bstep (se 1 (by rfl) ⟨2037590, by rfl⟩ : syracuseStep 2716787 = 4075181) B4075181
theorem B2577539 : Blo 1809606 2577539 := bstep (se 1 (by rfl) ⟨1933154, by rfl⟩ : syracuseStep 2577539 = 3866309) B3866309
theorem B2716817 : Blo 1809606 2716817 := bstep (se 2 (by rfl) ⟨1018806, by rfl⟩ : syracuseStep 2716817 = 2037613) B2037613
theorem B2716835 : Blo 1809606 2716835 := bstep (se 1 (by rfl) ⟨2037626, by rfl⟩ : syracuseStep 2716835 = 4075253) B4075253
theorem B2716865 : Blo 1809606 2716865 := bstep (se 2 (by rfl) ⟨1018824, by rfl⟩ : syracuseStep 2716865 = 2037649) B2037649
theorem B2577619 : Blo 1809606 2577619 := bstep (se 1 (by rfl) ⟨1933214, by rfl⟩ : syracuseStep 2577619 = 3866429) B3866429
theorem B2036947 : Blo 1809606 2036947 := bstep (se 1 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 2036947 = 3055421) B3055421
theorem B2716883 : Blo 1809606 2716883 := bstep (se 1 (by rfl) ⟨2037662, by rfl⟩ : syracuseStep 2716883 = 4075325) B4075325
theorem B58758371 : Blo 1809606 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B2716913 : Blo 1809606 2716913 := bstep (se 2 (by rfl) ⟨1018842, by rfl⟩ : syracuseStep 2716913 = 2037685) B2037685
theorem B2716931 : Blo 1809606 2716931 := bstep (se 1 (by rfl) ⟨2037698, by rfl⟩ : syracuseStep 2716931 = 4075397) B4075397
theorem B4584721 : Blo 1809606 4584721 := bstep (se 2 (by rfl) ⟨1719270, by rfl⟩ : syracuseStep 4584721 = 3438541) B3438541
theorem B2716961 : Blo 1809606 2716961 := bstep (se 2 (by rfl) ⟨1018860, by rfl⟩ : syracuseStep 2716961 = 2037721) B2037721
theorem B3437873 : Blo 1809606 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B2716979 : Blo 1809606 2716979 := bstep (se 1 (by rfl) ⟨2037734, by rfl⟩ : syracuseStep 2716979 = 4075469) B4075469
theorem B2717009 : Blo 1809606 2717009 := bstep (se 2 (by rfl) ⟨1018878, by rfl⟩ : syracuseStep 2717009 = 2037757) B2037757
theorem B2037091 : Blo 1809606 2037091 := bstep (se 1 (by rfl) ⟨1527818, by rfl⟩ : syracuseStep 2037091 = 3055637) B3055637
theorem B2717027 : Blo 1809606 2717027 := bstep (se 1 (by rfl) ⟨2037770, by rfl⟩ : syracuseStep 2717027 = 4075541) B4075541
theorem B2717057 : Blo 1809606 2717057 := bstep (se 2 (by rfl) ⟨1018896, by rfl⟩ : syracuseStep 2717057 = 2037793) B2037793
theorem B2717075 : Blo 1809606 2717075 := bstep (se 1 (by rfl) ⟨2037806, by rfl⟩ : syracuseStep 2717075 = 4075613) B4075613
theorem B2717105 : Blo 1809606 2717105 := bstep (se 2 (by rfl) ⟨1018914, by rfl⟩ : syracuseStep 2717105 = 2037829) B2037829
theorem B2717123 : Blo 1809606 2717123 := bstep (se 1 (by rfl) ⟨2037842, by rfl⟩ : syracuseStep 2717123 = 4075685) B4075685
theorem B5297617 : Blo 1809606 5297617 := bstep (se 2 (by rfl) ⟨1986606, by rfl⟩ : syracuseStep 5297617 = 3973213) B3973213
theorem B20624867 : Blo 1809606 20624867 := bstep (se 1 (by rfl) ⟨15468650, by rfl⟩ : syracuseStep 20624867 = 30937301) B30937301
theorem B2717153 : Blo 1809606 2717153 := bstep (se 2 (by rfl) ⟨1018932, by rfl⟩ : syracuseStep 2717153 = 2037865) B2037865
theorem B2037235 : Blo 1809606 2037235 := bstep (se 1 (by rfl) ⟨1527926, by rfl⟩ : syracuseStep 2037235 = 3055853) B3055853
theorem B2717171 : Blo 1809606 2717171 := bstep (se 1 (by rfl) ⟨2037878, by rfl⟩ : syracuseStep 2717171 = 4075757) B4075757
theorem B2717201 : Blo 1809606 2717201 := bstep (se 2 (by rfl) ⟨1018950, by rfl⟩ : syracuseStep 2717201 = 2037901) B2037901
theorem B4584995 : Blo 1809606 4584995 := bstep (se 1 (by rfl) ⟨3438746, by rfl⟩ : syracuseStep 4584995 = 6877493) B6877493
theorem B2717219 : Blo 1809606 2717219 := bstep (se 1 (by rfl) ⟨2037914, by rfl⟩ : syracuseStep 2717219 = 4075829) B4075829
theorem B2717249 : Blo 1809606 2717249 := bstep (se 2 (by rfl) ⟨1018968, by rfl⟩ : syracuseStep 2717249 = 2037937) B2037937
theorem B2291267 : Blo 1809606 2291267 := bstep (se 1 (by rfl) ⟨1718450, by rfl⟩ : syracuseStep 2291267 = 3436901) B3436901
theorem B5797453 : Blo 1809606 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B6108749 : Blo 1809606 6108749 := bstep (se 3 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 6108749 = 2290781) B2290781
theorem B2717267 : Blo 1809606 2717267 := bstep (se 1 (by rfl) ⟨2037950, by rfl⟩ : syracuseStep 2717267 = 4075901) B4075901
theorem B2717297 : Blo 1809606 2717297 := bstep (se 2 (by rfl) ⟨1018986, by rfl⟩ : syracuseStep 2717297 = 2037973) B2037973
theorem B2479745 : Blo 1809606 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B6108803 : Blo 1809606 6108803 := bstep (se 1 (by rfl) ⟨4581602, by rfl⟩ : syracuseStep 6108803 = 9163205) B9163205
theorem B2037379 : Blo 1809606 2037379 := bstep (se 1 (by rfl) ⟨1528034, by rfl⟩ : syracuseStep 2037379 = 3056069) B3056069
theorem B2717315 : Blo 1809606 2717315 := bstep (se 1 (by rfl) ⟨2037986, by rfl⟩ : syracuseStep 2717315 = 4075973) B4075973
theorem B5158541 : Blo 1809606 5158541 := bstep (se 3 (by rfl) ⟨967226, by rfl⟩ : syracuseStep 5158541 = 1934453) B1934453
theorem B2717345 : Blo 1809606 2717345 := bstep (se 2 (by rfl) ⟨1019004, by rfl⟩ : syracuseStep 2717345 = 2038009) B2038009
theorem B2717363 : Blo 1809606 2717363 := bstep (se 1 (by rfl) ⟨2038022, by rfl⟩ : syracuseStep 2717363 = 4076045) B4076045
theorem B2717393 : Blo 1809606 2717393 := bstep (se 2 (by rfl) ⟨1019022, by rfl⟩ : syracuseStep 2717393 = 2038045) B2038045
theorem B4585187 : Blo 1809606 4585187 := bstep (se 1 (by rfl) ⟨3438890, by rfl⟩ : syracuseStep 4585187 = 6877781) B6877781
theorem B2578177 : Blo 1809606 2578177 := bstep (se 2 (by rfl) ⟨966816, by rfl⟩ : syracuseStep 2578177 = 1933633) B1933633
theorem B2037523 : Blo 1809606 2037523 := bstep (se 1 (by rfl) ⟨1528142, by rfl⟩ : syracuseStep 2037523 = 3056285) B3056285
theorem B127112981 : Blo 1809606 127112981 := bstep (se 6 (by rfl) ⟨2979210, by rfl⟩ : syracuseStep 127112981 = 5958421) B5958421
theorem B5158723 : Blo 1809606 5158723 := bstep (se 1 (by rfl) ⟨3869042, by rfl⟩ : syracuseStep 5158723 = 7738085) B7738085
theorem B12392291 : Blo 1809606 12392291 := bstep (se 1 (by rfl) ⟨9294218, by rfl⟩ : syracuseStep 12392291 = 18588437) B18588437
theorem B6109073 : Blo 1809606 6109073 := bstep (se 2 (by rfl) ⟨2290902, by rfl⟩ : syracuseStep 6109073 = 4581805) B4581805
theorem B2037667 : Blo 1809606 2037667 := bstep (se 1 (by rfl) ⟨1528250, by rfl⟩ : syracuseStep 2037667 = 3056501) B3056501
theorem B17405923 : Blo 1809606 17405923 := bstep (se 1 (by rfl) ⟨13054442, by rfl⟩ : syracuseStep 17405923 = 26108885) B26108885
theorem B2037811 : Blo 1809606 2037811 := bstep (se 1 (by rfl) ⟨1528358, by rfl⟩ : syracuseStep 2037811 = 3056717) B3056717
theorem B3053713 : Blo 1809606 3053713 := bstep (se 2 (by rfl) ⟨1145142, by rfl⟩ : syracuseStep 3053713 = 2290285) B2290285
theorem B3438769 : Blo 1809606 3438769 := bstep (se 2 (by rfl) ⟨1289538, by rfl⟩ : syracuseStep 3438769 = 2579077) B2579077
theorem B3053747 : Blo 1809606 3053747 := bstep (se 1 (by rfl) ⟨2290310, by rfl⟩ : syracuseStep 3053747 = 4580621) B4580621
theorem B2037955 : Blo 1809606 2037955 := bstep (se 1 (by rfl) ⟨1528466, by rfl⟩ : syracuseStep 2037955 = 3056933) B3056933
theorem B2291971 : Blo 1809606 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B3053875 : Blo 1809606 3053875 := bstep (se 1 (by rfl) ⟨2290406, by rfl⟩ : syracuseStep 3053875 = 4580813) B4580813
theorem B4962637 : Blo 1809606 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B3438929 : Blo 1809606 3438929 := bstep (se 2 (by rfl) ⟨1289598, by rfl⟩ : syracuseStep 3438929 = 2579197) B2579197
theorem B2292067 : Blo 1809606 2292067 := bstep (se 1 (by rfl) ⟨1719050, by rfl⟩ : syracuseStep 2292067 = 3438101) B3438101
theorem B10312069 : Blo 1809606 10312069 := bstep (se 4 (by rfl) ⟨966756, by rfl⟩ : syracuseStep 10312069 = 1933513) B1933513
theorem B6109613 : Blo 1809606 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B11164081 : Blo 1809606 11164081 := bstep (se 2 (by rfl) ⟨4186530, by rfl⟩ : syracuseStep 11164081 = 8373061) B8373061
theorem B3054017 : Blo 1809606 3054017 := bstep (se 2 (by rfl) ⟨1145256, by rfl⟩ : syracuseStep 3054017 = 2290513) B2290513
theorem B2578883 : Blo 1809606 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B6109667 : Blo 1809606 6109667 := bstep (se 1 (by rfl) ⟨4582250, by rfl⟩ : syracuseStep 6109667 = 9164501) B9164501
theorem B3054145 : Blo 1809606 3054145 := bstep (se 2 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 3054145 = 2290609) B2290609
theorem B14678597 : Blo 1809606 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B3054179 : Blo 1809606 3054179 := bstep (se 1 (by rfl) ⟨2290634, by rfl⟩ : syracuseStep 3054179 = 4581269) B4581269
theorem B3054307 : Blo 1809606 3054307 := bstep (se 1 (by rfl) ⟨2290730, by rfl⟩ : syracuseStep 3054307 = 4581461) B4581461
theorem B6109937 : Blo 1809606 6109937 := bstep (se 2 (by rfl) ⟨2291226, by rfl⟩ : syracuseStep 6109937 = 4582453) B4582453
theorem B4348675 : Blo 1809606 4348675 := bstep (se 1 (by rfl) ⟨3261506, by rfl⟩ : syracuseStep 4348675 = 6523013) B6523013
theorem B2292563 : Blo 1809606 2292563 := bstep (se 1 (by rfl) ⟨1719422, by rfl⟩ : syracuseStep 2292563 = 3438845) B3438845
theorem B2448227 : Blo 1809606 2448227 := bstep (se 1 (by rfl) ⟨1836170, by rfl⟩ : syracuseStep 2448227 = 3672341) B3672341
theorem B3054449 : Blo 1809606 3054449 := bstep (se 2 (by rfl) ⟨1145418, by rfl⟩ : syracuseStep 3054449 = 2290837) B2290837
theorem B6871949 : Blo 1809606 6871949 := bstep (se 3 (by rfl) ⟨1288490, by rfl⟩ : syracuseStep 6871949 = 2576981) B2576981
theorem B5225357 : Blo 1809606 5225357 := bstep (se 3 (by rfl) ⟨979754, by rfl⟩ : syracuseStep 5225357 = 1959509) B1959509
theorem B3054577 : Blo 1809606 3054577 := bstep (se 2 (by rfl) ⟨1145466, by rfl⟩ : syracuseStep 3054577 = 2290933) B2290933
theorem B3054611 : Blo 1809606 3054611 := bstep (se 1 (by rfl) ⟨2290958, by rfl⟩ : syracuseStep 3054611 = 4581917) B4581917
theorem B4643939 : Blo 1809606 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B5799053 : Blo 1809606 5799053 := bstep (se 3 (by rfl) ⟨1087322, by rfl⟩ : syracuseStep 5799053 = 2174645) B2174645
theorem B3865745 : Blo 1809606 3865745 := bstep (se 2 (by rfl) ⟨1449654, by rfl⟩ : syracuseStep 3865745 = 2899309) B2899309
theorem B3054739 : Blo 1809606 3054739 := bstep (se 1 (by rfl) ⟨2291054, by rfl⟩ : syracuseStep 3054739 = 4582109) B4582109
theorem B2899091 : Blo 1809606 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B1809619 : Blo 1809606 1809619 := bstep (se 1 (by rfl) ⟨1357214, by rfl⟩ : syracuseStep 1809619 = 2714429) B2714429
theorem B1809635 : Blo 1809606 1809635 := bstep (se 1 (by rfl) ⟨1357226, by rfl⟩ : syracuseStep 1809635 = 2714453) B2714453
theorem B49544419 : Blo 1809606 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B1809651 : Blo 1809606 1809651 := bstep (se 1 (by rfl) ⟨1357238, by rfl⟩ : syracuseStep 1809651 = 2714477) B2714477
theorem B1809667 : Blo 1809606 1809667 := bstep (se 1 (by rfl) ⟨1357250, by rfl⟩ : syracuseStep 1809667 = 2714501) B2714501
theorem B6110477 : Blo 1809606 6110477 := bstep (se 3 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 6110477 = 2291429) B2291429
theorem B1809683 : Blo 1809606 1809683 := bstep (se 1 (by rfl) ⟨1357262, by rfl⟩ : syracuseStep 1809683 = 2714525) B2714525
theorem B3054881 : Blo 1809606 3054881 := bstep (se 2 (by rfl) ⟨1145580, by rfl⟩ : syracuseStep 3054881 = 2291161) B2291161
theorem B1809699 : Blo 1809606 1809699 := bstep (se 1 (by rfl) ⟨1357274, by rfl⟩ : syracuseStep 1809699 = 2714549) B2714549
theorem B1809715 : Blo 1809606 1809715 := bstep (se 1 (by rfl) ⟨1357286, by rfl⟩ : syracuseStep 1809715 = 2714573) B2714573
theorem B1809731 : Blo 1809606 1809731 := bstep (se 1 (by rfl) ⟨1357298, by rfl⟩ : syracuseStep 1809731 = 2714597) B2714597
theorem B6110531 : Blo 1809606 6110531 := bstep (se 1 (by rfl) ⟨4582898, by rfl⟩ : syracuseStep 6110531 = 9165797) B9165797
theorem B1809747 : Blo 1809606 1809747 := bstep (se 1 (by rfl) ⟨1357310, by rfl⟩ : syracuseStep 1809747 = 2714621) B2714621
theorem B1809763 : Blo 1809606 1809763 := bstep (se 1 (by rfl) ⟨1357322, by rfl⟩ : syracuseStep 1809763 = 2714645) B2714645
theorem B1809779 : Blo 1809606 1809779 := bstep (se 1 (by rfl) ⟨1357334, by rfl⟩ : syracuseStep 1809779 = 2714669) B2714669
theorem B1809795 : Blo 1809606 1809795 := bstep (se 1 (by rfl) ⟨1357346, by rfl⟩ : syracuseStep 1809795 = 2714693) B2714693
theorem B1809811 : Blo 1809606 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B3055009 : Blo 1809606 3055009 := bstep (se 2 (by rfl) ⟨1145628, by rfl⟩ : syracuseStep 3055009 = 2291257) B2291257
theorem B1809827 : Blo 1809606 1809827 := bstep (se 1 (by rfl) ⟨1357370, by rfl⟩ : syracuseStep 1809827 = 2714741) B2714741
theorem B1809843 : Blo 1809606 1809843 := bstep (se 1 (by rfl) ⟨1357382, by rfl⟩ : syracuseStep 1809843 = 2714765) B2714765
theorem B1809859 : Blo 1809606 1809859 := bstep (se 1 (by rfl) ⟨1357394, by rfl⟩ : syracuseStep 1809859 = 2714789) B2714789
theorem B3055043 : Blo 1809606 3055043 := bstep (se 1 (by rfl) ⟨2291282, by rfl⟩ : syracuseStep 3055043 = 4582565) B4582565
theorem B7732685 : Blo 1809606 7732685 := bstep (se 3 (by rfl) ⟨1449878, by rfl⟩ : syracuseStep 7732685 = 2899757) B2899757
theorem B1809875 : Blo 1809606 1809875 := bstep (se 1 (by rfl) ⟨1357406, by rfl⟩ : syracuseStep 1809875 = 2714813) B2714813
theorem B1809891 : Blo 1809606 1809891 := bstep (se 1 (by rfl) ⟨1357418, by rfl⟩ : syracuseStep 1809891 = 2714837) B2714837
theorem B1809907 : Blo 1809606 1809907 := bstep (se 1 (by rfl) ⟨1357430, by rfl⟩ : syracuseStep 1809907 = 2714861) B2714861
theorem B1809923 : Blo 1809606 1809923 := bstep (se 1 (by rfl) ⟨1357442, by rfl⟩ : syracuseStep 1809923 = 2714885) B2714885
theorem B1809939 : Blo 1809606 1809939 := bstep (se 1 (by rfl) ⟨1357454, by rfl⟩ : syracuseStep 1809939 = 2714909) B2714909
theorem B1809955 : Blo 1809606 1809955 := bstep (se 1 (by rfl) ⟨1357466, by rfl⟩ : syracuseStep 1809955 = 2714933) B2714933
theorem B1809971 : Blo 1809606 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B1809987 : Blo 1809606 1809987 := bstep (se 1 (by rfl) ⟨1357490, by rfl⟩ : syracuseStep 1809987 = 2714981) B2714981
theorem B3055171 : Blo 1809606 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B6110801 : Blo 1809606 6110801 := bstep (se 2 (by rfl) ⟨2291550, by rfl⟩ : syracuseStep 6110801 = 4583101) B4583101
theorem B1810003 : Blo 1809606 1810003 := bstep (se 1 (by rfl) ⟨1357502, by rfl⟩ : syracuseStep 1810003 = 2715005) B2715005
theorem B1810019 : Blo 1809606 1810019 := bstep (se 1 (by rfl) ⟨1357514, by rfl⟩ : syracuseStep 1810019 = 2715029) B2715029
theorem B5504611 : Blo 1809606 5504611 := bstep (se 1 (by rfl) ⟨4128458, by rfl⟩ : syracuseStep 5504611 = 8256917) B8256917
theorem B3669617 : Blo 1809606 3669617 := bstep (se 2 (by rfl) ⟨1376106, by rfl⟩ : syracuseStep 3669617 = 2752213) B2752213
theorem B1810035 : Blo 1809606 1810035 := bstep (se 1 (by rfl) ⟨1357526, by rfl⟩ : syracuseStep 1810035 = 2715053) B2715053
theorem B1810051 : Blo 1809606 1810051 := bstep (se 1 (by rfl) ⟨1357538, by rfl⟩ : syracuseStep 1810051 = 2715077) B2715077
theorem B1810067 : Blo 1809606 1810067 := bstep (se 1 (by rfl) ⟨1357550, by rfl⟩ : syracuseStep 1810067 = 2715101) B2715101
theorem B1810083 : Blo 1809606 1810083 := bstep (se 1 (by rfl) ⟨1357562, by rfl⟩ : syracuseStep 1810083 = 2715125) B2715125
theorem B1810099 : Blo 1809606 1810099 := bstep (se 1 (by rfl) ⟨1357574, by rfl⟩ : syracuseStep 1810099 = 2715149) B2715149
theorem B1810115 : Blo 1809606 1810115 := bstep (se 1 (by rfl) ⟨1357586, by rfl⟩ : syracuseStep 1810115 = 2715173) B2715173
theorem B3718865 : Blo 1809606 3718865 := bstep (se 2 (by rfl) ⟨1394574, by rfl⟩ : syracuseStep 3718865 = 2789149) B2789149
theorem B1810131 : Blo 1809606 1810131 := bstep (se 1 (by rfl) ⟨1357598, by rfl⟩ : syracuseStep 1810131 = 2715197) B2715197
theorem B3055313 : Blo 1809606 3055313 := bstep (se 2 (by rfl) ⟨1145742, by rfl⟩ : syracuseStep 3055313 = 2291485) B2291485
theorem B1810147 : Blo 1809606 1810147 := bstep (se 1 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 1810147 = 2715221) B2715221
theorem B1810163 : Blo 1809606 1810163 := bstep (se 1 (by rfl) ⟨1357622, by rfl⟩ : syracuseStep 1810163 = 2715245) B2715245
theorem B1810179 : Blo 1809606 1810179 := bstep (se 1 (by rfl) ⟨1357634, by rfl⟩ : syracuseStep 1810179 = 2715269) B2715269
theorem B4349713 : Blo 1809606 4349713 := bstep (se 2 (by rfl) ⟨1631142, by rfl⟩ : syracuseStep 4349713 = 3262285) B3262285
theorem B1810195 : Blo 1809606 1810195 := bstep (se 1 (by rfl) ⟨1357646, by rfl⟩ : syracuseStep 1810195 = 2715293) B2715293
theorem B1810211 : Blo 1809606 1810211 := bstep (se 1 (by rfl) ⟨1357658, by rfl⟩ : syracuseStep 1810211 = 2715317) B2715317
theorem B1810227 : Blo 1809606 1810227 := bstep (se 1 (by rfl) ⟨1357670, by rfl⟩ : syracuseStep 1810227 = 2715341) B2715341
theorem B1810243 : Blo 1809606 1810243 := bstep (se 1 (by rfl) ⟨1357682, by rfl⟩ : syracuseStep 1810243 = 2715365) B2715365
theorem B3055441 : Blo 1809606 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B1810259 : Blo 1809606 1810259 := bstep (se 1 (by rfl) ⟨1357694, by rfl⟩ : syracuseStep 1810259 = 2715389) B2715389
theorem B1810275 : Blo 1809606 1810275 := bstep (se 1 (by rfl) ⟨1357706, by rfl⟩ : syracuseStep 1810275 = 2715413) B2715413
theorem B1810291 : Blo 1809606 1810291 := bstep (se 1 (by rfl) ⟨1357718, by rfl⟩ : syracuseStep 1810291 = 2715437) B2715437
theorem B3055475 : Blo 1809606 3055475 := bstep (se 1 (by rfl) ⟨2291606, by rfl⟩ : syracuseStep 3055475 = 4583213) B4583213
theorem B1810307 : Blo 1809606 1810307 := bstep (se 1 (by rfl) ⟨1357730, by rfl⟩ : syracuseStep 1810307 = 2715461) B2715461
theorem B1810323 : Blo 1809606 1810323 := bstep (se 1 (by rfl) ⟨1357742, by rfl⟩ : syracuseStep 1810323 = 2715485) B2715485
theorem B1810339 : Blo 1809606 1810339 := bstep (se 1 (by rfl) ⟨1357754, by rfl⟩ : syracuseStep 1810339 = 2715509) B2715509
theorem B9166769 : Blo 1809606 9166769 := bstep (se 2 (by rfl) ⟨3437538, by rfl⟩ : syracuseStep 9166769 = 6875077) B6875077
theorem B1810355 : Blo 1809606 1810355 := bstep (se 1 (by rfl) ⟨1357766, by rfl⟩ : syracuseStep 1810355 = 2715533) B2715533
theorem B1810371 : Blo 1809606 1810371 := bstep (se 1 (by rfl) ⟨1357778, by rfl⟩ : syracuseStep 1810371 = 2715557) B2715557
theorem B1810387 : Blo 1809606 1810387 := bstep (se 1 (by rfl) ⟨1357790, by rfl⟩ : syracuseStep 1810387 = 2715581) B2715581
theorem B2899937 : Blo 1809606 2899937 := bstep (se 2 (by rfl) ⟨1087476, by rfl⟩ : syracuseStep 2899937 = 2174953) B2174953
theorem B1810403 : Blo 1809606 1810403 := bstep (se 1 (by rfl) ⟨1357802, by rfl⟩ : syracuseStep 1810403 = 2715605) B2715605
theorem B3866609 : Blo 1809606 3866609 := bstep (se 2 (by rfl) ⟨1449978, by rfl⟩ : syracuseStep 3866609 = 2899957) B2899957
theorem B1810419 : Blo 1809606 1810419 := bstep (se 1 (by rfl) ⟨1357814, by rfl⟩ : syracuseStep 1810419 = 2715629) B2715629
theorem B3055603 : Blo 1809606 3055603 := bstep (se 1 (by rfl) ⟨2291702, by rfl⟩ : syracuseStep 3055603 = 4583405) B4583405
theorem B1810443 : Blo 1809606 1810443 := bstep (se 1 (by rfl) ⟨1357832, by rfl⟩ : syracuseStep 1810443 = 2715665) B2715665
theorem B4186123 : Blo 1809606 4186123 := bstep (se 1 (by rfl) ⟨3139592, by rfl⟩ : syracuseStep 4186123 = 6279185) B6279185
theorem B1810455 : Blo 1809606 1810455 := bstep (se 1 (by rfl) ⟨1357841, by rfl⟩ : syracuseStep 1810455 = 2715683) B2715683
theorem B19095587 : Blo 1809606 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B1810475 : Blo 1809606 1810475 := bstep (se 1 (by rfl) ⟨1357856, by rfl⟩ : syracuseStep 1810475 = 2715713) B2715713
theorem B6873133 : Blo 1809606 6873133 := bstep (se 3 (by rfl) ⟨1288712, by rfl⟩ : syracuseStep 6873133 = 2577425) B2577425
theorem B1810487 : Blo 1809606 1810487 := bstep (se 1 (by rfl) ⟨1357865, by rfl⟩ : syracuseStep 1810487 = 2715731) B2715731
theorem B1810507 : Blo 1809606 1810507 := bstep (se 1 (by rfl) ⟨1357880, by rfl⟩ : syracuseStep 1810507 = 2715761) B2715761
theorem B3055691 : Blo 1809606 3055691 := bstep (se 1 (by rfl) ⟨2291768, by rfl⟩ : syracuseStep 3055691 = 4583537) B4583537
theorem B1810519 : Blo 1809606 1810519 := bstep (se 1 (by rfl) ⟨1357889, by rfl⟩ : syracuseStep 1810519 = 2715779) B2715779
theorem B1810539 : Blo 1809606 1810539 := bstep (se 1 (by rfl) ⟨1357904, by rfl⟩ : syracuseStep 1810539 = 2715809) B2715809
theorem B1810551 : Blo 1809606 1810551 := bstep (se 1 (by rfl) ⟨1357913, by rfl⟩ : syracuseStep 1810551 = 2715827) B2715827
theorem B3866753 : Blo 1809606 3866753 := bstep (se 2 (by rfl) ⟨1450032, by rfl⟩ : syracuseStep 3866753 = 2900065) B2900065
theorem B1810571 : Blo 1809606 1810571 := bstep (se 1 (by rfl) ⟨1357928, by rfl⟩ : syracuseStep 1810571 = 2715857) B2715857
theorem B1810583 : Blo 1809606 1810583 := bstep (se 1 (by rfl) ⟨1357937, by rfl⟩ : syracuseStep 1810583 = 2715875) B2715875
theorem B1810603 : Blo 1809606 1810603 := bstep (se 1 (by rfl) ⟨1357952, by rfl⟩ : syracuseStep 1810603 = 2715905) B2715905
theorem B5505203 : Blo 1809606 5505203 := bstep (se 1 (by rfl) ⟨4128902, by rfl⟩ : syracuseStep 5505203 = 8257805) B8257805
theorem B13050035 : Blo 1809606 13050035 := bstep (se 1 (by rfl) ⟨9787526, by rfl⟩ : syracuseStep 13050035 = 19575053) B19575053
theorem B1810615 : Blo 1809606 1810615 := bstep (se 1 (by rfl) ⟨1357961, by rfl⟩ : syracuseStep 1810615 = 2715923) B2715923
theorem B4071617 : Blo 1809606 4071617 := bstep (se 2 (by rfl) ⟨1526856, by rfl⟩ : syracuseStep 4071617 = 3053713) B3053713
theorem B1810635 : Blo 1809606 1810635 := bstep (se 1 (by rfl) ⟨1357976, by rfl⟩ : syracuseStep 1810635 = 2715953) B2715953
theorem B3055819 : Blo 1809606 3055819 := bstep (se 1 (by rfl) ⟨2291864, by rfl⟩ : syracuseStep 3055819 = 4583729) B4583729
theorem B1810647 : Blo 1809606 1810647 := bstep (se 1 (by rfl) ⟨1357985, by rfl⟩ : syracuseStep 1810647 = 2715971) B2715971
theorem B6111449 : Blo 1809606 6111449 := bstep (se 2 (by rfl) ⟨2291793, by rfl⟩ : syracuseStep 6111449 = 4583587) B4583587
theorem B5800157 : Blo 1809606 5800157 := bstep (se 3 (by rfl) ⟨1087529, by rfl⟩ : syracuseStep 5800157 = 2175059) B2175059
theorem B1810667 : Blo 1809606 1810667 := bstep (se 1 (by rfl) ⟨1358000, by rfl⟩ : syracuseStep 1810667 = 2716001) B2716001
theorem B1810679 : Blo 1809606 1810679 := bstep (se 1 (by rfl) ⟨1358009, by rfl⟩ : syracuseStep 1810679 = 2716019) B2716019
theorem B1810699 : Blo 1809606 1810699 := bstep (se 1 (by rfl) ⟨1358024, by rfl⟩ : syracuseStep 1810699 = 2716049) B2716049
theorem B1810711 : Blo 1809606 1810711 := bstep (se 1 (by rfl) ⟨1358033, by rfl⟩ : syracuseStep 1810711 = 2716067) B2716067
theorem B1810731 : Blo 1809606 1810731 := bstep (se 1 (by rfl) ⟨1358048, by rfl⟩ : syracuseStep 1810731 = 2716097) B2716097
theorem B1810743 : Blo 1809606 1810743 := bstep (se 1 (by rfl) ⟨1358057, by rfl⟩ : syracuseStep 1810743 = 2716115) B2716115
theorem B1810763 : Blo 1809606 1810763 := bstep (se 1 (by rfl) ⟨1358072, by rfl⟩ : syracuseStep 1810763 = 2716145) B2716145
theorem B1810775 : Blo 1809606 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B3055961 : Blo 1809606 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B6873437 : Blo 1809606 6873437 := bstep (se 3 (by rfl) ⟨1288769, by rfl⟩ : syracuseStep 6873437 = 2577539) B2577539
theorem B1810795 : Blo 1809606 1810795 := bstep (se 1 (by rfl) ⟨1358096, by rfl⟩ : syracuseStep 1810795 = 2716193) B2716193
theorem B1810807 : Blo 1809606 1810807 := bstep (se 1 (by rfl) ⟨1358105, by rfl⟩ : syracuseStep 1810807 = 2716211) B2716211
theorem B1810827 : Blo 1809606 1810827 := bstep (se 1 (by rfl) ⟨1358120, by rfl⟩ : syracuseStep 1810827 = 2716241) B2716241
theorem B9167255 : Blo 1809606 9167255 := bstep (se 1 (by rfl) ⟨6875441, by rfl⟩ : syracuseStep 9167255 = 13750883) B13750883
theorem B4071833 : Blo 1809606 4071833 := bstep (se 2 (by rfl) ⟨1526937, by rfl⟩ : syracuseStep 4071833 = 3053875) B3053875
theorem B1810839 : Blo 1809606 1810839 := bstep (se 1 (by rfl) ⟨1358129, by rfl⟩ : syracuseStep 1810839 = 2716259) B2716259
theorem B7733677 : Blo 1809606 7733677 := bstep (se 3 (by rfl) ⟨1450064, by rfl⟩ : syracuseStep 7733677 = 2900129) B2900129
theorem B1810859 : Blo 1809606 1810859 := bstep (se 1 (by rfl) ⟨1358144, by rfl⟩ : syracuseStep 1810859 = 2716289) B2716289
theorem B1810871 : Blo 1809606 1810871 := bstep (se 1 (by rfl) ⟨1358153, by rfl⟩ : syracuseStep 1810871 = 2716307) B2716307
theorem B1810891 : Blo 1809606 1810891 := bstep (se 1 (by rfl) ⟨1358168, by rfl⟩ : syracuseStep 1810891 = 2716337) B2716337
theorem B3867095 : Blo 1809606 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B1810903 : Blo 1809606 1810903 := bstep (se 1 (by rfl) ⟨1358177, by rfl⟩ : syracuseStep 1810903 = 2716355) B2716355
theorem B3056089 : Blo 1809606 3056089 := bstep (se 2 (by rfl) ⟨1146033, by rfl⟩ : syracuseStep 3056089 = 2292067) B2292067
theorem B1810923 : Blo 1809606 1810923 := bstep (se 1 (by rfl) ⟨1358192, by rfl⟩ : syracuseStep 1810923 = 2716385) B2716385
theorem B4071923 : Blo 1809606 4071923 := bstep (se 1 (by rfl) ⟨3053942, by rfl⟩ : syracuseStep 4071923 = 6107885) B6107885
theorem B1810935 : Blo 1809606 1810935 := bstep (se 1 (by rfl) ⟨1358201, by rfl⟩ : syracuseStep 1810935 = 2716403) B2716403
theorem B1810955 : Blo 1809606 1810955 := bstep (se 1 (by rfl) ⟨1358216, by rfl⟩ : syracuseStep 1810955 = 2716433) B2716433
theorem B4071959 : Blo 1809606 4071959 := bstep (se 1 (by rfl) ⟨3053969, by rfl⟩ : syracuseStep 4071959 = 6107939) B6107939
theorem B1810967 : Blo 1809606 1810967 := bstep (se 1 (by rfl) ⟨1358225, by rfl⟩ : syracuseStep 1810967 = 2716451) B2716451
theorem B1810987 : Blo 1809606 1810987 := bstep (se 1 (by rfl) ⟨1358240, by rfl⟩ : syracuseStep 1810987 = 2716481) B2716481
theorem B1810999 : Blo 1809606 1810999 := bstep (se 1 (by rfl) ⟨1358249, by rfl⟩ : syracuseStep 1810999 = 2716499) B2716499
theorem B14885441 : Blo 1809606 14885441 := bstep (se 2 (by rfl) ⟨5582040, by rfl⟩ : syracuseStep 14885441 = 11164081) B11164081
theorem B6193739 : Blo 1809606 6193739 := bstep (se 1 (by rfl) ⟨4645304, by rfl⟩ : syracuseStep 6193739 = 9290609) B9290609
theorem B1811019 : Blo 1809606 1811019 := bstep (se 1 (by rfl) ⟨1358264, by rfl⟩ : syracuseStep 1811019 = 2716529) B2716529
theorem B1811031 : Blo 1809606 1811031 := bstep (se 1 (by rfl) ⟨1358273, by rfl⟩ : syracuseStep 1811031 = 2716547) B2716547
theorem B1811051 : Blo 1809606 1811051 := bstep (se 1 (by rfl) ⟨1358288, by rfl⟩ : syracuseStep 1811051 = 2716577) B2716577
theorem B1811063 : Blo 1809606 1811063 := bstep (se 1 (by rfl) ⟨1358297, by rfl⟩ : syracuseStep 1811063 = 2716595) B2716595
theorem B1811083 : Blo 1809606 1811083 := bstep (se 1 (by rfl) ⟨1358312, by rfl⟩ : syracuseStep 1811083 = 2716625) B2716625
theorem B1811095 : Blo 1809606 1811095 := bstep (se 1 (by rfl) ⟨1358321, by rfl⟩ : syracuseStep 1811095 = 2716643) B2716643
theorem B1811115 : Blo 1809606 1811115 := bstep (se 1 (by rfl) ⟨1358336, by rfl⟩ : syracuseStep 1811115 = 2716673) B2716673
theorem B1811127 : Blo 1809606 1811127 := bstep (se 1 (by rfl) ⟨1358345, by rfl⟩ : syracuseStep 1811127 = 2716691) B2716691
theorem B5153483 : Blo 1809606 5153483 := bstep (se 1 (by rfl) ⟨3865112, by rfl⟩ : syracuseStep 5153483 = 7730225) B7730225
theorem B4072139 : Blo 1809606 4072139 := bstep (se 1 (by rfl) ⟨3054104, by rfl⟩ : syracuseStep 4072139 = 6108209) B6108209
theorem B1811147 : Blo 1809606 1811147 := bstep (se 1 (by rfl) ⟨1358360, by rfl⟩ : syracuseStep 1811147 = 2716721) B2716721
theorem B1811159 : Blo 1809606 1811159 := bstep (se 1 (by rfl) ⟨1358369, by rfl⟩ : syracuseStep 1811159 = 2716739) B2716739
theorem B1811179 : Blo 1809606 1811179 := bstep (se 1 (by rfl) ⟨1358384, by rfl⟩ : syracuseStep 1811179 = 2716769) B2716769
theorem B1811191 : Blo 1809606 1811191 := bstep (se 1 (by rfl) ⟨1358393, by rfl⟩ : syracuseStep 1811191 = 2716787) B2716787
theorem B4072193 : Blo 1809606 4072193 := bstep (se 2 (by rfl) ⟨1527072, by rfl⟩ : syracuseStep 4072193 = 3054145) B3054145
theorem B1811211 : Blo 1809606 1811211 := bstep (se 1 (by rfl) ⟨1358408, by rfl⟩ : syracuseStep 1811211 = 2716817) B2716817
theorem B1811223 : Blo 1809606 1811223 := bstep (se 1 (by rfl) ⟨1358417, by rfl⟩ : syracuseStep 1811223 = 2716835) B2716835
theorem B1811243 : Blo 1809606 1811243 := bstep (se 1 (by rfl) ⟨1358432, by rfl⟩ : syracuseStep 1811243 = 2716865) B2716865
theorem B1811255 : Blo 1809606 1811255 := bstep (se 1 (by rfl) ⟨1358441, by rfl⟩ : syracuseStep 1811255 = 2716883) B2716883
theorem B1811275 : Blo 1809606 1811275 := bstep (se 1 (by rfl) ⟨1358456, by rfl⟩ : syracuseStep 1811275 = 2716913) B2716913
theorem B1811287 : Blo 1809606 1811287 := bstep (se 1 (by rfl) ⟨1358465, by rfl⟩ : syracuseStep 1811287 = 2716931) B2716931
theorem B4129625 : Blo 1809606 4129625 := bstep (se 2 (by rfl) ⟨1548609, by rfl⟩ : syracuseStep 4129625 = 3097219) B3097219
theorem B4350809 : Blo 1809606 4350809 := bstep (se 2 (by rfl) ⟨1631553, by rfl⟩ : syracuseStep 4350809 = 3263107) B3263107
theorem B1811307 : Blo 1809606 1811307 := bstep (se 1 (by rfl) ⟨1358480, by rfl⟩ : syracuseStep 1811307 = 2716961) B2716961
theorem B1811319 : Blo 1809606 1811319 := bstep (se 1 (by rfl) ⟨1358489, by rfl⟩ : syracuseStep 1811319 = 2716979) B2716979
theorem B1811339 : Blo 1809606 1811339 := bstep (se 1 (by rfl) ⟨1358504, by rfl⟩ : syracuseStep 1811339 = 2717009) B2717009
theorem B6112151 : Blo 1809606 6112151 := bstep (se 1 (by rfl) ⟨4584113, by rfl⟩ : syracuseStep 6112151 = 9168227) B9168227
theorem B1811351 : Blo 1809606 1811351 := bstep (se 1 (by rfl) ⟨1358513, by rfl⟩ : syracuseStep 1811351 = 2717027) B2717027
theorem B1811371 : Blo 1809606 1811371 := bstep (se 1 (by rfl) ⟨1358528, by rfl⟩ : syracuseStep 1811371 = 2717057) B2717057
theorem B1811383 : Blo 1809606 1811383 := bstep (se 1 (by rfl) ⟨1358537, by rfl⟩ : syracuseStep 1811383 = 2717075) B2717075
theorem B1811403 : Blo 1809606 1811403 := bstep (se 1 (by rfl) ⟨1358552, by rfl⟩ : syracuseStep 1811403 = 2717105) B2717105
theorem B6702041 : Blo 1809606 6702041 := bstep (se 2 (by rfl) ⟨2513265, by rfl⟩ : syracuseStep 6702041 = 5026531) B5026531
theorem B4072409 : Blo 1809606 4072409 := bstep (se 2 (by rfl) ⟨1527153, by rfl⟩ : syracuseStep 4072409 = 3054307) B3054307
theorem B1811415 : Blo 1809606 1811415 := bstep (se 1 (by rfl) ⟨1358561, by rfl⟩ : syracuseStep 1811415 = 2717123) B2717123
theorem B1811435 : Blo 1809606 1811435 := bstep (se 1 (by rfl) ⟨1358576, by rfl⟩ : syracuseStep 1811435 = 2717153) B2717153
theorem B1811447 : Blo 1809606 1811447 := bstep (se 1 (by rfl) ⟨1358585, by rfl⟩ : syracuseStep 1811447 = 2717171) B2717171
theorem B3867659 : Blo 1809606 3867659 := bstep (se 1 (by rfl) ⟨2900744, by rfl⟩ : syracuseStep 3867659 = 5801489) B5801489
theorem B1811467 : Blo 1809606 1811467 := bstep (se 1 (by rfl) ⟨1358600, by rfl⟩ : syracuseStep 1811467 = 2717201) B2717201
theorem B3056663 : Blo 1809606 3056663 := bstep (se 1 (by rfl) ⟨2292497, by rfl⟩ : syracuseStep 3056663 = 4584995) B4584995
theorem B1811479 : Blo 1809606 1811479 := bstep (se 1 (by rfl) ⟨1358609, by rfl⟩ : syracuseStep 1811479 = 2717219) B2717219
theorem B1811499 : Blo 1809606 1811499 := bstep (se 1 (by rfl) ⟨1358624, by rfl⟩ : syracuseStep 1811499 = 2717249) B2717249
theorem B4072499 : Blo 1809606 4072499 := bstep (se 1 (by rfl) ⟨3054374, by rfl⟩ : syracuseStep 4072499 = 6108749) B6108749
theorem B1811511 : Blo 1809606 1811511 := bstep (se 1 (by rfl) ⟨1358633, by rfl⟩ : syracuseStep 1811511 = 2717267) B2717267
theorem B2065483 : Blo 1809606 2065483 := bstep (se 1 (by rfl) ⟨1549112, by rfl⟩ : syracuseStep 2065483 = 3098225) B3098225
theorem B1811531 : Blo 1809606 1811531 := bstep (se 1 (by rfl) ⟨1358648, by rfl⟩ : syracuseStep 1811531 = 2717297) B2717297
theorem B4072535 : Blo 1809606 4072535 := bstep (se 1 (by rfl) ⟨3054401, by rfl⟩ : syracuseStep 4072535 = 6108803) B6108803
theorem B1811543 : Blo 1809606 1811543 := bstep (se 1 (by rfl) ⟨1358657, by rfl⟩ : syracuseStep 1811543 = 2717315) B2717315
theorem B1811563 : Blo 1809606 1811563 := bstep (se 1 (by rfl) ⟨1358672, by rfl⟩ : syracuseStep 1811563 = 2717345) B2717345
theorem B1811575 : Blo 1809606 1811575 := bstep (se 1 (by rfl) ⟨1358681, by rfl⟩ : syracuseStep 1811575 = 2717363) B2717363
theorem B1811595 : Blo 1809606 1811595 := bstep (se 1 (by rfl) ⟨1358696, by rfl⟩ : syracuseStep 1811595 = 2717393) B2717393
theorem B29377687 : Blo 1809606 29377687 := bstep (se 1 (by rfl) ⟨22033265, by rfl⟩ : syracuseStep 29377687 = 44066531) B44066531
theorem B3056791 : Blo 1809606 3056791 := bstep (se 1 (by rfl) ⟨2292593, by rfl⟩ : syracuseStep 3056791 = 4585187) B4585187
theorem B3261593 : Blo 1809606 3261593 := bstep (se 2 (by rfl) ⟨1223097, by rfl⟩ : syracuseStep 3261593 = 2446195) B2446195
theorem B1836203 : Blo 1809606 1836203 := bstep (se 1 (by rfl) ⟨1377152, by rfl⟩ : syracuseStep 1836203 = 2754305) B2754305
theorem B20620493 : Blo 1809606 20620493 := bstep (se 3 (by rfl) ⟨3866342, by rfl⟩ : syracuseStep 20620493 = 7732685) B7732685
theorem B4072715 : Blo 1809606 4072715 := bstep (se 1 (by rfl) ⟨3054536, by rfl⟩ : syracuseStep 4072715 = 6109073) B6109073
theorem B2065675 : Blo 1809606 2065675 := bstep (se 1 (by rfl) ⟨1549256, by rfl⟩ : syracuseStep 2065675 = 3098513) B3098513
theorem B4072769 : Blo 1809606 4072769 := bstep (se 2 (by rfl) ⟨1527288, by rfl⟩ : syracuseStep 4072769 = 3054577) B3054577
theorem B2753867 : Blo 1809606 2753867 := bstep (se 1 (by rfl) ⟨2065400, by rfl⟩ : syracuseStep 2753867 = 4130801) B4130801
theorem B5506397 : Blo 1809606 5506397 := bstep (se 3 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 5506397 = 2064899) B2064899
theorem B6112691 : Blo 1809606 6112691 := bstep (se 1 (by rfl) ⟨4584518, by rfl⟩ : syracuseStep 6112691 = 9169037) B9169037
theorem B39142925 : Blo 1809606 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B4130327 : Blo 1809606 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B4072985 : Blo 1809606 4072985 := bstep (se 2 (by rfl) ⟨1527369, by rfl⟩ : syracuseStep 4072985 = 3054739) B3054739
theorem B3868249 : Blo 1809606 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B4073075 : Blo 1809606 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B4073111 : Blo 1809606 4073111 := bstep (se 1 (by rfl) ⟨3054833, by rfl⟩ : syracuseStep 4073111 = 6109667) B6109667
theorem B6612653 : Blo 1809606 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B6112961 : Blo 1809606 6112961 := bstep (se 2 (by rfl) ⟨2292360, by rfl⟩ : syracuseStep 6112961 = 4584721) B4584721
theorem B2901719 : Blo 1809606 2901719 := bstep (se 1 (by rfl) ⟨2176289, by rfl⟩ : syracuseStep 2901719 = 4352579) B4352579
theorem B4073291 : Blo 1809606 4073291 := bstep (se 1 (by rfl) ⟨3054968, by rfl⟩ : syracuseStep 4073291 = 6109937) B6109937
theorem B6522713 : Blo 1809606 6522713 := bstep (se 2 (by rfl) ⟨2446017, by rfl⟩ : syracuseStep 6522713 = 4892035) B4892035
theorem B4073345 : Blo 1809606 4073345 := bstep (se 2 (by rfl) ⟨1527504, by rfl⟩ : syracuseStep 4073345 = 3055009) B3055009
theorem B4581299 : Blo 1809606 4581299 := bstep (se 1 (by rfl) ⟨3435974, by rfl⟩ : syracuseStep 4581299 = 6871949) B6871949
theorem B3483571 : Blo 1809606 3483571 := bstep (se 1 (by rfl) ⟨2612678, by rfl⟩ : syracuseStep 3483571 = 5225357) B5225357
theorem B7063489 : Blo 1809606 7063489 := bstep (se 2 (by rfl) ⟨2648808, by rfl⟩ : syracuseStep 7063489 = 5297617) B5297617
theorem B24774731 : Blo 1809606 24774731 := bstep (se 1 (by rfl) ⟨18581048, by rfl⟩ : syracuseStep 24774731 = 37162097) B37162097
theorem B4073561 : Blo 1809606 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B5802077 : Blo 1809606 5802077 := bstep (se 3 (by rfl) ⟨1087889, by rfl⟩ : syracuseStep 5802077 = 2175779) B2175779
theorem B4073651 : Blo 1809606 4073651 := bstep (se 1 (by rfl) ⟨3055238, by rfl⟩ : syracuseStep 4073651 = 6110477) B6110477
theorem B4073687 : Blo 1809606 4073687 := bstep (se 1 (by rfl) ⟨3055265, by rfl⟩ : syracuseStep 4073687 = 6110531) B6110531
theorem B4581593 : Blo 1809606 4581593 := bstep (se 2 (by rfl) ⟨1718097, by rfl⟩ : syracuseStep 4581593 = 3436195) B3436195
theorem B6113501 : Blo 1809606 6113501 := bstep (se 3 (by rfl) ⟨1146281, by rfl⟩ : syracuseStep 6113501 = 2292563) B2292563
theorem B15468893 : Blo 1809606 15468893 := bstep (se 3 (by rfl) ⟨2900417, by rfl⟩ : syracuseStep 15468893 = 5800835) B5800835
theorem B4073867 : Blo 1809606 4073867 := bstep (se 1 (by rfl) ⟨3055400, by rfl⟩ : syracuseStep 4073867 = 6110801) B6110801
theorem B4073921 : Blo 1809606 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B9161261 : Blo 1809606 9161261 := bstep (se 3 (by rfl) ⟨1717736, by rfl⟩ : syracuseStep 9161261 = 3435473) B3435473
theorem B49572445 : Blo 1809606 49572445 := bstep (se 3 (by rfl) ⟨9294833, by rfl⟩ : syracuseStep 49572445 = 18589667) B18589667
theorem B4074137 : Blo 1809606 4074137 := bstep (se 2 (by rfl) ⟨1527801, by rfl⟩ : syracuseStep 4074137 = 3055603) B3055603
theorem B8260289 : Blo 1809606 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B4074227 : Blo 1809606 4074227 := bstep (se 1 (by rfl) ⟨3055670, by rfl⟩ : syracuseStep 4074227 = 6111341) B6111341
theorem B4074263 : Blo 1809606 4074263 := bstep (se 1 (by rfl) ⟨3055697, by rfl⟩ : syracuseStep 4074263 = 6111395) B6111395
theorem B7736087 : Blo 1809606 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B5507929 : Blo 1809606 5507929 := bstep (se 2 (by rfl) ⟨2065473, by rfl⟩ : syracuseStep 5507929 = 4130947) B4130947
theorem B45255523 : Blo 1809606 45255523 := bstep (se 1 (by rfl) ⟨33941642, by rfl⟩ : syracuseStep 45255523 = 67883285) B67883285
theorem B6876035 : Blo 1809606 6876035 := bstep (se 1 (by rfl) ⟨5157026, by rfl⟩ : syracuseStep 6876035 = 10314053) B10314053
theorem B2714507 : Blo 1809606 2714507 := bstep (se 1 (by rfl) ⟨2035880, by rfl⟩ : syracuseStep 2714507 = 4071761) B4071761
theorem B6876049 : Blo 1809606 6876049 := bstep (se 2 (by rfl) ⟨2578518, by rfl⟩ : syracuseStep 6876049 = 5157037) B5157037
theorem B2714519 : Blo 1809606 2714519 := bstep (se 1 (by rfl) ⟨2035889, by rfl⟩ : syracuseStep 2714519 = 4071779) B4071779
theorem B3435443 : Blo 1809606 3435443 := bstep (se 1 (by rfl) ⟨2576582, by rfl⟩ : syracuseStep 3435443 = 5153165) B5153165
theorem B4074443 : Blo 1809606 4074443 := bstep (se 1 (by rfl) ⟨3055832, by rfl⟩ : syracuseStep 4074443 = 6111665) B6111665
theorem B2714585 : Blo 1809606 2714585 := bstep (se 2 (by rfl) ⟨1017969, by rfl⟩ : syracuseStep 2714585 = 2035939) B2035939
theorem B4074497 : Blo 1809606 4074497 := bstep (se 2 (by rfl) ⟨1527936, by rfl⟩ : syracuseStep 4074497 = 3055873) B3055873
theorem B10308653 : Blo 1809606 10308653 := bstep (se 3 (by rfl) ⟨1932872, by rfl⟩ : syracuseStep 10308653 = 3865745) B3865745
theorem B2714699 : Blo 1809606 2714699 := bstep (se 1 (by rfl) ⟨2036024, by rfl⟩ : syracuseStep 2714699 = 4072049) B4072049
theorem B2714711 : Blo 1809606 2714711 := bstep (se 1 (by rfl) ⟨2036033, by rfl⟩ : syracuseStep 2714711 = 4072067) B4072067
theorem B5155933 : Blo 1809606 5155933 := bstep (se 3 (by rfl) ⟨966737, by rfl⟩ : syracuseStep 5155933 = 1933475) B1933475
theorem B13053059 : Blo 1809606 13053059 := bstep (se 1 (by rfl) ⟨9789794, by rfl⟩ : syracuseStep 13053059 = 19579589) B19579589
theorem B3435671 : Blo 1809606 3435671 := bstep (se 1 (by rfl) ⟨2576753, by rfl⟩ : syracuseStep 3435671 = 5153507) B5153507
theorem B23194775 : Blo 1809606 23194775 := bstep (se 1 (by rfl) ⟨17396081, by rfl⟩ : syracuseStep 23194775 = 34792163) B34792163
theorem B2714777 : Blo 1809606 2714777 := bstep (se 2 (by rfl) ⟨1018041, by rfl⟩ : syracuseStep 2714777 = 2036083) B2036083
theorem B13749425 : Blo 1809606 13749425 := bstep (se 2 (by rfl) ⟨5156034, by rfl⟩ : syracuseStep 13749425 = 10312069) B10312069
theorem B6876353 : Blo 1809606 6876353 := bstep (se 2 (by rfl) ⟨2578632, by rfl⟩ : syracuseStep 6876353 = 5157265) B5157265
theorem B4074713 : Blo 1809606 4074713 := bstep (se 2 (by rfl) ⟨1528017, by rfl⟩ : syracuseStep 4074713 = 3056035) B3056035
theorem B2714891 : Blo 1809606 2714891 := bstep (se 1 (by rfl) ⟨2036168, by rfl⟩ : syracuseStep 2714891 = 4072337) B4072337
theorem B2714903 : Blo 1809606 2714903 := bstep (se 1 (by rfl) ⟨2036177, by rfl⟩ : syracuseStep 2714903 = 4072355) B4072355
theorem B4074803 : Blo 1809606 4074803 := bstep (se 1 (by rfl) ⟨3056102, by rfl⟩ : syracuseStep 4074803 = 6112205) B6112205
theorem B6524225 : Blo 1809606 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B4074839 : Blo 1809606 4074839 := bstep (se 1 (by rfl) ⟨3056129, by rfl⟩ : syracuseStep 4074839 = 6112259) B6112259
theorem B2714969 : Blo 1809606 2714969 := bstep (se 2 (by rfl) ⟨1018113, by rfl⟩ : syracuseStep 2714969 = 2036227) B2036227
theorem B11595109 : Blo 1809606 11595109 := bstep (se 4 (by rfl) ⟨1087041, by rfl⟩ : syracuseStep 11595109 = 2174083) B2174083
theorem B3435929 : Blo 1809606 3435929 := bstep (se 2 (by rfl) ⟨1288473, by rfl⟩ : syracuseStep 3435929 = 2576947) B2576947
theorem B2715083 : Blo 1809606 2715083 := bstep (se 1 (by rfl) ⟨2036312, by rfl⟩ : syracuseStep 2715083 = 4072625) B4072625
theorem B2715095 : Blo 1809606 2715095 := bstep (se 1 (by rfl) ⟨2036321, by rfl⟩ : syracuseStep 2715095 = 4072643) B4072643
theorem B28241369 : Blo 1809606 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B4075019 : Blo 1809606 4075019 := bstep (se 1 (by rfl) ⟨3056264, by rfl⟩ : syracuseStep 4075019 = 6112529) B6112529
theorem B2715161 : Blo 1809606 2715161 := bstep (se 2 (by rfl) ⟨1018185, by rfl⟩ : syracuseStep 2715161 = 2036371) B2036371
theorem B11759149 : Blo 1809606 11759149 := bstep (se 3 (by rfl) ⟨2204840, by rfl⟩ : syracuseStep 11759149 = 4409681) B4409681
theorem B4075073 : Blo 1809606 4075073 := bstep (se 2 (by rfl) ⟨1528152, by rfl⟩ : syracuseStep 4075073 = 3056305) B3056305
theorem B2715275 : Blo 1809606 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B2715287 : Blo 1809606 2715287 := bstep (se 1 (by rfl) ⟨2036465, by rfl⟩ : syracuseStep 2715287 = 4072931) B4072931
theorem B13749911 : Blo 1809606 13749911 := bstep (se 1 (by rfl) ⟨10312433, by rfl⟩ : syracuseStep 13749911 = 20624867) B20624867
theorem B2715353 : Blo 1809606 2715353 := bstep (se 2 (by rfl) ⟨1018257, by rfl⟩ : syracuseStep 2715353 = 2036515) B2036515
theorem B4075289 : Blo 1809606 4075289 := bstep (se 2 (by rfl) ⟨1528233, by rfl⟩ : syracuseStep 4075289 = 3056467) B3056467
theorem B3436339 : Blo 1809606 3436339 := bstep (se 1 (by rfl) ⟨2577254, by rfl⟩ : syracuseStep 3436339 = 5154509) B5154509
theorem B11595595 : Blo 1809606 11595595 := bstep (se 1 (by rfl) ⟨8696696, by rfl⟩ : syracuseStep 11595595 = 17393393) B17393393
theorem B2715467 : Blo 1809606 2715467 := bstep (se 1 (by rfl) ⟨2036600, by rfl⟩ : syracuseStep 2715467 = 4073201) B4073201
theorem B4583243 : Blo 1809606 4583243 := bstep (se 1 (by rfl) ⟨3437432, by rfl⟩ : syracuseStep 4583243 = 6874865) B6874865
theorem B2715479 : Blo 1809606 2715479 := bstep (se 1 (by rfl) ⟨2036609, by rfl⟩ : syracuseStep 2715479 = 4073219) B4073219
theorem B6877021 : Blo 1809606 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B4075379 : Blo 1809606 4075379 := bstep (se 1 (by rfl) ⟨3056534, by rfl⟩ : syracuseStep 4075379 = 6113069) B6113069
theorem B9170819 : Blo 1809606 9170819 := bstep (se 1 (by rfl) ⟨6878114, by rfl⟩ : syracuseStep 9170819 = 13756229) B13756229
theorem B8261527 : Blo 1809606 8261527 := bstep (se 1 (by rfl) ⟨6196145, by rfl⟩ : syracuseStep 8261527 = 12392291) B12392291
theorem B4075415 : Blo 1809606 4075415 := bstep (se 1 (by rfl) ⟨3056561, by rfl⟩ : syracuseStep 4075415 = 6113123) B6113123
theorem B2715545 : Blo 1809606 2715545 := bstep (se 2 (by rfl) ⟨1018329, by rfl⟩ : syracuseStep 2715545 = 2036659) B2036659
theorem B2715659 : Blo 1809606 2715659 := bstep (se 1 (by rfl) ⟨2036744, by rfl⟩ : syracuseStep 2715659 = 4073489) B4073489
theorem B2715671 : Blo 1809606 2715671 := bstep (se 1 (by rfl) ⟨2036753, by rfl⟩ : syracuseStep 2715671 = 4073507) B4073507
theorem B9793601 : Blo 1809606 9793601 := bstep (se 2 (by rfl) ⟨3672600, by rfl⟩ : syracuseStep 9793601 = 7345201) B7345201
theorem B11006027 : Blo 1809606 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B31354955 : Blo 1809606 31354955 := bstep (se 1 (by rfl) ⟨23516216, by rfl⟩ : syracuseStep 31354955 = 47032433) B47032433
theorem B4075595 : Blo 1809606 4075595 := bstep (se 1 (by rfl) ⟨3056696, by rfl⟩ : syracuseStep 4075595 = 6113393) B6113393
theorem B2715737 : Blo 1809606 2715737 := bstep (se 2 (by rfl) ⟨1018401, by rfl⟩ : syracuseStep 2715737 = 2036803) B2036803
theorem B2035831 : Blo 1809606 2035831 := bstep (se 1 (by rfl) ⟨1526873, by rfl⟩ : syracuseStep 2035831 = 3053747) B3053747
theorem B4075649 : Blo 1809606 4075649 := bstep (se 2 (by rfl) ⟨1528368, by rfl⟩ : syracuseStep 4075649 = 3056737) B3056737
theorem B2715851 : Blo 1809606 2715851 := bstep (se 1 (by rfl) ⟨2036888, by rfl⟩ : syracuseStep 2715851 = 4073777) B4073777
theorem B1814731 : Blo 1809606 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B2715863 : Blo 1809606 2715863 := bstep (se 1 (by rfl) ⟨2036897, by rfl⟩ : syracuseStep 2715863 = 4073795) B4073795
theorem B3436825 : Blo 1809606 3436825 := bstep (se 2 (by rfl) ⟨1288809, by rfl⟩ : syracuseStep 3436825 = 2577619) B2577619
theorem B2715929 : Blo 1809606 2715929 := bstep (se 2 (by rfl) ⟨1018473, by rfl⟩ : syracuseStep 2715929 = 2036947) B2036947
theorem B2036011 : Blo 1809606 2036011 := bstep (se 1 (by rfl) ⟨1527008, by rfl⟩ : syracuseStep 2036011 = 3054017) B3054017
theorem B5157209 : Blo 1809606 5157209 := bstep (se 2 (by rfl) ⟨1933953, by rfl⟩ : syracuseStep 5157209 = 3867907) B3867907
theorem B4075865 : Blo 1809606 4075865 := bstep (se 2 (by rfl) ⟨1528449, by rfl⟩ : syracuseStep 4075865 = 3056899) B3056899
theorem B2716043 : Blo 1809606 2716043 := bstep (se 1 (by rfl) ⟨2037032, by rfl⟩ : syracuseStep 2716043 = 4074065) B4074065
theorem B2036119 : Blo 1809606 2036119 := bstep (se 1 (by rfl) ⟨1527089, by rfl⟩ : syracuseStep 2036119 = 3054179) B3054179
theorem B2716055 : Blo 1809606 2716055 := bstep (se 1 (by rfl) ⟨2037041, by rfl⟩ : syracuseStep 2716055 = 4074083) B4074083
theorem B17633713 : Blo 1809606 17633713 := bstep (se 2 (by rfl) ⟨6612642, by rfl⟩ : syracuseStep 17633713 = 13225285) B13225285
theorem B4075955 : Blo 1809606 4075955 := bstep (se 1 (by rfl) ⟨3056966, by rfl⟩ : syracuseStep 4075955 = 6113933) B6113933
theorem B6525377 : Blo 1809606 6525377 := bstep (se 2 (by rfl) ⟨2447016, by rfl⟩ : syracuseStep 6525377 = 4894033) B4894033
theorem B4075991 : Blo 1809606 4075991 := bstep (se 1 (by rfl) ⟨3056993, by rfl⟩ : syracuseStep 4075991 = 6113987) B6113987
theorem B2716121 : Blo 1809606 2716121 := bstep (se 2 (by rfl) ⟨1018545, by rfl⟩ : syracuseStep 2716121 = 2037091) B2037091
theorem B6107723 : Blo 1809606 6107723 := bstep (se 1 (by rfl) ⟨4580792, by rfl⟩ : syracuseStep 6107723 = 9161585) B9161585
theorem B2036299 : Blo 1809606 2036299 := bstep (se 1 (by rfl) ⟨1527224, by rfl⟩ : syracuseStep 2036299 = 3054449) B3054449
theorem B2716235 : Blo 1809606 2716235 := bstep (se 1 (by rfl) ⟨2037176, by rfl⟩ : syracuseStep 2716235 = 4074353) B4074353
theorem B2716247 : Blo 1809606 2716247 := bstep (se 1 (by rfl) ⟨2037185, by rfl⟩ : syracuseStep 2716247 = 4074371) B4074371
theorem B20632157 : Blo 1809606 20632157 := bstep (se 3 (by rfl) ⟨3868529, by rfl⟩ : syracuseStep 20632157 = 7737059) B7737059
theorem B7738001 : Blo 1809606 7738001 := bstep (se 2 (by rfl) ⟨2901750, by rfl⟩ : syracuseStep 7738001 = 5803501) B5803501
theorem B2716313 : Blo 1809606 2716313 := bstep (se 2 (by rfl) ⟨1018617, by rfl⟩ : syracuseStep 2716313 = 2037235) B2037235
theorem B2036407 : Blo 1809606 2036407 := bstep (se 1 (by rfl) ⟨1527305, by rfl⟩ : syracuseStep 2036407 = 3054611) B3054611
theorem B2716427 : Blo 1809606 2716427 := bstep (se 1 (by rfl) ⟨2037320, by rfl⟩ : syracuseStep 2716427 = 4074641) B4074641
theorem B7729937 : Blo 1809606 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B9286417 : Blo 1809606 9286417 := bstep (se 2 (by rfl) ⟨3482406, by rfl⟩ : syracuseStep 9286417 = 6964813) B6964813
theorem B2716439 : Blo 1809606 2716439 := bstep (se 1 (by rfl) ⟨2037329, by rfl⟩ : syracuseStep 2716439 = 4074659) B4074659
theorem B4584215 : Blo 1809606 4584215 := bstep (se 1 (by rfl) ⟨3438161, by rfl⟩ : syracuseStep 4584215 = 6876323) B6876323
theorem B3437387 : Blo 1809606 3437387 := bstep (se 1 (by rfl) ⟨2578040, by rfl⟩ : syracuseStep 3437387 = 5156081) B5156081
theorem B6107993 : Blo 1809606 6107993 := bstep (se 2 (by rfl) ⟨2290497, by rfl⟩ : syracuseStep 6107993 = 4580995) B4580995
theorem B2716505 : Blo 1809606 2716505 := bstep (se 2 (by rfl) ⟨1018689, by rfl⟩ : syracuseStep 2716505 = 2037379) B2037379
theorem B2036587 : Blo 1809606 2036587 := bstep (se 1 (by rfl) ⟨1527440, by rfl⟩ : syracuseStep 2036587 = 3054881) B3054881
theorem B2716619 : Blo 1809606 2716619 := bstep (se 1 (by rfl) ⟨2037464, by rfl⟩ : syracuseStep 2716619 = 4074929) B4074929
theorem B2036695 : Blo 1809606 2036695 := bstep (se 1 (by rfl) ⟨1527521, by rfl⟩ : syracuseStep 2036695 = 3055043) B3055043
theorem B2716631 : Blo 1809606 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B3437569 : Blo 1809606 3437569 := bstep (se 2 (by rfl) ⟨1289088, by rfl⟩ : syracuseStep 3437569 = 2578177) B2578177
theorem B2716697 : Blo 1809606 2716697 := bstep (se 2 (by rfl) ⟨1018761, by rfl⟩ : syracuseStep 2716697 = 2037523) B2037523
theorem B2446411 : Blo 1809606 2446411 := bstep (se 1 (by rfl) ⟨1834808, by rfl⟩ : syracuseStep 2446411 = 3669617) B3669617
theorem B2176087 : Blo 1809606 2176087 := bstep (se 1 (by rfl) ⟨1632065, by rfl⟩ : syracuseStep 2176087 = 3264131) B3264131
theorem B6878297 : Blo 1809606 6878297 := bstep (se 2 (by rfl) ⟨2579361, by rfl⟩ : syracuseStep 6878297 = 5158723) B5158723
theorem B2479243 : Blo 1809606 2479243 := bstep (se 1 (by rfl) ⟨1859432, by rfl⟩ : syracuseStep 2479243 = 3718865) B3718865
theorem B2036875 : Blo 1809606 2036875 := bstep (se 1 (by rfl) ⟨1527656, by rfl⟩ : syracuseStep 2036875 = 3055313) B3055313
theorem B2716811 : Blo 1809606 2716811 := bstep (se 1 (by rfl) ⟨2037608, by rfl⟩ : syracuseStep 2716811 = 4075217) B4075217
theorem B2716823 : Blo 1809606 2716823 := bstep (se 1 (by rfl) ⟨2037617, by rfl⟩ : syracuseStep 2716823 = 4075235) B4075235
theorem B2716889 : Blo 1809606 2716889 := bstep (se 2 (by rfl) ⟨1018833, by rfl⟩ : syracuseStep 2716889 = 2037667) B2037667
theorem B2036983 : Blo 1809606 2036983 := bstep (se 1 (by rfl) ⟨1527737, by rfl⟩ : syracuseStep 2036983 = 3055475) B3055475
theorem B7943447 : Blo 1809606 7943447 := bstep (se 1 (by rfl) ⟨5957585, by rfl⟩ : syracuseStep 7943447 = 11915171) B11915171
theorem B2577739 : Blo 1809606 2577739 := bstep (se 1 (by rfl) ⟨1933304, by rfl⟩ : syracuseStep 2577739 = 3866609) B3866609
theorem B2717003 : Blo 1809606 2717003 := bstep (se 1 (by rfl) ⟨2037752, by rfl⟩ : syracuseStep 2717003 = 4075505) B4075505
theorem B2717015 : Blo 1809606 2717015 := bstep (se 1 (by rfl) ⟨2037761, by rfl⟩ : syracuseStep 2717015 = 4075523) B4075523
theorem B2291095 : Blo 1809606 2291095 := bstep (se 1 (by rfl) ⟨1718321, by rfl⟩ : syracuseStep 2291095 = 3436643) B3436643
theorem B2717081 : Blo 1809606 2717081 := bstep (se 2 (by rfl) ⟨1018905, by rfl⟩ : syracuseStep 2717081 = 2037811) B2037811
theorem B2037163 : Blo 1809606 2037163 := bstep (se 1 (by rfl) ⟨1527872, by rfl⟩ : syracuseStep 2037163 = 3055745) B3055745
theorem B4584883 : Blo 1809606 4584883 := bstep (se 1 (by rfl) ⟨3438662, by rfl⟩ : syracuseStep 4584883 = 6877325) B6877325
theorem B7730635 : Blo 1809606 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B2717195 : Blo 1809606 2717195 := bstep (se 1 (by rfl) ⟨2037896, by rfl⟩ : syracuseStep 2717195 = 4075793) B4075793
theorem B6108695 : Blo 1809606 6108695 := bstep (se 1 (by rfl) ⟨4581521, by rfl⟩ : syracuseStep 6108695 = 9163043) B9163043
theorem B2037271 : Blo 1809606 2037271 := bstep (se 1 (by rfl) ⟨1527953, by rfl⟩ : syracuseStep 2037271 = 3055907) B3055907
theorem B2717207 : Blo 1809606 2717207 := bstep (se 1 (by rfl) ⟨2037905, by rfl⟩ : syracuseStep 2717207 = 4075811) B4075811
theorem B4585025 : Blo 1809606 4585025 := bstep (se 2 (by rfl) ⟨1719384, by rfl⟩ : syracuseStep 4585025 = 3438769) B3438769
theorem B2717273 : Blo 1809606 2717273 := bstep (se 2 (by rfl) ⟨1018977, by rfl⟩ : syracuseStep 2717273 = 2037955) B2037955
theorem B12383837 : Blo 1809606 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B2037451 : Blo 1809606 2037451 := bstep (se 1 (by rfl) ⟨1528088, by rfl⟩ : syracuseStep 2037451 = 3056177) B3056177
theorem B3438283 : Blo 1809606 3438283 := bstep (se 1 (by rfl) ⟨2578712, by rfl⟩ : syracuseStep 3438283 = 5157425) B5157425
theorem B15464141 : Blo 1809606 15464141 := bstep (se 3 (by rfl) ⟨2899526, by rfl⟩ : syracuseStep 15464141 = 5799053) B5799053
theorem B2717387 : Blo 1809606 2717387 := bstep (se 1 (by rfl) ⟨2038040, by rfl⟩ : syracuseStep 2717387 = 4076081) B4076081
theorem B2717399 : Blo 1809606 2717399 := bstep (se 1 (by rfl) ⟨2038049, by rfl⟩ : syracuseStep 2717399 = 4076099) B4076099
theorem B7730909 : Blo 1809606 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B6616849 : Blo 1809606 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B3438359 : Blo 1809606 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B12392237 : Blo 1809606 12392237 := bstep (se 3 (by rfl) ⟨2323544, by rfl⟩ : syracuseStep 12392237 = 4647089) B4647089
theorem B2037559 : Blo 1809606 2037559 := bstep (se 1 (by rfl) ⟨1528169, by rfl⟩ : syracuseStep 2037559 = 3056339) B3056339
theorem B3921815 : Blo 1809606 3921815 := bstep (se 1 (by rfl) ⟨2941361, by rfl⟩ : syracuseStep 3921815 = 5882723) B5882723
theorem B6870977 : Blo 1809606 6870977 := bstep (se 2 (by rfl) ⟨2576616, by rfl⟩ : syracuseStep 6870977 = 5153233) B5153233
theorem B2037739 : Blo 1809606 2037739 := bstep (se 1 (by rfl) ⟨1528304, by rfl⟩ : syracuseStep 2037739 = 3056609) B3056609
theorem B6969361 : Blo 1809606 6969361 := bstep (se 2 (by rfl) ⟨2613510, by rfl⟩ : syracuseStep 6969361 = 5227021) B5227021
theorem B7731251 : Blo 1809606 7731251 := bstep (se 1 (by rfl) ⟨5798438, by rfl⟩ : syracuseStep 7731251 = 11596877) B11596877
theorem B6109235 : Blo 1809606 6109235 := bstep (se 1 (by rfl) ⟨4581926, by rfl⟩ : syracuseStep 6109235 = 9163853) B9163853
theorem B2037847 : Blo 1809606 2037847 := bstep (se 1 (by rfl) ⟨1528385, by rfl⟩ : syracuseStep 2037847 = 3056771) B3056771
theorem B39172247 : Blo 1809606 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B2291915 : Blo 1809606 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B2038027 : Blo 1809606 2038027 := bstep (se 1 (by rfl) ⟨1528520, by rfl⟩ : syracuseStep 2038027 = 3057041) B3057041
theorem B2939159 : Blo 1809606 2939159 := bstep (se 1 (by rfl) ⟨2204369, by rfl⟩ : syracuseStep 2939159 = 4408739) B4408739
theorem B7444759 : Blo 1809606 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B6109505 : Blo 1809606 6109505 := bstep (se 2 (by rfl) ⟨2291064, by rfl⟩ : syracuseStep 6109505 = 4582129) B4582129
theorem B5798233 : Blo 1809606 5798233 := bstep (se 2 (by rfl) ⟨2174337, by rfl⟩ : syracuseStep 5798233 = 4348675) B4348675
theorem B9165149 : Blo 1809606 9165149 := bstep (se 3 (by rfl) ⟨1718465, by rfl⟩ : syracuseStep 9165149 = 3436931) B3436931
theorem B3053963 : Blo 1809606 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B3439027 : Blo 1809606 3439027 := bstep (se 1 (by rfl) ⟨2579270, by rfl⟩ : syracuseStep 3439027 = 5158541) B5158541
theorem B3054091 : Blo 1809606 3054091 := bstep (se 1 (by rfl) ⟨2290568, by rfl⟩ : syracuseStep 3054091 = 4581137) B4581137
theorem B2578969 : Blo 1809606 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B9787979 : Blo 1809606 9787979 := bstep (se 1 (by rfl) ⟨7340984, by rfl⟩ : syracuseStep 9787979 = 14681969) B14681969
theorem B17406539 : Blo 1809606 17406539 := bstep (se 1 (by rfl) ⟨13054904, by rfl⟩ : syracuseStep 17406539 = 26109809) B26109809
theorem B10312343 : Blo 1809606 10312343 := bstep (se 1 (by rfl) ⟨7734257, by rfl⟩ : syracuseStep 10312343 = 15468515) B15468515
theorem B3054233 : Blo 1809606 3054233 := bstep (se 2 (by rfl) ⟨1145337, by rfl⟩ : syracuseStep 3054233 = 2290675) B2290675
theorem B3054361 : Blo 1809606 3054361 := bstep (se 2 (by rfl) ⟨1145385, by rfl⟩ : syracuseStep 3054361 = 2290771) B2290771
theorem B6110045 : Blo 1809606 6110045 := bstep (se 3 (by rfl) ⟨1145633, by rfl⟩ : syracuseStep 6110045 = 2291267) B2291267
theorem B2292619 : Blo 1809606 2292619 := bstep (se 1 (by rfl) ⟨1719464, by rfl⟩ : syracuseStep 2292619 = 3438929) B3438929
theorem B66059225 : Blo 1809606 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B1809611 : Blo 1809606 1809611 := bstep (se 1 (by rfl) ⟨1357208, by rfl⟩ : syracuseStep 1809611 = 2714417) B2714417
theorem B1809623 : Blo 1809606 1809623 := bstep (se 1 (by rfl) ⟨1357217, by rfl⟩ : syracuseStep 1809623 = 2714435) B2714435
theorem B1809643 : Blo 1809606 1809643 := bstep (se 1 (by rfl) ⟨1357232, by rfl⟩ : syracuseStep 1809643 = 2714465) B2714465
theorem B1809655 : Blo 1809606 1809655 := bstep (se 1 (by rfl) ⟨1357241, by rfl⟩ : syracuseStep 1809655 = 2714483) B2714483
theorem B1809675 : Blo 1809606 1809675 := bstep (se 1 (by rfl) ⟨1357256, by rfl⟩ : syracuseStep 1809675 = 2714513) B2714513
theorem B1809687 : Blo 1809606 1809687 := bstep (se 1 (by rfl) ⟨1357265, by rfl⟩ : syracuseStep 1809687 = 2714531) B2714531
theorem B1809707 : Blo 1809606 1809707 := bstep (se 1 (by rfl) ⟨1357280, by rfl⟩ : syracuseStep 1809707 = 2714561) B2714561
theorem B1809719 : Blo 1809606 1809719 := bstep (se 1 (by rfl) ⟨1357289, by rfl⟩ : syracuseStep 1809719 = 2714579) B2714579
theorem B1809739 : Blo 1809606 1809739 := bstep (se 1 (by rfl) ⟨1357304, by rfl⟩ : syracuseStep 1809739 = 2714609) B2714609
theorem B1809751 : Blo 1809606 1809751 := bstep (se 1 (by rfl) ⟨1357313, by rfl⟩ : syracuseStep 1809751 = 2714627) B2714627
theorem B3054935 : Blo 1809606 3054935 := bstep (se 1 (by rfl) ⟨2291201, by rfl⟩ : syracuseStep 3054935 = 4582403) B4582403
theorem B1809771 : Blo 1809606 1809771 := bstep (se 1 (by rfl) ⟨1357328, by rfl⟩ : syracuseStep 1809771 = 2714657) B2714657
theorem B1809783 : Blo 1809606 1809783 := bstep (se 1 (by rfl) ⟨1357337, by rfl⟩ : syracuseStep 1809783 = 2714675) B2714675
theorem B1809803 : Blo 1809606 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B338967949 : Blo 1809606 338967949 := bstep (se 3 (by rfl) ⟨63556490, by rfl⟩ : syracuseStep 338967949 = 127112981) B127112981
theorem B6872465 : Blo 1809606 6872465 := bstep (se 2 (by rfl) ⟨2577174, by rfl⟩ : syracuseStep 6872465 = 5154349) B5154349
theorem B1809815 : Blo 1809606 1809815 := bstep (se 1 (by rfl) ⟨1357361, by rfl⟩ : syracuseStep 1809815 = 2714723) B2714723
theorem B1809835 : Blo 1809606 1809835 := bstep (se 1 (by rfl) ⟨1357376, by rfl⟩ : syracuseStep 1809835 = 2714753) B2714753
theorem B1809847 : Blo 1809606 1809847 := bstep (se 1 (by rfl) ⟨1357385, by rfl⟩ : syracuseStep 1809847 = 2714771) B2714771
theorem B1809867 : Blo 1809606 1809867 := bstep (se 1 (by rfl) ⟨1357400, by rfl⟩ : syracuseStep 1809867 = 2714801) B2714801
theorem B1809879 : Blo 1809606 1809879 := bstep (se 1 (by rfl) ⟨1357409, by rfl⟩ : syracuseStep 1809879 = 2714819) B2714819
theorem B3055063 : Blo 1809606 3055063 := bstep (se 1 (by rfl) ⟨2291297, by rfl⟩ : syracuseStep 3055063 = 4582595) B4582595
theorem B7339481 : Blo 1809606 7339481 := bstep (se 2 (by rfl) ⟨2752305, by rfl⟩ : syracuseStep 7339481 = 5504611) B5504611
theorem B1809899 : Blo 1809606 1809899 := bstep (se 1 (by rfl) ⟨1357424, by rfl⟩ : syracuseStep 1809899 = 2714849) B2714849
theorem B1809911 : Blo 1809606 1809911 := bstep (se 1 (by rfl) ⟨1357433, by rfl⟩ : syracuseStep 1809911 = 2714867) B2714867
theorem B1809931 : Blo 1809606 1809931 := bstep (se 1 (by rfl) ⟨1357448, by rfl⟩ : syracuseStep 1809931 = 2714897) B2714897
theorem B1809943 : Blo 1809606 1809943 := bstep (se 1 (by rfl) ⟨1357457, by rfl⟩ : syracuseStep 1809943 = 2714915) B2714915
theorem B1809963 : Blo 1809606 1809963 := bstep (se 1 (by rfl) ⟨1357472, by rfl⟩ : syracuseStep 1809963 = 2714945) B2714945
theorem B1809975 : Blo 1809606 1809975 := bstep (se 1 (by rfl) ⟨1357481, by rfl⟩ : syracuseStep 1809975 = 2714963) B2714963
theorem B1809995 : Blo 1809606 1809995 := bstep (se 1 (by rfl) ⟨1357496, by rfl⟩ : syracuseStep 1809995 = 2714993) B2714993
theorem B1810007 : Blo 1809606 1810007 := bstep (se 1 (by rfl) ⟨1357505, by rfl⟩ : syracuseStep 1810007 = 2715011) B2715011
theorem B6528605 : Blo 1809606 6528605 := bstep (se 3 (by rfl) ⟨1224113, by rfl⟩ : syracuseStep 6528605 = 2448227) B2448227
theorem B1810027 : Blo 1809606 1810027 := bstep (se 1 (by rfl) ⟨1357520, by rfl⟩ : syracuseStep 1810027 = 2715041) B2715041
theorem B1810039 : Blo 1809606 1810039 := bstep (se 1 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 1810039 = 2715059) B2715059
theorem B1810059 : Blo 1809606 1810059 := bstep (se 1 (by rfl) ⟨1357544, by rfl⟩ : syracuseStep 1810059 = 2715089) B2715089
theorem B1810071 : Blo 1809606 1810071 := bstep (se 1 (by rfl) ⟨1357553, by rfl⟩ : syracuseStep 1810071 = 2715107) B2715107
theorem B1810091 : Blo 1809606 1810091 := bstep (se 1 (by rfl) ⟨1357568, by rfl⟩ : syracuseStep 1810091 = 2715137) B2715137
theorem B1810103 : Blo 1809606 1810103 := bstep (se 1 (by rfl) ⟨1357577, by rfl⟩ : syracuseStep 1810103 = 2715155) B2715155
theorem B5799617 : Blo 1809606 5799617 := bstep (se 2 (by rfl) ⟨2174856, by rfl⟩ : syracuseStep 5799617 = 4349713) B4349713
theorem B1810123 : Blo 1809606 1810123 := bstep (se 1 (by rfl) ⟨1357592, by rfl⟩ : syracuseStep 1810123 = 2715185) B2715185
theorem B1810135 : Blo 1809606 1810135 := bstep (se 1 (by rfl) ⟨1357601, by rfl⟩ : syracuseStep 1810135 = 2715203) B2715203
theorem B1810155 : Blo 1809606 1810155 := bstep (se 1 (by rfl) ⟨1357616, by rfl⟩ : syracuseStep 1810155 = 2715233) B2715233
theorem B1810167 : Blo 1809606 1810167 := bstep (se 1 (by rfl) ⟨1357625, by rfl⟩ : syracuseStep 1810167 = 2715251) B2715251
theorem B1810187 : Blo 1809606 1810187 := bstep (se 1 (by rfl) ⟨1357640, by rfl⟩ : syracuseStep 1810187 = 2715281) B2715281
theorem B1810199 : Blo 1809606 1810199 := bstep (se 1 (by rfl) ⟨1357649, by rfl⟩ : syracuseStep 1810199 = 2715299) B2715299
theorem B1810219 : Blo 1809606 1810219 := bstep (se 1 (by rfl) ⟨1357664, by rfl⟩ : syracuseStep 1810219 = 2715329) B2715329
theorem B1810231 : Blo 1809606 1810231 := bstep (se 1 (by rfl) ⟨1357673, by rfl⟩ : syracuseStep 1810231 = 2715347) B2715347
theorem B1810251 : Blo 1809606 1810251 := bstep (se 1 (by rfl) ⟨1357688, by rfl⟩ : syracuseStep 1810251 = 2715377) B2715377
theorem B1810263 : Blo 1809606 1810263 := bstep (se 1 (by rfl) ⟨1357697, by rfl⟩ : syracuseStep 1810263 = 2715395) B2715395
theorem B6872921 : Blo 1809606 6872921 := bstep (se 2 (by rfl) ⟨2577345, by rfl⟩ : syracuseStep 6872921 = 5154691) B5154691
theorem B1810283 : Blo 1809606 1810283 := bstep (se 1 (by rfl) ⟨1357712, by rfl⟩ : syracuseStep 1810283 = 2715425) B2715425
theorem B1810295 : Blo 1809606 1810295 := bstep (se 1 (by rfl) ⟨1357721, by rfl⟩ : syracuseStep 1810295 = 2715443) B2715443
theorem B1810315 : Blo 1809606 1810315 := bstep (se 1 (by rfl) ⟨1357736, by rfl⟩ : syracuseStep 1810315 = 2715473) B2715473
theorem B1810327 : Blo 1809606 1810327 := bstep (se 1 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 1810327 = 2715491) B2715491
theorem B1810347 : Blo 1809606 1810347 := bstep (se 1 (by rfl) ⟨1357760, by rfl⟩ : syracuseStep 1810347 = 2715521) B2715521
theorem B1810359 : Blo 1809606 1810359 := bstep (se 1 (by rfl) ⟨1357769, by rfl⟩ : syracuseStep 1810359 = 2715539) B2715539
theorem B1810379 : Blo 1809606 1810379 := bstep (se 1 (by rfl) ⟨1357784, by rfl⟩ : syracuseStep 1810379 = 2715569) B2715569
theorem B6111179 : Blo 1809606 6111179 := bstep (se 1 (by rfl) ⟨4583384, by rfl⟩ : syracuseStep 6111179 = 9166769) B9166769
theorem B1810391 : Blo 1809606 1810391 := bstep (se 1 (by rfl) ⟨1357793, by rfl⟩ : syracuseStep 1810391 = 2715587) B2715587
theorem B23207897 : Blo 1809606 23207897 := bstep (se 2 (by rfl) ⟨8702961, by rfl⟩ : syracuseStep 23207897 = 17405923) B17405923
theorem B1810411 : Blo 1809606 1810411 := bstep (se 1 (by rfl) ⟨1357808, by rfl⟩ : syracuseStep 1810411 = 2715617) B2715617
theorem B1933291 : Blo 1809606 1933291 := bstep (se 1 (by rfl) ⟨1449968, by rfl⟩ : syracuseStep 1933291 = 2899937) B2899937
theorem B1810423 : Blo 1809606 1810423 := bstep (se 1 (by rfl) ⟨1357817, by rfl⟩ : syracuseStep 1810423 = 2715635) B2715635
theorem B1810439 : Blo 1809606 1810439 := bstep (se 1 (by rfl) ⟨1357829, by rfl⟩ : syracuseStep 1810439 = 2715659) B2715659
theorem B1810447 : Blo 1809606 1810447 := bstep (se 1 (by rfl) ⟨1357835, by rfl⟩ : syracuseStep 1810447 = 2715671) B2715671
theorem B12730391 : Blo 1809606 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B6529067 : Blo 1809606 6529067 := bstep (se 1 (by rfl) ⟨4896800, by rfl⟩ : syracuseStep 6529067 = 9793601) B9793601
theorem B1810491 : Blo 1809606 1810491 := bstep (se 1 (by rfl) ⟨1357868, by rfl⟩ : syracuseStep 1810491 = 2715737) B2715737
theorem B8700023 : Blo 1809606 8700023 := bstep (se 1 (by rfl) ⟨6525017, by rfl⟩ : syracuseStep 8700023 = 13050035) B13050035
theorem B1810567 : Blo 1809606 1810567 := bstep (se 1 (by rfl) ⟨1357925, by rfl⟩ : syracuseStep 1810567 = 2715851) B2715851
theorem B1810575 : Blo 1809606 1810575 := bstep (se 1 (by rfl) ⟨1357931, by rfl⟩ : syracuseStep 1810575 = 2715863) B2715863
theorem B3866771 : Blo 1809606 3866771 := bstep (se 1 (by rfl) ⟨2900078, by rfl⟩ : syracuseStep 3866771 = 5800157) B5800157
theorem B1810619 : Blo 1809606 1810619 := bstep (se 1 (by rfl) ⟨1357964, by rfl⟩ : syracuseStep 1810619 = 2715929) B2715929
theorem B1810695 : Blo 1809606 1810695 := bstep (se 1 (by rfl) ⟨1358021, by rfl⟩ : syracuseStep 1810695 = 2716043) B2716043
theorem B1810703 : Blo 1809606 1810703 := bstep (se 1 (by rfl) ⟨1358027, by rfl⟩ : syracuseStep 1810703 = 2716055) B2716055
theorem B6111503 : Blo 1809606 6111503 := bstep (se 1 (by rfl) ⟨4583627, by rfl⟩ : syracuseStep 6111503 = 9167255) B9167255
theorem B4350251 : Blo 1809606 4350251 := bstep (se 1 (by rfl) ⟨3262688, by rfl⟩ : syracuseStep 4350251 = 6525377) B6525377
theorem B1810747 : Blo 1809606 1810747 := bstep (se 1 (by rfl) ⟨1358060, by rfl⟩ : syracuseStep 1810747 = 2716121) B2716121
theorem B4071815 : Blo 1809606 4071815 := bstep (se 1 (by rfl) ⟨3053861, by rfl⟩ : syracuseStep 4071815 = 6107723) B6107723
theorem B4129159 : Blo 1809606 4129159 := bstep (se 1 (by rfl) ⟨3096869, by rfl⟩ : syracuseStep 4129159 = 6193739) B6193739
theorem B1810823 : Blo 1809606 1810823 := bstep (se 1 (by rfl) ⟨1358117, by rfl⟩ : syracuseStep 1810823 = 2716235) B2716235
theorem B1810831 : Blo 1809606 1810831 := bstep (se 1 (by rfl) ⟨1358123, by rfl⟩ : syracuseStep 1810831 = 2716247) B2716247
theorem B13754771 : Blo 1809606 13754771 := bstep (se 1 (by rfl) ⟨10316078, by rfl⟩ : syracuseStep 13754771 = 20632157) B20632157
theorem B1810875 : Blo 1809606 1810875 := bstep (se 1 (by rfl) ⟨1358156, by rfl⟩ : syracuseStep 1810875 = 2716313) B2716313
theorem B14680541 : Blo 1809606 14680541 := bstep (se 3 (by rfl) ⟨2752601, by rfl⟩ : syracuseStep 14680541 = 5505203) B5505203
theorem B1810951 : Blo 1809606 1810951 := bstep (se 1 (by rfl) ⟨1358213, by rfl⟩ : syracuseStep 1810951 = 2716427) B2716427
theorem B5153291 : Blo 1809606 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B1810959 : Blo 1809606 1810959 := bstep (se 1 (by rfl) ⟨1358219, by rfl⟩ : syracuseStep 1810959 = 2716439) B2716439
theorem B3056143 : Blo 1809606 3056143 := bstep (se 1 (by rfl) ⟨2292107, by rfl⟩ : syracuseStep 3056143 = 4584215) B4584215
theorem B6111773 : Blo 1809606 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B4071995 : Blo 1809606 4071995 := bstep (se 1 (by rfl) ⟨3053996, by rfl⟩ : syracuseStep 4071995 = 6107993) B6107993
theorem B2753083 : Blo 1809606 2753083 := bstep (se 1 (by rfl) ⟨2064812, by rfl⟩ : syracuseStep 2753083 = 4129625) B4129625
theorem B2900539 : Blo 1809606 2900539 := bstep (se 1 (by rfl) ⟨2175404, by rfl⟩ : syracuseStep 2900539 = 4350809) B4350809
theorem B1811003 : Blo 1809606 1811003 := bstep (se 1 (by rfl) ⟨1358252, by rfl⟩ : syracuseStep 1811003 = 2716505) B2716505
theorem B23511617 : Blo 1809606 23511617 := bstep (se 2 (by rfl) ⟨8816856, by rfl⟩ : syracuseStep 23511617 = 17633713) B17633713
theorem B1811079 : Blo 1809606 1811079 := bstep (se 1 (by rfl) ⟨1358309, by rfl⟩ : syracuseStep 1811079 = 2716619) B2716619
theorem B1811087 : Blo 1809606 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B4072121 : Blo 1809606 4072121 := bstep (se 2 (by rfl) ⟨1527045, by rfl⟩ : syracuseStep 4072121 = 3054091) B3054091
theorem B1811131 : Blo 1809606 1811131 := bstep (se 1 (by rfl) ⟨1358348, by rfl⟩ : syracuseStep 1811131 = 2716697) B2716697
theorem B1811207 : Blo 1809606 1811207 := bstep (se 1 (by rfl) ⟨1358405, by rfl⟩ : syracuseStep 1811207 = 2716811) B2716811
theorem B1811215 : Blo 1809606 1811215 := bstep (se 1 (by rfl) ⟨1358411, by rfl⟩ : syracuseStep 1811215 = 2716823) B2716823
theorem B13746995 : Blo 1809606 13746995 := bstep (se 1 (by rfl) ⟨10310246, by rfl⟩ : syracuseStep 13746995 = 20620493) B20620493
theorem B1811259 : Blo 1809606 1811259 := bstep (se 1 (by rfl) ⟨1358444, by rfl⟩ : syracuseStep 1811259 = 2716889) B2716889
theorem B1835911 : Blo 1809606 1835911 := bstep (se 1 (by rfl) ⟨1376933, by rfl⟩ : syracuseStep 1835911 = 2753867) B2753867
theorem B1811335 : Blo 1809606 1811335 := bstep (se 1 (by rfl) ⟨1358501, by rfl⟩ : syracuseStep 1811335 = 2717003) B2717003
theorem B1811343 : Blo 1809606 1811343 := bstep (se 1 (by rfl) ⟨1358507, by rfl⟩ : syracuseStep 1811343 = 2717015) B2717015
theorem B3670931 : Blo 1809606 3670931 := bstep (se 1 (by rfl) ⟨2753198, by rfl⟩ : syracuseStep 3670931 = 5506397) B5506397
theorem B1811387 : Blo 1809606 1811387 := bstep (se 1 (by rfl) ⟨1358540, by rfl⟩ : syracuseStep 1811387 = 2717081) B2717081
theorem B1811463 : Blo 1809606 1811463 := bstep (se 1 (by rfl) ⟨1358597, by rfl⟩ : syracuseStep 1811463 = 2717195) B2717195
theorem B4072463 : Blo 1809606 4072463 := bstep (se 1 (by rfl) ⟨3054347, by rfl⟩ : syracuseStep 4072463 = 6108695) B6108695
theorem B2753551 : Blo 1809606 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B1811471 : Blo 1809606 1811471 := bstep (se 1 (by rfl) ⟨1358603, by rfl⟩ : syracuseStep 1811471 = 2717207) B2717207
theorem B4072481 : Blo 1809606 4072481 := bstep (se 2 (by rfl) ⟨1527180, by rfl⟩ : syracuseStep 4072481 = 3054361) B3054361
theorem B3056683 : Blo 1809606 3056683 := bstep (se 1 (by rfl) ⟨2292512, by rfl⟩ : syracuseStep 3056683 = 4585025) B4585025
theorem B1811515 : Blo 1809606 1811515 := bstep (se 1 (by rfl) ⟨1358636, by rfl⟩ : syracuseStep 1811515 = 2717273) B2717273
theorem B4408435 : Blo 1809606 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B1811591 : Blo 1809606 1811591 := bstep (se 1 (by rfl) ⟨1358693, by rfl⟩ : syracuseStep 1811591 = 2717387) B2717387
theorem B1934479 : Blo 1809606 1934479 := bstep (se 1 (by rfl) ⟨1450859, by rfl⟩ : syracuseStep 1934479 = 2901719) B2901719
theorem B1811599 : Blo 1809606 1811599 := bstep (se 1 (by rfl) ⟨1358699, by rfl⟩ : syracuseStep 1811599 = 2717399) B2717399
theorem B5153939 : Blo 1809606 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B3056825 : Blo 1809606 3056825 := bstep (se 2 (by rfl) ⟨1146309, by rfl⟩ : syracuseStep 3056825 = 2292619) B2292619
theorem B9168065 : Blo 1809606 9168065 := bstep (se 2 (by rfl) ⟨3438024, by rfl⟩ : syracuseStep 9168065 = 6876049) B6876049
theorem B4580651 : Blo 1809606 4580651 := bstep (se 1 (by rfl) ⟨3435488, by rfl⟩ : syracuseStep 4580651 = 6870977) B6870977
theorem B5154167 : Blo 1809606 5154167 := bstep (se 1 (by rfl) ⟨3865625, by rfl⟩ : syracuseStep 5154167 = 7731251) B7731251
theorem B4072823 : Blo 1809606 4072823 := bstep (se 1 (by rfl) ⟨3054617, by rfl⟩ : syracuseStep 4072823 = 6109235) B6109235
theorem B16516487 : Blo 1809606 16516487 := bstep (se 1 (by rfl) ⟨12387365, by rfl⟩ : syracuseStep 16516487 = 24774731) B24774731
theorem B3261881 : Blo 1809606 3261881 := bstep (se 2 (by rfl) ⟨1223205, by rfl⟩ : syracuseStep 3261881 = 2446411) B2446411
theorem B2901449 : Blo 1809606 2901449 := bstep (se 2 (by rfl) ⟨1088043, by rfl⟩ : syracuseStep 2901449 = 2176087) B2176087
theorem B6874577 : Blo 1809606 6874577 := bstep (se 2 (by rfl) ⟨2577966, by rfl⟩ : syracuseStep 6874577 = 5155933) B5155933
theorem B1959439 : Blo 1809606 1959439 := bstep (se 1 (by rfl) ⟨1469579, by rfl⟩ : syracuseStep 1959439 = 2939159) B2939159
theorem B26101277 : Blo 1809606 26101277 := bstep (se 3 (by rfl) ⟨4893989, by rfl⟩ : syracuseStep 26101277 = 9787979) B9787979
theorem B4073003 : Blo 1809606 4073003 := bstep (se 1 (by rfl) ⟨3054752, by rfl⟩ : syracuseStep 4073003 = 6109505) B6109505
theorem B2754233 : Blo 1809606 2754233 := bstep (se 2 (by rfl) ⟨1032837, by rfl⟩ : syracuseStep 2754233 = 2065675) B2065675
theorem B6874895 : Blo 1809606 6874895 := bstep (se 1 (by rfl) ⟨5156171, by rfl⟩ : syracuseStep 6874895 = 10312343) B10312343
theorem B5506859 : Blo 1809606 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B15460145 : Blo 1809606 15460145 := bstep (se 2 (by rfl) ⟨5797554, by rfl⟩ : syracuseStep 15460145 = 11595109) B11595109
theorem B4073363 : Blo 1809606 4073363 := bstep (se 1 (by rfl) ⟨3055022, by rfl⟩ : syracuseStep 4073363 = 6110045) B6110045
theorem B6113177 : Blo 1809606 6113177 := bstep (se 2 (by rfl) ⟨2292441, by rfl⟩ : syracuseStep 6113177 = 4584883) B4584883
theorem B10307513 : Blo 1809606 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B4073417 : Blo 1809606 4073417 := bstep (se 2 (by rfl) ⟨1527531, by rfl⟩ : syracuseStep 4073417 = 3055063) B3055063
theorem B8702039 : Blo 1809606 8702039 := bstep (se 1 (by rfl) ⟨6526529, by rfl⟩ : syracuseStep 8702039 = 13053059) B13053059
theorem B4581643 : Blo 1809606 4581643 := bstep (se 1 (by rfl) ⟨3436232, by rfl⟩ : syracuseStep 4581643 = 6872465) B6872465
theorem B18827579 : Blo 1809606 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B4892987 : Blo 1809606 4892987 := bstep (se 1 (by rfl) ⟨3669740, by rfl⟩ : syracuseStep 4892987 = 7339481) B7339481
theorem B4581785 : Blo 1809606 4581785 := bstep (se 2 (by rfl) ⟨1718169, by rfl⟩ : syracuseStep 4581785 = 3436339) B3436339
theorem B15460793 : Blo 1809606 15460793 := bstep (se 2 (by rfl) ⟨5797797, by rfl⟩ : syracuseStep 15460793 = 11595595) B11595595
theorem B9169361 : Blo 1809606 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B4581947 : Blo 1809606 4581947 := bstep (se 1 (by rfl) ⟨3436460, by rfl⟩ : syracuseStep 4581947 = 6872921) B6872921
theorem B6113879 : Blo 1809606 6113879 := bstep (se 1 (by rfl) ⟨4585409, by rfl⟩ : syracuseStep 6113879 = 9170819) B9170819
theorem B4074119 : Blo 1809606 4074119 := bstep (se 1 (by rfl) ⟨3055589, by rfl⟩ : syracuseStep 4074119 = 6111179) B6111179
theorem B9292481 : Blo 1809606 9292481 := bstep (se 2 (by rfl) ⟨3484680, by rfl⟩ : syracuseStep 9292481 = 6969361) B6969361
theorem B2714411 : Blo 1809606 2714411 := bstep (se 1 (by rfl) ⟨2035808, by rfl⟩ : syracuseStep 2714411 = 4071617) B4071617
theorem B4074299 : Blo 1809606 4074299 := bstep (se 1 (by rfl) ⟨3055724, by rfl⟩ : syracuseStep 4074299 = 6111449) B6111449
theorem B2714441 : Blo 1809606 2714441 := bstep (se 2 (by rfl) ⟨1017915, by rfl⟩ : syracuseStep 2714441 = 2035831) B2035831
theorem B4582291 : Blo 1809606 4582291 := bstep (se 1 (by rfl) ⟨3436718, by rfl⟩ : syracuseStep 4582291 = 6873437) B6873437
theorem B89303957 : Blo 1809606 89303957 := bstep (se 6 (by rfl) ⟨2093061, by rfl⟩ : syracuseStep 89303957 = 4186123) B4186123
theorem B4074425 : Blo 1809606 4074425 := bstep (se 2 (by rfl) ⟨1527909, by rfl⟩ : syracuseStep 4074425 = 3055819) B3055819
theorem B2714555 : Blo 1809606 2714555 := bstep (se 1 (by rfl) ⟨2035916, by rfl⟩ : syracuseStep 2714555 = 4071833) B4071833
theorem B2714615 : Blo 1809606 2714615 := bstep (se 1 (by rfl) ⟨2035961, by rfl⟩ : syracuseStep 2714615 = 4071923) B4071923
theorem B2714639 : Blo 1809606 2714639 := bstep (se 1 (by rfl) ⟨2035979, by rfl⟩ : syracuseStep 2714639 = 4071959) B4071959
theorem B4582433 : Blo 1809606 4582433 := bstep (se 2 (by rfl) ⟨1718412, by rfl⟩ : syracuseStep 4582433 = 3436825) B3436825
theorem B9923627 : Blo 1809606 9923627 := bstep (se 1 (by rfl) ⟨7442720, by rfl⟩ : syracuseStep 9923627 = 14885441) B14885441
theorem B2714681 : Blo 1809606 2714681 := bstep (se 2 (by rfl) ⟨1018005, by rfl⟩ : syracuseStep 2714681 = 2036011) B2036011
theorem B2714759 : Blo 1809606 2714759 := bstep (se 1 (by rfl) ⟨2036069, by rfl⟩ : syracuseStep 2714759 = 4072139) B4072139
theorem B2714795 : Blo 1809606 2714795 := bstep (se 1 (by rfl) ⟨2036096, by rfl⟩ : syracuseStep 2714795 = 4072193) B4072193
theorem B2714825 : Blo 1809606 2714825 := bstep (se 2 (by rfl) ⟨1018059, by rfl⟩ : syracuseStep 2714825 = 2036119) B2036119
theorem B4074767 : Blo 1809606 4074767 := bstep (se 1 (by rfl) ⟨3056075, by rfl⟩ : syracuseStep 4074767 = 6112151) B6112151
theorem B4074785 : Blo 1809606 4074785 := bstep (se 2 (by rfl) ⟨1528044, by rfl⟩ : syracuseStep 4074785 = 3056089) B3056089
theorem B2714939 : Blo 1809606 2714939 := bstep (se 1 (by rfl) ⟨2036204, by rfl⟩ : syracuseStep 2714939 = 4072409) B4072409
theorem B2714999 : Blo 1809606 2714999 := bstep (se 1 (by rfl) ⟨2036249, by rfl⟩ : syracuseStep 2714999 = 4072499) B4072499
theorem B2715023 : Blo 1809606 2715023 := bstep (se 1 (by rfl) ⟨2036267, by rfl⟩ : syracuseStep 2715023 = 4072535) B4072535
theorem B2715065 : Blo 1809606 2715065 := bstep (se 2 (by rfl) ⟨1018149, by rfl⟩ : syracuseStep 2715065 = 2036299) B2036299
theorem B66096593 : Blo 1809606 66096593 := bstep (se 2 (by rfl) ⟨24786222, by rfl⟩ : syracuseStep 66096593 = 49572445) B49572445
theorem B2715143 : Blo 1809606 2715143 := bstep (se 1 (by rfl) ⟨2036357, by rfl⟩ : syracuseStep 2715143 = 4072715) B4072715
theorem B5295631 : Blo 1809606 5295631 := bstep (se 1 (by rfl) ⟨3971723, by rfl⟩ : syracuseStep 5295631 = 7943447) B7943447
theorem B2715179 : Blo 1809606 2715179 := bstep (se 1 (by rfl) ⟨2036384, by rfl⟩ : syracuseStep 2715179 = 4072769) B4072769
theorem B2715209 : Blo 1809606 2715209 := bstep (se 2 (by rfl) ⟨1018203, by rfl⟩ : syracuseStep 2715209 = 2036407) B2036407
theorem B4075127 : Blo 1809606 4075127 := bstep (se 1 (by rfl) ⟨3056345, by rfl⟩ : syracuseStep 4075127 = 6112691) B6112691
theorem B26095283 : Blo 1809606 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B2715323 : Blo 1809606 2715323 := bstep (se 1 (by rfl) ⟨2036492, by rfl⟩ : syracuseStep 2715323 = 4072985) B4072985
theorem B12381889 : Blo 1809606 12381889 := bstep (se 2 (by rfl) ⟨4643208, by rfl⟩ : syracuseStep 12381889 = 9286417) B9286417
theorem B9678565 : Blo 1809606 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B2715383 : Blo 1809606 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B2715407 : Blo 1809606 2715407 := bstep (se 1 (by rfl) ⟨2036555, by rfl⟩ : syracuseStep 2715407 = 4073111) B4073111
theorem B7343905 : Blo 1809606 7343905 := bstep (se 2 (by rfl) ⟨2753964, by rfl⟩ : syracuseStep 7343905 = 5507929) B5507929
theorem B4075307 : Blo 1809606 4075307 := bstep (se 1 (by rfl) ⟨3056480, by rfl⟩ : syracuseStep 4075307 = 6112961) B6112961
theorem B10309427 : Blo 1809606 10309427 := bstep (se 1 (by rfl) ⟨7732070, by rfl⟩ : syracuseStep 10309427 = 15464141) B15464141
theorem B2715449 : Blo 1809606 2715449 := bstep (se 2 (by rfl) ⟨1018293, by rfl⟩ : syracuseStep 2715449 = 2036587) B2036587
theorem B2715527 : Blo 1809606 2715527 := bstep (se 1 (by rfl) ⟨2036645, by rfl⟩ : syracuseStep 2715527 = 4073291) B4073291
theorem B2715563 : Blo 1809606 2715563 := bstep (se 1 (by rfl) ⟨2036672, by rfl⟩ : syracuseStep 2715563 = 4073345) B4073345
theorem B2715593 : Blo 1809606 2715593 := bstep (se 2 (by rfl) ⟨1018347, by rfl⟩ : syracuseStep 2715593 = 2036695) B2036695
theorem B4583425 : Blo 1809606 4583425 := bstep (se 2 (by rfl) ⟨1718784, by rfl⟩ : syracuseStep 4583425 = 3437569) B3437569
theorem B2715707 : Blo 1809606 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B2715767 : Blo 1809606 2715767 := bstep (se 1 (by rfl) ⟨2036825, by rfl⟩ : syracuseStep 2715767 = 4073651) B4073651
theorem B2715791 : Blo 1809606 2715791 := bstep (se 1 (by rfl) ⟨2036843, by rfl⟩ : syracuseStep 2715791 = 4073687) B4073687
theorem B4075667 : Blo 1809606 4075667 := bstep (se 1 (by rfl) ⟨3056750, by rfl⟩ : syracuseStep 4075667 = 6113501) B6113501
theorem B3305657 : Blo 1809606 3305657 := bstep (se 2 (by rfl) ⟨1239621, by rfl⟩ : syracuseStep 3305657 = 2479243) B2479243
theorem B2715833 : Blo 1809606 2715833 := bstep (se 2 (by rfl) ⟨1018437, by rfl⟩ : syracuseStep 2715833 = 2036875) B2036875
theorem B39170249 : Blo 1809606 39170249 := bstep (se 2 (by rfl) ⟨14688843, by rfl⟩ : syracuseStep 39170249 = 29377687) B29377687
theorem B4075721 : Blo 1809606 4075721 := bstep (se 2 (by rfl) ⟨1528395, by rfl⟩ : syracuseStep 4075721 = 3056791) B3056791
theorem B2035975 : Blo 1809606 2035975 := bstep (se 1 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 2035975 = 3053963) B3053963
theorem B2715911 : Blo 1809606 2715911 := bstep (se 1 (by rfl) ⟨2036933, by rfl⟩ : syracuseStep 2715911 = 4073867) B4073867
theorem B2715947 : Blo 1809606 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B2715977 : Blo 1809606 2715977 := bstep (se 2 (by rfl) ⟨1018491, by rfl⟩ : syracuseStep 2715977 = 2036983) B2036983
theorem B6107507 : Blo 1809606 6107507 := bstep (se 1 (by rfl) ⟨4580630, by rfl⟩ : syracuseStep 6107507 = 9161261) B9161261
theorem B11604359 : Blo 1809606 11604359 := bstep (se 1 (by rfl) ⟨8703269, by rfl⟩ : syracuseStep 11604359 = 17406539) B17406539
theorem B3436985 : Blo 1809606 3436985 := bstep (se 2 (by rfl) ⟨1288869, by rfl⟩ : syracuseStep 3436985 = 2577739) B2577739
theorem B2036155 : Blo 1809606 2036155 := bstep (se 1 (by rfl) ⟨1527116, by rfl⟩ : syracuseStep 2036155 = 3054233) B3054233
theorem B2716091 : Blo 1809606 2716091 := bstep (se 1 (by rfl) ⟨2037068, by rfl⟩ : syracuseStep 2716091 = 4074137) B4074137
theorem B2716151 : Blo 1809606 2716151 := bstep (se 1 (by rfl) ⟨2037113, by rfl⟩ : syracuseStep 2716151 = 4074227) B4074227
theorem B2716175 : Blo 1809606 2716175 := bstep (se 1 (by rfl) ⟨2037131, by rfl⟩ : syracuseStep 2716175 = 4074263) B4074263
theorem B5157391 : Blo 1809606 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B451957265 : Blo 1809606 451957265 := bstep (se 2 (by rfl) ⟨169483974, by rfl⟩ : syracuseStep 451957265 = 338967949) B338967949
theorem B13742621 : Blo 1809606 13742621 := bstep (se 3 (by rfl) ⟨2576741, by rfl⟩ : syracuseStep 13742621 = 5153483) B5153483
theorem B2716217 : Blo 1809606 2716217 := bstep (se 2 (by rfl) ⟨1018581, by rfl⟩ : syracuseStep 2716217 = 2037163) B2037163
theorem B4584023 : Blo 1809606 4584023 := bstep (se 1 (by rfl) ⟨3438017, by rfl⟩ : syracuseStep 4584023 = 6876035) B6876035
theorem B2290295 : Blo 1809606 2290295 := bstep (se 1 (by rfl) ⟨1717721, by rfl⟩ : syracuseStep 2290295 = 3435443) B3435443
theorem B2716295 : Blo 1809606 2716295 := bstep (se 1 (by rfl) ⟨2037221, by rfl⟩ : syracuseStep 2716295 = 4074443) B4074443
theorem B2716331 : Blo 1809606 2716331 := bstep (se 1 (by rfl) ⟨2037248, by rfl⟩ : syracuseStep 2716331 = 4074497) B4074497
theorem B2716361 : Blo 1809606 2716361 := bstep (se 2 (by rfl) ⟨1018635, by rfl⟩ : syracuseStep 2716361 = 2037271) B2037271
theorem B2290447 : Blo 1809606 2290447 := bstep (se 1 (by rfl) ⟨1717835, by rfl⟩ : syracuseStep 2290447 = 3435671) B3435671
theorem B15463183 : Blo 1809606 15463183 := bstep (se 1 (by rfl) ⟨11597387, by rfl⟩ : syracuseStep 15463183 = 23194775) B23194775
theorem B5157665 : Blo 1809606 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B4584235 : Blo 1809606 4584235 := bstep (se 1 (by rfl) ⟨3438176, by rfl⟩ : syracuseStep 4584235 = 6876353) B6876353
theorem B2716475 : Blo 1809606 2716475 := bstep (se 1 (by rfl) ⟨2037356, by rfl⟩ : syracuseStep 2716475 = 4074713) B4074713
theorem B2716535 : Blo 1809606 2716535 := bstep (se 1 (by rfl) ⟨2037401, by rfl⟩ : syracuseStep 2716535 = 4074803) B4074803
theorem B2036623 : Blo 1809606 2036623 := bstep (se 1 (by rfl) ⟨1527467, by rfl⟩ : syracuseStep 2036623 = 3054935) B3054935
theorem B2716559 : Blo 1809606 2716559 := bstep (se 1 (by rfl) ⟨2037419, by rfl⟩ : syracuseStep 2716559 = 4074839) B4074839
theorem B2716601 : Blo 1809606 2716601 := bstep (se 2 (by rfl) ⟨1018725, by rfl⟩ : syracuseStep 2716601 = 2037451) B2037451
theorem B4584377 : Blo 1809606 4584377 := bstep (se 2 (by rfl) ⟨1719141, by rfl⟩ : syracuseStep 4584377 = 3438283) B3438283
theorem B2290619 : Blo 1809606 2290619 := bstep (se 1 (by rfl) ⟨1717964, by rfl⟩ : syracuseStep 2290619 = 3435929) B3435929
theorem B37671941 : Blo 1809606 37671941 := bstep (se 4 (by rfl) ⟨3531744, by rfl⟩ : syracuseStep 37671941 = 7063489) B7063489
theorem B2716679 : Blo 1809606 2716679 := bstep (se 1 (by rfl) ⟨2037509, by rfl⟩ : syracuseStep 2716679 = 4075019) B4075019
theorem B2716715 : Blo 1809606 2716715 := bstep (se 1 (by rfl) ⟨2037536, by rfl⟩ : syracuseStep 2716715 = 4075073) B4075073
theorem B10458173 : Blo 1809606 10458173 := bstep (se 3 (by rfl) ⟨1960907, by rfl⟩ : syracuseStep 10458173 = 3921815) B3921815
theorem B2716745 : Blo 1809606 2716745 := bstep (se 2 (by rfl) ⟨1018779, by rfl⟩ : syracuseStep 2716745 = 2037559) B2037559
theorem B2716859 : Blo 1809606 2716859 := bstep (se 1 (by rfl) ⟨2037644, by rfl⟩ : syracuseStep 2716859 = 4075289) B4075289
theorem B11015369 : Blo 1809606 11015369 := bstep (se 2 (by rfl) ⟨4130763, by rfl⟩ : syracuseStep 11015369 = 8261527) B8261527
theorem B10310885 : Blo 1809606 10310885 := bstep (se 4 (by rfl) ⟨966645, by rfl⟩ : syracuseStep 10310885 = 1933291) B1933291
theorem B17872109 : Blo 1809606 17872109 := bstep (se 3 (by rfl) ⟨3351020, by rfl⟩ : syracuseStep 17872109 = 6702041) B6702041
theorem B2716919 : Blo 1809606 2716919 := bstep (se 1 (by rfl) ⟨2037689, by rfl⟩ : syracuseStep 2716919 = 4075379) B4075379
theorem B2716943 : Blo 1809606 2716943 := bstep (se 1 (by rfl) ⟨2037707, by rfl⟩ : syracuseStep 2716943 = 4075415) B4075415
theorem B2716985 : Blo 1809606 2716985 := bstep (se 2 (by rfl) ⟨1018869, by rfl⟩ : syracuseStep 2716985 = 2037739) B2037739
theorem B15471931 : Blo 1809606 15471931 := bstep (se 1 (by rfl) ⟨11603948, by rfl⟩ : syracuseStep 15471931 = 23207897) B23207897
theorem B20903303 : Blo 1809606 20903303 := bstep (se 1 (by rfl) ⟨15677477, by rfl⟩ : syracuseStep 20903303 = 31354955) B31354955
theorem B7337351 : Blo 1809606 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B2037127 : Blo 1809606 2037127 := bstep (se 1 (by rfl) ⟨1527845, by rfl⟩ : syracuseStep 2037127 = 3055691) B3055691
theorem B2717063 : Blo 1809606 2717063 := bstep (se 1 (by rfl) ⟨2037797, by rfl⟩ : syracuseStep 2717063 = 4075595) B4075595
theorem B9164177 : Blo 1809606 9164177 := bstep (se 2 (by rfl) ⟨3436566, by rfl⟩ : syracuseStep 9164177 = 6873133) B6873133
theorem B2577835 : Blo 1809606 2577835 := bstep (se 1 (by rfl) ⟨1933376, by rfl⟩ : syracuseStep 2577835 = 3866753) B3866753
theorem B2717099 : Blo 1809606 2717099 := bstep (se 1 (by rfl) ⟨2037824, by rfl⟩ : syracuseStep 2717099 = 4075649) B4075649
theorem B2717129 : Blo 1809606 2717129 := bstep (se 2 (by rfl) ⟨1018923, by rfl⟩ : syracuseStep 2717129 = 2037847) B2037847
theorem B2037307 : Blo 1809606 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B3438139 : Blo 1809606 3438139 := bstep (se 1 (by rfl) ⟨2578604, by rfl⟩ : syracuseStep 3438139 = 5157209) B5157209
theorem B2717243 : Blo 1809606 2717243 := bstep (se 1 (by rfl) ⟨2037932, by rfl⟩ : syracuseStep 2717243 = 4075865) B4075865
theorem B15472205 : Blo 1809606 15472205 := bstep (se 3 (by rfl) ⟨2901038, by rfl⟩ : syracuseStep 15472205 = 5802077) B5802077
theorem B2717303 : Blo 1809606 2717303 := bstep (se 1 (by rfl) ⟨2037977, by rfl⟩ : syracuseStep 2717303 = 4075955) B4075955
theorem B2578063 : Blo 1809606 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B2717327 : Blo 1809606 2717327 := bstep (se 1 (by rfl) ⟨2037995, by rfl⟩ : syracuseStep 2717327 = 4075991) B4075991
theorem B2717369 : Blo 1809606 2717369 := bstep (se 2 (by rfl) ⟨1019013, by rfl⟩ : syracuseStep 2717369 = 2038027) B2038027
theorem B9926345 : Blo 1809606 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B11015909 : Blo 1809606 11015909 := bstep (se 4 (by rfl) ⟨1032741, by rfl⟩ : syracuseStep 11015909 = 2065483) B2065483
theorem B8697581 : Blo 1809606 8697581 := bstep (se 3 (by rfl) ⟨1630796, by rfl⟩ : syracuseStep 8697581 = 3261593) B3261593
theorem B5158667 : Blo 1809606 5158667 := bstep (se 1 (by rfl) ⟨3869000, by rfl⟩ : syracuseStep 5158667 = 7738001) B7738001
theorem B4896541 : Blo 1809606 4896541 := bstep (se 3 (by rfl) ⟨918101, by rfl⟩ : syracuseStep 4896541 = 1836203) B1836203
theorem B7730977 : Blo 1809606 7730977 := bstep (se 2 (by rfl) ⟨2899116, by rfl⟩ : syracuseStep 7730977 = 5798233) B5798233
theorem B2291591 : Blo 1809606 2291591 := bstep (se 1 (by rfl) ⟨1718693, by rfl⟩ : syracuseStep 2291591 = 3437387) B3437387
theorem B10311569 : Blo 1809606 10311569 := bstep (se 2 (by rfl) ⟨3866838, by rfl⟩ : syracuseStep 10311569 = 7733677) B7733677
theorem B4585369 : Blo 1809606 4585369 := bstep (se 2 (by rfl) ⟨1719513, by rfl⟩ : syracuseStep 4585369 = 3439027) B3439027
theorem B2578439 : Blo 1809606 2578439 := bstep (se 1 (by rfl) ⟨1933829, by rfl⟩ : syracuseStep 2578439 = 3867659) B3867659
theorem B2037775 : Blo 1809606 2037775 := bstep (se 1 (by rfl) ⟨1528331, by rfl⟩ : syracuseStep 2037775 = 3056663) B3056663
theorem B3438625 : Blo 1809606 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B4585531 : Blo 1809606 4585531 := bstep (se 1 (by rfl) ⟨3439148, by rfl⟩ : syracuseStep 4585531 = 6878297) B6878297
theorem B69638453 : Blo 1809606 69638453 := bstep (se 5 (by rfl) ⟨3264302, by rfl⟩ : syracuseStep 69638453 = 6528605) B6528605
theorem B8255891 : Blo 1809606 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B60340697 : Blo 1809606 60340697 := bstep (se 2 (by rfl) ⟨22627761, by rfl⟩ : syracuseStep 60340697 = 45255523) B45255523
theorem B2292239 : Blo 1809606 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B4348475 : Blo 1809606 4348475 := bstep (se 1 (by rfl) ⟨3261356, by rfl⟩ : syracuseStep 4348475 = 6522713) B6522713
theorem B3054199 : Blo 1809606 3054199 := bstep (se 1 (by rfl) ⟨2290649, by rfl⟩ : syracuseStep 3054199 = 4581299) B4581299
theorem B26114831 : Blo 1809606 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B3054395 : Blo 1809606 3054395 := bstep (se 1 (by rfl) ⟨2290796, by rfl⟩ : syracuseStep 3054395 = 4581593) B4581593
theorem B6110099 : Blo 1809606 6110099 := bstep (se 1 (by rfl) ⟨4582574, by rfl⟩ : syracuseStep 6110099 = 9165149) B9165149
theorem B10312595 : Blo 1809606 10312595 := bstep (se 1 (by rfl) ⟨7734446, by rfl⟩ : syracuseStep 10312595 = 15468893) B15468893
theorem B3054793 : Blo 1809606 3054793 := bstep (se 2 (by rfl) ⟨1145547, by rfl⟩ : syracuseStep 3054793 = 2291095) B2291095
theorem B1809671 : Blo 1809606 1809671 := bstep (se 1 (by rfl) ⟨1357253, by rfl⟩ : syracuseStep 1809671 = 2714507) B2714507
theorem B1809679 : Blo 1809606 1809679 := bstep (se 1 (by rfl) ⟨1357259, by rfl⟩ : syracuseStep 1809679 = 2714519) B2714519
theorem B1809723 : Blo 1809606 1809723 := bstep (se 1 (by rfl) ⟨1357292, by rfl⟩ : syracuseStep 1809723 = 2714585) B2714585
theorem B44039483 : Blo 1809606 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B6872435 : Blo 1809606 6872435 := bstep (se 1 (by rfl) ⟨5154326, by rfl⟩ : syracuseStep 6872435 = 10308653) B10308653
theorem B1809799 : Blo 1809606 1809799 := bstep (se 1 (by rfl) ⟨1357349, by rfl⟩ : syracuseStep 1809799 = 2714699) B2714699
theorem B1809807 : Blo 1809606 1809807 := bstep (se 1 (by rfl) ⟨1357355, by rfl⟩ : syracuseStep 1809807 = 2714711) B2714711
theorem B15678865 : Blo 1809606 15678865 := bstep (se 2 (by rfl) ⟨5879574, by rfl⟩ : syracuseStep 15678865 = 11759149) B11759149
theorem B1809851 : Blo 1809606 1809851 := bstep (se 1 (by rfl) ⟨1357388, by rfl⟩ : syracuseStep 1809851 = 2714777) B2714777
theorem B9166283 : Blo 1809606 9166283 := bstep (se 1 (by rfl) ⟨6874712, by rfl⟩ : syracuseStep 9166283 = 13749425) B13749425
theorem B33045965 : Blo 1809606 33045965 := bstep (se 3 (by rfl) ⟨6196118, by rfl⟩ : syracuseStep 33045965 = 12392237) B12392237
theorem B1809927 : Blo 1809606 1809927 := bstep (se 1 (by rfl) ⟨1357445, by rfl⟩ : syracuseStep 1809927 = 2714891) B2714891
theorem B1809935 : Blo 1809606 1809935 := bstep (se 1 (by rfl) ⟨1357451, by rfl⟩ : syracuseStep 1809935 = 2714903) B2714903
theorem B4349483 : Blo 1809606 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B1809979 : Blo 1809606 1809979 := bstep (se 1 (by rfl) ⟨1357484, by rfl⟩ : syracuseStep 1809979 = 2714969) B2714969
theorem B1810055 : Blo 1809606 1810055 := bstep (se 1 (by rfl) ⟨1357541, by rfl⟩ : syracuseStep 1810055 = 2715083) B2715083
theorem B1810063 : Blo 1809606 1810063 := bstep (se 1 (by rfl) ⟨1357547, by rfl⟩ : syracuseStep 1810063 = 2715095) B2715095
theorem B1810107 : Blo 1809606 1810107 := bstep (se 1 (by rfl) ⟨1357580, by rfl⟩ : syracuseStep 1810107 = 2715161) B2715161
theorem B8822465 : Blo 1809606 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1810183 : Blo 1809606 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B1810191 : Blo 1809606 1810191 := bstep (se 1 (by rfl) ⟨1357643, by rfl⟩ : syracuseStep 1810191 = 2715287) B2715287
theorem B9166607 : Blo 1809606 9166607 := bstep (se 1 (by rfl) ⟨6874955, by rfl⟩ : syracuseStep 9166607 = 13749911) B13749911
theorem B3866411 : Blo 1809606 3866411 := bstep (se 1 (by rfl) ⟨2899808, by rfl⟩ : syracuseStep 3866411 = 5799617) B5799617
theorem B1810235 : Blo 1809606 1810235 := bstep (se 1 (by rfl) ⟨1357676, by rfl⟩ : syracuseStep 1810235 = 2715353) B2715353
theorem B1810311 : Blo 1809606 1810311 := bstep (se 1 (by rfl) ⟨1357733, by rfl⟩ : syracuseStep 1810311 = 2715467) B2715467
theorem B3055495 : Blo 1809606 3055495 := bstep (se 1 (by rfl) ⟨2291621, by rfl⟩ : syracuseStep 3055495 = 4583243) B4583243
theorem B1810319 : Blo 1809606 1810319 := bstep (se 1 (by rfl) ⟨1357739, by rfl⟩ : syracuseStep 1810319 = 2715479) B2715479
theorem B4644761 : Blo 1809606 4644761 := bstep (se 2 (by rfl) ⟨1741785, by rfl⟩ : syracuseStep 4644761 = 3483571) B3483571
theorem B1810363 : Blo 1809606 1810363 := bstep (se 1 (by rfl) ⟨1357772, by rfl⟩ : syracuseStep 1810363 = 2715545) B2715545
theorem B6111233 : Blo 1809606 6111233 := bstep (se 2 (by rfl) ⟨2291712, by rfl⟩ : syracuseStep 6111233 = 4583425) B4583425
theorem B8486927 : Blo 1809606 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B1810471 : Blo 1809606 1810471 := bstep (se 1 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 1810471 = 2715707) B2715707
theorem B5800015 : Blo 1809606 5800015 := bstep (se 1 (by rfl) ⟨4350011, by rfl⟩ : syracuseStep 5800015 = 8700023) B8700023
theorem B1810511 : Blo 1809606 1810511 := bstep (se 1 (by rfl) ⟨1357883, by rfl⟩ : syracuseStep 1810511 = 2715767) B2715767
theorem B1810527 : Blo 1809606 1810527 := bstep (se 1 (by rfl) ⟨1357895, by rfl⟩ : syracuseStep 1810527 = 2715791) B2715791
theorem B2203771 : Blo 1809606 2203771 := bstep (se 1 (by rfl) ⟨1652828, by rfl⟩ : syracuseStep 2203771 = 3305657) B3305657
theorem B1810555 : Blo 1809606 1810555 := bstep (se 1 (by rfl) ⟨1357916, by rfl⟩ : syracuseStep 1810555 = 2715833) B2715833
theorem B1810607 : Blo 1809606 1810607 := bstep (se 1 (by rfl) ⟨1357955, by rfl⟩ : syracuseStep 1810607 = 2715911) B2715911
theorem B2900167 : Blo 1809606 2900167 := bstep (se 1 (by rfl) ⟨2175125, by rfl⟩ : syracuseStep 2900167 = 4350251) B4350251
theorem B1810631 : Blo 1809606 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B1810651 : Blo 1809606 1810651 := bstep (se 1 (by rfl) ⟨1357988, by rfl⟩ : syracuseStep 1810651 = 2715977) B2715977
theorem B4071671 : Blo 1809606 4071671 := bstep (se 1 (by rfl) ⟨3053753, by rfl⟩ : syracuseStep 4071671 = 6107507) B6107507
theorem B1810727 : Blo 1809606 1810727 := bstep (se 1 (by rfl) ⟨1358045, by rfl⟩ : syracuseStep 1810727 = 2716091) B2716091
theorem B1810767 : Blo 1809606 1810767 := bstep (se 1 (by rfl) ⟨1358075, by rfl⟩ : syracuseStep 1810767 = 2716151) B2716151
theorem B1810783 : Blo 1809606 1810783 := bstep (se 1 (by rfl) ⟨1358087, by rfl⟩ : syracuseStep 1810783 = 2716175) B2716175
theorem B1810811 : Blo 1809606 1810811 := bstep (se 1 (by rfl) ⟨1358108, by rfl⟩ : syracuseStep 1810811 = 2716217) B2716217
theorem B3056015 : Blo 1809606 3056015 := bstep (se 1 (by rfl) ⟨2292011, by rfl⟩ : syracuseStep 3056015 = 4584023) B4584023
theorem B1810863 : Blo 1809606 1810863 := bstep (se 1 (by rfl) ⟨1358147, by rfl⟩ : syracuseStep 1810863 = 2716295) B2716295
theorem B1810887 : Blo 1809606 1810887 := bstep (se 1 (by rfl) ⟨1358165, by rfl⟩ : syracuseStep 1810887 = 2716331) B2716331
theorem B1810907 : Blo 1809606 1810907 := bstep (se 1 (by rfl) ⟨1358180, by rfl⟩ : syracuseStep 1810907 = 2716361) B2716361
theorem B5505545 : Blo 1809606 5505545 := bstep (se 2 (by rfl) ⟨2064579, by rfl⟩ : syracuseStep 5505545 = 4129159) B4129159
theorem B1810983 : Blo 1809606 1810983 := bstep (se 1 (by rfl) ⟨1358237, by rfl⟩ : syracuseStep 1810983 = 2716475) B2716475
theorem B1811023 : Blo 1809606 1811023 := bstep (se 1 (by rfl) ⟨1358267, by rfl⟩ : syracuseStep 1811023 = 2716535) B2716535
theorem B1811039 : Blo 1809606 1811039 := bstep (se 1 (by rfl) ⟨1358279, by rfl⟩ : syracuseStep 1811039 = 2716559) B2716559
theorem B23511653 : Blo 1809606 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B1811067 : Blo 1809606 1811067 := bstep (se 1 (by rfl) ⟨1358300, by rfl⟩ : syracuseStep 1811067 = 2716601) B2716601
theorem B3056251 : Blo 1809606 3056251 := bstep (se 1 (by rfl) ⟨2292188, by rfl⟩ : syracuseStep 3056251 = 4584377) B4584377
theorem B1811119 : Blo 1809606 1811119 := bstep (se 1 (by rfl) ⟨1358339, by rfl⟩ : syracuseStep 1811119 = 2716679) B2716679
theorem B1811143 : Blo 1809606 1811143 := bstep (se 1 (by rfl) ⟨1358357, by rfl⟩ : syracuseStep 1811143 = 2716715) B2716715
theorem B6972115 : Blo 1809606 6972115 := bstep (se 1 (by rfl) ⟨5229086, by rfl⟩ : syracuseStep 6972115 = 10458173) B10458173
theorem B1811163 : Blo 1809606 1811163 := bstep (se 1 (by rfl) ⟨1358372, by rfl⟩ : syracuseStep 1811163 = 2716745) B2716745
theorem B3670777 : Blo 1809606 3670777 := bstep (se 2 (by rfl) ⟨1376541, by rfl⟩ : syracuseStep 3670777 = 2753083) B2753083
theorem B1811239 : Blo 1809606 1811239 := bstep (se 1 (by rfl) ⟨1358429, by rfl⟩ : syracuseStep 1811239 = 2716859) B2716859
theorem B6112043 : Blo 1809606 6112043 := bstep (se 1 (by rfl) ⟨4584032, by rfl⟩ : syracuseStep 6112043 = 9168065) B9168065
theorem B6873923 : Blo 1809606 6873923 := bstep (se 1 (by rfl) ⟨5155442, by rfl⟩ : syracuseStep 6873923 = 10310885) B10310885
theorem B4072265 : Blo 1809606 4072265 := bstep (se 2 (by rfl) ⟨1527099, by rfl⟩ : syracuseStep 4072265 = 3054199) B3054199
theorem B1811279 : Blo 1809606 1811279 := bstep (se 1 (by rfl) ⟨1358459, by rfl⟩ : syracuseStep 1811279 = 2716919) B2716919
theorem B1811295 : Blo 1809606 1811295 := bstep (se 1 (by rfl) ⟨1358471, by rfl⟩ : syracuseStep 1811295 = 2716943) B2716943
theorem B1811323 : Blo 1809606 1811323 := bstep (se 1 (by rfl) ⟨1358492, by rfl⟩ : syracuseStep 1811323 = 2716985) B2716985
theorem B11010991 : Blo 1809606 11010991 := bstep (se 1 (by rfl) ⟨8258243, by rfl⟩ : syracuseStep 11010991 = 16516487) B16516487
theorem B1811375 : Blo 1809606 1811375 := bstep (se 1 (by rfl) ⟨1358531, by rfl⟩ : syracuseStep 1811375 = 2717063) B2717063
theorem B1811399 : Blo 1809606 1811399 := bstep (se 1 (by rfl) ⟨1358549, by rfl⟩ : syracuseStep 1811399 = 2717099) B2717099
theorem B1934299 : Blo 1809606 1934299 := bstep (se 1 (by rfl) ⟨1450724, by rfl⟩ : syracuseStep 1934299 = 2901449) B2901449
theorem B1811419 : Blo 1809606 1811419 := bstep (se 1 (by rfl) ⟨1358564, by rfl⟩ : syracuseStep 1811419 = 2717129) B2717129
theorem B17400851 : Blo 1809606 17400851 := bstep (se 1 (by rfl) ⟨13050638, by rfl⟩ : syracuseStep 17400851 = 26101277) B26101277
theorem B1811495 : Blo 1809606 1811495 := bstep (se 1 (by rfl) ⟨1358621, by rfl⟩ : syracuseStep 1811495 = 2717243) B2717243
theorem B10314803 : Blo 1809606 10314803 := bstep (se 1 (by rfl) ⟨7736102, by rfl⟩ : syracuseStep 10314803 = 15472205) B15472205
theorem B6112313 : Blo 1809606 6112313 := bstep (se 2 (by rfl) ⟨2292117, by rfl⟩ : syracuseStep 6112313 = 4584235) B4584235
theorem B1811535 : Blo 1809606 1811535 := bstep (se 1 (by rfl) ⟨1358651, by rfl⟩ : syracuseStep 1811535 = 2717303) B2717303
theorem B1811551 : Blo 1809606 1811551 := bstep (se 1 (by rfl) ⟨1358663, by rfl⟩ : syracuseStep 1811551 = 2717327) B2717327
theorem B1836155 : Blo 1809606 1836155 := bstep (se 1 (by rfl) ⟨1377116, by rfl⟩ : syracuseStep 1836155 = 2754233) B2754233
theorem B1811579 : Blo 1809606 1811579 := bstep (se 1 (by rfl) ⟨1358684, by rfl⟩ : syracuseStep 1811579 = 2717369) B2717369
theorem B3671239 : Blo 1809606 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B10306763 : Blo 1809606 10306763 := bstep (se 1 (by rfl) ⟨7730072, by rfl⟩ : syracuseStep 10306763 = 15460145) B15460145
theorem B6874379 : Blo 1809606 6874379 := bstep (se 1 (by rfl) ⟨5155784, by rfl⟩ : syracuseStep 6874379 = 10311569) B10311569
theorem B3671401 : Blo 1809606 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B6112637 : Blo 1809606 6112637 := bstep (se 3 (by rfl) ⟨1146119, by rfl⟩ : syracuseStep 6112637 = 2292239) B2292239
theorem B46425635 : Blo 1809606 46425635 := bstep (se 1 (by rfl) ⟨34819226, by rfl⟩ : syracuseStep 46425635 = 69638453) B69638453
theorem B3261991 : Blo 1809606 3261991 := bstep (se 1 (by rfl) ⟨2446493, by rfl⟩ : syracuseStep 3261991 = 4892987) B4892987
theorem B4073057 : Blo 1809606 4073057 := bstep (se 2 (by rfl) ⟨1527396, by rfl⟩ : syracuseStep 4073057 = 3054793) B3054793
theorem B10307195 : Blo 1809606 10307195 := bstep (se 1 (by rfl) ⟨7730396, by rfl⟩ : syracuseStep 10307195 = 15460793) B15460793
theorem B6112907 : Blo 1809606 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B20629241 : Blo 1809606 20629241 := bstep (se 2 (by rfl) ⟨7735965, by rfl⟩ : syracuseStep 20629241 = 15471931) B15471931
theorem B6194987 : Blo 1809606 6194987 := bstep (se 1 (by rfl) ⟨4646240, by rfl⟩ : syracuseStep 6194987 = 9292481) B9292481
theorem B17409887 : Blo 1809606 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B26470253 : Blo 1809606 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B4073399 : Blo 1809606 4073399 := bstep (se 1 (by rfl) ⟨3055049, by rfl⟩ : syracuseStep 4073399 = 6110099) B6110099
theorem B6875063 : Blo 1809606 6875063 := bstep (se 1 (by rfl) ⟨5156297, by rfl⟩ : syracuseStep 6875063 = 10312595) B10312595
theorem B13748453 : Blo 1809606 13748453 := bstep (se 4 (by rfl) ⟨1288917, by rfl⟩ : syracuseStep 13748453 = 2577835) B2577835
theorem B4581623 : Blo 1809606 4581623 := bstep (se 1 (by rfl) ⟨3436217, by rfl⟩ : syracuseStep 4581623 = 6872435) B6872435
theorem B16509185 : Blo 1809606 16509185 := bstep (se 2 (by rfl) ⟨6190944, by rfl⟩ : syracuseStep 16509185 = 12381889) B12381889
theorem B12904753 : Blo 1809606 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B22030643 : Blo 1809606 22030643 := bstep (se 1 (by rfl) ⟨16522982, by rfl⟩ : syracuseStep 22030643 = 33045965) B33045965
theorem B10307969 : Blo 1809606 10307969 := bstep (se 2 (by rfl) ⟨3865488, by rfl⟩ : syracuseStep 10307969 = 7730977) B7730977
theorem B9791873 : Blo 1809606 9791873 := bstep (se 2 (by rfl) ⟨3671952, by rfl⟩ : syracuseStep 9791873 = 7343905) B7343905
theorem B4073993 : Blo 1809606 4073993 := bstep (se 2 (by rfl) ⟨1527747, by rfl⟩ : syracuseStep 4073993 = 3055495) B3055495
theorem B6113825 : Blo 1809606 6113825 := bstep (se 2 (by rfl) ⟨2292684, by rfl⟩ : syracuseStep 6113825 = 4585369) B4585369
theorem B6875837 : Blo 1809606 6875837 := bstep (se 3 (by rfl) ⟨1289219, by rfl⟩ : syracuseStep 6875837 = 2578439) B2578439
theorem B4352711 : Blo 1809606 4352711 := bstep (se 1 (by rfl) ⟨3264533, by rfl⟩ : syracuseStep 4352711 = 6529067) B6529067
theorem B6114041 : Blo 1809606 6114041 := bstep (se 2 (by rfl) ⟨2292765, by rfl⟩ : syracuseStep 6114041 = 4585531) B4585531
theorem B4074335 : Blo 1809606 4074335 := bstep (se 1 (by rfl) ⟨3055751, by rfl⟩ : syracuseStep 4074335 = 6111503) B6111503
theorem B2714543 : Blo 1809606 2714543 := bstep (se 1 (by rfl) ⟨2035907, by rfl⟩ : syracuseStep 2714543 = 4071815) B4071815
theorem B7736239 : Blo 1809606 7736239 := bstep (se 1 (by rfl) ⟨5802179, by rfl⟩ : syracuseStep 7736239 = 11604359) B11604359
theorem B9169847 : Blo 1809606 9169847 := bstep (se 1 (by rfl) ⟨6877385, by rfl⟩ : syracuseStep 9169847 = 13754771) B13754771
theorem B15469541 : Blo 1809606 15469541 := bstep (se 4 (by rfl) ⟨1450269, by rfl⟩ : syracuseStep 15469541 = 2900539) B2900539
theorem B3435527 : Blo 1809606 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B2714633 : Blo 1809606 2714633 := bstep (se 2 (by rfl) ⟨1017987, by rfl⟩ : syracuseStep 2714633 = 2035975) B2035975
theorem B301304843 : Blo 1809606 301304843 := bstep (se 1 (by rfl) ⟨225978632, by rfl⟩ : syracuseStep 301304843 = 451957265) B451957265
theorem B9161747 : Blo 1809606 9161747 := bstep (se 1 (by rfl) ⟨6871310, by rfl⟩ : syracuseStep 9161747 = 13742621) B13742621
theorem B4074515 : Blo 1809606 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B2714663 : Blo 1809606 2714663 := bstep (se 1 (by rfl) ⟨2035997, by rfl⟩ : syracuseStep 2714663 = 4071995) B4071995
theorem B15674411 : Blo 1809606 15674411 := bstep (se 1 (by rfl) ⟨11755808, by rfl⟩ : syracuseStep 15674411 = 23511617) B23511617
theorem B2714747 : Blo 1809606 2714747 := bstep (se 1 (by rfl) ⟨2036060, by rfl⟩ : syracuseStep 2714747 = 4072121) B4072121
theorem B2714873 : Blo 1809606 2714873 := bstep (se 2 (by rfl) ⟨1018077, by rfl⟩ : syracuseStep 2714873 = 2036155) B2036155
theorem B2714975 : Blo 1809606 2714975 := bstep (se 1 (by rfl) ⟨2036231, by rfl⟩ : syracuseStep 2714975 = 4072463) B4072463
theorem B4074857 : Blo 1809606 4074857 := bstep (se 2 (by rfl) ⟨1528071, by rfl⟩ : syracuseStep 4074857 = 3056143) B3056143
theorem B6876521 : Blo 1809606 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B2714987 : Blo 1809606 2714987 := bstep (se 1 (by rfl) ⟨2036240, by rfl⟩ : syracuseStep 2714987 = 4072481) B4072481
theorem B3435959 : Blo 1809606 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B7343579 : Blo 1809606 7343579 := bstep (se 1 (by rfl) ⟨5507684, by rfl⟩ : syracuseStep 7343579 = 11015369) B11015369
theorem B11914739 : Blo 1809606 11914739 := bstep (se 1 (by rfl) ⟨8936054, by rfl⟩ : syracuseStep 11914739 = 17872109) B17872109
theorem B3436111 : Blo 1809606 3436111 := bstep (se 1 (by rfl) ⟨2577083, by rfl⟩ : syracuseStep 3436111 = 5154167) B5154167
theorem B2715215 : Blo 1809606 2715215 := bstep (se 1 (by rfl) ⟨2036411, by rfl⟩ : syracuseStep 2715215 = 4072823) B4072823
theorem B4583051 : Blo 1809606 4583051 := bstep (se 1 (by rfl) ⟨3437288, by rfl⟩ : syracuseStep 4583051 = 6874577) B6874577
theorem B55742141 : Blo 1809606 55742141 := bstep (se 3 (by rfl) ⟨10451651, by rfl⟩ : syracuseStep 55742141 = 20903303) B20903303
theorem B19566269 : Blo 1809606 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B2715335 : Blo 1809606 2715335 := bstep (se 1 (by rfl) ⟨2036501, by rfl⟩ : syracuseStep 2715335 = 4073003) B4073003
theorem B22015709 : Blo 1809606 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B7343939 : Blo 1809606 7343939 := bstep (se 1 (by rfl) ⟨5507954, by rfl⟩ : syracuseStep 7343939 = 11015909) B11015909
theorem B4583263 : Blo 1809606 4583263 := bstep (se 1 (by rfl) ⟨3437447, by rfl⟩ : syracuseStep 4583263 = 6874895) B6874895
theorem B2715497 : Blo 1809606 2715497 := bstep (se 2 (by rfl) ⟨1018311, by rfl⟩ : syracuseStep 2715497 = 2036623) B2036623
theorem B2715575 : Blo 1809606 2715575 := bstep (se 1 (by rfl) ⟨2036681, by rfl⟩ : syracuseStep 2715575 = 4073363) B4073363
theorem B4075451 : Blo 1809606 4075451 := bstep (se 1 (by rfl) ⟨3056588, by rfl⟩ : syracuseStep 4075451 = 6113177) B6113177
theorem B2715611 : Blo 1809606 2715611 := bstep (se 1 (by rfl) ⟨2036708, by rfl⟩ : syracuseStep 2715611 = 4073417) B4073417
theorem B4075577 : Blo 1809606 4075577 := bstep (se 2 (by rfl) ⟨1528341, by rfl⟩ : syracuseStep 4075577 = 3056683) B3056683
theorem B40227131 : Blo 1809606 40227131 := bstep (se 1 (by rfl) ⟨30170348, by rfl⟩ : syracuseStep 40227131 = 60340697) B60340697
theorem B6107453 : Blo 1809606 6107453 := bstep (se 3 (by rfl) ⟨1145147, by rfl⟩ : syracuseStep 6107453 = 2290295) B2290295
theorem B4075919 : Blo 1809606 4075919 := bstep (se 1 (by rfl) ⟨3056939, by rfl⟩ : syracuseStep 4075919 = 6113879) B6113879
theorem B2716079 : Blo 1809606 2716079 := bstep (se 1 (by rfl) ⟨2037059, by rfl⟩ : syracuseStep 2716079 = 4074119) B4074119
theorem B2716169 : Blo 1809606 2716169 := bstep (se 2 (by rfl) ⟨1018563, by rfl⟩ : syracuseStep 2716169 = 2037127) B2037127
theorem B2036263 : Blo 1809606 2036263 := bstep (se 1 (by rfl) ⟨1527197, by rfl⟩ : syracuseStep 2036263 = 3054395) B3054395
theorem B2716199 : Blo 1809606 2716199 := bstep (se 1 (by rfl) ⟨2037149, by rfl⟩ : syracuseStep 2716199 = 4074299) B4074299
theorem B59535971 : Blo 1809606 59535971 := bstep (se 1 (by rfl) ⟨44651978, by rfl⟩ : syracuseStep 59535971 = 89303957) B89303957
theorem B2716283 : Blo 1809606 2716283 := bstep (se 1 (by rfl) ⟨2037212, by rfl⟩ : syracuseStep 2716283 = 4074425) B4074425
theorem B6615751 : Blo 1809606 6615751 := bstep (se 1 (by rfl) ⟨4961813, by rfl⟩ : syracuseStep 6615751 = 9923627) B9923627
theorem B2716409 : Blo 1809606 2716409 := bstep (se 2 (by rfl) ⟨1018653, by rfl⟩ : syracuseStep 2716409 = 2037307) B2037307
theorem B4584185 : Blo 1809606 4584185 := bstep (se 2 (by rfl) ⟨1719069, by rfl⟩ : syracuseStep 4584185 = 3438139) B3438139
theorem B83620613 : Blo 1809606 83620613 := bstep (se 4 (by rfl) ⟨7839432, by rfl⟩ : syracuseStep 83620613 = 15678865) B15678865
theorem B10310429 : Blo 1809606 10310429 := bstep (se 3 (by rfl) ⟨1933205, by rfl⟩ : syracuseStep 10310429 = 3866411) B3866411
theorem B2716511 : Blo 1809606 2716511 := bstep (se 1 (by rfl) ⟨2037383, by rfl⟩ : syracuseStep 2716511 = 4074767) B4074767
theorem B3437417 : Blo 1809606 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B2716523 : Blo 1809606 2716523 := bstep (se 1 (by rfl) ⟨2037392, by rfl⟩ : syracuseStep 2716523 = 4074785) B4074785
theorem B2716751 : Blo 1809606 2716751 := bstep (se 1 (by rfl) ⟨2037563, by rfl⟩ : syracuseStep 2716751 = 4075127) B4075127
theorem B17396855 : Blo 1809606 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B6108317 : Blo 1809606 6108317 := bstep (se 3 (by rfl) ⟨1145309, by rfl⟩ : syracuseStep 6108317 = 2290619) B2290619
theorem B2716871 : Blo 1809606 2716871 := bstep (se 1 (by rfl) ⟨2037653, by rfl⟩ : syracuseStep 2716871 = 4075307) B4075307
theorem B2717033 : Blo 1809606 2717033 := bstep (se 2 (by rfl) ⟨1018887, by rfl⟩ : syracuseStep 2717033 = 2037775) B2037775
theorem B4584833 : Blo 1809606 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B2577847 : Blo 1809606 2577847 := bstep (se 1 (by rfl) ⟨1933385, by rfl⟩ : syracuseStep 2577847 = 3866771) B3866771
theorem B2717111 : Blo 1809606 2717111 := bstep (se 1 (by rfl) ⟨2037833, by rfl⟩ : syracuseStep 2717111 = 4075667) B4075667
theorem B26113499 : Blo 1809606 26113499 := bstep (se 1 (by rfl) ⟨19585124, by rfl⟩ : syracuseStep 26113499 = 39170249) B39170249
theorem B2717147 : Blo 1809606 2717147 := bstep (se 1 (by rfl) ⟨2037860, by rfl⟩ : syracuseStep 2717147 = 4075721) B4075721
theorem B23205437 : Blo 1809606 23205437 := bstep (se 3 (by rfl) ⟨4351019, by rfl⟩ : syracuseStep 23205437 = 8702039) B8702039
theorem B2291323 : Blo 1809606 2291323 := bstep (se 1 (by rfl) ⟨1718492, by rfl⟩ : syracuseStep 2291323 = 3436985) B3436985
theorem B9787027 : Blo 1809606 9787027 := bstep (se 1 (by rfl) ⟨7340270, by rfl⟩ : syracuseStep 9787027 = 14680541) B14680541
theorem B6108857 : Blo 1809606 6108857 := bstep (se 2 (by rfl) ⟨2290821, by rfl⟩ : syracuseStep 6108857 = 4581643) B4581643
theorem B3438443 : Blo 1809606 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B9164663 : Blo 1809606 9164663 := bstep (se 1 (by rfl) ⟨6873497, by rfl⟩ : syracuseStep 9164663 = 13746995) B13746995
theorem B25114627 : Blo 1809606 25114627 := bstep (se 1 (by rfl) ⟨18835970, by rfl⟩ : syracuseStep 25114627 = 37671941) B37671941
theorem B2037883 : Blo 1809606 2037883 := bstep (se 1 (by rfl) ⟨1528412, by rfl⟩ : syracuseStep 2037883 = 3056825) B3056825
theorem B50206877 : Blo 1809606 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B3053767 : Blo 1809606 3053767 := bstep (se 1 (by rfl) ⟨2290325, by rfl⟩ : syracuseStep 3053767 = 4580651) B4580651
theorem B6109451 : Blo 1809606 6109451 := bstep (se 1 (by rfl) ⟨4582088, by rfl⟩ : syracuseStep 6109451 = 9164177) B9164177
theorem B3053929 : Blo 1809606 3053929 := bstep (se 2 (by rfl) ⟨1145223, by rfl⟩ : syracuseStep 3053929 = 2290447) B2290447
theorem B20617577 : Blo 1809606 20617577 := bstep (se 2 (by rfl) ⟨7731591, by rfl⟩ : syracuseStep 20617577 = 15463183) B15463183
theorem B8698349 : Blo 1809606 8698349 := bstep (se 3 (by rfl) ⟨1630940, by rfl⟩ : syracuseStep 8698349 = 3261881) B3261881
theorem B5798387 : Blo 1809606 5798387 := bstep (se 1 (by rfl) ⟨4348790, by rfl⟩ : syracuseStep 5798387 = 8697581) B8697581
theorem B3439111 : Blo 1809606 3439111 := bstep (se 1 (by rfl) ⟨2579333, by rfl⟩ : syracuseStep 3439111 = 5158667) B5158667
theorem B2447881 : Blo 1809606 2447881 := bstep (se 2 (by rfl) ⟨917955, by rfl⟩ : syracuseStep 2447881 = 1835911) B1835911
theorem B6109721 : Blo 1809606 6109721 := bstep (se 2 (by rfl) ⟨2291145, by rfl⟩ : syracuseStep 6109721 = 4582291) B4582291
theorem B6871675 : Blo 1809606 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B26114885 : Blo 1809606 26114885 := bstep (se 4 (by rfl) ⟨2448270, by rfl⟩ : syracuseStep 26114885 = 4896541) B4896541
theorem B2579305 : Blo 1809606 2579305 := bstep (se 2 (by rfl) ⟨967239, by rfl⟩ : syracuseStep 2579305 = 1934479) B1934479
theorem B3054523 : Blo 1809606 3054523 := bstep (se 1 (by rfl) ⟨2290892, by rfl⟩ : syracuseStep 3054523 = 4581785) B4581785
theorem B2898983 : Blo 1809606 2898983 := bstep (se 1 (by rfl) ⟨2174237, by rfl⟩ : syracuseStep 2898983 = 4348475) B4348475
theorem B3054631 : Blo 1809606 3054631 := bstep (se 1 (by rfl) ⟨2290973, by rfl⟩ : syracuseStep 3054631 = 4581947) B4581947
theorem B1809607 : Blo 1809606 1809607 := bstep (se 1 (by rfl) ⟨1357205, by rfl⟩ : syracuseStep 1809607 = 2714411) B2714411
theorem B1809627 : Blo 1809606 1809627 := bstep (se 1 (by rfl) ⟨1357220, by rfl⟩ : syracuseStep 1809627 = 2714441) B2714441
theorem B1809703 : Blo 1809606 1809703 := bstep (se 1 (by rfl) ⟨1357277, by rfl⟩ : syracuseStep 1809703 = 2714555) B2714555
theorem B1809743 : Blo 1809606 1809743 := bstep (se 1 (by rfl) ⟨1357307, by rfl⟩ : syracuseStep 1809743 = 2714615) B2714615
theorem B1809759 : Blo 1809606 1809759 := bstep (se 1 (by rfl) ⟨1357319, by rfl⟩ : syracuseStep 1809759 = 2714639) B2714639
theorem B7060841 : Blo 1809606 7060841 := bstep (se 2 (by rfl) ⟨2647815, by rfl⟩ : syracuseStep 7060841 = 5295631) B5295631
theorem B2612585 : Blo 1809606 2612585 := bstep (se 2 (by rfl) ⟨979719, by rfl⟩ : syracuseStep 2612585 = 1959439) B1959439
theorem B3054955 : Blo 1809606 3054955 := bstep (se 1 (by rfl) ⟨2291216, by rfl⟩ : syracuseStep 3054955 = 4582433) B4582433
theorem B1809787 : Blo 1809606 1809787 := bstep (se 1 (by rfl) ⟨1357340, by rfl⟩ : syracuseStep 1809787 = 2714681) B2714681
theorem B1809839 : Blo 1809606 1809839 := bstep (se 1 (by rfl) ⟨1357379, by rfl⟩ : syracuseStep 1809839 = 2714759) B2714759
theorem B1809863 : Blo 1809606 1809863 := bstep (se 1 (by rfl) ⟨1357397, by rfl⟩ : syracuseStep 1809863 = 2714795) B2714795
theorem B1809883 : Blo 1809606 1809883 := bstep (se 1 (by rfl) ⟨1357412, by rfl⟩ : syracuseStep 1809883 = 2714825) B2714825
theorem B1809959 : Blo 1809606 1809959 := bstep (se 1 (by rfl) ⟨1357469, by rfl⟩ : syracuseStep 1809959 = 2714939) B2714939
theorem B29359655 : Blo 1809606 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B1809999 : Blo 1809606 1809999 := bstep (se 1 (by rfl) ⟨1357499, by rfl⟩ : syracuseStep 1809999 = 2714999) B2714999
theorem B1810015 : Blo 1809606 1810015 := bstep (se 1 (by rfl) ⟨1357511, by rfl⟩ : syracuseStep 1810015 = 2715023) B2715023
theorem B1810043 : Blo 1809606 1810043 := bstep (se 1 (by rfl) ⟨1357532, by rfl⟩ : syracuseStep 1810043 = 2715065) B2715065
theorem B6110855 : Blo 1809606 6110855 := bstep (se 1 (by rfl) ⟨4583141, by rfl⟩ : syracuseStep 6110855 = 9166283) B9166283
theorem B44064395 : Blo 1809606 44064395 := bstep (se 1 (by rfl) ⟨33048296, by rfl⟩ : syracuseStep 44064395 = 66096593) B66096593
theorem B1810095 : Blo 1809606 1810095 := bstep (se 1 (by rfl) ⟨1357571, by rfl⟩ : syracuseStep 1810095 = 2715143) B2715143
theorem B6110909 : Blo 1809606 6110909 := bstep (se 3 (by rfl) ⟨1145795, by rfl⟩ : syracuseStep 6110909 = 2291591) B2291591
theorem B1810119 : Blo 1809606 1810119 := bstep (se 1 (by rfl) ⟨1357589, by rfl⟩ : syracuseStep 1810119 = 2715179) B2715179
theorem B2899655 : Blo 1809606 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B1810139 : Blo 1809606 1810139 := bstep (se 1 (by rfl) ⟨1357604, by rfl⟩ : syracuseStep 1810139 = 2715209) B2715209
theorem B9789149 : Blo 1809606 9789149 := bstep (se 3 (by rfl) ⟨1835465, by rfl⟩ : syracuseStep 9789149 = 3670931) B3670931
theorem B12386029 : Blo 1809606 12386029 := bstep (se 3 (by rfl) ⟨2322380, by rfl⟩ : syracuseStep 12386029 = 4644761) B4644761
theorem B1810215 : Blo 1809606 1810215 := bstep (se 1 (by rfl) ⟨1357661, by rfl⟩ : syracuseStep 1810215 = 2715323) B2715323
theorem B5881643 : Blo 1809606 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1810255 : Blo 1809606 1810255 := bstep (se 1 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 1810255 = 2715383) B2715383
theorem B1810271 : Blo 1809606 1810271 := bstep (se 1 (by rfl) ⟨1357703, by rfl⟩ : syracuseStep 1810271 = 2715407) B2715407
theorem B6111071 : Blo 1809606 6111071 := bstep (se 1 (by rfl) ⟨4583303, by rfl⟩ : syracuseStep 6111071 = 9166607) B9166607
theorem B6872951 : Blo 1809606 6872951 := bstep (se 1 (by rfl) ⟨5154713, by rfl⟩ : syracuseStep 6872951 = 10309427) B10309427
theorem B1810299 : Blo 1809606 1810299 := bstep (se 1 (by rfl) ⟨1357724, by rfl⟩ : syracuseStep 1810299 = 2715449) B2715449
theorem B1810351 : Blo 1809606 1810351 := bstep (se 1 (by rfl) ⟨1357763, by rfl⟩ : syracuseStep 1810351 = 2715527) B2715527
theorem B1810375 : Blo 1809606 1810375 := bstep (se 1 (by rfl) ⟨1357781, by rfl⟩ : syracuseStep 1810375 = 2715563) B2715563
theorem B1810395 : Blo 1809606 1810395 := bstep (se 1 (by rfl) ⟨1357796, by rfl⟩ : syracuseStep 1810395 = 2715593) B2715593
theorem B7733353 : Blo 1809606 7733353 := bstep (se 2 (by rfl) ⟨2900007, by rfl⟩ : syracuseStep 7733353 = 5800015) B5800015
theorem B4071635 : Blo 1809606 4071635 := bstep (se 1 (by rfl) ⟨3053726, by rfl⟩ : syracuseStep 4071635 = 6107453) B6107453
theorem B4071689 : Blo 1809606 4071689 := bstep (se 2 (by rfl) ⟨1526883, by rfl⟩ : syracuseStep 4071689 = 3053767) B3053767
theorem B1810719 : Blo 1809606 1810719 := bstep (se 1 (by rfl) ⟨1358039, by rfl⟩ : syracuseStep 1810719 = 2716079) B2716079
theorem B3670363 : Blo 1809606 3670363 := bstep (se 1 (by rfl) ⟨2752772, by rfl⟩ : syracuseStep 3670363 = 5505545) B5505545
theorem B1810779 : Blo 1809606 1810779 := bstep (se 1 (by rfl) ⟨1358084, by rfl⟩ : syracuseStep 1810779 = 2716169) B2716169
theorem B1810799 : Blo 1809606 1810799 := bstep (se 1 (by rfl) ⟨1358099, by rfl⟩ : syracuseStep 1810799 = 2716199) B2716199
theorem B39690647 : Blo 1809606 39690647 := bstep (se 1 (by rfl) ⟨29767985, by rfl⟩ : syracuseStep 39690647 = 59535971) B59535971
theorem B1810855 : Blo 1809606 1810855 := bstep (se 1 (by rfl) ⟨1358141, by rfl⟩ : syracuseStep 1810855 = 2716283) B2716283
theorem B4071905 : Blo 1809606 4071905 := bstep (se 2 (by rfl) ⟨1526964, by rfl⟩ : syracuseStep 4071905 = 3053929) B3053929
theorem B1810939 : Blo 1809606 1810939 := bstep (se 1 (by rfl) ⟨1358204, by rfl⟩ : syracuseStep 1810939 = 2716409) B2716409
theorem B3056123 : Blo 1809606 3056123 := bstep (se 1 (by rfl) ⟨2292092, by rfl⟩ : syracuseStep 3056123 = 4584185) B4584185
theorem B55747075 : Blo 1809606 55747075 := bstep (se 1 (by rfl) ⟨41810306, by rfl⟩ : syracuseStep 55747075 = 83620613) B83620613
theorem B6873619 : Blo 1809606 6873619 := bstep (se 1 (by rfl) ⟨5155214, by rfl⟩ : syracuseStep 6873619 = 10310429) B10310429
theorem B1811007 : Blo 1809606 1811007 := bstep (se 1 (by rfl) ⟨1358255, by rfl⟩ : syracuseStep 1811007 = 2716511) B2716511
theorem B1811015 : Blo 1809606 1811015 := bstep (se 1 (by rfl) ⟨1358261, by rfl⟩ : syracuseStep 1811015 = 2716523) B2716523
theorem B11600567 : Blo 1809606 11600567 := bstep (se 1 (by rfl) ⟨8700425, by rfl⟩ : syracuseStep 11600567 = 17400851) B17400851
theorem B1811167 : Blo 1809606 1811167 := bstep (se 1 (by rfl) ⟨1358375, by rfl⟩ : syracuseStep 1811167 = 2716751) B2716751
theorem B4072211 : Blo 1809606 4072211 := bstep (se 1 (by rfl) ⟨3054158, by rfl⟩ : syracuseStep 4072211 = 6108317) B6108317
theorem B1811247 : Blo 1809606 1811247 := bstep (se 1 (by rfl) ⟨1358435, by rfl⟩ : syracuseStep 1811247 = 2716871) B2716871
theorem B1811355 : Blo 1809606 1811355 := bstep (se 1 (by rfl) ⟨1358516, by rfl⟩ : syracuseStep 1811355 = 2717033) B2717033
theorem B3056555 : Blo 1809606 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B1811407 : Blo 1809606 1811407 := bstep (se 1 (by rfl) ⟨1358555, by rfl⟩ : syracuseStep 1811407 = 2717111) B2717111
theorem B17408999 : Blo 1809606 17408999 := bstep (se 1 (by rfl) ⟨13056749, by rfl⟩ : syracuseStep 17408999 = 26113499) B26113499
theorem B1811431 : Blo 1809606 1811431 := bstep (se 1 (by rfl) ⟨1358573, by rfl⟩ : syracuseStep 1811431 = 2717147) B2717147
theorem B30950423 : Blo 1809606 30950423 := bstep (se 1 (by rfl) ⟨23212817, by rfl⟩ : syracuseStep 30950423 = 46425635) B46425635
theorem B15467557 : Blo 1809606 15467557 := bstep (se 4 (by rfl) ⟨1450083, by rfl⟩ : syracuseStep 15467557 = 2900167) B2900167
theorem B4072571 : Blo 1809606 4072571 := bstep (se 1 (by rfl) ⟨3054428, by rfl⟩ : syracuseStep 4072571 = 6108857) B6108857
theorem B4129991 : Blo 1809606 4129991 := bstep (se 1 (by rfl) ⟨3097493, by rfl⟩ : syracuseStep 4129991 = 6194987) B6194987
theorem B14681321 : Blo 1809606 14681321 := bstep (se 2 (by rfl) ⟨5505495, by rfl⟩ : syracuseStep 14681321 = 11010991) B11010991
theorem B10314985 : Blo 1809606 10314985 := bstep (se 2 (by rfl) ⟨3868119, by rfl⟩ : syracuseStep 10314985 = 7736239) B7736239
theorem B17646835 : Blo 1809606 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B4072697 : Blo 1809606 4072697 := bstep (se 2 (by rfl) ⟨1527261, by rfl⟩ : syracuseStep 4072697 = 3054523) B3054523
theorem B4072841 : Blo 1809606 4072841 := bstep (se 2 (by rfl) ⟨1527315, by rfl⟩ : syracuseStep 4072841 = 3054631) B3054631
theorem B4072967 : Blo 1809606 4072967 := bstep (se 1 (by rfl) ⟨3054725, by rfl⟩ : syracuseStep 4072967 = 6109451) B6109451
theorem B4073147 : Blo 1809606 4073147 := bstep (se 1 (by rfl) ⟨3054860, by rfl⟩ : syracuseStep 4073147 = 6109721) B6109721
theorem B4073273 : Blo 1809606 4073273 := bstep (se 2 (by rfl) ⟨1527477, by rfl⟩ : syracuseStep 4073273 = 3054955) B3054955
theorem B148645709 : Blo 1809606 148645709 := bstep (se 3 (by rfl) ⟨27871070, by rfl⟩ : syracuseStep 148645709 = 55742141) B55742141
theorem B17409923 : Blo 1809606 17409923 := bstep (se 1 (by rfl) ⟨13057442, by rfl⟩ : syracuseStep 17409923 = 26114885) B26114885
theorem B6113231 : Blo 1809606 6113231 := bstep (se 1 (by rfl) ⟨4584923, by rfl⟩ : syracuseStep 6113231 = 9169847) B9169847
theorem B200869895 : Blo 1809606 200869895 := bstep (se 1 (by rfl) ⟨150652421, by rfl⟩ : syracuseStep 200869895 = 301304843) B301304843
theorem B4581481 : Blo 1809606 4581481 := bstep (se 2 (by rfl) ⟨1718055, by rfl⟩ : syracuseStep 4581481 = 3436111) B3436111
theorem B19573103 : Blo 1809606 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B4073903 : Blo 1809606 4073903 := bstep (se 1 (by rfl) ⟨3055427, by rfl⟩ : syracuseStep 4073903 = 6110855) B6110855
theorem B13044179 : Blo 1809606 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B4073939 : Blo 1809606 4073939 := bstep (se 1 (by rfl) ⟨3055454, by rfl⟩ : syracuseStep 4073939 = 6110909) B6110909
theorem B10316261 : Blo 1809606 10316261 := bstep (se 4 (by rfl) ⟨967149, by rfl⟩ : syracuseStep 10316261 = 1934299) B1934299
theorem B4074047 : Blo 1809606 4074047 := bstep (se 1 (by rfl) ⟨3055535, by rfl⟩ : syracuseStep 4074047 = 6111071) B6111071
theorem B4581967 : Blo 1809606 4581967 := bstep (se 1 (by rfl) ⟨3436475, by rfl⟩ : syracuseStep 4581967 = 6872951) B6872951
theorem B4074155 : Blo 1809606 4074155 := bstep (se 1 (by rfl) ⟨3055616, by rfl⟩ : syracuseStep 4074155 = 6111233) B6111233
theorem B2714447 : Blo 1809606 2714447 := bstep (se 1 (by rfl) ⟨2035835, by rfl⟩ : syracuseStep 2714447 = 4071671) B4071671
theorem B17206337 : Blo 1809606 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B15674435 : Blo 1809606 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B4074695 : Blo 1809606 4074695 := bstep (se 1 (by rfl) ⟨3056021, by rfl⟩ : syracuseStep 4074695 = 6112043) B6112043
theorem B4582615 : Blo 1809606 4582615 := bstep (se 1 (by rfl) ⟨3436961, by rfl⟩ : syracuseStep 4582615 = 6873923) B6873923
theorem B2714843 : Blo 1809606 2714843 := bstep (se 1 (by rfl) ⟨2036132, by rfl⟩ : syracuseStep 2714843 = 4072265) B4072265
theorem B6876535 : Blo 1809606 6876535 := bstep (se 1 (by rfl) ⟨5157401, by rfl⟩ : syracuseStep 6876535 = 10314803) B10314803
theorem B4074875 : Blo 1809606 4074875 := bstep (se 1 (by rfl) ⟨3056156, by rfl⟩ : syracuseStep 4074875 = 6112313) B6112313
theorem B2715017 : Blo 1809606 2715017 := bstep (se 2 (by rfl) ⟨1018131, by rfl⟩ : syracuseStep 2715017 = 2036263) B2036263
theorem B9162233 : Blo 1809606 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B4075001 : Blo 1809606 4075001 := bstep (se 2 (by rfl) ⟨1528125, by rfl⟩ : syracuseStep 4075001 = 3056251) B3056251
theorem B4582919 : Blo 1809606 4582919 := bstep (se 1 (by rfl) ⟨3437189, by rfl⟩ : syracuseStep 4582919 = 6874379) B6874379
theorem B4075091 : Blo 1809606 4075091 := bstep (se 1 (by rfl) ⟨3056318, by rfl⟩ : syracuseStep 4075091 = 6112637) B6112637
theorem B6966893 : Blo 1809606 6966893 := bstep (se 3 (by rfl) ⟨1306292, by rfl⟩ : syracuseStep 6966893 = 2612585) B2612585
theorem B15470291 : Blo 1809606 15470291 := bstep (se 1 (by rfl) ⟨11602718, by rfl⟩ : syracuseStep 15470291 = 23205437) B23205437
theorem B2715371 : Blo 1809606 2715371 := bstep (se 1 (by rfl) ⟨2036528, by rfl⟩ : syracuseStep 2715371 = 4073057) B4073057
theorem B4075271 : Blo 1809606 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B9162557 : Blo 1809606 9162557 := bstep (se 3 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 9162557 = 3435959) B3435959
theorem B19582877 : Blo 1809606 19582877 := bstep (se 3 (by rfl) ⟨3671789, by rfl⟩ : syracuseStep 19582877 = 7343579) B7343579
theorem B2715599 : Blo 1809606 2715599 := bstep (se 1 (by rfl) ⟨2036699, by rfl⟩ : syracuseStep 2715599 = 4073399) B4073399
theorem B4583375 : Blo 1809606 4583375 := bstep (se 1 (by rfl) ⟨3437531, by rfl⟩ : syracuseStep 4583375 = 6875063) B6875063
theorem B11006123 : Blo 1809606 11006123 := bstep (se 1 (by rfl) ⟨8254592, by rfl⟩ : syracuseStep 11006123 = 16509185) B16509185
theorem B4894985 : Blo 1809606 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B2715995 : Blo 1809606 2715995 := bstep (se 1 (by rfl) ⟨2036996, by rfl⟩ : syracuseStep 2715995 = 4073993) B4073993
theorem B4075883 : Blo 1809606 4075883 := bstep (se 1 (by rfl) ⟨3056912, by rfl⟩ : syracuseStep 4075883 = 6113825) B6113825
theorem B4583891 : Blo 1809606 4583891 := bstep (se 1 (by rfl) ⟨3437918, by rfl⟩ : syracuseStep 4583891 = 6875837) B6875837
theorem B4895201 : Blo 1809606 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B4076027 : Blo 1809606 4076027 := bstep (se 1 (by rfl) ⟨3057020, by rfl⟩ : syracuseStep 4076027 = 6114041) B6114041
theorem B2716223 : Blo 1809606 2716223 := bstep (se 1 (by rfl) ⟨2037167, by rfl⟩ : syracuseStep 2716223 = 4074335) B4074335
theorem B3437129 : Blo 1809606 3437129 := bstep (se 2 (by rfl) ⟨1288923, by rfl⟩ : syracuseStep 3437129 = 2577847) B2577847
theorem B2290351 : Blo 1809606 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B6107831 : Blo 1809606 6107831 := bstep (se 1 (by rfl) ⟨4580873, by rfl⟩ : syracuseStep 6107831 = 9161747) B9161747
theorem B2716343 : Blo 1809606 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B10449607 : Blo 1809606 10449607 := bstep (se 1 (by rfl) ⟨7837205, by rfl⟩ : syracuseStep 10449607 = 15674411) B15674411
theorem B4707227 : Blo 1809606 4707227 := bstep (se 1 (by rfl) ⟨3530420, by rfl⟩ : syracuseStep 4707227 = 7060841) B7060841
theorem B2716571 : Blo 1809606 2716571 := bstep (se 1 (by rfl) ⟨2037428, by rfl⟩ : syracuseStep 2716571 = 4074857) B4074857
theorem B4584347 : Blo 1809606 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B7943159 : Blo 1809606 7943159 := bstep (se 1 (by rfl) ⟨5957369, by rfl⟩ : syracuseStep 7943159 = 11914739) B11914739
theorem B14677139 : Blo 1809606 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B6526099 : Blo 1809606 6526099 := bstep (se 1 (by rfl) ⟨4894574, by rfl⟩ : syracuseStep 6526099 = 9789149) B9789149
theorem B3921095 : Blo 1809606 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B4895959 : Blo 1809606 4895959 := bstep (se 1 (by rfl) ⟨3671969, by rfl⟩ : syracuseStep 4895959 = 7343939) B7343939
theorem B2716967 : Blo 1809606 2716967 := bstep (se 1 (by rfl) ⟨2037725, by rfl⟩ : syracuseStep 2716967 = 4075451) B4075451
theorem B33486169 : Blo 1809606 33486169 := bstep (se 2 (by rfl) ⟨12557313, by rfl⟩ : syracuseStep 33486169 = 25114627) B25114627
theorem B5657951 : Blo 1809606 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B2717051 : Blo 1809606 2717051 := bstep (se 1 (by rfl) ⟨2037788, by rfl⟩ : syracuseStep 2717051 = 4075577) B4075577
theorem B13055365 : Blo 1809606 13055365 := bstep (se 4 (by rfl) ⟨1223940, by rfl⟩ : syracuseStep 13055365 = 2447881) B2447881
theorem B2938361 : Blo 1809606 2938361 := bstep (se 2 (by rfl) ⟨1101885, by rfl⟩ : syracuseStep 2938361 = 2203771) B2203771
theorem B2717177 : Blo 1809606 2717177 := bstep (se 2 (by rfl) ⟨1018941, by rfl⟩ : syracuseStep 2717177 = 2037883) B2037883
theorem B26818087 : Blo 1809606 26818087 := bstep (se 1 (by rfl) ⟨20113565, by rfl⟩ : syracuseStep 26818087 = 40227131) B40227131
theorem B2037343 : Blo 1809606 2037343 := bstep (se 1 (by rfl) ⟨1528007, by rfl⟩ : syracuseStep 2037343 = 3056015) B3056015
theorem B2717279 : Blo 1809606 2717279 := bstep (se 1 (by rfl) ⟨2037959, by rfl⟩ : syracuseStep 2717279 = 4075919) B4075919
theorem B4896413 : Blo 1809606 4896413 := bstep (se 3 (by rfl) ⟨918077, by rfl⟩ : syracuseStep 4896413 = 1836155) B1836155
theorem B4585481 : Blo 1809606 4585481 := bstep (se 2 (by rfl) ⟨1719555, by rfl⟩ : syracuseStep 4585481 = 3439111) B3439111
theorem B11597903 : Blo 1809606 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B6871175 : Blo 1809606 6871175 := bstep (se 1 (by rfl) ⟨5153381, by rfl⟩ : syracuseStep 6871175 = 10306763) B10306763
theorem B8821001 : Blo 1809606 8821001 := bstep (se 2 (by rfl) ⟨3307875, by rfl⟩ : syracuseStep 8821001 = 6615751) B6615751
theorem B9296153 : Blo 1809606 9296153 := bstep (se 2 (by rfl) ⟨3486057, by rfl⟩ : syracuseStep 9296153 = 6972115) B6972115
theorem B6871463 : Blo 1809606 6871463 := bstep (se 1 (by rfl) ⟨5153597, by rfl⟩ : syracuseStep 6871463 = 10307195) B10307195
theorem B3439073 : Blo 1809606 3439073 := bstep (se 2 (by rfl) ⟨1289652, by rfl⟩ : syracuseStep 3439073 = 2579305) B2579305
theorem B13752827 : Blo 1809606 13752827 := bstep (se 1 (by rfl) ⟨10314620, by rfl⟩ : syracuseStep 13752827 = 20629241) B20629241
theorem B11606591 : Blo 1809606 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B2292295 : Blo 1809606 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B6109775 : Blo 1809606 6109775 := bstep (se 1 (by rfl) ⟨4582331, by rfl⟩ : syracuseStep 6109775 = 9164663) B9164663
theorem B19577477 : Blo 1809606 19577477 := bstep (se 4 (by rfl) ⟨1835388, by rfl⟩ : syracuseStep 19577477 = 3670777) B3670777
theorem B33471251 : Blo 1809606 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B9165635 : Blo 1809606 9165635 := bstep (se 1 (by rfl) ⟨6874226, by rfl⟩ : syracuseStep 9165635 = 13748453) B13748453
theorem B3054415 : Blo 1809606 3054415 := bstep (se 1 (by rfl) ⟨2290811, by rfl⟩ : syracuseStep 3054415 = 4581623) B4581623
theorem B14687095 : Blo 1809606 14687095 := bstep (se 1 (by rfl) ⟨11015321, by rfl⟩ : syracuseStep 14687095 = 22030643) B22030643
theorem B13745051 : Blo 1809606 13745051 := bstep (se 1 (by rfl) ⟨10308788, by rfl⟩ : syracuseStep 13745051 = 20617577) B20617577
theorem B6871979 : Blo 1809606 6871979 := bstep (se 1 (by rfl) ⟨5153984, by rfl⟩ : syracuseStep 6871979 = 10307969) B10307969
theorem B6527915 : Blo 1809606 6527915 := bstep (se 1 (by rfl) ⟨4895936, by rfl⟩ : syracuseStep 6527915 = 9791873) B9791873
theorem B5798899 : Blo 1809606 5798899 := bstep (se 1 (by rfl) ⟨4349174, by rfl⟩ : syracuseStep 5798899 = 8698349) B8698349
theorem B3865591 : Blo 1809606 3865591 := bstep (se 1 (by rfl) ⟨2899193, by rfl⟩ : syracuseStep 3865591 = 5798387) B5798387
theorem B11607229 : Blo 1809606 11607229 := bstep (se 3 (by rfl) ⟨2176355, by rfl⟩ : syracuseStep 11607229 = 4352711) B4352711
theorem B1809695 : Blo 1809606 1809695 := bstep (se 1 (by rfl) ⟨1357271, by rfl⟩ : syracuseStep 1809695 = 2714543) B2714543
theorem B10313027 : Blo 1809606 10313027 := bstep (se 1 (by rfl) ⟨7734770, by rfl⟩ : syracuseStep 10313027 = 15469541) B15469541
theorem B1809755 : Blo 1809606 1809755 := bstep (se 1 (by rfl) ⟨1357316, by rfl⟩ : syracuseStep 1809755 = 2714633) B2714633
theorem B1809775 : Blo 1809606 1809775 := bstep (se 1 (by rfl) ⟨1357331, by rfl⟩ : syracuseStep 1809775 = 2714663) B2714663
theorem B1932655 : Blo 1809606 1932655 := bstep (se 1 (by rfl) ⟨1449491, by rfl⟩ : syracuseStep 1932655 = 2898983) B2898983
theorem B4349321 : Blo 1809606 4349321 := bstep (se 2 (by rfl) ⟨1630995, by rfl⟩ : syracuseStep 4349321 = 3261991) B3261991
theorem B1809831 : Blo 1809606 1809831 := bstep (se 1 (by rfl) ⟨1357373, by rfl⟩ : syracuseStep 1809831 = 2714747) B2714747
theorem B3055097 : Blo 1809606 3055097 := bstep (se 2 (by rfl) ⟨1145661, by rfl⟩ : syracuseStep 3055097 = 2291323) B2291323
theorem B1809915 : Blo 1809606 1809915 := bstep (se 1 (by rfl) ⟨1357436, by rfl⟩ : syracuseStep 1809915 = 2714873) B2714873
theorem B13049369 : Blo 1809606 13049369 := bstep (se 2 (by rfl) ⟨4893513, by rfl⟩ : syracuseStep 13049369 = 9787027) B9787027
theorem B1809983 : Blo 1809606 1809983 := bstep (se 1 (by rfl) ⟨1357487, by rfl⟩ : syracuseStep 1809983 = 2714975) B2714975
theorem B1809991 : Blo 1809606 1809991 := bstep (se 1 (by rfl) ⟨1357493, by rfl⟩ : syracuseStep 1809991 = 2714987) B2714987
theorem B9166445 : Blo 1809606 9166445 := bstep (se 3 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 9166445 = 3437417) B3437417
theorem B16514705 : Blo 1809606 16514705 := bstep (se 2 (by rfl) ⟨6193014, by rfl⟩ : syracuseStep 16514705 = 12386029) B12386029
theorem B1810143 : Blo 1809606 1810143 := bstep (se 1 (by rfl) ⟨1357607, by rfl⟩ : syracuseStep 1810143 = 2715215) B2715215
theorem B3055367 : Blo 1809606 3055367 := bstep (se 1 (by rfl) ⟨2291525, by rfl⟩ : syracuseStep 3055367 = 4583051) B4583051
theorem B29376263 : Blo 1809606 29376263 := bstep (se 1 (by rfl) ⟨22032197, by rfl⟩ : syracuseStep 29376263 = 44064395) B44064395
theorem B6111017 : Blo 1809606 6111017 := bstep (se 2 (by rfl) ⟨2291631, by rfl⟩ : syracuseStep 6111017 = 4583263) B4583263
theorem B1810223 : Blo 1809606 1810223 := bstep (se 1 (by rfl) ⟨1357667, by rfl⟩ : syracuseStep 1810223 = 2715335) B2715335
theorem B1933103 : Blo 1809606 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B1810331 : Blo 1809606 1810331 := bstep (se 1 (by rfl) ⟨1357748, by rfl⟩ : syracuseStep 1810331 = 2715497) B2715497
theorem B1810383 : Blo 1809606 1810383 := bstep (se 1 (by rfl) ⟨1357787, by rfl⟩ : syracuseStep 1810383 = 2715575) B2715575
theorem B1810407 : Blo 1809606 1810407 := bstep (se 1 (by rfl) ⟨1357805, by rfl⟩ : syracuseStep 1810407 = 2715611) B2715611
theorem B1810663 : Blo 1809606 1810663 := bstep (se 1 (by rfl) ⟨1357997, by rfl⟩ : syracuseStep 1810663 = 2715995) B2715995
theorem B26460431 : Blo 1809606 26460431 := bstep (se 1 (by rfl) ⟨19845323, by rfl⟩ : syracuseStep 26460431 = 39690647) B39690647
theorem B3055927 : Blo 1809606 3055927 := bstep (se 1 (by rfl) ⟨2291945, by rfl⟩ : syracuseStep 3055927 = 4583891) B4583891
theorem B1810815 : Blo 1809606 1810815 := bstep (se 1 (by rfl) ⟨1358111, by rfl⟩ : syracuseStep 1810815 = 2716223) B2716223
theorem B4071887 : Blo 1809606 4071887 := bstep (se 1 (by rfl) ⟨3053915, by rfl⟩ : syracuseStep 4071887 = 6107831) B6107831
theorem B7733711 : Blo 1809606 7733711 := bstep (se 1 (by rfl) ⟨5800283, by rfl⟩ : syracuseStep 7733711 = 11600567) B11600567
theorem B1810895 : Blo 1809606 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B3138151 : Blo 1809606 3138151 := bstep (se 1 (by rfl) ⟨2353613, by rfl⟩ : syracuseStep 3138151 = 4707227) B4707227
theorem B1811047 : Blo 1809606 1811047 := bstep (se 1 (by rfl) ⟨1358285, by rfl⟩ : syracuseStep 1811047 = 2716571) B2716571
theorem B3056231 : Blo 1809606 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B3056393 : Blo 1809606 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B2753327 : Blo 1809606 2753327 := bstep (se 1 (by rfl) ⟨2064995, by rfl⟩ : syracuseStep 2753327 = 4129991) B4129991
theorem B1811311 : Blo 1809606 1811311 := bstep (se 1 (by rfl) ⟨1358483, by rfl⟩ : syracuseStep 1811311 = 2716967) B2716967
theorem B1811367 : Blo 1809606 1811367 := bstep (se 1 (by rfl) ⟨1358525, by rfl⟩ : syracuseStep 1811367 = 2717051) B2717051
theorem B1811451 : Blo 1809606 1811451 := bstep (se 1 (by rfl) ⟨1358588, by rfl⟩ : syracuseStep 1811451 = 2717177) B2717177
theorem B1811519 : Blo 1809606 1811519 := bstep (se 1 (by rfl) ⟨1358639, by rfl⟩ : syracuseStep 1811519 = 2717279) B2717279
theorem B4072553 : Blo 1809606 4072553 := bstep (se 2 (by rfl) ⟨1527207, by rfl⟩ : syracuseStep 4072553 = 3054415) B3054415
theorem B34784477 : Blo 1809606 34784477 := bstep (se 3 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 34784477 = 13044179) B13044179
theorem B5154121 : Blo 1809606 5154121 := bstep (se 2 (by rfl) ⟨1932795, by rfl⟩ : syracuseStep 5154121 = 3865591) B3865591
theorem B3056987 : Blo 1809606 3056987 := bstep (se 1 (by rfl) ⟨2292740, by rfl⟩ : syracuseStep 3056987 = 4585481) B4585481
theorem B4580783 : Blo 1809606 4580783 := bstep (se 1 (by rfl) ⟨3435587, by rfl⟩ : syracuseStep 4580783 = 6871175) B6871175
theorem B8701465 : Blo 1809606 8701465 := bstep (se 2 (by rfl) ⟨3263049, by rfl⟩ : syracuseStep 8701465 = 6526099) B6526099
theorem B15476305 : Blo 1809606 15476305 := bstep (se 2 (by rfl) ⟨5803614, by rfl⟩ : syracuseStep 15476305 = 11607229) B11607229
theorem B4580975 : Blo 1809606 4580975 := bstep (se 1 (by rfl) ⟨3435731, by rfl⟩ : syracuseStep 4580975 = 6871463) B6871463
theorem B23529113 : Blo 1809606 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B9168551 : Blo 1809606 9168551 := bstep (se 1 (by rfl) ⟨6876413, by rfl⟩ : syracuseStep 9168551 = 13752827) B13752827
theorem B4073183 : Blo 1809606 4073183 := bstep (se 1 (by rfl) ⟨3054887, by rfl⟩ : syracuseStep 4073183 = 6109775) B6109775
theorem B13051651 : Blo 1809606 13051651 := bstep (se 1 (by rfl) ⟨9788738, by rfl⟩ : syracuseStep 13051651 = 19577477) B19577477
theorem B44648225 : Blo 1809606 44648225 := bstep (se 2 (by rfl) ⟨16743084, by rfl⟩ : syracuseStep 44648225 = 33486169) B33486169
theorem B9168713 : Blo 1809606 9168713 := bstep (se 2 (by rfl) ⟨3438267, by rfl⟩ : syracuseStep 9168713 = 6876535) B6876535
theorem B4581319 : Blo 1809606 4581319 := bstep (se 1 (by rfl) ⟨3435989, by rfl⟩ : syracuseStep 4581319 = 6871979) B6871979
theorem B4351943 : Blo 1809606 4351943 := bstep (se 1 (by rfl) ⟨3263957, by rfl⟩ : syracuseStep 4351943 = 6527915) B6527915
theorem B11470891 : Blo 1809606 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B5154941 : Blo 1809606 5154941 := bstep (se 3 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 5154941 = 1933103) B1933103
theorem B6875351 : Blo 1809606 6875351 := bstep (se 1 (by rfl) ⟨5156513, by rfl⟩ : syracuseStep 6875351 = 10313027) B10313027
theorem B4074011 : Blo 1809606 4074011 := bstep (se 1 (by rfl) ⟨3055508, by rfl⟩ : syracuseStep 4074011 = 6111017) B6111017
theorem B2714423 : Blo 1809606 2714423 := bstep (se 1 (by rfl) ⟨2035817, by rfl⟩ : syracuseStep 2714423 = 4071635) B4071635
theorem B2714459 : Blo 1809606 2714459 := bstep (se 1 (by rfl) ⟨2035844, by rfl⟩ : syracuseStep 2714459 = 4071689) B4071689
theorem B3263323 : Blo 1809606 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B2714603 : Blo 1809606 2714603 := bstep (se 1 (by rfl) ⟨2035952, by rfl⟩ : syracuseStep 2714603 = 4071905) B4071905
theorem B2714807 : Blo 1809606 2714807 := bstep (se 1 (by rfl) ⟨2036105, by rfl⟩ : syracuseStep 2714807 = 4072211) B4072211
theorem B10456253 : Blo 1809606 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B5295439 : Blo 1809606 5295439 := bstep (se 1 (by rfl) ⟨3971579, by rfl⟩ : syracuseStep 5295439 = 7943159) B7943159
theorem B74329433 : Blo 1809606 74329433 := bstep (se 2 (by rfl) ⟨27873537, by rfl⟩ : syracuseStep 74329433 = 55747075) B55747075
theorem B2715047 : Blo 1809606 2715047 := bstep (se 1 (by rfl) ⟨2036285, by rfl⟩ : syracuseStep 2715047 = 4072571) B4072571
theorem B9784759 : Blo 1809606 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B2715131 : Blo 1809606 2715131 := bstep (se 1 (by rfl) ⟨2036348, by rfl⟩ : syracuseStep 2715131 = 4072697) B4072697
theorem B2715227 : Blo 1809606 2715227 := bstep (se 1 (by rfl) ⟨2036420, by rfl⟩ : syracuseStep 2715227 = 4072841) B4072841
theorem B52194941 : Blo 1809606 52194941 := bstep (se 3 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 52194941 = 19573103) B19573103
theorem B2715311 : Blo 1809606 2715311 := bstep (se 1 (by rfl) ⟨2036483, by rfl⟩ : syracuseStep 2715311 = 4072967) B4072967
theorem B3264275 : Blo 1809606 3264275 := bstep (se 1 (by rfl) ⟨2448206, by rfl⟩ : syracuseStep 3264275 = 4896413) B4896413
theorem B2715431 : Blo 1809606 2715431 := bstep (se 1 (by rfl) ⟨2036573, by rfl⟩ : syracuseStep 2715431 = 4073147) B4073147
theorem B19582793 : Blo 1809606 19582793 := bstep (se 2 (by rfl) ⟨7343547, by rfl⟩ : syracuseStep 19582793 = 14687095) B14687095
theorem B2715515 : Blo 1809606 2715515 := bstep (se 1 (by rfl) ⟨2036636, by rfl⟩ : syracuseStep 2715515 = 4073273) B4073273
theorem B13053869 : Blo 1809606 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B4075487 : Blo 1809606 4075487 := bstep (se 1 (by rfl) ⟨3056615, by rfl⟩ : syracuseStep 4075487 = 6113231) B6113231
theorem B7835629 : Blo 1809606 7835629 := bstep (se 3 (by rfl) ⟨1469180, by rfl⟩ : syracuseStep 7835629 = 2938361) B2938361
theorem B20623409 : Blo 1809606 20623409 := bstep (se 2 (by rfl) ⟨7733778, by rfl⟩ : syracuseStep 20623409 = 15467557) B15467557
theorem B6197435 : Blo 1809606 6197435 := bstep (se 1 (by rfl) ⟨4648076, by rfl⟩ : syracuseStep 6197435 = 9296153) B9296153
theorem B2715935 : Blo 1809606 2715935 := bstep (se 1 (by rfl) ⟨2036951, by rfl⟩ : syracuseStep 2715935 = 4073903) B4073903
theorem B2715959 : Blo 1809606 2715959 := bstep (se 1 (by rfl) ⟨2036969, by rfl⟩ : syracuseStep 2715959 = 4073939) B4073939
theorem B6877507 : Blo 1809606 6877507 := bstep (se 1 (by rfl) ⟨5158130, by rfl⟩ : syracuseStep 6877507 = 10316261) B10316261
theorem B2716031 : Blo 1809606 2716031 := bstep (se 1 (by rfl) ⟨2037023, by rfl⟩ : syracuseStep 2716031 = 4074047) B4074047
theorem B7737727 : Blo 1809606 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B2716103 : Blo 1809606 2716103 := bstep (se 1 (by rfl) ⟨2037077, by rfl⟩ : syracuseStep 2716103 = 4074155) B4074155
theorem B19575269 : Blo 1809606 19575269 := bstep (se 4 (by rfl) ⟨1835181, by rfl⟩ : syracuseStep 19575269 = 3670363) B3670363
theorem B2576873 : Blo 1809606 2576873 := bstep (se 2 (by rfl) ⟨966327, by rfl⟩ : syracuseStep 2576873 = 1932655) B1932655
theorem B9163367 : Blo 1809606 9163367 := bstep (se 1 (by rfl) ⟨6872525, by rfl⟩ : syracuseStep 9163367 = 13745051) B13745051
theorem B10449623 : Blo 1809606 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B2716457 : Blo 1809606 2716457 := bstep (se 2 (by rfl) ⟨1018671, by rfl⟩ : syracuseStep 2716457 = 2037343) B2037343
theorem B2716463 : Blo 1809606 2716463 := bstep (se 1 (by rfl) ⟨2037347, by rfl⟩ : syracuseStep 2716463 = 4074695) B4074695
theorem B2716583 : Blo 1809606 2716583 := bstep (se 1 (by rfl) ⟨2037437, by rfl⟩ : syracuseStep 2716583 = 4074875) B4074875
theorem B6108155 : Blo 1809606 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B2036731 : Blo 1809606 2036731 := bstep (se 1 (by rfl) ⟨1527548, by rfl⟩ : syracuseStep 2036731 = 3055097) B3055097
theorem B2716667 : Blo 1809606 2716667 := bstep (se 1 (by rfl) ⟨2037500, by rfl⟩ : syracuseStep 2716667 = 4075001) B4075001
theorem B2716727 : Blo 1809606 2716727 := bstep (se 1 (by rfl) ⟨2037545, by rfl⟩ : syracuseStep 2716727 = 4075091) B4075091
theorem B2036911 : Blo 1809606 2036911 := bstep (se 1 (by rfl) ⟨1527683, by rfl⟩ : syracuseStep 2036911 = 3055367) B3055367
theorem B2716847 : Blo 1809606 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B19584175 : Blo 1809606 19584175 := bstep (se 1 (by rfl) ⟨14688131, by rfl⟩ : syracuseStep 19584175 = 29376263) B29376263
theorem B6108371 : Blo 1809606 6108371 := bstep (se 1 (by rfl) ⟨4581278, by rfl⟩ : syracuseStep 6108371 = 9162557) B9162557
theorem B13055251 : Blo 1809606 13055251 := bstep (se 1 (by rfl) ⟨9791438, by rfl⟩ : syracuseStep 13055251 = 19582877) B19582877
theorem B6108641 : Blo 1809606 6108641 := bstep (se 2 (by rfl) ⟨2290740, by rfl⟩ : syracuseStep 6108641 = 4581481) B4581481
theorem B10311137 : Blo 1809606 10311137 := bstep (se 2 (by rfl) ⟨3866676, by rfl⟩ : syracuseStep 10311137 = 7733353) B7733353
theorem B2717255 : Blo 1809606 2717255 := bstep (se 1 (by rfl) ⟨2037941, by rfl⟩ : syracuseStep 2717255 = 4075883) B4075883
theorem B2037415 : Blo 1809606 2037415 := bstep (se 1 (by rfl) ⟨1528061, by rfl⟩ : syracuseStep 2037415 = 3056123) B3056123
theorem B2717351 : Blo 1809606 2717351 := bstep (se 1 (by rfl) ⟨2038013, by rfl⟩ : syracuseStep 2717351 = 4076027) B4076027
theorem B2291419 : Blo 1809606 2291419 := bstep (se 1 (by rfl) ⟨1718564, by rfl⟩ : syracuseStep 2291419 = 3437129) B3437129
theorem B29349661 : Blo 1809606 29349661 := bstep (se 3 (by rfl) ⟨5503061, by rfl⟩ : syracuseStep 29349661 = 11006123) B11006123
theorem B2037703 : Blo 1809606 2037703 := bstep (se 1 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 2037703 = 3056555) B3056555
theorem B11605999 : Blo 1809606 11605999 := bstep (se 1 (by rfl) ⟨8704499, by rfl⟩ : syracuseStep 11605999 = 17408999) B17408999
theorem B20633615 : Blo 1809606 20633615 := bstep (se 1 (by rfl) ⟨15475211, by rfl⟩ : syracuseStep 20633615 = 30950423) B30950423
theorem B9164825 : Blo 1809606 9164825 := bstep (se 2 (by rfl) ⟨3436809, by rfl⟩ : syracuseStep 9164825 = 6873619) B6873619
theorem B6109289 : Blo 1809606 6109289 := bstep (se 2 (by rfl) ⟨2290983, by rfl⟩ : syracuseStep 6109289 = 4581967) B4581967
theorem B9787547 : Blo 1809606 9787547 := bstep (se 1 (by rfl) ⟨7340660, by rfl⟩ : syracuseStep 9787547 = 14681321) B14681321
theorem B3053801 : Blo 1809606 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B15087869 : Blo 1809606 15087869 := bstep (se 3 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 15087869 = 5657951) B5657951
theorem B13932809 : Blo 1809606 13932809 := bstep (se 2 (by rfl) ⟨5224803, by rfl⟩ : syracuseStep 13932809 = 10449607) B10449607
theorem B99097139 : Blo 1809606 99097139 := bstep (se 1 (by rfl) ⟨74322854, by rfl⟩ : syracuseStep 99097139 = 148645709) B148645709
theorem B11606615 : Blo 1809606 11606615 := bstep (se 1 (by rfl) ⟨8704961, by rfl⟩ : syracuseStep 11606615 = 17409923) B17409923
theorem B7731865 : Blo 1809606 7731865 := bstep (se 2 (by rfl) ⟨2899449, by rfl⟩ : syracuseStep 7731865 = 5798899) B5798899
theorem B133913263 : Blo 1809606 133913263 := bstep (se 1 (by rfl) ⟨100434947, by rfl⟩ : syracuseStep 133913263 = 200869895) B200869895
theorem B7731935 : Blo 1809606 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B5880667 : Blo 1809606 5880667 := bstep (se 1 (by rfl) ⟨4410500, by rfl⟩ : syracuseStep 5880667 = 8821001) B8821001
theorem B6110153 : Blo 1809606 6110153 := bstep (se 2 (by rfl) ⟨2291307, by rfl⟩ : syracuseStep 6110153 = 4582615) B4582615
theorem B6527945 : Blo 1809606 6527945 := bstep (se 2 (by rfl) ⟨2447979, by rfl⟩ : syracuseStep 6527945 = 4895959) B4895959
theorem B13753313 : Blo 1809606 13753313 := bstep (se 2 (by rfl) ⟨5157492, by rfl⟩ : syracuseStep 13753313 = 10314985) B10314985
theorem B2292715 : Blo 1809606 2292715 := bstep (se 1 (by rfl) ⟨1719536, by rfl⟩ : syracuseStep 2292715 = 3439073) B3439073
theorem B17407153 : Blo 1809606 17407153 := bstep (se 2 (by rfl) ⟨6527682, by rfl⟩ : syracuseStep 17407153 = 13055365) B13055365
theorem B22314167 : Blo 1809606 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B6110423 : Blo 1809606 6110423 := bstep (se 1 (by rfl) ⟨4582817, by rfl⟩ : syracuseStep 6110423 = 9165635) B9165635
theorem B1809631 : Blo 1809606 1809631 := bstep (se 1 (by rfl) ⟨1357223, by rfl⟩ : syracuseStep 1809631 = 2714447) B2714447
theorem B35757449 : Blo 1809606 35757449 := bstep (se 2 (by rfl) ⟨13409043, by rfl⟩ : syracuseStep 35757449 = 26818087) B26818087
theorem B1809895 : Blo 1809606 1809895 := bstep (se 1 (by rfl) ⟨1357421, by rfl⟩ : syracuseStep 1809895 = 2714843) B2714843
theorem B1810011 : Blo 1809606 1810011 := bstep (se 1 (by rfl) ⟨1357508, by rfl⟩ : syracuseStep 1810011 = 2715017) B2715017
theorem B2899547 : Blo 1809606 2899547 := bstep (se 1 (by rfl) ⟨2174660, by rfl⟩ : syracuseStep 2899547 = 4349321) B4349321
theorem B3055279 : Blo 1809606 3055279 := bstep (se 1 (by rfl) ⟨2291459, by rfl⟩ : syracuseStep 3055279 = 4582919) B4582919
theorem B8699579 : Blo 1809606 8699579 := bstep (se 1 (by rfl) ⟨6524684, by rfl⟩ : syracuseStep 8699579 = 13049369) B13049369
theorem B4644595 : Blo 1809606 4644595 := bstep (se 1 (by rfl) ⟨3483446, by rfl⟩ : syracuseStep 4644595 = 6966893) B6966893
theorem B6110963 : Blo 1809606 6110963 := bstep (se 1 (by rfl) ⟨4583222, by rfl⟩ : syracuseStep 6110963 = 9166445) B9166445
theorem B11009803 : Blo 1809606 11009803 := bstep (se 1 (by rfl) ⟨8257352, by rfl⟩ : syracuseStep 11009803 = 16514705) B16514705
theorem B10313527 : Blo 1809606 10313527 := bstep (se 1 (by rfl) ⟨7735145, by rfl⟩ : syracuseStep 10313527 = 15470291) B15470291
theorem B1810247 : Blo 1809606 1810247 := bstep (se 1 (by rfl) ⟨1357685, by rfl⟩ : syracuseStep 1810247 = 2715371) B2715371
theorem B1810399 : Blo 1809606 1810399 := bstep (se 1 (by rfl) ⟨1357799, by rfl⟩ : syracuseStep 1810399 = 2715599) B2715599
theorem B3055583 : Blo 1809606 3055583 := bstep (se 1 (by rfl) ⟨2291687, by rfl⟩ : syracuseStep 3055583 = 4583375) B4583375
theorem B15294521 : Blo 1809606 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B1810623 : Blo 1809606 1810623 := bstep (se 1 (by rfl) ⟨1357967, by rfl⟩ : syracuseStep 1810623 = 2715935) B2715935
theorem B1810639 : Blo 1809606 1810639 := bstep (se 1 (by rfl) ⟨1357979, by rfl⟩ : syracuseStep 1810639 = 2715959) B2715959
theorem B1810687 : Blo 1809606 1810687 := bstep (se 1 (by rfl) ⟨1358015, by rfl⟩ : syracuseStep 1810687 = 2716031) B2716031
theorem B1810735 : Blo 1809606 1810735 := bstep (se 1 (by rfl) ⟨1358051, by rfl⟩ : syracuseStep 1810735 = 2716103) B2716103
theorem B13050179 : Blo 1809606 13050179 := bstep (se 1 (by rfl) ⟨9787634, by rfl⟩ : syracuseStep 13050179 = 19575269) B19575269
theorem B13746509 : Blo 1809606 13746509 := bstep (se 3 (by rfl) ⟨2577470, by rfl⟩ : syracuseStep 13746509 = 5154941) B5154941
theorem B1810971 : Blo 1809606 1810971 := bstep (se 1 (by rfl) ⟨1358228, by rfl⟩ : syracuseStep 1810971 = 2716457) B2716457
theorem B1835551 : Blo 1809606 1835551 := bstep (se 1 (by rfl) ⟨1376663, by rfl⟩ : syracuseStep 1835551 = 2753327) B2753327
theorem B1810975 : Blo 1809606 1810975 := bstep (se 1 (by rfl) ⟨1358231, by rfl⟩ : syracuseStep 1810975 = 2716463) B2716463
theorem B1811055 : Blo 1809606 1811055 := bstep (se 1 (by rfl) ⟨1358291, by rfl⟩ : syracuseStep 1811055 = 2716583) B2716583
theorem B4072103 : Blo 1809606 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B1811111 : Blo 1809606 1811111 := bstep (se 1 (by rfl) ⟨1358333, by rfl⟩ : syracuseStep 1811111 = 2716667) B2716667
theorem B1811151 : Blo 1809606 1811151 := bstep (se 1 (by rfl) ⟨1358363, by rfl⟩ : syracuseStep 1811151 = 2716727) B2716727
theorem B1811231 : Blo 1809606 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B4072247 : Blo 1809606 4072247 := bstep (se 1 (by rfl) ⟨3054185, by rfl⟩ : syracuseStep 4072247 = 6108371) B6108371
theorem B4072427 : Blo 1809606 4072427 := bstep (se 1 (by rfl) ⟨3054320, by rfl⟩ : syracuseStep 4072427 = 6108641) B6108641
theorem B6874091 : Blo 1809606 6874091 := bstep (se 1 (by rfl) ⟨5155568, by rfl⟩ : syracuseStep 6874091 = 10311137) B10311137
theorem B1811503 : Blo 1809606 1811503 := bstep (se 1 (by rfl) ⟨1358627, by rfl⟩ : syracuseStep 1811503 = 2717255) B2717255
theorem B6112367 : Blo 1809606 6112367 := bstep (se 1 (by rfl) ⟨4584275, by rfl⟩ : syracuseStep 6112367 = 9168551) B9168551
theorem B1811567 : Blo 1809606 1811567 := bstep (se 1 (by rfl) ⟨1358675, by rfl⟩ : syracuseStep 1811567 = 2717351) B2717351
theorem B4351097 : Blo 1809606 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B7840889 : Blo 1809606 7840889 := bstep (se 2 (by rfl) ⟨2940333, by rfl⟩ : syracuseStep 7840889 = 5880667) B5880667
theorem B6112475 : Blo 1809606 6112475 := bstep (se 1 (by rfl) ⟨4584356, by rfl⟩ : syracuseStep 6112475 = 9168713) B9168713
theorem B2901295 : Blo 1809606 2901295 := bstep (se 1 (by rfl) ⟨2175971, by rfl⟩ : syracuseStep 2901295 = 4351943) B4351943
theorem B3056953 : Blo 1809606 3056953 := bstep (se 2 (by rfl) ⟨1146357, by rfl⟩ : syracuseStep 3056953 = 2292715) B2292715
theorem B13755743 : Blo 1809606 13755743 := bstep (se 1 (by rfl) ⟨10316807, by rfl⟩ : syracuseStep 13755743 = 20633615) B20633615
theorem B4072859 : Blo 1809606 4072859 := bstep (se 1 (by rfl) ⟨3054644, by rfl⟩ : syracuseStep 4072859 = 6109289) B6109289
theorem B264259037 : Blo 1809606 264259037 := bstep (se 3 (by rfl) ⟨49548569, by rfl⟩ : syracuseStep 264259037 = 99097139) B99097139
theorem B23209537 : Blo 1809606 23209537 := bstep (se 2 (by rfl) ⟨8703576, by rfl⟩ : syracuseStep 23209537 = 17407153) B17407153
theorem B5154623 : Blo 1809606 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B4073435 : Blo 1809606 4073435 := bstep (se 1 (by rfl) ⟨3055076, by rfl⟩ : syracuseStep 4073435 = 6110153) B6110153
theorem B4351963 : Blo 1809606 4351963 := bstep (se 1 (by rfl) ⟨3263972, by rfl⟩ : syracuseStep 4351963 = 6527945) B6527945
theorem B9168875 : Blo 1809606 9168875 := bstep (se 1 (by rfl) ⟨6876656, by rfl⟩ : syracuseStep 9168875 = 13753313) B13753313
theorem B11601953 : Blo 1809606 11601953 := bstep (se 2 (by rfl) ⟨4350732, by rfl⟩ : syracuseStep 11601953 = 8701465) B8701465
theorem B4073615 : Blo 1809606 4073615 := bstep (se 1 (by rfl) ⟨3055211, by rfl⟩ : syracuseStep 4073615 = 6110423) B6110423
theorem B4073705 : Blo 1809606 4073705 := bstep (se 2 (by rfl) ⟨1527639, by rfl⟩ : syracuseStep 4073705 = 3055279) B3055279
theorem B17402201 : Blo 1809606 17402201 := bstep (se 2 (by rfl) ⟨6525825, by rfl⟩ : syracuseStep 17402201 = 13051651) B13051651
theorem B4073975 : Blo 1809606 4073975 := bstep (se 1 (by rfl) ⟨3055481, by rfl⟩ : syracuseStep 4073975 = 6110963) B6110963
theorem B8702579 : Blo 1809606 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B10447505 : Blo 1809606 10447505 := bstep (se 2 (by rfl) ⟨3917814, by rfl⟩ : syracuseStep 10447505 = 7835629) B7835629
theorem B13748939 : Blo 1809606 13748939 := bstep (se 1 (by rfl) ⟨10311704, by rfl⟩ : syracuseStep 13748939 = 20623409) B20623409
theorem B4131623 : Blo 1809606 4131623 := bstep (se 1 (by rfl) ⟨3098717, by rfl⟩ : syracuseStep 4131623 = 6197435) B6197435
theorem B17640287 : Blo 1809606 17640287 := bstep (se 1 (by rfl) ⟨13230215, by rfl⟩ : syracuseStep 17640287 = 26460431) B26460431
theorem B2714591 : Blo 1809606 2714591 := bstep (se 1 (by rfl) ⟨2035943, by rfl⟩ : syracuseStep 2714591 = 4071887) B4071887
theorem B5155807 : Blo 1809606 5155807 := bstep (se 1 (by rfl) ⟨3866855, by rfl⟩ : syracuseStep 5155807 = 7733711) B7733711
theorem B4074569 : Blo 1809606 4074569 := bstep (se 2 (by rfl) ⟨1527963, by rfl⟩ : syracuseStep 4074569 = 3055927) B3055927
theorem B9170009 : Blo 1809606 9170009 := bstep (se 2 (by rfl) ⟨3438753, by rfl⟩ : syracuseStep 9170009 = 6877507) B6877507
theorem B6966415 : Blo 1809606 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B10316969 : Blo 1809606 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B2715035 : Blo 1809606 2715035 := bstep (se 1 (by rfl) ⟨2036276, by rfl⟩ : syracuseStep 2715035 = 4072553) B4072553
theorem B10309153 : Blo 1809606 10309153 := bstep (se 2 (by rfl) ⟨3865932, by rfl⟩ : syracuseStep 10309153 = 7731865) B7731865
theorem B2715455 : Blo 1809606 2715455 := bstep (se 1 (by rfl) ⟨2036591, by rfl⟩ : syracuseStep 2715455 = 4073183) B4073183
theorem B29765483 : Blo 1809606 29765483 := bstep (se 1 (by rfl) ⟨22324112, by rfl⟩ : syracuseStep 29765483 = 44648225) B44648225
theorem B2715641 : Blo 1809606 2715641 := bstep (se 2 (by rfl) ⟨1018365, by rfl⟩ : syracuseStep 2715641 = 2036731) B2036731
theorem B6525031 : Blo 1809606 6525031 := bstep (se 1 (by rfl) ⟨4893773, by rfl⟩ : syracuseStep 6525031 = 9787547) B9787547
theorem B4583567 : Blo 1809606 4583567 := bstep (se 1 (by rfl) ⟨3437675, by rfl⟩ : syracuseStep 4583567 = 6875351) B6875351
theorem B2035867 : Blo 1809606 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B2715881 : Blo 1809606 2715881 := bstep (se 2 (by rfl) ⟨1018455, by rfl⟩ : syracuseStep 2715881 = 2036911) B2036911
theorem B26112233 : Blo 1809606 26112233 := bstep (se 2 (by rfl) ⟨9792087, by rfl⟩ : syracuseStep 26112233 = 19584175) B19584175
theorem B2716007 : Blo 1809606 2716007 := bstep (se 1 (by rfl) ⟨2037005, by rfl⟩ : syracuseStep 2716007 = 4074011) B4074011
theorem B7737743 : Blo 1809606 7737743 := bstep (se 1 (by rfl) ⟨5803307, by rfl⟩ : syracuseStep 7737743 = 11606615) B11606615
theorem B28242341 : Blo 1809606 28242341 := bstep (se 4 (by rfl) ⟨2647719, by rfl⟩ : syracuseStep 28242341 = 5295439) B5295439
theorem B13046345 : Blo 1809606 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B2716553 : Blo 1809606 2716553 := bstep (se 2 (by rfl) ⟨1018707, by rfl⟩ : syracuseStep 2716553 = 2037415) B2037415
theorem B13751369 : Blo 1809606 13751369 := bstep (se 2 (by rfl) ⟨5156763, by rfl⟩ : syracuseStep 13751369 = 10313527) B10313527
theorem B34796627 : Blo 1809606 34796627 := bstep (se 1 (by rfl) ⟨26097470, by rfl⟩ : syracuseStep 34796627 = 52194941) B52194941
theorem B2176183 : Blo 1809606 2176183 := bstep (se 1 (by rfl) ⟨1632137, by rfl⟩ : syracuseStep 2176183 = 3264275) B3264275
theorem B13055195 : Blo 1809606 13055195 := bstep (se 1 (by rfl) ⟨9791396, by rfl⟩ : syracuseStep 13055195 = 19582793) B19582793
theorem B6108425 : Blo 1809606 6108425 := bstep (se 2 (by rfl) ⟨2290659, by rfl⟩ : syracuseStep 6108425 = 4581319) B4581319
theorem B2716937 : Blo 1809606 2716937 := bstep (se 2 (by rfl) ⟨1018851, by rfl⟩ : syracuseStep 2716937 = 2037703) B2037703
theorem B2037055 : Blo 1809606 2037055 := bstep (se 1 (by rfl) ⟨1527791, by rfl⟩ : syracuseStep 2037055 = 3055583) B3055583
theorem B2716991 : Blo 1809606 2716991 := bstep (se 1 (by rfl) ⟨2037743, by rfl⟩ : syracuseStep 2716991 = 4075487) B4075487
theorem B6108911 : Blo 1809606 6108911 := bstep (se 1 (by rfl) ⟨4581683, by rfl⟩ : syracuseStep 6108911 = 9163367) B9163367
theorem B2037487 : Blo 1809606 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B2037595 : Blo 1809606 2037595 := bstep (se 1 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 2037595 = 3056393) B3056393
theorem B4184201 : Blo 1809606 4184201 := bstep (se 2 (by rfl) ⟨1569075, by rfl⟩ : syracuseStep 4184201 = 3138151) B3138151
theorem B23189651 : Blo 1809606 23189651 := bstep (se 1 (by rfl) ⟨17392238, by rfl⟩ : syracuseStep 23189651 = 34784477) B34784477
theorem B2037991 : Blo 1809606 2037991 := bstep (se 1 (by rfl) ⟨1528493, by rfl⟩ : syracuseStep 2037991 = 3056987) B3056987
theorem B178551017 : Blo 1809606 178551017 := bstep (se 2 (by rfl) ⟨66956631, by rfl⟩ : syracuseStep 178551017 = 133913263) B133913263
theorem B3053855 : Blo 1809606 3053855 := bstep (se 1 (by rfl) ⟨2290391, by rfl⟩ : syracuseStep 3053855 = 4580783) B4580783
theorem B3053983 : Blo 1809606 3053983 := bstep (se 1 (by rfl) ⟨2290487, by rfl⟩ : syracuseStep 3053983 = 4580975) B4580975
theorem B15686075 : Blo 1809606 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B6871661 : Blo 1809606 6871661 := bstep (se 3 (by rfl) ⟨1288436, by rfl⟩ : syracuseStep 6871661 = 2576873) B2576873
theorem B6109883 : Blo 1809606 6109883 := bstep (se 1 (by rfl) ⟨4582412, by rfl⟩ : syracuseStep 6109883 = 9164825) B9164825
theorem B10058579 : Blo 1809606 10058579 := bstep (se 1 (by rfl) ⟨7543934, by rfl⟩ : syracuseStep 10058579 = 15087869) B15087869
theorem B9288539 : Blo 1809606 9288539 := bstep (se 1 (by rfl) ⟨6966404, by rfl⟩ : syracuseStep 9288539 = 13932809) B13932809
theorem B17407001 : Blo 1809606 17407001 := bstep (se 2 (by rfl) ⟨6527625, by rfl⟩ : syracuseStep 17407001 = 13055251) B13055251
theorem B6872161 : Blo 1809606 6872161 := bstep (se 2 (by rfl) ⟨2577060, by rfl⟩ : syracuseStep 6872161 = 5154121) B5154121
theorem B1809615 : Blo 1809606 1809615 := bstep (se 1 (by rfl) ⟨1357211, by rfl⟩ : syracuseStep 1809615 = 2714423) B2714423
theorem B1809639 : Blo 1809606 1809639 := bstep (se 1 (by rfl) ⟨1357229, by rfl⟩ : syracuseStep 1809639 = 2714459) B2714459
theorem B1809735 : Blo 1809606 1809735 := bstep (se 1 (by rfl) ⟨1357301, by rfl⟩ : syracuseStep 1809735 = 2714603) B2714603
theorem B20635073 : Blo 1809606 20635073 := bstep (se 2 (by rfl) ⟨7738152, by rfl⟩ : syracuseStep 20635073 = 15476305) B15476305
theorem B14876111 : Blo 1809606 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B1809871 : Blo 1809606 1809871 := bstep (se 1 (by rfl) ⟨1357403, by rfl⟩ : syracuseStep 1809871 = 2714807) B2714807
theorem B6970835 : Blo 1809606 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B49552955 : Blo 1809606 49552955 := bstep (se 1 (by rfl) ⟨37164716, by rfl⟩ : syracuseStep 49552955 = 74329433) B74329433
theorem B23838299 : Blo 1809606 23838299 := bstep (se 1 (by rfl) ⟨17878724, by rfl⟩ : syracuseStep 23838299 = 35757449) B35757449
theorem B1810031 : Blo 1809606 1810031 := bstep (se 1 (by rfl) ⟨1357523, by rfl⟩ : syracuseStep 1810031 = 2715047) B2715047
theorem B3055225 : Blo 1809606 3055225 := bstep (se 2 (by rfl) ⟨1145709, by rfl⟩ : syracuseStep 3055225 = 2291419) B2291419
theorem B6192793 : Blo 1809606 6192793 := bstep (se 2 (by rfl) ⟨2322297, by rfl⟩ : syracuseStep 6192793 = 4644595) B4644595
theorem B1810087 : Blo 1809606 1810087 := bstep (se 1 (by rfl) ⟨1357565, by rfl⟩ : syracuseStep 1810087 = 2715131) B2715131
theorem B14679737 : Blo 1809606 14679737 := bstep (se 2 (by rfl) ⟨5504901, by rfl⟩ : syracuseStep 14679737 = 11009803) B11009803
theorem B39132881 : Blo 1809606 39132881 := bstep (se 2 (by rfl) ⟨14674830, by rfl⟩ : syracuseStep 39132881 = 29349661) B29349661
theorem B1810151 : Blo 1809606 1810151 := bstep (se 1 (by rfl) ⟨1357613, by rfl⟩ : syracuseStep 1810151 = 2715227) B2715227
theorem B1933031 : Blo 1809606 1933031 := bstep (se 1 (by rfl) ⟨1449773, by rfl⟩ : syracuseStep 1933031 = 2899547) B2899547
theorem B1810207 : Blo 1809606 1810207 := bstep (se 1 (by rfl) ⟨1357655, by rfl⟩ : syracuseStep 1810207 = 2715311) B2715311
theorem B5799719 : Blo 1809606 5799719 := bstep (se 1 (by rfl) ⟨4349789, by rfl⟩ : syracuseStep 5799719 = 8699579) B8699579
theorem B1810287 : Blo 1809606 1810287 := bstep (se 1 (by rfl) ⟨1357715, by rfl⟩ : syracuseStep 1810287 = 2715431) B2715431
theorem B1810343 : Blo 1809606 1810343 := bstep (se 1 (by rfl) ⟨1357757, by rfl⟩ : syracuseStep 1810343 = 2715515) B2715515
theorem B15474665 : Blo 1809606 15474665 := bstep (se 2 (by rfl) ⟨5802999, by rfl⟩ : syracuseStep 15474665 = 11605999) B11605999
theorem B3055711 : Blo 1809606 3055711 := bstep (se 1 (by rfl) ⟨2291783, by rfl⟩ : syracuseStep 3055711 = 4583567) B4583567
theorem B8700041 : Blo 1809606 8700041 := bstep (se 2 (by rfl) ⟨3262515, by rfl⟩ : syracuseStep 8700041 = 6525031) B6525031
theorem B1810587 : Blo 1809606 1810587 := bstep (se 1 (by rfl) ⟨1357940, by rfl⟩ : syracuseStep 1810587 = 2715881) B2715881
theorem B17408155 : Blo 1809606 17408155 := bstep (se 1 (by rfl) ⟨13056116, by rfl⟩ : syracuseStep 17408155 = 26112233) B26112233
theorem B9789605 : Blo 1809606 9789605 := bstep (se 4 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 9789605 = 1835551) B1835551
theorem B8700119 : Blo 1809606 8700119 := bstep (se 1 (by rfl) ⟨6525089, by rfl⟩ : syracuseStep 8700119 = 13050179) B13050179
theorem B1810671 : Blo 1809606 1810671 := bstep (se 1 (by rfl) ⟨1358003, by rfl⟩ : syracuseStep 1810671 = 2716007) B2716007
theorem B11157869 : Blo 1809606 11157869 := bstep (se 3 (by rfl) ⟨2092100, by rfl⟩ : syracuseStep 11157869 = 4184201) B4184201
theorem B4071977 : Blo 1809606 4071977 := bstep (se 2 (by rfl) ⟨1526991, by rfl⟩ : syracuseStep 4071977 = 3053983) B3053983
theorem B1811035 : Blo 1809606 1811035 := bstep (se 1 (by rfl) ⟨1358276, by rfl⟩ : syracuseStep 1811035 = 2716553) B2716553
theorem B9167579 : Blo 1809606 9167579 := bstep (se 1 (by rfl) ⟨6875684, by rfl⟩ : syracuseStep 9167579 = 13751369) B13751369
theorem B5227259 : Blo 1809606 5227259 := bstep (se 1 (by rfl) ⟨3920444, by rfl⟩ : syracuseStep 5227259 = 7840889) B7840889
theorem B4072283 : Blo 1809606 4072283 := bstep (se 1 (by rfl) ⟨3054212, by rfl⟩ : syracuseStep 4072283 = 6108425) B6108425
theorem B1811291 : Blo 1809606 1811291 := bstep (se 1 (by rfl) ⟨1358468, by rfl⟩ : syracuseStep 1811291 = 2716937) B2716937
theorem B1811327 : Blo 1809606 1811327 := bstep (se 1 (by rfl) ⟨1358495, by rfl⟩ : syracuseStep 1811327 = 2716991) B2716991
theorem B41829533 : Blo 1809606 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B4072607 : Blo 1809606 4072607 := bstep (se 1 (by rfl) ⟨3054455, by rfl⟩ : syracuseStep 4072607 = 6108911) B6108911
theorem B6874409 : Blo 1809606 6874409 := bstep (se 2 (by rfl) ⟨2577903, by rfl⟩ : syracuseStep 6874409 = 5155807) B5155807
theorem B6112583 : Blo 1809606 6112583 := bstep (se 1 (by rfl) ⟨4584437, by rfl⟩ : syracuseStep 6112583 = 9168875) B9168875
theorem B7734635 : Blo 1809606 7734635 := bstep (se 1 (by rfl) ⟨5800976, by rfl⟩ : syracuseStep 7734635 = 11601953) B11601953
theorem B15459767 : Blo 1809606 15459767 := bstep (se 1 (by rfl) ⟨11594825, by rfl⟩ : syracuseStep 15459767 = 23189651) B23189651
theorem B11601467 : Blo 1809606 11601467 := bstep (se 1 (by rfl) ⟨8701100, by rfl⟩ : syracuseStep 11601467 = 17402201) B17402201
theorem B2901577 : Blo 1809606 2901577 := bstep (se 2 (by rfl) ⟨1088091, by rfl⟩ : syracuseStep 2901577 = 2176183) B2176183
theorem B3868393 : Blo 1809606 3868393 := bstep (se 2 (by rfl) ⟨1450647, by rfl⟩ : syracuseStep 3868393 = 2901295) B2901295
theorem B4581107 : Blo 1809606 4581107 := bstep (se 1 (by rfl) ⟨3435830, by rfl⟩ : syracuseStep 4581107 = 6871661) B6871661
theorem B5801719 : Blo 1809606 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B6965003 : Blo 1809606 6965003 := bstep (se 1 (by rfl) ⟨5223752, by rfl⟩ : syracuseStep 6965003 = 10447505) B10447505
theorem B4073255 : Blo 1809606 4073255 := bstep (se 1 (by rfl) ⟨3054941, by rfl⟩ : syracuseStep 4073255 = 6109883) B6109883
theorem B2754415 : Blo 1809606 2754415 := bstep (se 1 (by rfl) ⟨2065811, by rfl⟩ : syracuseStep 2754415 = 4131623) B4131623
theorem B5154749 : Blo 1809606 5154749 := bstep (se 3 (by rfl) ⟨966515, by rfl⟩ : syracuseStep 5154749 = 1933031) B1933031
theorem B6113339 : Blo 1809606 6113339 := bstep (se 1 (by rfl) ⟨4585004, by rfl⟩ : syracuseStep 6113339 = 9170009) B9170009
theorem B4073633 : Blo 1809606 4073633 := bstep (se 2 (by rfl) ⟨1527612, by rfl⟩ : syracuseStep 4073633 = 3055225) B3055225
theorem B13756715 : Blo 1809606 13756715 := bstep (se 1 (by rfl) ⟨10317536, by rfl⟩ : syracuseStep 13756715 = 20635073) B20635073
theorem B4647223 : Blo 1809606 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B19843655 : Blo 1809606 19843655 := bstep (se 1 (by rfl) ⟨14882741, by rfl⟩ : syracuseStep 19843655 = 29765483) B29765483
theorem B5802617 : Blo 1809606 5802617 := bstep (se 2 (by rfl) ⟨2175981, by rfl⟩ : syracuseStep 5802617 = 4351963) B4351963
theorem B10316443 : Blo 1809606 10316443 := bstep (se 1 (by rfl) ⟨7737332, by rfl⟩ : syracuseStep 10316443 = 15474665) B15474665
theorem B2714489 : Blo 1809606 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B18828227 : Blo 1809606 18828227 := bstep (se 1 (by rfl) ⟨14121170, by rfl⟩ : syracuseStep 18828227 = 28242341) B28242341
theorem B11602925 : Blo 1809606 11602925 := bstep (se 3 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 11602925 = 4351097) B4351097
theorem B2714735 : Blo 1809606 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B2714831 : Blo 1809606 2714831 := bstep (se 1 (by rfl) ⟨2036123, by rfl⟩ : syracuseStep 2714831 = 4072247) B4072247
theorem B2714951 : Blo 1809606 2714951 := bstep (se 1 (by rfl) ⟨2036213, by rfl⟩ : syracuseStep 2714951 = 4072427) B4072427
theorem B4582727 : Blo 1809606 4582727 := bstep (se 1 (by rfl) ⟨3437045, by rfl⟩ : syracuseStep 4582727 = 6874091) B6874091
theorem B4074911 : Blo 1809606 4074911 := bstep (se 1 (by rfl) ⟨3056183, by rfl⟩ : syracuseStep 4074911 = 6112367) B6112367
theorem B37154213 : Blo 1809606 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B4074983 : Blo 1809606 4074983 := bstep (se 1 (by rfl) ⟨3056237, by rfl⟩ : syracuseStep 4074983 = 6112475) B6112475
theorem B8703463 : Blo 1809606 8703463 := bstep (se 1 (by rfl) ⟨6527597, by rfl⟩ : syracuseStep 8703463 = 13055195) B13055195
theorem B9170495 : Blo 1809606 9170495 := bstep (se 1 (by rfl) ⟨6877871, by rfl⟩ : syracuseStep 9170495 = 13755743) B13755743
theorem B2715239 : Blo 1809606 2715239 := bstep (se 1 (by rfl) ⟨2036429, by rfl⟩ : syracuseStep 2715239 = 4072859) B4072859
theorem B176172691 : Blo 1809606 176172691 := bstep (se 1 (by rfl) ⟨132129518, by rfl⟩ : syracuseStep 176172691 = 264259037) B264259037
theorem B3436415 : Blo 1809606 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B2715623 : Blo 1809606 2715623 := bstep (se 1 (by rfl) ⟨2036717, by rfl⟩ : syracuseStep 2715623 = 4073435) B4073435
theorem B2715743 : Blo 1809606 2715743 := bstep (se 1 (by rfl) ⟨2036807, by rfl⟩ : syracuseStep 2715743 = 4073615) B4073615
theorem B9162881 : Blo 1809606 9162881 := bstep (se 2 (by rfl) ⟨3436080, by rfl⟩ : syracuseStep 9162881 = 6872161) B6872161
theorem B119034011 : Blo 1809606 119034011 := bstep (se 1 (by rfl) ⟨89275508, by rfl⟩ : syracuseStep 119034011 = 178551017) B178551017
theorem B2715803 : Blo 1809606 2715803 := bstep (se 1 (by rfl) ⟨2036852, by rfl⟩ : syracuseStep 2715803 = 4073705) B4073705
theorem B2035903 : Blo 1809606 2035903 := bstep (se 1 (by rfl) ⟨1526927, by rfl⟩ : syracuseStep 2035903 = 3053855) B3053855
theorem B2715983 : Blo 1809606 2715983 := bstep (se 1 (by rfl) ⟨2036987, by rfl⟩ : syracuseStep 2715983 = 4073975) B4073975
theorem B4075937 : Blo 1809606 4075937 := bstep (se 2 (by rfl) ⟨1528476, by rfl⟩ : syracuseStep 4075937 = 3056953) B3056953
theorem B2716073 : Blo 1809606 2716073 := bstep (se 2 (by rfl) ⟨1018527, by rfl⟩ : syracuseStep 2716073 = 2037055) B2037055
theorem B6705719 : Blo 1809606 6705719 := bstep (se 1 (by rfl) ⟨5029289, by rfl⟩ : syracuseStep 6705719 = 10058579) B10058579
theorem B11760191 : Blo 1809606 11760191 := bstep (se 1 (by rfl) ⟨8820143, by rfl⟩ : syracuseStep 11760191 = 17640287) B17640287
theorem B11604667 : Blo 1809606 11604667 := bstep (se 1 (by rfl) ⟨8703500, by rfl⟩ : syracuseStep 11604667 = 17407001) B17407001
theorem B2716379 : Blo 1809606 2716379 := bstep (se 1 (by rfl) ⟨2037284, by rfl⟩ : syracuseStep 2716379 = 4074569) B4074569
theorem B30946049 : Blo 1809606 30946049 := bstep (se 2 (by rfl) ⟨11604768, by rfl⟩ : syracuseStep 30946049 = 23209537) B23209537
theorem B6877979 : Blo 1809606 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B9917407 : Blo 1809606 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B2716649 : Blo 1809606 2716649 := bstep (se 2 (by rfl) ⟨1018743, by rfl⟩ : syracuseStep 2716649 = 2037487) B2037487
theorem B33035303 : Blo 1809606 33035303 := bstep (se 1 (by rfl) ⟨24776477, by rfl⟩ : syracuseStep 33035303 = 49552955) B49552955
theorem B9786491 : Blo 1809606 9786491 := bstep (se 1 (by rfl) ⟨7339868, by rfl⟩ : syracuseStep 9786491 = 14679737) B14679737
theorem B2716793 : Blo 1809606 2716793 := bstep (se 2 (by rfl) ⟨1018797, by rfl⟩ : syracuseStep 2716793 = 2037595) B2037595
theorem B26088587 : Blo 1809606 26088587 := bstep (se 1 (by rfl) ⟨19566440, by rfl⟩ : syracuseStep 26088587 = 39132881) B39132881
theorem B10196347 : Blo 1809606 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B9164339 : Blo 1809606 9164339 := bstep (se 1 (by rfl) ⟨6873254, by rfl⟩ : syracuseStep 9164339 = 13746509) B13746509
theorem B5158495 : Blo 1809606 5158495 := bstep (se 1 (by rfl) ⟨3868871, by rfl⟩ : syracuseStep 5158495 = 7737743) B7737743
theorem B2717321 : Blo 1809606 2717321 := bstep (se 2 (by rfl) ⟨1018995, by rfl⟩ : syracuseStep 2717321 = 2037991) B2037991
theorem B8697563 : Blo 1809606 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B23197751 : Blo 1809606 23197751 := bstep (se 1 (by rfl) ⟨17398313, by rfl⟩ : syracuseStep 23197751 = 34796627) B34796627
theorem B33028229 : Blo 1809606 33028229 := bstep (se 4 (by rfl) ⟨3096396, by rfl⟩ : syracuseStep 33028229 = 6192793) B6192793
theorem B9165959 : Blo 1809606 9165959 := bstep (se 1 (by rfl) ⟨6874469, by rfl⟩ : syracuseStep 9165959 = 13748939) B13748939
theorem B6192359 : Blo 1809606 6192359 := bstep (se 1 (by rfl) ⟨4644269, by rfl⟩ : syracuseStep 6192359 = 9288539) B9288539
theorem B1809727 : Blo 1809606 1809727 := bstep (se 1 (by rfl) ⟨1357295, by rfl⟩ : syracuseStep 1809727 = 2714591) B2714591
theorem B13745537 : Blo 1809606 13745537 := bstep (se 2 (by rfl) ⟨5154576, by rfl⟩ : syracuseStep 13745537 = 10309153) B10309153
theorem B15465917 : Blo 1809606 15465917 := bstep (se 3 (by rfl) ⟨2899859, by rfl⟩ : syracuseStep 15465917 = 5799719) B5799719
theorem B1810023 : Blo 1809606 1810023 := bstep (se 1 (by rfl) ⟨1357517, by rfl⟩ : syracuseStep 1810023 = 2715035) B2715035
theorem B15892199 : Blo 1809606 15892199 := bstep (se 1 (by rfl) ⟨11919149, by rfl⟩ : syracuseStep 15892199 = 23838299) B23838299
theorem B1810303 : Blo 1809606 1810303 := bstep (se 1 (by rfl) ⟨1357727, by rfl⟩ : syracuseStep 1810303 = 2715455) B2715455
theorem B1810427 : Blo 1809606 1810427 := bstep (se 1 (by rfl) ⟨1357820, by rfl⟩ : syracuseStep 1810427 = 2715641) B2715641
theorem B1810495 : Blo 1809606 1810495 := bstep (se 1 (by rfl) ⟨1357871, by rfl⟩ : syracuseStep 1810495 = 2715743) B2715743
theorem B5800027 : Blo 1809606 5800027 := bstep (se 1 (by rfl) ⟨4350020, by rfl⟩ : syracuseStep 5800027 = 8700041) B8700041
theorem B79356007 : Blo 1809606 79356007 := bstep (se 1 (by rfl) ⟨59517005, by rfl⟩ : syracuseStep 79356007 = 119034011) B119034011
theorem B1810535 : Blo 1809606 1810535 := bstep (se 1 (by rfl) ⟨1357901, by rfl⟩ : syracuseStep 1810535 = 2715803) B2715803
theorem B5800079 : Blo 1809606 5800079 := bstep (se 1 (by rfl) ⟨4350059, by rfl⟩ : syracuseStep 5800079 = 8700119) B8700119
theorem B1810655 : Blo 1809606 1810655 := bstep (se 1 (by rfl) ⟨1357991, by rfl⟩ : syracuseStep 1810655 = 2715983) B2715983
theorem B1810715 : Blo 1809606 1810715 := bstep (se 1 (by rfl) ⟨1358036, by rfl⟩ : syracuseStep 1810715 = 2716073) B2716073
theorem B7840127 : Blo 1809606 7840127 := bstep (se 1 (by rfl) ⟨5880095, by rfl⟩ : syracuseStep 7840127 = 11760191) B11760191
theorem B6111719 : Blo 1809606 6111719 := bstep (se 1 (by rfl) ⟨4583789, by rfl⟩ : syracuseStep 6111719 = 9167579) B9167579
theorem B1810919 : Blo 1809606 1810919 := bstep (se 1 (by rfl) ⟨1358189, by rfl⟩ : syracuseStep 1810919 = 2716379) B2716379
theorem B1811099 : Blo 1809606 1811099 := bstep (se 1 (by rfl) ⟨1358324, by rfl⟩ : syracuseStep 1811099 = 2716649) B2716649
theorem B1811195 : Blo 1809606 1811195 := bstep (se 1 (by rfl) ⟨1358396, by rfl⟩ : syracuseStep 1811195 = 2716793) B2716793
theorem B17392391 : Blo 1809606 17392391 := bstep (se 1 (by rfl) ⟨13044293, by rfl⟩ : syracuseStep 17392391 = 26088587) B26088587
theorem B27886355 : Blo 1809606 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B13755257 : Blo 1809606 13755257 := bstep (se 2 (by rfl) ⟨5158221, by rfl⟩ : syracuseStep 13755257 = 10316443) B10316443
theorem B29754317 : Blo 1809606 29754317 := bstep (se 3 (by rfl) ⟨5578934, by rfl⟩ : syracuseStep 29754317 = 11157869) B11157869
theorem B10306511 : Blo 1809606 10306511 := bstep (se 1 (by rfl) ⟨7729883, by rfl⟩ : syracuseStep 10306511 = 15459767) B15459767
theorem B7734311 : Blo 1809606 7734311 := bstep (se 1 (by rfl) ⟨5800733, by rfl⟩ : syracuseStep 7734311 = 11601467) B11601467
theorem B1811547 : Blo 1809606 1811547 := bstep (se 1 (by rfl) ⟨1358660, by rfl⟩ : syracuseStep 1811547 = 2717321) B2717321
theorem B3868411 : Blo 1809606 3868411 := bstep (se 1 (by rfl) ⟨2901308, by rfl⟩ : syracuseStep 3868411 = 5802617) B5802617
theorem B12552151 : Blo 1809606 12552151 := bstep (se 1 (by rfl) ⟨9414113, by rfl⟩ : syracuseStep 12552151 = 18828227) B18828227
theorem B7735283 : Blo 1809606 7735283 := bstep (se 1 (by rfl) ⟨5801462, by rfl⟩ : syracuseStep 7735283 = 11602925) B11602925
theorem B3868769 : Blo 1809606 3868769 := bstep (se 2 (by rfl) ⟨1450788, by rfl⟩ : syracuseStep 3868769 = 2901577) B2901577
theorem B7735625 : Blo 1809606 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B6113663 : Blo 1809606 6113663 := bstep (se 1 (by rfl) ⟨4585247, by rfl⟩ : syracuseStep 6113663 = 9170495) B9170495
theorem B3672553 : Blo 1809606 3672553 := bstep (se 2 (by rfl) ⟨1377207, by rfl⟩ : syracuseStep 3672553 = 2754415) B2754415
theorem B10594799 : Blo 1809606 10594799 := bstep (se 1 (by rfl) ⟨7946099, by rfl⟩ : syracuseStep 10594799 = 15892199) B15892199
theorem B55757429 : Blo 1809606 55757429 := bstep (se 5 (by rfl) ⟨2613629, by rfl⟩ : syracuseStep 55757429 = 5227259) B5227259
theorem B4074281 : Blo 1809606 4074281 := bstep (se 2 (by rfl) ⟨1527855, by rfl⟩ : syracuseStep 4074281 = 3055711) B3055711
theorem B23210873 : Blo 1809606 23210873 := bstep (se 2 (by rfl) ⟨8704077, by rfl⟩ : syracuseStep 23210873 = 17408155) B17408155
theorem B2714537 : Blo 1809606 2714537 := bstep (se 2 (by rfl) ⟨1017951, by rfl⟩ : syracuseStep 2714537 = 2035903) B2035903
theorem B2714651 : Blo 1809606 2714651 := bstep (se 1 (by rfl) ⟨2035988, by rfl⟩ : syracuseStep 2714651 = 4071977) B4071977
theorem B20630699 : Blo 1809606 20630699 := bstep (se 1 (by rfl) ⟨15473024, by rfl⟩ : syracuseStep 20630699 = 30946049) B30946049
theorem B2714855 : Blo 1809606 2714855 := bstep (se 1 (by rfl) ⟨2036141, by rfl⟩ : syracuseStep 2714855 = 4072283) B4072283
theorem B22023535 : Blo 1809606 22023535 := bstep (se 1 (by rfl) ⟨16517651, by rfl⟩ : syracuseStep 22023535 = 33035303) B33035303
theorem B6524327 : Blo 1809606 6524327 := bstep (se 1 (by rfl) ⟨4893245, by rfl⟩ : syracuseStep 6524327 = 9786491) B9786491
theorem B2715071 : Blo 1809606 2715071 := bstep (se 1 (by rfl) ⟨2036303, by rfl⟩ : syracuseStep 2715071 = 4072607) B4072607
theorem B4582939 : Blo 1809606 4582939 := bstep (se 1 (by rfl) ⟨3437204, by rfl⟩ : syracuseStep 4582939 = 6874409) B6874409
theorem B4075055 : Blo 1809606 4075055 := bstep (se 1 (by rfl) ⟨3056291, by rfl⟩ : syracuseStep 4075055 = 6112583) B6112583
theorem B5156423 : Blo 1809606 5156423 := bstep (se 1 (by rfl) ⟨3867317, by rfl⟩ : syracuseStep 5156423 = 7734635) B7734635
theorem B2715503 : Blo 1809606 2715503 := bstep (se 1 (by rfl) ⟨2036627, by rfl⟩ : syracuseStep 2715503 = 4073255) B4073255
theorem B3436499 : Blo 1809606 3436499 := bstep (se 1 (by rfl) ⟨2577374, by rfl⟩ : syracuseStep 3436499 = 5154749) B5154749
theorem B4075559 : Blo 1809606 4075559 := bstep (se 1 (by rfl) ⟨3056669, by rfl⟩ : syracuseStep 4075559 = 6113339) B6113339
theorem B2715755 : Blo 1809606 2715755 := bstep (se 1 (by rfl) ⟨2036816, by rfl⟩ : syracuseStep 2715755 = 4073633) B4073633
theorem B52916413 : Blo 1809606 52916413 := bstep (se 3 (by rfl) ⟨9921827, by rfl⟩ : syracuseStep 52916413 = 19843655) B19843655
theorem B9171143 : Blo 1809606 9171143 := bstep (se 1 (by rfl) ⟨6878357, by rfl⟩ : syracuseStep 9171143 = 13756715) B13756715
theorem B24785189 : Blo 1809606 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B13595129 : Blo 1809606 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B11604617 : Blo 1809606 11604617 := bstep (se 2 (by rfl) ⟨4351731, by rfl⟩ : syracuseStep 11604617 = 8703463) B8703463
theorem B6877993 : Blo 1809606 6877993 := bstep (se 2 (by rfl) ⟨2579247, by rfl⟩ : syracuseStep 6877993 = 5158495) B5158495
theorem B9163691 : Blo 1809606 9163691 := bstep (se 1 (by rfl) ⟨6872768, by rfl⟩ : syracuseStep 9163691 = 13745537) B13745537
theorem B2716607 : Blo 1809606 2716607 := bstep (se 1 (by rfl) ⟨2037455, by rfl⟩ : syracuseStep 2716607 = 4074911) B4074911
theorem B24769475 : Blo 1809606 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B10310611 : Blo 1809606 10310611 := bstep (se 1 (by rfl) ⟨7732958, by rfl⟩ : syracuseStep 10310611 = 15465917) B15465917
theorem B5157857 : Blo 1809606 5157857 := bstep (se 2 (by rfl) ⟨1934196, by rfl⟩ : syracuseStep 5157857 = 3868393) B3868393
theorem B2716655 : Blo 1809606 2716655 := bstep (se 1 (by rfl) ⟨2037491, by rfl⟩ : syracuseStep 2716655 = 4074983) B4074983
theorem B52892837 : Blo 1809606 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B2290943 : Blo 1809606 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B6108587 : Blo 1809606 6108587 := bstep (se 1 (by rfl) ⟨4581440, by rfl⟩ : syracuseStep 6108587 = 9162881) B9162881
theorem B6526403 : Blo 1809606 6526403 := bstep (se 1 (by rfl) ⟨4894802, by rfl⟩ : syracuseStep 6526403 = 9789605) B9789605
theorem B2717291 : Blo 1809606 2717291 := bstep (se 1 (by rfl) ⟨2037968, by rfl⟩ : syracuseStep 2717291 = 4075937) B4075937
theorem B4470479 : Blo 1809606 4470479 := bstep (se 1 (by rfl) ⟨3352859, by rfl⟩ : syracuseStep 4470479 = 6705719) B6705719
theorem B4585319 : Blo 1809606 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B15472889 : Blo 1809606 15472889 := bstep (se 2 (by rfl) ⟨5802333, by rfl⟩ : syracuseStep 15472889 = 11604667) B11604667
theorem B6109559 : Blo 1809606 6109559 := bstep (se 1 (by rfl) ⟨4582169, by rfl⟩ : syracuseStep 6109559 = 9164339) B9164339
theorem B5798375 : Blo 1809606 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B3054071 : Blo 1809606 3054071 := bstep (se 1 (by rfl) ⟨2290553, by rfl⟩ : syracuseStep 3054071 = 4581107) B4581107
theorem B4643335 : Blo 1809606 4643335 := bstep (se 1 (by rfl) ⟨3482501, by rfl⟩ : syracuseStep 4643335 = 6965003) B6965003
theorem B15465167 : Blo 1809606 15465167 := bstep (se 1 (by rfl) ⟨11598875, by rfl⟩ : syracuseStep 15465167 = 23197751) B23197751
theorem B22018819 : Blo 1809606 22018819 := bstep (se 1 (by rfl) ⟨16514114, by rfl⟩ : syracuseStep 22018819 = 33028229) B33028229
theorem B1809659 : Blo 1809606 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B1809823 : Blo 1809606 1809823 := bstep (se 1 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 1809823 = 2714735) B2714735
theorem B6110639 : Blo 1809606 6110639 := bstep (se 1 (by rfl) ⟨4582979, by rfl⟩ : syracuseStep 6110639 = 9165959) B9165959
theorem B1809887 : Blo 1809606 1809887 := bstep (se 1 (by rfl) ⟨1357415, by rfl⟩ : syracuseStep 1809887 = 2714831) B2714831
theorem B4128239 : Blo 1809606 4128239 := bstep (se 1 (by rfl) ⟨3096179, by rfl⟩ : syracuseStep 4128239 = 6192359) B6192359
theorem B234896921 : Blo 1809606 234896921 := bstep (se 2 (by rfl) ⟨88086345, by rfl⟩ : syracuseStep 234896921 = 176172691) B176172691
theorem B1809967 : Blo 1809606 1809967 := bstep (se 1 (by rfl) ⟨1357475, by rfl⟩ : syracuseStep 1809967 = 2714951) B2714951
theorem B3055151 : Blo 1809606 3055151 := bstep (se 1 (by rfl) ⟨2291363, by rfl⟩ : syracuseStep 3055151 = 4582727) B4582727
theorem B1810159 : Blo 1809606 1810159 := bstep (se 1 (by rfl) ⟨1357619, by rfl⟩ : syracuseStep 1810159 = 2715239) B2715239
theorem B1810415 : Blo 1809606 1810415 := bstep (se 1 (by rfl) ⟨1357811, by rfl⟩ : syracuseStep 1810415 = 2715623) B2715623
theorem B1810503 : Blo 1809606 1810503 := bstep (se 1 (by rfl) ⟨1357877, by rfl⟩ : syracuseStep 1810503 = 2715755) B2715755
theorem B3866719 : Blo 1809606 3866719 := bstep (se 1 (by rfl) ⟨2900039, by rfl⟩ : syracuseStep 3866719 = 5800079) B5800079
theorem B7733369 : Blo 1809606 7733369 := bstep (se 2 (by rfl) ⟨2900013, by rfl⟩ : syracuseStep 7733369 = 5800027) B5800027
theorem B16523459 : Blo 1809606 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B5226751 : Blo 1809606 5226751 := bstep (se 1 (by rfl) ⟨3920063, by rfl⟩ : syracuseStep 5226751 = 7840127) B7840127
theorem B423232037 : Blo 1809606 423232037 := bstep (se 4 (by rfl) ⟨39678003, by rfl⟩ : syracuseStep 423232037 = 79356007) B79356007
theorem B1811071 : Blo 1809606 1811071 := bstep (se 1 (by rfl) ⟨1358303, by rfl⟩ : syracuseStep 1811071 = 2716607) B2716607
theorem B1811103 : Blo 1809606 1811103 := bstep (se 1 (by rfl) ⟨1358327, by rfl⟩ : syracuseStep 1811103 = 2716655) B2716655
theorem B4072391 : Blo 1809606 4072391 := bstep (se 1 (by rfl) ⟨3054293, by rfl⟩ : syracuseStep 4072391 = 6108587) B6108587
theorem B4350935 : Blo 1809606 4350935 := bstep (se 1 (by rfl) ⟨3263201, by rfl⟩ : syracuseStep 4350935 = 6526403) B6526403
theorem B1811527 : Blo 1809606 1811527 := bstep (se 1 (by rfl) ⟨1358645, by rfl⟩ : syracuseStep 1811527 = 2717291) B2717291
theorem B3056879 : Blo 1809606 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B13747481 : Blo 1809606 13747481 := bstep (se 2 (by rfl) ⟨5155305, by rfl⟩ : syracuseStep 13747481 = 10310611) B10310611
theorem B10315259 : Blo 1809606 10315259 := bstep (se 1 (by rfl) ⟨7736444, by rfl⟩ : syracuseStep 10315259 = 15472889) B15472889
theorem B4073039 : Blo 1809606 4073039 := bstep (se 1 (by rfl) ⟨3054779, by rfl⟩ : syracuseStep 4073039 = 6109559) B6109559
theorem B7063199 : Blo 1809606 7063199 := bstep (se 1 (by rfl) ⟨5297399, by rfl⟩ : syracuseStep 7063199 = 10594799) B10594799
theorem B4073759 : Blo 1809606 4073759 := bstep (se 1 (by rfl) ⟨3055319, by rfl⟩ : syracuseStep 4073759 = 6110639) B6110639
theorem B6114095 : Blo 1809606 6114095 := bstep (se 1 (by rfl) ⟨4585571, by rfl⟩ : syracuseStep 6114095 = 9171143) B9171143
theorem B10316717 : Blo 1809606 10316717 := bstep (se 3 (by rfl) ⟨1934384, by rfl⟩ : syracuseStep 10316717 = 3868769) B3868769
theorem B4074479 : Blo 1809606 4074479 := bstep (se 1 (by rfl) ⟨3055859, by rfl⟩ : syracuseStep 4074479 = 6111719) B6111719
theorem B9063419 : Blo 1809606 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B7736411 : Blo 1809606 7736411 := bstep (se 1 (by rfl) ⟨5802308, by rfl⟩ : syracuseStep 7736411 = 11604617) B11604617
theorem B11594927 : Blo 1809606 11594927 := bstep (se 1 (by rfl) ⟨8696195, by rfl⟩ : syracuseStep 11594927 = 17392391) B17392391
theorem B18590903 : Blo 1809606 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B9170171 : Blo 1809606 9170171 := bstep (se 1 (by rfl) ⟨6877628, by rfl⟩ : syracuseStep 9170171 = 13755257) B13755257
theorem B19836211 : Blo 1809606 19836211 := bstep (se 1 (by rfl) ⟨14877158, by rfl⟩ : syracuseStep 19836211 = 29754317) B29754317
theorem B5156207 : Blo 1809606 5156207 := bstep (se 1 (by rfl) ⟨3867155, by rfl⟩ : syracuseStep 5156207 = 7734311) B7734311
theorem B35261891 : Blo 1809606 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B9170657 : Blo 1809606 9170657 := bstep (se 2 (by rfl) ⟨3438996, by rfl⟩ : syracuseStep 9170657 = 6877993) B6877993
theorem B5156855 : Blo 1809606 5156855 := bstep (se 1 (by rfl) ⟨3867641, by rfl⟩ : syracuseStep 5156855 = 7735283) B7735283
theorem B5157083 : Blo 1809606 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B4075775 : Blo 1809606 4075775 := bstep (se 1 (by rfl) ⟨3056831, by rfl⟩ : syracuseStep 4075775 = 6113663) B6113663
theorem B2036047 : Blo 1809606 2036047 := bstep (se 1 (by rfl) ⟨1527035, by rfl⟩ : syracuseStep 2036047 = 3054071) B3054071
theorem B37171619 : Blo 1809606 37171619 := bstep (se 1 (by rfl) ⟨27878714, by rfl⟩ : syracuseStep 37171619 = 55757429) B55757429
theorem B10310111 : Blo 1809606 10310111 := bstep (se 1 (by rfl) ⟨7732583, by rfl⟩ : syracuseStep 10310111 = 15465167) B15465167
theorem B29364713 : Blo 1809606 29364713 := bstep (se 2 (by rfl) ⟨11011767, by rfl⟩ : syracuseStep 29364713 = 22023535) B22023535
theorem B2716187 : Blo 1809606 2716187 := bstep (se 1 (by rfl) ⟨2037140, by rfl⟩ : syracuseStep 2716187 = 4074281) B4074281
theorem B5157881 : Blo 1809606 5157881 := bstep (se 2 (by rfl) ⟨1934205, by rfl⟩ : syracuseStep 5157881 = 3868411) B3868411
theorem B2036767 : Blo 1809606 2036767 := bstep (se 1 (by rfl) ⟨1527575, by rfl⟩ : syracuseStep 2036767 = 3055151) B3055151
theorem B2716703 : Blo 1809606 2716703 := bstep (se 1 (by rfl) ⟨2037527, by rfl⟩ : syracuseStep 2716703 = 4075055) B4075055
theorem B3437615 : Blo 1809606 3437615 := bstep (se 1 (by rfl) ⟨2578211, by rfl⟩ : syracuseStep 3437615 = 5156423) B5156423
theorem B2290999 : Blo 1809606 2290999 := bstep (se 1 (by rfl) ⟨1718249, by rfl⟩ : syracuseStep 2290999 = 3436499) B3436499
theorem B2717039 : Blo 1809606 2717039 := bstep (se 1 (by rfl) ⟨2037779, by rfl⟩ : syracuseStep 2717039 = 4075559) B4075559
theorem B70555217 : Blo 1809606 70555217 := bstep (se 2 (by rfl) ⟨26458206, by rfl⟩ : syracuseStep 70555217 = 52916413) B52916413
theorem B6109127 : Blo 1809606 6109127 := bstep (se 1 (by rfl) ⟨4581845, by rfl⟩ : syracuseStep 6109127 = 9163691) B9163691
theorem B16512983 : Blo 1809606 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B6871007 : Blo 1809606 6871007 := bstep (se 1 (by rfl) ⟨5153255, by rfl⟩ : syracuseStep 6871007 = 10306511) B10306511
theorem B4896737 : Blo 1809606 4896737 := bstep (se 2 (by rfl) ⟨1836276, by rfl⟩ : syracuseStep 4896737 = 3672553) B3672553
theorem B6109181 : Blo 1809606 6109181 := bstep (se 3 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 6109181 = 2290943) B2290943
theorem B6191113 : Blo 1809606 6191113 := bstep (se 2 (by rfl) ⟨2321667, by rfl⟩ : syracuseStep 6191113 = 4643335) B4643335
theorem B29358425 : Blo 1809606 29358425 := bstep (se 2 (by rfl) ⟨11009409, by rfl⟩ : syracuseStep 29358425 = 22018819) B22018819
theorem B2980319 : Blo 1809606 2980319 := bstep (se 1 (by rfl) ⟨2235239, by rfl⟩ : syracuseStep 2980319 = 4470479) B4470479
theorem B3865583 : Blo 1809606 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B15473915 : Blo 1809606 15473915 := bstep (se 1 (by rfl) ⟨11605436, by rfl⟩ : syracuseStep 15473915 = 23210873) B23210873
theorem B1809691 : Blo 1809606 1809691 := bstep (se 1 (by rfl) ⟨1357268, by rfl⟩ : syracuseStep 1809691 = 2714537) B2714537
theorem B1809767 : Blo 1809606 1809767 := bstep (se 1 (by rfl) ⟨1357325, by rfl⟩ : syracuseStep 1809767 = 2714651) B2714651
theorem B6110585 : Blo 1809606 6110585 := bstep (se 2 (by rfl) ⟨2291469, by rfl⟩ : syracuseStep 6110585 = 4582939) B4582939
theorem B13753799 : Blo 1809606 13753799 := bstep (se 1 (by rfl) ⟨10315349, by rfl⟩ : syracuseStep 13753799 = 20630699) B20630699
theorem B1809903 : Blo 1809606 1809903 := bstep (se 1 (by rfl) ⟨1357427, by rfl⟩ : syracuseStep 1809903 = 2714855) B2714855
theorem B4349551 : Blo 1809606 4349551 := bstep (se 1 (by rfl) ⟨3262163, by rfl⟩ : syracuseStep 4349551 = 6524327) B6524327
theorem B1810047 : Blo 1809606 1810047 := bstep (se 1 (by rfl) ⟨1357535, by rfl⟩ : syracuseStep 1810047 = 2715071) B2715071
theorem B2752159 : Blo 1809606 2752159 := bstep (se 1 (by rfl) ⟨2064119, by rfl⟩ : syracuseStep 2752159 = 4128239) B4128239
theorem B156597947 : Blo 1809606 156597947 := bstep (se 1 (by rfl) ⟨117448460, by rfl⟩ : syracuseStep 156597947 = 234896921) B234896921
theorem B1810335 : Blo 1809606 1810335 := bstep (se 1 (by rfl) ⟨1357751, by rfl⟩ : syracuseStep 1810335 = 2715503) B2715503
theorem B13754285 : Blo 1809606 13754285 := bstep (se 3 (by rfl) ⟨2578928, by rfl⟩ : syracuseStep 13754285 = 5157857) B5157857
theorem B16736201 : Blo 1809606 16736201 := bstep (se 2 (by rfl) ⟨6276075, by rfl⟩ : syracuseStep 16736201 = 12552151) B12552151
theorem B24781079 : Blo 1809606 24781079 := bstep (se 1 (by rfl) ⟨18585809, by rfl⟩ : syracuseStep 24781079 = 37171619) B37171619
theorem B6873407 : Blo 1809606 6873407 := bstep (se 1 (by rfl) ⟨5155055, by rfl⟩ : syracuseStep 6873407 = 10310111) B10310111
theorem B1810791 : Blo 1809606 1810791 := bstep (se 1 (by rfl) ⟨1358093, by rfl⟩ : syracuseStep 1810791 = 2716187) B2716187
theorem B2900623 : Blo 1809606 2900623 := bstep (se 1 (by rfl) ⟨2175467, by rfl⟩ : syracuseStep 2900623 = 4350935) B4350935
theorem B1811135 : Blo 1809606 1811135 := bstep (se 1 (by rfl) ⟨1358351, by rfl⟩ : syracuseStep 1811135 = 2716703) B2716703
theorem B1811359 : Blo 1809606 1811359 := bstep (se 1 (by rfl) ⟨1358519, by rfl⟩ : syracuseStep 1811359 = 2717039) B2717039
theorem B7947517 : Blo 1809606 7947517 := bstep (se 3 (by rfl) ⟨1490159, by rfl⟩ : syracuseStep 7947517 = 2980319) B2980319
theorem B4072751 : Blo 1809606 4072751 := bstep (se 1 (by rfl) ⟨3054563, by rfl⟩ : syracuseStep 4072751 = 6109127) B6109127
theorem B4580671 : Blo 1809606 4580671 := bstep (se 1 (by rfl) ⟨3435503, by rfl⟩ : syracuseStep 4580671 = 6871007) B6871007
theorem B4072787 : Blo 1809606 4072787 := bstep (se 1 (by rfl) ⟨3054590, by rfl⟩ : syracuseStep 4072787 = 6109181) B6109181
theorem B188147245 : Blo 1809606 188147245 := bstep (se 3 (by rfl) ⟨35277608, by rfl⟩ : syracuseStep 188147245 = 70555217) B70555217
theorem B19572283 : Blo 1809606 19572283 := bstep (se 1 (by rfl) ⟨14679212, by rfl⟩ : syracuseStep 19572283 = 29358425) B29358425
theorem B10315943 : Blo 1809606 10315943 := bstep (se 1 (by rfl) ⟨7736957, by rfl⟩ : syracuseStep 10315943 = 15473915) B15473915
theorem B6113447 : Blo 1809606 6113447 := bstep (se 1 (by rfl) ⟨4585085, by rfl⟩ : syracuseStep 6113447 = 9170171) B9170171
theorem B4073723 : Blo 1809606 4073723 := bstep (se 1 (by rfl) ⟨3055292, by rfl⟩ : syracuseStep 4073723 = 6110585) B6110585
theorem B9169199 : Blo 1809606 9169199 := bstep (se 1 (by rfl) ⟨6876899, by rfl⟩ : syracuseStep 9169199 = 13753799) B13753799
theorem B6113771 : Blo 1809606 6113771 := bstep (se 1 (by rfl) ⟨4585328, by rfl⟩ : syracuseStep 6113771 = 9170657) B9170657
theorem B9169523 : Blo 1809606 9169523 := bstep (se 1 (by rfl) ⟨6877142, by rfl⟩ : syracuseStep 9169523 = 13754285) B13754285
theorem B10308221 : Blo 1809606 10308221 := bstep (se 3 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 10308221 = 3865583) B3865583
theorem B24169117 : Blo 1809606 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B5155579 : Blo 1809606 5155579 := bstep (se 1 (by rfl) ⟨3866684, by rfl⟩ : syracuseStep 5155579 = 7733369) B7733369
theorem B5155625 : Blo 1809606 5155625 := bstep (se 2 (by rfl) ⟨1933359, by rfl⟩ : syracuseStep 5155625 = 3866719) B3866719
theorem B2714729 : Blo 1809606 2714729 := bstep (se 2 (by rfl) ⟨1018023, by rfl⟩ : syracuseStep 2714729 = 2036047) B2036047
theorem B30919805 : Blo 1809606 30919805 := bstep (se 3 (by rfl) ⟨5797463, by rfl⟩ : syracuseStep 30919805 = 11594927) B11594927
theorem B2714927 : Blo 1809606 2714927 := bstep (se 1 (by rfl) ⟨2036195, by rfl⟩ : syracuseStep 2714927 = 4072391) B4072391
theorem B6876839 : Blo 1809606 6876839 := bstep (se 1 (by rfl) ⟨5157629, by rfl⟩ : syracuseStep 6876839 = 10315259) B10315259
theorem B2715359 : Blo 1809606 2715359 := bstep (se 1 (by rfl) ⟨2036519, by rfl⟩ : syracuseStep 2715359 = 4073039) B4073039
theorem B3264491 : Blo 1809606 3264491 := bstep (se 1 (by rfl) ⟨2448368, by rfl⟩ : syracuseStep 3264491 = 4896737) B4896737
theorem B2715689 : Blo 1809606 2715689 := bstep (se 2 (by rfl) ⟨1018383, by rfl⟩ : syracuseStep 2715689 = 2036767) B2036767
theorem B2715839 : Blo 1809606 2715839 := bstep (se 1 (by rfl) ⟨2036879, by rfl⟩ : syracuseStep 2715839 = 4073759) B4073759
theorem B26448281 : Blo 1809606 26448281 := bstep (se 2 (by rfl) ⟨9918105, by rfl⟩ : syracuseStep 26448281 = 19836211) B19836211
theorem B4076063 : Blo 1809606 4076063 := bstep (se 1 (by rfl) ⟨3057047, by rfl⟩ : syracuseStep 4076063 = 6114095) B6114095
theorem B6877811 : Blo 1809606 6877811 := bstep (se 1 (by rfl) ⟨5158358, by rfl⟩ : syracuseStep 6877811 = 10316717) B10316717
theorem B2716319 : Blo 1809606 2716319 := bstep (se 1 (by rfl) ⟨2037239, by rfl⟩ : syracuseStep 2716319 = 4074479) B4074479
theorem B5157607 : Blo 1809606 5157607 := bstep (se 1 (by rfl) ⟨3868205, by rfl⟩ : syracuseStep 5157607 = 7736411) B7736411
theorem B3437471 : Blo 1809606 3437471 := bstep (se 1 (by rfl) ⟨2578103, by rfl⟩ : syracuseStep 3437471 = 5156207) B5156207
theorem B23507927 : Blo 1809606 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B3437903 : Blo 1809606 3437903 := bstep (se 1 (by rfl) ⟨2578427, by rfl⟩ : syracuseStep 3437903 = 5156855) B5156855
theorem B8254817 : Blo 1809606 8254817 := bstep (se 2 (by rfl) ⟨3095556, by rfl⟩ : syracuseStep 8254817 = 6191113) B6191113
theorem B11015639 : Blo 1809606 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B3438055 : Blo 1809606 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B2717183 : Blo 1809606 2717183 := bstep (se 1 (by rfl) ⟨2037887, by rfl⟩ : syracuseStep 2717183 = 4075775) B4075775
theorem B19576475 : Blo 1809606 19576475 := bstep (se 1 (by rfl) ⟨14682356, by rfl⟩ : syracuseStep 19576475 = 29364713) B29364713
theorem B6969001 : Blo 1809606 6969001 := bstep (se 2 (by rfl) ⟨2613375, by rfl⟩ : syracuseStep 6969001 = 5226751) B5226751
theorem B282154691 : Blo 1809606 282154691 := bstep (se 1 (by rfl) ⟨211616018, by rfl⟩ : syracuseStep 282154691 = 423232037) B423232037
theorem B3438587 : Blo 1809606 3438587 := bstep (se 1 (by rfl) ⟨2578940, by rfl⟩ : syracuseStep 3438587 = 5157881) B5157881
theorem B2291743 : Blo 1809606 2291743 := bstep (se 1 (by rfl) ⟨1718807, by rfl⟩ : syracuseStep 2291743 = 3437615) B3437615
theorem B2037919 : Blo 1809606 2037919 := bstep (se 1 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 2037919 = 3056879) B3056879
theorem B9164987 : Blo 1809606 9164987 := bstep (se 1 (by rfl) ⟨6873740, by rfl⟩ : syracuseStep 9164987 = 13747481) B13747481
theorem B4708799 : Blo 1809606 4708799 := bstep (se 1 (by rfl) ⟨3531599, by rfl⟩ : syracuseStep 4708799 = 7063199) B7063199
theorem B11008655 : Blo 1809606 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B3054665 : Blo 1809606 3054665 := bstep (se 2 (by rfl) ⟨1145499, by rfl⟩ : syracuseStep 3054665 = 2290999) B2290999
theorem B12393935 : Blo 1809606 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B5799401 : Blo 1809606 5799401 := bstep (se 2 (by rfl) ⟨2174775, by rfl⟩ : syracuseStep 5799401 = 4349551) B4349551
theorem B3669545 : Blo 1809606 3669545 := bstep (se 2 (by rfl) ⟨1376079, by rfl⟩ : syracuseStep 3669545 = 2752159) B2752159
theorem B104398631 : Blo 1809606 104398631 := bstep (se 1 (by rfl) ⟨78298973, by rfl⟩ : syracuseStep 104398631 = 156597947) B156597947
theorem B11157467 : Blo 1809606 11157467 := bstep (se 1 (by rfl) ⟨8368100, by rfl⟩ : syracuseStep 11157467 = 16736201) B16736201
theorem B1810459 : Blo 1809606 1810459 := bstep (se 1 (by rfl) ⟨1357844, by rfl⟩ : syracuseStep 1810459 = 2715689) B2715689
theorem B3055657 : Blo 1809606 3055657 := bstep (se 2 (by rfl) ⟨1145871, by rfl⟩ : syracuseStep 3055657 = 2291743) B2291743
theorem B1810559 : Blo 1809606 1810559 := bstep (se 1 (by rfl) ⟨1357919, by rfl⟩ : syracuseStep 1810559 = 2715839) B2715839
theorem B1810879 : Blo 1809606 1810879 := bstep (se 1 (by rfl) ⟨1358159, by rfl⟩ : syracuseStep 1810879 = 2716319) B2716319
theorem B15671951 : Blo 1809606 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B3867497 : Blo 1809606 3867497 := bstep (se 2 (by rfl) ⟨1450311, by rfl⟩ : syracuseStep 3867497 = 2900623) B2900623
theorem B9167741 : Blo 1809606 9167741 := bstep (se 3 (by rfl) ⟨1718951, by rfl⟩ : syracuseStep 9167741 = 3437903) B3437903
theorem B6874105 : Blo 1809606 6874105 := bstep (se 2 (by rfl) ⟨2577789, by rfl⟩ : syracuseStep 6874105 = 5155579) B5155579
theorem B1811455 : Blo 1809606 1811455 := bstep (se 1 (by rfl) ⟨1358591, by rfl⟩ : syracuseStep 1811455 = 2717183) B2717183
theorem B13050983 : Blo 1809606 13050983 := bstep (se 1 (by rfl) ⟨9788237, by rfl⟩ : syracuseStep 13050983 = 19576475) B19576475
theorem B6112799 : Blo 1809606 6112799 := bstep (se 1 (by rfl) ⟨4584599, by rfl⟩ : syracuseStep 6112799 = 9169199) B9169199
theorem B3139199 : Blo 1809606 3139199 := bstep (se 1 (by rfl) ⟨2354399, by rfl⟩ : syracuseStep 3139199 = 4708799) B4708799
theorem B6113015 : Blo 1809606 6113015 := bstep (se 1 (by rfl) ⟨4584761, by rfl⟩ : syracuseStep 6113015 = 9169523) B9169523
theorem B752412509 : Blo 1809606 752412509 := bstep (se 3 (by rfl) ⟨141077345, by rfl⟩ : syracuseStep 752412509 = 282154691) B282154691
theorem B20613203 : Blo 1809606 20613203 := bstep (se 1 (by rfl) ⟨15459902, by rfl⟩ : syracuseStep 20613203 = 30919805) B30919805
theorem B9292001 : Blo 1809606 9292001 := bstep (se 2 (by rfl) ⟨3484500, by rfl⟩ : syracuseStep 9292001 = 6969001) B6969001
theorem B4582271 : Blo 1809606 4582271 := bstep (se 1 (by rfl) ⟨3436703, by rfl⟩ : syracuseStep 4582271 = 6873407) B6873407
theorem B17632187 : Blo 1809606 17632187 := bstep (se 1 (by rfl) ⟨13224140, by rfl⟩ : syracuseStep 17632187 = 26448281) B26448281
theorem B2715167 : Blo 1809606 2715167 := bstep (se 1 (by rfl) ⟨2036375, by rfl⟩ : syracuseStep 2715167 = 4072751) B4072751
theorem B2715191 : Blo 1809606 2715191 := bstep (se 1 (by rfl) ⟨2036393, by rfl⟩ : syracuseStep 2715191 = 4072787) B4072787
theorem B6876809 : Blo 1809606 6876809 := bstep (se 2 (by rfl) ⟨2578803, by rfl⟩ : syracuseStep 6876809 = 5157607) B5157607
theorem B7343759 : Blo 1809606 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B6877295 : Blo 1809606 6877295 := bstep (se 1 (by rfl) ⟨5157971, by rfl⟩ : syracuseStep 6877295 = 10315943) B10315943
theorem B4075631 : Blo 1809606 4075631 := bstep (se 1 (by rfl) ⟨3056723, by rfl⟩ : syracuseStep 4075631 = 6113447) B6113447
theorem B2715815 : Blo 1809606 2715815 := bstep (se 1 (by rfl) ⟨2036861, by rfl⟩ : syracuseStep 2715815 = 4073723) B4073723
theorem B4075847 : Blo 1809606 4075847 := bstep (se 1 (by rfl) ⟨3056885, by rfl⟩ : syracuseStep 4075847 = 6113771) B6113771
theorem B10596689 : Blo 1809606 10596689 := bstep (se 2 (by rfl) ⟨3973758, by rfl⟩ : syracuseStep 10596689 = 7947517) B7947517
theorem B6107561 : Blo 1809606 6107561 := bstep (se 2 (by rfl) ⟨2290335, by rfl⟩ : syracuseStep 6107561 = 4580671) B4580671
theorem B3437083 : Blo 1809606 3437083 := bstep (se 1 (by rfl) ⟨2577812, by rfl⟩ : syracuseStep 3437083 = 5155625) B5155625
theorem B4584073 : Blo 1809606 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B2036443 : Blo 1809606 2036443 := bstep (se 1 (by rfl) ⟨1527332, by rfl⟩ : syracuseStep 2036443 = 3054665) B3054665
theorem B26096377 : Blo 1809606 26096377 := bstep (se 2 (by rfl) ⟨9786141, by rfl⟩ : syracuseStep 26096377 = 19572283) B19572283
theorem B8262623 : Blo 1809606 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B2446363 : Blo 1809606 2446363 := bstep (se 1 (by rfl) ⟨1834772, by rfl⟩ : syracuseStep 2446363 = 3669545) B3669545
theorem B4584559 : Blo 1809606 4584559 := bstep (se 1 (by rfl) ⟨3438419, by rfl⟩ : syracuseStep 4584559 = 6876839) B6876839
theorem B2176327 : Blo 1809606 2176327 := bstep (se 1 (by rfl) ⟨1632245, by rfl⟩ : syracuseStep 2176327 = 3264491) B3264491
theorem B16520719 : Blo 1809606 16520719 := bstep (se 1 (by rfl) ⟨12390539, by rfl⟩ : syracuseStep 16520719 = 24781079) B24781079
theorem B2717225 : Blo 1809606 2717225 := bstep (se 2 (by rfl) ⟨1018959, by rfl⟩ : syracuseStep 2717225 = 2037919) B2037919
theorem B2717375 : Blo 1809606 2717375 := bstep (se 1 (by rfl) ⟨2038031, by rfl⟩ : syracuseStep 2717375 = 4076063) B4076063
theorem B4585207 : Blo 1809606 4585207 := bstep (se 1 (by rfl) ⟨3438905, by rfl⟩ : syracuseStep 4585207 = 6877811) B6877811
theorem B2291647 : Blo 1809606 2291647 := bstep (se 1 (by rfl) ⟨1718735, by rfl⟩ : syracuseStep 2291647 = 3437471) B3437471
theorem B32225489 : Blo 1809606 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B5503211 : Blo 1809606 5503211 := bstep (se 1 (by rfl) ⟨4127408, by rfl⟩ : syracuseStep 5503211 = 8254817) B8254817
theorem B2292391 : Blo 1809606 2292391 := bstep (se 1 (by rfl) ⟨1719293, by rfl⟩ : syracuseStep 2292391 = 3438587) B3438587
theorem B6109991 : Blo 1809606 6109991 := bstep (se 1 (by rfl) ⟨4582493, by rfl⟩ : syracuseStep 6109991 = 9164987) B9164987
theorem B6872147 : Blo 1809606 6872147 := bstep (se 1 (by rfl) ⟨5154110, by rfl⟩ : syracuseStep 6872147 = 10308221) B10308221
theorem B7339103 : Blo 1809606 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B250862993 : Blo 1809606 250862993 := bstep (se 2 (by rfl) ⟨94073622, by rfl⟩ : syracuseStep 250862993 = 188147245) B188147245
theorem B1809819 : Blo 1809606 1809819 := bstep (se 1 (by rfl) ⟨1357364, by rfl⟩ : syracuseStep 1809819 = 2714729) B2714729
theorem B1809951 : Blo 1809606 1809951 := bstep (se 1 (by rfl) ⟨1357463, by rfl⟩ : syracuseStep 1809951 = 2714927) B2714927
theorem B3866267 : Blo 1809606 3866267 := bstep (se 1 (by rfl) ⟨2899700, by rfl⟩ : syracuseStep 3866267 = 5799401) B5799401
theorem B1810239 : Blo 1809606 1810239 := bstep (se 1 (by rfl) ⟨1357679, by rfl⟩ : syracuseStep 1810239 = 2715359) B2715359
theorem B69599087 : Blo 1809606 69599087 := bstep (se 1 (by rfl) ⟨52199315, by rfl⟩ : syracuseStep 69599087 = 104398631) B104398631
theorem B29753245 : Blo 1809606 29753245 := bstep (se 3 (by rfl) ⟨5578733, by rfl⟩ : syracuseStep 29753245 = 11157467) B11157467
theorem B1810543 : Blo 1809606 1810543 := bstep (se 1 (by rfl) ⟨1357907, by rfl⟩ : syracuseStep 1810543 = 2715815) B2715815
theorem B4071707 : Blo 1809606 4071707 := bstep (se 1 (by rfl) ⟨3053780, by rfl⟩ : syracuseStep 4071707 = 6107561) B6107561
theorem B6111827 : Blo 1809606 6111827 := bstep (se 1 (by rfl) ⟨4583870, by rfl⟩ : syracuseStep 6111827 = 9167741) B9167741
theorem B6112097 : Blo 1809606 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B3056521 : Blo 1809606 3056521 := bstep (se 2 (by rfl) ⟨1146195, by rfl⟩ : syracuseStep 3056521 = 2292391) B2292391
theorem B1811483 : Blo 1809606 1811483 := bstep (se 1 (by rfl) ⟨1358612, by rfl⟩ : syracuseStep 1811483 = 2717225) B2717225
theorem B1811583 : Blo 1809606 1811583 := bstep (se 1 (by rfl) ⟨1358687, by rfl⟩ : syracuseStep 1811583 = 2717375) B2717375
theorem B3261817 : Blo 1809606 3261817 := bstep (se 2 (by rfl) ⟨1223181, by rfl⟩ : syracuseStep 3261817 = 2446363) B2446363
theorem B6112745 : Blo 1809606 6112745 := bstep (se 2 (by rfl) ⟨2292279, by rfl⟩ : syracuseStep 6112745 = 4584559) B4584559
theorem B4073327 : Blo 1809606 4073327 := bstep (se 1 (by rfl) ⟨3054995, by rfl⟩ : syracuseStep 4073327 = 6109991) B6109991
theorem B4581431 : Blo 1809606 4581431 := bstep (se 1 (by rfl) ⟨3436073, by rfl⟩ : syracuseStep 4581431 = 6872147) B6872147
theorem B4892735 : Blo 1809606 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B167241995 : Blo 1809606 167241995 := bstep (se 1 (by rfl) ⟨125431496, by rfl⟩ : syracuseStep 167241995 = 250862993) B250862993
theorem B6113609 : Blo 1809606 6113609 := bstep (se 2 (by rfl) ⟨2292603, by rfl⟩ : syracuseStep 6113609 = 4585207) B4585207
theorem B4074209 : Blo 1809606 4074209 := bstep (se 2 (by rfl) ⟨1527828, by rfl⟩ : syracuseStep 4074209 = 3055657) B3055657
theorem B7064459 : Blo 1809606 7064459 := bstep (se 1 (by rfl) ⟨5298344, by rfl⟩ : syracuseStep 7064459 = 10596689) B10596689
theorem B34802621 : Blo 1809606 34802621 := bstep (se 3 (by rfl) ⟨6525491, by rfl⟩ : syracuseStep 34802621 = 13050983) B13050983
theorem B10447967 : Blo 1809606 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B5508415 : Blo 1809606 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B4582777 : Blo 1809606 4582777 := bstep (se 2 (by rfl) ⟨1718541, by rfl⟩ : syracuseStep 4582777 = 3437083) B3437083
theorem B2715257 : Blo 1809606 2715257 := bstep (se 2 (by rfl) ⟨1018221, by rfl⟩ : syracuseStep 2715257 = 2036443) B2036443
theorem B34795169 : Blo 1809606 34795169 := bstep (se 2 (by rfl) ⟨13048188, by rfl⟩ : syracuseStep 34795169 = 26096377) B26096377
theorem B4075199 : Blo 1809606 4075199 := bstep (se 1 (by rfl) ⟨3056399, by rfl⟩ : syracuseStep 4075199 = 6112799) B6112799
theorem B2092799 : Blo 1809606 2092799 := bstep (se 1 (by rfl) ⟨1569599, by rfl⟩ : syracuseStep 2092799 = 3139199) B3139199
theorem B4075343 : Blo 1809606 4075343 := bstep (se 1 (by rfl) ⟨3056507, by rfl⟩ : syracuseStep 4075343 = 6113015) B6113015
theorem B501608339 : Blo 1809606 501608339 := bstep (se 1 (by rfl) ⟨376206254, by rfl⟩ : syracuseStep 501608339 = 752412509) B752412509
theorem B13742135 : Blo 1809606 13742135 := bstep (se 1 (by rfl) ⟨10306601, by rfl⟩ : syracuseStep 13742135 = 20613203) B20613203
theorem B21483659 : Blo 1809606 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B4584539 : Blo 1809606 4584539 := bstep (se 1 (by rfl) ⟨3438404, by rfl⟩ : syracuseStep 4584539 = 6876809) B6876809
theorem B4895839 : Blo 1809606 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B2577511 : Blo 1809606 2577511 := bstep (se 1 (by rfl) ⟨1933133, by rfl⟩ : syracuseStep 2577511 = 3866267) B3866267
theorem B39670993 : Blo 1809606 39670993 := bstep (se 2 (by rfl) ⟨14876622, by rfl⟩ : syracuseStep 39670993 = 29753245) B29753245
theorem B4584863 : Blo 1809606 4584863 := bstep (se 1 (by rfl) ⟨3438647, by rfl⟩ : syracuseStep 4584863 = 6877295) B6877295
theorem B2717087 : Blo 1809606 2717087 := bstep (se 1 (by rfl) ⟨2037815, by rfl⟩ : syracuseStep 2717087 = 4075631) B4075631
theorem B2717231 : Blo 1809606 2717231 := bstep (se 1 (by rfl) ⟨2037923, by rfl⟩ : syracuseStep 2717231 = 4075847) B4075847
theorem B2578331 : Blo 1809606 2578331 := bstep (se 1 (by rfl) ⟨1933748, by rfl⟩ : syracuseStep 2578331 = 3867497) B3867497
theorem B24778669 : Blo 1809606 24778669 := bstep (se 3 (by rfl) ⟨4646000, by rfl⟩ : syracuseStep 24778669 = 9292001) B9292001
theorem B9165473 : Blo 1809606 9165473 := bstep (se 2 (by rfl) ⟨3437052, by rfl⟩ : syracuseStep 9165473 = 6874105) B6874105
theorem B3668807 : Blo 1809606 3668807 := bstep (se 1 (by rfl) ⟨2751605, by rfl⟩ : syracuseStep 3668807 = 5503211) B5503211
theorem B11607077 : Blo 1809606 11607077 := bstep (se 4 (by rfl) ⟨1088163, by rfl⟩ : syracuseStep 11607077 = 2176327) B2176327
theorem B3054847 : Blo 1809606 3054847 := bstep (se 1 (by rfl) ⟨2291135, by rfl⟩ : syracuseStep 3054847 = 4582271) B4582271
theorem B11754791 : Blo 1809606 11754791 := bstep (se 1 (by rfl) ⟨8816093, by rfl⟩ : syracuseStep 11754791 = 17632187) B17632187
theorem B22027625 : Blo 1809606 22027625 := bstep (se 2 (by rfl) ⟨8260359, by rfl⟩ : syracuseStep 22027625 = 16520719) B16520719
theorem B1810111 : Blo 1809606 1810111 := bstep (se 1 (by rfl) ⟨1357583, by rfl⟩ : syracuseStep 1810111 = 2715167) B2715167
theorem B1810127 : Blo 1809606 1810127 := bstep (se 1 (by rfl) ⟨1357595, by rfl⟩ : syracuseStep 1810127 = 2715191) B2715191
theorem B46399391 : Blo 1809606 46399391 := bstep (se 1 (by rfl) ⟨34799543, by rfl⟩ : syracuseStep 46399391 = 69599087) B69599087
theorem B3055529 : Blo 1809606 3055529 := bstep (se 2 (by rfl) ⟨1145823, by rfl⟩ : syracuseStep 3055529 = 2291647) B2291647
theorem B3056359 : Blo 1809606 3056359 := bstep (se 1 (by rfl) ⟨2292269, by rfl⟩ : syracuseStep 3056359 = 4584539) B4584539
theorem B3056575 : Blo 1809606 3056575 := bstep (se 1 (by rfl) ⟨2292431, by rfl⟩ : syracuseStep 3056575 = 4584863) B4584863
theorem B1811391 : Blo 1809606 1811391 := bstep (se 1 (by rfl) ⟨1358543, by rfl⟩ : syracuseStep 1811391 = 2717087) B2717087
theorem B1811487 : Blo 1809606 1811487 := bstep (se 1 (by rfl) ⟨1358615, by rfl⟩ : syracuseStep 1811487 = 2717231) B2717231
theorem B111494663 : Blo 1809606 111494663 := bstep (se 1 (by rfl) ⟨83620997, by rfl⟩ : syracuseStep 111494663 = 167241995) B167241995
theorem B29378213 : Blo 1809606 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B4073129 : Blo 1809606 4073129 := bstep (se 2 (by rfl) ⟨1527423, by rfl⟩ : syracuseStep 4073129 = 3054847) B3054847
theorem B23201747 : Blo 1809606 23201747 := bstep (se 1 (by rfl) ⟨17401310, by rfl⟩ : syracuseStep 23201747 = 34802621) B34802621
theorem B5580797 : Blo 1809606 5580797 := bstep (se 3 (by rfl) ⟨1046399, by rfl⟩ : syracuseStep 5580797 = 2092799) B2092799
theorem B6965311 : Blo 1809606 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B6875549 : Blo 1809606 6875549 := bstep (se 3 (by rfl) ⟨1289165, by rfl⟩ : syracuseStep 6875549 = 2578331) B2578331
theorem B9161423 : Blo 1809606 9161423 := bstep (se 1 (by rfl) ⟨6871067, by rfl⟩ : syracuseStep 9161423 = 13742135) B13742135
theorem B14322439 : Blo 1809606 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B2714471 : Blo 1809606 2714471 := bstep (se 1 (by rfl) ⟨2035853, by rfl⟩ : syracuseStep 2714471 = 4071707) B4071707
theorem B4074551 : Blo 1809606 4074551 := bstep (se 1 (by rfl) ⟨3055913, by rfl⟩ : syracuseStep 4074551 = 6111827) B6111827
theorem B4074731 : Blo 1809606 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B4075163 : Blo 1809606 4075163 := bstep (se 1 (by rfl) ⟨3056372, by rfl⟩ : syracuseStep 4075163 = 6112745) B6112745
theorem B4075361 : Blo 1809606 4075361 := bstep (se 2 (by rfl) ⟨1528260, by rfl⟩ : syracuseStep 4075361 = 3056521) B3056521
theorem B2715551 : Blo 1809606 2715551 := bstep (se 1 (by rfl) ⟨2036663, by rfl⟩ : syracuseStep 2715551 = 4073327) B4073327
theorem B3436681 : Blo 1809606 3436681 := bstep (se 2 (by rfl) ⟨1288755, by rfl⟩ : syracuseStep 3436681 = 2577511) B2577511
theorem B4075739 : Blo 1809606 4075739 := bstep (se 1 (by rfl) ⟨3056804, by rfl⟩ : syracuseStep 4075739 = 6113609) B6113609
theorem B2716139 : Blo 1809606 2716139 := bstep (se 1 (by rfl) ⟨2037104, by rfl⟩ : syracuseStep 2716139 = 4074209) B4074209
theorem B2445871 : Blo 1809606 2445871 := bstep (se 1 (by rfl) ⟨1834403, by rfl⟩ : syracuseStep 2445871 = 3668807) B3668807
theorem B7738051 : Blo 1809606 7738051 := bstep (se 1 (by rfl) ⟨5803538, by rfl⟩ : syracuseStep 7738051 = 11607077) B11607077
theorem B7836527 : Blo 1809606 7836527 := bstep (se 1 (by rfl) ⟨5877395, by rfl⟩ : syracuseStep 7836527 = 11754791) B11754791
theorem B14685083 : Blo 1809606 14685083 := bstep (se 1 (by rfl) ⟨11013812, by rfl⟩ : syracuseStep 14685083 = 22027625) B22027625
theorem B23196779 : Blo 1809606 23196779 := bstep (se 1 (by rfl) ⟨17397584, by rfl⟩ : syracuseStep 23196779 = 34795169) B34795169
theorem B2716799 : Blo 1809606 2716799 := bstep (se 1 (by rfl) ⟨2037599, by rfl⟩ : syracuseStep 2716799 = 4075199) B4075199
theorem B2716895 : Blo 1809606 2716895 := bstep (se 1 (by rfl) ⟨2037671, by rfl⟩ : syracuseStep 2716895 = 4075343) B4075343
theorem B2037019 : Blo 1809606 2037019 := bstep (se 1 (by rfl) ⟨1527764, by rfl⟩ : syracuseStep 2037019 = 3055529) B3055529
theorem B13047293 : Blo 1809606 13047293 := bstep (se 3 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 13047293 = 4892735) B4892735
theorem B3054287 : Blo 1809606 3054287 := bstep (se 1 (by rfl) ⟨2290715, by rfl⟩ : syracuseStep 3054287 = 4581431) B4581431
theorem B6527785 : Blo 1809606 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B52894657 : Blo 1809606 52894657 := bstep (se 2 (by rfl) ⟨19835496, by rfl⟩ : syracuseStep 52894657 = 39670993) B39670993
theorem B6110315 : Blo 1809606 6110315 := bstep (se 1 (by rfl) ⟨4582736, by rfl⟩ : syracuseStep 6110315 = 9165473) B9165473
theorem B4349089 : Blo 1809606 4349089 := bstep (se 2 (by rfl) ⟨1630908, by rfl⟩ : syracuseStep 4349089 = 3261817) B3261817
theorem B6110369 : Blo 1809606 6110369 := bstep (se 2 (by rfl) ⟨2291388, by rfl⟩ : syracuseStep 6110369 = 4582777) B4582777
theorem B4709639 : Blo 1809606 4709639 := bstep (se 1 (by rfl) ⟨3532229, by rfl⟩ : syracuseStep 4709639 = 7064459) B7064459
theorem B1810171 : Blo 1809606 1810171 := bstep (se 1 (by rfl) ⟨1357628, by rfl⟩ : syracuseStep 1810171 = 2715257) B2715257
theorem B33038225 : Blo 1809606 33038225 := bstep (se 2 (by rfl) ⟨12389334, by rfl⟩ : syracuseStep 33038225 = 24778669) B24778669
theorem B334405559 : Blo 1809606 334405559 := bstep (se 1 (by rfl) ⟨250804169, by rfl⟩ : syracuseStep 334405559 = 501608339) B501608339
theorem B30932927 : Blo 1809606 30932927 := bstep (se 1 (by rfl) ⟨23199695, by rfl⟩ : syracuseStep 30932927 = 46399391) B46399391
theorem B1810759 : Blo 1809606 1810759 := bstep (se 1 (by rfl) ⟨1358069, by rfl⟩ : syracuseStep 1810759 = 2716139) B2716139
theorem B9790055 : Blo 1809606 9790055 := bstep (se 1 (by rfl) ⟨7342541, by rfl⟩ : syracuseStep 9790055 = 14685083) B14685083
theorem B3261161 : Blo 1809606 3261161 := bstep (se 2 (by rfl) ⟨1222935, by rfl⟩ : syracuseStep 3261161 = 2445871) B2445871
theorem B1811199 : Blo 1809606 1811199 := bstep (se 1 (by rfl) ⟨1358399, by rfl⟩ : syracuseStep 1811199 = 2716799) B2716799
theorem B1811263 : Blo 1809606 1811263 := bstep (se 1 (by rfl) ⟨1358447, by rfl⟩ : syracuseStep 1811263 = 2716895) B2716895
theorem B70526209 : Blo 1809606 70526209 := bstep (se 2 (by rfl) ⟨26447328, by rfl⟩ : syracuseStep 70526209 = 52894657) B52894657
theorem B15467831 : Blo 1809606 15467831 := bstep (se 1 (by rfl) ⟨11600873, by rfl⟩ : syracuseStep 15467831 = 23201747) B23201747
theorem B4073543 : Blo 1809606 4073543 := bstep (se 1 (by rfl) ⟨3055157, by rfl⟩ : syracuseStep 4073543 = 6110315) B6110315
theorem B4073579 : Blo 1809606 4073579 := bstep (se 1 (by rfl) ⟨3055184, by rfl⟩ : syracuseStep 4073579 = 6110369) B6110369
theorem B3139759 : Blo 1809606 3139759 := bstep (se 1 (by rfl) ⟨2354819, by rfl⟩ : syracuseStep 3139759 = 4709639) B4709639
theorem B20621951 : Blo 1809606 20621951 := bstep (se 1 (by rfl) ⟨15466463, by rfl⟩ : syracuseStep 20621951 = 30932927) B30932927
theorem B4582241 : Blo 1809606 4582241 := bstep (se 2 (by rfl) ⟨1718340, by rfl⟩ : syracuseStep 4582241 = 3436681) B3436681
theorem B10317401 : Blo 1809606 10317401 := bstep (se 2 (by rfl) ⟨3869025, by rfl⟩ : syracuseStep 10317401 = 7738051) B7738051
theorem B4075145 : Blo 1809606 4075145 := bstep (se 2 (by rfl) ⟨1528179, by rfl⟩ : syracuseStep 4075145 = 3056359) B3056359
theorem B74329775 : Blo 1809606 74329775 := bstep (se 1 (by rfl) ⟨55747331, by rfl⟩ : syracuseStep 74329775 = 111494663) B111494663
theorem B8703713 : Blo 1809606 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B2715419 : Blo 1809606 2715419 := bstep (se 1 (by rfl) ⟨2036564, by rfl⟩ : syracuseStep 2715419 = 4073129) B4073129
theorem B4075433 : Blo 1809606 4075433 := bstep (se 2 (by rfl) ⟨1528287, by rfl⟩ : syracuseStep 4075433 = 3056575) B3056575
theorem B76386341 : Blo 1809606 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B4583699 : Blo 1809606 4583699 := bstep (se 1 (by rfl) ⟨3437774, by rfl⟩ : syracuseStep 4583699 = 6875549) B6875549
theorem B2716025 : Blo 1809606 2716025 := bstep (se 2 (by rfl) ⟨1018509, by rfl⟩ : syracuseStep 2716025 = 2037019) B2037019
theorem B6107615 : Blo 1809606 6107615 := bstep (se 1 (by rfl) ⟨4580711, by rfl⟩ : syracuseStep 6107615 = 9161423) B9161423
theorem B2036191 : Blo 1809606 2036191 := bstep (se 1 (by rfl) ⟨1527143, by rfl⟩ : syracuseStep 2036191 = 3054287) B3054287
theorem B2716367 : Blo 1809606 2716367 := bstep (se 1 (by rfl) ⟨2037275, by rfl⟩ : syracuseStep 2716367 = 4074551) B4074551
theorem B2716487 : Blo 1809606 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B2716775 : Blo 1809606 2716775 := bstep (se 1 (by rfl) ⟨2037581, by rfl⟩ : syracuseStep 2716775 = 4075163) B4075163
theorem B2716907 : Blo 1809606 2716907 := bstep (se 1 (by rfl) ⟨2037680, by rfl⟩ : syracuseStep 2716907 = 4075361) B4075361
theorem B22025483 : Blo 1809606 22025483 := bstep (se 1 (by rfl) ⟨16519112, by rfl⟩ : syracuseStep 22025483 = 33038225) B33038225
theorem B14882125 : Blo 1809606 14882125 := bstep (se 3 (by rfl) ⟨2790398, by rfl⟩ : syracuseStep 14882125 = 5580797) B5580797
theorem B9287081 : Blo 1809606 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B2717159 : Blo 1809606 2717159 := bstep (se 1 (by rfl) ⟨2037869, by rfl⟩ : syracuseStep 2717159 = 4075739) B4075739
theorem B5224351 : Blo 1809606 5224351 := bstep (se 1 (by rfl) ⟨3918263, by rfl⟩ : syracuseStep 5224351 = 7836527) B7836527
theorem B15464519 : Blo 1809606 15464519 := bstep (se 1 (by rfl) ⟨11598389, by rfl⟩ : syracuseStep 15464519 = 23196779) B23196779
theorem B8698195 : Blo 1809606 8698195 := bstep (se 1 (by rfl) ⟨6523646, by rfl⟩ : syracuseStep 8698195 = 13047293) B13047293
theorem B19585475 : Blo 1809606 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B5798785 : Blo 1809606 5798785 := bstep (se 2 (by rfl) ⟨2174544, by rfl⟩ : syracuseStep 5798785 = 4349089) B4349089
theorem B1809647 : Blo 1809606 1809647 := bstep (se 1 (by rfl) ⟨1357235, by rfl⟩ : syracuseStep 1809647 = 2714471) B2714471
theorem B1810367 : Blo 1809606 1810367 := bstep (se 1 (by rfl) ⟨1357775, by rfl⟩ : syracuseStep 1810367 = 2715551) B2715551
theorem B222937039 : Blo 1809606 222937039 := bstep (se 1 (by rfl) ⟨167202779, by rfl⟩ : syracuseStep 222937039 = 334405559) B334405559
theorem B3055799 : Blo 1809606 3055799 := bstep (se 1 (by rfl) ⟨2291849, by rfl⟩ : syracuseStep 3055799 = 4583699) B4583699
theorem B1810683 : Blo 1809606 1810683 := bstep (se 1 (by rfl) ⟨1358012, by rfl⟩ : syracuseStep 1810683 = 2716025) B2716025
theorem B4071743 : Blo 1809606 4071743 := bstep (se 1 (by rfl) ⟨3053807, by rfl⟩ : syracuseStep 4071743 = 6107615) B6107615
theorem B1810911 : Blo 1809606 1810911 := bstep (se 1 (by rfl) ⟨1358183, by rfl⟩ : syracuseStep 1810911 = 2716367) B2716367
theorem B1810991 : Blo 1809606 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B1811183 : Blo 1809606 1811183 := bstep (se 1 (by rfl) ⟨1358387, by rfl⟩ : syracuseStep 1811183 = 2716775) B2716775
theorem B1811271 : Blo 1809606 1811271 := bstep (se 1 (by rfl) ⟨1358453, by rfl⟩ : syracuseStep 1811271 = 2716907) B2716907
theorem B16745381 : Blo 1809606 16745381 := bstep (se 4 (by rfl) ⟨1569879, by rfl⟩ : syracuseStep 16745381 = 3139759) B3139759
theorem B1811439 : Blo 1809606 1811439 := bstep (se 1 (by rfl) ⟨1358579, by rfl⟩ : syracuseStep 1811439 = 2717159) B2717159
theorem B13747967 : Blo 1809606 13747967 := bstep (se 1 (by rfl) ⟨10310975, by rfl⟩ : syracuseStep 13747967 = 20621951) B20621951
theorem B19842833 : Blo 1809606 19842833 := bstep (se 2 (by rfl) ⟨7441062, by rfl⟩ : syracuseStep 19842833 = 14882125) B14882125
theorem B23209901 : Blo 1809606 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B6965801 : Blo 1809606 6965801 := bstep (se 2 (by rfl) ⟨2612175, by rfl⟩ : syracuseStep 6965801 = 5224351) B5224351
theorem B297249385 : Blo 1809606 297249385 := bstep (se 2 (by rfl) ⟨111468519, by rfl⟩ : syracuseStep 297249385 = 222937039) B222937039
theorem B50924227 : Blo 1809606 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B2714921 : Blo 1809606 2714921 := bstep (se 2 (by rfl) ⟨1018095, by rfl⟩ : syracuseStep 2714921 = 2036191) B2036191
theorem B14683655 : Blo 1809606 14683655 := bstep (se 1 (by rfl) ⟨11012741, by rfl⟩ : syracuseStep 14683655 = 22025483) B22025483
theorem B10309679 : Blo 1809606 10309679 := bstep (se 1 (by rfl) ⟨7732259, by rfl⟩ : syracuseStep 10309679 = 15464519) B15464519
theorem B2715695 : Blo 1809606 2715695 := bstep (se 1 (by rfl) ⟨2036771, by rfl⟩ : syracuseStep 2715695 = 4073543) B4073543
theorem B2715719 : Blo 1809606 2715719 := bstep (se 1 (by rfl) ⟨2036789, by rfl⟩ : syracuseStep 2715719 = 4073579) B4073579
theorem B8696429 : Blo 1809606 8696429 := bstep (se 3 (by rfl) ⟨1630580, by rfl⟩ : syracuseStep 8696429 = 3261161) B3261161
theorem B6878267 : Blo 1809606 6878267 := bstep (se 1 (by rfl) ⟨5158700, by rfl⟩ : syracuseStep 6878267 = 10317401) B10317401
theorem B2716763 : Blo 1809606 2716763 := bstep (se 1 (by rfl) ⟨2037572, by rfl⟩ : syracuseStep 2716763 = 4075145) B4075145
theorem B2716955 : Blo 1809606 2716955 := bstep (se 1 (by rfl) ⟨2037716, by rfl⟩ : syracuseStep 2716955 = 4075433) B4075433
theorem B6526703 : Blo 1809606 6526703 := bstep (se 1 (by rfl) ⟨4895027, by rfl⟩ : syracuseStep 6526703 = 9790055) B9790055
theorem B11597593 : Blo 1809606 11597593 := bstep (se 2 (by rfl) ⟨4349097, by rfl⟩ : syracuseStep 11597593 = 8698195) B8698195
theorem B10311887 : Blo 1809606 10311887 := bstep (se 1 (by rfl) ⟨7733915, by rfl⟩ : syracuseStep 10311887 = 15467831) B15467831
theorem B6191387 : Blo 1809606 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B7731713 : Blo 1809606 7731713 := bstep (se 2 (by rfl) ⟨2899392, by rfl⟩ : syracuseStep 7731713 = 5798785) B5798785
theorem B13056983 : Blo 1809606 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B94034945 : Blo 1809606 94034945 := bstep (se 2 (by rfl) ⟨35263104, by rfl⟩ : syracuseStep 94034945 = 70526209) B70526209
theorem B3054827 : Blo 1809606 3054827 := bstep (se 1 (by rfl) ⟨2291120, by rfl⟩ : syracuseStep 3054827 = 4582241) B4582241
theorem B49553183 : Blo 1809606 49553183 := bstep (se 1 (by rfl) ⟨37164887, by rfl⟩ : syracuseStep 49553183 = 74329775) B74329775
theorem B1810279 : Blo 1809606 1810279 := bstep (se 1 (by rfl) ⟨1357709, by rfl⟩ : syracuseStep 1810279 = 2715419) B2715419
theorem B6873119 : Blo 1809606 6873119 := bstep (se 1 (by rfl) ⟨5154839, by rfl⟩ : syracuseStep 6873119 = 10309679) B10309679
theorem B1810463 : Blo 1809606 1810463 := bstep (se 1 (by rfl) ⟨1357847, by rfl⟩ : syracuseStep 1810463 = 2715695) B2715695
theorem B1810479 : Blo 1809606 1810479 := bstep (se 1 (by rfl) ⟨1357859, by rfl⟩ : syracuseStep 1810479 = 2715719) B2715719
theorem B1811175 : Blo 1809606 1811175 := bstep (se 1 (by rfl) ⟨1358381, by rfl⟩ : syracuseStep 1811175 = 2716763) B2716763
theorem B1811303 : Blo 1809606 1811303 := bstep (se 1 (by rfl) ⟨1358477, by rfl⟩ : syracuseStep 1811303 = 2716955) B2716955
theorem B6874591 : Blo 1809606 6874591 := bstep (se 1 (by rfl) ⟨5155943, by rfl⟩ : syracuseStep 6874591 = 10311887) B10311887
theorem B5154475 : Blo 1809606 5154475 := bstep (se 1 (by rfl) ⟨3865856, by rfl⟩ : syracuseStep 5154475 = 7731713) B7731713
theorem B2714495 : Blo 1809606 2714495 := bstep (se 1 (by rfl) ⟨2035871, by rfl⟩ : syracuseStep 2714495 = 4071743) B4071743
theorem B396332513 : Blo 1809606 396332513 := bstep (se 2 (by rfl) ⟨148624692, by rfl⟩ : syracuseStep 396332513 = 297249385) B297249385
theorem B67898969 : Blo 1809606 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B17404541 : Blo 1809606 17404541 := bstep (se 3 (by rfl) ⟨3263351, by rfl⟩ : syracuseStep 17404541 = 6526703) B6526703
theorem B8704655 : Blo 1809606 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B62689963 : Blo 1809606 62689963 := bstep (se 1 (by rfl) ⟨47017472, by rfl⟩ : syracuseStep 62689963 = 94034945) B94034945
theorem B2036551 : Blo 1809606 2036551 := bstep (se 1 (by rfl) ⟨1527413, by rfl⟩ : syracuseStep 2036551 = 3054827) B3054827
theorem B15463457 : Blo 1809606 15463457 := bstep (se 2 (by rfl) ⟨5798796, by rfl⟩ : syracuseStep 15463457 = 11597593) B11597593
theorem B33035455 : Blo 1809606 33035455 := bstep (se 1 (by rfl) ⟨24776591, by rfl⟩ : syracuseStep 33035455 = 49553183) B49553183
theorem B2037199 : Blo 1809606 2037199 := bstep (se 1 (by rfl) ⟨1527899, by rfl⟩ : syracuseStep 2037199 = 3055799) B3055799
theorem B5797619 : Blo 1809606 5797619 := bstep (se 1 (by rfl) ⟨4348214, by rfl⟩ : syracuseStep 5797619 = 8696429) B8696429
theorem B11163587 : Blo 1809606 11163587 := bstep (se 1 (by rfl) ⟨8372690, by rfl⟩ : syracuseStep 11163587 = 16745381) B16745381
theorem B4585511 : Blo 1809606 4585511 := bstep (se 1 (by rfl) ⟨3439133, by rfl⟩ : syracuseStep 4585511 = 6878267) B6878267
theorem B9165311 : Blo 1809606 9165311 := bstep (se 1 (by rfl) ⟨6873983, by rfl⟩ : syracuseStep 9165311 = 13747967) B13747967
theorem B13228555 : Blo 1809606 13228555 := bstep (se 1 (by rfl) ⟨9921416, by rfl⟩ : syracuseStep 13228555 = 19842833) B19842833
theorem B15473267 : Blo 1809606 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B4127591 : Blo 1809606 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B4643867 : Blo 1809606 4643867 := bstep (se 1 (by rfl) ⟨3482900, by rfl⟩ : syracuseStep 4643867 = 6965801) B6965801
theorem B1809947 : Blo 1809606 1809947 := bstep (se 1 (by rfl) ⟨1357460, by rfl⟩ : syracuseStep 1809947 = 2714921) B2714921
theorem B9789103 : Blo 1809606 9789103 := bstep (se 1 (by rfl) ⟨7341827, by rfl⟩ : syracuseStep 9789103 = 14683655) B14683655
theorem B17638073 : Blo 1809606 17638073 := bstep (se 2 (by rfl) ⟨6614277, by rfl⟩ : syracuseStep 17638073 = 13228555) B13228555
theorem B3057007 : Blo 1809606 3057007 := bstep (se 1 (by rfl) ⟨2292755, by rfl⟩ : syracuseStep 3057007 = 4585511) B4585511
theorem B10315511 : Blo 1809606 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B13052137 : Blo 1809606 13052137 := bstep (se 2 (by rfl) ⟨4894551, by rfl⟩ : syracuseStep 13052137 = 9789103) B9789103
theorem B4582079 : Blo 1809606 4582079 := bstep (se 1 (by rfl) ⟨3436559, by rfl⟩ : syracuseStep 4582079 = 6873119) B6873119
theorem B11603027 : Blo 1809606 11603027 := bstep (se 1 (by rfl) ⟨8702270, by rfl⟩ : syracuseStep 11603027 = 17404541) B17404541
theorem B5803103 : Blo 1809606 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B10308971 : Blo 1809606 10308971 := bstep (se 1 (by rfl) ⟨7731728, by rfl⟩ : syracuseStep 10308971 = 15463457) B15463457
theorem B83586617 : Blo 1809606 83586617 := bstep (se 2 (by rfl) ⟨31344981, by rfl⟩ : syracuseStep 83586617 = 62689963) B62689963
theorem B2715401 : Blo 1809606 2715401 := bstep (se 2 (by rfl) ⟨1018275, by rfl⟩ : syracuseStep 2715401 = 2036551) B2036551
theorem B2716265 : Blo 1809606 2716265 := bstep (se 2 (by rfl) ⟨1018599, by rfl⟩ : syracuseStep 2716265 = 2037199) B2037199
theorem B264221675 : Blo 1809606 264221675 := bstep (se 1 (by rfl) ⟨198166256, by rfl⟩ : syracuseStep 264221675 = 396332513) B396332513
theorem B45265979 : Blo 1809606 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B3865079 : Blo 1809606 3865079 := bstep (se 1 (by rfl) ⟨2898809, by rfl⟩ : syracuseStep 3865079 = 5797619) B5797619
theorem B44047273 : Blo 1809606 44047273 := bstep (se 2 (by rfl) ⟨16517727, by rfl⟩ : syracuseStep 44047273 = 33035455) B33035455
theorem B6110207 : Blo 1809606 6110207 := bstep (se 1 (by rfl) ⟨4582655, by rfl⟩ : syracuseStep 6110207 = 9165311) B9165311
theorem B2751727 : Blo 1809606 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B1809663 : Blo 1809606 1809663 := bstep (se 1 (by rfl) ⟨1357247, by rfl⟩ : syracuseStep 1809663 = 2714495) B2714495
theorem B9166121 : Blo 1809606 9166121 := bstep (se 2 (by rfl) ⟨3437295, by rfl⟩ : syracuseStep 9166121 = 6874591) B6874591
theorem B3095911 : Blo 1809606 3095911 := bstep (se 1 (by rfl) ⟨2321933, by rfl⟩ : syracuseStep 3095911 = 4643867) B4643867
theorem B6872633 : Blo 1809606 6872633 := bstep (se 2 (by rfl) ⟨2577237, by rfl⟩ : syracuseStep 6872633 = 5154475) B5154475
theorem B29769565 : Blo 1809606 29769565 := bstep (se 3 (by rfl) ⟨5581793, by rfl⟩ : syracuseStep 29769565 = 11163587) B11163587
theorem B1810843 : Blo 1809606 1810843 := bstep (se 1 (by rfl) ⟨1358132, by rfl⟩ : syracuseStep 1810843 = 2716265) B2716265
theorem B58729697 : Blo 1809606 58729697 := bstep (se 2 (by rfl) ⟨22023636, by rfl⟩ : syracuseStep 58729697 = 44047273) B44047273
theorem B4073471 : Blo 1809606 4073471 := bstep (se 1 (by rfl) ⟨3055103, by rfl⟩ : syracuseStep 4073471 = 6110207) B6110207
theorem B7735351 : Blo 1809606 7735351 := bstep (se 1 (by rfl) ⟨5801513, by rfl⟩ : syracuseStep 7735351 = 11603027) B11603027
theorem B3868735 : Blo 1809606 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B55724411 : Blo 1809606 55724411 := bstep (se 1 (by rfl) ⟨41793308, by rfl⟩ : syracuseStep 55724411 = 83586617) B83586617
theorem B4581755 : Blo 1809606 4581755 := bstep (se 1 (by rfl) ⟨3436316, by rfl⟩ : syracuseStep 4581755 = 6872633) B6872633
theorem B39692753 : Blo 1809606 39692753 := bstep (se 2 (by rfl) ⟨14884782, by rfl⟩ : syracuseStep 39692753 = 29769565) B29769565
theorem B17402849 : Blo 1809606 17402849 := bstep (se 2 (by rfl) ⟨6526068, by rfl⟩ : syracuseStep 17402849 = 13052137) B13052137
theorem B11758715 : Blo 1809606 11758715 := bstep (se 1 (by rfl) ⟨8819036, by rfl⟩ : syracuseStep 11758715 = 17638073) B17638073
theorem B176147783 : Blo 1809606 176147783 := bstep (se 1 (by rfl) ⟨132110837, by rfl⟩ : syracuseStep 176147783 = 264221675) B264221675
theorem B6877007 : Blo 1809606 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2576719 : Blo 1809606 2576719 := bstep (se 1 (by rfl) ⟨1932539, by rfl⟩ : syracuseStep 2576719 = 3865079) B3865079
theorem B4076009 : Blo 1809606 4076009 := bstep (se 2 (by rfl) ⟨1528503, by rfl⟩ : syracuseStep 4076009 = 3057007) B3057007
theorem B30177319 : Blo 1809606 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B3668969 : Blo 1809606 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B3054719 : Blo 1809606 3054719 := bstep (se 1 (by rfl) ⟨2291039, by rfl⟩ : syracuseStep 3054719 = 4582079) B4582079
theorem B4127881 : Blo 1809606 4127881 := bstep (se 2 (by rfl) ⟨1547955, by rfl⟩ : syracuseStep 4127881 = 3095911) B3095911
theorem B6110747 : Blo 1809606 6110747 := bstep (se 1 (by rfl) ⟨4583060, by rfl⟩ : syracuseStep 6110747 = 9166121) B9166121
theorem B6872647 : Blo 1809606 6872647 := bstep (se 1 (by rfl) ⟨5154485, by rfl⟩ : syracuseStep 6872647 = 10308971) B10308971
theorem B1810267 : Blo 1809606 1810267 := bstep (se 1 (by rfl) ⟨1357700, by rfl⟩ : syracuseStep 1810267 = 2715401) B2715401
theorem B10313801 : Blo 1809606 10313801 := bstep (se 2 (by rfl) ⟨3867675, by rfl⟩ : syracuseStep 10313801 = 7735351) B7735351
theorem B26461835 : Blo 1809606 26461835 := bstep (se 1 (by rfl) ⟨19846376, by rfl⟩ : syracuseStep 26461835 = 39692753) B39692753
theorem B11601899 : Blo 1809606 11601899 := bstep (se 1 (by rfl) ⟨8701424, by rfl⟩ : syracuseStep 11601899 = 17402849) B17402849
theorem B4073831 : Blo 1809606 4073831 := bstep (se 1 (by rfl) ⟨3055373, by rfl⟩ : syracuseStep 4073831 = 6110747) B6110747
theorem B3435625 : Blo 1809606 3435625 := bstep (se 2 (by rfl) ⟨1288359, by rfl⟩ : syracuseStep 3435625 = 2576719) B2576719
theorem B39153131 : Blo 1809606 39153131 := bstep (se 1 (by rfl) ⟨29364848, by rfl⟩ : syracuseStep 39153131 = 58729697) B58729697
theorem B2715647 : Blo 1809606 2715647 := bstep (se 1 (by rfl) ⟨2036735, by rfl⟩ : syracuseStep 2715647 = 4073471) B4073471
theorem B2445979 : Blo 1809606 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B2036479 : Blo 1809606 2036479 := bstep (se 1 (by rfl) ⟨1527359, by rfl⟩ : syracuseStep 2036479 = 3054719) B3054719
theorem B9163529 : Blo 1809606 9163529 := bstep (se 2 (by rfl) ⟨3436323, by rfl⟩ : syracuseStep 9163529 = 6872647) B6872647
theorem B4584671 : Blo 1809606 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B40236425 : Blo 1809606 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B5158313 : Blo 1809606 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B2717339 : Blo 1809606 2717339 := bstep (se 1 (by rfl) ⟨2038004, by rfl⟩ : syracuseStep 2717339 = 4076009) B4076009
theorem B5503841 : Blo 1809606 5503841 := bstep (se 2 (by rfl) ⟨2063940, by rfl⟩ : syracuseStep 5503841 = 4127881) B4127881
theorem B37149607 : Blo 1809606 37149607 := bstep (se 1 (by rfl) ⟨27862205, by rfl⟩ : syracuseStep 37149607 = 55724411) B55724411
theorem B3054503 : Blo 1809606 3054503 := bstep (se 1 (by rfl) ⟨2290877, by rfl⟩ : syracuseStep 3054503 = 4581755) B4581755
theorem B7839143 : Blo 1809606 7839143 := bstep (se 1 (by rfl) ⟨5879357, by rfl⟩ : syracuseStep 7839143 = 11758715) B11758715
theorem B117431855 : Blo 1809606 117431855 := bstep (se 1 (by rfl) ⟨88073891, by rfl⟩ : syracuseStep 117431855 = 176147783) B176147783
theorem B3056447 : Blo 1809606 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B3261305 : Blo 1809606 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B1811559 : Blo 1809606 1811559 := bstep (se 1 (by rfl) ⟨1358669, by rfl⟩ : syracuseStep 1811559 = 2717339) B2717339
theorem B7734599 : Blo 1809606 7734599 := bstep (se 1 (by rfl) ⟨5800949, by rfl⟩ : syracuseStep 7734599 = 11601899) B11601899
theorem B4580833 : Blo 1809606 4580833 := bstep (se 2 (by rfl) ⟨1717812, by rfl⟩ : syracuseStep 4580833 = 3435625) B3435625
theorem B26102087 : Blo 1809606 26102087 := bstep (se 1 (by rfl) ⟨19576565, by rfl⟩ : syracuseStep 26102087 = 39153131) B39153131
theorem B6875867 : Blo 1809606 6875867 := bstep (se 1 (by rfl) ⟨5156900, by rfl⟩ : syracuseStep 6875867 = 10313801) B10313801
theorem B26824283 : Blo 1809606 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B2715305 : Blo 1809606 2715305 := bstep (se 2 (by rfl) ⟨1018239, by rfl⟩ : syracuseStep 2715305 = 2036479) B2036479
theorem B17641223 : Blo 1809606 17641223 := bstep (se 1 (by rfl) ⟨13230917, by rfl⟩ : syracuseStep 17641223 = 26461835) B26461835
theorem B49532809 : Blo 1809606 49532809 := bstep (se 2 (by rfl) ⟨18574803, by rfl⟩ : syracuseStep 49532809 = 37149607) B37149607
theorem B2715887 : Blo 1809606 2715887 := bstep (se 1 (by rfl) ⟨2036915, by rfl⟩ : syracuseStep 2715887 = 4073831) B4073831
theorem B2036335 : Blo 1809606 2036335 := bstep (se 1 (by rfl) ⟨1527251, by rfl⟩ : syracuseStep 2036335 = 3054503) B3054503
theorem B78287903 : Blo 1809606 78287903 := bstep (se 1 (by rfl) ⟨58715927, by rfl⟩ : syracuseStep 78287903 = 117431855) B117431855
theorem B6109019 : Blo 1809606 6109019 := bstep (se 1 (by rfl) ⟨4581764, by rfl⟩ : syracuseStep 6109019 = 9163529) B9163529
theorem B3438875 : Blo 1809606 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B3669227 : Blo 1809606 3669227 := bstep (se 1 (by rfl) ⟨2751920, by rfl⟩ : syracuseStep 3669227 = 5503841) B5503841
theorem B5226095 : Blo 1809606 5226095 := bstep (se 1 (by rfl) ⟨3919571, by rfl⟩ : syracuseStep 5226095 = 7839143) B7839143
theorem B1810431 : Blo 1809606 1810431 := bstep (se 1 (by rfl) ⟨1357823, by rfl⟩ : syracuseStep 1810431 = 2715647) B2715647
theorem B1810591 : Blo 1809606 1810591 := bstep (se 1 (by rfl) ⟨1357943, by rfl⟩ : syracuseStep 1810591 = 2715887) B2715887
theorem B52191935 : Blo 1809606 52191935 := bstep (se 1 (by rfl) ⟨39143951, by rfl⟩ : syracuseStep 52191935 = 78287903) B78287903
theorem B4072679 : Blo 1809606 4072679 := bstep (se 1 (by rfl) ⟨3054509, by rfl⟩ : syracuseStep 4072679 = 6109019) B6109019
theorem B17401391 : Blo 1809606 17401391 := bstep (se 1 (by rfl) ⟨13051043, by rfl⟩ : syracuseStep 17401391 = 26102087) B26102087
theorem B3484063 : Blo 1809606 3484063 := bstep (se 1 (by rfl) ⟨2613047, by rfl⟩ : syracuseStep 3484063 = 5226095) B5226095
theorem B2174203 : Blo 1809606 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B9170333 : Blo 1809606 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B2715113 : Blo 1809606 2715113 := bstep (se 2 (by rfl) ⟨1018167, by rfl⟩ : syracuseStep 2715113 = 2036335) B2036335
theorem B5156399 : Blo 1809606 5156399 := bstep (se 1 (by rfl) ⟨3867299, by rfl⟩ : syracuseStep 5156399 = 7734599) B7734599
theorem B4583911 : Blo 1809606 4583911 := bstep (se 1 (by rfl) ⟨3437933, by rfl⟩ : syracuseStep 4583911 = 6875867) B6875867
theorem B6107777 : Blo 1809606 6107777 := bstep (se 2 (by rfl) ⟨2290416, by rfl⟩ : syracuseStep 6107777 = 4580833) B4580833
theorem B2446151 : Blo 1809606 2446151 := bstep (se 1 (by rfl) ⟨1834613, by rfl⟩ : syracuseStep 2446151 = 3669227) B3669227
theorem B11760815 : Blo 1809606 11760815 := bstep (se 1 (by rfl) ⟨8820611, by rfl⟩ : syracuseStep 11760815 = 17641223) B17641223
theorem B2037631 : Blo 1809606 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B17882855 : Blo 1809606 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B1810203 : Blo 1809606 1810203 := bstep (se 1 (by rfl) ⟨1357652, by rfl⟩ : syracuseStep 1810203 = 2715305) B2715305
theorem B66043745 : Blo 1809606 66043745 := bstep (se 2 (by rfl) ⟨24766404, by rfl⟩ : syracuseStep 66043745 = 49532809) B49532809
theorem B4071851 : Blo 1809606 4071851 := bstep (se 1 (by rfl) ⟨3053888, by rfl⟩ : syracuseStep 4071851 = 6107777) B6107777
theorem B6111881 : Blo 1809606 6111881 := bstep (se 2 (by rfl) ⟨2291955, by rfl⟩ : syracuseStep 6111881 = 4583911) B4583911
theorem B26092277 : Blo 1809606 26092277 := bstep (se 5 (by rfl) ⟨1223075, by rfl⟩ : syracuseStep 26092277 = 2446151) B2446151
theorem B11600927 : Blo 1809606 11600927 := bstep (se 1 (by rfl) ⟨8700695, by rfl⟩ : syracuseStep 11600927 = 17401391) B17401391
theorem B18581669 : Blo 1809606 18581669 := bstep (se 4 (by rfl) ⟨1742031, by rfl⟩ : syracuseStep 18581669 = 3484063) B3484063
theorem B6113555 : Blo 1809606 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B11921903 : Blo 1809606 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B31362173 : Blo 1809606 31362173 := bstep (se 3 (by rfl) ⟨5880407, by rfl⟩ : syracuseStep 31362173 = 11760815) B11760815
theorem B34794623 : Blo 1809606 34794623 := bstep (se 1 (by rfl) ⟨26095967, by rfl⟩ : syracuseStep 34794623 = 52191935) B52191935
theorem B2715119 : Blo 1809606 2715119 := bstep (se 1 (by rfl) ⟨2036339, by rfl⟩ : syracuseStep 2715119 = 4072679) B4072679
theorem B13750397 : Blo 1809606 13750397 := bstep (se 3 (by rfl) ⟨2578199, by rfl⟩ : syracuseStep 13750397 = 5156399) B5156399
theorem B2716841 : Blo 1809606 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B44029163 : Blo 1809606 44029163 := bstep (se 1 (by rfl) ⟨33021872, by rfl⟩ : syracuseStep 44029163 = 66043745) B66043745
theorem B2898937 : Blo 1809606 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B1810075 : Blo 1809606 1810075 := bstep (se 1 (by rfl) ⟨1357556, by rfl⟩ : syracuseStep 1810075 = 2715113) B2715113
theorem B9166931 : Blo 1809606 9166931 := bstep (se 1 (by rfl) ⟨6875198, by rfl⟩ : syracuseStep 9166931 = 13750397) B13750397
theorem B7733951 : Blo 1809606 7733951 := bstep (se 1 (by rfl) ⟨5800463, by rfl⟩ : syracuseStep 7733951 = 11600927) B11600927
theorem B1811227 : Blo 1809606 1811227 := bstep (se 1 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 1811227 = 2716841) B2716841
theorem B29352775 : Blo 1809606 29352775 := bstep (se 1 (by rfl) ⟨22014581, by rfl⟩ : syracuseStep 29352775 = 44029163) B44029163
theorem B12387779 : Blo 1809606 12387779 := bstep (se 1 (by rfl) ⟨9290834, by rfl⟩ : syracuseStep 12387779 = 18581669) B18581669
theorem B7947935 : Blo 1809606 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B20908115 : Blo 1809606 20908115 := bstep (se 1 (by rfl) ⟨15681086, by rfl⟩ : syracuseStep 20908115 = 31362173) B31362173
theorem B2714567 : Blo 1809606 2714567 := bstep (se 1 (by rfl) ⟨2035925, by rfl⟩ : syracuseStep 2714567 = 4071851) B4071851
theorem B4074587 : Blo 1809606 4074587 := bstep (se 1 (by rfl) ⟨3055940, by rfl⟩ : syracuseStep 4074587 = 6111881) B6111881
theorem B17394851 : Blo 1809606 17394851 := bstep (se 1 (by rfl) ⟨13046138, by rfl⟩ : syracuseStep 17394851 = 26092277) B26092277
theorem B4075703 : Blo 1809606 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B23196415 : Blo 1809606 23196415 := bstep (se 1 (by rfl) ⟨17397311, by rfl⟩ : syracuseStep 23196415 = 34794623) B34794623
theorem B3865249 : Blo 1809606 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B1810079 : Blo 1809606 1810079 := bstep (se 1 (by rfl) ⟨1357559, by rfl⟩ : syracuseStep 1810079 = 2715119) B2715119
theorem B6111287 : Blo 1809606 6111287 := bstep (se 1 (by rfl) ⟨4583465, by rfl⟩ : syracuseStep 6111287 = 9166931) B9166931
theorem B8258519 : Blo 1809606 8258519 := bstep (se 1 (by rfl) ⟨6193889, by rfl⟩ : syracuseStep 8258519 = 12387779) B12387779
theorem B46386269 : Blo 1809606 46386269 := bstep (se 3 (by rfl) ⟨8697425, by rfl⟩ : syracuseStep 46386269 = 17394851) B17394851
theorem B5155967 : Blo 1809606 5155967 := bstep (se 1 (by rfl) ⟨3866975, by rfl⟩ : syracuseStep 5155967 = 7733951) B7733951
theorem B20614661 : Blo 1809606 20614661 := bstep (se 4 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 20614661 = 3865249) B3865249
theorem B30928553 : Blo 1809606 30928553 := bstep (se 2 (by rfl) ⟨11598207, by rfl⟩ : syracuseStep 30928553 = 23196415) B23196415
theorem B39137033 : Blo 1809606 39137033 := bstep (se 2 (by rfl) ⟨14676387, by rfl⟩ : syracuseStep 39137033 = 29352775) B29352775
theorem B13938743 : Blo 1809606 13938743 := bstep (se 1 (by rfl) ⟨10454057, by rfl⟩ : syracuseStep 13938743 = 20908115) B20908115
theorem B2716391 : Blo 1809606 2716391 := bstep (se 1 (by rfl) ⟨2037293, by rfl⟩ : syracuseStep 2716391 = 4074587) B4074587
theorem B2717135 : Blo 1809606 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B5298623 : Blo 1809606 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B1809711 : Blo 1809606 1809711 := bstep (se 1 (by rfl) ⟨1357283, by rfl⟩ : syracuseStep 1809711 = 2714567) B2714567
theorem B1810927 : Blo 1809606 1810927 := bstep (se 1 (by rfl) ⟨1358195, by rfl⟩ : syracuseStep 1810927 = 2716391) B2716391
theorem B5505679 : Blo 1809606 5505679 := bstep (se 1 (by rfl) ⟨4129259, by rfl⟩ : syracuseStep 5505679 = 8258519) B8258519
theorem B1811423 : Blo 1809606 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B3532415 : Blo 1809606 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B4074191 : Blo 1809606 4074191 := bstep (se 1 (by rfl) ⟨3055643, by rfl⟩ : syracuseStep 4074191 = 6111287) B6111287
theorem B9292495 : Blo 1809606 9292495 := bstep (se 1 (by rfl) ⟨6969371, by rfl⟩ : syracuseStep 9292495 = 13938743) B13938743
theorem B3437311 : Blo 1809606 3437311 := bstep (se 1 (by rfl) ⟨2577983, by rfl⟩ : syracuseStep 3437311 = 5155967) B5155967
theorem B13743107 : Blo 1809606 13743107 := bstep (se 1 (by rfl) ⟨10307330, by rfl⟩ : syracuseStep 13743107 = 20614661) B20614661
theorem B30924179 : Blo 1809606 30924179 := bstep (se 1 (by rfl) ⟨23193134, by rfl⟩ : syracuseStep 30924179 = 46386269) B46386269
theorem B20619035 : Blo 1809606 20619035 := bstep (se 1 (by rfl) ⟨15464276, by rfl⟩ : syracuseStep 20619035 = 30928553) B30928553
theorem B26091355 : Blo 1809606 26091355 := bstep (se 1 (by rfl) ⟨19568516, by rfl⟩ : syracuseStep 26091355 = 39137033) B39137033
theorem B7340905 : Blo 1809606 7340905 := bstep (se 2 (by rfl) ⟨2752839, by rfl⟩ : syracuseStep 7340905 = 5505679) B5505679
theorem B9162071 : Blo 1809606 9162071 := bstep (se 1 (by rfl) ⟨6871553, by rfl⟩ : syracuseStep 9162071 = 13743107) B13743107
theorem B12389993 : Blo 1809606 12389993 := bstep (se 2 (by rfl) ⟨4646247, by rfl⟩ : syracuseStep 12389993 = 9292495) B9292495
theorem B4583081 : Blo 1809606 4583081 := bstep (se 2 (by rfl) ⟨1718655, by rfl⟩ : syracuseStep 4583081 = 3437311) B3437311
theorem B37679093 : Blo 1809606 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B2716127 : Blo 1809606 2716127 := bstep (se 1 (by rfl) ⟨2037095, by rfl⟩ : syracuseStep 2716127 = 4074191) B4074191
theorem B20616119 : Blo 1809606 20616119 := bstep (se 1 (by rfl) ⟨15462089, by rfl⟩ : syracuseStep 20616119 = 30924179) B30924179
theorem B34788473 : Blo 1809606 34788473 := bstep (se 2 (by rfl) ⟨13045677, by rfl⟩ : syracuseStep 34788473 = 26091355) B26091355
theorem B13746023 : Blo 1809606 13746023 := bstep (se 1 (by rfl) ⟨10309517, by rfl⟩ : syracuseStep 13746023 = 20619035) B20619035
theorem B1810751 : Blo 1809606 1810751 := bstep (se 1 (by rfl) ⟨1358063, by rfl⟩ : syracuseStep 1810751 = 2716127) B2716127
theorem B23192315 : Blo 1809606 23192315 := bstep (se 1 (by rfl) ⟨17394236, by rfl⟩ : syracuseStep 23192315 = 34788473) B34788473
theorem B8259995 : Blo 1809606 8259995 := bstep (se 1 (by rfl) ⟨6194996, by rfl⟩ : syracuseStep 8259995 = 12389993) B12389993
theorem B25119395 : Blo 1809606 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B6108047 : Blo 1809606 6108047 := bstep (se 1 (by rfl) ⟨4581035, by rfl⟩ : syracuseStep 6108047 = 9162071) B9162071
theorem B9164015 : Blo 1809606 9164015 := bstep (se 1 (by rfl) ⟨6873011, by rfl⟩ : syracuseStep 9164015 = 13746023) B13746023
theorem B13744079 : Blo 1809606 13744079 := bstep (se 1 (by rfl) ⟨10308059, by rfl⟩ : syracuseStep 13744079 = 20616119) B20616119
theorem B9787873 : Blo 1809606 9787873 := bstep (se 2 (by rfl) ⟨3670452, by rfl⟩ : syracuseStep 9787873 = 7340905) B7340905
theorem B3055387 : Blo 1809606 3055387 := bstep (se 1 (by rfl) ⟨2291540, by rfl⟩ : syracuseStep 3055387 = 4583081) B4583081
theorem B4072031 : Blo 1809606 4072031 := bstep (se 1 (by rfl) ⟨3054023, by rfl⟩ : syracuseStep 4072031 = 6108047) B6108047
theorem B13050497 : Blo 1809606 13050497 := bstep (se 2 (by rfl) ⟨4893936, by rfl⟩ : syracuseStep 13050497 = 9787873) B9787873
theorem B16746263 : Blo 1809606 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B4073849 : Blo 1809606 4073849 := bstep (se 2 (by rfl) ⟨1527693, by rfl⟩ : syracuseStep 4073849 = 3055387) B3055387
theorem B15461543 : Blo 1809606 15461543 := bstep (se 1 (by rfl) ⟨11596157, by rfl⟩ : syracuseStep 15461543 = 23192315) B23192315
theorem B9162719 : Blo 1809606 9162719 := bstep (se 1 (by rfl) ⟨6872039, by rfl⟩ : syracuseStep 9162719 = 13744079) B13744079
theorem B6109343 : Blo 1809606 6109343 := bstep (se 1 (by rfl) ⟨4582007, by rfl⟩ : syracuseStep 6109343 = 9164015) B9164015
theorem B22026653 : Blo 1809606 22026653 := bstep (se 3 (by rfl) ⟨4129997, by rfl⟩ : syracuseStep 22026653 = 8259995) B8259995
theorem B8700331 : Blo 1809606 8700331 := bstep (se 1 (by rfl) ⟨6525248, by rfl⟩ : syracuseStep 8700331 = 13050497) B13050497
theorem B4072895 : Blo 1809606 4072895 := bstep (se 1 (by rfl) ⟨3054671, by rfl⟩ : syracuseStep 4072895 = 6109343) B6109343
theorem B10307695 : Blo 1809606 10307695 := bstep (se 1 (by rfl) ⟨7730771, by rfl⟩ : syracuseStep 10307695 = 15461543) B15461543
theorem B2714687 : Blo 1809606 2714687 := bstep (se 1 (by rfl) ⟨2036015, by rfl⟩ : syracuseStep 2714687 = 4072031) B4072031
theorem B2715899 : Blo 1809606 2715899 := bstep (se 1 (by rfl) ⟨2036924, by rfl⟩ : syracuseStep 2715899 = 4073849) B4073849
theorem B14684435 : Blo 1809606 14684435 := bstep (se 1 (by rfl) ⟨11013326, by rfl⟩ : syracuseStep 14684435 = 22026653) B22026653
theorem B6108479 : Blo 1809606 6108479 := bstep (se 1 (by rfl) ⟨4581359, by rfl⟩ : syracuseStep 6108479 = 9162719) B9162719
theorem B11164175 : Blo 1809606 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B1810599 : Blo 1809606 1810599 := bstep (se 1 (by rfl) ⟨1357949, by rfl⟩ : syracuseStep 1810599 = 2715899) B2715899
theorem B9789623 : Blo 1809606 9789623 := bstep (se 1 (by rfl) ⟨7342217, by rfl⟩ : syracuseStep 9789623 = 14684435) B14684435
theorem B11600441 : Blo 1809606 11600441 := bstep (se 2 (by rfl) ⟨4350165, by rfl⟩ : syracuseStep 11600441 = 8700331) B8700331
theorem B4072319 : Blo 1809606 4072319 := bstep (se 1 (by rfl) ⟨3054239, by rfl⟩ : syracuseStep 4072319 = 6108479) B6108479
theorem B2715263 : Blo 1809606 2715263 := bstep (se 1 (by rfl) ⟨2036447, by rfl⟩ : syracuseStep 2715263 = 4072895) B4072895
theorem B7442783 : Blo 1809606 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B13743593 : Blo 1809606 13743593 := bstep (se 2 (by rfl) ⟨5153847, by rfl⟩ : syracuseStep 13743593 = 10307695) B10307695
theorem B1809791 : Blo 1809606 1809791 := bstep (se 1 (by rfl) ⟨1357343, by rfl⟩ : syracuseStep 1809791 = 2714687) B2714687
theorem B7733627 : Blo 1809606 7733627 := bstep (se 1 (by rfl) ⟨5800220, by rfl⟩ : syracuseStep 7733627 = 11600441) B11600441
theorem B2714879 : Blo 1809606 2714879 := bstep (se 1 (by rfl) ⟨2036159, by rfl⟩ : syracuseStep 2714879 = 4072319) B4072319
theorem B9162395 : Blo 1809606 9162395 := bstep (se 1 (by rfl) ⟨6871796, by rfl⟩ : syracuseStep 9162395 = 13743593) B13743593
theorem B6526415 : Blo 1809606 6526415 := bstep (se 1 (by rfl) ⟨4894811, by rfl⟩ : syracuseStep 6526415 = 9789623) B9789623
theorem B4961855 : Blo 1809606 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B1810175 : Blo 1809606 1810175 := bstep (se 1 (by rfl) ⟨1357631, by rfl⟩ : syracuseStep 1810175 = 2715263) B2715263
theorem B4350943 : Blo 1809606 4350943 := bstep (se 1 (by rfl) ⟨3263207, by rfl⟩ : syracuseStep 4350943 = 6526415) B6526415
theorem B13231613 : Blo 1809606 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B5155751 : Blo 1809606 5155751 := bstep (se 1 (by rfl) ⟨3866813, by rfl⟩ : syracuseStep 5155751 = 7733627) B7733627
theorem B6108263 : Blo 1809606 6108263 := bstep (se 1 (by rfl) ⟨4581197, by rfl⟩ : syracuseStep 6108263 = 9162395) B9162395
theorem B1809919 : Blo 1809606 1809919 := bstep (se 1 (by rfl) ⟨1357439, by rfl⟩ : syracuseStep 1809919 = 2714879) B2714879
theorem B4072175 : Blo 1809606 4072175 := bstep (se 1 (by rfl) ⟨3054131, by rfl⟩ : syracuseStep 4072175 = 6108263) B6108263
theorem B5801257 : Blo 1809606 5801257 := bstep (se 2 (by rfl) ⟨2175471, by rfl⟩ : syracuseStep 5801257 = 4350943) B4350943
theorem B35284301 : Blo 1809606 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B3437167 : Blo 1809606 3437167 := bstep (se 1 (by rfl) ⟨2577875, by rfl⟩ : syracuseStep 3437167 = 5155751) B5155751
theorem B7735009 : Blo 1809606 7735009 := bstep (se 2 (by rfl) ⟨2900628, by rfl⟩ : syracuseStep 7735009 = 5801257) B5801257
theorem B2714783 : Blo 1809606 2714783 := bstep (se 1 (by rfl) ⟨2036087, by rfl⟩ : syracuseStep 2714783 = 4072175) B4072175
theorem B4582889 : Blo 1809606 4582889 := bstep (se 2 (by rfl) ⟨1718583, by rfl⟩ : syracuseStep 4582889 = 3437167) B3437167
theorem B23522867 : Blo 1809606 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B250910581 : Blo 1809606 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B1809855 : Blo 1809606 1809855 := bstep (se 1 (by rfl) ⟨1357391, by rfl⟩ : syracuseStep 1809855 = 2714783) B2714783
theorem B10313345 : Blo 1809606 10313345 := bstep (se 2 (by rfl) ⟨3867504, by rfl⟩ : syracuseStep 10313345 = 7735009) B7735009
theorem B3055259 : Blo 1809606 3055259 := bstep (se 1 (by rfl) ⟨2291444, by rfl⟩ : syracuseStep 3055259 = 4582889) B4582889
theorem B6875563 : Blo 1809606 6875563 := bstep (se 1 (by rfl) ⟨5156672, by rfl⟩ : syracuseStep 6875563 = 10313345) B10313345
theorem B334547441 : Blo 1809606 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B2036839 : Blo 1809606 2036839 := bstep (se 1 (by rfl) ⟨1527629, by rfl⟩ : syracuseStep 2036839 = 3055259) B3055259
theorem B9167417 : Blo 1809606 9167417 := bstep (se 2 (by rfl) ⟨3437781, by rfl⟩ : syracuseStep 9167417 = 6875563) B6875563
theorem B2715785 : Blo 1809606 2715785 := bstep (se 2 (by rfl) ⟨1018419, by rfl⟩ : syracuseStep 2715785 = 2036839) B2036839
theorem B223031627 : Blo 1809606 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B1810523 : Blo 1809606 1810523 := bstep (se 1 (by rfl) ⟨1357892, by rfl⟩ : syracuseStep 1810523 = 2715785) B2715785
theorem B6111611 : Blo 1809606 6111611 := bstep (se 1 (by rfl) ⟨4583708, by rfl⟩ : syracuseStep 6111611 = 9167417) B9167417
theorem B148687751 : Blo 1809606 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B99125167 : Blo 1809606 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B4074407 : Blo 1809606 4074407 := bstep (se 1 (by rfl) ⟨3055805, by rfl⟩ : syracuseStep 4074407 = 6111611) B6111611
theorem B2716271 : Blo 1809606 2716271 := bstep (se 1 (by rfl) ⟨2037203, by rfl⟩ : syracuseStep 2716271 = 4074407) B4074407
theorem B132166889 : Blo 1809606 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B1810847 : Blo 1809606 1810847 := bstep (se 1 (by rfl) ⟨1358135, by rfl⟩ : syracuseStep 1810847 = 2716271) B2716271
theorem B88111259 : Blo 1809606 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B58740839 : Blo 1809606 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B39160559 : Blo 1809606 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B26107039 : Blo 1809606 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B34809385 : Blo 1809606 34809385 := bstep (se 2 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 34809385 = 26107039) B26107039
theorem B46412513 : Blo 1809606 46412513 := bstep (se 2 (by rfl) ⟨17404692, by rfl⟩ : syracuseStep 46412513 = 34809385) B34809385
theorem B30941675 : Blo 1809606 30941675 := bstep (se 1 (by rfl) ⟨23206256, by rfl⟩ : syracuseStep 30941675 = 46412513) B46412513
theorem B20627783 : Blo 1809606 20627783 := bstep (se 1 (by rfl) ⟨15470837, by rfl⟩ : syracuseStep 20627783 = 30941675) B30941675
theorem B13751855 : Blo 1809606 13751855 := bstep (se 1 (by rfl) ⟨10313891, by rfl⟩ : syracuseStep 13751855 = 20627783) B20627783
theorem B9167903 : Blo 1809606 9167903 := bstep (se 1 (by rfl) ⟨6875927, by rfl⟩ : syracuseStep 9167903 = 13751855) B13751855
theorem B6111935 : Blo 1809606 6111935 := bstep (se 1 (by rfl) ⟨4583951, by rfl⟩ : syracuseStep 6111935 = 9167903) B9167903
theorem B4074623 : Blo 1809606 4074623 := bstep (se 1 (by rfl) ⟨3055967, by rfl⟩ : syracuseStep 4074623 = 6111935) B6111935
theorem B2716415 : Blo 1809606 2716415 := bstep (se 1 (by rfl) ⟨2037311, by rfl⟩ : syracuseStep 2716415 = 4074623) B4074623
theorem B1810943 : Blo 1809606 1810943 := bstep (se 1 (by rfl) ⟨1358207, by rfl⟩ : syracuseStep 1810943 = 2716415) B2716415

theorem C0 (j : ℕ) (h1 : 452401 ≤ j) (h2 : j ≤ 452900) : Blo 1809606 (4 * j + 3) := by
  interval_cases j
  · exact B1809607
  · exact B1809611
  · exact B1809615
  · exact B1809619
  · exact B1809623
  · exact B1809627
  · exact B1809631
  · exact B1809635
  · exact B1809639
  · exact B1809643
  · exact B1809647
  · exact B1809651
  · exact B1809655
  · exact B1809659
  · exact B1809663
  · exact B1809667
  · exact B1809671
  · exact B1809675
  · exact B1809679
  · exact B1809683
  · exact B1809687
  · exact B1809691
  · exact B1809695
  · exact B1809699
  · exact B1809703
  · exact B1809707
  · exact B1809711
  · exact B1809715
  · exact B1809719
  · exact B1809723
  · exact B1809727
  · exact B1809731
  · exact B1809735
  · exact B1809739
  · exact B1809743
  · exact B1809747
  · exact B1809751
  · exact B1809755
  · exact B1809759
  · exact B1809763
  · exact B1809767
  · exact B1809771
  · exact B1809775
  · exact B1809779
  · exact B1809783
  · exact B1809787
  · exact B1809791
  · exact B1809795
  · exact B1809799
  · exact B1809803
  · exact B1809807
  · exact B1809811
  · exact B1809815
  · exact B1809819
  · exact B1809823
  · exact B1809827
  · exact B1809831
  · exact B1809835
  · exact B1809839
  · exact B1809843
  · exact B1809847
  · exact B1809851
  · exact B1809855
  · exact B1809859
  · exact B1809863
  · exact B1809867
  · exact B1809871
  · exact B1809875
  · exact B1809879
  · exact B1809883
  · exact B1809887
  · exact B1809891
  · exact B1809895
  · exact B1809899
  · exact B1809903
  · exact B1809907
  · exact B1809911
  · exact B1809915
  · exact B1809919
  · exact B1809923
  · exact B1809927
  · exact B1809931
  · exact B1809935
  · exact B1809939
  · exact B1809943
  · exact B1809947
  · exact B1809951
  · exact B1809955
  · exact B1809959
  · exact B1809963
  · exact B1809967
  · exact B1809971
  · exact B1809975
  · exact B1809979
  · exact B1809983
  · exact B1809987
  · exact B1809991
  · exact B1809995
  · exact B1809999
  · exact B1810003
  · exact B1810007
  · exact B1810011
  · exact B1810015
  · exact B1810019
  · exact B1810023
  · exact B1810027
  · exact B1810031
  · exact B1810035
  · exact B1810039
  · exact B1810043
  · exact B1810047
  · exact B1810051
  · exact B1810055
  · exact B1810059
  · exact B1810063
  · exact B1810067
  · exact B1810071
  · exact B1810075
  · exact B1810079
  · exact B1810083
  · exact B1810087
  · exact B1810091
  · exact B1810095
  · exact B1810099
  · exact B1810103
  · exact B1810107
  · exact B1810111
  · exact B1810115
  · exact B1810119
  · exact B1810123
  · exact B1810127
  · exact B1810131
  · exact B1810135
  · exact B1810139
  · exact B1810143
  · exact B1810147
  · exact B1810151
  · exact B1810155
  · exact B1810159
  · exact B1810163
  · exact B1810167
  · exact B1810171
  · exact B1810175
  · exact B1810179
  · exact B1810183
  · exact B1810187
  · exact B1810191
  · exact B1810195
  · exact B1810199
  · exact B1810203
  · exact B1810207
  · exact B1810211
  · exact B1810215
  · exact B1810219
  · exact B1810223
  · exact B1810227
  · exact B1810231
  · exact B1810235
  · exact B1810239
  · exact B1810243
  · exact B1810247
  · exact B1810251
  · exact B1810255
  · exact B1810259
  · exact B1810263
  · exact B1810267
  · exact B1810271
  · exact B1810275
  · exact B1810279
  · exact B1810283
  · exact B1810287
  · exact B1810291
  · exact B1810295
  · exact B1810299
  · exact B1810303
  · exact B1810307
  · exact B1810311
  · exact B1810315
  · exact B1810319
  · exact B1810323
  · exact B1810327
  · exact B1810331
  · exact B1810335
  · exact B1810339
  · exact B1810343
  · exact B1810347
  · exact B1810351
  · exact B1810355
  · exact B1810359
  · exact B1810363
  · exact B1810367
  · exact B1810371
  · exact B1810375
  · exact B1810379
  · exact B1810383
  · exact B1810387
  · exact B1810391
  · exact B1810395
  · exact B1810399
  · exact B1810403
  · exact B1810407
  · exact B1810411
  · exact B1810415
  · exact B1810419
  · exact B1810423
  · exact B1810427
  · exact B1810431
  · exact B1810435
  · exact B1810439
  · exact B1810443
  · exact B1810447
  · exact B1810451
  · exact B1810455
  · exact B1810459
  · exact B1810463
  · exact B1810467
  · exact B1810471
  · exact B1810475
  · exact B1810479
  · exact B1810483
  · exact B1810487
  · exact B1810491
  · exact B1810495
  · exact B1810499
  · exact B1810503
  · exact B1810507
  · exact B1810511
  · exact B1810515
  · exact B1810519
  · exact B1810523
  · exact B1810527
  · exact B1810531
  · exact B1810535
  · exact B1810539
  · exact B1810543
  · exact B1810547
  · exact B1810551
  · exact B1810555
  · exact B1810559
  · exact B1810563
  · exact B1810567
  · exact B1810571
  · exact B1810575
  · exact B1810579
  · exact B1810583
  · exact B1810587
  · exact B1810591
  · exact B1810595
  · exact B1810599
  · exact B1810603
  · exact B1810607
  · exact B1810611
  · exact B1810615
  · exact B1810619
  · exact B1810623
  · exact B1810627
  · exact B1810631
  · exact B1810635
  · exact B1810639
  · exact B1810643
  · exact B1810647
  · exact B1810651
  · exact B1810655
  · exact B1810659
  · exact B1810663
  · exact B1810667
  · exact B1810671
  · exact B1810675
  · exact B1810679
  · exact B1810683
  · exact B1810687
  · exact B1810691
  · exact B1810695
  · exact B1810699
  · exact B1810703
  · exact B1810707
  · exact B1810711
  · exact B1810715
  · exact B1810719
  · exact B1810723
  · exact B1810727
  · exact B1810731
  · exact B1810735
  · exact B1810739
  · exact B1810743
  · exact B1810747
  · exact B1810751
  · exact B1810755
  · exact B1810759
  · exact B1810763
  · exact B1810767
  · exact B1810771
  · exact B1810775
  · exact B1810779
  · exact B1810783
  · exact B1810787
  · exact B1810791
  · exact B1810795
  · exact B1810799
  · exact B1810803
  · exact B1810807
  · exact B1810811
  · exact B1810815
  · exact B1810819
  · exact B1810823
  · exact B1810827
  · exact B1810831
  · exact B1810835
  · exact B1810839
  · exact B1810843
  · exact B1810847
  · exact B1810851
  · exact B1810855
  · exact B1810859
  · exact B1810863
  · exact B1810867
  · exact B1810871
  · exact B1810875
  · exact B1810879
  · exact B1810883
  · exact B1810887
  · exact B1810891
  · exact B1810895
  · exact B1810899
  · exact B1810903
  · exact B1810907
  · exact B1810911
  · exact B1810915
  · exact B1810919
  · exact B1810923
  · exact B1810927
  · exact B1810931
  · exact B1810935
  · exact B1810939
  · exact B1810943
  · exact B1810947
  · exact B1810951
  · exact B1810955
  · exact B1810959
  · exact B1810963
  · exact B1810967
  · exact B1810971
  · exact B1810975
  · exact B1810979
  · exact B1810983
  · exact B1810987
  · exact B1810991
  · exact B1810995
  · exact B1810999
  · exact B1811003
  · exact B1811007
  · exact B1811011
  · exact B1811015
  · exact B1811019
  · exact B1811023
  · exact B1811027
  · exact B1811031
  · exact B1811035
  · exact B1811039
  · exact B1811043
  · exact B1811047
  · exact B1811051
  · exact B1811055
  · exact B1811059
  · exact B1811063
  · exact B1811067
  · exact B1811071
  · exact B1811075
  · exact B1811079
  · exact B1811083
  · exact B1811087
  · exact B1811091
  · exact B1811095
  · exact B1811099
  · exact B1811103
  · exact B1811107
  · exact B1811111
  · exact B1811115
  · exact B1811119
  · exact B1811123
  · exact B1811127
  · exact B1811131
  · exact B1811135
  · exact B1811139
  · exact B1811143
  · exact B1811147
  · exact B1811151
  · exact B1811155
  · exact B1811159
  · exact B1811163
  · exact B1811167
  · exact B1811171
  · exact B1811175
  · exact B1811179
  · exact B1811183
  · exact B1811187
  · exact B1811191
  · exact B1811195
  · exact B1811199
  · exact B1811203
  · exact B1811207
  · exact B1811211
  · exact B1811215
  · exact B1811219
  · exact B1811223
  · exact B1811227
  · exact B1811231
  · exact B1811235
  · exact B1811239
  · exact B1811243
  · exact B1811247
  · exact B1811251
  · exact B1811255
  · exact B1811259
  · exact B1811263
  · exact B1811267
  · exact B1811271
  · exact B1811275
  · exact B1811279
  · exact B1811283
  · exact B1811287
  · exact B1811291
  · exact B1811295
  · exact B1811299
  · exact B1811303
  · exact B1811307
  · exact B1811311
  · exact B1811315
  · exact B1811319
  · exact B1811323
  · exact B1811327
  · exact B1811331
  · exact B1811335
  · exact B1811339
  · exact B1811343
  · exact B1811347
  · exact B1811351
  · exact B1811355
  · exact B1811359
  · exact B1811363
  · exact B1811367
  · exact B1811371
  · exact B1811375
  · exact B1811379
  · exact B1811383
  · exact B1811387
  · exact B1811391
  · exact B1811395
  · exact B1811399
  · exact B1811403
  · exact B1811407
  · exact B1811411
  · exact B1811415
  · exact B1811419
  · exact B1811423
  · exact B1811427
  · exact B1811431
  · exact B1811435
  · exact B1811439
  · exact B1811443
  · exact B1811447
  · exact B1811451
  · exact B1811455
  · exact B1811459
  · exact B1811463
  · exact B1811467
  · exact B1811471
  · exact B1811475
  · exact B1811479
  · exact B1811483
  · exact B1811487
  · exact B1811491
  · exact B1811495
  · exact B1811499
  · exact B1811503
  · exact B1811507
  · exact B1811511
  · exact B1811515
  · exact B1811519
  · exact B1811523
  · exact B1811527
  · exact B1811531
  · exact B1811535
  · exact B1811539
  · exact B1811543
  · exact B1811547
  · exact B1811551
  · exact B1811555
  · exact B1811559
  · exact B1811563
  · exact B1811567
  · exact B1811571
  · exact B1811575
  · exact B1811579
  · exact B1811583
  · exact B1811587
  · exact B1811591
  · exact B1811595
  · exact B1811599
  · exact B1811603

theorem solution (m : ℕ) (hlo : 1809606 ≤ m) (hhi : m ≤ 1811606) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 452401 ≤ j := by omega
    have hj2 : j ≤ 452900 := by omega
    have hb : Blo 1809606 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
