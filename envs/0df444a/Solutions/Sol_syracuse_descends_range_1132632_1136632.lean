-- Prove2me | solution 1 for syracuse_descends_range_1132632_1136632
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:44.314288+00:00
-- url     : https://prove2.me/submissions/24707a83-84e9-4e5f-a049-1ed9197dccdc

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


theorem B2555909 : Blo 1132632 2555909 := bbase (se 4 (by rfl) ⟨239616, by rfl⟩ : syracuseStep 2555909 = 479233) (by norm_num)
theorem B1703957 : Blo 1132632 1703957 := bbase (se 6 (by rfl) ⟨39936, by rfl⟩ : syracuseStep 1703957 = 79873) (by norm_num)
theorem B1277977 : Blo 1132632 1277977 := bbase (se 2 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 1277977 = 958483) (by norm_num)
theorem B1703981 : Blo 1132632 1703981 := bbase (se 3 (by rfl) ⟨319496, by rfl⟩ : syracuseStep 1703981 = 638993) (by norm_num)
theorem B1278013 : Blo 1132632 1278013 := bbase (se 3 (by rfl) ⟨239627, by rfl⟩ : syracuseStep 1278013 = 479255) (by norm_num)
theorem B1704005 : Blo 1132632 1704005 := bbase (se 4 (by rfl) ⟨159750, by rfl⟩ : syracuseStep 1704005 = 319501) (by norm_num)
theorem B2555981 : Blo 1132632 2555981 := bbase (se 3 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 2555981 = 958493) (by norm_num)
theorem B1704029 : Blo 1132632 1704029 := bbase (se 3 (by rfl) ⟨319505, by rfl⟩ : syracuseStep 1704029 = 639011) (by norm_num)
theorem B1278049 : Blo 1132632 1278049 := bbase (se 2 (by rfl) ⟨479268, by rfl⟩ : syracuseStep 1278049 = 958537) (by norm_num)
theorem B1212517 : Blo 1132632 1212517 := bbase (se 4 (by rfl) ⟨113673, by rfl⟩ : syracuseStep 1212517 = 227347) (by norm_num)
theorem B1704053 : Blo 1132632 1704053 := bbase (se 5 (by rfl) ⟨79877, by rfl⟩ : syracuseStep 1704053 = 159755) (by norm_num)
theorem B1278085 : Blo 1132632 1278085 := bbase (se 4 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 1278085 = 239641) (by norm_num)
theorem B2424973 : Blo 1132632 2424973 := bbase (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) (by norm_num)
theorem B1704077 : Blo 1132632 1704077 := bbase (se 3 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 1704077 = 639029) (by norm_num)
theorem B2556053 : Blo 1132632 2556053 := bbase (se 6 (by rfl) ⟨59907, by rfl⟩ : syracuseStep 2556053 = 119815) (by norm_num)
theorem B1704101 : Blo 1132632 1704101 := bbase (se 4 (by rfl) ⟨159759, by rfl⟩ : syracuseStep 1704101 = 319519) (by norm_num)
theorem B1278121 : Blo 1132632 1278121 := bbase (se 2 (by rfl) ⟨479295, by rfl⟩ : syracuseStep 1278121 = 958591) (by norm_num)
theorem B1212589 : Blo 1132632 1212589 := bbase (se 3 (by rfl) ⟨227360, by rfl⟩ : syracuseStep 1212589 = 454721) (by norm_num)
theorem B6455477 : Blo 1132632 6455477 := bbase (se 5 (by rfl) ⟨302600, by rfl⟩ : syracuseStep 6455477 = 605201) (by norm_num)
theorem B1704125 : Blo 1132632 1704125 := bbase (se 3 (by rfl) ⟨319523, by rfl⟩ : syracuseStep 1704125 = 639047) (by norm_num)
theorem B3834053 : Blo 1132632 3834053 := bbase (se 4 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 3834053 = 718885) (by norm_num)
theorem B1278157 : Blo 1132632 1278157 := bbase (se 3 (by rfl) ⟨239654, by rfl⟩ : syracuseStep 1278157 = 479309) (by norm_num)
theorem B11043029 : Blo 1132632 11043029 := bbase (se 7 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 11043029 = 258821) (by norm_num)
theorem B1704149 : Blo 1132632 1704149 := bbase (se 7 (by rfl) ⟨19970, by rfl⟩ : syracuseStep 1704149 = 39941) (by norm_num)
theorem B2556125 : Blo 1132632 2556125 := bbase (se 3 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 2556125 = 958547) (by norm_num)
theorem B1704173 : Blo 1132632 1704173 := bbase (se 3 (by rfl) ⟨319532, by rfl⟩ : syracuseStep 1704173 = 639065) (by norm_num)
theorem B1278193 : Blo 1132632 1278193 := bbase (se 2 (by rfl) ⟨479322, by rfl⟩ : syracuseStep 1278193 = 958645) (by norm_num)
theorem B1704197 : Blo 1132632 1704197 := bbase (se 4 (by rfl) ⟨159768, by rfl⟩ : syracuseStep 1704197 = 319537) (by norm_num)
theorem B1278229 : Blo 1132632 1278229 := bbase (se 6 (by rfl) ⟨29958, by rfl⟩ : syracuseStep 1278229 = 59917) (by norm_num)
theorem B1704221 : Blo 1132632 1704221 := bbase (se 3 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 1704221 = 639083) (by norm_num)
theorem B2556197 : Blo 1132632 2556197 := bbase (se 4 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 2556197 = 479287) (by norm_num)
theorem B1704245 : Blo 1132632 1704245 := bbase (se 5 (by rfl) ⟨79886, by rfl⟩ : syracuseStep 1704245 = 159773) (by norm_num)
theorem B1278265 : Blo 1132632 1278265 := bbase (se 2 (by rfl) ⟨479349, by rfl⟩ : syracuseStep 1278265 = 958699) (by norm_num)
theorem B1704269 : Blo 1132632 1704269 := bbase (se 3 (by rfl) ⟨319550, by rfl⟩ : syracuseStep 1704269 = 639101) (by norm_num)
theorem B1278301 : Blo 1132632 1278301 := bbase (se 3 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 1278301 = 479363) (by norm_num)
theorem B1212769 : Blo 1132632 1212769 := bbase (se 2 (by rfl) ⟨454788, by rfl⟩ : syracuseStep 1212769 = 909577) (by norm_num)
theorem B1704293 : Blo 1132632 1704293 := bbase (se 4 (by rfl) ⟨159777, by rfl⟩ : syracuseStep 1704293 = 319555) (by norm_num)
theorem B2556269 : Blo 1132632 2556269 := bbase (se 3 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 2556269 = 958601) (by norm_num)
theorem B1704317 : Blo 1132632 1704317 := bbase (se 3 (by rfl) ⟨319559, by rfl⟩ : syracuseStep 1704317 = 639119) (by norm_num)
theorem B1278337 : Blo 1132632 1278337 := bbase (se 2 (by rfl) ⟨479376, by rfl⟩ : syracuseStep 1278337 = 958753) (by norm_num)
theorem B1704341 : Blo 1132632 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B1278373 : Blo 1132632 1278373 := bbase (se 4 (by rfl) ⟨119847, by rfl⟩ : syracuseStep 1278373 = 239695) (by norm_num)
theorem B1704365 : Blo 1132632 1704365 := bbase (se 3 (by rfl) ⟨319568, by rfl⟩ : syracuseStep 1704365 = 639137) (by norm_num)
theorem B2556341 : Blo 1132632 2556341 := bbase (se 5 (by rfl) ⟨119828, by rfl⟩ : syracuseStep 2556341 = 239657) (by norm_num)
theorem B1704389 : Blo 1132632 1704389 := bbase (se 4 (by rfl) ⟨159786, by rfl⟩ : syracuseStep 1704389 = 319573) (by norm_num)
theorem B1278409 : Blo 1132632 1278409 := bbase (se 2 (by rfl) ⟨479403, by rfl⟩ : syracuseStep 1278409 = 958807) (by norm_num)
theorem B1704413 : Blo 1132632 1704413 := bbase (se 3 (by rfl) ⟨319577, by rfl⟩ : syracuseStep 1704413 = 639155) (by norm_num)
theorem B1278445 : Blo 1132632 1278445 := bbase (se 3 (by rfl) ⟨239708, by rfl⟩ : syracuseStep 1278445 = 479417) (by norm_num)
theorem B1704437 : Blo 1132632 1704437 := bbase (se 5 (by rfl) ⟨79895, by rfl⟩ : syracuseStep 1704437 = 159791) (by norm_num)
theorem B2556413 : Blo 1132632 2556413 := bbase (se 3 (by rfl) ⟨479327, by rfl⟩ : syracuseStep 2556413 = 958655) (by norm_num)
theorem B2425349 : Blo 1132632 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B1704461 : Blo 1132632 1704461 := bbase (se 3 (by rfl) ⟨319586, by rfl⟩ : syracuseStep 1704461 = 639173) (by norm_num)
theorem B1278481 : Blo 1132632 1278481 := bbase (se 2 (by rfl) ⟨479430, by rfl⟩ : syracuseStep 1278481 = 958861) (by norm_num)
theorem B1704485 : Blo 1132632 1704485 := bbase (se 4 (by rfl) ⟨159795, by rfl⟩ : syracuseStep 1704485 = 319591) (by norm_num)
theorem B1278517 : Blo 1132632 1278517 := bbase (se 5 (by rfl) ⟨59930, by rfl⟩ : syracuseStep 1278517 = 119861) (by norm_num)
theorem B1704509 : Blo 1132632 1704509 := bbase (se 3 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 1704509 = 639191) (by norm_num)
theorem B2556485 : Blo 1132632 2556485 := bbase (se 4 (by rfl) ⟨239670, by rfl⟩ : syracuseStep 2556485 = 479341) (by norm_num)
theorem B1704533 : Blo 1132632 1704533 := bbase (se 8 (by rfl) ⟨9987, by rfl⟩ : syracuseStep 1704533 = 19975) (by norm_num)
theorem B1278553 : Blo 1132632 1278553 := bbase (se 2 (by rfl) ⟨479457, by rfl⟩ : syracuseStep 1278553 = 958915) (by norm_num)
theorem B1704557 : Blo 1132632 1704557 := bbase (se 3 (by rfl) ⟨319604, by rfl⟩ : syracuseStep 1704557 = 639209) (by norm_num)
theorem B3834485 : Blo 1132632 3834485 := bbase (se 5 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 3834485 = 359483) (by norm_num)
theorem B1278589 : Blo 1132632 1278589 := bbase (se 3 (by rfl) ⟨239735, by rfl⟩ : syracuseStep 1278589 = 479471) (by norm_num)
theorem B1704581 : Blo 1132632 1704581 := bbase (se 4 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 1704581 = 319609) (by norm_num)
theorem B1311373 : Blo 1132632 1311373 := bbase (se 3 (by rfl) ⟨245882, by rfl⟩ : syracuseStep 1311373 = 491765) (by norm_num)
theorem B2556557 : Blo 1132632 2556557 := bbase (se 3 (by rfl) ⟨479354, by rfl⟩ : syracuseStep 2556557 = 958709) (by norm_num)
theorem B1704605 : Blo 1132632 1704605 := bbase (se 3 (by rfl) ⟨319613, by rfl⟩ : syracuseStep 1704605 = 639227) (by norm_num)
theorem B1278625 : Blo 1132632 1278625 := bbase (se 2 (by rfl) ⟨479484, by rfl⟩ : syracuseStep 1278625 = 958969) (by norm_num)
theorem B1704629 : Blo 1132632 1704629 := bbase (se 5 (by rfl) ⟨79904, by rfl⟩ : syracuseStep 1704629 = 159809) (by norm_num)
theorem B1278661 : Blo 1132632 1278661 := bbase (se 4 (by rfl) ⟨119874, by rfl⟩ : syracuseStep 1278661 = 239749) (by norm_num)
theorem B1704653 : Blo 1132632 1704653 := bbase (se 3 (by rfl) ⟨319622, by rfl⟩ : syracuseStep 1704653 = 639245) (by norm_num)
theorem B3637973 : Blo 1132632 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B2556629 : Blo 1132632 2556629 := bbase (se 7 (by rfl) ⟨29960, by rfl⟩ : syracuseStep 2556629 = 59921) (by norm_num)
theorem B2589413 : Blo 1132632 2589413 := bbase (se 4 (by rfl) ⟨242757, by rfl⟩ : syracuseStep 2589413 = 485515) (by norm_num)
theorem B1704677 : Blo 1132632 1704677 := bbase (se 4 (by rfl) ⟨159813, by rfl⟩ : syracuseStep 1704677 = 319627) (by norm_num)
theorem B1278697 : Blo 1132632 1278697 := bbase (se 2 (by rfl) ⟨479511, by rfl⟩ : syracuseStep 1278697 = 959023) (by norm_num)
theorem B1704701 : Blo 1132632 1704701 := bbase (se 3 (by rfl) ⟨319631, by rfl⟩ : syracuseStep 1704701 = 639263) (by norm_num)
theorem B1704725 : Blo 1132632 1704725 := bbase (se 6 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 1704725 = 79909) (by norm_num)
theorem B1213213 : Blo 1132632 1213213 := bbase (se 3 (by rfl) ⟨227477, by rfl⟩ : syracuseStep 1213213 = 454955) (by norm_num)
theorem B2556701 : Blo 1132632 2556701 := bbase (se 3 (by rfl) ⟨479381, by rfl⟩ : syracuseStep 2556701 = 958763) (by norm_num)
theorem B1704749 : Blo 1132632 1704749 := bbase (se 3 (by rfl) ⟨319640, by rfl⟩ : syracuseStep 1704749 = 639281) (by norm_num)
theorem B1704773 : Blo 1132632 1704773 := bbase (se 4 (by rfl) ⟨159822, by rfl⟩ : syracuseStep 1704773 = 319645) (by norm_num)
theorem B1704797 : Blo 1132632 1704797 := bbase (se 3 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 1704797 = 639299) (by norm_num)
theorem B2556773 : Blo 1132632 2556773 := bbase (se 4 (by rfl) ⟨239697, by rfl⟩ : syracuseStep 2556773 = 479395) (by norm_num)
theorem B5735285 : Blo 1132632 5735285 := bbase (se 5 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 5735285 = 537683) (by norm_num)
theorem B2425717 : Blo 1132632 2425717 := bbase (se 5 (by rfl) ⟨113705, by rfl⟩ : syracuseStep 2425717 = 227411) (by norm_num)
theorem B1704821 : Blo 1132632 1704821 := bbase (se 5 (by rfl) ⟨79913, by rfl⟩ : syracuseStep 1704821 = 159827) (by norm_num)
theorem B1704845 : Blo 1132632 1704845 := bbase (se 3 (by rfl) ⟨319658, by rfl⟩ : syracuseStep 1704845 = 639317) (by norm_num)
theorem B1213337 : Blo 1132632 1213337 := bbase (se 2 (by rfl) ⟨455001, by rfl⟩ : syracuseStep 1213337 = 910003) (by norm_num)
theorem B1704869 : Blo 1132632 1704869 := bbase (se 4 (by rfl) ⟨159831, by rfl⟩ : syracuseStep 1704869 = 319663) (by norm_num)
theorem B2556845 : Blo 1132632 2556845 := bbase (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) (by norm_num)
theorem B1704893 : Blo 1132632 1704893 := bbase (se 3 (by rfl) ⟨319667, by rfl⟩ : syracuseStep 1704893 = 639335) (by norm_num)
theorem B1704917 : Blo 1132632 1704917 := bbase (se 7 (by rfl) ⟨19979, by rfl⟩ : syracuseStep 1704917 = 39959) (by norm_num)
theorem B1704941 : Blo 1132632 1704941 := bbase (se 3 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 1704941 = 639353) (by norm_num)
theorem B2556917 : Blo 1132632 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B2327549 : Blo 1132632 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6554645 : Blo 1132632 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B3834917 : Blo 1132632 3834917 := bbase (se 4 (by rfl) ⟨359523, by rfl⟩ : syracuseStep 3834917 = 719047) (by norm_num)
theorem B2556989 : Blo 1132632 2556989 := bbase (se 3 (by rfl) ⟨479435, by rfl⟩ : syracuseStep 2556989 = 958871) (by norm_num)
theorem B2557061 : Blo 1132632 2557061 := bbase (se 4 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 2557061 = 479449) (by norm_num)
theorem B1213589 : Blo 1132632 1213589 := bbase (se 6 (by rfl) ⟨28443, by rfl⟩ : syracuseStep 1213589 = 56887) (by norm_num)
theorem B2557133 : Blo 1132632 2557133 := bbase (se 3 (by rfl) ⟨479462, by rfl⟩ : syracuseStep 2557133 = 958925) (by norm_num)
theorem B6227221 : Blo 1132632 6227221 := bbase (se 6 (by rfl) ⟨145950, by rfl⟩ : syracuseStep 6227221 = 291901) (by norm_num)
theorem B2557205 : Blo 1132632 2557205 := bbase (se 6 (by rfl) ⟨59934, by rfl⟩ : syracuseStep 2557205 = 119869) (by norm_num)
theorem B2557277 : Blo 1132632 2557277 := bbase (se 3 (by rfl) ⟨479489, by rfl⟩ : syracuseStep 2557277 = 958979) (by norm_num)
theorem B2557349 : Blo 1132632 2557349 := bbase (se 4 (by rfl) ⟨239751, by rfl⟩ : syracuseStep 2557349 = 479503) (by norm_num)
theorem B1148329 : Blo 1132632 1148329 := bbase (se 2 (by rfl) ⟨430623, by rfl⟩ : syracuseStep 1148329 = 861247) (by norm_num)
theorem B3835349 : Blo 1132632 3835349 := bbase (se 7 (by rfl) ⟨44945, by rfl⟩ : syracuseStep 3835349 = 89891) (by norm_num)
theorem B2557421 : Blo 1132632 2557421 := bbase (se 3 (by rfl) ⟨479516, by rfl⟩ : syracuseStep 2557421 = 959033) (by norm_num)
theorem B1312405 : Blo 1132632 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B1148629 : Blo 1132632 1148629 := bbase (se 7 (by rfl) ⟨13460, by rfl⟩ : syracuseStep 1148629 = 26921) (by norm_num)
theorem B3835781 : Blo 1132632 3835781 := bbase (se 4 (by rfl) ⟨359604, by rfl⟩ : syracuseStep 3835781 = 719209) (by norm_num)
theorem B39782357 : Blo 1132632 39782357 := bbase (se 7 (by rfl) ⟨466199, by rfl⟩ : syracuseStep 39782357 = 932399) (by norm_num)
theorem B1148969 : Blo 1132632 1148969 := bbase (se 2 (by rfl) ⟨430863, by rfl⟩ : syracuseStep 1148969 = 861727) (by norm_num)
theorem B5736581 : Blo 1132632 5736581 := bbase (se 4 (by rfl) ⟨537804, by rfl⟩ : syracuseStep 5736581 = 1075609) (by norm_num)
theorem B4851845 : Blo 1132632 4851845 := bbase (se 4 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 4851845 = 909721) (by norm_num)
theorem B8620181 : Blo 1132632 8620181 := bbase (se 6 (by rfl) ⟨202035, by rfl⟩ : syracuseStep 8620181 = 404071) (by norm_num)
theorem B1149229 : Blo 1132632 1149229 := bbase (se 3 (by rfl) ⟨215480, by rfl⟩ : syracuseStep 1149229 = 430961) (by norm_num)
theorem B1476917 : Blo 1132632 1476917 := bbase (se 5 (by rfl) ⟨69230, by rfl⟩ : syracuseStep 1476917 = 138461) (by norm_num)
theorem B2427221 : Blo 1132632 2427221 := bbase (se 10 (by rfl) ⟨3555, by rfl⟩ : syracuseStep 2427221 = 7111) (by norm_num)
theorem B4852133 : Blo 1132632 4852133 := bbase (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) (by norm_num)
theorem B2427365 : Blo 1132632 2427365 := bbase (se 4 (by rfl) ⟨227565, by rfl⟩ : syracuseStep 2427365 = 455131) (by norm_num)
theorem B2296333 : Blo 1132632 2296333 := bbase (se 3 (by rfl) ⟨430562, by rfl⟩ : syracuseStep 2296333 = 861125) (by norm_num)
theorem B2722349 : Blo 1132632 2722349 := bbase (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) (by norm_num)
theorem B1149553 : Blo 1132632 1149553 := bbase (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) (by norm_num)
theorem B1149841 : Blo 1132632 1149841 := bbase (se 2 (by rfl) ⟨431190, by rfl⟩ : syracuseStep 1149841 = 862381) (by norm_num)
theorem B2722781 : Blo 1132632 2722781 := bbase (se 3 (by rfl) ⟨510521, by rfl⟩ : syracuseStep 2722781 = 1021043) (by norm_num)
theorem B2296829 : Blo 1132632 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B2591813 : Blo 1132632 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B4852885 : Blo 1132632 4852885 := bbase (se 6 (by rfl) ⟨113739, by rfl⟩ : syracuseStep 4852885 = 227479) (by norm_num)
theorem B2592005 : Blo 1132632 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B5442965 : Blo 1132632 5442965 := bbase (se 6 (by rfl) ⟨127569, by rfl⟩ : syracuseStep 5442965 = 255139) (by norm_num)
theorem B5737877 : Blo 1132632 5737877 := bbase (se 6 (by rfl) ⟨134481, by rfl⟩ : syracuseStep 5737877 = 268963) (by norm_num)
theorem B2297501 : Blo 1132632 2297501 := bbase (se 3 (by rfl) ⟨430781, by rfl⟩ : syracuseStep 2297501 = 861563) (by norm_num)
theorem B4853621 : Blo 1132632 4853621 := bbase (se 5 (by rfl) ⟨227513, by rfl⟩ : syracuseStep 4853621 = 455027) (by norm_num)
theorem B6131861 : Blo 1132632 6131861 := bbase (se 6 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 6131861 = 287431) (by norm_num)
theorem B2330797 : Blo 1132632 2330797 := bbase (se 3 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 2330797 = 874049) (by norm_num)
theorem B1937677 : Blo 1132632 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B2298133 : Blo 1132632 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B1151281 : Blo 1132632 1151281 := bbase (se 2 (by rfl) ⟨431730, by rfl⟩ : syracuseStep 1151281 = 863461) (by norm_num)
theorem B1151581 : Blo 1132632 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1151597 : Blo 1132632 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B5739173 : Blo 1132632 5739173 := bbase (se 4 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 5739173 = 1076095) (by norm_num)
theorem B6558517 : Blo 1132632 6558517 := bbase (se 5 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 6558517 = 614861) (by norm_num)
theorem B8164277 : Blo 1132632 8164277 := bbase (se 5 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 8164277 = 765401) (by norm_num)
theorem B2332045 : Blo 1132632 2332045 := bbase (se 3 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 2332045 = 874517) (by norm_num)
theorem B4920725 : Blo 1132632 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B3937781 : Blo 1132632 3937781 := bbase (se 5 (by rfl) ⟨184583, by rfl⟩ : syracuseStep 3937781 = 369167) (by norm_num)
theorem B5740469 : Blo 1132632 5740469 := bbase (se 5 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 5740469 = 538169) (by norm_num)
theorem B2299853 : Blo 1132632 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B5445733 : Blo 1132632 5445733 := bbase (se 4 (by rfl) ⟨510537, by rfl⟩ : syracuseStep 5445733 = 1021075) (by norm_num)
theorem B2726173 : Blo 1132632 2726173 := bbase (se 3 (by rfl) ⟨511157, by rfl⟩ : syracuseStep 2726173 = 1022315) (by norm_num)
theorem B14522773 : Blo 1132632 14522773 := bbase (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) (by norm_num)
theorem B10885589 : Blo 1132632 10885589 := bbase (se 7 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 10885589 = 255131) (by norm_num)
theorem B2300485 : Blo 1132632 2300485 := bbase (se 4 (by rfl) ⟨215670, by rfl⟩ : syracuseStep 2300485 = 431341) (by norm_num)
theorem B2726597 : Blo 1132632 2726597 := bbase (se 4 (by rfl) ⟨255618, by rfl⟩ : syracuseStep 2726597 = 511237) (by norm_num)
theorem B1940365 : Blo 1132632 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B2726885 : Blo 1132632 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B4660325 : Blo 1132632 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B3939445 : Blo 1132632 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B1612981 : Blo 1132632 1612981 := bbase (se 5 (by rfl) ⟨75608, by rfl⟩ : syracuseStep 1612981 = 151217) (by norm_num)
theorem B5741765 : Blo 1132632 5741765 := bbase (se 4 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 5741765 = 1076581) (by norm_num)
theorem B3939877 : Blo 1132632 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B1941077 : Blo 1132632 1941077 := bbase (se 8 (by rfl) ⟨11373, by rfl⟩ : syracuseStep 1941077 = 22747) (by norm_num)
theorem B2301605 : Blo 1132632 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B3448757 : Blo 1132632 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B1613773 : Blo 1132632 1613773 := bbase (se 3 (by rfl) ⟨302582, by rfl⟩ : syracuseStep 1613773 = 605165) (by norm_num)
theorem B39297109 : Blo 1132632 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B1941781 : Blo 1132632 1941781 := bbase (se 6 (by rfl) ⟨45510, by rfl⟩ : syracuseStep 1941781 = 91021) (by norm_num)
theorem B1614109 : Blo 1132632 1614109 := bbase (se 3 (by rfl) ⟨302645, by rfl⟩ : syracuseStep 1614109 = 605291) (by norm_num)
theorem B2302277 : Blo 1132632 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B2302285 : Blo 1132632 2302285 := bbase (se 3 (by rfl) ⟨431678, by rfl⟩ : syracuseStep 2302285 = 863357) (by norm_num)
theorem B4301221 : Blo 1132632 4301221 := bbase (se 4 (by rfl) ⟨403239, by rfl⟩ : syracuseStep 4301221 = 806479) (by norm_num)
theorem B9707957 : Blo 1132632 9707957 := bbase (se 5 (by rfl) ⟨455060, by rfl⟩ : syracuseStep 9707957 = 910121) (by norm_num)
theorem B5743061 : Blo 1132632 5743061 := bbase (se 7 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 5743061 = 134603) (by norm_num)
theorem B1614325 : Blo 1132632 1614325 := bbase (se 5 (by rfl) ⟨75671, by rfl⟩ : syracuseStep 1614325 = 151343) (by norm_num)
theorem B4301525 : Blo 1132632 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B12264149 : Blo 1132632 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B2073373 : Blo 1132632 2073373 := bbase (se 3 (by rfl) ⟨388757, by rfl⟩ : syracuseStep 2073373 = 777515) (by norm_num)
theorem B5448485 : Blo 1132632 5448485 := bbase (se 4 (by rfl) ⟨510795, by rfl⟩ : syracuseStep 5448485 = 1021591) (by norm_num)
theorem B1614701 : Blo 1132632 1614701 := bbase (se 3 (by rfl) ⟨302756, by rfl⟩ : syracuseStep 1614701 = 605513) (by norm_num)
theorem B3646453 : Blo 1132632 3646453 := bbase (se 5 (by rfl) ⟨170927, by rfl⟩ : syracuseStep 3646453 = 341855) (by norm_num)
theorem B4138037 : Blo 1132632 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B2041301 : Blo 1132632 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B5744357 : Blo 1132632 5744357 := bbase (se 4 (by rfl) ⟨538533, by rfl⟩ : syracuseStep 5744357 = 1077067) (by norm_num)
theorem B8627957 : Blo 1132632 8627957 := bbase (se 5 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 8627957 = 808871) (by norm_num)
theorem B6465365 : Blo 1132632 6465365 := bbase (se 9 (by rfl) ⟨18941, by rfl⟩ : syracuseStep 6465365 = 37883) (by norm_num)
theorem B2424829 : Blo 1132632 2424829 := bbase (se 3 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 2424829 = 909311) (by norm_num)
theorem B2730037 : Blo 1132632 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B2042093 : Blo 1132632 2042093 := bbase (se 3 (by rfl) ⟨382892, by rfl⟩ : syracuseStep 2042093 = 765785) (by norm_num)
theorem B1616125 : Blo 1132632 1616125 := bbase (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) (by norm_num)
theorem B3451189 : Blo 1132632 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B2042237 : Blo 1132632 2042237 := bbase (se 3 (by rfl) ⟨382919, by rfl⟩ : syracuseStep 2042237 = 765839) (by norm_num)
theorem B2042381 : Blo 1132632 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B1944101 : Blo 1132632 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B2042453 : Blo 1132632 2042453 := bbase (se 8 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 2042453 = 23935) (by norm_num)
theorem B1911397 : Blo 1132632 1911397 := bbase (se 4 (by rfl) ⟨179193, by rfl⟩ : syracuseStep 1911397 = 358387) (by norm_num)
theorem B1911485 : Blo 1132632 1911485 := bbase (se 3 (by rfl) ⟨358403, by rfl⟩ : syracuseStep 1911485 = 716807) (by norm_num)
theorem B2730709 : Blo 1132632 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B4303637 : Blo 1132632 4303637 := bbase (se 6 (by rfl) ⟨100866, by rfl⟩ : syracuseStep 4303637 = 201733) (by norm_num)
theorem B1911613 : Blo 1132632 1911613 := bbase (se 3 (by rfl) ⟨358427, by rfl⟩ : syracuseStep 1911613 = 716855) (by norm_num)
theorem B1616717 : Blo 1132632 1616717 := bbase (se 3 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 1616717 = 606269) (by norm_num)
theorem B9677717 : Blo 1132632 9677717 := bbase (se 6 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 9677717 = 453643) (by norm_num)
theorem B1911701 : Blo 1132632 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B1616797 : Blo 1132632 1616797 := bbase (se 3 (by rfl) ⟨303149, by rfl⟩ : syracuseStep 1616797 = 606299) (by norm_num)
theorem B2730941 : Blo 1132632 2730941 := bbase (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) (by norm_num)
theorem B5745653 : Blo 1132632 5745653 := bbase (se 5 (by rfl) ⟨269327, by rfl⟩ : syracuseStep 5745653 = 538655) (by norm_num)
theorem B1911829 : Blo 1132632 1911829 := bbase (se 6 (by rfl) ⟨44808, by rfl⟩ : syracuseStep 1911829 = 89617) (by norm_num)
theorem B1616917 : Blo 1132632 1616917 := bbase (se 6 (by rfl) ⟨37896, by rfl⟩ : syracuseStep 1616917 = 75793) (by norm_num)
theorem B4303925 : Blo 1132632 4303925 := bbase (se 5 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 4303925 = 403493) (by norm_num)
theorem B1911917 : Blo 1132632 1911917 := bbase (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) (by norm_num)
theorem B1617013 : Blo 1132632 1617013 := bbase (se 5 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 1617013 = 151595) (by norm_num)
theorem B5450885 : Blo 1132632 5450885 := bbase (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) (by norm_num)
theorem B1912045 : Blo 1132632 1912045 := bbase (se 3 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 1912045 = 717017) (by norm_num)
theorem B1912133 : Blo 1132632 1912133 := bbase (se 4 (by rfl) ⟨179262, by rfl⟩ : syracuseStep 1912133 = 358525) (by norm_num)
theorem B1912261 : Blo 1132632 1912261 := bbase (se 4 (by rfl) ⟨179274, by rfl⟩ : syracuseStep 1912261 = 358549) (by norm_num)
theorem B3452357 : Blo 1132632 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B1912349 : Blo 1132632 1912349 := bbase (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) (by norm_num)
theorem B1617509 : Blo 1132632 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B1912477 : Blo 1132632 1912477 := bbase (se 3 (by rfl) ⟨358589, by rfl⟩ : syracuseStep 1912477 = 717179) (by norm_num)
theorem B1912565 : Blo 1132632 1912565 := bbase (se 5 (by rfl) ⟨89651, by rfl⟩ : syracuseStep 1912565 = 179303) (by norm_num)
theorem B6893333 : Blo 1132632 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B2043701 : Blo 1132632 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B1912693 : Blo 1132632 1912693 := bbase (se 5 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 1912693 = 179315) (by norm_num)
theorem B1912781 : Blo 1132632 1912781 := bbase (se 3 (by rfl) ⟨358646, by rfl⟩ : syracuseStep 1912781 = 717293) (by norm_num)
theorem B1912909 : Blo 1132632 1912909 := bbase (se 3 (by rfl) ⟨358670, by rfl⟩ : syracuseStep 1912909 = 717341) (by norm_num)
theorem B1618061 : Blo 1132632 1618061 := bbase (se 3 (by rfl) ⟨303386, by rfl⟩ : syracuseStep 1618061 = 606773) (by norm_num)
theorem B1912997 : Blo 1132632 1912997 := bbase (se 4 (by rfl) ⟨179343, by rfl⟩ : syracuseStep 1912997 = 358687) (by norm_num)
theorem B4305109 : Blo 1132632 4305109 := bbase (se 7 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 4305109 = 100901) (by norm_num)
theorem B6140117 : Blo 1132632 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B5746949 : Blo 1132632 5746949 := bbase (se 4 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 5746949 = 1077553) (by norm_num)
theorem B1913125 : Blo 1132632 1913125 := bbase (se 4 (by rfl) ⟨179355, by rfl⟩ : syracuseStep 1913125 = 358711) (by norm_num)
theorem B1814861 : Blo 1132632 1814861 := bbase (se 3 (by rfl) ⟨340286, by rfl⟩ : syracuseStep 1814861 = 680573) (by norm_num)
theorem B1913213 : Blo 1132632 1913213 := bbase (se 3 (by rfl) ⟨358727, by rfl⟩ : syracuseStep 1913213 = 717455) (by norm_num)
theorem B1913341 : Blo 1132632 1913341 := bbase (se 3 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 1913341 = 717503) (by norm_num)
theorem B4305413 : Blo 1132632 4305413 := bbase (se 4 (by rfl) ⟨403632, by rfl⟩ : syracuseStep 4305413 = 807265) (by norm_num)
theorem B1815085 : Blo 1132632 1815085 := bbase (se 3 (by rfl) ⟨340328, by rfl⟩ : syracuseStep 1815085 = 680657) (by norm_num)
theorem B1454657 : Blo 1132632 1454657 := bbase (se 2 (by rfl) ⟨545496, by rfl⟩ : syracuseStep 1454657 = 1090993) (by norm_num)
theorem B1913429 : Blo 1132632 1913429 := bbase (se 8 (by rfl) ⟨11211, by rfl⟩ : syracuseStep 1913429 = 22423) (by norm_num)
theorem B1913557 : Blo 1132632 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B1913645 : Blo 1132632 1913645 := bbase (se 3 (by rfl) ⟨358808, by rfl⟩ : syracuseStep 1913645 = 717617) (by norm_num)
theorem B3683141 : Blo 1132632 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B1454965 : Blo 1132632 1454965 := bbase (se 5 (by rfl) ⟨68201, by rfl⟩ : syracuseStep 1454965 = 136403) (by norm_num)
theorem B6140789 : Blo 1132632 6140789 := bbase (se 5 (by rfl) ⟨287849, by rfl⟩ : syracuseStep 6140789 = 575699) (by norm_num)
theorem B1913773 : Blo 1132632 1913773 := bbase (se 3 (by rfl) ⟨358832, by rfl⟩ : syracuseStep 1913773 = 717665) (by norm_num)
theorem B1913861 : Blo 1132632 1913861 := bbase (se 4 (by rfl) ⟨179424, by rfl⟩ : syracuseStep 1913861 = 358849) (by norm_num)
theorem B1913989 : Blo 1132632 1913989 := bbase (se 4 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 1913989 = 358873) (by norm_num)
theorem B1914077 : Blo 1132632 1914077 := bbase (se 3 (by rfl) ⟨358889, by rfl⟩ : syracuseStep 1914077 = 717779) (by norm_num)
theorem B1455365 : Blo 1132632 1455365 := bbase (se 4 (by rfl) ⟨136440, by rfl⟩ : syracuseStep 1455365 = 272881) (by norm_num)
theorem B1914205 : Blo 1132632 1914205 := bbase (se 3 (by rfl) ⟨358913, by rfl⟩ : syracuseStep 1914205 = 717827) (by norm_num)
theorem B1914293 : Blo 1132632 1914293 := bbase (se 5 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 1914293 = 179465) (by norm_num)
theorem B1291769 : Blo 1132632 1291769 := bbase (se 2 (by rfl) ⟨484413, by rfl⟩ : syracuseStep 1291769 = 968827) (by norm_num)
theorem B5748245 : Blo 1132632 5748245 := bbase (se 6 (by rfl) ⟨134724, by rfl⟩ : syracuseStep 5748245 = 269449) (by norm_num)
theorem B1914421 : Blo 1132632 1914421 := bbase (se 5 (by rfl) ⟨89738, by rfl⟩ : syracuseStep 1914421 = 179477) (by norm_num)
theorem B1914509 : Blo 1132632 1914509 := bbase (se 3 (by rfl) ⟨358970, by rfl⟩ : syracuseStep 1914509 = 717941) (by norm_num)
theorem B1914637 : Blo 1132632 1914637 := bbase (se 3 (by rfl) ⟨358994, by rfl⟩ : syracuseStep 1914637 = 717989) (by norm_num)
theorem B1455889 : Blo 1132632 1455889 := bbase (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) (by norm_num)
theorem B2045725 : Blo 1132632 2045725 := bbase (se 3 (by rfl) ⟨383573, by rfl⟩ : syracuseStep 2045725 = 767147) (by norm_num)
theorem B1914725 : Blo 1132632 1914725 := bbase (se 4 (by rfl) ⟨179505, by rfl⟩ : syracuseStep 1914725 = 359011) (by norm_num)
theorem B1816501 : Blo 1132632 1816501 := bbase (se 5 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 1816501 = 170297) (by norm_num)
theorem B3225541 : Blo 1132632 3225541 := bbase (se 4 (by rfl) ⟨302394, by rfl⟩ : syracuseStep 3225541 = 604789) (by norm_num)
theorem B1914853 : Blo 1132632 1914853 := bbase (se 4 (by rfl) ⟨179517, by rfl⟩ : syracuseStep 1914853 = 359035) (by norm_num)
theorem B1914941 : Blo 1132632 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B1816757 : Blo 1132632 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B1915069 : Blo 1132632 1915069 := bbase (se 3 (by rfl) ⟨359075, by rfl⟩ : syracuseStep 1915069 = 718151) (by norm_num)
theorem B1915157 : Blo 1132632 1915157 := bbase (se 6 (by rfl) ⟨44886, by rfl⟩ : syracuseStep 1915157 = 89773) (by norm_num)
theorem B1816949 : Blo 1132632 1816949 := bbase (se 5 (by rfl) ⟨85169, by rfl⟩ : syracuseStep 1816949 = 170339) (by norm_num)
theorem B1915285 : Blo 1132632 1915285 := bbase (se 6 (by rfl) ⟨44889, by rfl⟩ : syracuseStep 1915285 = 89779) (by norm_num)
theorem B1915373 : Blo 1132632 1915373 := bbase (se 3 (by rfl) ⟨359132, by rfl⟩ : syracuseStep 1915373 = 718265) (by norm_num)
theorem B2767421 : Blo 1132632 2767421 := bbase (se 3 (by rfl) ⟨518891, by rfl⟩ : syracuseStep 2767421 = 1037783) (by norm_num)
theorem B4307525 : Blo 1132632 4307525 := bbase (se 4 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 4307525 = 807661) (by norm_num)
theorem B1915501 : Blo 1132632 1915501 := bbase (se 3 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 1915501 = 718313) (by norm_num)
theorem B2046605 : Blo 1132632 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B1915589 : Blo 1132632 1915589 := bbase (se 4 (by rfl) ⟨179586, by rfl⟩ : syracuseStep 1915589 = 359173) (by norm_num)
theorem B1227505 : Blo 1132632 1227505 := bbase (se 2 (by rfl) ⟨460314, by rfl⟩ : syracuseStep 1227505 = 920629) (by norm_num)
theorem B3062533 : Blo 1132632 3062533 := bbase (se 4 (by rfl) ⟨287112, by rfl⟩ : syracuseStep 3062533 = 574225) (by norm_num)
theorem B5749541 : Blo 1132632 5749541 := bbase (se 4 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 5749541 = 1078039) (by norm_num)
theorem B1915717 : Blo 1132632 1915717 := bbase (se 4 (by rfl) ⟨179598, by rfl⟩ : syracuseStep 1915717 = 359197) (by norm_num)
theorem B4307813 : Blo 1132632 4307813 := bbase (se 4 (by rfl) ⟨403857, by rfl⟩ : syracuseStep 4307813 = 807715) (by norm_num)
theorem B1915805 : Blo 1132632 1915805 := bbase (se 3 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 1915805 = 718427) (by norm_num)
theorem B1293229 : Blo 1132632 1293229 := bbase (se 3 (by rfl) ⟨242480, by rfl⟩ : syracuseStep 1293229 = 484961) (by norm_num)
theorem B3226645 : Blo 1132632 3226645 := bbase (se 6 (by rfl) ⟨75624, by rfl⟩ : syracuseStep 3226645 = 151249) (by norm_num)
theorem B1915933 : Blo 1132632 1915933 := bbase (se 3 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 1915933 = 718475) (by norm_num)
theorem B4602997 : Blo 1132632 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B1916021 : Blo 1132632 1916021 := bbase (se 5 (by rfl) ⟨89813, by rfl⟩ : syracuseStep 1916021 = 179627) (by norm_num)
theorem B4603013 : Blo 1132632 4603013 := bbase (se 4 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 4603013 = 863065) (by norm_num)
theorem B16333973 : Blo 1132632 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B1916149 : Blo 1132632 1916149 := bbase (se 5 (by rfl) ⟨89819, by rfl⟩ : syracuseStep 1916149 = 179639) (by norm_num)
theorem B1817885 : Blo 1132632 1817885 := bbase (se 3 (by rfl) ⟨340853, by rfl⟩ : syracuseStep 1817885 = 681707) (by norm_num)
theorem B1916237 : Blo 1132632 1916237 := bbase (se 3 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 1916237 = 718589) (by norm_num)
theorem B1916365 : Blo 1132632 1916365 := bbase (se 3 (by rfl) ⟨359318, by rfl⟩ : syracuseStep 1916365 = 718637) (by norm_num)
theorem B1916453 : Blo 1132632 1916453 := bbase (se 4 (by rfl) ⟨179667, by rfl⟩ : syracuseStep 1916453 = 359335) (by norm_num)
theorem B1818269 : Blo 1132632 1818269 := bbase (se 3 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 1818269 = 681851) (by norm_num)
theorem B1916581 : Blo 1132632 1916581 := bbase (se 4 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 1916581 = 359359) (by norm_num)
theorem B1916669 : Blo 1132632 1916669 := bbase (se 3 (by rfl) ⟨359375, by rfl⟩ : syracuseStep 1916669 = 718751) (by norm_num)
theorem B1294105 : Blo 1132632 1294105 := bbase (se 2 (by rfl) ⟨485289, by rfl⟩ : syracuseStep 1294105 = 970579) (by norm_num)
theorem B1818397 : Blo 1132632 1818397 := bbase (se 3 (by rfl) ⟨340949, by rfl⟩ : syracuseStep 1818397 = 681899) (by norm_num)
theorem B1916797 : Blo 1132632 1916797 := bbase (se 3 (by rfl) ⟨359399, by rfl⟩ : syracuseStep 1916797 = 718799) (by norm_num)
theorem B1916885 : Blo 1132632 1916885 := bbase (se 7 (by rfl) ⟨22463, by rfl⟩ : syracuseStep 1916885 = 44927) (by norm_num)
theorem B2867197 : Blo 1132632 2867197 := bbase (se 3 (by rfl) ⟨537599, by rfl⟩ : syracuseStep 2867197 = 1075199) (by norm_num)
theorem B4308997 : Blo 1132632 4308997 := bbase (se 4 (by rfl) ⟨403968, by rfl⟩ : syracuseStep 4308997 = 807937) (by norm_num)
theorem B5750837 : Blo 1132632 5750837 := bbase (se 5 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 5750837 = 539141) (by norm_num)
theorem B1917013 : Blo 1132632 1917013 := bbase (se 8 (by rfl) ⟨11232, by rfl⟩ : syracuseStep 1917013 = 22465) (by norm_num)
theorem B2867309 : Blo 1132632 2867309 := bbase (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) (by norm_num)
theorem B1917101 : Blo 1132632 1917101 := bbase (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) (by norm_num)
theorem B2867501 : Blo 1132632 2867501 := bbase (se 3 (by rfl) ⟨537656, by rfl⟩ : syracuseStep 2867501 = 1075313) (by norm_num)
theorem B1917229 : Blo 1132632 1917229 := bbase (se 3 (by rfl) ⟨359480, by rfl⟩ : syracuseStep 1917229 = 718961) (by norm_num)
theorem B4309301 : Blo 1132632 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B1917317 : Blo 1132632 1917317 := bbase (se 4 (by rfl) ⟨179748, by rfl⟩ : syracuseStep 1917317 = 359497) (by norm_num)
theorem B7258517 : Blo 1132632 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B3228149 : Blo 1132632 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B1917445 : Blo 1132632 1917445 := bbase (se 4 (by rfl) ⟨179760, by rfl⟩ : syracuseStep 1917445 = 359521) (by norm_num)
theorem B1917533 : Blo 1132632 1917533 := bbase (se 3 (by rfl) ⟨359537, by rfl⟩ : syracuseStep 1917533 = 719075) (by norm_num)
theorem B2867845 : Blo 1132632 2867845 := bbase (se 4 (by rfl) ⟨268860, by rfl⟩ : syracuseStep 2867845 = 537721) (by norm_num)
theorem B1917661 : Blo 1132632 1917661 := bbase (se 3 (by rfl) ⟨359561, by rfl⟩ : syracuseStep 1917661 = 719123) (by norm_num)
theorem B2867957 : Blo 1132632 2867957 := bbase (se 5 (by rfl) ⟨134435, by rfl⟩ : syracuseStep 2867957 = 268871) (by norm_num)
theorem B1819397 : Blo 1132632 1819397 := bbase (se 4 (by rfl) ⟨170568, by rfl⟩ : syracuseStep 1819397 = 341137) (by norm_num)
theorem B20726549 : Blo 1132632 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B1917749 : Blo 1132632 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B1819525 : Blo 1132632 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B2868149 : Blo 1132632 2868149 := bbase (se 5 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 2868149 = 268889) (by norm_num)
theorem B1917877 : Blo 1132632 1917877 := bbase (se 5 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 1917877 = 179801) (by norm_num)
theorem B1917965 : Blo 1132632 1917965 := bbase (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) (by norm_num)
theorem B1295437 : Blo 1132632 1295437 := bbase (se 3 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 1295437 = 485789) (by norm_num)
theorem B12928085 : Blo 1132632 12928085 := bbase (se 8 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 12928085 = 151501) (by norm_num)
theorem B46613717 : Blo 1132632 46613717 := bbase (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) (by norm_num)
theorem B1819909 : Blo 1132632 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B2868493 : Blo 1132632 2868493 := bbase (se 3 (by rfl) ⟨537842, by rfl⟩ : syracuseStep 2868493 = 1075685) (by norm_num)
theorem B5752133 : Blo 1132632 5752133 := bbase (se 4 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 5752133 = 1078525) (by norm_num)
theorem B2868605 : Blo 1132632 2868605 := bbase (se 3 (by rfl) ⟨537863, by rfl⟩ : syracuseStep 2868605 = 1075727) (by norm_num)
theorem B1230277 : Blo 1132632 1230277 := bbase (se 4 (by rfl) ⟨115338, by rfl⟩ : syracuseStep 1230277 = 230677) (by norm_num)
theorem B1361405 : Blo 1132632 1361405 := bbase (se 3 (by rfl) ⟨255263, by rfl⟩ : syracuseStep 1361405 = 510527) (by norm_num)
theorem B1820165 : Blo 1132632 1820165 := bbase (se 4 (by rfl) ⟨170640, by rfl⟩ : syracuseStep 1820165 = 341281) (by norm_num)
theorem B1361453 : Blo 1132632 1361453 := bbase (se 3 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 1361453 = 510545) (by norm_num)
theorem B2868797 : Blo 1132632 2868797 := bbase (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) (by norm_num)
theorem B1361549 : Blo 1132632 1361549 := bbase (se 3 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 1361549 = 510581) (by norm_num)
theorem B5457557 : Blo 1132632 5457557 := bbase (se 6 (by rfl) ⟨127911, by rfl⟩ : syracuseStep 5457557 = 255823) (by norm_num)
theorem B6473429 : Blo 1132632 6473429 := bbase (se 7 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 6473429 = 151721) (by norm_num)
theorem B1361713 : Blo 1132632 1361713 := bbase (se 2 (by rfl) ⟨510642, by rfl⟩ : syracuseStep 1361713 = 1021285) (by norm_num)
theorem B2869141 : Blo 1132632 2869141 := bbase (se 6 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 2869141 = 134491) (by norm_num)
theorem B2869253 : Blo 1132632 2869253 := bbase (se 4 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 2869253 = 537985) (by norm_num)
theorem B1361929 : Blo 1132632 1361929 := bbase (se 2 (by rfl) ⟨510723, by rfl⟩ : syracuseStep 1361929 = 1021447) (by norm_num)
theorem B3229733 : Blo 1132632 3229733 := bbase (se 4 (by rfl) ⟨302787, by rfl⟩ : syracuseStep 3229733 = 605575) (by norm_num)
theorem B1362097 : Blo 1132632 1362097 := bbase (se 2 (by rfl) ⟨510786, by rfl⟩ : syracuseStep 1362097 = 1021573) (by norm_num)
theorem B2869445 : Blo 1132632 2869445 := bbase (se 4 (by rfl) ⟨269010, by rfl⟩ : syracuseStep 2869445 = 538021) (by norm_num)
theorem B5458229 : Blo 1132632 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B4311413 : Blo 1132632 4311413 := bbase (se 5 (by rfl) ⟨202097, by rfl⟩ : syracuseStep 4311413 = 404195) (by norm_num)
theorem B4147685 : Blo 1132632 4147685 := bbase (se 4 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 4147685 = 777691) (by norm_num)
theorem B2869789 : Blo 1132632 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B5753429 : Blo 1132632 5753429 := bbase (se 8 (by rfl) ⟨33711, by rfl⟩ : syracuseStep 5753429 = 67423) (by norm_num)
theorem B2869901 : Blo 1132632 2869901 := bbase (se 3 (by rfl) ⟨538106, by rfl⟩ : syracuseStep 2869901 = 1076213) (by norm_num)
theorem B4311701 : Blo 1132632 4311701 := bbase (se 6 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 4311701 = 202111) (by norm_num)
theorem B1362625 : Blo 1132632 1362625 := bbase (se 2 (by rfl) ⟨510984, by rfl⟩ : syracuseStep 1362625 = 1021969) (by norm_num)
theorem B3230405 : Blo 1132632 3230405 := bbase (se 4 (by rfl) ⟨302850, by rfl⟩ : syracuseStep 3230405 = 605701) (by norm_num)
theorem B1723205 : Blo 1132632 1723205 := bbase (se 4 (by rfl) ⟨161550, by rfl⟩ : syracuseStep 1723205 = 323101) (by norm_num)
theorem B2870093 : Blo 1132632 2870093 := bbase (se 3 (by rfl) ⟨538142, by rfl⟩ : syracuseStep 2870093 = 1076285) (by norm_num)
theorem B8604629 : Blo 1132632 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B3230837 : Blo 1132632 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B2870437 : Blo 1132632 2870437 := bbase (se 4 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 2870437 = 538207) (by norm_num)
theorem B28331221 : Blo 1132632 28331221 := bbase (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) (by norm_num)
theorem B3067109 : Blo 1132632 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B9194741 : Blo 1132632 9194741 := bbase (se 5 (by rfl) ⟨431003, by rfl⟩ : syracuseStep 9194741 = 862007) (by norm_num)
theorem B2870549 : Blo 1132632 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B4083061 : Blo 1132632 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B1723789 : Blo 1132632 1723789 := bbase (se 3 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 1723789 = 646421) (by norm_num)
theorem B2870741 : Blo 1132632 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B1363721 : Blo 1132632 1363721 := bbase (se 2 (by rfl) ⟨511395, by rfl⟩ : syracuseStep 1363721 = 1022791) (by norm_num)
theorem B2871085 : Blo 1132632 2871085 := bbase (se 3 (by rfl) ⟨538328, by rfl⟩ : syracuseStep 2871085 = 1076657) (by norm_num)
theorem B4312885 : Blo 1132632 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B3231589 : Blo 1132632 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B2871197 : Blo 1132632 2871197 := bbase (se 3 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 2871197 = 1076699) (by norm_num)
theorem B1703933 : Blo 1132632 1703933 := bbase (se 3 (by rfl) ⟨319487, by rfl⟩ : syracuseStep 1703933 = 638975) (by norm_num)
theorem B2871389 : Blo 1132632 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B4313189 : Blo 1132632 4313189 := bbase (se 4 (by rfl) ⟨404361, by rfl⟩ : syracuseStep 4313189 = 808723) (by norm_num)
theorem B2150725 : Blo 1132632 2150725 := bbase (se 4 (by rfl) ⟨201630, by rfl⟩ : syracuseStep 2150725 = 403261) (by norm_num)
theorem B4084069 : Blo 1132632 4084069 := bbase (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) (by norm_num)
theorem B3887461 : Blo 1132632 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B2871733 : Blo 1132632 2871733 := bbase (se 5 (by rfl) ⟨134612, by rfl⟩ : syracuseStep 2871733 = 269225) (by norm_num)
theorem B1364413 : Blo 1132632 1364413 := bbase (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) (by norm_num)
theorem B2150869 : Blo 1132632 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B1364509 : Blo 1132632 1364509 := bbase (se 3 (by rfl) ⟨255845, by rfl⟩ : syracuseStep 1364509 = 511691) (by norm_num)
theorem B2871845 : Blo 1132632 2871845 := bbase (se 4 (by rfl) ⟨269235, by rfl⟩ : syracuseStep 2871845 = 538471) (by norm_num)
theorem B3494453 : Blo 1132632 3494453 := bbase (se 5 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 3494453 = 327605) (by norm_num)
theorem B2183773 : Blo 1132632 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B2151029 : Blo 1132632 2151029 := bbase (se 5 (by rfl) ⟨100829, by rfl⟩ : syracuseStep 2151029 = 201659) (by norm_num)
theorem B2872037 : Blo 1132632 2872037 := bbase (se 4 (by rfl) ⟨269253, by rfl⟩ : syracuseStep 2872037 = 538507) (by norm_num)
theorem B2151173 : Blo 1132632 2151173 := bbase (se 4 (by rfl) ⟨201672, by rfl⟩ : syracuseStep 2151173 = 403345) (by norm_num)
theorem B1364893 : Blo 1132632 1364893 := bbase (se 3 (by rfl) ⟨255917, by rfl⟩ : syracuseStep 1364893 = 511835) (by norm_num)
theorem B2151461 : Blo 1132632 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B2872381 : Blo 1132632 2872381 := bbase (se 3 (by rfl) ⟨538571, by rfl⟩ : syracuseStep 2872381 = 1077143) (by norm_num)
theorem B2872493 : Blo 1132632 2872493 := bbase (se 3 (by rfl) ⟨538592, by rfl⟩ : syracuseStep 2872493 = 1077185) (by norm_num)
theorem B2151613 : Blo 1132632 2151613 := bbase (se 3 (by rfl) ⟨403427, by rfl⟩ : syracuseStep 2151613 = 806855) (by norm_num)
theorem B3822821 : Blo 1132632 3822821 := bbase (se 4 (by rfl) ⟨358389, by rfl⟩ : syracuseStep 3822821 = 716779) (by norm_num)
theorem B2872685 : Blo 1132632 2872685 := bbase (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) (by norm_num)
theorem B2151917 : Blo 1132632 2151917 := bbase (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) (by norm_num)
theorem B3823253 : Blo 1132632 3823253 := bbase (se 6 (by rfl) ⟨89607, by rfl⟩ : syracuseStep 3823253 = 179215) (by norm_num)
theorem B2873029 : Blo 1132632 2873029 := bbase (se 4 (by rfl) ⟨269346, by rfl⟩ : syracuseStep 2873029 = 538693) (by norm_num)
theorem B2873141 : Blo 1132632 2873141 := bbase (se 5 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 2873141 = 269357) (by norm_num)
theorem B8181749 : Blo 1132632 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B2873333 : Blo 1132632 2873333 := bbase (se 5 (by rfl) ⟨134687, by rfl⟩ : syracuseStep 2873333 = 269375) (by norm_num)
theorem B3823685 : Blo 1132632 3823685 := bbase (se 4 (by rfl) ⟨358470, by rfl⟩ : syracuseStep 3823685 = 716941) (by norm_num)
theorem B4315301 : Blo 1132632 4315301 := bbase (se 4 (by rfl) ⟨404559, by rfl⟩ : syracuseStep 4315301 = 809119) (by norm_num)
theorem B2152669 : Blo 1132632 2152669 := bbase (se 3 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 2152669 = 807251) (by norm_num)
theorem B2873677 : Blo 1132632 2873677 := bbase (se 3 (by rfl) ⟨538814, by rfl⟩ : syracuseStep 2873677 = 1077629) (by norm_num)
theorem B2152813 : Blo 1132632 2152813 := bbase (se 3 (by rfl) ⟨403652, by rfl⟩ : syracuseStep 2152813 = 807305) (by norm_num)
theorem B2873789 : Blo 1132632 2873789 := bbase (se 3 (by rfl) ⟨538835, by rfl⟩ : syracuseStep 2873789 = 1077671) (by norm_num)
theorem B4315589 : Blo 1132632 4315589 := bbase (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) (by norm_num)
theorem B3824117 : Blo 1132632 3824117 := bbase (se 5 (by rfl) ⟨179255, by rfl⟩ : syracuseStep 3824117 = 358511) (by norm_num)
theorem B2152973 : Blo 1132632 2152973 := bbase (se 3 (by rfl) ⟨403682, by rfl⟩ : syracuseStep 2152973 = 807365) (by norm_num)
theorem B2185805 : Blo 1132632 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B4840037 : Blo 1132632 4840037 := bbase (se 4 (by rfl) ⟨453753, by rfl⟩ : syracuseStep 4840037 = 907507) (by norm_num)
theorem B2873981 : Blo 1132632 2873981 := bbase (se 3 (by rfl) ⟨538871, by rfl⟩ : syracuseStep 2873981 = 1077743) (by norm_num)
theorem B3234437 : Blo 1132632 3234437 := bbase (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) (by norm_num)
theorem B2153117 : Blo 1132632 2153117 := bbase (se 3 (by rfl) ⟨403709, by rfl⟩ : syracuseStep 2153117 = 807419) (by norm_num)
theorem B1727165 : Blo 1132632 1727165 := bbase (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) (by norm_num)
theorem B2906933 : Blo 1132632 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B3824549 : Blo 1132632 3824549 := bbase (se 4 (by rfl) ⟨358551, by rfl⟩ : syracuseStep 3824549 = 717103) (by norm_num)
theorem B2153405 : Blo 1132632 2153405 := bbase (se 3 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 2153405 = 807527) (by norm_num)
theorem B2874325 : Blo 1132632 2874325 := bbase (se 7 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 2874325 = 67367) (by norm_num)
theorem B8739829 : Blo 1132632 8739829 := bbase (se 5 (by rfl) ⟨409679, by rfl⟩ : syracuseStep 8739829 = 819359) (by norm_num)
theorem B2874437 : Blo 1132632 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B49699925 : Blo 1132632 49699925 := bbase (se 8 (by rfl) ⟨291210, by rfl⟩ : syracuseStep 49699925 = 582421) (by norm_num)
theorem B2153557 : Blo 1132632 2153557 := bbase (se 8 (by rfl) ⟨12618, by rfl⟩ : syracuseStep 2153557 = 25237) (by norm_num)
theorem B2186389 : Blo 1132632 2186389 := bbase (se 6 (by rfl) ⟨51243, by rfl⟩ : syracuseStep 2186389 = 102487) (by norm_num)
theorem B5823701 : Blo 1132632 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B2874629 : Blo 1132632 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B1400101 : Blo 1132632 1400101 := bbase (se 4 (by rfl) ⟨131259, by rfl⟩ : syracuseStep 1400101 = 262519) (by norm_num)
theorem B1727797 : Blo 1132632 1727797 := bbase (se 5 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 1727797 = 161981) (by norm_num)
theorem B3824981 : Blo 1132632 3824981 := bbase (se 11 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 3824981 = 5603) (by norm_num)
theorem B14736725 : Blo 1132632 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B2153861 : Blo 1132632 2153861 := bbase (se 4 (by rfl) ⟨201924, by rfl⟩ : syracuseStep 2153861 = 403849) (by norm_num)
theorem B2874973 : Blo 1132632 2874973 := bbase (se 3 (by rfl) ⟨539057, by rfl⟩ : syracuseStep 2874973 = 1078115) (by norm_num)
theorem B2875085 : Blo 1132632 2875085 := bbase (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) (by norm_num)
theorem B3825413 : Blo 1132632 3825413 := bbase (se 4 (by rfl) ⟨358632, by rfl⟩ : syracuseStep 3825413 = 717265) (by norm_num)
theorem B3235621 : Blo 1132632 3235621 := bbase (se 4 (by rfl) ⟨303339, by rfl⟩ : syracuseStep 3235621 = 606679) (by norm_num)
theorem B7757621 : Blo 1132632 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B3628901 : Blo 1132632 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B2875277 : Blo 1132632 2875277 := bbase (se 3 (by rfl) ⟨539114, by rfl⟩ : syracuseStep 2875277 = 1078229) (by norm_num)
theorem B1433533 : Blo 1132632 1433533 := bbase (se 3 (by rfl) ⟨268787, by rfl⟩ : syracuseStep 1433533 = 537575) (by norm_num)
theorem B3235781 : Blo 1132632 3235781 := bbase (se 4 (by rfl) ⟨303354, by rfl⟩ : syracuseStep 3235781 = 606709) (by norm_num)
theorem B1433629 : Blo 1132632 1433629 := bbase (se 3 (by rfl) ⟨268805, by rfl⟩ : syracuseStep 1433629 = 537611) (by norm_num)
theorem B2154613 : Blo 1132632 2154613 := bbase (se 5 (by rfl) ⟨100997, by rfl⟩ : syracuseStep 2154613 = 201995) (by norm_num)
theorem B3825845 : Blo 1132632 3825845 := bbase (se 5 (by rfl) ⟨179336, by rfl⟩ : syracuseStep 3825845 = 358673) (by norm_num)
theorem B3236021 : Blo 1132632 3236021 := bbase (se 5 (by rfl) ⟨151688, by rfl⟩ : syracuseStep 3236021 = 303377) (by norm_num)
theorem B1433801 : Blo 1132632 1433801 := bbase (se 2 (by rfl) ⟨537675, by rfl⟩ : syracuseStep 1433801 = 1075351) (by norm_num)
theorem B2875621 : Blo 1132632 2875621 := bbase (se 4 (by rfl) ⟨269589, by rfl⟩ : syracuseStep 2875621 = 539179) (by norm_num)
theorem B1433857 : Blo 1132632 1433857 := bbase (se 2 (by rfl) ⟨537696, by rfl⟩ : syracuseStep 1433857 = 1075393) (by norm_num)
theorem B2154757 : Blo 1132632 2154757 := bbase (se 4 (by rfl) ⟨202008, by rfl⟩ : syracuseStep 2154757 = 404017) (by norm_num)
theorem B1532197 : Blo 1132632 1532197 := bbase (se 4 (by rfl) ⟨143643, by rfl⟩ : syracuseStep 1532197 = 287287) (by norm_num)
theorem B2908493 : Blo 1132632 2908493 := bbase (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) (by norm_num)
theorem B2875733 : Blo 1132632 2875733 := bbase (se 10 (by rfl) ⟨4212, by rfl⟩ : syracuseStep 2875733 = 8425) (by norm_num)
theorem B1433953 : Blo 1132632 1433953 := bbase (se 2 (by rfl) ⟨537732, by rfl⟩ : syracuseStep 1433953 = 1075465) (by norm_num)
theorem B3236213 : Blo 1132632 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2154917 : Blo 1132632 2154917 := bbase (se 4 (by rfl) ⟨202023, by rfl⟩ : syracuseStep 2154917 = 404047) (by norm_num)
theorem B1434125 : Blo 1132632 1434125 := bbase (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) (by norm_num)
theorem B2875925 : Blo 1132632 2875925 := bbase (se 6 (by rfl) ⟨67404, by rfl⟩ : syracuseStep 2875925 = 134809) (by norm_num)
theorem B2155061 : Blo 1132632 2155061 := bbase (se 5 (by rfl) ⟨101018, by rfl⟩ : syracuseStep 2155061 = 202037) (by norm_num)
theorem B1434181 : Blo 1132632 1434181 := bbase (se 4 (by rfl) ⟨134454, by rfl⟩ : syracuseStep 1434181 = 268909) (by norm_num)
theorem B3826277 : Blo 1132632 3826277 := bbase (se 4 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 3826277 = 717427) (by norm_num)
theorem B1434277 : Blo 1132632 1434277 := bbase (se 4 (by rfl) ⟨134463, by rfl⟩ : syracuseStep 1434277 = 268927) (by norm_num)
theorem B8741621 : Blo 1132632 8741621 := bbase (se 5 (by rfl) ⟨409763, by rfl⟩ : syracuseStep 8741621 = 819527) (by norm_num)
theorem B2548493 : Blo 1132632 2548493 := bbase (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) (by norm_num)
theorem B1434449 : Blo 1132632 1434449 := bbase (se 2 (by rfl) ⟨537918, by rfl⟩ : syracuseStep 1434449 = 1075837) (by norm_num)
theorem B2548565 : Blo 1132632 2548565 := bbase (se 9 (by rfl) ⟨7466, by rfl⟩ : syracuseStep 2548565 = 14933) (by norm_num)
theorem B2155349 : Blo 1132632 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B2909029 : Blo 1132632 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B2876269 : Blo 1132632 2876269 := bbase (se 3 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 2876269 = 1078601) (by norm_num)
theorem B1434505 : Blo 1132632 1434505 := bbase (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) (by norm_num)
theorem B2548637 : Blo 1132632 2548637 := bbase (se 3 (by rfl) ⟨477869, by rfl⟩ : syracuseStep 2548637 = 955739) (by norm_num)
theorem B2876381 : Blo 1132632 2876381 := bbase (se 3 (by rfl) ⟨539321, by rfl⟩ : syracuseStep 2876381 = 1078643) (by norm_num)
theorem B2548709 : Blo 1132632 2548709 := bbase (se 4 (by rfl) ⟨238941, by rfl⟩ : syracuseStep 2548709 = 477883) (by norm_num)
theorem B1434601 : Blo 1132632 1434601 := bbase (se 2 (by rfl) ⟨537975, by rfl⟩ : syracuseStep 1434601 = 1075951) (by norm_num)
theorem B2155501 : Blo 1132632 2155501 := bbase (se 3 (by rfl) ⟨404156, by rfl⟩ : syracuseStep 2155501 = 808313) (by norm_num)
theorem B3826709 : Blo 1132632 3826709 := bbase (se 6 (by rfl) ⟨89688, by rfl⟩ : syracuseStep 3826709 = 179377) (by norm_num)
theorem B2548781 : Blo 1132632 2548781 := bbase (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) (by norm_num)
theorem B2548853 : Blo 1132632 2548853 := bbase (se 5 (by rfl) ⟨119477, by rfl⟩ : syracuseStep 2548853 = 238955) (by norm_num)
theorem B1434773 : Blo 1132632 1434773 := bbase (se 6 (by rfl) ⟨33627, by rfl⟩ : syracuseStep 1434773 = 67255) (by norm_num)
theorem B2876573 : Blo 1132632 2876573 := bbase (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) (by norm_num)
theorem B3105973 : Blo 1132632 3105973 := bbase (se 5 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 3105973 = 291185) (by norm_num)
theorem B2548925 : Blo 1132632 2548925 := bbase (se 3 (by rfl) ⟨477923, by rfl⟩ : syracuseStep 2548925 = 955847) (by norm_num)
theorem B1434829 : Blo 1132632 1434829 := bbase (se 3 (by rfl) ⟨269030, by rfl⟩ : syracuseStep 1434829 = 538061) (by norm_num)
theorem B2548997 : Blo 1132632 2548997 := bbase (se 4 (by rfl) ⟨238968, by rfl⟩ : syracuseStep 2548997 = 477937) (by norm_num)
theorem B2155805 : Blo 1132632 2155805 := bbase (se 3 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 2155805 = 808427) (by norm_num)
theorem B1434925 : Blo 1132632 1434925 := bbase (se 3 (by rfl) ⟨269048, by rfl⟩ : syracuseStep 1434925 = 538097) (by norm_num)
theorem B2549069 : Blo 1132632 2549069 := bbase (se 3 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 2549069 = 955901) (by norm_num)
theorem B2549141 : Blo 1132632 2549141 := bbase (se 6 (by rfl) ⟨59745, by rfl⟩ : syracuseStep 2549141 = 119491) (by norm_num)
theorem B3827141 : Blo 1132632 3827141 := bbase (se 4 (by rfl) ⟨358794, by rfl⟩ : syracuseStep 3827141 = 717589) (by norm_num)
theorem B1435097 : Blo 1132632 1435097 := bbase (se 2 (by rfl) ⟨538161, by rfl⟩ : syracuseStep 1435097 = 1076323) (by norm_num)
theorem B2549213 : Blo 1132632 2549213 := bbase (se 3 (by rfl) ⟨477977, by rfl⟩ : syracuseStep 2549213 = 955955) (by norm_num)
theorem B2876917 : Blo 1132632 2876917 := bbase (se 5 (by rfl) ⟨134855, by rfl⟩ : syracuseStep 2876917 = 269711) (by norm_num)
theorem B1435153 : Blo 1132632 1435153 := bbase (se 2 (by rfl) ⟨538182, by rfl⟩ : syracuseStep 1435153 = 1076365) (by norm_num)
theorem B2549285 : Blo 1132632 2549285 := bbase (se 4 (by rfl) ⟨238995, by rfl⟩ : syracuseStep 2549285 = 477991) (by norm_num)
theorem B2877029 : Blo 1132632 2877029 := bbase (se 4 (by rfl) ⟨269721, by rfl⟩ : syracuseStep 2877029 = 539443) (by norm_num)
theorem B2549357 : Blo 1132632 2549357 := bbase (se 3 (by rfl) ⟨478004, by rfl⟩ : syracuseStep 2549357 = 956009) (by norm_num)
theorem B1435249 : Blo 1132632 1435249 := bbase (se 2 (by rfl) ⟨538218, by rfl⟩ : syracuseStep 1435249 = 1076437) (by norm_num)
theorem B2549429 : Blo 1132632 2549429 := bbase (se 5 (by rfl) ⟨119504, by rfl⟩ : syracuseStep 2549429 = 239009) (by norm_num)
theorem B4908773 : Blo 1132632 4908773 := bbase (se 4 (by rfl) ⟨460197, by rfl⟩ : syracuseStep 4908773 = 920395) (by norm_num)
theorem B2549501 : Blo 1132632 2549501 := bbase (se 3 (by rfl) ⟨478031, by rfl⟩ : syracuseStep 2549501 = 956063) (by norm_num)
theorem B1435421 : Blo 1132632 1435421 := bbase (se 3 (by rfl) ⟨269141, by rfl⟩ : syracuseStep 1435421 = 538283) (by norm_num)
theorem B2549573 : Blo 1132632 2549573 := bbase (se 4 (by rfl) ⟨239022, by rfl⟩ : syracuseStep 2549573 = 478045) (by norm_num)
theorem B1435477 : Blo 1132632 1435477 := bbase (se 9 (by rfl) ⟨4205, by rfl⟩ : syracuseStep 1435477 = 8411) (by norm_num)
theorem B3827573 : Blo 1132632 3827573 := bbase (se 5 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 3827573 = 358835) (by norm_num)
theorem B10905461 : Blo 1132632 10905461 := bbase (se 5 (by rfl) ⟨511193, by rfl⟩ : syracuseStep 10905461 = 1022387) (by norm_num)
theorem B2549645 : Blo 1132632 2549645 := bbase (se 3 (by rfl) ⟨478058, by rfl⟩ : syracuseStep 2549645 = 956117) (by norm_num)
theorem B1435573 : Blo 1132632 1435573 := bbase (se 5 (by rfl) ⟨67292, by rfl⟩ : syracuseStep 1435573 = 134585) (by norm_num)
theorem B2549717 : Blo 1132632 2549717 := bbase (se 7 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 2549717 = 59759) (by norm_num)
theorem B2156557 : Blo 1132632 2156557 := bbase (se 3 (by rfl) ⟨404354, by rfl⟩ : syracuseStep 2156557 = 808709) (by norm_num)
theorem B2549789 : Blo 1132632 2549789 := bbase (se 3 (by rfl) ⟨478085, by rfl⟩ : syracuseStep 2549789 = 956171) (by norm_num)
theorem B1435745 : Blo 1132632 1435745 := bbase (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) (by norm_num)
theorem B2549861 : Blo 1132632 2549861 := bbase (se 4 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 2549861 = 478099) (by norm_num)
theorem B4909189 : Blo 1132632 4909189 := bbase (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) (by norm_num)
theorem B1435801 : Blo 1132632 1435801 := bbase (se 2 (by rfl) ⟨538425, by rfl⟩ : syracuseStep 1435801 = 1076851) (by norm_num)
theorem B2156701 : Blo 1132632 2156701 := bbase (se 3 (by rfl) ⟨404381, by rfl⟩ : syracuseStep 2156701 = 808763) (by norm_num)
theorem B2549933 : Blo 1132632 2549933 := bbase (se 3 (by rfl) ⟨478112, by rfl⟩ : syracuseStep 2549933 = 956225) (by norm_num)
theorem B2550005 : Blo 1132632 2550005 := bbase (se 5 (by rfl) ⟨119531, by rfl⟩ : syracuseStep 2550005 = 239063) (by norm_num)
theorem B1435897 : Blo 1132632 1435897 := bbase (se 2 (by rfl) ⟨538461, by rfl⟩ : syracuseStep 1435897 = 1076923) (by norm_num)
theorem B3828005 : Blo 1132632 3828005 := bbase (se 4 (by rfl) ⟨358875, by rfl⟩ : syracuseStep 3828005 = 717751) (by norm_num)
theorem B2550077 : Blo 1132632 2550077 := bbase (se 3 (by rfl) ⟨478139, by rfl⟩ : syracuseStep 2550077 = 956279) (by norm_num)
theorem B2156861 : Blo 1132632 2156861 := bbase (se 3 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 2156861 = 808823) (by norm_num)
theorem B2550149 : Blo 1132632 2550149 := bbase (se 4 (by rfl) ⟨239076, by rfl⟩ : syracuseStep 2550149 = 478153) (by norm_num)
theorem B1534349 : Blo 1132632 1534349 := bbase (se 3 (by rfl) ⟨287690, by rfl⟩ : syracuseStep 1534349 = 575381) (by norm_num)
theorem B1436069 : Blo 1132632 1436069 := bbase (se 4 (by rfl) ⟨134631, by rfl⟩ : syracuseStep 1436069 = 269263) (by norm_num)
theorem B2550221 : Blo 1132632 2550221 := bbase (se 3 (by rfl) ⟨478166, by rfl⟩ : syracuseStep 2550221 = 956333) (by norm_num)
theorem B2157005 : Blo 1132632 2157005 := bbase (se 3 (by rfl) ⟨404438, by rfl⟩ : syracuseStep 2157005 = 808877) (by norm_num)
theorem B1436125 : Blo 1132632 1436125 := bbase (se 3 (by rfl) ⟨269273, by rfl⟩ : syracuseStep 1436125 = 538547) (by norm_num)
theorem B2910701 : Blo 1132632 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B2550293 : Blo 1132632 2550293 := bbase (se 6 (by rfl) ⟨59772, by rfl⟩ : syracuseStep 2550293 = 119545) (by norm_num)
theorem B4844069 : Blo 1132632 4844069 := bbase (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) (by norm_num)
theorem B8612405 : Blo 1132632 8612405 := bbase (se 5 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 8612405 = 807413) (by norm_num)
theorem B1436221 : Blo 1132632 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B2550365 : Blo 1132632 2550365 := bbase (se 3 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 2550365 = 956387) (by norm_num)
theorem B2419301 : Blo 1132632 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B2550437 : Blo 1132632 2550437 := bbase (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) (by norm_num)
theorem B9693877 : Blo 1132632 9693877 := bbase (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) (by norm_num)
theorem B3828437 : Blo 1132632 3828437 := bbase (se 7 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 3828437 = 89729) (by norm_num)
theorem B1436393 : Blo 1132632 1436393 := bbase (se 2 (by rfl) ⟨538647, by rfl⟩ : syracuseStep 1436393 = 1077295) (by norm_num)
theorem B2550509 : Blo 1132632 2550509 := bbase (se 3 (by rfl) ⟨478220, by rfl⟩ : syracuseStep 2550509 = 956441) (by norm_num)
theorem B2157293 : Blo 1132632 2157293 := bbase (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) (by norm_num)
theorem B1436449 : Blo 1132632 1436449 := bbase (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) (by norm_num)
theorem B2550581 : Blo 1132632 2550581 := bbase (se 5 (by rfl) ⟨119558, by rfl⟩ : syracuseStep 2550581 = 239117) (by norm_num)
theorem B2550653 : Blo 1132632 2550653 := bbase (se 3 (by rfl) ⟨478247, by rfl⟩ : syracuseStep 2550653 = 956495) (by norm_num)
theorem B1436545 : Blo 1132632 1436545 := bbase (se 2 (by rfl) ⟨538704, by rfl⟩ : syracuseStep 1436545 = 1077409) (by norm_num)
theorem B2157445 : Blo 1132632 2157445 := bbase (se 4 (by rfl) ⟨202260, by rfl⟩ : syracuseStep 2157445 = 404521) (by norm_num)
theorem B5827493 : Blo 1132632 5827493 := bbase (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) (by norm_num)
theorem B3632053 : Blo 1132632 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B2550725 : Blo 1132632 2550725 := bbase (se 4 (by rfl) ⟨239130, by rfl⟩ : syracuseStep 2550725 = 478261) (by norm_num)
theorem B2550797 : Blo 1132632 2550797 := bbase (se 3 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 2550797 = 956549) (by norm_num)
theorem B1436717 : Blo 1132632 1436717 := bbase (se 3 (by rfl) ⟨269384, by rfl⟩ : syracuseStep 1436717 = 538769) (by norm_num)
theorem B2550869 : Blo 1132632 2550869 := bbase (se 8 (by rfl) ⟨14946, by rfl⟩ : syracuseStep 2550869 = 29893) (by norm_num)
theorem B1436773 : Blo 1132632 1436773 := bbase (se 4 (by rfl) ⟨134697, by rfl⟩ : syracuseStep 1436773 = 269395) (by norm_num)
theorem B3828869 : Blo 1132632 3828869 := bbase (se 4 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 3828869 = 717913) (by norm_num)
theorem B1698965 : Blo 1132632 1698965 := bbase (se 6 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 1698965 = 79639) (by norm_num)
theorem B2550941 : Blo 1132632 2550941 := bbase (se 3 (by rfl) ⟨478301, by rfl⟩ : syracuseStep 2550941 = 956603) (by norm_num)
theorem B1698989 : Blo 1132632 1698989 := bbase (se 3 (by rfl) ⟨318560, by rfl⟩ : syracuseStep 1698989 = 637121) (by norm_num)
theorem B2157749 : Blo 1132632 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1699013 : Blo 1132632 1699013 := bbase (se 4 (by rfl) ⟨159282, by rfl⟩ : syracuseStep 1699013 = 318565) (by norm_num)
theorem B1436869 : Blo 1132632 1436869 := bbase (se 4 (by rfl) ⟨134706, by rfl⟩ : syracuseStep 1436869 = 269413) (by norm_num)
theorem B4091093 : Blo 1132632 4091093 := bbase (se 7 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 4091093 = 95885) (by norm_num)
theorem B1699037 : Blo 1132632 1699037 := bbase (se 3 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 1699037 = 637139) (by norm_num)
theorem B2551013 : Blo 1132632 2551013 := bbase (se 4 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 2551013 = 478315) (by norm_num)
theorem B1699061 : Blo 1132632 1699061 := bbase (se 5 (by rfl) ⟨79643, by rfl⟩ : syracuseStep 1699061 = 159287) (by norm_num)
theorem B8285429 : Blo 1132632 8285429 := bbase (se 5 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 8285429 = 776759) (by norm_num)
theorem B1699085 : Blo 1132632 1699085 := bbase (se 3 (by rfl) ⟨318578, by rfl⟩ : syracuseStep 1699085 = 637157) (by norm_num)
theorem B1699109 : Blo 1132632 1699109 := bbase (se 4 (by rfl) ⟨159291, by rfl⟩ : syracuseStep 1699109 = 318583) (by norm_num)
theorem B2551085 : Blo 1132632 2551085 := bbase (se 3 (by rfl) ⟨478328, by rfl⟩ : syracuseStep 2551085 = 956657) (by norm_num)
theorem B1699133 : Blo 1132632 1699133 := bbase (se 3 (by rfl) ⟨318587, by rfl⟩ : syracuseStep 1699133 = 637175) (by norm_num)
theorem B1699157 : Blo 1132632 1699157 := bbase (se 11 (by rfl) ⟨1244, by rfl⟩ : syracuseStep 1699157 = 2489) (by norm_num)
theorem B1699181 : Blo 1132632 1699181 := bbase (se 3 (by rfl) ⟨318596, by rfl⟩ : syracuseStep 1699181 = 637193) (by norm_num)
theorem B1437041 : Blo 1132632 1437041 := bbase (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) (by norm_num)
theorem B2551157 : Blo 1132632 2551157 := bbase (se 5 (by rfl) ⟨119585, by rfl⟩ : syracuseStep 2551157 = 239171) (by norm_num)
theorem B1699205 : Blo 1132632 1699205 := bbase (se 4 (by rfl) ⟨159300, by rfl⟩ : syracuseStep 1699205 = 318601) (by norm_num)
theorem B1699229 : Blo 1132632 1699229 := bbase (se 3 (by rfl) ⟨318605, by rfl⟩ : syracuseStep 1699229 = 637211) (by norm_num)
theorem B1437097 : Blo 1132632 1437097 := bbase (se 2 (by rfl) ⟨538911, by rfl⟩ : syracuseStep 1437097 = 1077823) (by norm_num)
theorem B1699253 : Blo 1132632 1699253 := bbase (se 5 (by rfl) ⟨79652, by rfl⟩ : syracuseStep 1699253 = 159305) (by norm_num)
theorem B2551229 : Blo 1132632 2551229 := bbase (se 3 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 2551229 = 956711) (by norm_num)
theorem B1699277 : Blo 1132632 1699277 := bbase (se 3 (by rfl) ⟨318614, by rfl⟩ : syracuseStep 1699277 = 637229) (by norm_num)
theorem B1699301 : Blo 1132632 1699301 := bbase (se 4 (by rfl) ⟨159309, by rfl⟩ : syracuseStep 1699301 = 318619) (by norm_num)
theorem B1699325 : Blo 1132632 1699325 := bbase (se 3 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 1699325 = 637247) (by norm_num)
theorem B2551301 : Blo 1132632 2551301 := bbase (se 4 (by rfl) ⟨239184, by rfl⟩ : syracuseStep 2551301 = 478369) (by norm_num)
theorem B1437193 : Blo 1132632 1437193 := bbase (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) (by norm_num)
theorem B1699349 : Blo 1132632 1699349 := bbase (se 6 (by rfl) ⟨39828, by rfl⟩ : syracuseStep 1699349 = 79657) (by norm_num)
theorem B1699373 : Blo 1132632 1699373 := bbase (se 3 (by rfl) ⟨318632, by rfl⟩ : syracuseStep 1699373 = 637265) (by norm_num)
theorem B3829301 : Blo 1132632 3829301 := bbase (se 5 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 3829301 = 358997) (by norm_num)
theorem B1699397 : Blo 1132632 1699397 := bbase (se 4 (by rfl) ⟨159318, by rfl⟩ : syracuseStep 1699397 = 318637) (by norm_num)
theorem B2551373 : Blo 1132632 2551373 := bbase (se 3 (by rfl) ⟨478382, by rfl⟩ : syracuseStep 2551373 = 956765) (by norm_num)
theorem B1699421 : Blo 1132632 1699421 := bbase (se 3 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 1699421 = 637283) (by norm_num)
theorem B1699445 : Blo 1132632 1699445 := bbase (se 5 (by rfl) ⟨79661, by rfl⟩ : syracuseStep 1699445 = 159323) (by norm_num)
theorem B1699469 : Blo 1132632 1699469 := bbase (se 3 (by rfl) ⟨318650, by rfl⟩ : syracuseStep 1699469 = 637301) (by norm_num)
theorem B2551445 : Blo 1132632 2551445 := bbase (se 6 (by rfl) ⟨59799, by rfl⟩ : syracuseStep 2551445 = 119599) (by norm_num)
theorem B1699493 : Blo 1132632 1699493 := bbase (se 4 (by rfl) ⟨159327, by rfl⟩ : syracuseStep 1699493 = 318655) (by norm_num)
theorem B1437365 : Blo 1132632 1437365 := bbase (se 5 (by rfl) ⟨67376, by rfl⟩ : syracuseStep 1437365 = 134753) (by norm_num)
theorem B1699517 : Blo 1132632 1699517 := bbase (se 3 (by rfl) ⟨318659, by rfl⟩ : syracuseStep 1699517 = 637319) (by norm_num)
theorem B4419269 : Blo 1132632 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B1699541 : Blo 1132632 1699541 := bbase (se 7 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 1699541 = 39833) (by norm_num)
theorem B2551517 : Blo 1132632 2551517 := bbase (se 3 (by rfl) ⟨478409, by rfl⟩ : syracuseStep 2551517 = 956819) (by norm_num)
theorem B1699565 : Blo 1132632 1699565 := bbase (se 3 (by rfl) ⟨318668, by rfl⟩ : syracuseStep 1699565 = 637337) (by norm_num)
theorem B1437421 : Blo 1132632 1437421 := bbase (se 3 (by rfl) ⟨269516, by rfl⟩ : syracuseStep 1437421 = 539033) (by norm_num)
theorem B1699589 : Blo 1132632 1699589 := bbase (se 4 (by rfl) ⟨159336, by rfl⟩ : syracuseStep 1699589 = 318673) (by norm_num)
theorem B1699613 : Blo 1132632 1699613 := bbase (se 3 (by rfl) ⟨318677, by rfl⟩ : syracuseStep 1699613 = 637355) (by norm_num)
theorem B2551589 : Blo 1132632 2551589 := bbase (se 4 (by rfl) ⟨239211, by rfl⟩ : syracuseStep 2551589 = 478423) (by norm_num)
theorem B1699637 : Blo 1132632 1699637 := bbase (se 5 (by rfl) ⟨79670, by rfl⟩ : syracuseStep 1699637 = 159341) (by norm_num)
theorem B1699661 : Blo 1132632 1699661 := bbase (se 3 (by rfl) ⟨318686, by rfl⟩ : syracuseStep 1699661 = 637373) (by norm_num)
theorem B1437517 : Blo 1132632 1437517 := bbase (se 3 (by rfl) ⟨269534, by rfl⟩ : syracuseStep 1437517 = 539069) (by norm_num)
theorem B1699685 : Blo 1132632 1699685 := bbase (se 4 (by rfl) ⟨159345, by rfl⟩ : syracuseStep 1699685 = 318691) (by norm_num)
theorem B2551661 : Blo 1132632 2551661 := bbase (se 3 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 2551661 = 956873) (by norm_num)
theorem B1699709 : Blo 1132632 1699709 := bbase (se 3 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 1699709 = 637391) (by norm_num)
theorem B1699733 : Blo 1132632 1699733 := bbase (se 6 (by rfl) ⟨39837, by rfl⟩ : syracuseStep 1699733 = 79675) (by norm_num)
theorem B1699757 : Blo 1132632 1699757 := bbase (se 3 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 1699757 = 637409) (by norm_num)
theorem B2551733 : Blo 1132632 2551733 := bbase (se 5 (by rfl) ⟨119612, by rfl⟩ : syracuseStep 2551733 = 239225) (by norm_num)
theorem B1699781 : Blo 1132632 1699781 := bbase (se 4 (by rfl) ⟨159354, by rfl⟩ : syracuseStep 1699781 = 318709) (by norm_num)
theorem B1699805 : Blo 1132632 1699805 := bbase (se 3 (by rfl) ⟨318713, by rfl⟩ : syracuseStep 1699805 = 637427) (by norm_num)
theorem B3829733 : Blo 1132632 3829733 := bbase (se 4 (by rfl) ⟨359037, by rfl⟩ : syracuseStep 3829733 = 718075) (by norm_num)
theorem B1699829 : Blo 1132632 1699829 := bbase (se 5 (by rfl) ⟨79679, by rfl⟩ : syracuseStep 1699829 = 159359) (by norm_num)
theorem B1437689 : Blo 1132632 1437689 := bbase (se 2 (by rfl) ⟨539133, by rfl⟩ : syracuseStep 1437689 = 1078267) (by norm_num)
theorem B2551805 : Blo 1132632 2551805 := bbase (se 3 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 2551805 = 956927) (by norm_num)
theorem B1699853 : Blo 1132632 1699853 := bbase (se 3 (by rfl) ⟨318722, by rfl⟩ : syracuseStep 1699853 = 637445) (by norm_num)
theorem B14544917 : Blo 1132632 14544917 := bbase (se 6 (by rfl) ⟨340896, by rfl⟩ : syracuseStep 14544917 = 681793) (by norm_num)
theorem B1699877 : Blo 1132632 1699877 := bbase (se 4 (by rfl) ⟨159363, by rfl⟩ : syracuseStep 1699877 = 318727) (by norm_num)
theorem B1437745 : Blo 1132632 1437745 := bbase (se 2 (by rfl) ⟨539154, by rfl⟩ : syracuseStep 1437745 = 1078309) (by norm_num)
theorem B1699901 : Blo 1132632 1699901 := bbase (se 3 (by rfl) ⟨318731, by rfl⟩ : syracuseStep 1699901 = 637463) (by norm_num)
theorem B2551877 : Blo 1132632 2551877 := bbase (se 4 (by rfl) ⟨239238, by rfl⟩ : syracuseStep 2551877 = 478477) (by norm_num)
theorem B6451285 : Blo 1132632 6451285 := bbase (se 8 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 6451285 = 75601) (by norm_num)
theorem B1699925 : Blo 1132632 1699925 := bbase (se 8 (by rfl) ⟨9960, by rfl⟩ : syracuseStep 1699925 = 19921) (by norm_num)
theorem B1699949 : Blo 1132632 1699949 := bbase (se 3 (by rfl) ⟨318740, by rfl⟩ : syracuseStep 1699949 = 637481) (by norm_num)
theorem B1699973 : Blo 1132632 1699973 := bbase (se 4 (by rfl) ⟨159372, by rfl⟩ : syracuseStep 1699973 = 318745) (by norm_num)
theorem B2551949 : Blo 1132632 2551949 := bbase (se 3 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 2551949 = 956981) (by norm_num)
theorem B1437841 : Blo 1132632 1437841 := bbase (se 2 (by rfl) ⟨539190, by rfl⟩ : syracuseStep 1437841 = 1078381) (by norm_num)
theorem B1699997 : Blo 1132632 1699997 := bbase (se 3 (by rfl) ⟨318749, by rfl⟩ : syracuseStep 1699997 = 637499) (by norm_num)
theorem B1700021 : Blo 1132632 1700021 := bbase (se 5 (by rfl) ⟨79688, by rfl⟩ : syracuseStep 1700021 = 159377) (by norm_num)
theorem B1700045 : Blo 1132632 1700045 := bbase (se 3 (by rfl) ⟨318758, by rfl⟩ : syracuseStep 1700045 = 637517) (by norm_num)
theorem B2420941 : Blo 1132632 2420941 := bbase (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) (by norm_num)
theorem B2552021 : Blo 1132632 2552021 := bbase (se 7 (by rfl) ⟨29906, by rfl⟩ : syracuseStep 2552021 = 59813) (by norm_num)
theorem B1700069 : Blo 1132632 1700069 := bbase (se 4 (by rfl) ⟨159381, by rfl⟩ : syracuseStep 1700069 = 318763) (by norm_num)
theorem B1700093 : Blo 1132632 1700093 := bbase (se 3 (by rfl) ⟨318767, by rfl⟩ : syracuseStep 1700093 = 637535) (by norm_num)
theorem B1700117 : Blo 1132632 1700117 := bbase (se 6 (by rfl) ⟨39846, by rfl⟩ : syracuseStep 1700117 = 79693) (by norm_num)
theorem B4845845 : Blo 1132632 4845845 := bbase (se 6 (by rfl) ⟨113574, by rfl⟩ : syracuseStep 4845845 = 227149) (by norm_num)
theorem B2552093 : Blo 1132632 2552093 := bbase (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) (by norm_num)
theorem B1700141 : Blo 1132632 1700141 := bbase (se 3 (by rfl) ⟨318776, by rfl⟩ : syracuseStep 1700141 = 637553) (by norm_num)
theorem B1438013 : Blo 1132632 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1700165 : Blo 1132632 1700165 := bbase (se 4 (by rfl) ⟨159390, by rfl⟩ : syracuseStep 1700165 = 318781) (by norm_num)
theorem B2584909 : Blo 1132632 2584909 := bbase (se 3 (by rfl) ⟨484670, by rfl⟩ : syracuseStep 2584909 = 969341) (by norm_num)
theorem B1700189 : Blo 1132632 1700189 := bbase (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) (by norm_num)
theorem B2552165 : Blo 1132632 2552165 := bbase (se 4 (by rfl) ⟨239265, by rfl⟩ : syracuseStep 2552165 = 478531) (by norm_num)
theorem B1700213 : Blo 1132632 1700213 := bbase (se 5 (by rfl) ⟨79697, by rfl⟩ : syracuseStep 1700213 = 159395) (by norm_num)
theorem B1438069 : Blo 1132632 1438069 := bbase (se 5 (by rfl) ⟨67409, by rfl⟩ : syracuseStep 1438069 = 134819) (by norm_num)
theorem B1274233 : Blo 1132632 1274233 := bbase (se 2 (by rfl) ⟨477837, by rfl⟩ : syracuseStep 1274233 = 955675) (by norm_num)
theorem B1700237 : Blo 1132632 1700237 := bbase (se 3 (by rfl) ⟨318794, by rfl⟩ : syracuseStep 1700237 = 637589) (by norm_num)
theorem B3830165 : Blo 1132632 3830165 := bbase (se 6 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 3830165 = 179539) (by norm_num)
theorem B1274269 : Blo 1132632 1274269 := bbase (se 3 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 1274269 = 477851) (by norm_num)
theorem B1700261 : Blo 1132632 1700261 := bbase (se 4 (by rfl) ⟨159399, by rfl⟩ : syracuseStep 1700261 = 318799) (by norm_num)
theorem B2552237 : Blo 1132632 2552237 := bbase (se 3 (by rfl) ⟨478544, by rfl⟩ : syracuseStep 2552237 = 957089) (by norm_num)
theorem B1700285 : Blo 1132632 1700285 := bbase (se 3 (by rfl) ⟨318803, by rfl⟩ : syracuseStep 1700285 = 637607) (by norm_num)
theorem B1274305 : Blo 1132632 1274305 := bbase (se 2 (by rfl) ⟨477864, by rfl⟩ : syracuseStep 1274305 = 955729) (by norm_num)
theorem B20672981 : Blo 1132632 20672981 := bbase (se 7 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 20672981 = 484523) (by norm_num)
theorem B1700309 : Blo 1132632 1700309 := bbase (se 7 (by rfl) ⟨19925, by rfl⟩ : syracuseStep 1700309 = 39851) (by norm_num)
theorem B4092373 : Blo 1132632 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B1438165 : Blo 1132632 1438165 := bbase (se 7 (by rfl) ⟨16853, by rfl⟩ : syracuseStep 1438165 = 33707) (by norm_num)
theorem B1274341 : Blo 1132632 1274341 := bbase (se 4 (by rfl) ⟨119469, by rfl⟩ : syracuseStep 1274341 = 238939) (by norm_num)
theorem B1700333 : Blo 1132632 1700333 := bbase (se 3 (by rfl) ⟨318812, by rfl⟩ : syracuseStep 1700333 = 637625) (by norm_num)
theorem B2552309 : Blo 1132632 2552309 := bbase (se 5 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 2552309 = 239279) (by norm_num)
theorem B1700357 : Blo 1132632 1700357 := bbase (se 4 (by rfl) ⟨159408, by rfl⟩ : syracuseStep 1700357 = 318817) (by norm_num)
theorem B1274377 : Blo 1132632 1274377 := bbase (se 2 (by rfl) ⟨477891, by rfl⟩ : syracuseStep 1274377 = 955783) (by norm_num)
theorem B1700381 : Blo 1132632 1700381 := bbase (se 3 (by rfl) ⟨318821, by rfl⟩ : syracuseStep 1700381 = 637643) (by norm_num)
theorem B1274413 : Blo 1132632 1274413 := bbase (se 3 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 1274413 = 477905) (by norm_num)
theorem B1700405 : Blo 1132632 1700405 := bbase (se 5 (by rfl) ⟨79706, by rfl⟩ : syracuseStep 1700405 = 159413) (by norm_num)
theorem B2552381 : Blo 1132632 2552381 := bbase (se 3 (by rfl) ⟨478571, by rfl⟩ : syracuseStep 2552381 = 957143) (by norm_num)
theorem B1700429 : Blo 1132632 1700429 := bbase (se 3 (by rfl) ⟨318830, by rfl⟩ : syracuseStep 1700429 = 637661) (by norm_num)
theorem B1274449 : Blo 1132632 1274449 := bbase (se 2 (by rfl) ⟨477918, by rfl⟩ : syracuseStep 1274449 = 955837) (by norm_num)
theorem B1700453 : Blo 1132632 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B1274485 : Blo 1132632 1274485 := bbase (se 5 (by rfl) ⟨59741, by rfl⟩ : syracuseStep 1274485 = 119483) (by norm_num)
theorem B9695861 : Blo 1132632 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B1700477 : Blo 1132632 1700477 := bbase (se 3 (by rfl) ⟨318839, by rfl⟩ : syracuseStep 1700477 = 637679) (by norm_num)
theorem B1438337 : Blo 1132632 1438337 := bbase (se 2 (by rfl) ⟨539376, by rfl⟩ : syracuseStep 1438337 = 1078753) (by norm_num)
theorem B2552453 : Blo 1132632 2552453 := bbase (se 4 (by rfl) ⟨239292, by rfl⟩ : syracuseStep 2552453 = 478585) (by norm_num)
theorem B1700501 : Blo 1132632 1700501 := bbase (se 6 (by rfl) ⟨39855, by rfl⟩ : syracuseStep 1700501 = 79711) (by norm_num)
theorem B1274521 : Blo 1132632 1274521 := bbase (se 2 (by rfl) ⟨477945, by rfl⟩ : syracuseStep 1274521 = 955891) (by norm_num)
theorem B1700525 : Blo 1132632 1700525 := bbase (se 3 (by rfl) ⟨318848, by rfl⟩ : syracuseStep 1700525 = 637697) (by norm_num)
theorem B1438393 : Blo 1132632 1438393 := bbase (se 2 (by rfl) ⟨539397, by rfl⟩ : syracuseStep 1438393 = 1078795) (by norm_num)
theorem B1274557 : Blo 1132632 1274557 := bbase (se 3 (by rfl) ⟨238979, by rfl⟩ : syracuseStep 1274557 = 477959) (by norm_num)
theorem B1700549 : Blo 1132632 1700549 := bbase (se 4 (by rfl) ⟨159426, by rfl⟩ : syracuseStep 1700549 = 318853) (by norm_num)
theorem B2552525 : Blo 1132632 2552525 := bbase (se 3 (by rfl) ⟨478598, by rfl⟩ : syracuseStep 2552525 = 957197) (by norm_num)
theorem B1700573 : Blo 1132632 1700573 := bbase (se 3 (by rfl) ⟨318857, by rfl⟩ : syracuseStep 1700573 = 637715) (by norm_num)
theorem B1274593 : Blo 1132632 1274593 := bbase (se 2 (by rfl) ⟨477972, by rfl⟩ : syracuseStep 1274593 = 955945) (by norm_num)
theorem B1700597 : Blo 1132632 1700597 := bbase (se 5 (by rfl) ⟨79715, by rfl⟩ : syracuseStep 1700597 = 159431) (by norm_num)
theorem B1274629 : Blo 1132632 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B1700621 : Blo 1132632 1700621 := bbase (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) (by norm_num)
theorem B2552597 : Blo 1132632 2552597 := bbase (se 6 (by rfl) ⟨59826, by rfl⟩ : syracuseStep 2552597 = 119653) (by norm_num)
theorem B1438489 : Blo 1132632 1438489 := bbase (se 2 (by rfl) ⟨539433, by rfl⟩ : syracuseStep 1438489 = 1078867) (by norm_num)
theorem B1700645 : Blo 1132632 1700645 := bbase (se 4 (by rfl) ⟨159435, by rfl⟩ : syracuseStep 1700645 = 318871) (by norm_num)
theorem B1274665 : Blo 1132632 1274665 := bbase (se 2 (by rfl) ⟨477999, by rfl⟩ : syracuseStep 1274665 = 955999) (by norm_num)
theorem B1700669 : Blo 1132632 1700669 := bbase (se 3 (by rfl) ⟨318875, by rfl⟩ : syracuseStep 1700669 = 637751) (by norm_num)
theorem B3830597 : Blo 1132632 3830597 := bbase (se 4 (by rfl) ⟨359118, by rfl⟩ : syracuseStep 3830597 = 718237) (by norm_num)
theorem B1274701 : Blo 1132632 1274701 := bbase (se 3 (by rfl) ⟨239006, by rfl⟩ : syracuseStep 1274701 = 478013) (by norm_num)
theorem B1700693 : Blo 1132632 1700693 := bbase (se 9 (by rfl) ⟨4982, by rfl⟩ : syracuseStep 1700693 = 9965) (by norm_num)
theorem B2552669 : Blo 1132632 2552669 := bbase (se 3 (by rfl) ⟨478625, by rfl⟩ : syracuseStep 2552669 = 957251) (by norm_num)
theorem B1700717 : Blo 1132632 1700717 := bbase (se 3 (by rfl) ⟨318884, by rfl⟩ : syracuseStep 1700717 = 637769) (by norm_num)
theorem B1274737 : Blo 1132632 1274737 := bbase (se 2 (by rfl) ⟨478026, by rfl⟩ : syracuseStep 1274737 = 956053) (by norm_num)
theorem B1700741 : Blo 1132632 1700741 := bbase (se 4 (by rfl) ⟨159444, by rfl⟩ : syracuseStep 1700741 = 318889) (by norm_num)
theorem B1274773 : Blo 1132632 1274773 := bbase (se 6 (by rfl) ⟨29877, by rfl⟩ : syracuseStep 1274773 = 59755) (by norm_num)
theorem B1700765 : Blo 1132632 1700765 := bbase (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) (by norm_num)
theorem B2552741 : Blo 1132632 2552741 := bbase (se 4 (by rfl) ⟨239319, by rfl⟩ : syracuseStep 2552741 = 478639) (by norm_num)
theorem B1700789 : Blo 1132632 1700789 := bbase (se 5 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 1700789 = 159449) (by norm_num)
theorem B1274809 : Blo 1132632 1274809 := bbase (se 2 (by rfl) ⟨478053, by rfl⟩ : syracuseStep 1274809 = 956107) (by norm_num)
theorem B1700813 : Blo 1132632 1700813 := bbase (se 3 (by rfl) ⟨318902, by rfl⟩ : syracuseStep 1700813 = 637805) (by norm_num)
theorem B1274845 : Blo 1132632 1274845 := bbase (se 3 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 1274845 = 478067) (by norm_num)
theorem B1700837 : Blo 1132632 1700837 := bbase (se 4 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 1700837 = 318907) (by norm_num)
theorem B2552813 : Blo 1132632 2552813 := bbase (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) (by norm_num)
theorem B9204725 : Blo 1132632 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B1700861 : Blo 1132632 1700861 := bbase (se 3 (by rfl) ⟨318911, by rfl⟩ : syracuseStep 1700861 = 637823) (by norm_num)
theorem B1274881 : Blo 1132632 1274881 := bbase (se 2 (by rfl) ⟨478080, by rfl⟩ : syracuseStep 1274881 = 956161) (by norm_num)
theorem B1700885 : Blo 1132632 1700885 := bbase (se 6 (by rfl) ⟨39864, by rfl⟩ : syracuseStep 1700885 = 79729) (by norm_num)
theorem B1274917 : Blo 1132632 1274917 := bbase (se 4 (by rfl) ⟨119523, by rfl⟩ : syracuseStep 1274917 = 239047) (by norm_num)
theorem B1700909 : Blo 1132632 1700909 := bbase (se 3 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 1700909 = 637841) (by norm_num)
theorem B2552885 : Blo 1132632 2552885 := bbase (se 5 (by rfl) ⟨119666, by rfl⟩ : syracuseStep 2552885 = 239333) (by norm_num)
theorem B2421829 : Blo 1132632 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B1700933 : Blo 1132632 1700933 := bbase (se 4 (by rfl) ⟨159462, by rfl⟩ : syracuseStep 1700933 = 318925) (by norm_num)
theorem B1274953 : Blo 1132632 1274953 := bbase (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) (by norm_num)
theorem B1700957 : Blo 1132632 1700957 := bbase (se 3 (by rfl) ⟨318929, by rfl⟩ : syracuseStep 1700957 = 637859) (by norm_num)
theorem B1274989 : Blo 1132632 1274989 := bbase (se 3 (by rfl) ⟨239060, by rfl⟩ : syracuseStep 1274989 = 478121) (by norm_num)
theorem B1700981 : Blo 1132632 1700981 := bbase (se 5 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 1700981 = 159467) (by norm_num)
theorem B2552957 : Blo 1132632 2552957 := bbase (se 3 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 2552957 = 957359) (by norm_num)
theorem B1701005 : Blo 1132632 1701005 := bbase (se 3 (by rfl) ⟨318938, by rfl⟩ : syracuseStep 1701005 = 637877) (by norm_num)
theorem B1275025 : Blo 1132632 1275025 := bbase (se 2 (by rfl) ⟨478134, by rfl⟩ : syracuseStep 1275025 = 956269) (by norm_num)
theorem B1701029 : Blo 1132632 1701029 := bbase (se 4 (by rfl) ⟨159471, by rfl⟩ : syracuseStep 1701029 = 318943) (by norm_num)
theorem B1275061 : Blo 1132632 1275061 := bbase (se 5 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 1275061 = 119537) (by norm_num)
theorem B1701053 : Blo 1132632 1701053 := bbase (se 3 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 1701053 = 637895) (by norm_num)
theorem B2553029 : Blo 1132632 2553029 := bbase (se 4 (by rfl) ⟨239346, by rfl⟩ : syracuseStep 2553029 = 478693) (by norm_num)
theorem B1701077 : Blo 1132632 1701077 := bbase (se 7 (by rfl) ⟨19934, by rfl⟩ : syracuseStep 1701077 = 39869) (by norm_num)
theorem B1275097 : Blo 1132632 1275097 := bbase (se 2 (by rfl) ⟨478161, by rfl⟩ : syracuseStep 1275097 = 956323) (by norm_num)
theorem B1701101 : Blo 1132632 1701101 := bbase (se 3 (by rfl) ⟨318956, by rfl⟩ : syracuseStep 1701101 = 637913) (by norm_num)
theorem B4846837 : Blo 1132632 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B3831029 : Blo 1132632 3831029 := bbase (se 5 (by rfl) ⟨179579, by rfl⟩ : syracuseStep 3831029 = 359159) (by norm_num)
theorem B1275133 : Blo 1132632 1275133 := bbase (se 3 (by rfl) ⟨239087, by rfl⟩ : syracuseStep 1275133 = 478175) (by norm_num)
theorem B1701125 : Blo 1132632 1701125 := bbase (se 4 (by rfl) ⟨159480, by rfl⟩ : syracuseStep 1701125 = 318961) (by norm_num)
theorem B2553101 : Blo 1132632 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B1701149 : Blo 1132632 1701149 := bbase (se 3 (by rfl) ⟨318965, by rfl⟩ : syracuseStep 1701149 = 637931) (by norm_num)
theorem B1275169 : Blo 1132632 1275169 := bbase (se 2 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 1275169 = 956377) (by norm_num)
theorem B1701173 : Blo 1132632 1701173 := bbase (se 5 (by rfl) ⟨79742, by rfl⟩ : syracuseStep 1701173 = 159485) (by norm_num)
theorem B1275205 : Blo 1132632 1275205 := bbase (se 4 (by rfl) ⟨119550, by rfl⟩ : syracuseStep 1275205 = 239101) (by norm_num)
theorem B1701197 : Blo 1132632 1701197 := bbase (se 3 (by rfl) ⟨318974, by rfl⟩ : syracuseStep 1701197 = 637949) (by norm_num)
theorem B2553173 : Blo 1132632 2553173 := bbase (se 13 (by rfl) ⟨467, by rfl⟩ : syracuseStep 2553173 = 935) (by norm_num)
theorem B1701221 : Blo 1132632 1701221 := bbase (se 4 (by rfl) ⟨159489, by rfl⟩ : syracuseStep 1701221 = 318979) (by norm_num)
theorem B1275241 : Blo 1132632 1275241 := bbase (se 2 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 1275241 = 956431) (by norm_num)
theorem B1701245 : Blo 1132632 1701245 := bbase (se 3 (by rfl) ⟨318983, by rfl⟩ : syracuseStep 1701245 = 637967) (by norm_num)
theorem B1275277 : Blo 1132632 1275277 := bbase (se 3 (by rfl) ⟨239114, by rfl⟩ : syracuseStep 1275277 = 478229) (by norm_num)
theorem B1701269 : Blo 1132632 1701269 := bbase (se 6 (by rfl) ⟨39873, by rfl⟩ : syracuseStep 1701269 = 79747) (by norm_num)
theorem B2553245 : Blo 1132632 2553245 := bbase (se 3 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 2553245 = 957467) (by norm_num)
theorem B1701293 : Blo 1132632 1701293 := bbase (se 3 (by rfl) ⟨318992, by rfl⟩ : syracuseStep 1701293 = 637985) (by norm_num)
theorem B1275313 : Blo 1132632 1275313 := bbase (se 2 (by rfl) ⟨478242, by rfl⟩ : syracuseStep 1275313 = 956485) (by norm_num)
theorem B1701317 : Blo 1132632 1701317 := bbase (se 4 (by rfl) ⟨159498, by rfl⟩ : syracuseStep 1701317 = 318997) (by norm_num)
theorem B1275349 : Blo 1132632 1275349 := bbase (se 7 (by rfl) ⟨14945, by rfl⟩ : syracuseStep 1275349 = 29891) (by norm_num)
theorem B1209821 : Blo 1132632 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B2586077 : Blo 1132632 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B1701341 : Blo 1132632 1701341 := bbase (se 3 (by rfl) ⟨319001, by rfl⟩ : syracuseStep 1701341 = 638003) (by norm_num)
theorem B2553317 : Blo 1132632 2553317 := bbase (se 4 (by rfl) ⟨239373, by rfl⟩ : syracuseStep 2553317 = 478747) (by norm_num)
theorem B1701365 : Blo 1132632 1701365 := bbase (se 5 (by rfl) ⟨79751, by rfl⟩ : syracuseStep 1701365 = 159503) (by norm_num)
theorem B1275385 : Blo 1132632 1275385 := bbase (se 2 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 1275385 = 956539) (by norm_num)
theorem B1701389 : Blo 1132632 1701389 := bbase (se 3 (by rfl) ⟨319010, by rfl⟩ : syracuseStep 1701389 = 638021) (by norm_num)
theorem B1275421 : Blo 1132632 1275421 := bbase (se 3 (by rfl) ⟨239141, by rfl⟩ : syracuseStep 1275421 = 478283) (by norm_num)
theorem B1701413 : Blo 1132632 1701413 := bbase (se 4 (by rfl) ⟨159507, by rfl⟩ : syracuseStep 1701413 = 319015) (by norm_num)
theorem B2553389 : Blo 1132632 2553389 := bbase (se 3 (by rfl) ⟨478760, by rfl⟩ : syracuseStep 2553389 = 957521) (by norm_num)
theorem B2422325 : Blo 1132632 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B1701437 : Blo 1132632 1701437 := bbase (se 3 (by rfl) ⟨319019, by rfl⟩ : syracuseStep 1701437 = 638039) (by norm_num)
theorem B1275457 : Blo 1132632 1275457 := bbase (se 2 (by rfl) ⟨478296, by rfl⟩ : syracuseStep 1275457 = 956593) (by norm_num)
theorem B1701461 : Blo 1132632 1701461 := bbase (se 8 (by rfl) ⟨9969, by rfl⟩ : syracuseStep 1701461 = 19939) (by norm_num)
theorem B1275493 : Blo 1132632 1275493 := bbase (se 4 (by rfl) ⟨119577, by rfl⟩ : syracuseStep 1275493 = 239155) (by norm_num)
theorem B1701485 : Blo 1132632 1701485 := bbase (se 3 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 1701485 = 638057) (by norm_num)
theorem B2553461 : Blo 1132632 2553461 := bbase (se 5 (by rfl) ⟨119693, by rfl⟩ : syracuseStep 2553461 = 239387) (by norm_num)
theorem B1701509 : Blo 1132632 1701509 := bbase (se 4 (by rfl) ⟨159516, by rfl⟩ : syracuseStep 1701509 = 319033) (by norm_num)
theorem B1275529 : Blo 1132632 1275529 := bbase (se 2 (by rfl) ⟨478323, by rfl⟩ : syracuseStep 1275529 = 956647) (by norm_num)
theorem B1701533 : Blo 1132632 1701533 := bbase (se 3 (by rfl) ⟨319037, by rfl⟩ : syracuseStep 1701533 = 638075) (by norm_num)
theorem B3831461 : Blo 1132632 3831461 := bbase (se 4 (by rfl) ⟨359199, by rfl⟩ : syracuseStep 3831461 = 718399) (by norm_num)
theorem B1275565 : Blo 1132632 1275565 := bbase (se 3 (by rfl) ⟨239168, by rfl⟩ : syracuseStep 1275565 = 478337) (by norm_num)
theorem B1701557 : Blo 1132632 1701557 := bbase (se 5 (by rfl) ⟨79760, by rfl⟩ : syracuseStep 1701557 = 159521) (by norm_num)
theorem B2553533 : Blo 1132632 2553533 := bbase (se 3 (by rfl) ⟨478787, by rfl⟩ : syracuseStep 2553533 = 957575) (by norm_num)
theorem B3634885 : Blo 1132632 3634885 := bbase (se 4 (by rfl) ⟨340770, by rfl⟩ : syracuseStep 3634885 = 681541) (by norm_num)
theorem B1701581 : Blo 1132632 1701581 := bbase (se 3 (by rfl) ⟨319046, by rfl⟩ : syracuseStep 1701581 = 638093) (by norm_num)
theorem B1275601 : Blo 1132632 1275601 := bbase (se 2 (by rfl) ⟨478350, by rfl⟩ : syracuseStep 1275601 = 956701) (by norm_num)
theorem B1210069 : Blo 1132632 1210069 := bbase (se 7 (by rfl) ⟨14180, by rfl⟩ : syracuseStep 1210069 = 28361) (by norm_num)
theorem B1701605 : Blo 1132632 1701605 := bbase (se 4 (by rfl) ⟨159525, by rfl⟩ : syracuseStep 1701605 = 319051) (by norm_num)
theorem B1275637 : Blo 1132632 1275637 := bbase (se 5 (by rfl) ⟨59795, by rfl⟩ : syracuseStep 1275637 = 119591) (by norm_num)
theorem B1701629 : Blo 1132632 1701629 := bbase (se 3 (by rfl) ⟨319055, by rfl⟩ : syracuseStep 1701629 = 638111) (by norm_num)
theorem B3634949 : Blo 1132632 3634949 := bbase (se 4 (by rfl) ⟨340776, by rfl⟩ : syracuseStep 3634949 = 681553) (by norm_num)
theorem B2553605 : Blo 1132632 2553605 := bbase (se 4 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 2553605 = 478801) (by norm_num)
theorem B1701653 : Blo 1132632 1701653 := bbase (se 6 (by rfl) ⟨39882, by rfl⟩ : syracuseStep 1701653 = 79765) (by norm_num)
theorem B1275673 : Blo 1132632 1275673 := bbase (se 2 (by rfl) ⟨478377, by rfl⟩ : syracuseStep 1275673 = 956755) (by norm_num)
theorem B1701677 : Blo 1132632 1701677 := bbase (se 3 (by rfl) ⟨319064, by rfl⟩ : syracuseStep 1701677 = 638129) (by norm_num)
theorem B1275709 : Blo 1132632 1275709 := bbase (se 3 (by rfl) ⟨239195, by rfl⟩ : syracuseStep 1275709 = 478391) (by norm_num)
theorem B1701701 : Blo 1132632 1701701 := bbase (se 4 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 1701701 = 319069) (by norm_num)
theorem B2553677 : Blo 1132632 2553677 := bbase (se 3 (by rfl) ⟨478814, by rfl⟩ : syracuseStep 2553677 = 957629) (by norm_num)
theorem B1701725 : Blo 1132632 1701725 := bbase (se 3 (by rfl) ⟨319073, by rfl⟩ : syracuseStep 1701725 = 638147) (by norm_num)
theorem B1275745 : Blo 1132632 1275745 := bbase (se 2 (by rfl) ⟨478404, by rfl⟩ : syracuseStep 1275745 = 956809) (by norm_num)
theorem B1701749 : Blo 1132632 1701749 := bbase (se 5 (by rfl) ⟨79769, by rfl⟩ : syracuseStep 1701749 = 159539) (by norm_num)
theorem B1275781 : Blo 1132632 1275781 := bbase (se 4 (by rfl) ⟨119604, by rfl⟩ : syracuseStep 1275781 = 239209) (by norm_num)
theorem B1701773 : Blo 1132632 1701773 := bbase (se 3 (by rfl) ⟨319082, by rfl⟩ : syracuseStep 1701773 = 638165) (by norm_num)
theorem B2553749 : Blo 1132632 2553749 := bbase (se 6 (by rfl) ⟨59853, by rfl⟩ : syracuseStep 2553749 = 119707) (by norm_num)
theorem B1701797 : Blo 1132632 1701797 := bbase (se 4 (by rfl) ⟨159543, by rfl⟩ : syracuseStep 1701797 = 319087) (by norm_num)
theorem B1275817 : Blo 1132632 1275817 := bbase (se 2 (by rfl) ⟨478431, by rfl⟩ : syracuseStep 1275817 = 956863) (by norm_num)
theorem B1701821 : Blo 1132632 1701821 := bbase (se 3 (by rfl) ⟨319091, by rfl⟩ : syracuseStep 1701821 = 638183) (by norm_num)
theorem B1275853 : Blo 1132632 1275853 := bbase (se 3 (by rfl) ⟨239222, by rfl⟩ : syracuseStep 1275853 = 478445) (by norm_num)
theorem B1701845 : Blo 1132632 1701845 := bbase (se 7 (by rfl) ⟨19943, by rfl⟩ : syracuseStep 1701845 = 39887) (by norm_num)
theorem B2553821 : Blo 1132632 2553821 := bbase (se 3 (by rfl) ⟨478841, by rfl⟩ : syracuseStep 2553821 = 957683) (by norm_num)
theorem B1701869 : Blo 1132632 1701869 := bbase (se 3 (by rfl) ⟨319100, by rfl⟩ : syracuseStep 1701869 = 638201) (by norm_num)
theorem B1275889 : Blo 1132632 1275889 := bbase (se 2 (by rfl) ⟨478458, by rfl⟩ : syracuseStep 1275889 = 956917) (by norm_num)
theorem B1701893 : Blo 1132632 1701893 := bbase (se 4 (by rfl) ⟨159552, by rfl⟩ : syracuseStep 1701893 = 319105) (by norm_num)
theorem B6453269 : Blo 1132632 6453269 := bbase (se 6 (by rfl) ⟨151248, by rfl⟩ : syracuseStep 6453269 = 302497) (by norm_num)
theorem B1275925 : Blo 1132632 1275925 := bbase (se 6 (by rfl) ⟨29904, by rfl⟩ : syracuseStep 1275925 = 59809) (by norm_num)
theorem B1701917 : Blo 1132632 1701917 := bbase (se 3 (by rfl) ⟨319109, by rfl⟩ : syracuseStep 1701917 = 638219) (by norm_num)
theorem B2553893 : Blo 1132632 2553893 := bbase (se 4 (by rfl) ⟨239427, by rfl⟩ : syracuseStep 2553893 = 478855) (by norm_num)
theorem B1701941 : Blo 1132632 1701941 := bbase (se 5 (by rfl) ⟨79778, by rfl⟩ : syracuseStep 1701941 = 159557) (by norm_num)
theorem B1275961 : Blo 1132632 1275961 := bbase (se 2 (by rfl) ⟨478485, by rfl⟩ : syracuseStep 1275961 = 956971) (by norm_num)
theorem B1701965 : Blo 1132632 1701965 := bbase (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) (by norm_num)
theorem B3831893 : Blo 1132632 3831893 := bbase (se 8 (by rfl) ⟨22452, by rfl⟩ : syracuseStep 3831893 = 44905) (by norm_num)
theorem B1275997 : Blo 1132632 1275997 := bbase (se 3 (by rfl) ⟨239249, by rfl⟩ : syracuseStep 1275997 = 478499) (by norm_num)
theorem B1701989 : Blo 1132632 1701989 := bbase (se 4 (by rfl) ⟨159561, by rfl⟩ : syracuseStep 1701989 = 319123) (by norm_num)
theorem B2553965 : Blo 1132632 2553965 := bbase (se 3 (by rfl) ⟨478868, by rfl⟩ : syracuseStep 2553965 = 957737) (by norm_num)
theorem B1702013 : Blo 1132632 1702013 := bbase (se 3 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 1702013 = 638255) (by norm_num)
theorem B1276033 : Blo 1132632 1276033 := bbase (se 2 (by rfl) ⟨478512, by rfl⟩ : syracuseStep 1276033 = 957025) (by norm_num)
theorem B1210501 : Blo 1132632 1210501 := bbase (se 4 (by rfl) ⟨113484, by rfl⟩ : syracuseStep 1210501 = 226969) (by norm_num)
theorem B1702037 : Blo 1132632 1702037 := bbase (se 6 (by rfl) ⟨39891, by rfl⟩ : syracuseStep 1702037 = 79783) (by norm_num)
theorem B1276069 : Blo 1132632 1276069 := bbase (se 4 (by rfl) ⟨119631, by rfl⟩ : syracuseStep 1276069 = 239263) (by norm_num)
theorem B1702061 : Blo 1132632 1702061 := bbase (se 3 (by rfl) ⟨319136, by rfl⟩ : syracuseStep 1702061 = 638273) (by norm_num)
theorem B2554037 : Blo 1132632 2554037 := bbase (se 5 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 2554037 = 239441) (by norm_num)
theorem B1702085 : Blo 1132632 1702085 := bbase (se 4 (by rfl) ⟨159570, by rfl⟩ : syracuseStep 1702085 = 319141) (by norm_num)
theorem B1276105 : Blo 1132632 1276105 := bbase (se 2 (by rfl) ⟨478539, by rfl⟩ : syracuseStep 1276105 = 957079) (by norm_num)
theorem B1210573 : Blo 1132632 1210573 := bbase (se 3 (by rfl) ⟨226982, by rfl⟩ : syracuseStep 1210573 = 453965) (by norm_num)
theorem B1702109 : Blo 1132632 1702109 := bbase (se 3 (by rfl) ⟨319145, by rfl⟩ : syracuseStep 1702109 = 638291) (by norm_num)
theorem B1276141 : Blo 1132632 1276141 := bbase (se 3 (by rfl) ⟨239276, by rfl⟩ : syracuseStep 1276141 = 478553) (by norm_num)
theorem B1702133 : Blo 1132632 1702133 := bbase (se 5 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 1702133 = 159575) (by norm_num)
theorem B2554109 : Blo 1132632 2554109 := bbase (se 3 (by rfl) ⟨478895, by rfl⟩ : syracuseStep 2554109 = 957791) (by norm_num)
theorem B1702157 : Blo 1132632 1702157 := bbase (se 3 (by rfl) ⟨319154, by rfl⟩ : syracuseStep 1702157 = 638309) (by norm_num)
theorem B1276177 : Blo 1132632 1276177 := bbase (se 2 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 1276177 = 957133) (by norm_num)
theorem B1702181 : Blo 1132632 1702181 := bbase (se 4 (by rfl) ⟨159579, by rfl⟩ : syracuseStep 1702181 = 319159) (by norm_num)
theorem B3733813 : Blo 1132632 3733813 := bbase (se 5 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 3733813 = 350045) (by norm_num)
theorem B1276213 : Blo 1132632 1276213 := bbase (se 5 (by rfl) ⟨59822, by rfl⟩ : syracuseStep 1276213 = 119645) (by norm_num)
theorem B1702205 : Blo 1132632 1702205 := bbase (se 3 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 1702205 = 638327) (by norm_num)
theorem B2554181 : Blo 1132632 2554181 := bbase (se 4 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 2554181 = 478909) (by norm_num)
theorem B1243477 : Blo 1132632 1243477 := bbase (se 10 (by rfl) ⟨1821, by rfl⟩ : syracuseStep 1243477 = 3643) (by norm_num)
theorem B1702229 : Blo 1132632 1702229 := bbase (se 10 (by rfl) ⟨2493, by rfl⟩ : syracuseStep 1702229 = 4987) (by norm_num)
theorem B1276249 : Blo 1132632 1276249 := bbase (se 2 (by rfl) ⟨478593, by rfl⟩ : syracuseStep 1276249 = 957187) (by norm_num)
theorem B1702253 : Blo 1132632 1702253 := bbase (se 3 (by rfl) ⟨319172, by rfl⟩ : syracuseStep 1702253 = 638345) (by norm_num)
theorem B1276285 : Blo 1132632 1276285 := bbase (se 3 (by rfl) ⟨239303, by rfl⟩ : syracuseStep 1276285 = 478607) (by norm_num)
theorem B1702277 : Blo 1132632 1702277 := bbase (se 4 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 1702277 = 319177) (by norm_num)
theorem B2554253 : Blo 1132632 2554253 := bbase (se 3 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 2554253 = 957845) (by norm_num)
theorem B2423189 : Blo 1132632 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B1702301 : Blo 1132632 1702301 := bbase (se 3 (by rfl) ⟨319181, by rfl⟩ : syracuseStep 1702301 = 638363) (by norm_num)
theorem B1276321 : Blo 1132632 1276321 := bbase (se 2 (by rfl) ⟨478620, by rfl⟩ : syracuseStep 1276321 = 957241) (by norm_num)
theorem B1702325 : Blo 1132632 1702325 := bbase (se 5 (by rfl) ⟨79796, by rfl⟩ : syracuseStep 1702325 = 159593) (by norm_num)
theorem B1276357 : Blo 1132632 1276357 := bbase (se 4 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 1276357 = 239317) (by norm_num)
theorem B1702349 : Blo 1132632 1702349 := bbase (se 3 (by rfl) ⟨319190, by rfl⟩ : syracuseStep 1702349 = 638381) (by norm_num)
theorem B3275221 : Blo 1132632 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B2554325 : Blo 1132632 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B1702373 : Blo 1132632 1702373 := bbase (se 4 (by rfl) ⟨159597, by rfl⟩ : syracuseStep 1702373 = 319195) (by norm_num)
theorem B1276393 : Blo 1132632 1276393 := bbase (se 2 (by rfl) ⟨478647, by rfl⟩ : syracuseStep 1276393 = 957295) (by norm_num)
theorem B1702397 : Blo 1132632 1702397 := bbase (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) (by norm_num)
theorem B3832325 : Blo 1132632 3832325 := bbase (se 4 (by rfl) ⟨359280, by rfl⟩ : syracuseStep 3832325 = 718561) (by norm_num)
theorem B1276429 : Blo 1132632 1276429 := bbase (se 3 (by rfl) ⟨239330, by rfl⟩ : syracuseStep 1276429 = 478661) (by norm_num)
theorem B1702421 : Blo 1132632 1702421 := bbase (se 6 (by rfl) ⟨39900, by rfl⟩ : syracuseStep 1702421 = 79801) (by norm_num)
theorem B2554397 : Blo 1132632 2554397 := bbase (se 3 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 2554397 = 957899) (by norm_num)
theorem B2423333 : Blo 1132632 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B1702445 : Blo 1132632 1702445 := bbase (se 3 (by rfl) ⟨319208, by rfl⟩ : syracuseStep 1702445 = 638417) (by norm_num)
theorem B1276465 : Blo 1132632 1276465 := bbase (se 2 (by rfl) ⟨478674, by rfl⟩ : syracuseStep 1276465 = 957349) (by norm_num)
theorem B1210945 : Blo 1132632 1210945 := bbase (se 2 (by rfl) ⟨454104, by rfl⟩ : syracuseStep 1210945 = 908209) (by norm_num)
theorem B1702469 : Blo 1132632 1702469 := bbase (se 4 (by rfl) ⟨159606, by rfl⟩ : syracuseStep 1702469 = 319213) (by norm_num)
theorem B1276501 : Blo 1132632 1276501 := bbase (se 8 (by rfl) ⟨7479, by rfl⟩ : syracuseStep 1276501 = 14959) (by norm_num)
theorem B1702493 : Blo 1132632 1702493 := bbase (se 3 (by rfl) ⟨319217, by rfl⟩ : syracuseStep 1702493 = 638435) (by norm_num)
theorem B2554469 : Blo 1132632 2554469 := bbase (se 4 (by rfl) ⟨239481, by rfl⟩ : syracuseStep 2554469 = 478963) (by norm_num)
theorem B1702517 : Blo 1132632 1702517 := bbase (se 5 (by rfl) ⟨79805, by rfl⟩ : syracuseStep 1702517 = 159611) (by norm_num)
theorem B1276537 : Blo 1132632 1276537 := bbase (se 2 (by rfl) ⟨478701, by rfl⟩ : syracuseStep 1276537 = 957403) (by norm_num)
theorem B1702541 : Blo 1132632 1702541 := bbase (se 3 (by rfl) ⟨319226, by rfl⟩ : syracuseStep 1702541 = 638453) (by norm_num)
theorem B1276573 : Blo 1132632 1276573 := bbase (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) (by norm_num)
theorem B1702565 : Blo 1132632 1702565 := bbase (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) (by norm_num)
theorem B2554541 : Blo 1132632 2554541 := bbase (se 3 (by rfl) ⟨478976, by rfl⟩ : syracuseStep 2554541 = 957953) (by norm_num)
theorem B1702589 : Blo 1132632 1702589 := bbase (se 3 (by rfl) ⟨319235, by rfl⟩ : syracuseStep 1702589 = 638471) (by norm_num)
theorem B1276609 : Blo 1132632 1276609 := bbase (se 2 (by rfl) ⟨478728, by rfl⟩ : syracuseStep 1276609 = 957457) (by norm_num)
theorem B1702613 : Blo 1132632 1702613 := bbase (se 7 (by rfl) ⟨19952, by rfl⟩ : syracuseStep 1702613 = 39905) (by norm_num)
theorem B1276645 : Blo 1132632 1276645 := bbase (se 4 (by rfl) ⟨119685, by rfl⟩ : syracuseStep 1276645 = 239371) (by norm_num)
theorem B1702637 : Blo 1132632 1702637 := bbase (se 3 (by rfl) ⟨319244, by rfl⟩ : syracuseStep 1702637 = 638489) (by norm_num)
theorem B2554613 : Blo 1132632 2554613 := bbase (se 5 (by rfl) ⟨119747, by rfl⟩ : syracuseStep 2554613 = 239495) (by norm_num)
theorem B1702661 : Blo 1132632 1702661 := bbase (se 4 (by rfl) ⟨159624, by rfl⟩ : syracuseStep 1702661 = 319249) (by norm_num)
theorem B1276681 : Blo 1132632 1276681 := bbase (se 2 (by rfl) ⟨478755, by rfl⟩ : syracuseStep 1276681 = 957511) (by norm_num)
theorem B1702685 : Blo 1132632 1702685 := bbase (se 3 (by rfl) ⟨319253, by rfl⟩ : syracuseStep 1702685 = 638507) (by norm_num)
theorem B1276717 : Blo 1132632 1276717 := bbase (se 3 (by rfl) ⟨239384, by rfl⟩ : syracuseStep 1276717 = 478769) (by norm_num)
theorem B1702709 : Blo 1132632 1702709 := bbase (se 5 (by rfl) ⟨79814, by rfl⟩ : syracuseStep 1702709 = 159629) (by norm_num)
theorem B2554685 : Blo 1132632 2554685 := bbase (se 3 (by rfl) ⟨479003, by rfl⟩ : syracuseStep 2554685 = 958007) (by norm_num)
theorem B1702733 : Blo 1132632 1702733 := bbase (se 3 (by rfl) ⟨319262, by rfl⟩ : syracuseStep 1702733 = 638525) (by norm_num)
theorem B1276753 : Blo 1132632 1276753 := bbase (se 2 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 1276753 = 957565) (by norm_num)
theorem B1702757 : Blo 1132632 1702757 := bbase (se 4 (by rfl) ⟨159633, by rfl⟩ : syracuseStep 1702757 = 319267) (by norm_num)
theorem B1276789 : Blo 1132632 1276789 := bbase (se 5 (by rfl) ⟨59849, by rfl⟩ : syracuseStep 1276789 = 119699) (by norm_num)
theorem B1702781 : Blo 1132632 1702781 := bbase (se 3 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 1702781 = 638543) (by norm_num)
theorem B2554757 : Blo 1132632 2554757 := bbase (se 4 (by rfl) ⟨239508, by rfl⟩ : syracuseStep 2554757 = 479017) (by norm_num)
theorem B1702805 : Blo 1132632 1702805 := bbase (se 6 (by rfl) ⟨39909, by rfl⟩ : syracuseStep 1702805 = 79819) (by norm_num)
theorem B1276825 : Blo 1132632 1276825 := bbase (se 2 (by rfl) ⟨478809, by rfl⟩ : syracuseStep 1276825 = 957619) (by norm_num)
theorem B1702829 : Blo 1132632 1702829 := bbase (se 3 (by rfl) ⟨319280, by rfl⟩ : syracuseStep 1702829 = 638561) (by norm_num)
theorem B3832757 : Blo 1132632 3832757 := bbase (se 5 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 3832757 = 359321) (by norm_num)
theorem B1211321 : Blo 1132632 1211321 := bbase (se 2 (by rfl) ⟨454245, by rfl⟩ : syracuseStep 1211321 = 908491) (by norm_num)
theorem B1276861 : Blo 1132632 1276861 := bbase (se 3 (by rfl) ⟨239411, by rfl⟩ : syracuseStep 1276861 = 478823) (by norm_num)
theorem B1702853 : Blo 1132632 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B2554829 : Blo 1132632 2554829 := bbase (se 3 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 2554829 = 958061) (by norm_num)
theorem B1702877 : Blo 1132632 1702877 := bbase (se 3 (by rfl) ⟨319289, by rfl⟩ : syracuseStep 1702877 = 638579) (by norm_num)
theorem B1276897 : Blo 1132632 1276897 := bbase (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) (by norm_num)
theorem B1702901 : Blo 1132632 1702901 := bbase (se 5 (by rfl) ⟨79823, by rfl⟩ : syracuseStep 1702901 = 159647) (by norm_num)
theorem B1211393 : Blo 1132632 1211393 := bbase (se 2 (by rfl) ⟨454272, by rfl⟩ : syracuseStep 1211393 = 908545) (by norm_num)
theorem B1276933 : Blo 1132632 1276933 := bbase (se 4 (by rfl) ⟨119712, by rfl⟩ : syracuseStep 1276933 = 239425) (by norm_num)
theorem B2587661 : Blo 1132632 2587661 := bbase (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) (by norm_num)
theorem B1702925 : Blo 1132632 1702925 := bbase (se 3 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 1702925 = 638597) (by norm_num)
theorem B2554901 : Blo 1132632 2554901 := bbase (se 6 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 2554901 = 119761) (by norm_num)
theorem B1702949 : Blo 1132632 1702949 := bbase (se 4 (by rfl) ⟨159651, by rfl⟩ : syracuseStep 1702949 = 319303) (by norm_num)
theorem B1276969 : Blo 1132632 1276969 := bbase (se 2 (by rfl) ⟨478863, by rfl⟩ : syracuseStep 1276969 = 957727) (by norm_num)
theorem B1702973 : Blo 1132632 1702973 := bbase (se 3 (by rfl) ⟨319307, by rfl⟩ : syracuseStep 1702973 = 638615) (by norm_num)
theorem B2915389 : Blo 1132632 2915389 := bbase (se 3 (by rfl) ⟨546635, by rfl⟩ : syracuseStep 2915389 = 1093271) (by norm_num)
theorem B1277005 : Blo 1132632 1277005 := bbase (se 3 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 1277005 = 478877) (by norm_num)
theorem B1702997 : Blo 1132632 1702997 := bbase (se 8 (by rfl) ⟨9978, by rfl⟩ : syracuseStep 1702997 = 19957) (by norm_num)
theorem B2554973 : Blo 1132632 2554973 := bbase (se 3 (by rfl) ⟨479057, by rfl⟩ : syracuseStep 2554973 = 958115) (by norm_num)
theorem B1703021 : Blo 1132632 1703021 := bbase (se 3 (by rfl) ⟨319316, by rfl⟩ : syracuseStep 1703021 = 638633) (by norm_num)
theorem B1277041 : Blo 1132632 1277041 := bbase (se 2 (by rfl) ⟨478890, by rfl⟩ : syracuseStep 1277041 = 957781) (by norm_num)
theorem B1703045 : Blo 1132632 1703045 := bbase (se 4 (by rfl) ⟨159660, by rfl⟩ : syracuseStep 1703045 = 319321) (by norm_num)
theorem B1277077 : Blo 1132632 1277077 := bbase (se 6 (by rfl) ⟨29931, by rfl⟩ : syracuseStep 1277077 = 59863) (by norm_num)
theorem B1703069 : Blo 1132632 1703069 := bbase (se 3 (by rfl) ⟨319325, by rfl⟩ : syracuseStep 1703069 = 638651) (by norm_num)
theorem B2555045 : Blo 1132632 2555045 := bbase (se 4 (by rfl) ⟨239535, by rfl⟩ : syracuseStep 2555045 = 479071) (by norm_num)
theorem B1703093 : Blo 1132632 1703093 := bbase (se 5 (by rfl) ⟨79832, by rfl⟩ : syracuseStep 1703093 = 159665) (by norm_num)
theorem B1277113 : Blo 1132632 1277113 := bbase (se 2 (by rfl) ⟨478917, by rfl⟩ : syracuseStep 1277113 = 957835) (by norm_num)
theorem B1211581 : Blo 1132632 1211581 := bbase (se 3 (by rfl) ⟨227171, by rfl⟩ : syracuseStep 1211581 = 454343) (by norm_num)
theorem B1703117 : Blo 1132632 1703117 := bbase (se 3 (by rfl) ⟨319334, by rfl⟩ : syracuseStep 1703117 = 638669) (by norm_num)
theorem B13991125 : Blo 1132632 13991125 := bbase (se 7 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 13991125 = 327917) (by norm_num)
theorem B1277149 : Blo 1132632 1277149 := bbase (se 3 (by rfl) ⟨239465, by rfl⟩ : syracuseStep 1277149 = 478931) (by norm_num)
theorem B1703141 : Blo 1132632 1703141 := bbase (se 4 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 1703141 = 319339) (by norm_num)
theorem B2555117 : Blo 1132632 2555117 := bbase (se 3 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 2555117 = 958169) (by norm_num)
theorem B1703165 : Blo 1132632 1703165 := bbase (se 3 (by rfl) ⟨319343, by rfl⟩ : syracuseStep 1703165 = 638687) (by norm_num)
theorem B1277185 : Blo 1132632 1277185 := bbase (se 2 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 1277185 = 957889) (by norm_num)
theorem B2424077 : Blo 1132632 2424077 := bbase (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) (by norm_num)
theorem B1703189 : Blo 1132632 1703189 := bbase (se 6 (by rfl) ⟨39918, by rfl⟩ : syracuseStep 1703189 = 79837) (by norm_num)
theorem B1277221 : Blo 1132632 1277221 := bbase (se 4 (by rfl) ⟨119739, by rfl⟩ : syracuseStep 1277221 = 239479) (by norm_num)
theorem B1703213 : Blo 1132632 1703213 := bbase (se 3 (by rfl) ⟨319352, by rfl⟩ : syracuseStep 1703213 = 638705) (by norm_num)
theorem B2555189 : Blo 1132632 2555189 := bbase (se 5 (by rfl) ⟨119774, by rfl⟩ : syracuseStep 2555189 = 239549) (by norm_num)
theorem B1703237 : Blo 1132632 1703237 := bbase (se 4 (by rfl) ⟨159678, by rfl⟩ : syracuseStep 1703237 = 319357) (by norm_num)
theorem B1277257 : Blo 1132632 1277257 := bbase (se 2 (by rfl) ⟨478971, by rfl⟩ : syracuseStep 1277257 = 957943) (by norm_num)
theorem B1703261 : Blo 1132632 1703261 := bbase (se 3 (by rfl) ⟨319361, by rfl⟩ : syracuseStep 1703261 = 638723) (by norm_num)
theorem B3833189 : Blo 1132632 3833189 := bbase (se 4 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 3833189 = 718723) (by norm_num)
theorem B1277293 : Blo 1132632 1277293 := bbase (se 3 (by rfl) ⟨239492, by rfl⟩ : syracuseStep 1277293 = 478985) (by norm_num)
theorem B1211765 : Blo 1132632 1211765 := bbase (se 5 (by rfl) ⟨56801, by rfl⟩ : syracuseStep 1211765 = 113603) (by norm_num)
theorem B1703285 : Blo 1132632 1703285 := bbase (se 5 (by rfl) ⟨79841, by rfl⟩ : syracuseStep 1703285 = 159683) (by norm_num)
theorem B2555261 : Blo 1132632 2555261 := bbase (se 3 (by rfl) ⟨479111, by rfl⟩ : syracuseStep 2555261 = 958223) (by norm_num)
theorem B1703309 : Blo 1132632 1703309 := bbase (se 3 (by rfl) ⟨319370, by rfl⟩ : syracuseStep 1703309 = 638741) (by norm_num)
theorem B1277329 : Blo 1132632 1277329 := bbase (se 2 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 1277329 = 957997) (by norm_num)
theorem B1703333 : Blo 1132632 1703333 := bbase (se 4 (by rfl) ⟨159687, by rfl⟩ : syracuseStep 1703333 = 319375) (by norm_num)
theorem B1277365 : Blo 1132632 1277365 := bbase (se 5 (by rfl) ⟨59876, by rfl⟩ : syracuseStep 1277365 = 119753) (by norm_num)
theorem B1703357 : Blo 1132632 1703357 := bbase (se 3 (by rfl) ⟨319379, by rfl⟩ : syracuseStep 1703357 = 638759) (by norm_num)
theorem B2555333 : Blo 1132632 2555333 := bbase (se 4 (by rfl) ⟨239562, by rfl⟩ : syracuseStep 2555333 = 479125) (by norm_num)
theorem B1703381 : Blo 1132632 1703381 := bbase (se 7 (by rfl) ⟨19961, by rfl⟩ : syracuseStep 1703381 = 39923) (by norm_num)
theorem B1277401 : Blo 1132632 1277401 := bbase (se 2 (by rfl) ⟨479025, by rfl⟩ : syracuseStep 1277401 = 958051) (by norm_num)
theorem B1703405 : Blo 1132632 1703405 := bbase (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) (by norm_num)
theorem B1277437 : Blo 1132632 1277437 := bbase (se 3 (by rfl) ⟨239519, by rfl⟩ : syracuseStep 1277437 = 479039) (by norm_num)
theorem B1703429 : Blo 1132632 1703429 := bbase (se 4 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 1703429 = 319393) (by norm_num)
theorem B2555405 : Blo 1132632 2555405 := bbase (se 3 (by rfl) ⟨479138, by rfl⟩ : syracuseStep 2555405 = 958277) (by norm_num)
theorem B20708885 : Blo 1132632 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B1703453 : Blo 1132632 1703453 := bbase (se 3 (by rfl) ⟨319397, by rfl⟩ : syracuseStep 1703453 = 638795) (by norm_num)
theorem B1277473 : Blo 1132632 1277473 := bbase (se 2 (by rfl) ⟨479052, by rfl⟩ : syracuseStep 1277473 = 958105) (by norm_num)
theorem B1703477 : Blo 1132632 1703477 := bbase (se 5 (by rfl) ⟨79850, by rfl⟩ : syracuseStep 1703477 = 159701) (by norm_num)
theorem B1277509 : Blo 1132632 1277509 := bbase (se 4 (by rfl) ⟨119766, by rfl⟩ : syracuseStep 1277509 = 239533) (by norm_num)
theorem B1703501 : Blo 1132632 1703501 := bbase (se 3 (by rfl) ⟨319406, by rfl⟩ : syracuseStep 1703501 = 638813) (by norm_num)
theorem B2555477 : Blo 1132632 2555477 := bbase (se 8 (by rfl) ⟨14973, by rfl⟩ : syracuseStep 2555477 = 29947) (by norm_num)
theorem B5733989 : Blo 1132632 5733989 := bbase (se 4 (by rfl) ⟨537561, by rfl⟩ : syracuseStep 5733989 = 1075123) (by norm_num)
theorem B1703525 : Blo 1132632 1703525 := bbase (se 4 (by rfl) ⟨159705, by rfl⟩ : syracuseStep 1703525 = 319411) (by norm_num)
theorem B1277545 : Blo 1132632 1277545 := bbase (se 2 (by rfl) ⟨479079, by rfl⟩ : syracuseStep 1277545 = 958159) (by norm_num)
theorem B1703549 : Blo 1132632 1703549 := bbase (se 3 (by rfl) ⟨319415, by rfl⟩ : syracuseStep 1703549 = 638831) (by norm_num)
theorem B1277581 : Blo 1132632 1277581 := bbase (se 3 (by rfl) ⟨239546, by rfl⟩ : syracuseStep 1277581 = 479093) (by norm_num)
theorem B1703573 : Blo 1132632 1703573 := bbase (se 6 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 1703573 = 79855) (by norm_num)
theorem B2555549 : Blo 1132632 2555549 := bbase (se 3 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 2555549 = 958331) (by norm_num)
theorem B1703597 : Blo 1132632 1703597 := bbase (se 3 (by rfl) ⟨319424, by rfl⟩ : syracuseStep 1703597 = 638849) (by norm_num)
theorem B1277617 : Blo 1132632 1277617 := bbase (se 2 (by rfl) ⟨479106, by rfl⟩ : syracuseStep 1277617 = 958213) (by norm_num)
theorem B1703621 : Blo 1132632 1703621 := bbase (se 4 (by rfl) ⟨159714, by rfl⟩ : syracuseStep 1703621 = 319429) (by norm_num)
theorem B1277653 : Blo 1132632 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B1703645 : Blo 1132632 1703645 := bbase (se 3 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 1703645 = 638867) (by norm_num)
theorem B2457317 : Blo 1132632 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B2555621 : Blo 1132632 2555621 := bbase (se 4 (by rfl) ⟨239589, by rfl⟩ : syracuseStep 2555621 = 479179) (by norm_num)
theorem B1703669 : Blo 1132632 1703669 := bbase (se 5 (by rfl) ⟨79859, by rfl⟩ : syracuseStep 1703669 = 159719) (by norm_num)
theorem B1277689 : Blo 1132632 1277689 := bbase (se 2 (by rfl) ⟨479133, by rfl⟩ : syracuseStep 1277689 = 958267) (by norm_num)
theorem B1703693 : Blo 1132632 1703693 := bbase (se 3 (by rfl) ⟨319442, by rfl⟩ : syracuseStep 1703693 = 638885) (by norm_num)
theorem B3833621 : Blo 1132632 3833621 := bbase (se 6 (by rfl) ⟨89850, by rfl⟩ : syracuseStep 3833621 = 179701) (by norm_num)
theorem B1277725 : Blo 1132632 1277725 := bbase (se 3 (by rfl) ⟨239573, by rfl⟩ : syracuseStep 1277725 = 479147) (by norm_num)
theorem B1703717 : Blo 1132632 1703717 := bbase (se 4 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 1703717 = 319447) (by norm_num)
theorem B2555693 : Blo 1132632 2555693 := bbase (se 3 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 2555693 = 958385) (by norm_num)
theorem B1703741 : Blo 1132632 1703741 := bbase (se 3 (by rfl) ⟨319451, by rfl⟩ : syracuseStep 1703741 = 638903) (by norm_num)
theorem B1277761 : Blo 1132632 1277761 := bbase (se 2 (by rfl) ⟨479160, by rfl⟩ : syracuseStep 1277761 = 958321) (by norm_num)
theorem B1703765 : Blo 1132632 1703765 := bbase (se 9 (by rfl) ⟨4991, by rfl⟩ : syracuseStep 1703765 = 9983) (by norm_num)
theorem B1277797 : Blo 1132632 1277797 := bbase (se 4 (by rfl) ⟨119793, by rfl⟩ : syracuseStep 1277797 = 239587) (by norm_num)
theorem B1703789 : Blo 1132632 1703789 := bbase (se 3 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 1703789 = 638921) (by norm_num)
theorem B7274357 : Blo 1132632 7274357 := bbase (se 5 (by rfl) ⟨340985, by rfl⟩ : syracuseStep 7274357 = 681971) (by norm_num)
theorem B2555765 : Blo 1132632 2555765 := bbase (se 5 (by rfl) ⟨119801, by rfl⟩ : syracuseStep 2555765 = 239603) (by norm_num)
theorem B1703813 : Blo 1132632 1703813 := bbase (se 4 (by rfl) ⟨159732, by rfl⟩ : syracuseStep 1703813 = 319465) (by norm_num)
theorem B1277833 : Blo 1132632 1277833 := bbase (se 2 (by rfl) ⟨479187, by rfl⟩ : syracuseStep 1277833 = 958375) (by norm_num)
theorem B1703837 : Blo 1132632 1703837 := bbase (se 3 (by rfl) ⟨319469, by rfl⟩ : syracuseStep 1703837 = 638939) (by norm_num)
theorem B1310629 : Blo 1132632 1310629 := bbase (se 4 (by rfl) ⟨122871, by rfl⟩ : syracuseStep 1310629 = 245743) (by norm_num)
theorem B1277869 : Blo 1132632 1277869 := bbase (se 3 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 1277869 = 479201) (by norm_num)
theorem B1703861 : Blo 1132632 1703861 := bbase (se 5 (by rfl) ⟨79868, by rfl⟩ : syracuseStep 1703861 = 159737) (by norm_num)
theorem B2555837 : Blo 1132632 2555837 := bbase (se 3 (by rfl) ⟨479219, by rfl⟩ : syracuseStep 2555837 = 958439) (by norm_num)
theorem B1703885 : Blo 1132632 1703885 := bbase (se 3 (by rfl) ⟨319478, by rfl⟩ : syracuseStep 1703885 = 638957) (by norm_num)
theorem B1277905 : Blo 1132632 1277905 := bbase (se 2 (by rfl) ⟨479214, by rfl⟩ : syracuseStep 1277905 = 958429) (by norm_num)
theorem B1703909 : Blo 1132632 1703909 := bbase (se 4 (by rfl) ⟨159741, by rfl⟩ : syracuseStep 1703909 = 319483) (by norm_num)
theorem B1277941 : Blo 1132632 1277941 := bbase (se 5 (by rfl) ⟨59903, by rfl⟩ : syracuseStep 1277941 = 119807) (by norm_num)
theorem B1703939 : Blo 1132632 1703939 := bstep (se 1 (by rfl) ⟨1277954, by rfl⟩ : syracuseStep 1703939 = 2555909) B2555909
theorem B1703969 : Blo 1132632 1703969 := bstep (se 2 (by rfl) ⟨638988, by rfl⟩ : syracuseStep 1703969 = 1277977) B1277977
theorem B3833891 : Blo 1132632 3833891 := bstep (se 1 (by rfl) ⟨2875418, by rfl⟩ : syracuseStep 3833891 = 5750837) B5750837
theorem B1703987 : Blo 1132632 1703987 := bstep (se 1 (by rfl) ⟨1277990, by rfl⟩ : syracuseStep 1703987 = 2555981) B2555981
theorem B1704017 : Blo 1132632 1704017 := bstep (se 2 (by rfl) ⟨639006, by rfl⟩ : syracuseStep 1704017 = 1278013) B1278013
theorem B1704035 : Blo 1132632 1704035 := bstep (se 1 (by rfl) ⟨1278026, by rfl⟩ : syracuseStep 1704035 = 2556053) B2556053
theorem B52396145 : Blo 1132632 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B2556017 : Blo 1132632 2556017 := bstep (se 2 (by rfl) ⟨958506, by rfl⟩ : syracuseStep 2556017 = 1917013) B1917013
theorem B1278067 : Blo 1132632 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B1704065 : Blo 1132632 1704065 := bstep (se 2 (by rfl) ⟨639024, by rfl⟩ : syracuseStep 1704065 = 1278049) B1278049
theorem B2556035 : Blo 1132632 2556035 := bstep (se 1 (by rfl) ⟨1917026, by rfl⟩ : syracuseStep 2556035 = 3834053) B3834053
theorem B1704083 : Blo 1132632 1704083 := bstep (se 1 (by rfl) ⟨1278062, by rfl⟩ : syracuseStep 1704083 = 2556125) B2556125
theorem B1704113 : Blo 1132632 1704113 := bstep (se 2 (by rfl) ⟨639042, by rfl⟩ : syracuseStep 1704113 = 1278085) B1278085
theorem B1704131 : Blo 1132632 1704131 := bstep (se 1 (by rfl) ⟨1278098, by rfl⟩ : syracuseStep 1704131 = 2556197) B2556197
theorem B1704161 : Blo 1132632 1704161 := bstep (se 2 (by rfl) ⟨639060, by rfl⟩ : syracuseStep 1704161 = 1278121) B1278121
theorem B1704179 : Blo 1132632 1704179 := bstep (se 1 (by rfl) ⟨1278134, by rfl⟩ : syracuseStep 1704179 = 2556269) B2556269
theorem B1278211 : Blo 1132632 1278211 := bstep (se 1 (by rfl) ⟨958658, by rfl⟩ : syracuseStep 1278211 = 1917317) B1917317
theorem B1704209 : Blo 1132632 1704209 := bstep (se 2 (by rfl) ⟨639078, by rfl⟩ : syracuseStep 1704209 = 1278157) B1278157
theorem B1704227 : Blo 1132632 1704227 := bstep (se 1 (by rfl) ⟨1278170, by rfl⟩ : syracuseStep 1704227 = 2556341) B2556341
theorem B3834161 : Blo 1132632 3834161 := bstep (se 2 (by rfl) ⟨1437810, by rfl⟩ : syracuseStep 3834161 = 2875621) B2875621
theorem B1704257 : Blo 1132632 1704257 := bstep (se 2 (by rfl) ⟨639096, by rfl⟩ : syracuseStep 1704257 = 1278193) B1278193
theorem B1704275 : Blo 1132632 1704275 := bstep (se 1 (by rfl) ⟨1278206, by rfl⟩ : syracuseStep 1704275 = 2556413) B2556413
theorem B2589041 : Blo 1132632 2589041 := bstep (se 2 (by rfl) ⟨970890, by rfl⟩ : syracuseStep 2589041 = 1941781) B1941781
theorem B1704305 : Blo 1132632 1704305 := bstep (se 2 (by rfl) ⟨639114, by rfl⟩ : syracuseStep 1704305 = 1278229) B1278229
theorem B1704323 : Blo 1132632 1704323 := bstep (se 1 (by rfl) ⟨1278242, by rfl⟩ : syracuseStep 1704323 = 2556485) B2556485
theorem B2556305 : Blo 1132632 2556305 := bstep (se 2 (by rfl) ⟨958614, by rfl⟩ : syracuseStep 2556305 = 1917229) B1917229
theorem B1278355 : Blo 1132632 1278355 := bstep (se 1 (by rfl) ⟨958766, by rfl⟩ : syracuseStep 1278355 = 1917533) B1917533
theorem B1704353 : Blo 1132632 1704353 := bstep (se 2 (by rfl) ⟨639132, by rfl⟩ : syracuseStep 1704353 = 1278265) B1278265
theorem B2556323 : Blo 1132632 2556323 := bstep (se 1 (by rfl) ⟨1917242, by rfl⟩ : syracuseStep 2556323 = 3834485) B3834485
theorem B1704371 : Blo 1132632 1704371 := bstep (se 1 (by rfl) ⟨1278278, by rfl⟩ : syracuseStep 1704371 = 2556557) B2556557
theorem B1704401 : Blo 1132632 1704401 := bstep (se 2 (by rfl) ⟨639150, by rfl⟩ : syracuseStep 1704401 = 1278301) B1278301
theorem B2425315 : Blo 1132632 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B1704419 : Blo 1132632 1704419 := bstep (se 1 (by rfl) ⟨1278314, by rfl⟩ : syracuseStep 1704419 = 2556629) B2556629
theorem B1704449 : Blo 1132632 1704449 := bstep (se 2 (by rfl) ⟨639168, by rfl⟩ : syracuseStep 1704449 = 1278337) B1278337
theorem B1212931 : Blo 1132632 1212931 := bstep (se 1 (by rfl) ⟨909698, by rfl⟩ : syracuseStep 1212931 = 1819397) B1819397
theorem B1704467 : Blo 1132632 1704467 := bstep (se 1 (by rfl) ⟨1278350, by rfl⟩ : syracuseStep 1704467 = 2556701) B2556701
theorem B1278499 : Blo 1132632 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B5734961 : Blo 1132632 5734961 := bstep (se 2 (by rfl) ⟨2150610, by rfl⟩ : syracuseStep 5734961 = 4301221) B4301221
theorem B1704497 : Blo 1132632 1704497 := bstep (se 2 (by rfl) ⟨639186, by rfl⟩ : syracuseStep 1704497 = 1278373) B1278373
theorem B1704515 : Blo 1132632 1704515 := bstep (se 1 (by rfl) ⟨1278386, by rfl⟩ : syracuseStep 1704515 = 2556773) B2556773
theorem B1704545 : Blo 1132632 1704545 := bstep (se 2 (by rfl) ⟨639204, by rfl⟩ : syracuseStep 1704545 = 1278409) B1278409
theorem B1704563 : Blo 1132632 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B1704593 : Blo 1132632 1704593 := bstep (se 2 (by rfl) ⟨639222, by rfl⟩ : syracuseStep 1704593 = 1278445) B1278445
theorem B1704611 : Blo 1132632 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B2556593 : Blo 1132632 2556593 := bstep (se 2 (by rfl) ⟨958722, by rfl⟩ : syracuseStep 2556593 = 1917445) B1917445
theorem B1278643 : Blo 1132632 1278643 := bstep (se 1 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 1278643 = 1917965) B1917965
theorem B1704641 : Blo 1132632 1704641 := bstep (se 2 (by rfl) ⟨639240, by rfl⟩ : syracuseStep 1704641 = 1278481) B1278481
theorem B2556611 : Blo 1132632 2556611 := bstep (se 1 (by rfl) ⟨1917458, by rfl⟩ : syracuseStep 2556611 = 3834917) B3834917
theorem B1704659 : Blo 1132632 1704659 := bstep (se 1 (by rfl) ⟨1278494, by rfl⟩ : syracuseStep 1704659 = 2556989) B2556989
theorem B8618723 : Blo 1132632 8618723 := bstep (se 1 (by rfl) ⟨6464042, by rfl⟩ : syracuseStep 8618723 = 12928085) B12928085
theorem B1704689 : Blo 1132632 1704689 := bstep (se 2 (by rfl) ⟨639258, by rfl⟩ : syracuseStep 1704689 = 1278517) B1278517
theorem B1704707 : Blo 1132632 1704707 := bstep (se 1 (by rfl) ⟨1278530, by rfl⟩ : syracuseStep 1704707 = 2557061) B2557061
theorem B1704737 : Blo 1132632 1704737 := bstep (se 2 (by rfl) ⟨639276, by rfl⟩ : syracuseStep 1704737 = 1278553) B1278553
theorem B1704755 : Blo 1132632 1704755 := bstep (se 1 (by rfl) ⟨1278566, by rfl⟩ : syracuseStep 1704755 = 2557133) B2557133
theorem B3834701 : Blo 1132632 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B1704785 : Blo 1132632 1704785 := bstep (se 2 (by rfl) ⟨639294, by rfl⟩ : syracuseStep 1704785 = 1278589) B1278589
theorem B1704803 : Blo 1132632 1704803 := bstep (se 1 (by rfl) ⟨1278602, by rfl⟩ : syracuseStep 1704803 = 2557205) B2557205
theorem B1704833 : Blo 1132632 1704833 := bstep (se 2 (by rfl) ⟨639312, by rfl⟩ : syracuseStep 1704833 = 1278625) B1278625
theorem B3834755 : Blo 1132632 3834755 := bstep (se 1 (by rfl) ⟨2876066, by rfl⟩ : syracuseStep 3834755 = 5752133) B5752133
theorem B1704851 : Blo 1132632 1704851 := bstep (se 1 (by rfl) ⟨1278638, by rfl⟩ : syracuseStep 1704851 = 2557277) B2557277
theorem B1704881 : Blo 1132632 1704881 := bstep (se 2 (by rfl) ⟨639330, by rfl⟩ : syracuseStep 1704881 = 1278661) B1278661
theorem B1704899 : Blo 1132632 1704899 := bstep (se 1 (by rfl) ⟨1278674, by rfl⟩ : syracuseStep 1704899 = 2557349) B2557349
theorem B2556881 : Blo 1132632 2556881 := bstep (se 2 (by rfl) ⟨958830, by rfl⟩ : syracuseStep 2556881 = 1917661) B1917661
theorem B1704929 : Blo 1132632 1704929 := bstep (se 2 (by rfl) ⟨639348, by rfl⟩ : syracuseStep 1704929 = 1278697) B1278697
theorem B2556899 : Blo 1132632 2556899 := bstep (se 1 (by rfl) ⟨1917674, by rfl⟩ : syracuseStep 2556899 = 3835349) B3835349
theorem B1704947 : Blo 1132632 1704947 := bstep (se 1 (by rfl) ⟨1278710, by rfl⟩ : syracuseStep 1704947 = 2557421) B2557421
theorem B3638371 : Blo 1132632 3638371 := bstep (se 1 (by rfl) ⟨2728778, by rfl⟩ : syracuseStep 3638371 = 5457557) B5457557
theorem B3835025 : Blo 1132632 3835025 := bstep (se 2 (by rfl) ⟨1438134, by rfl⟩ : syracuseStep 3835025 = 2876269) B2876269
theorem B2426033 : Blo 1132632 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B2557169 : Blo 1132632 2557169 := bstep (se 2 (by rfl) ⟨958938, by rfl⟩ : syracuseStep 2557169 = 1917877) B1917877
theorem B2557187 : Blo 1132632 2557187 := bstep (se 1 (by rfl) ⟨1917890, by rfl⟩ : syracuseStep 2557187 = 3835781) B3835781
theorem B3638819 : Blo 1132632 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B3835565 : Blo 1132632 3835565 := bstep (se 3 (by rfl) ⟨719168, by rfl⟩ : syracuseStep 3835565 = 1438337) B1438337
theorem B2426545 : Blo 1132632 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B3835619 : Blo 1132632 3835619 := bstep (se 1 (by rfl) ⟨2876714, by rfl⟩ : syracuseStep 3835619 = 5753429) B5753429
theorem B1148803 : Blo 1132632 1148803 := bstep (se 1 (by rfl) ⟨861602, by rfl⟩ : syracuseStep 1148803 = 1723205) B1723205
theorem B1640369 : Blo 1132632 1640369 := bstep (se 2 (by rfl) ⟨615138, by rfl⟩ : syracuseStep 1640369 = 1230277) B1230277
theorem B5736419 : Blo 1132632 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B3835889 : Blo 1132632 3835889 := bstep (se 2 (by rfl) ⟨1438458, by rfl⟩ : syracuseStep 3835889 = 2876917) B2876917
theorem B6129827 : Blo 1132632 6129827 := bstep (se 1 (by rfl) ⟨4597370, by rfl⟩ : syracuseStep 6129827 = 9194741) B9194741
theorem B3640049 : Blo 1132632 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B5737229 : Blo 1132632 5737229 := bstep (se 3 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 5737229 = 2151461) B2151461
theorem B5442851 : Blo 1132632 5442851 := bstep (se 1 (by rfl) ⟨4082138, by rfl⟩ : syracuseStep 5442851 = 8164277) B8164277
theorem B3280483 : Blo 1132632 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B3640945 : Blo 1132632 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B4853773 : Blo 1132632 4853773 := bstep (se 3 (by rfl) ⟨910082, by rfl⟩ : syracuseStep 4853773 = 1820165) B1820165
theorem B6459533 : Blo 1132632 6459533 := bstep (se 3 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 6459533 = 2422325) B2422325
theorem B1151443 : Blo 1132632 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B5444081 : Blo 1132632 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B2298385 : Blo 1132632 2298385 := bstep (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) B1723789
theorem B33133283 : Blo 1132632 33133283 := bstep (se 1 (by rfl) ⟨24849962, by rfl⟩ : syracuseStep 33133283 = 49699925) B49699925
theorem B6132485 : Blo 1132632 6132485 := bstep (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) B1149841
theorem B26186773 : Blo 1132632 26186773 := bstep (se 6 (by rfl) ⟨613752, by rfl⟩ : syracuseStep 26186773 = 1227505) B1227505
theorem B6132941 : Blo 1132632 6132941 := bstep (se 3 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 6132941 = 2299853) B2299853
theorem B1938995 : Blo 1132632 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B5740145 : Blo 1132632 5740145 := bstep (se 2 (by rfl) ⟨2152554, by rfl⟩ : syracuseStep 5740145 = 4305109) B4305109
theorem B12916421 : Blo 1132632 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B3446545 : Blo 1132632 3446545 := bstep (se 2 (by rfl) ⟨1292454, by rfl⟩ : syracuseStep 3446545 = 2584909) B2584909
theorem B5445425 : Blo 1132632 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B5183281 : Blo 1132632 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B24549317 : Blo 1132632 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B8624069 : Blo 1132632 8624069 := bstep (se 4 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 8624069 = 1617013) B1617013
theorem B21010373 : Blo 1132632 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B2758691 : Blo 1132632 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B6461765 : Blo 1132632 6461765 := bstep (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) B1211581
theorem B5446349 : Blo 1132632 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B5184269 : Blo 1132632 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B5446541 : Blo 1132632 5446541 := bstep (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) B2042453
theorem B6462449 : Blo 1132632 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B5741603 : Blo 1132632 5741603 := bstep (se 1 (by rfl) ⟨4306202, by rfl⟩ : syracuseStep 5741603 = 8612405) B8612405
theorem B1612867 : Blo 1132632 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B2727395 : Blo 1132632 2727395 := bstep (se 1 (by rfl) ⟨2045546, by rfl⟩ : syracuseStep 2727395 = 4091093) B4091093
theorem B2301571 : Blo 1132632 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B1941185 : Blo 1132632 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B5742413 : Blo 1132632 5742413 := bstep (se 3 (by rfl) ⟨1076702, by rfl⟩ : syracuseStep 5742413 = 2153405) B2153405
theorem B4595555 : Blo 1132632 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B4300721 : Blo 1132632 4300721 := bstep (se 2 (by rfl) ⟨1612770, by rfl⟩ : syracuseStep 4300721 = 3225541) B3225541
theorem B1614001 : Blo 1132632 1614001 := bstep (se 2 (by rfl) ⟨605250, by rfl⟩ : syracuseStep 1614001 = 1210501) B1210501
theorem B1614097 : Blo 1132632 1614097 := bstep (se 2 (by rfl) ⟨605286, by rfl⟩ : syracuseStep 1614097 = 1210573) B1210573
theorem B6463907 : Blo 1132632 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B31007285 : Blo 1132632 31007285 := bstep (se 5 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 31007285 = 2906933) B2906933
theorem B4366961 : Blo 1132632 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B22094477 : Blo 1132632 22094477 := bstep (se 3 (by rfl) ⟨4142714, by rfl⟩ : syracuseStep 22094477 = 8285429) B8285429
theorem B6136483 : Blo 1132632 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B1614593 : Blo 1132632 1614593 := bstep (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) B1210945
theorem B4302179 : Blo 1132632 4302179 := bstep (se 1 (by rfl) ⟨3226634, by rfl⟩ : syracuseStep 4302179 = 6453269) B6453269
theorem B4302193 : Blo 1132632 4302193 := bstep (se 2 (by rfl) ⟨1613322, by rfl⟩ : syracuseStep 4302193 = 3226645) B3226645
theorem B1615459 : Blo 1132632 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B18654833 : Blo 1132632 18654833 := bstep (se 2 (by rfl) ⟨6995562, by rfl⟩ : syracuseStep 18654833 = 13991125) B13991125
theorem B1615555 : Blo 1132632 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B1844947 : Blo 1132632 1844947 := bstep (se 1 (by rfl) ⟨1383710, by rfl⟩ : syracuseStep 1844947 = 2767421) B2767421
theorem B2303729 : Blo 1132632 2303729 := bstep (se 2 (by rfl) ⟨863898, by rfl⟩ : syracuseStep 2303729 = 1727797) B1727797
theorem B5253169 : Blo 1132632 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B10889315 : Blo 1132632 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B1616051 : Blo 1132632 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B13805923 : Blo 1132632 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B1747505 : Blo 1132632 1747505 := bstep (se 2 (by rfl) ⟨655314, by rfl⟩ : syracuseStep 1747505 = 1310629) B1310629
theorem B1911377 : Blo 1132632 1911377 := bstep (se 2 (by rfl) ⟨716766, by rfl⟩ : syracuseStep 1911377 = 1433533) B1433533
theorem B5745329 : Blo 1132632 5745329 := bstep (se 2 (by rfl) ⟨2154498, by rfl⟩ : syracuseStep 5745329 = 4308997) B4308997
theorem B1911505 : Blo 1132632 1911505 := bstep (se 2 (by rfl) ⟨716814, by rfl⟩ : syracuseStep 1911505 = 1433629) B1433629
theorem B1911539 : Blo 1132632 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B4303651 : Blo 1132632 4303651 := bstep (se 1 (by rfl) ⟨3227738, by rfl⟩ : syracuseStep 4303651 = 6455477) B6455477
theorem B1616689 : Blo 1132632 1616689 := bstep (se 2 (by rfl) ⟨606258, by rfl⟩ : syracuseStep 1616689 = 1212517) B1212517
theorem B27601717 : Blo 1132632 27601717 := bstep (se 5 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 27601717 = 2587661) B2587661
theorem B1911667 : Blo 1132632 1911667 := bstep (se 1 (by rfl) ⟨1433750, by rfl⟩ : syracuseStep 1911667 = 2867501) B2867501
theorem B1911809 : Blo 1132632 1911809 := bstep (se 2 (by rfl) ⟨716928, by rfl⟩ : syracuseStep 1911809 = 1433857) B1433857
theorem B2042929 : Blo 1132632 2042929 := bstep (se 2 (by rfl) ⟨766098, by rfl⟩ : syracuseStep 2042929 = 1532197) B1532197
theorem B1911937 : Blo 1132632 1911937 := bstep (se 2 (by rfl) ⟨716976, by rfl⟩ : syracuseStep 1911937 = 1433953) B1433953
theorem B1617025 : Blo 1132632 1617025 := bstep (se 2 (by rfl) ⟨606384, by rfl⟩ : syracuseStep 1617025 = 1212769) B1212769
theorem B1911971 : Blo 1132632 1911971 := bstep (se 1 (by rfl) ⟨1433978, by rfl⟩ : syracuseStep 1911971 = 2867957) B2867957
theorem B1912099 : Blo 1132632 1912099 := bstep (se 1 (by rfl) ⟨1434074, by rfl⟩ : syracuseStep 1912099 = 2868149) B2868149
theorem B4369763 : Blo 1132632 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B12922253 : Blo 1132632 12922253 := bstep (se 3 (by rfl) ⟨2422922, by rfl⟩ : syracuseStep 12922253 = 4845845) B4845845
theorem B1912241 : Blo 1132632 1912241 := bstep (se 2 (by rfl) ⟨717090, by rfl⟩ : syracuseStep 1912241 = 1434181) B1434181
theorem B31075811 : Blo 1132632 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B6139405 : Blo 1132632 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B1912369 : Blo 1132632 1912369 := bstep (se 2 (by rfl) ⟨717138, by rfl⟩ : syracuseStep 1912369 = 1434277) B1434277
theorem B6467141 : Blo 1132632 6467141 := bstep (se 4 (by rfl) ⟨606294, by rfl⟩ : syracuseStep 6467141 = 1212589) B1212589
theorem B1912403 : Blo 1132632 1912403 := bstep (se 1 (by rfl) ⟨1434302, by rfl⟩ : syracuseStep 1912403 = 2868605) B2868605
theorem B8629901 : Blo 1132632 8629901 := bstep (se 3 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 8629901 = 3236213) B3236213
theorem B1617617 : Blo 1132632 1617617 := bstep (se 2 (by rfl) ⟨606606, by rfl⟩ : syracuseStep 1617617 = 1213213) B1213213
theorem B1912531 : Blo 1132632 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B3878705 : Blo 1132632 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B1912673 : Blo 1132632 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B1912801 : Blo 1132632 1912801 := bstep (se 2 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 1912801 = 1434601) B1434601
theorem B26521571 : Blo 1132632 26521571 := bstep (se 1 (by rfl) ⟨19891178, by rfl⟩ : syracuseStep 26521571 = 39782357) B39782357
theorem B4861937 : Blo 1132632 4861937 := bstep (se 2 (by rfl) ⟨1823226, by rfl⟩ : syracuseStep 4861937 = 3646453) B3646453
theorem B1912835 : Blo 1132632 1912835 := bstep (se 1 (by rfl) ⟨1434626, by rfl⟩ : syracuseStep 1912835 = 2869253) B2869253
theorem B6467597 : Blo 1132632 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B5746787 : Blo 1132632 5746787 := bstep (se 1 (by rfl) ⟨4310090, by rfl⟩ : syracuseStep 5746787 = 8620181) B8620181
theorem B1912963 : Blo 1132632 1912963 := bstep (se 1 (by rfl) ⟨1434722, by rfl⟩ : syracuseStep 1912963 = 2869445) B2869445
theorem B3879085 : Blo 1132632 3879085 := bstep (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) B1454657
theorem B1618147 : Blo 1132632 1618147 := bstep (se 1 (by rfl) ⟨1213610, by rfl⟩ : syracuseStep 1618147 = 2427221) B2427221
theorem B4141297 : Blo 1132632 4141297 := bstep (se 2 (by rfl) ⟨1552986, by rfl⟩ : syracuseStep 4141297 = 3105973) B3105973
theorem B1913105 : Blo 1132632 1913105 := bstep (se 2 (by rfl) ⟨717414, by rfl⟩ : syracuseStep 1913105 = 1434829) B1434829
theorem B2765123 : Blo 1132632 2765123 := bstep (se 1 (by rfl) ⟨2073842, by rfl⟩ : syracuseStep 2765123 = 4147685) B4147685
theorem B8302961 : Blo 1132632 8302961 := bstep (se 2 (by rfl) ⟨3113610, by rfl⟩ : syracuseStep 8302961 = 6227221) B6227221
theorem B1814899 : Blo 1132632 1814899 := bstep (se 1 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 1814899 = 2722349) B2722349
theorem B1913233 : Blo 1132632 1913233 := bstep (se 2 (by rfl) ⟨717462, by rfl⟩ : syracuseStep 1913233 = 1434925) B1434925
theorem B1913267 : Blo 1132632 1913267 := bstep (se 1 (by rfl) ⟨1434950, by rfl⟩ : syracuseStep 1913267 = 2869901) B2869901
theorem B6631877 : Blo 1132632 6631877 := bstep (se 4 (by rfl) ⟨621738, by rfl⟩ : syracuseStep 6631877 = 1243477) B1243477
theorem B1913395 : Blo 1132632 1913395 := bstep (se 1 (by rfl) ⟨1435046, by rfl⟩ : syracuseStep 1913395 = 2870093) B2870093
theorem B1913537 : Blo 1132632 1913537 := bstep (se 2 (by rfl) ⟨717576, by rfl⟩ : syracuseStep 1913537 = 1435153) B1435153
theorem B1913665 : Blo 1132632 1913665 := bstep (se 2 (by rfl) ⟨717624, by rfl⟩ : syracuseStep 1913665 = 1435249) B1435249
theorem B2044739 : Blo 1132632 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B1913699 : Blo 1132632 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B5747597 : Blo 1132632 5747597 := bstep (se 3 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 5747597 = 2155349) B2155349
theorem B4305869 : Blo 1132632 4305869 := bstep (se 3 (by rfl) ⟨807350, by rfl⟩ : syracuseStep 4305869 = 1614701) B1614701
theorem B1913827 : Blo 1132632 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B1815617 : Blo 1132632 1815617 := bstep (se 2 (by rfl) ⟨680856, by rfl⟩ : syracuseStep 1815617 = 1361713) B1361713
theorem B1913969 : Blo 1132632 1913969 := bstep (se 2 (by rfl) ⟨717738, by rfl⟩ : syracuseStep 1913969 = 1435477) B1435477
theorem B1914097 : Blo 1132632 1914097 := bstep (se 2 (by rfl) ⟨717786, by rfl⟩ : syracuseStep 1914097 = 1435573) B1435573
theorem B1914131 : Blo 1132632 1914131 := bstep (se 1 (by rfl) ⟨1435598, by rfl⟩ : syracuseStep 1914131 = 2871197) B2871197
theorem B6206797 : Blo 1132632 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B1815905 : Blo 1132632 1815905 := bstep (se 2 (by rfl) ⟨680964, by rfl⟩ : syracuseStep 1815905 = 1361929) B1361929
theorem B1914259 : Blo 1132632 1914259 := bstep (se 1 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 1914259 = 2871389) B2871389
theorem B1914401 : Blo 1132632 1914401 := bstep (se 2 (by rfl) ⟨717900, by rfl⟩ : syracuseStep 1914401 = 1435801) B1435801
theorem B1816129 : Blo 1132632 1816129 := bstep (se 2 (by rfl) ⟨681048, by rfl⟩ : syracuseStep 1816129 = 1362097) B1362097
theorem B1914529 : Blo 1132632 1914529 := bstep (se 2 (by rfl) ⟨717948, by rfl⟩ : syracuseStep 1914529 = 1435897) B1435897
theorem B1914563 : Blo 1132632 1914563 := bstep (se 1 (by rfl) ⟨1435922, by rfl⟩ : syracuseStep 1914563 = 2871845) B2871845
theorem B4601585 : Blo 1132632 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B27997973 : Blo 1132632 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1914691 : Blo 1132632 1914691 := bstep (se 1 (by rfl) ⟨1436018, by rfl⟩ : syracuseStep 1914691 = 2872037) B2872037
theorem B1914833 : Blo 1132632 1914833 := bstep (se 2 (by rfl) ⟨718062, by rfl⟩ : syracuseStep 1914833 = 1436125) B1436125
theorem B3880973 : Blo 1132632 3880973 := bstep (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) B1455365
theorem B6993989 : Blo 1132632 6993989 := bstep (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) B1311373
theorem B1914961 : Blo 1132632 1914961 := bstep (se 2 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 1914961 = 1436221) B1436221
theorem B1914995 : Blo 1132632 1914995 := bstep (se 1 (by rfl) ⟨1436246, by rfl⟩ : syracuseStep 1914995 = 2872493) B2872493
theorem B12925169 : Blo 1132632 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B1915123 : Blo 1132632 1915123 := bstep (se 1 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 1915123 = 2872685) B2872685
theorem B1915265 : Blo 1132632 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B1915393 : Blo 1132632 1915393 := bstep (se 2 (by rfl) ⟨718272, by rfl⟩ : syracuseStep 1915393 = 1436545) B1436545
theorem B1915427 : Blo 1132632 1915427 := bstep (se 1 (by rfl) ⟨1436570, by rfl⟩ : syracuseStep 1915427 = 2873141) B2873141
theorem B10500749 : Blo 1132632 10500749 := bstep (se 3 (by rfl) ⟨1968890, by rfl⟩ : syracuseStep 10500749 = 3937781) B3937781
theorem B5454499 : Blo 1132632 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B1915555 : Blo 1132632 1915555 := bstep (se 1 (by rfl) ⟨1436666, by rfl⟩ : syracuseStep 1915555 = 2873333) B2873333
theorem B1915697 : Blo 1132632 1915697 := bstep (se 2 (by rfl) ⟨718386, by rfl⟩ : syracuseStep 1915697 = 1436773) B1436773
theorem B6470513 : Blo 1132632 6470513 := bstep (se 2 (by rfl) ⟨2426442, by rfl⟩ : syracuseStep 6470513 = 4852885) B4852885
theorem B1915825 : Blo 1132632 1915825 := bstep (se 2 (by rfl) ⟨718434, by rfl⟩ : syracuseStep 1915825 = 1436869) B1436869
theorem B1915859 : Blo 1132632 1915859 := bstep (se 1 (by rfl) ⟨1436894, by rfl⟩ : syracuseStep 1915859 = 2873789) B2873789
theorem B7257059 : Blo 1132632 7257059 := bstep (se 1 (by rfl) ⟨5442794, by rfl⟩ : syracuseStep 7257059 = 10885589) B10885589
theorem B1457203 : Blo 1132632 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B3226691 : Blo 1132632 3226691 := bstep (se 1 (by rfl) ⟨2420018, by rfl⟩ : syracuseStep 3226691 = 4840037) B4840037
theorem B1915987 : Blo 1132632 1915987 := bstep (se 1 (by rfl) ⟨1436990, by rfl⟩ : syracuseStep 1915987 = 2873981) B2873981
theorem B1817731 : Blo 1132632 1817731 := bstep (se 1 (by rfl) ⟨1363298, by rfl⟩ : syracuseStep 1817731 = 2726597) B2726597
theorem B1916129 : Blo 1132632 1916129 := bstep (se 2 (by rfl) ⟨718548, by rfl⟩ : syracuseStep 1916129 = 1437097) B1437097
theorem B13090061 : Blo 1132632 13090061 := bstep (se 3 (by rfl) ⟨2454386, by rfl⟩ : syracuseStep 13090061 = 4908773) B4908773
theorem B1916257 : Blo 1132632 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B1916291 : Blo 1132632 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B3882467 : Blo 1132632 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B1916419 : Blo 1132632 1916419 := bstep (se 1 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 1916419 = 2874629) B2874629
theorem B6897221 : Blo 1132632 6897221 := bstep (se 4 (by rfl) ⟨646614, by rfl⟩ : syracuseStep 6897221 = 1293229) B1293229
theorem B1916561 : Blo 1132632 1916561 := bstep (se 2 (by rfl) ⟨718710, by rfl⟩ : syracuseStep 1916561 = 1437421) B1437421
theorem B1294051 : Blo 1132632 1294051 := bstep (se 1 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 1294051 = 1941077) B1941077
theorem B5750513 : Blo 1132632 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B1916689 : Blo 1132632 1916689 := bstep (se 2 (by rfl) ⟨718758, by rfl⟩ : syracuseStep 1916689 = 1437517) B1437517
theorem B4308785 : Blo 1132632 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B1916723 : Blo 1132632 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B1916851 : Blo 1132632 1916851 := bstep (se 1 (by rfl) ⟨1437638, by rfl⟩ : syracuseStep 1916851 = 2875277) B2875277
theorem B46612421 : Blo 1132632 46612421 := bstep (se 4 (by rfl) ⟨4369914, by rfl⟩ : syracuseStep 46612421 = 8739829) B8739829
theorem B1916993 : Blo 1132632 1916993 := bstep (se 2 (by rfl) ⟨718872, by rfl⟩ : syracuseStep 1916993 = 1437745) B1437745
theorem B3063917 : Blo 1132632 3063917 := bstep (se 3 (by rfl) ⟨574484, by rfl⟩ : syracuseStep 3063917 = 1148969) B1148969
theorem B8601713 : Blo 1132632 8601713 := bstep (se 2 (by rfl) ⟨3225642, by rfl⟩ : syracuseStep 8601713 = 6451285) B6451285
theorem B1917121 : Blo 1132632 1917121 := bstep (se 2 (by rfl) ⟨718920, by rfl⟩ : syracuseStep 1917121 = 1437841) B1437841
theorem B1917155 : Blo 1132632 1917155 := bstep (se 1 (by rfl) ⟨1437866, by rfl⟩ : syracuseStep 1917155 = 2875733) B2875733
theorem B3227921 : Blo 1132632 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B6471971 : Blo 1132632 6471971 := bstep (se 1 (by rfl) ⟨4853978, by rfl⟩ : syracuseStep 6471971 = 9707957) B9707957
theorem B1917283 : Blo 1132632 1917283 := bstep (se 1 (by rfl) ⟨1437962, by rfl⟩ : syracuseStep 1917283 = 2875925) B2875925
theorem B3064177 : Blo 1132632 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B2867633 : Blo 1132632 2867633 := bstep (se 2 (by rfl) ⟨1075362, by rfl⟩ : syracuseStep 2867633 = 2150725) B2150725
theorem B2867683 : Blo 1132632 2867683 := bstep (se 1 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 2867683 = 4301525) B4301525
theorem B8176099 : Blo 1132632 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B1917425 : Blo 1132632 1917425 := bstep (se 2 (by rfl) ⟨719034, by rfl⟩ : syracuseStep 1917425 = 1438069) B1438069
theorem B37274165 : Blo 1132632 37274165 := bstep (se 5 (by rfl) ⟨1747226, by rfl⟩ : syracuseStep 37274165 = 3494453) B3494453
theorem B1819217 : Blo 1132632 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B2867825 : Blo 1132632 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B5456497 : Blo 1132632 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B1917553 : Blo 1132632 1917553 := bstep (se 2 (by rfl) ⟨719082, by rfl⟩ : syracuseStep 1917553 = 1438165) B1438165
theorem B1917587 : Blo 1132632 1917587 := bstep (se 1 (by rfl) ⟨1438190, by rfl⟩ : syracuseStep 1917587 = 2876381) B2876381
theorem B1819345 : Blo 1132632 1819345 := bstep (se 2 (by rfl) ⟨682254, by rfl⟩ : syracuseStep 1819345 = 1364509) B1364509
theorem B1917715 : Blo 1132632 1917715 := bstep (se 1 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 1917715 = 2876573) B2876573
theorem B29868821 : Blo 1132632 29868821 := bstep (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) B1400101
theorem B1917857 : Blo 1132632 1917857 := bstep (se 2 (by rfl) ⟨719196, by rfl⟩ : syracuseStep 1917857 = 1438393) B1438393
theorem B1360867 : Blo 1132632 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1917985 : Blo 1132632 1917985 := bstep (se 2 (by rfl) ⟨719244, by rfl⟩ : syracuseStep 1917985 = 1438489) B1438489
theorem B1918019 : Blo 1132632 1918019 := bstep (se 1 (by rfl) ⟨1438514, by rfl⟩ : syracuseStep 1918019 = 2877029) B2877029
theorem B5751971 : Blo 1132632 5751971 := bstep (se 1 (by rfl) ⟨4313978, by rfl⟩ : syracuseStep 5751971 = 8627957) B8627957
theorem B4310243 : Blo 1132632 4310243 := bstep (se 1 (by rfl) ⟨3232682, by rfl⟩ : syracuseStep 4310243 = 6465365) B6465365
theorem B6472973 : Blo 1132632 6472973 := bstep (se 3 (by rfl) ⟨1213682, by rfl⟩ : syracuseStep 6472973 = 2427365) B2427365
theorem B1361395 : Blo 1132632 1361395 := bstep (se 1 (by rfl) ⟨1021046, by rfl⟩ : syracuseStep 1361395 = 2042093) B2042093
theorem B2868817 : Blo 1132632 2868817 := bstep (se 2 (by rfl) ⟨1075806, by rfl⟩ : syracuseStep 2868817 = 2151613) B2151613
theorem B1361491 : Blo 1132632 1361491 := bstep (se 1 (by rfl) ⟨1021118, by rfl⟩ : syracuseStep 1361491 = 2042237) B2042237
theorem B3229379 : Blo 1132632 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B5457613 : Blo 1132632 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B2869091 : Blo 1132632 2869091 := bstep (se 1 (by rfl) ⟨2151818, by rfl⟩ : syracuseStep 2869091 = 4303637) B4303637
theorem B3884995 : Blo 1132632 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B5752781 : Blo 1132632 5752781 := bstep (se 3 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 5752781 = 2157293) B2157293
theorem B1820627 : Blo 1132632 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B2869283 : Blo 1132632 2869283 := bstep (se 1 (by rfl) ⟨2151962, by rfl⟩ : syracuseStep 2869283 = 4303925) B4303925
theorem B1132643 : Blo 1132632 1132643 := bstep (se 1 (by rfl) ⟨849482, by rfl⟩ : syracuseStep 1132643 = 1698965) B1698965
theorem B1132659 : Blo 1132632 1132659 := bstep (se 1 (by rfl) ⟨849494, by rfl⟩ : syracuseStep 1132659 = 1698989) B1698989
theorem B1132675 : Blo 1132632 1132675 := bstep (se 1 (by rfl) ⟨849506, by rfl⟩ : syracuseStep 1132675 = 1699013) B1699013
theorem B1132691 : Blo 1132632 1132691 := bstep (se 1 (by rfl) ⟨849518, by rfl⟩ : syracuseStep 1132691 = 1699037) B1699037
theorem B1132707 : Blo 1132632 1132707 := bstep (se 1 (by rfl) ⟨849530, by rfl⟩ : syracuseStep 1132707 = 1699061) B1699061
theorem B1132723 : Blo 1132632 1132723 := bstep (se 1 (by rfl) ⟨849542, by rfl⟩ : syracuseStep 1132723 = 1699085) B1699085
theorem B1132739 : Blo 1132632 1132739 := bstep (se 1 (by rfl) ⟨849554, by rfl⟩ : syracuseStep 1132739 = 1699109) B1699109
theorem B4311245 : Blo 1132632 4311245 := bstep (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) B1616717
theorem B1132755 : Blo 1132632 1132755 := bstep (se 1 (by rfl) ⟨849566, by rfl⟩ : syracuseStep 1132755 = 1699133) B1699133
theorem B1132771 : Blo 1132632 1132771 := bstep (se 1 (by rfl) ⟨849578, by rfl⟩ : syracuseStep 1132771 = 1699157) B1699157
theorem B1132787 : Blo 1132632 1132787 := bstep (se 1 (by rfl) ⟨849590, by rfl⟩ : syracuseStep 1132787 = 1699181) B1699181
theorem B1132803 : Blo 1132632 1132803 := bstep (se 1 (by rfl) ⟨849602, by rfl⟩ : syracuseStep 1132803 = 1699205) B1699205
theorem B1132819 : Blo 1132632 1132819 := bstep (se 1 (by rfl) ⟨849614, by rfl⟩ : syracuseStep 1132819 = 1699229) B1699229
theorem B1132835 : Blo 1132632 1132835 := bstep (se 1 (by rfl) ⟨849626, by rfl⟩ : syracuseStep 1132835 = 1699253) B1699253
theorem B1132851 : Blo 1132632 1132851 := bstep (se 1 (by rfl) ⟨849638, by rfl⟩ : syracuseStep 1132851 = 1699277) B1699277
theorem B1132867 : Blo 1132632 1132867 := bstep (se 1 (by rfl) ⟨849650, by rfl⟩ : syracuseStep 1132867 = 1699301) B1699301
theorem B1132883 : Blo 1132632 1132883 := bstep (se 1 (by rfl) ⟨849662, by rfl⟩ : syracuseStep 1132883 = 1699325) B1699325
theorem B1132899 : Blo 1132632 1132899 := bstep (se 1 (by rfl) ⟨849674, by rfl⟩ : syracuseStep 1132899 = 1699349) B1699349
theorem B1132915 : Blo 1132632 1132915 := bstep (se 1 (by rfl) ⟨849686, by rfl⟩ : syracuseStep 1132915 = 1699373) B1699373
theorem B1132931 : Blo 1132632 1132931 := bstep (se 1 (by rfl) ⟨849698, by rfl⟩ : syracuseStep 1132931 = 1699397) B1699397
theorem B1132947 : Blo 1132632 1132947 := bstep (se 1 (by rfl) ⟨849710, by rfl⟩ : syracuseStep 1132947 = 1699421) B1699421
theorem B1132963 : Blo 1132632 1132963 := bstep (se 1 (by rfl) ⟨849722, by rfl⟩ : syracuseStep 1132963 = 1699445) B1699445
theorem B1132979 : Blo 1132632 1132979 := bstep (se 1 (by rfl) ⟨849734, by rfl⟩ : syracuseStep 1132979 = 1699469) B1699469
theorem B1132995 : Blo 1132632 1132995 := bstep (se 1 (by rfl) ⟨849746, by rfl⟩ : syracuseStep 1132995 = 1699493) B1699493
theorem B1133011 : Blo 1132632 1133011 := bstep (se 1 (by rfl) ⟨849758, by rfl⟩ : syracuseStep 1133011 = 1699517) B1699517
theorem B1133027 : Blo 1132632 1133027 := bstep (se 1 (by rfl) ⟨849770, by rfl⟩ : syracuseStep 1133027 = 1699541) B1699541
theorem B3230189 : Blo 1132632 3230189 := bstep (se 3 (by rfl) ⟨605660, by rfl⟩ : syracuseStep 3230189 = 1211321) B1211321
theorem B1133043 : Blo 1132632 1133043 := bstep (se 1 (by rfl) ⟨849782, by rfl⟩ : syracuseStep 1133043 = 1699565) B1699565
theorem B1133059 : Blo 1132632 1133059 := bstep (se 1 (by rfl) ⟨849794, by rfl⟩ : syracuseStep 1133059 = 1699589) B1699589
theorem B1133075 : Blo 1132632 1133075 := bstep (se 1 (by rfl) ⟨849806, by rfl⟩ : syracuseStep 1133075 = 1699613) B1699613
theorem B1133091 : Blo 1132632 1133091 := bstep (se 1 (by rfl) ⟨849818, by rfl⟩ : syracuseStep 1133091 = 1699637) B1699637
theorem B1362467 : Blo 1132632 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B1133107 : Blo 1132632 1133107 := bstep (se 1 (by rfl) ⟨849830, by rfl⟩ : syracuseStep 1133107 = 1699661) B1699661
theorem B1133123 : Blo 1132632 1133123 := bstep (se 1 (by rfl) ⟨849842, by rfl⟩ : syracuseStep 1133123 = 1699685) B1699685
theorem B7260749 : Blo 1132632 7260749 := bstep (se 3 (by rfl) ⟨1361390, by rfl⟩ : syracuseStep 7260749 = 2722781) B2722781
theorem B1133139 : Blo 1132632 1133139 := bstep (se 1 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 1133139 = 1699709) B1699709
theorem B1133155 : Blo 1132632 1133155 := bstep (se 1 (by rfl) ⟨849866, by rfl⟩ : syracuseStep 1133155 = 1699733) B1699733
theorem B1133171 : Blo 1132632 1133171 := bstep (se 1 (by rfl) ⟨849878, by rfl⟩ : syracuseStep 1133171 = 1699757) B1699757
theorem B1133187 : Blo 1132632 1133187 := bstep (se 1 (by rfl) ⟨849890, by rfl⟩ : syracuseStep 1133187 = 1699781) B1699781
theorem B1133203 : Blo 1132632 1133203 := bstep (se 1 (by rfl) ⟨849902, by rfl⟩ : syracuseStep 1133203 = 1699805) B1699805
theorem B1133219 : Blo 1132632 1133219 := bstep (se 1 (by rfl) ⟨849914, by rfl⟩ : syracuseStep 1133219 = 1699829) B1699829
theorem B3230381 : Blo 1132632 3230381 := bstep (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) B1211393
theorem B1133235 : Blo 1132632 1133235 := bstep (se 1 (by rfl) ⟨849926, by rfl⟩ : syracuseStep 1133235 = 1699853) B1699853
theorem B1133251 : Blo 1132632 1133251 := bstep (se 1 (by rfl) ⟨849938, by rfl⟩ : syracuseStep 1133251 = 1699877) B1699877
theorem B1133267 : Blo 1132632 1133267 := bstep (se 1 (by rfl) ⟨849950, by rfl⟩ : syracuseStep 1133267 = 1699901) B1699901
theorem B1133283 : Blo 1132632 1133283 := bstep (se 1 (by rfl) ⟨849962, by rfl⟩ : syracuseStep 1133283 = 1699925) B1699925
theorem B1133299 : Blo 1132632 1133299 := bstep (se 1 (by rfl) ⟨849974, by rfl⟩ : syracuseStep 1133299 = 1699949) B1699949
theorem B1133315 : Blo 1132632 1133315 := bstep (se 1 (by rfl) ⟨849986, by rfl⟩ : syracuseStep 1133315 = 1699973) B1699973
theorem B1133331 : Blo 1132632 1133331 := bstep (se 1 (by rfl) ⟨849998, by rfl⟩ : syracuseStep 1133331 = 1699997) B1699997
theorem B1133347 : Blo 1132632 1133347 := bstep (se 1 (by rfl) ⟨850010, by rfl⟩ : syracuseStep 1133347 = 1700021) B1700021
theorem B7260977 : Blo 1132632 7260977 := bstep (se 2 (by rfl) ⟨2722866, by rfl⟩ : syracuseStep 7260977 = 5445733) B5445733
theorem B1133363 : Blo 1132632 1133363 := bstep (se 1 (by rfl) ⟨850022, by rfl⟩ : syracuseStep 1133363 = 1700045) B1700045
theorem B1133379 : Blo 1132632 1133379 := bstep (se 1 (by rfl) ⟨850034, by rfl⟩ : syracuseStep 1133379 = 1700069) B1700069
theorem B1133395 : Blo 1132632 1133395 := bstep (se 1 (by rfl) ⟨850046, by rfl⟩ : syracuseStep 1133395 = 1700093) B1700093
theorem B1133411 : Blo 1132632 1133411 := bstep (se 1 (by rfl) ⟨850058, by rfl⟩ : syracuseStep 1133411 = 1700117) B1700117
theorem B1133427 : Blo 1132632 1133427 := bstep (se 1 (by rfl) ⟨850070, by rfl⟩ : syracuseStep 1133427 = 1700141) B1700141
theorem B1133443 : Blo 1132632 1133443 := bstep (se 1 (by rfl) ⟨850082, by rfl⟩ : syracuseStep 1133443 = 1700165) B1700165
theorem B1133459 : Blo 1132632 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B1133475 : Blo 1132632 1133475 := bstep (se 1 (by rfl) ⟨850106, by rfl⟩ : syracuseStep 1133475 = 1700213) B1700213
theorem B1133491 : Blo 1132632 1133491 := bstep (se 1 (by rfl) ⟨850118, by rfl⟩ : syracuseStep 1133491 = 1700237) B1700237
theorem B1133507 : Blo 1132632 1133507 := bstep (se 1 (by rfl) ⟨850130, by rfl⟩ : syracuseStep 1133507 = 1700261) B1700261
theorem B2870225 : Blo 1132632 2870225 := bstep (se 2 (by rfl) ⟨1076334, by rfl⟩ : syracuseStep 2870225 = 2152669) B2152669
theorem B1133523 : Blo 1132632 1133523 := bstep (se 1 (by rfl) ⟨850142, by rfl⟩ : syracuseStep 1133523 = 1700285) B1700285
theorem B13781987 : Blo 1132632 13781987 := bstep (se 1 (by rfl) ⟨10336490, by rfl⟩ : syracuseStep 13781987 = 20672981) B20672981
theorem B1133539 : Blo 1132632 1133539 := bstep (se 1 (by rfl) ⟨850154, by rfl⟩ : syracuseStep 1133539 = 1700309) B1700309
theorem B1133555 : Blo 1132632 1133555 := bstep (se 1 (by rfl) ⟨850166, by rfl⟩ : syracuseStep 1133555 = 1700333) B1700333
theorem B1133571 : Blo 1132632 1133571 := bstep (se 1 (by rfl) ⟨850178, by rfl⟩ : syracuseStep 1133571 = 1700357) B1700357
theorem B2870275 : Blo 1132632 2870275 := bstep (se 1 (by rfl) ⟨2152706, by rfl⟩ : syracuseStep 2870275 = 4305413) B4305413
theorem B1133587 : Blo 1132632 1133587 := bstep (se 1 (by rfl) ⟨850190, by rfl⟩ : syracuseStep 1133587 = 1700381) B1700381
theorem B1133603 : Blo 1132632 1133603 := bstep (se 1 (by rfl) ⟨850202, by rfl⟩ : syracuseStep 1133603 = 1700405) B1700405
theorem B1133619 : Blo 1132632 1133619 := bstep (se 1 (by rfl) ⟨850214, by rfl⟩ : syracuseStep 1133619 = 1700429) B1700429
theorem B1133635 : Blo 1132632 1133635 := bstep (se 1 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 1133635 = 1700453) B1700453
theorem B1133651 : Blo 1132632 1133651 := bstep (se 1 (by rfl) ⟨850238, by rfl⟩ : syracuseStep 1133651 = 1700477) B1700477
theorem B1133667 : Blo 1132632 1133667 := bstep (se 1 (by rfl) ⟨850250, by rfl⟩ : syracuseStep 1133667 = 1700501) B1700501
theorem B1133683 : Blo 1132632 1133683 := bstep (se 1 (by rfl) ⟨850262, by rfl⟩ : syracuseStep 1133683 = 1700525) B1700525
theorem B1133699 : Blo 1132632 1133699 := bstep (se 1 (by rfl) ⟨850274, by rfl⟩ : syracuseStep 1133699 = 1700549) B1700549
theorem B2870417 : Blo 1132632 2870417 := bstep (se 2 (by rfl) ⟨1076406, by rfl⟩ : syracuseStep 2870417 = 2152813) B2152813
theorem B1133715 : Blo 1132632 1133715 := bstep (se 1 (by rfl) ⟨850286, by rfl⟩ : syracuseStep 1133715 = 1700573) B1700573
theorem B1133731 : Blo 1132632 1133731 := bstep (se 1 (by rfl) ⟨850298, by rfl⟩ : syracuseStep 1133731 = 1700597) B1700597
theorem B1133747 : Blo 1132632 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B1133763 : Blo 1132632 1133763 := bstep (se 1 (by rfl) ⟨850322, by rfl⟩ : syracuseStep 1133763 = 1700645) B1700645
theorem B1133779 : Blo 1132632 1133779 := bstep (se 1 (by rfl) ⟨850334, by rfl⟩ : syracuseStep 1133779 = 1700669) B1700669
theorem B1133795 : Blo 1132632 1133795 := bstep (se 1 (by rfl) ⟨850346, by rfl⟩ : syracuseStep 1133795 = 1700693) B1700693
theorem B1133811 : Blo 1132632 1133811 := bstep (se 1 (by rfl) ⟨850358, by rfl⟩ : syracuseStep 1133811 = 1700717) B1700717
theorem B1133827 : Blo 1132632 1133827 := bstep (se 1 (by rfl) ⟨850370, by rfl⟩ : syracuseStep 1133827 = 1700741) B1700741
theorem B1133843 : Blo 1132632 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B29117717 : Blo 1132632 29117717 := bstep (se 6 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 29117717 = 1364893) B1364893
theorem B1133859 : Blo 1132632 1133859 := bstep (se 1 (by rfl) ⟨850394, by rfl⟩ : syracuseStep 1133859 = 1700789) B1700789
theorem B1133875 : Blo 1132632 1133875 := bstep (se 1 (by rfl) ⟨850406, by rfl⟩ : syracuseStep 1133875 = 1700813) B1700813
theorem B1133891 : Blo 1132632 1133891 := bstep (se 1 (by rfl) ⟨850418, by rfl⟩ : syracuseStep 1133891 = 1700837) B1700837
theorem B1133907 : Blo 1132632 1133907 := bstep (se 1 (by rfl) ⟨850430, by rfl⟩ : syracuseStep 1133907 = 1700861) B1700861
theorem B1133923 : Blo 1132632 1133923 := bstep (se 1 (by rfl) ⟨850442, by rfl⟩ : syracuseStep 1133923 = 1700885) B1700885
theorem B1133939 : Blo 1132632 1133939 := bstep (se 1 (by rfl) ⟨850454, by rfl⟩ : syracuseStep 1133939 = 1700909) B1700909
theorem B1133955 : Blo 1132632 1133955 := bstep (se 1 (by rfl) ⟨850466, by rfl⟩ : syracuseStep 1133955 = 1700933) B1700933
theorem B1133971 : Blo 1132632 1133971 := bstep (se 1 (by rfl) ⟨850478, by rfl⟩ : syracuseStep 1133971 = 1700957) B1700957
theorem B1133987 : Blo 1132632 1133987 := bstep (se 1 (by rfl) ⟨850490, by rfl⟩ : syracuseStep 1133987 = 1700981) B1700981
theorem B3067313 : Blo 1132632 3067313 := bstep (se 2 (by rfl) ⟨1150242, by rfl⟩ : syracuseStep 3067313 = 2300485) B2300485
theorem B1134003 : Blo 1132632 1134003 := bstep (se 1 (by rfl) ⟨850502, by rfl⟩ : syracuseStep 1134003 = 1701005) B1701005
theorem B1134019 : Blo 1132632 1134019 := bstep (se 1 (by rfl) ⟨850514, by rfl⟩ : syracuseStep 1134019 = 1701029) B1701029
theorem B1134035 : Blo 1132632 1134035 := bstep (se 1 (by rfl) ⟨850526, by rfl⟩ : syracuseStep 1134035 = 1701053) B1701053
theorem B1134051 : Blo 1132632 1134051 := bstep (se 1 (by rfl) ⟨850538, by rfl⟩ : syracuseStep 1134051 = 1701077) B1701077
theorem B1134067 : Blo 1132632 1134067 := bstep (se 1 (by rfl) ⟨850550, by rfl⟩ : syracuseStep 1134067 = 1701101) B1701101
theorem B1134083 : Blo 1132632 1134083 := bstep (se 1 (by rfl) ⟨850562, by rfl⟩ : syracuseStep 1134083 = 1701125) B1701125
theorem B1134099 : Blo 1132632 1134099 := bstep (se 1 (by rfl) ⟨850574, by rfl⟩ : syracuseStep 1134099 = 1701149) B1701149
theorem B1134115 : Blo 1132632 1134115 := bstep (se 1 (by rfl) ⟨850586, by rfl⟩ : syracuseStep 1134115 = 1701173) B1701173
theorem B1134131 : Blo 1132632 1134131 := bstep (se 1 (by rfl) ⟨850598, by rfl⟩ : syracuseStep 1134131 = 1701197) B1701197
theorem B1134147 : Blo 1132632 1134147 := bstep (se 1 (by rfl) ⟨850610, by rfl⟩ : syracuseStep 1134147 = 1701221) B1701221
theorem B1134163 : Blo 1132632 1134163 := bstep (se 1 (by rfl) ⟨850622, by rfl⟩ : syracuseStep 1134163 = 1701245) B1701245
theorem B1134179 : Blo 1132632 1134179 := bstep (se 1 (by rfl) ⟨850634, by rfl⟩ : syracuseStep 1134179 = 1701269) B1701269
theorem B1134195 : Blo 1132632 1134195 := bstep (se 1 (by rfl) ⟨850646, by rfl⟩ : syracuseStep 1134195 = 1701293) B1701293
theorem B1134211 : Blo 1132632 1134211 := bstep (se 1 (by rfl) ⟨850658, by rfl⟩ : syracuseStep 1134211 = 1701317) B1701317
theorem B3231373 : Blo 1132632 3231373 := bstep (se 3 (by rfl) ⟨605882, by rfl⟩ : syracuseStep 3231373 = 1211765) B1211765
theorem B1724051 : Blo 1132632 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B1134227 : Blo 1132632 1134227 := bstep (se 1 (by rfl) ⟨850670, by rfl⟩ : syracuseStep 1134227 = 1701341) B1701341
theorem B1134243 : Blo 1132632 1134243 := bstep (se 1 (by rfl) ⟨850682, by rfl⟩ : syracuseStep 1134243 = 1701365) B1701365
theorem B4083377 : Blo 1132632 4083377 := bstep (se 2 (by rfl) ⟨1531266, by rfl⟩ : syracuseStep 4083377 = 3062533) B3062533
theorem B1134259 : Blo 1132632 1134259 := bstep (se 1 (by rfl) ⟨850694, by rfl⟩ : syracuseStep 1134259 = 1701389) B1701389
theorem B1134275 : Blo 1132632 1134275 := bstep (se 1 (by rfl) ⟨850706, by rfl⟩ : syracuseStep 1134275 = 1701413) B1701413
theorem B1134291 : Blo 1132632 1134291 := bstep (se 1 (by rfl) ⟨850718, by rfl⟩ : syracuseStep 1134291 = 1701437) B1701437
theorem B1134307 : Blo 1132632 1134307 := bstep (se 1 (by rfl) ⟨850730, by rfl⟩ : syracuseStep 1134307 = 1701461) B1701461
theorem B1134323 : Blo 1132632 1134323 := bstep (se 1 (by rfl) ⟨850742, by rfl⟩ : syracuseStep 1134323 = 1701485) B1701485
theorem B1134339 : Blo 1132632 1134339 := bstep (se 1 (by rfl) ⟨850754, by rfl⟩ : syracuseStep 1134339 = 1701509) B1701509
theorem B1134355 : Blo 1132632 1134355 := bstep (se 1 (by rfl) ⟨850766, by rfl⟩ : syracuseStep 1134355 = 1701533) B1701533
theorem B1134371 : Blo 1132632 1134371 := bstep (se 1 (by rfl) ⟨850778, by rfl⟩ : syracuseStep 1134371 = 1701557) B1701557
theorem B1134387 : Blo 1132632 1134387 := bstep (se 1 (by rfl) ⟨850790, by rfl⟩ : syracuseStep 1134387 = 1701581) B1701581
theorem B1134403 : Blo 1132632 1134403 := bstep (se 1 (by rfl) ⟨850802, by rfl⟩ : syracuseStep 1134403 = 1701605) B1701605
theorem B1134419 : Blo 1132632 1134419 := bstep (se 1 (by rfl) ⟨850814, by rfl⟩ : syracuseStep 1134419 = 1701629) B1701629
theorem B1134435 : Blo 1132632 1134435 := bstep (se 1 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 1134435 = 1701653) B1701653
theorem B1134451 : Blo 1132632 1134451 := bstep (se 1 (by rfl) ⟨850838, by rfl⟩ : syracuseStep 1134451 = 1701677) B1701677
theorem B1134467 : Blo 1132632 1134467 := bstep (se 1 (by rfl) ⟨850850, by rfl⟩ : syracuseStep 1134467 = 1701701) B1701701
theorem B1134483 : Blo 1132632 1134483 := bstep (se 1 (by rfl) ⟨850862, by rfl⟩ : syracuseStep 1134483 = 1701725) B1701725
theorem B1134499 : Blo 1132632 1134499 := bstep (se 1 (by rfl) ⟨850874, by rfl⟩ : syracuseStep 1134499 = 1701749) B1701749
theorem B1134515 : Blo 1132632 1134515 := bstep (se 1 (by rfl) ⟨850886, by rfl⟩ : syracuseStep 1134515 = 1701773) B1701773
theorem B1134531 : Blo 1132632 1134531 := bstep (se 1 (by rfl) ⟨850898, by rfl⟩ : syracuseStep 1134531 = 1701797) B1701797
theorem B1134547 : Blo 1132632 1134547 := bstep (se 1 (by rfl) ⟨850910, by rfl⟩ : syracuseStep 1134547 = 1701821) B1701821
theorem B1134563 : Blo 1132632 1134563 := bstep (se 1 (by rfl) ⟨850922, by rfl⟩ : syracuseStep 1134563 = 1701845) B1701845
theorem B1134579 : Blo 1132632 1134579 := bstep (se 1 (by rfl) ⟨850934, by rfl⟩ : syracuseStep 1134579 = 1701869) B1701869
theorem B1134595 : Blo 1132632 1134595 := bstep (se 1 (by rfl) ⟨850946, by rfl⟩ : syracuseStep 1134595 = 1701893) B1701893
theorem B1134611 : Blo 1132632 1134611 := bstep (se 1 (by rfl) ⟨850958, by rfl⟩ : syracuseStep 1134611 = 1701917) B1701917
theorem B1134627 : Blo 1132632 1134627 := bstep (se 1 (by rfl) ⟨850970, by rfl⟩ : syracuseStep 1134627 = 1701941) B1701941
theorem B1134643 : Blo 1132632 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B1134659 : Blo 1132632 1134659 := bstep (se 1 (by rfl) ⟨850994, by rfl⟩ : syracuseStep 1134659 = 1701989) B1701989
theorem B3887185 : Blo 1132632 3887185 := bstep (se 2 (by rfl) ⟨1457694, by rfl⟩ : syracuseStep 3887185 = 2915389) B2915389
theorem B1134675 : Blo 1132632 1134675 := bstep (se 1 (by rfl) ⟨851006, by rfl⟩ : syracuseStep 1134675 = 1702013) B1702013
theorem B1134691 : Blo 1132632 1134691 := bstep (se 1 (by rfl) ⟨851018, by rfl⟩ : syracuseStep 1134691 = 1702037) B1702037
theorem B2871409 : Blo 1132632 2871409 := bstep (se 2 (by rfl) ⟨1076778, by rfl⟩ : syracuseStep 2871409 = 2153557) B2153557
theorem B1134707 : Blo 1132632 1134707 := bstep (se 1 (by rfl) ⟨851030, by rfl⟩ : syracuseStep 1134707 = 1702061) B1702061
theorem B1134723 : Blo 1132632 1134723 := bstep (se 1 (by rfl) ⟨851042, by rfl⟩ : syracuseStep 1134723 = 1702085) B1702085
theorem B1134739 : Blo 1132632 1134739 := bstep (se 1 (by rfl) ⟨851054, by rfl⟩ : syracuseStep 1134739 = 1702109) B1702109
theorem B1134755 : Blo 1132632 1134755 := bstep (se 1 (by rfl) ⟨851066, by rfl⟩ : syracuseStep 1134755 = 1702133) B1702133
theorem B1134771 : Blo 1132632 1134771 := bstep (se 1 (by rfl) ⟨851078, by rfl⟩ : syracuseStep 1134771 = 1702157) B1702157
theorem B1134787 : Blo 1132632 1134787 := bstep (se 1 (by rfl) ⟨851090, by rfl⟩ : syracuseStep 1134787 = 1702181) B1702181
theorem B1134803 : Blo 1132632 1134803 := bstep (se 1 (by rfl) ⟨851102, by rfl⟩ : syracuseStep 1134803 = 1702205) B1702205
theorem B1134819 : Blo 1132632 1134819 := bstep (se 1 (by rfl) ⟨851114, by rfl⟩ : syracuseStep 1134819 = 1702229) B1702229
theorem B2150641 : Blo 1132632 2150641 := bstep (se 2 (by rfl) ⟨806490, by rfl⟩ : syracuseStep 2150641 = 1612981) B1612981
theorem B1134835 : Blo 1132632 1134835 := bstep (se 1 (by rfl) ⟨851126, by rfl⟩ : syracuseStep 1134835 = 1702253) B1702253
theorem B1134851 : Blo 1132632 1134851 := bstep (se 1 (by rfl) ⟨851138, by rfl⟩ : syracuseStep 1134851 = 1702277) B1702277
theorem B4313357 : Blo 1132632 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B1134867 : Blo 1132632 1134867 := bstep (se 1 (by rfl) ⟨851150, by rfl⟩ : syracuseStep 1134867 = 1702301) B1702301
theorem B1134883 : Blo 1132632 1134883 := bstep (se 1 (by rfl) ⟨851162, by rfl⟩ : syracuseStep 1134883 = 1702325) B1702325
theorem B1134899 : Blo 1132632 1134899 := bstep (se 1 (by rfl) ⟨851174, by rfl⟩ : syracuseStep 1134899 = 1702349) B1702349
theorem B1134915 : Blo 1132632 1134915 := bstep (se 1 (by rfl) ⟨851186, by rfl⟩ : syracuseStep 1134915 = 1702373) B1702373
theorem B1134931 : Blo 1132632 1134931 := bstep (se 1 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 1134931 = 1702397) B1702397
theorem B1134947 : Blo 1132632 1134947 := bstep (se 1 (by rfl) ⟨851210, by rfl⟩ : syracuseStep 1134947 = 1702421) B1702421
theorem B1134963 : Blo 1132632 1134963 := bstep (se 1 (by rfl) ⟨851222, by rfl⟩ : syracuseStep 1134963 = 1702445) B1702445
theorem B2871683 : Blo 1132632 2871683 := bstep (se 1 (by rfl) ⟨2153762, by rfl⟩ : syracuseStep 2871683 = 4307525) B4307525
theorem B1134979 : Blo 1132632 1134979 := bstep (se 1 (by rfl) ⟨851234, by rfl⟩ : syracuseStep 1134979 = 1702469) B1702469
theorem B1134995 : Blo 1132632 1134995 := bstep (se 1 (by rfl) ⟨851246, by rfl⟩ : syracuseStep 1134995 = 1702493) B1702493
theorem B1135011 : Blo 1132632 1135011 := bstep (se 1 (by rfl) ⟨851258, by rfl⟩ : syracuseStep 1135011 = 1702517) B1702517
theorem B1135027 : Blo 1132632 1135027 := bstep (se 1 (by rfl) ⟨851270, by rfl⟩ : syracuseStep 1135027 = 1702541) B1702541
theorem B1135043 : Blo 1132632 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B1135059 : Blo 1132632 1135059 := bstep (se 1 (by rfl) ⟨851294, by rfl⟩ : syracuseStep 1135059 = 1702589) B1702589
theorem B1135075 : Blo 1132632 1135075 := bstep (se 1 (by rfl) ⟨851306, by rfl⟩ : syracuseStep 1135075 = 1702613) B1702613
theorem B1135091 : Blo 1132632 1135091 := bstep (se 1 (by rfl) ⟨851318, by rfl⟩ : syracuseStep 1135091 = 1702637) B1702637
theorem B1135107 : Blo 1132632 1135107 := bstep (se 1 (by rfl) ⟨851330, by rfl⟩ : syracuseStep 1135107 = 1702661) B1702661
theorem B1135123 : Blo 1132632 1135123 := bstep (se 1 (by rfl) ⟨851342, by rfl⟩ : syracuseStep 1135123 = 1702685) B1702685
theorem B1135139 : Blo 1132632 1135139 := bstep (se 1 (by rfl) ⟨851354, by rfl⟩ : syracuseStep 1135139 = 1702709) B1702709
theorem B1135155 : Blo 1132632 1135155 := bstep (se 1 (by rfl) ⟨851366, by rfl⟩ : syracuseStep 1135155 = 1702733) B1702733
theorem B2871875 : Blo 1132632 2871875 := bstep (se 1 (by rfl) ⟨2153906, by rfl⟩ : syracuseStep 2871875 = 4307813) B4307813
theorem B1135171 : Blo 1132632 1135171 := bstep (se 1 (by rfl) ⟨851378, by rfl⟩ : syracuseStep 1135171 = 1702757) B1702757
theorem B1135187 : Blo 1132632 1135187 := bstep (se 1 (by rfl) ⟨851390, by rfl⟩ : syracuseStep 1135187 = 1702781) B1702781
theorem B1135203 : Blo 1132632 1135203 := bstep (se 1 (by rfl) ⟨851402, by rfl⟩ : syracuseStep 1135203 = 1702805) B1702805
theorem B1135219 : Blo 1132632 1135219 := bstep (se 1 (by rfl) ⟨851414, by rfl⟩ : syracuseStep 1135219 = 1702829) B1702829
theorem B1135235 : Blo 1132632 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B1135251 : Blo 1132632 1135251 := bstep (se 1 (by rfl) ⟨851438, by rfl⟩ : syracuseStep 1135251 = 1702877) B1702877
theorem B1135267 : Blo 1132632 1135267 := bstep (se 1 (by rfl) ⟨851450, by rfl⟩ : syracuseStep 1135267 = 1702901) B1702901
theorem B1135283 : Blo 1132632 1135283 := bstep (se 1 (by rfl) ⟨851462, by rfl⟩ : syracuseStep 1135283 = 1702925) B1702925
theorem B1135299 : Blo 1132632 1135299 := bstep (se 1 (by rfl) ⟨851474, by rfl⟩ : syracuseStep 1135299 = 1702949) B1702949
theorem B1135315 : Blo 1132632 1135315 := bstep (se 1 (by rfl) ⟨851486, by rfl⟩ : syracuseStep 1135315 = 1702973) B1702973
theorem B1135331 : Blo 1132632 1135331 := bstep (se 1 (by rfl) ⟨851498, by rfl⟩ : syracuseStep 1135331 = 1702997) B1702997
theorem B1135347 : Blo 1132632 1135347 := bstep (se 1 (by rfl) ⟨851510, by rfl⟩ : syracuseStep 1135347 = 1703021) B1703021
theorem B1135363 : Blo 1132632 1135363 := bstep (se 1 (by rfl) ⟨851522, by rfl⟩ : syracuseStep 1135363 = 1703045) B1703045
theorem B3068675 : Blo 1132632 3068675 := bstep (se 1 (by rfl) ⟨2301506, by rfl⟩ : syracuseStep 3068675 = 4603013) B4603013
theorem B1135379 : Blo 1132632 1135379 := bstep (se 1 (by rfl) ⟨851534, by rfl⟩ : syracuseStep 1135379 = 1703069) B1703069
theorem B1135395 : Blo 1132632 1135395 := bstep (se 1 (by rfl) ⟨851546, by rfl⟩ : syracuseStep 1135395 = 1703093) B1703093
theorem B1135411 : Blo 1132632 1135411 := bstep (se 1 (by rfl) ⟨851558, by rfl⟩ : syracuseStep 1135411 = 1703117) B1703117
theorem B1135427 : Blo 1132632 1135427 := bstep (se 1 (by rfl) ⟨851570, by rfl⟩ : syracuseStep 1135427 = 1703141) B1703141
theorem B1135443 : Blo 1132632 1135443 := bstep (se 1 (by rfl) ⟨851582, by rfl⟩ : syracuseStep 1135443 = 1703165) B1703165
theorem B1135459 : Blo 1132632 1135459 := bstep (se 1 (by rfl) ⟨851594, by rfl⟩ : syracuseStep 1135459 = 1703189) B1703189
theorem B1135475 : Blo 1132632 1135475 := bstep (se 1 (by rfl) ⟨851606, by rfl⟩ : syracuseStep 1135475 = 1703213) B1703213
theorem B1135491 : Blo 1132632 1135491 := bstep (se 1 (by rfl) ⟨851618, by rfl⟩ : syracuseStep 1135491 = 1703237) B1703237
theorem B1135507 : Blo 1132632 1135507 := bstep (se 1 (by rfl) ⟨851630, by rfl⟩ : syracuseStep 1135507 = 1703261) B1703261
theorem B1135523 : Blo 1132632 1135523 := bstep (se 1 (by rfl) ⟨851642, by rfl⟩ : syracuseStep 1135523 = 1703285) B1703285
theorem B1135539 : Blo 1132632 1135539 := bstep (se 1 (by rfl) ⟨851654, by rfl⟩ : syracuseStep 1135539 = 1703309) B1703309
theorem B1135555 : Blo 1132632 1135555 := bstep (se 1 (by rfl) ⟨851666, by rfl⟩ : syracuseStep 1135555 = 1703333) B1703333
theorem B1135571 : Blo 1132632 1135571 := bstep (se 1 (by rfl) ⟨851678, by rfl⟩ : syracuseStep 1135571 = 1703357) B1703357
theorem B1135587 : Blo 1132632 1135587 := bstep (se 1 (by rfl) ⟨851690, by rfl⟩ : syracuseStep 1135587 = 1703381) B1703381
theorem B1135603 : Blo 1132632 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1135619 : Blo 1132632 1135619 := bstep (se 1 (by rfl) ⟨851714, by rfl⟩ : syracuseStep 1135619 = 1703429) B1703429
theorem B1135635 : Blo 1132632 1135635 := bstep (se 1 (by rfl) ⟨851726, by rfl⟩ : syracuseStep 1135635 = 1703453) B1703453
theorem B1725473 : Blo 1132632 1725473 := bstep (se 2 (by rfl) ⟨647052, by rfl⟩ : syracuseStep 1725473 = 1294105) B1294105
theorem B1135651 : Blo 1132632 1135651 := bstep (se 1 (by rfl) ⟨851738, by rfl⟩ : syracuseStep 1135651 = 1703477) B1703477
theorem B4314161 : Blo 1132632 4314161 := bstep (se 2 (by rfl) ⟨1617810, by rfl⟩ : syracuseStep 4314161 = 3235621) B3235621
theorem B1135667 : Blo 1132632 1135667 := bstep (se 1 (by rfl) ⟨851750, by rfl⟩ : syracuseStep 1135667 = 1703501) B1703501
theorem B3822659 : Blo 1132632 3822659 := bstep (se 1 (by rfl) ⟨2866994, by rfl⟩ : syracuseStep 3822659 = 5733989) B5733989
theorem B1135683 : Blo 1132632 1135683 := bstep (se 1 (by rfl) ⟨851762, by rfl⟩ : syracuseStep 1135683 = 1703525) B1703525
theorem B1135699 : Blo 1132632 1135699 := bstep (se 1 (by rfl) ⟨851774, by rfl⟩ : syracuseStep 1135699 = 1703549) B1703549
theorem B1135715 : Blo 1132632 1135715 := bstep (se 1 (by rfl) ⟨851786, by rfl⟩ : syracuseStep 1135715 = 1703573) B1703573
theorem B1135731 : Blo 1132632 1135731 := bstep (se 1 (by rfl) ⟨851798, by rfl⟩ : syracuseStep 1135731 = 1703597) B1703597
theorem B1135747 : Blo 1132632 1135747 := bstep (se 1 (by rfl) ⟨851810, by rfl⟩ : syracuseStep 1135747 = 1703621) B1703621
theorem B9196685 : Blo 1132632 9196685 := bstep (se 3 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 9196685 = 3448757) B3448757
theorem B1135763 : Blo 1132632 1135763 := bstep (se 1 (by rfl) ⟨851822, by rfl⟩ : syracuseStep 1135763 = 1703645) B1703645
theorem B1135779 : Blo 1132632 1135779 := bstep (se 1 (by rfl) ⟨851834, by rfl⟩ : syracuseStep 1135779 = 1703669) B1703669
theorem B1135795 : Blo 1132632 1135795 := bstep (se 1 (by rfl) ⟨851846, by rfl⟩ : syracuseStep 1135795 = 1703693) B1703693
theorem B1135811 : Blo 1132632 1135811 := bstep (se 1 (by rfl) ⟨851858, by rfl⟩ : syracuseStep 1135811 = 1703717) B1703717
theorem B1135827 : Blo 1132632 1135827 := bstep (se 1 (by rfl) ⟨851870, by rfl⟩ : syracuseStep 1135827 = 1703741) B1703741
theorem B1135843 : Blo 1132632 1135843 := bstep (se 1 (by rfl) ⟨851882, by rfl⟩ : syracuseStep 1135843 = 1703765) B1703765
theorem B1135859 : Blo 1132632 1135859 := bstep (se 1 (by rfl) ⟨851894, by rfl⟩ : syracuseStep 1135859 = 1703789) B1703789
theorem B1135875 : Blo 1132632 1135875 := bstep (se 1 (by rfl) ⟨851906, by rfl⟩ : syracuseStep 1135875 = 1703813) B1703813
theorem B2151697 : Blo 1132632 2151697 := bstep (se 2 (by rfl) ⟨806886, by rfl⟩ : syracuseStep 2151697 = 1613773) B1613773
theorem B1135891 : Blo 1132632 1135891 := bstep (se 1 (by rfl) ⟨851918, by rfl⟩ : syracuseStep 1135891 = 1703837) B1703837
theorem B1135907 : Blo 1132632 1135907 := bstep (se 1 (by rfl) ⟨851930, by rfl⟩ : syracuseStep 1135907 = 1703861) B1703861
theorem B1135923 : Blo 1132632 1135923 := bstep (se 1 (by rfl) ⟨851942, by rfl⟩ : syracuseStep 1135923 = 1703885) B1703885
theorem B1135939 : Blo 1132632 1135939 := bstep (se 1 (by rfl) ⟨851954, by rfl⟩ : syracuseStep 1135939 = 1703909) B1703909
theorem B3822929 : Blo 1132632 3822929 := bstep (se 2 (by rfl) ⟨1433598, by rfl⟩ : syracuseStep 3822929 = 2867197) B2867197
theorem B3233105 : Blo 1132632 3233105 := bstep (se 2 (by rfl) ⟨1212414, by rfl⟩ : syracuseStep 3233105 = 2424829) B2424829
theorem B1135955 : Blo 1132632 1135955 := bstep (se 1 (by rfl) ⟨851966, by rfl⟩ : syracuseStep 1135955 = 1703933) B1703933
theorem B1135971 : Blo 1132632 1135971 := bstep (se 1 (by rfl) ⟨851978, by rfl⟩ : syracuseStep 1135971 = 1703957) B1703957
theorem B1135987 : Blo 1132632 1135987 := bstep (se 1 (by rfl) ⟨851990, by rfl⟩ : syracuseStep 1135987 = 1703981) B1703981
theorem B1136003 : Blo 1132632 1136003 := bstep (se 1 (by rfl) ⟨852002, by rfl⟩ : syracuseStep 1136003 = 1704005) B1704005
theorem B1136019 : Blo 1132632 1136019 := bstep (se 1 (by rfl) ⟨852014, by rfl⟩ : syracuseStep 1136019 = 1704029) B1704029
theorem B1136035 : Blo 1132632 1136035 := bstep (se 1 (by rfl) ⟨852026, by rfl⟩ : syracuseStep 1136035 = 1704053) B1704053
theorem B1136051 : Blo 1132632 1136051 := bstep (se 1 (by rfl) ⟨852038, by rfl⟩ : syracuseStep 1136051 = 1704077) B1704077
theorem B1136067 : Blo 1132632 1136067 := bstep (se 1 (by rfl) ⟨852050, by rfl⟩ : syracuseStep 1136067 = 1704101) B1704101
theorem B1136083 : Blo 1132632 1136083 := bstep (se 1 (by rfl) ⟨852062, by rfl⟩ : syracuseStep 1136083 = 1704125) B1704125
theorem B7362019 : Blo 1132632 7362019 := bstep (se 1 (by rfl) ⟨5521514, by rfl⟩ : syracuseStep 7362019 = 11043029) B11043029
theorem B1136099 : Blo 1132632 1136099 := bstep (se 1 (by rfl) ⟨852074, by rfl⟩ : syracuseStep 1136099 = 1704149) B1704149
theorem B2872817 : Blo 1132632 2872817 := bstep (se 2 (by rfl) ⟨1077306, by rfl⟩ : syracuseStep 2872817 = 2154613) B2154613
theorem B1136115 : Blo 1132632 1136115 := bstep (se 1 (by rfl) ⟨852086, by rfl⟩ : syracuseStep 1136115 = 1704173) B1704173
theorem B1136131 : Blo 1132632 1136131 := bstep (se 1 (by rfl) ⟨852098, by rfl⟩ : syracuseStep 1136131 = 1704197) B1704197
theorem B3233297 : Blo 1132632 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B1136147 : Blo 1132632 1136147 := bstep (se 1 (by rfl) ⟨852110, by rfl⟩ : syracuseStep 1136147 = 1704221) B1704221
theorem B2872867 : Blo 1132632 2872867 := bstep (se 1 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 2872867 = 4309301) B4309301
theorem B1136163 : Blo 1132632 1136163 := bstep (se 1 (by rfl) ⟨852122, by rfl⟩ : syracuseStep 1136163 = 1704245) B1704245
theorem B1136179 : Blo 1132632 1136179 := bstep (se 1 (by rfl) ⟨852134, by rfl⟩ : syracuseStep 1136179 = 1704269) B1704269
theorem B1136195 : Blo 1132632 1136195 := bstep (se 1 (by rfl) ⟨852146, by rfl⟩ : syracuseStep 1136195 = 1704293) B1704293
theorem B1136211 : Blo 1132632 1136211 := bstep (se 1 (by rfl) ⟨852158, by rfl⟩ : syracuseStep 1136211 = 1704317) B1704317
theorem B4839011 : Blo 1132632 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B1136227 : Blo 1132632 1136227 := bstep (se 1 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 1136227 = 1704341) B1704341
theorem B1136243 : Blo 1132632 1136243 := bstep (se 1 (by rfl) ⟨852182, by rfl⟩ : syracuseStep 1136243 = 1704365) B1704365
theorem B1136259 : Blo 1132632 1136259 := bstep (se 1 (by rfl) ⟨852194, by rfl⟩ : syracuseStep 1136259 = 1704389) B1704389
theorem B1136275 : Blo 1132632 1136275 := bstep (se 1 (by rfl) ⟨852206, by rfl⟩ : syracuseStep 1136275 = 1704413) B1704413
theorem B2152099 : Blo 1132632 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1136291 : Blo 1132632 1136291 := bstep (se 1 (by rfl) ⟨852218, by rfl⟩ : syracuseStep 1136291 = 1704437) B1704437
theorem B2873009 : Blo 1132632 2873009 := bstep (se 2 (by rfl) ⟨1077378, by rfl⟩ : syracuseStep 2873009 = 2154757) B2154757
theorem B1136307 : Blo 1132632 1136307 := bstep (se 1 (by rfl) ⟨852230, by rfl⟩ : syracuseStep 1136307 = 1704461) B1704461
theorem B1136323 : Blo 1132632 1136323 := bstep (se 1 (by rfl) ⟨852242, by rfl⟩ : syracuseStep 1136323 = 1704485) B1704485
theorem B4314829 : Blo 1132632 4314829 := bstep (se 3 (by rfl) ⟨809030, by rfl⟩ : syracuseStep 4314829 = 1618061) B1618061
theorem B2152145 : Blo 1132632 2152145 := bstep (se 2 (by rfl) ⟨807054, by rfl⟩ : syracuseStep 2152145 = 1614109) B1614109
theorem B1136339 : Blo 1132632 1136339 := bstep (se 1 (by rfl) ⟨852254, by rfl⟩ : syracuseStep 1136339 = 1704509) B1704509
theorem B1136355 : Blo 1132632 1136355 := bstep (se 1 (by rfl) ⟨852266, by rfl⟩ : syracuseStep 1136355 = 1704533) B1704533
theorem B1136371 : Blo 1132632 1136371 := bstep (se 1 (by rfl) ⟨852278, by rfl⟩ : syracuseStep 1136371 = 1704557) B1704557
theorem B1136387 : Blo 1132632 1136387 := bstep (se 1 (by rfl) ⟨852290, by rfl⟩ : syracuseStep 1136387 = 1704581) B1704581
theorem B3069713 : Blo 1132632 3069713 := bstep (se 2 (by rfl) ⟨1151142, by rfl⟩ : syracuseStep 3069713 = 2302285) B2302285
theorem B1136403 : Blo 1132632 1136403 := bstep (se 1 (by rfl) ⟨852302, by rfl⟩ : syracuseStep 1136403 = 1704605) B1704605
theorem B1136419 : Blo 1132632 1136419 := bstep (se 1 (by rfl) ⟨852314, by rfl⟩ : syracuseStep 1136419 = 1704629) B1704629
theorem B1136435 : Blo 1132632 1136435 := bstep (se 1 (by rfl) ⟨852326, by rfl⟩ : syracuseStep 1136435 = 1704653) B1704653
theorem B1136451 : Blo 1132632 1136451 := bstep (se 1 (by rfl) ⟨852338, by rfl⟩ : syracuseStep 1136451 = 1704677) B1704677
theorem B1136467 : Blo 1132632 1136467 := bstep (se 1 (by rfl) ⟨852350, by rfl⟩ : syracuseStep 1136467 = 1704701) B1704701
theorem B13817699 : Blo 1132632 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B1136483 : Blo 1132632 1136483 := bstep (se 1 (by rfl) ⟨852362, by rfl⟩ : syracuseStep 1136483 = 1704725) B1704725
theorem B3823469 : Blo 1132632 3823469 := bstep (se 3 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 3823469 = 1433801) B1433801
theorem B1136499 : Blo 1132632 1136499 := bstep (se 1 (by rfl) ⟨852374, by rfl⟩ : syracuseStep 1136499 = 1704749) B1704749
theorem B1136515 : Blo 1132632 1136515 := bstep (se 1 (by rfl) ⟨852386, by rfl⟩ : syracuseStep 1136515 = 1704773) B1704773
theorem B1136531 : Blo 1132632 1136531 := bstep (se 1 (by rfl) ⟨852398, by rfl⟩ : syracuseStep 1136531 = 1704797) B1704797
theorem B3823523 : Blo 1132632 3823523 := bstep (se 1 (by rfl) ⟨2867642, by rfl⟩ : syracuseStep 3823523 = 5735285) B5735285
theorem B1136547 : Blo 1132632 1136547 := bstep (se 1 (by rfl) ⟨852410, by rfl⟩ : syracuseStep 1136547 = 1704821) B1704821
theorem B1136563 : Blo 1132632 1136563 := bstep (se 1 (by rfl) ⟨852422, by rfl⟩ : syracuseStep 1136563 = 1704845) B1704845
theorem B1136579 : Blo 1132632 1136579 := bstep (se 1 (by rfl) ⟨852434, by rfl⟩ : syracuseStep 1136579 = 1704869) B1704869
theorem B1136595 : Blo 1132632 1136595 := bstep (se 1 (by rfl) ⟨852446, by rfl⟩ : syracuseStep 1136595 = 1704893) B1704893
theorem B1136611 : Blo 1132632 1136611 := bstep (se 1 (by rfl) ⟨852458, by rfl⟩ : syracuseStep 1136611 = 1704917) B1704917
theorem B2152433 : Blo 1132632 2152433 := bstep (se 2 (by rfl) ⟨807162, by rfl⟩ : syracuseStep 2152433 = 1614325) B1614325
theorem B1136627 : Blo 1132632 1136627 := bstep (se 1 (by rfl) ⟨852470, by rfl⟩ : syracuseStep 1136627 = 1704941) B1704941
theorem B3823793 : Blo 1132632 3823793 := bstep (se 2 (by rfl) ⟨1433922, by rfl⟩ : syracuseStep 3823793 = 2867845) B2867845
theorem B4315619 : Blo 1132632 4315619 := bstep (se 1 (by rfl) ⟨3236714, by rfl⟩ : syracuseStep 4315619 = 6473429) B6473429
theorem B3234289 : Blo 1132632 3234289 := bstep (se 2 (by rfl) ⟨1212858, by rfl⟩ : syracuseStep 3234289 = 2425717) B2425717
theorem B2874001 : Blo 1132632 2874001 := bstep (se 2 (by rfl) ⟨1077750, by rfl⟩ : syracuseStep 2874001 = 2155501) B2155501
theorem B2153155 : Blo 1132632 2153155 := bstep (se 1 (by rfl) ⟨1614866, by rfl⟩ : syracuseStep 2153155 = 3229733) B3229733
theorem B3824333 : Blo 1132632 3824333 := bstep (se 3 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 3824333 = 1434125) B1434125
theorem B3824387 : Blo 1132632 3824387 := bstep (se 1 (by rfl) ⟨2868290, by rfl⟩ : syracuseStep 3824387 = 5736581) B5736581
theorem B3234563 : Blo 1132632 3234563 := bstep (se 1 (by rfl) ⟨2425922, by rfl⟩ : syracuseStep 3234563 = 4851845) B4851845
theorem B1727249 : Blo 1132632 1727249 := bstep (se 2 (by rfl) ⟨647718, by rfl⟩ : syracuseStep 1727249 = 1295437) B1295437
theorem B2874275 : Blo 1132632 2874275 := bstep (se 1 (by rfl) ⟨2155706, by rfl⟩ : syracuseStep 2874275 = 4311413) B4311413
theorem B3234755 : Blo 1132632 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B3070925 : Blo 1132632 3070925 := bstep (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) B1151597
theorem B3824657 : Blo 1132632 3824657 := bstep (se 2 (by rfl) ⟨1434246, by rfl⟩ : syracuseStep 3824657 = 2868493) B2868493
theorem B2874467 : Blo 1132632 2874467 := bstep (se 1 (by rfl) ⟨2155850, by rfl⟩ : syracuseStep 2874467 = 4311701) B4311701
theorem B2153603 : Blo 1132632 2153603 := bstep (se 1 (by rfl) ⟨1615202, by rfl⟩ : syracuseStep 2153603 = 3230405) B3230405
theorem B1531105 : Blo 1132632 1531105 := bstep (se 2 (by rfl) ⟨574164, by rfl⟩ : syracuseStep 1531105 = 1148329) B1148329
theorem B6905101 : Blo 1132632 6905101 := bstep (se 3 (by rfl) ⟨1294706, by rfl⟩ : syracuseStep 6905101 = 2589413) B2589413
theorem B1531219 : Blo 1132632 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B2153891 : Blo 1132632 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B3825197 : Blo 1132632 3825197 := bstep (se 3 (by rfl) ⟨717224, by rfl⟩ : syracuseStep 3825197 = 1434449) B1434449
theorem B3628643 : Blo 1132632 3628643 := bstep (se 1 (by rfl) ⟨2721482, by rfl⟩ : syracuseStep 3628643 = 5442965) B5442965
theorem B3825251 : Blo 1132632 3825251 := bstep (se 1 (by rfl) ⟨2868938, by rfl⟩ : syracuseStep 3825251 = 5737877) B5737877
theorem B1531505 : Blo 1132632 1531505 := bstep (se 2 (by rfl) ⟨574314, by rfl⟩ : syracuseStep 1531505 = 1148629) B1148629
theorem B3235565 : Blo 1132632 3235565 := bstep (se 3 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 3235565 = 1213337) B1213337
theorem B1531667 : Blo 1132632 1531667 := bstep (se 1 (by rfl) ⟨1148750, by rfl⟩ : syracuseStep 1531667 = 2297501) B2297501
theorem B3825521 : Blo 1132632 3825521 := bstep (se 2 (by rfl) ⟨1434570, by rfl⟩ : syracuseStep 3825521 = 2869141) B2869141
theorem B3235747 : Blo 1132632 3235747 := bstep (se 1 (by rfl) ⟨2426810, by rfl⟩ : syracuseStep 3235747 = 4853621) B4853621
theorem B2875409 : Blo 1132632 2875409 := bstep (se 2 (by rfl) ⟨1078278, by rfl⟩ : syracuseStep 2875409 = 2156557) B2156557
theorem B27648053 : Blo 1132632 27648053 := bstep (se 5 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 27648053 = 2592005) B2592005
theorem B2875459 : Blo 1132632 2875459 := bstep (se 1 (by rfl) ⟨2156594, by rfl⟩ : syracuseStep 2875459 = 4313189) B4313189
theorem B12247109 : Blo 1132632 12247109 := bstep (se 4 (by rfl) ⟨1148166, by rfl⟩ : syracuseStep 12247109 = 2296333) B2296333
theorem B4087907 : Blo 1132632 4087907 := bstep (se 1 (by rfl) ⟨3065930, by rfl⟩ : syracuseStep 4087907 = 6131861) B6131861
theorem B6545585 : Blo 1132632 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B2875601 : Blo 1132632 2875601 := bstep (se 2 (by rfl) ⟨1078350, by rfl⟩ : syracuseStep 2875601 = 2156701) B2156701
theorem B2154833 : Blo 1132632 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B3826061 : Blo 1132632 3826061 := bstep (se 3 (by rfl) ⟨717386, by rfl⟩ : syracuseStep 3826061 = 1434773) B1434773
theorem B3236237 : Blo 1132632 3236237 := bstep (se 3 (by rfl) ⟨606794, by rfl⟩ : syracuseStep 3236237 = 1213589) B1213589
theorem B1532305 : Blo 1132632 1532305 := bstep (se 2 (by rfl) ⟨574614, by rfl⟩ : syracuseStep 1532305 = 1149229) B1149229
theorem B1434019 : Blo 1132632 1434019 := bstep (se 1 (by rfl) ⟨1075514, by rfl⟩ : syracuseStep 1434019 = 2151029) B2151029
theorem B3826115 : Blo 1132632 3826115 := bstep (se 1 (by rfl) ⟨2869586, by rfl⟩ : syracuseStep 3826115 = 5739173) B5739173
theorem B1434115 : Blo 1132632 1434115 := bstep (se 1 (by rfl) ⟨1075586, by rfl⟩ : syracuseStep 1434115 = 2151173) B2151173
theorem B15753781 : Blo 1132632 15753781 := bstep (se 5 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 15753781 = 1476917) B1476917
theorem B3826385 : Blo 1132632 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B2548529 : Blo 1132632 2548529 := bstep (se 2 (by rfl) ⟨955698, by rfl⟩ : syracuseStep 2548529 = 1911397) B1911397
theorem B1532737 : Blo 1132632 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B2548547 : Blo 1132632 2548547 := bstep (se 1 (by rfl) ⟨1911410, by rfl⟩ : syracuseStep 2548547 = 3822821) B3822821
theorem B1434611 : Blo 1132632 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B7267333 : Blo 1132632 7267333 := bstep (se 4 (by rfl) ⟨681312, by rfl⟩ : syracuseStep 7267333 = 1362625) B1362625
theorem B2548817 : Blo 1132632 2548817 := bstep (se 2 (by rfl) ⟨955806, by rfl⟩ : syracuseStep 2548817 = 1911613) B1911613
theorem B2548835 : Blo 1132632 2548835 := bstep (se 1 (by rfl) ⟨1911626, by rfl⟩ : syracuseStep 2548835 = 3823253) B3823253
theorem B2876593 : Blo 1132632 2876593 := bstep (se 2 (by rfl) ⟨1078722, by rfl⟩ : syracuseStep 2876593 = 2157445) B2157445
theorem B2155729 : Blo 1132632 2155729 := bstep (se 2 (by rfl) ⟨808398, by rfl⟩ : syracuseStep 2155729 = 1616797) B1616797
theorem B3826925 : Blo 1132632 3826925 := bstep (se 3 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 3826925 = 1435097) B1435097
theorem B4842737 : Blo 1132632 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3826979 : Blo 1132632 3826979 := bstep (se 1 (by rfl) ⟨2870234, by rfl⟩ : syracuseStep 3826979 = 5740469) B5740469
theorem B3630413 : Blo 1132632 3630413 := bstep (se 3 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 3630413 = 1361405) B1361405
theorem B2549105 : Blo 1132632 2549105 := bstep (se 2 (by rfl) ⟨955914, by rfl⟩ : syracuseStep 2549105 = 1911829) B1911829
theorem B2155889 : Blo 1132632 2155889 := bstep (se 2 (by rfl) ⟨808458, by rfl⟩ : syracuseStep 2155889 = 1616917) B1616917
theorem B2549123 : Blo 1132632 2549123 := bstep (se 1 (by rfl) ⟨1911842, by rfl⟩ : syracuseStep 2549123 = 3823685) B3823685
theorem B2876867 : Blo 1132632 2876867 := bstep (se 1 (by rfl) ⟨2157650, by rfl⟩ : syracuseStep 2876867 = 4315301) B4315301
theorem B3630541 : Blo 1132632 3630541 := bstep (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) B1361453
theorem B3827249 : Blo 1132632 3827249 := bstep (se 2 (by rfl) ⟨1435218, by rfl⟩ : syracuseStep 3827249 = 2870437) B2870437
theorem B37774961 : Blo 1132632 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B2877059 : Blo 1132632 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B2549393 : Blo 1132632 2549393 := bstep (se 2 (by rfl) ⟨956022, by rfl⟩ : syracuseStep 2549393 = 1912045) B1912045
theorem B2549411 : Blo 1132632 2549411 := bstep (se 1 (by rfl) ⟨1912058, by rfl⟩ : syracuseStep 2549411 = 3824117) B3824117
theorem B1435315 : Blo 1132632 1435315 := bstep (se 1 (by rfl) ⟨1076486, by rfl⟩ : syracuseStep 1435315 = 2152973) B2152973
theorem B3630797 : Blo 1132632 3630797 := bstep (se 3 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 3630797 = 1361549) B1361549
theorem B2156291 : Blo 1132632 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B1435411 : Blo 1132632 1435411 := bstep (se 1 (by rfl) ⟨1076558, by rfl⟩ : syracuseStep 1435411 = 2153117) B2153117
theorem B2549681 : Blo 1132632 2549681 := bstep (se 2 (by rfl) ⟨956130, by rfl⟩ : syracuseStep 2549681 = 1912261) B1912261
theorem B2549699 : Blo 1132632 2549699 := bstep (se 1 (by rfl) ⟨1912274, by rfl⟩ : syracuseStep 2549699 = 3824549) B3824549
theorem B7759813 : Blo 1132632 7759813 := bstep (se 4 (by rfl) ⟨727482, by rfl⟩ : syracuseStep 7759813 = 1454965) B1454965
theorem B3106883 : Blo 1132632 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B3827789 : Blo 1132632 3827789 := bstep (se 3 (by rfl) ⟨717710, by rfl⟩ : syracuseStep 3827789 = 1435421) B1435421
theorem B3827843 : Blo 1132632 3827843 := bstep (se 1 (by rfl) ⟨2870882, by rfl⟩ : syracuseStep 3827843 = 5741765) B5741765
theorem B2549969 : Blo 1132632 2549969 := bstep (se 2 (by rfl) ⟨956238, by rfl⟩ : syracuseStep 2549969 = 1912477) B1912477
theorem B2549987 : Blo 1132632 2549987 := bstep (se 1 (by rfl) ⟨1912490, by rfl⟩ : syracuseStep 2549987 = 3824981) B3824981
theorem B9824483 : Blo 1132632 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B1435907 : Blo 1132632 1435907 := bstep (se 1 (by rfl) ⟨1076930, by rfl⟩ : syracuseStep 1435907 = 2153861) B2153861
theorem B12904757 : Blo 1132632 12904757 := bstep (se 5 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 12904757 = 1209821) B1209821
theorem B3828113 : Blo 1132632 3828113 := bstep (se 2 (by rfl) ⟨1435542, by rfl⟩ : syracuseStep 3828113 = 2871085) B2871085
theorem B1534403 : Blo 1132632 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B2550257 : Blo 1132632 2550257 := bstep (se 2 (by rfl) ⟨956346, by rfl⟩ : syracuseStep 2550257 = 1912693) B1912693
theorem B2550275 : Blo 1132632 2550275 := bstep (se 1 (by rfl) ⟨1912706, by rfl⟩ : syracuseStep 2550275 = 3825413) B3825413
theorem B5171747 : Blo 1132632 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B2419267 : Blo 1132632 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B2157187 : Blo 1132632 2157187 := bstep (se 1 (by rfl) ⟨1617890, by rfl⟩ : syracuseStep 2157187 = 3235781) B3235781
theorem B2550545 : Blo 1132632 2550545 := bstep (se 2 (by rfl) ⟨956454, by rfl⟩ : syracuseStep 2550545 = 1912909) B1912909
theorem B2550563 : Blo 1132632 2550563 := bstep (se 1 (by rfl) ⟨1912922, by rfl⟩ : syracuseStep 2550563 = 3825845) B3825845
theorem B2157347 : Blo 1132632 2157347 := bstep (se 1 (by rfl) ⟨1618010, by rfl⟩ : syracuseStep 2157347 = 3236021) B3236021
theorem B3107729 : Blo 1132632 3107729 := bstep (se 2 (by rfl) ⟨1165398, by rfl⟩ : syracuseStep 3107729 = 2330797) B2330797
theorem B3828653 : Blo 1132632 3828653 := bstep (se 3 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 3828653 = 1435745) B1435745
theorem B1436611 : Blo 1132632 1436611 := bstep (se 1 (by rfl) ⟨1077458, by rfl⟩ : syracuseStep 1436611 = 2154917) B2154917
theorem B3828707 : Blo 1132632 3828707 := bstep (se 1 (by rfl) ⟨2871530, by rfl⟩ : syracuseStep 3828707 = 5743061) B5743061
theorem B2583569 : Blo 1132632 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B1436707 : Blo 1132632 1436707 := bstep (se 1 (by rfl) ⟨1077530, by rfl⟩ : syracuseStep 1436707 = 2155061) B2155061
theorem B2550833 : Blo 1132632 2550833 := bstep (se 2 (by rfl) ⟨956562, by rfl⟩ : syracuseStep 2550833 = 1913125) B1913125
theorem B1535041 : Blo 1132632 1535041 := bstep (se 2 (by rfl) ⟨575640, by rfl⟩ : syracuseStep 1535041 = 1151281) B1151281
theorem B2550851 : Blo 1132632 2550851 := bstep (se 1 (by rfl) ⟨1913138, by rfl⟩ : syracuseStep 2550851 = 3826277) B3826277
theorem B1698977 : Blo 1132632 1698977 := bstep (se 2 (by rfl) ⟨637116, by rfl⟩ : syracuseStep 1698977 = 1274233) B1274233
theorem B5827747 : Blo 1132632 5827747 := bstep (se 1 (by rfl) ⟨4370810, by rfl⟩ : syracuseStep 5827747 = 8741621) B8741621
theorem B1698995 : Blo 1132632 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B3632323 : Blo 1132632 3632323 := bstep (se 1 (by rfl) ⟨2724242, by rfl⟩ : syracuseStep 3632323 = 5448485) B5448485
theorem B1699025 : Blo 1132632 1699025 := bstep (se 2 (by rfl) ⟨637134, by rfl⟩ : syracuseStep 1699025 = 1274269) B1274269
theorem B1699043 : Blo 1132632 1699043 := bstep (se 1 (by rfl) ⟨1274282, by rfl⟩ : syracuseStep 1699043 = 2548565) B2548565
theorem B3828977 : Blo 1132632 3828977 := bstep (se 2 (by rfl) ⟨1435866, by rfl⟩ : syracuseStep 3828977 = 2871733) B2871733
theorem B1699073 : Blo 1132632 1699073 := bstep (se 2 (by rfl) ⟨637152, by rfl⟩ : syracuseStep 1699073 = 1274305) B1274305
theorem B1699091 : Blo 1132632 1699091 := bstep (se 1 (by rfl) ⟨1274318, by rfl⟩ : syracuseStep 1699091 = 2548637) B2548637
theorem B44231957 : Blo 1132632 44231957 := bstep (se 6 (by rfl) ⟨1036686, by rfl⟩ : syracuseStep 44231957 = 2073373) B2073373
theorem B1699121 : Blo 1132632 1699121 := bstep (se 2 (by rfl) ⟨637170, by rfl⟩ : syracuseStep 1699121 = 1274341) B1274341
theorem B1699139 : Blo 1132632 1699139 := bstep (se 1 (by rfl) ⟨1274354, by rfl⟩ : syracuseStep 1699139 = 2548709) B2548709
theorem B2551121 : Blo 1132632 2551121 := bstep (se 2 (by rfl) ⟨956670, by rfl⟩ : syracuseStep 2551121 = 1913341) B1913341
theorem B1699169 : Blo 1132632 1699169 := bstep (se 2 (by rfl) ⟨637188, by rfl⟩ : syracuseStep 1699169 = 1274377) B1274377
theorem B2551139 : Blo 1132632 2551139 := bstep (se 1 (by rfl) ⟨1913354, by rfl⟩ : syracuseStep 2551139 = 3826709) B3826709
theorem B1699187 : Blo 1132632 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B1699217 : Blo 1132632 1699217 := bstep (se 2 (by rfl) ⟨637206, by rfl⟩ : syracuseStep 1699217 = 1274413) B1274413
theorem B2420113 : Blo 1132632 2420113 := bstep (se 2 (by rfl) ⟨907542, by rfl⟩ : syracuseStep 2420113 = 1815085) B1815085
theorem B1699235 : Blo 1132632 1699235 := bstep (se 1 (by rfl) ⟨1274426, by rfl⟩ : syracuseStep 1699235 = 2548853) B2548853
theorem B1699265 : Blo 1132632 1699265 := bstep (se 2 (by rfl) ⟨637224, by rfl⟩ : syracuseStep 1699265 = 1274449) B1274449
theorem B2911697 : Blo 1132632 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B1535441 : Blo 1132632 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1699283 : Blo 1132632 1699283 := bstep (se 1 (by rfl) ⟨1274462, by rfl⟩ : syracuseStep 1699283 = 2548925) B2548925
theorem B1699313 : Blo 1132632 1699313 := bstep (se 2 (by rfl) ⟨637242, by rfl⟩ : syracuseStep 1699313 = 1274485) B1274485
theorem B1699331 : Blo 1132632 1699331 := bstep (se 1 (by rfl) ⟨1274498, by rfl⟩ : syracuseStep 1699331 = 2548997) B2548997
theorem B1437203 : Blo 1132632 1437203 := bstep (se 1 (by rfl) ⟨1077902, by rfl⟩ : syracuseStep 1437203 = 2155805) B2155805
theorem B1699361 : Blo 1132632 1699361 := bstep (se 2 (by rfl) ⟨637260, by rfl⟩ : syracuseStep 1699361 = 1274521) B1274521
theorem B1699379 : Blo 1132632 1699379 := bstep (se 1 (by rfl) ⟨1274534, by rfl⟩ : syracuseStep 1699379 = 2549069) B2549069
theorem B1699409 : Blo 1132632 1699409 := bstep (se 2 (by rfl) ⟨637278, by rfl⟩ : syracuseStep 1699409 = 1274557) B1274557
theorem B1699427 : Blo 1132632 1699427 := bstep (se 1 (by rfl) ⟨1274570, by rfl⟩ : syracuseStep 1699427 = 2549141) B2549141
theorem B2551409 : Blo 1132632 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B1699457 : Blo 1132632 1699457 := bstep (se 2 (by rfl) ⟨637296, by rfl⟩ : syracuseStep 1699457 = 1274593) B1274593
theorem B2551427 : Blo 1132632 2551427 := bstep (se 1 (by rfl) ⟨1913570, by rfl⟩ : syracuseStep 2551427 = 3827141) B3827141
theorem B4845197 : Blo 1132632 4845197 := bstep (se 3 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 4845197 = 1816949) B1816949
theorem B1699475 : Blo 1132632 1699475 := bstep (se 1 (by rfl) ⟨1274606, by rfl⟩ : syracuseStep 1699475 = 2549213) B2549213
theorem B1699505 : Blo 1132632 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B1699523 : Blo 1132632 1699523 := bstep (se 1 (by rfl) ⟨1274642, by rfl⟩ : syracuseStep 1699523 = 2549285) B2549285
theorem B4091597 : Blo 1132632 4091597 := bstep (se 3 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 4091597 = 1534349) B1534349
theorem B1699553 : Blo 1132632 1699553 := bstep (se 2 (by rfl) ⟨637332, by rfl⟩ : syracuseStep 1699553 = 1274665) B1274665
theorem B8744689 : Blo 1132632 8744689 := bstep (se 2 (by rfl) ⟨3279258, by rfl⟩ : syracuseStep 8744689 = 6558517) B6558517
theorem B1699571 : Blo 1132632 1699571 := bstep (se 1 (by rfl) ⟨1274678, by rfl⟩ : syracuseStep 1699571 = 2549357) B2549357
theorem B3829517 : Blo 1132632 3829517 := bstep (se 3 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 3829517 = 1436069) B1436069
theorem B1699601 : Blo 1132632 1699601 := bstep (se 2 (by rfl) ⟨637350, by rfl⟩ : syracuseStep 1699601 = 1274701) B1274701
theorem B1699619 : Blo 1132632 1699619 := bstep (se 1 (by rfl) ⟨1274714, by rfl⟩ : syracuseStep 1699619 = 2549429) B2549429
theorem B1699649 : Blo 1132632 1699649 := bstep (se 2 (by rfl) ⟨637368, by rfl⟩ : syracuseStep 1699649 = 1274737) B1274737
theorem B3829571 : Blo 1132632 3829571 := bstep (se 1 (by rfl) ⟨2872178, by rfl⟩ : syracuseStep 3829571 = 5744357) B5744357
theorem B1699667 : Blo 1132632 1699667 := bstep (se 1 (by rfl) ⟨1274750, by rfl⟩ : syracuseStep 1699667 = 2549501) B2549501
theorem B1699697 : Blo 1132632 1699697 := bstep (se 2 (by rfl) ⟨637386, by rfl⟩ : syracuseStep 1699697 = 1274773) B1274773
theorem B1699715 : Blo 1132632 1699715 := bstep (se 1 (by rfl) ⟨1274786, by rfl⟩ : syracuseStep 1699715 = 2549573) B2549573
theorem B2551697 : Blo 1132632 2551697 := bstep (se 2 (by rfl) ⟨956886, by rfl⟩ : syracuseStep 2551697 = 1913773) B1913773
theorem B1699745 : Blo 1132632 1699745 := bstep (se 2 (by rfl) ⟨637404, by rfl⟩ : syracuseStep 1699745 = 1274809) B1274809
theorem B2551715 : Blo 1132632 2551715 := bstep (se 1 (by rfl) ⟨1913786, by rfl⟩ : syracuseStep 2551715 = 3827573) B3827573
theorem B7270307 : Blo 1132632 7270307 := bstep (se 1 (by rfl) ⟨5452730, by rfl⟩ : syracuseStep 7270307 = 10905461) B10905461
theorem B1699763 : Blo 1132632 1699763 := bstep (se 1 (by rfl) ⟨1274822, by rfl⟩ : syracuseStep 1699763 = 2549645) B2549645
theorem B7761869 : Blo 1132632 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B1699793 : Blo 1132632 1699793 := bstep (se 2 (by rfl) ⟨637422, by rfl⟩ : syracuseStep 1699793 = 1274845) B1274845
theorem B1699811 : Blo 1132632 1699811 := bstep (se 1 (by rfl) ⟨1274858, by rfl⟩ : syracuseStep 1699811 = 2549717) B2549717
theorem B1699841 : Blo 1132632 1699841 := bstep (se 2 (by rfl) ⟨637440, by rfl⟩ : syracuseStep 1699841 = 1274881) B1274881
theorem B1699859 : Blo 1132632 1699859 := bstep (se 1 (by rfl) ⟨1274894, by rfl⟩ : syracuseStep 1699859 = 2549789) B2549789
theorem B1699889 : Blo 1132632 1699889 := bstep (se 2 (by rfl) ⟨637458, by rfl⟩ : syracuseStep 1699889 = 1274917) B1274917
theorem B1699907 : Blo 1132632 1699907 := bstep (se 1 (by rfl) ⟨1274930, by rfl⟩ : syracuseStep 1699907 = 2549861) B2549861
theorem B3829841 : Blo 1132632 3829841 := bstep (se 2 (by rfl) ⟨1436190, by rfl⟩ : syracuseStep 3829841 = 2872381) B2872381
theorem B1699937 : Blo 1132632 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B1699955 : Blo 1132632 1699955 := bstep (se 1 (by rfl) ⟨1274966, by rfl⟩ : syracuseStep 1699955 = 2549933) B2549933
theorem B1699985 : Blo 1132632 1699985 := bstep (se 2 (by rfl) ⟨637494, by rfl⟩ : syracuseStep 1699985 = 1274989) B1274989
theorem B1700003 : Blo 1132632 1700003 := bstep (se 1 (by rfl) ⟨1275002, by rfl⟩ : syracuseStep 1700003 = 2550005) B2550005
theorem B2551985 : Blo 1132632 2551985 := bstep (se 2 (by rfl) ⟨956994, by rfl⟩ : syracuseStep 2551985 = 1913989) B1913989
theorem B1700033 : Blo 1132632 1700033 := bstep (se 2 (by rfl) ⟨637512, by rfl⟩ : syracuseStep 1700033 = 1275025) B1275025
theorem B2552003 : Blo 1132632 2552003 := bstep (se 1 (by rfl) ⟨1914002, by rfl⟩ : syracuseStep 2552003 = 3828005) B3828005
theorem B1700051 : Blo 1132632 1700051 := bstep (se 1 (by rfl) ⟨1275038, by rfl⟩ : syracuseStep 1700051 = 2550077) B2550077
theorem B1437907 : Blo 1132632 1437907 := bstep (se 1 (by rfl) ⟨1078430, by rfl⟩ : syracuseStep 1437907 = 2156861) B2156861
theorem B1700081 : Blo 1132632 1700081 := bstep (se 2 (by rfl) ⟨637530, by rfl⟩ : syracuseStep 1700081 = 1275061) B1275061
theorem B1700099 : Blo 1132632 1700099 := bstep (se 1 (by rfl) ⟨1275074, by rfl⟩ : syracuseStep 1700099 = 2550149) B2550149
theorem B1700129 : Blo 1132632 1700129 := bstep (se 2 (by rfl) ⟨637548, by rfl⟩ : syracuseStep 1700129 = 1275097) B1275097
theorem B1700147 : Blo 1132632 1700147 := bstep (se 1 (by rfl) ⟨1275110, by rfl⟩ : syracuseStep 1700147 = 2550221) B2550221
theorem B1438003 : Blo 1132632 1438003 := bstep (se 1 (by rfl) ⟨1078502, by rfl⟩ : syracuseStep 1438003 = 2157005) B2157005
theorem B1700177 : Blo 1132632 1700177 := bstep (se 2 (by rfl) ⟨637566, by rfl⟩ : syracuseStep 1700177 = 1275133) B1275133
theorem B1700195 : Blo 1132632 1700195 := bstep (se 1 (by rfl) ⟨1275146, by rfl⟩ : syracuseStep 1700195 = 2550293) B2550293
theorem B1700225 : Blo 1132632 1700225 := bstep (se 2 (by rfl) ⟨637584, by rfl⟩ : syracuseStep 1700225 = 1275169) B1275169
theorem B1700243 : Blo 1132632 1700243 := bstep (se 1 (by rfl) ⟨1275182, by rfl⟩ : syracuseStep 1700243 = 2550365) B2550365
theorem B1700273 : Blo 1132632 1700273 := bstep (se 2 (by rfl) ⟨637602, by rfl⟩ : syracuseStep 1700273 = 1275205) B1275205
theorem B1700291 : Blo 1132632 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B2552273 : Blo 1132632 2552273 := bstep (se 2 (by rfl) ⟨957102, by rfl⟩ : syracuseStep 2552273 = 1914205) B1914205
theorem B1274323 : Blo 1132632 1274323 := bstep (se 1 (by rfl) ⟨955742, by rfl⟩ : syracuseStep 1274323 = 1911485) B1911485
theorem B1700321 : Blo 1132632 1700321 := bstep (se 2 (by rfl) ⟨637620, by rfl⟩ : syracuseStep 1700321 = 1275241) B1275241
theorem B2552291 : Blo 1132632 2552291 := bstep (se 1 (by rfl) ⟨1914218, by rfl⟩ : syracuseStep 2552291 = 3828437) B3828437
theorem B1700339 : Blo 1132632 1700339 := bstep (se 1 (by rfl) ⟨1275254, by rfl⟩ : syracuseStep 1700339 = 2550509) B2550509
theorem B1700369 : Blo 1132632 1700369 := bstep (se 2 (by rfl) ⟨637638, by rfl⟩ : syracuseStep 1700369 = 1275277) B1275277
theorem B3109393 : Blo 1132632 3109393 := bstep (se 2 (by rfl) ⟨1166022, by rfl⟩ : syracuseStep 3109393 = 2332045) B2332045
theorem B1700387 : Blo 1132632 1700387 := bstep (se 1 (by rfl) ⟨1275290, by rfl⟩ : syracuseStep 1700387 = 2550581) B2550581
theorem B1700417 : Blo 1132632 1700417 := bstep (se 2 (by rfl) ⟨637656, by rfl⟩ : syracuseStep 1700417 = 1275313) B1275313
theorem B1700435 : Blo 1132632 1700435 := bstep (se 1 (by rfl) ⟨1275326, by rfl⟩ : syracuseStep 1700435 = 2550653) B2550653
theorem B6451811 : Blo 1132632 6451811 := bstep (se 1 (by rfl) ⟨4838858, by rfl⟩ : syracuseStep 6451811 = 9677717) B9677717
theorem B1274467 : Blo 1132632 1274467 := bstep (se 1 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 1274467 = 1911701) B1911701
theorem B3830381 : Blo 1132632 3830381 := bstep (se 3 (by rfl) ⟨718196, by rfl⟩ : syracuseStep 3830381 = 1436393) B1436393
theorem B1700465 : Blo 1132632 1700465 := bstep (se 2 (by rfl) ⟨637674, by rfl⟩ : syracuseStep 1700465 = 1275349) B1275349
theorem B1700483 : Blo 1132632 1700483 := bstep (se 1 (by rfl) ⟨1275362, by rfl⟩ : syracuseStep 1700483 = 2550725) B2550725
theorem B1700513 : Blo 1132632 1700513 := bstep (se 2 (by rfl) ⟨637692, by rfl⟩ : syracuseStep 1700513 = 1275385) B1275385
theorem B3830435 : Blo 1132632 3830435 := bstep (se 1 (by rfl) ⟨2872826, by rfl⟩ : syracuseStep 3830435 = 5745653) B5745653
theorem B1700531 : Blo 1132632 1700531 := bstep (se 1 (by rfl) ⟨1275398, by rfl⟩ : syracuseStep 1700531 = 2550797) B2550797
theorem B1700561 : Blo 1132632 1700561 := bstep (se 2 (by rfl) ⟨637710, by rfl⟩ : syracuseStep 1700561 = 1275421) B1275421
theorem B1700579 : Blo 1132632 1700579 := bstep (se 1 (by rfl) ⟨1275434, by rfl⟩ : syracuseStep 1700579 = 2550869) B2550869
theorem B2552561 : Blo 1132632 2552561 := bstep (se 2 (by rfl) ⟨957210, by rfl⟩ : syracuseStep 2552561 = 1914421) B1914421
theorem B1274611 : Blo 1132632 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B1700609 : Blo 1132632 1700609 := bstep (se 2 (by rfl) ⟨637728, by rfl⟩ : syracuseStep 1700609 = 1275457) B1275457
theorem B3633923 : Blo 1132632 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B2552579 : Blo 1132632 2552579 := bstep (se 1 (by rfl) ⟨1914434, by rfl⟩ : syracuseStep 2552579 = 3828869) B3828869
theorem B1700627 : Blo 1132632 1700627 := bstep (se 1 (by rfl) ⟨1275470, by rfl⟩ : syracuseStep 1700627 = 2550941) B2550941
theorem B1438499 : Blo 1132632 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B1700657 : Blo 1132632 1700657 := bstep (se 2 (by rfl) ⟨637746, by rfl⟩ : syracuseStep 1700657 = 1275493) B1275493
theorem B1700675 : Blo 1132632 1700675 := bstep (se 1 (by rfl) ⟨1275506, by rfl⟩ : syracuseStep 1700675 = 2551013) B2551013
theorem B1700705 : Blo 1132632 1700705 := bstep (se 2 (by rfl) ⟨637764, by rfl⟩ : syracuseStep 1700705 = 1275529) B1275529
theorem B1700723 : Blo 1132632 1700723 := bstep (se 1 (by rfl) ⟨1275542, by rfl⟩ : syracuseStep 1700723 = 2551085) B2551085
theorem B1274755 : Blo 1132632 1274755 := bstep (se 1 (by rfl) ⟨956066, by rfl⟩ : syracuseStep 1274755 = 1912133) B1912133
theorem B1700753 : Blo 1132632 1700753 := bstep (se 2 (by rfl) ⟨637782, by rfl⟩ : syracuseStep 1700753 = 1275565) B1275565
theorem B1700771 : Blo 1132632 1700771 := bstep (se 1 (by rfl) ⟨1275578, by rfl⟩ : syracuseStep 1700771 = 2551157) B2551157
theorem B4846513 : Blo 1132632 4846513 := bstep (se 2 (by rfl) ⟨1817442, by rfl⟩ : syracuseStep 4846513 = 3634885) B3634885
theorem B3830705 : Blo 1132632 3830705 := bstep (se 2 (by rfl) ⟨1436514, by rfl⟩ : syracuseStep 3830705 = 2873029) B2873029
theorem B1700801 : Blo 1132632 1700801 := bstep (se 2 (by rfl) ⟨637800, by rfl⟩ : syracuseStep 1700801 = 1275601) B1275601
theorem B1700819 : Blo 1132632 1700819 := bstep (se 1 (by rfl) ⟨1275614, by rfl⟩ : syracuseStep 1700819 = 2551229) B2551229
theorem B1700849 : Blo 1132632 1700849 := bstep (se 2 (by rfl) ⟨637818, by rfl⟩ : syracuseStep 1700849 = 1275637) B1275637
theorem B1700867 : Blo 1132632 1700867 := bstep (se 1 (by rfl) ⟨1275650, by rfl⟩ : syracuseStep 1700867 = 2551301) B2551301
theorem B2552849 : Blo 1132632 2552849 := bstep (se 2 (by rfl) ⟨957318, by rfl⟩ : syracuseStep 2552849 = 1914637) B1914637
theorem B1274899 : Blo 1132632 1274899 := bstep (se 1 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 1274899 = 1912349) B1912349
theorem B1700897 : Blo 1132632 1700897 := bstep (se 2 (by rfl) ⟨637836, by rfl⟩ : syracuseStep 1700897 = 1275673) B1275673
theorem B2552867 : Blo 1132632 2552867 := bstep (se 1 (by rfl) ⟨1914650, by rfl⟩ : syracuseStep 2552867 = 3829301) B3829301
theorem B1700915 : Blo 1132632 1700915 := bstep (se 1 (by rfl) ⟨1275686, by rfl⟩ : syracuseStep 1700915 = 2551373) B2551373
theorem B1700945 : Blo 1132632 1700945 := bstep (se 2 (by rfl) ⟨637854, by rfl⟩ : syracuseStep 1700945 = 1275709) B1275709
theorem B1700963 : Blo 1132632 1700963 := bstep (se 1 (by rfl) ⟨1275722, by rfl⟩ : syracuseStep 1700963 = 2551445) B2551445
theorem B1700993 : Blo 1132632 1700993 := bstep (se 2 (by rfl) ⟨637872, by rfl⟩ : syracuseStep 1700993 = 1275745) B1275745
theorem B2946179 : Blo 1132632 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1701011 : Blo 1132632 1701011 := bstep (se 1 (by rfl) ⟨1275758, by rfl⟩ : syracuseStep 1701011 = 2551517) B2551517
theorem B1275043 : Blo 1132632 1275043 := bstep (se 1 (by rfl) ⟨956282, by rfl⟩ : syracuseStep 1275043 = 1912565) B1912565
theorem B1701041 : Blo 1132632 1701041 := bstep (se 2 (by rfl) ⟨637890, by rfl⟩ : syracuseStep 1701041 = 1275781) B1275781
theorem B1701059 : Blo 1132632 1701059 := bstep (se 1 (by rfl) ⟨1275794, by rfl⟩ : syracuseStep 1701059 = 2551589) B2551589
theorem B1701089 : Blo 1132632 1701089 := bstep (se 2 (by rfl) ⟨637908, by rfl⟩ : syracuseStep 1701089 = 1275817) B1275817
theorem B2422001 : Blo 1132632 2422001 := bstep (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) B1816501
theorem B1701107 : Blo 1132632 1701107 := bstep (se 1 (by rfl) ⟨1275830, by rfl⟩ : syracuseStep 1701107 = 2551661) B2551661
theorem B7271693 : Blo 1132632 7271693 := bstep (se 3 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 7271693 = 2726885) B2726885
theorem B1701137 : Blo 1132632 1701137 := bstep (se 2 (by rfl) ⟨637926, by rfl⟩ : syracuseStep 1701137 = 1275853) B1275853
theorem B1701155 : Blo 1132632 1701155 := bstep (se 1 (by rfl) ⟨1275866, by rfl⟩ : syracuseStep 1701155 = 2551733) B2551733
theorem B2553137 : Blo 1132632 2553137 := bstep (se 2 (by rfl) ⟨957426, by rfl⟩ : syracuseStep 2553137 = 1914853) B1914853
theorem B1275187 : Blo 1132632 1275187 := bstep (se 1 (by rfl) ⟨956390, by rfl⟩ : syracuseStep 1275187 = 1912781) B1912781
theorem B1701185 : Blo 1132632 1701185 := bstep (se 2 (by rfl) ⟨637944, by rfl⟩ : syracuseStep 1701185 = 1275889) B1275889
theorem B2553155 : Blo 1132632 2553155 := bstep (se 1 (by rfl) ⟨1914866, by rfl⟩ : syracuseStep 2553155 = 3829733) B3829733
theorem B1701203 : Blo 1132632 1701203 := bstep (se 1 (by rfl) ⟨1275902, by rfl⟩ : syracuseStep 1701203 = 2551805) B2551805
theorem B9696611 : Blo 1132632 9696611 := bstep (se 1 (by rfl) ⟨7272458, by rfl⟩ : syracuseStep 9696611 = 14544917) B14544917
theorem B1701233 : Blo 1132632 1701233 := bstep (se 2 (by rfl) ⟨637962, by rfl⟩ : syracuseStep 1701233 = 1275925) B1275925
theorem B1701251 : Blo 1132632 1701251 := bstep (se 1 (by rfl) ⟨1275938, by rfl⟩ : syracuseStep 1701251 = 2551877) B2551877
theorem B1701281 : Blo 1132632 1701281 := bstep (se 2 (by rfl) ⟨637980, by rfl⟩ : syracuseStep 1701281 = 1275961) B1275961
theorem B1701299 : Blo 1132632 1701299 := bstep (se 1 (by rfl) ⟨1275974, by rfl⟩ : syracuseStep 1701299 = 2551949) B2551949
theorem B1275331 : Blo 1132632 1275331 := bstep (se 1 (by rfl) ⟨956498, by rfl⟩ : syracuseStep 1275331 = 1912997) B1912997
theorem B3831245 : Blo 1132632 3831245 := bstep (se 3 (by rfl) ⟨718358, by rfl⟩ : syracuseStep 3831245 = 1436717) B1436717
theorem B1701329 : Blo 1132632 1701329 := bstep (se 2 (by rfl) ⟨637998, by rfl⟩ : syracuseStep 1701329 = 1275997) B1275997
theorem B1701347 : Blo 1132632 1701347 := bstep (se 1 (by rfl) ⟨1276010, by rfl⟩ : syracuseStep 1701347 = 2552021) B2552021
theorem B4093411 : Blo 1132632 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B1701377 : Blo 1132632 1701377 := bstep (se 2 (by rfl) ⟨638016, by rfl⟩ : syracuseStep 1701377 = 1276033) B1276033
theorem B3831299 : Blo 1132632 3831299 := bstep (se 1 (by rfl) ⟨2873474, by rfl⟩ : syracuseStep 3831299 = 5746949) B5746949
theorem B6911501 : Blo 1132632 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B1701395 : Blo 1132632 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B1701425 : Blo 1132632 1701425 := bstep (se 2 (by rfl) ⟨638034, by rfl⟩ : syracuseStep 1701425 = 1276069) B1276069
theorem B1209907 : Blo 1132632 1209907 := bstep (se 1 (by rfl) ⟨907430, by rfl⟩ : syracuseStep 1209907 = 1814861) B1814861
theorem B1701443 : Blo 1132632 1701443 := bstep (se 1 (by rfl) ⟨1276082, by rfl⟩ : syracuseStep 1701443 = 2552165) B2552165
theorem B2553425 : Blo 1132632 2553425 := bstep (se 2 (by rfl) ⟨957534, by rfl⟩ : syracuseStep 2553425 = 1915069) B1915069
theorem B1275475 : Blo 1132632 1275475 := bstep (se 1 (by rfl) ⟨956606, by rfl⟩ : syracuseStep 1275475 = 1913213) B1913213
theorem B1701473 : Blo 1132632 1701473 := bstep (se 2 (by rfl) ⟨638052, by rfl⟩ : syracuseStep 1701473 = 1276105) B1276105
theorem B2553443 : Blo 1132632 2553443 := bstep (se 1 (by rfl) ⟨1915082, by rfl⟩ : syracuseStep 2553443 = 3830165) B3830165
theorem B1701491 : Blo 1132632 1701491 := bstep (se 1 (by rfl) ⟨1276118, by rfl⟩ : syracuseStep 1701491 = 2552237) B2552237
theorem B1701521 : Blo 1132632 1701521 := bstep (se 2 (by rfl) ⟨638070, by rfl⟩ : syracuseStep 1701521 = 1276141) B1276141
theorem B1701539 : Blo 1132632 1701539 := bstep (se 1 (by rfl) ⟨1276154, by rfl⟩ : syracuseStep 1701539 = 2552309) B2552309
theorem B1701569 : Blo 1132632 1701569 := bstep (se 2 (by rfl) ⟨638088, by rfl⟩ : syracuseStep 1701569 = 1276177) B1276177
theorem B3634897 : Blo 1132632 3634897 := bstep (se 2 (by rfl) ⟨1363086, by rfl⟩ : syracuseStep 3634897 = 2726173) B2726173
theorem B1701587 : Blo 1132632 1701587 := bstep (se 1 (by rfl) ⟨1276190, by rfl⟩ : syracuseStep 1701587 = 2552381) B2552381
theorem B1275619 : Blo 1132632 1275619 := bstep (se 1 (by rfl) ⟨956714, by rfl⟩ : syracuseStep 1275619 = 1913429) B1913429
theorem B4978417 : Blo 1132632 4978417 := bstep (se 2 (by rfl) ⟨1866906, by rfl⟩ : syracuseStep 4978417 = 3733813) B3733813
theorem B1701617 : Blo 1132632 1701617 := bstep (se 2 (by rfl) ⟨638106, by rfl⟩ : syracuseStep 1701617 = 1276213) B1276213
theorem B1701635 : Blo 1132632 1701635 := bstep (se 1 (by rfl) ⟨1276226, by rfl⟩ : syracuseStep 1701635 = 2552453) B2552453
theorem B3831569 : Blo 1132632 3831569 := bstep (se 2 (by rfl) ⟨1436838, by rfl⟩ : syracuseStep 3831569 = 2873677) B2873677
theorem B1701665 : Blo 1132632 1701665 := bstep (se 2 (by rfl) ⟨638124, by rfl⟩ : syracuseStep 1701665 = 1276249) B1276249
theorem B1701683 : Blo 1132632 1701683 := bstep (se 1 (by rfl) ⟨1276262, by rfl⟩ : syracuseStep 1701683 = 2552525) B2552525
theorem B1701713 : Blo 1132632 1701713 := bstep (se 2 (by rfl) ⟨638142, by rfl⟩ : syracuseStep 1701713 = 1276285) B1276285
theorem B1701731 : Blo 1132632 1701731 := bstep (se 1 (by rfl) ⟨1276298, by rfl⟩ : syracuseStep 1701731 = 2552597) B2552597
theorem B19363697 : Blo 1132632 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B2553713 : Blo 1132632 2553713 := bstep (se 2 (by rfl) ⟨957642, by rfl⟩ : syracuseStep 2553713 = 1915285) B1915285
theorem B1275763 : Blo 1132632 1275763 := bstep (se 1 (by rfl) ⟨956822, by rfl⟩ : syracuseStep 1275763 = 1913645) B1913645
theorem B1701761 : Blo 1132632 1701761 := bstep (se 2 (by rfl) ⟨638160, by rfl⟩ : syracuseStep 1701761 = 1276321) B1276321
theorem B2455427 : Blo 1132632 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B2553731 : Blo 1132632 2553731 := bstep (se 1 (by rfl) ⟨1915298, by rfl⟩ : syracuseStep 2553731 = 3830597) B3830597
theorem B1701779 : Blo 1132632 1701779 := bstep (se 1 (by rfl) ⟨1276334, by rfl⟩ : syracuseStep 1701779 = 2552669) B2552669
theorem B4093859 : Blo 1132632 4093859 := bstep (se 1 (by rfl) ⟨3070394, by rfl⟩ : syracuseStep 4093859 = 6140789) B6140789
theorem B1701809 : Blo 1132632 1701809 := bstep (se 2 (by rfl) ⟨638178, by rfl⟩ : syracuseStep 1701809 = 1276357) B1276357
theorem B1701827 : Blo 1132632 1701827 := bstep (se 1 (by rfl) ⟨1276370, by rfl⟩ : syracuseStep 1701827 = 2552741) B2552741
theorem B1701857 : Blo 1132632 1701857 := bstep (se 2 (by rfl) ⟨638196, by rfl⟩ : syracuseStep 1701857 = 1276393) B1276393
theorem B1701875 : Blo 1132632 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B1275907 : Blo 1132632 1275907 := bstep (se 1 (by rfl) ⟨956930, by rfl⟩ : syracuseStep 1275907 = 1913861) B1913861
theorem B1701905 : Blo 1132632 1701905 := bstep (se 2 (by rfl) ⟨638214, by rfl⟩ : syracuseStep 1701905 = 1276429) B1276429
theorem B1701923 : Blo 1132632 1701923 := bstep (se 1 (by rfl) ⟨1276442, by rfl⟩ : syracuseStep 1701923 = 2552885) B2552885
theorem B1701953 : Blo 1132632 1701953 := bstep (se 2 (by rfl) ⟨638232, by rfl⟩ : syracuseStep 1701953 = 1276465) B1276465
theorem B1701971 : Blo 1132632 1701971 := bstep (se 1 (by rfl) ⟨1276478, by rfl⟩ : syracuseStep 1701971 = 2552957) B2552957
theorem B1702001 : Blo 1132632 1702001 := bstep (se 2 (by rfl) ⟨638250, by rfl⟩ : syracuseStep 1702001 = 1276501) B1276501
theorem B1702019 : Blo 1132632 1702019 := bstep (se 1 (by rfl) ⟨1276514, by rfl⟩ : syracuseStep 1702019 = 2553029) B2553029
theorem B2554001 : Blo 1132632 2554001 := bstep (se 2 (by rfl) ⟨957750, by rfl⟩ : syracuseStep 2554001 = 1915501) B1915501
theorem B1276051 : Blo 1132632 1276051 := bstep (se 1 (by rfl) ⟨957038, by rfl⟩ : syracuseStep 1276051 = 1914077) B1914077
theorem B1702049 : Blo 1132632 1702049 := bstep (se 2 (by rfl) ⟨638268, by rfl⟩ : syracuseStep 1702049 = 1276537) B1276537
theorem B2554019 : Blo 1132632 2554019 := bstep (se 1 (by rfl) ⟨1915514, by rfl⟩ : syracuseStep 2554019 = 3831029) B3831029
theorem B1702067 : Blo 1132632 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B1702097 : Blo 1132632 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B1702115 : Blo 1132632 1702115 := bstep (se 1 (by rfl) ⟨1276586, by rfl⟩ : syracuseStep 1702115 = 2553173) B2553173
theorem B1702145 : Blo 1132632 1702145 := bstep (se 2 (by rfl) ⟨638304, by rfl⟩ : syracuseStep 1702145 = 1276609) B1276609
theorem B1702163 : Blo 1132632 1702163 := bstep (se 1 (by rfl) ⟨1276622, by rfl⟩ : syracuseStep 1702163 = 2553245) B2553245
theorem B1276195 : Blo 1132632 1276195 := bstep (se 1 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 1276195 = 1914293) B1914293
theorem B3832109 : Blo 1132632 3832109 := bstep (se 3 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 3832109 = 1437041) B1437041
theorem B1702193 : Blo 1132632 1702193 := bstep (se 2 (by rfl) ⟨638322, by rfl⟩ : syracuseStep 1702193 = 1276645) B1276645
theorem B1702211 : Blo 1132632 1702211 := bstep (se 1 (by rfl) ⟨1276658, by rfl⟩ : syracuseStep 1702211 = 2553317) B2553317
theorem B1702241 : Blo 1132632 1702241 := bstep (se 2 (by rfl) ⟨638340, by rfl⟩ : syracuseStep 1702241 = 1276681) B1276681
theorem B3832163 : Blo 1132632 3832163 := bstep (se 1 (by rfl) ⟨2874122, by rfl⟩ : syracuseStep 3832163 = 5748245) B5748245
theorem B1702259 : Blo 1132632 1702259 := bstep (se 1 (by rfl) ⟨1276694, by rfl⟩ : syracuseStep 1702259 = 2553389) B2553389
theorem B1702289 : Blo 1132632 1702289 := bstep (se 2 (by rfl) ⟨638358, by rfl⟩ : syracuseStep 1702289 = 1276717) B1276717
theorem B1702307 : Blo 1132632 1702307 := bstep (se 1 (by rfl) ⟨1276730, by rfl⟩ : syracuseStep 1702307 = 2553461) B2553461
theorem B2554289 : Blo 1132632 2554289 := bstep (se 2 (by rfl) ⟨957858, by rfl⟩ : syracuseStep 2554289 = 1915717) B1915717
theorem B1276339 : Blo 1132632 1276339 := bstep (se 1 (by rfl) ⟨957254, by rfl⟩ : syracuseStep 1276339 = 1914509) B1914509
theorem B1702337 : Blo 1132632 1702337 := bstep (se 2 (by rfl) ⟨638376, by rfl⟩ : syracuseStep 1702337 = 1276753) B1276753
theorem B2554307 : Blo 1132632 2554307 := bstep (se 1 (by rfl) ⟨1915730, by rfl⟩ : syracuseStep 2554307 = 3831461) B3831461
theorem B6453701 : Blo 1132632 6453701 := bstep (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) B1210069
theorem B1702355 : Blo 1132632 1702355 := bstep (se 1 (by rfl) ⟨1276766, by rfl⟩ : syracuseStep 1702355 = 2553533) B2553533
theorem B1702385 : Blo 1132632 1702385 := bstep (se 2 (by rfl) ⟨638394, by rfl⟩ : syracuseStep 1702385 = 1276789) B1276789
theorem B2423299 : Blo 1132632 2423299 := bstep (se 1 (by rfl) ⟨1817474, by rfl⟩ : syracuseStep 2423299 = 3634949) B3634949
theorem B1702403 : Blo 1132632 1702403 := bstep (se 1 (by rfl) ⟨1276802, by rfl⟩ : syracuseStep 1702403 = 2553605) B2553605
theorem B2587153 : Blo 1132632 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B1702433 : Blo 1132632 1702433 := bstep (se 2 (by rfl) ⟨638412, by rfl⟩ : syracuseStep 1702433 = 1276825) B1276825
theorem B1702451 : Blo 1132632 1702451 := bstep (se 1 (by rfl) ⟨1276838, by rfl⟩ : syracuseStep 1702451 = 2553677) B2553677
theorem B1276483 : Blo 1132632 1276483 := bstep (se 1 (by rfl) ⟨957362, by rfl⟩ : syracuseStep 1276483 = 1914725) B1914725
theorem B1702481 : Blo 1132632 1702481 := bstep (se 2 (by rfl) ⟨638430, by rfl⟩ : syracuseStep 1702481 = 1276861) B1276861
theorem B1702499 : Blo 1132632 1702499 := bstep (se 1 (by rfl) ⟨1276874, by rfl⟩ : syracuseStep 1702499 = 2553749) B2553749
theorem B3832433 : Blo 1132632 3832433 := bstep (se 2 (by rfl) ⟨1437162, by rfl⟩ : syracuseStep 3832433 = 2874325) B2874325
theorem B1702529 : Blo 1132632 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B1702547 : Blo 1132632 1702547 := bstep (se 1 (by rfl) ⟨1276910, by rfl⟩ : syracuseStep 1702547 = 2553821) B2553821
theorem B1702577 : Blo 1132632 1702577 := bstep (se 2 (by rfl) ⟨638466, by rfl⟩ : syracuseStep 1702577 = 1276933) B1276933
theorem B1702595 : Blo 1132632 1702595 := bstep (se 1 (by rfl) ⟨1276946, by rfl⟩ : syracuseStep 1702595 = 2553893) B2553893
theorem B2554577 : Blo 1132632 2554577 := bstep (se 2 (by rfl) ⟨957966, by rfl⟩ : syracuseStep 2554577 = 1915933) B1915933
theorem B1276627 : Blo 1132632 1276627 := bstep (se 1 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 1276627 = 1914941) B1914941
theorem B1702625 : Blo 1132632 1702625 := bstep (se 2 (by rfl) ⟨638484, by rfl⟩ : syracuseStep 1702625 = 1276969) B1276969
theorem B2554595 : Blo 1132632 2554595 := bstep (se 1 (by rfl) ⟨1915946, by rfl⟩ : syracuseStep 2554595 = 3831893) B3831893
theorem B1702643 : Blo 1132632 1702643 := bstep (se 1 (by rfl) ⟨1276982, by rfl⟩ : syracuseStep 1702643 = 2553965) B2553965
theorem B1702673 : Blo 1132632 1702673 := bstep (se 2 (by rfl) ⟨638502, by rfl⟩ : syracuseStep 1702673 = 1277005) B1277005
theorem B1211171 : Blo 1132632 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B1702691 : Blo 1132632 1702691 := bstep (se 1 (by rfl) ⟨1277018, by rfl⟩ : syracuseStep 1702691 = 2554037) B2554037
theorem B1702721 : Blo 1132632 1702721 := bstep (se 2 (by rfl) ⟨638520, by rfl⟩ : syracuseStep 1702721 = 1277041) B1277041
theorem B10910533 : Blo 1132632 10910533 := bstep (se 4 (by rfl) ⟨1022862, by rfl⟩ : syracuseStep 10910533 = 2045725) B2045725
theorem B1702739 : Blo 1132632 1702739 := bstep (se 1 (by rfl) ⟨1277054, by rfl⟩ : syracuseStep 1702739 = 2554109) B2554109
theorem B1276771 : Blo 1132632 1276771 := bstep (se 1 (by rfl) ⟨957578, by rfl⟩ : syracuseStep 1276771 = 1915157) B1915157
theorem B1702769 : Blo 1132632 1702769 := bstep (se 2 (by rfl) ⟨638538, by rfl⟩ : syracuseStep 1702769 = 1277077) B1277077
theorem B2915185 : Blo 1132632 2915185 := bstep (se 2 (by rfl) ⟨1093194, by rfl⟩ : syracuseStep 2915185 = 2186389) B2186389
theorem B1702787 : Blo 1132632 1702787 := bstep (se 1 (by rfl) ⟨1277090, by rfl⟩ : syracuseStep 1702787 = 2554181) B2554181
theorem B1702817 : Blo 1132632 1702817 := bstep (se 2 (by rfl) ⟨638556, by rfl⟩ : syracuseStep 1702817 = 1277113) B1277113
theorem B1702835 : Blo 1132632 1702835 := bstep (se 1 (by rfl) ⟨1277126, by rfl⟩ : syracuseStep 1702835 = 2554253) B2554253
theorem B1702865 : Blo 1132632 1702865 := bstep (se 2 (by rfl) ⟨638574, by rfl⟩ : syracuseStep 1702865 = 1277149) B1277149
theorem B1702883 : Blo 1132632 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B2554865 : Blo 1132632 2554865 := bstep (se 2 (by rfl) ⟨958074, by rfl⟩ : syracuseStep 2554865 = 1916149) B1916149
theorem B1276915 : Blo 1132632 1276915 := bstep (se 1 (by rfl) ⟨957686, by rfl⟩ : syracuseStep 1276915 = 1915373) B1915373
theorem B1702913 : Blo 1132632 1702913 := bstep (se 2 (by rfl) ⟨638592, by rfl⟩ : syracuseStep 1702913 = 1277185) B1277185
theorem B2554883 : Blo 1132632 2554883 := bstep (se 1 (by rfl) ⟨1916162, by rfl⟩ : syracuseStep 2554883 = 3832325) B3832325
theorem B1702931 : Blo 1132632 1702931 := bstep (se 1 (by rfl) ⟨1277198, by rfl⟩ : syracuseStep 1702931 = 2554397) B2554397
theorem B1702961 : Blo 1132632 1702961 := bstep (se 2 (by rfl) ⟨638610, by rfl⟩ : syracuseStep 1702961 = 1277221) B1277221
theorem B1702979 : Blo 1132632 1702979 := bstep (se 1 (by rfl) ⟨1277234, by rfl⟩ : syracuseStep 1702979 = 2554469) B2554469
theorem B1703009 : Blo 1132632 1703009 := bstep (se 2 (by rfl) ⟨638628, by rfl⟩ : syracuseStep 1703009 = 1277257) B1277257
theorem B1703027 : Blo 1132632 1703027 := bstep (se 1 (by rfl) ⟨1277270, by rfl⟩ : syracuseStep 1703027 = 2554541) B2554541
theorem B1277059 : Blo 1132632 1277059 := bstep (se 1 (by rfl) ⟨957794, by rfl⟩ : syracuseStep 1277059 = 1915589) B1915589
theorem B3832973 : Blo 1132632 3832973 := bstep (se 3 (by rfl) ⟨718682, by rfl⟩ : syracuseStep 3832973 = 1437365) B1437365
theorem B1703057 : Blo 1132632 1703057 := bstep (se 2 (by rfl) ⟨638646, by rfl⟩ : syracuseStep 1703057 = 1277293) B1277293
theorem B1703075 : Blo 1132632 1703075 := bstep (se 1 (by rfl) ⟨1277306, by rfl⟩ : syracuseStep 1703075 = 2554613) B2554613
theorem B1703105 : Blo 1132632 1703105 := bstep (se 2 (by rfl) ⟨638664, by rfl⟩ : syracuseStep 1703105 = 1277329) B1277329
theorem B3833027 : Blo 1132632 3833027 := bstep (se 1 (by rfl) ⟨2874770, by rfl⟩ : syracuseStep 3833027 = 5749541) B5749541
theorem B1703123 : Blo 1132632 1703123 := bstep (se 1 (by rfl) ⟨1277342, by rfl⟩ : syracuseStep 1703123 = 2554685) B2554685
theorem B1703153 : Blo 1132632 1703153 := bstep (se 2 (by rfl) ⟨638682, by rfl⟩ : syracuseStep 1703153 = 1277365) B1277365
theorem B1703171 : Blo 1132632 1703171 := bstep (se 1 (by rfl) ⟨1277378, by rfl⟩ : syracuseStep 1703171 = 2554757) B2554757
theorem B6552845 : Blo 1132632 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B2555153 : Blo 1132632 2555153 := bstep (se 2 (by rfl) ⟨958182, by rfl⟩ : syracuseStep 2555153 = 1916365) B1916365
theorem B1277203 : Blo 1132632 1277203 := bstep (se 1 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 1277203 = 1915805) B1915805
theorem B1703201 : Blo 1132632 1703201 := bstep (se 2 (by rfl) ⟨638700, by rfl⟩ : syracuseStep 1703201 = 1277401) B1277401
theorem B2555171 : Blo 1132632 2555171 := bstep (se 1 (by rfl) ⟨1916378, by rfl⟩ : syracuseStep 2555171 = 3832757) B3832757
theorem B1703219 : Blo 1132632 1703219 := bstep (se 1 (by rfl) ⟨1277414, by rfl⟩ : syracuseStep 1703219 = 2554829) B2554829
theorem B1703249 : Blo 1132632 1703249 := bstep (se 2 (by rfl) ⟨638718, by rfl⟩ : syracuseStep 1703249 = 1277437) B1277437
theorem B1703267 : Blo 1132632 1703267 := bstep (se 1 (by rfl) ⟨1277450, by rfl⟩ : syracuseStep 1703267 = 2554901) B2554901
theorem B3636589 : Blo 1132632 3636589 := bstep (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) B1363721
theorem B1703297 : Blo 1132632 1703297 := bstep (se 2 (by rfl) ⟨638736, by rfl⟩ : syracuseStep 1703297 = 1277473) B1277473
theorem B1703315 : Blo 1132632 1703315 := bstep (se 1 (by rfl) ⟨1277486, by rfl⟩ : syracuseStep 1703315 = 2554973) B2554973
theorem B1277347 : Blo 1132632 1277347 := bstep (se 1 (by rfl) ⟨958010, by rfl⟩ : syracuseStep 1277347 = 1916021) B1916021
theorem B1703345 : Blo 1132632 1703345 := bstep (se 2 (by rfl) ⟨638754, by rfl⟩ : syracuseStep 1703345 = 1277509) B1277509
theorem B1703363 : Blo 1132632 1703363 := bstep (se 1 (by rfl) ⟨1277522, by rfl⟩ : syracuseStep 1703363 = 2555045) B2555045
theorem B3833297 : Blo 1132632 3833297 := bstep (se 2 (by rfl) ⟨1437486, by rfl⟩ : syracuseStep 3833297 = 2874973) B2874973
theorem B1703393 : Blo 1132632 1703393 := bstep (se 2 (by rfl) ⟨638772, by rfl⟩ : syracuseStep 1703393 = 1277545) B1277545
theorem B1703411 : Blo 1132632 1703411 := bstep (se 1 (by rfl) ⟨1277558, by rfl⟩ : syracuseStep 1703411 = 2555117) B2555117
theorem B1703441 : Blo 1132632 1703441 := bstep (se 2 (by rfl) ⟨638790, by rfl⟩ : syracuseStep 1703441 = 1277581) B1277581
theorem B1211923 : Blo 1132632 1211923 := bstep (se 1 (by rfl) ⟨908942, by rfl⟩ : syracuseStep 1211923 = 1817885) B1817885
theorem B1703459 : Blo 1132632 1703459 := bstep (se 1 (by rfl) ⟨1277594, by rfl⟩ : syracuseStep 1703459 = 2555189) B2555189
theorem B2555441 : Blo 1132632 2555441 := bstep (se 2 (by rfl) ⟨958290, by rfl⟩ : syracuseStep 2555441 = 1916581) B1916581
theorem B1277491 : Blo 1132632 1277491 := bstep (se 1 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 1277491 = 1916237) B1916237
theorem B1703489 : Blo 1132632 1703489 := bstep (se 2 (by rfl) ⟨638808, by rfl⟩ : syracuseStep 1703489 = 1277617) B1277617
theorem B2555459 : Blo 1132632 2555459 := bstep (se 1 (by rfl) ⟨1916594, by rfl⟩ : syracuseStep 2555459 = 3833189) B3833189
theorem B1703507 : Blo 1132632 1703507 := bstep (se 1 (by rfl) ⟨1277630, by rfl⟩ : syracuseStep 1703507 = 2555261) B2555261
theorem B1703537 : Blo 1132632 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1703555 : Blo 1132632 1703555 := bstep (se 1 (by rfl) ⟨1277666, by rfl⟩ : syracuseStep 1703555 = 2555333) B2555333
theorem B1703585 : Blo 1132632 1703585 := bstep (se 2 (by rfl) ⟨638844, by rfl⟩ : syracuseStep 1703585 = 1277689) B1277689
theorem B1703603 : Blo 1132632 1703603 := bstep (se 1 (by rfl) ⟨1277702, by rfl⟩ : syracuseStep 1703603 = 2555405) B2555405
theorem B1277635 : Blo 1132632 1277635 := bstep (se 1 (by rfl) ⟨958226, by rfl⟩ : syracuseStep 1277635 = 1916453) B1916453
theorem B2424529 : Blo 1132632 2424529 := bstep (se 2 (by rfl) ⟨909198, by rfl⟩ : syracuseStep 2424529 = 1818397) B1818397
theorem B1703633 : Blo 1132632 1703633 := bstep (se 2 (by rfl) ⟨638862, by rfl⟩ : syracuseStep 1703633 = 1277725) B1277725
theorem B55115477 : Blo 1132632 55115477 := bstep (se 7 (by rfl) ⟨645884, by rfl⟩ : syracuseStep 55115477 = 1291769) B1291769
theorem B1703651 : Blo 1132632 1703651 := bstep (se 1 (by rfl) ⟨1277738, by rfl⟩ : syracuseStep 1703651 = 2555477) B2555477
theorem B1703681 : Blo 1132632 1703681 := bstep (se 2 (by rfl) ⟨638880, by rfl⟩ : syracuseStep 1703681 = 1277761) B1277761
theorem B1212179 : Blo 1132632 1212179 := bstep (se 1 (by rfl) ⟨909134, by rfl⟩ : syracuseStep 1212179 = 1818269) B1818269
theorem B1703699 : Blo 1132632 1703699 := bstep (se 1 (by rfl) ⟨1277774, by rfl⟩ : syracuseStep 1703699 = 2555549) B2555549
theorem B1703729 : Blo 1132632 1703729 := bstep (se 2 (by rfl) ⟨638898, by rfl⟩ : syracuseStep 1703729 = 1277797) B1277797
theorem B1703747 : Blo 1132632 1703747 := bstep (se 1 (by rfl) ⟨1277810, by rfl⟩ : syracuseStep 1703747 = 2555621) B2555621
theorem B2555729 : Blo 1132632 2555729 := bstep (se 2 (by rfl) ⟨958398, by rfl⟩ : syracuseStep 2555729 = 1916797) B1916797
theorem B1277779 : Blo 1132632 1277779 := bstep (se 1 (by rfl) ⟨958334, by rfl⟩ : syracuseStep 1277779 = 1916669) B1916669
theorem B1703777 : Blo 1132632 1703777 := bstep (se 2 (by rfl) ⟨638916, by rfl⟩ : syracuseStep 1703777 = 1277833) B1277833
theorem B2555747 : Blo 1132632 2555747 := bstep (se 1 (by rfl) ⟨1916810, by rfl⟩ : syracuseStep 2555747 = 3833621) B3833621
theorem B1703795 : Blo 1132632 1703795 := bstep (se 1 (by rfl) ⟨1277846, by rfl⟩ : syracuseStep 1703795 = 2555693) B2555693
theorem B1703825 : Blo 1132632 1703825 := bstep (se 2 (by rfl) ⟨638934, by rfl⟩ : syracuseStep 1703825 = 1277869) B1277869
theorem B4849571 : Blo 1132632 4849571 := bstep (se 1 (by rfl) ⟨3637178, by rfl⟩ : syracuseStep 4849571 = 7274357) B7274357
theorem B1703843 : Blo 1132632 1703843 := bstep (se 1 (by rfl) ⟨1277882, by rfl⟩ : syracuseStep 1703843 = 2555765) B2555765
theorem B1703873 : Blo 1132632 1703873 := bstep (se 2 (by rfl) ⟨638952, by rfl⟩ : syracuseStep 1703873 = 1277905) B1277905
theorem B1703891 : Blo 1132632 1703891 := bstep (se 1 (by rfl) ⟨1277918, by rfl⟩ : syracuseStep 1703891 = 2555837) B2555837
theorem B1277923 : Blo 1132632 1277923 := bstep (se 1 (by rfl) ⟨958442, by rfl⟩ : syracuseStep 1277923 = 1916885) B1916885
theorem B3833837 : Blo 1132632 3833837 := bstep (se 3 (by rfl) ⟨718844, by rfl⟩ : syracuseStep 3833837 = 1437689) B1437689
theorem B1703921 : Blo 1132632 1703921 := bstep (se 2 (by rfl) ⟨638970, by rfl⟩ : syracuseStep 1703921 = 1277941) B1277941
theorem B2555927 : Blo 1132632 2555927 := bstep (se 1 (by rfl) ⟨1916945, by rfl⟩ : syracuseStep 2555927 = 3833891) B3833891
theorem B1277995 : Blo 1132632 1277995 := bstep (se 1 (by rfl) ⟨958496, by rfl⟩ : syracuseStep 1277995 = 1916993) B1916993
theorem B5734475 : Blo 1132632 5734475 := bstep (se 1 (by rfl) ⟨4300856, by rfl⟩ : syracuseStep 5734475 = 8601713) B8601713
theorem B34930763 : Blo 1132632 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B1704011 : Blo 1132632 1704011 := bstep (se 1 (by rfl) ⟨1278008, by rfl⟩ : syracuseStep 1704011 = 2556017) B2556017
theorem B1704023 : Blo 1132632 1704023 := bstep (se 1 (by rfl) ⟨1278017, by rfl⟩ : syracuseStep 1704023 = 2556035) B2556035
theorem B3833945 : Blo 1132632 3833945 := bstep (se 2 (by rfl) ⟨1437729, by rfl⟩ : syracuseStep 3833945 = 2875459) B2875459
theorem B1278103 : Blo 1132632 1278103 := bstep (se 1 (by rfl) ⟨958577, by rfl⟩ : syracuseStep 1278103 = 1917155) B1917155
theorem B1704089 : Blo 1132632 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B2556107 : Blo 1132632 2556107 := bstep (se 1 (by rfl) ⟨1917080, by rfl⟩ : syracuseStep 2556107 = 3834161) B3834161
theorem B2556161 : Blo 1132632 2556161 := bstep (se 2 (by rfl) ⟨958560, by rfl⟩ : syracuseStep 2556161 = 1917121) B1917121
theorem B1704203 : Blo 1132632 1704203 := bstep (se 1 (by rfl) ⟨1278152, by rfl⟩ : syracuseStep 1704203 = 2556305) B2556305
theorem B1704215 : Blo 1132632 1704215 := bstep (se 1 (by rfl) ⟨1278161, by rfl⟩ : syracuseStep 1704215 = 2556323) B2556323
theorem B1278283 : Blo 1132632 1278283 := bstep (se 1 (by rfl) ⟨958712, by rfl⟩ : syracuseStep 1278283 = 1917425) B1917425
theorem B1704281 : Blo 1132632 1704281 := bstep (se 2 (by rfl) ⟨639105, by rfl⟩ : syracuseStep 1704281 = 1278211) B1278211
theorem B1278391 : Blo 1132632 1278391 := bstep (se 1 (by rfl) ⟨958793, by rfl⟩ : syracuseStep 1278391 = 1917587) B1917587
theorem B1704395 : Blo 1132632 1704395 := bstep (se 1 (by rfl) ⟨1278296, by rfl⟩ : syracuseStep 1704395 = 2556593) B2556593
theorem B1704407 : Blo 1132632 1704407 := bstep (se 1 (by rfl) ⟨1278305, by rfl⟩ : syracuseStep 1704407 = 2556611) B2556611
theorem B2556377 : Blo 1132632 2556377 := bstep (se 2 (by rfl) ⟨958641, by rfl⟩ : syracuseStep 2556377 = 1917283) B1917283
theorem B1704473 : Blo 1132632 1704473 := bstep (se 2 (by rfl) ⟨639177, by rfl⟩ : syracuseStep 1704473 = 1278355) B1278355
theorem B2556467 : Blo 1132632 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B2556503 : Blo 1132632 2556503 := bstep (se 1 (by rfl) ⟨1917377, by rfl⟩ : syracuseStep 2556503 = 3834755) B3834755
theorem B1278571 : Blo 1132632 1278571 := bstep (se 1 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 1278571 = 1917857) B1917857
theorem B1704587 : Blo 1132632 1704587 := bstep (se 1 (by rfl) ⟨1278440, by rfl⟩ : syracuseStep 1704587 = 2556881) B2556881
theorem B1704599 : Blo 1132632 1704599 := bstep (se 1 (by rfl) ⟨1278449, by rfl⟩ : syracuseStep 1704599 = 2556899) B2556899
theorem B1278679 : Blo 1132632 1278679 := bstep (se 1 (by rfl) ⟨959009, by rfl⟩ : syracuseStep 1278679 = 1918019) B1918019
theorem B1704665 : Blo 1132632 1704665 := bstep (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) B1278499
theorem B2556683 : Blo 1132632 2556683 := bstep (se 1 (by rfl) ⟨1917512, by rfl⟩ : syracuseStep 2556683 = 3835025) B3835025
theorem B3834647 : Blo 1132632 3834647 := bstep (se 1 (by rfl) ⟨2875985, by rfl⟩ : syracuseStep 3834647 = 5751971) B5751971
theorem B7275329 : Blo 1132632 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B2556737 : Blo 1132632 2556737 := bstep (se 2 (by rfl) ⟨958776, by rfl⟩ : syracuseStep 2556737 = 1917553) B1917553
theorem B1704779 : Blo 1132632 1704779 := bstep (se 1 (by rfl) ⟨1278584, by rfl⟩ : syracuseStep 1704779 = 2557169) B2557169
theorem B1704791 : Blo 1132632 1704791 := bstep (se 1 (by rfl) ⟨1278593, by rfl⟩ : syracuseStep 1704791 = 2557187) B2557187
theorem B1704857 : Blo 1132632 1704857 := bstep (se 2 (by rfl) ⟨639321, by rfl⟩ : syracuseStep 1704857 = 1278643) B1278643
theorem B2425793 : Blo 1132632 2425793 := bstep (se 2 (by rfl) ⟨909672, by rfl⟩ : syracuseStep 2425793 = 1819345) B1819345
theorem B2425879 : Blo 1132632 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B2556953 : Blo 1132632 2556953 := bstep (se 2 (by rfl) ⟨958857, by rfl⟩ : syracuseStep 2556953 = 1917715) B1917715
theorem B2557043 : Blo 1132632 2557043 := bstep (se 1 (by rfl) ⟨1917782, by rfl⟩ : syracuseStep 2557043 = 3835565) B3835565
theorem B2557079 : Blo 1132632 2557079 := bstep (se 1 (by rfl) ⟨1917809, by rfl⟩ : syracuseStep 2557079 = 3835619) B3835619
theorem B22086917 : Blo 1132632 22086917 := bstep (se 4 (by rfl) ⟨2070648, by rfl⟩ : syracuseStep 22086917 = 4141297) B4141297
theorem B3835187 : Blo 1132632 3835187 := bstep (se 1 (by rfl) ⟨2876390, by rfl⟩ : syracuseStep 3835187 = 5752781) B5752781
theorem B1213751 : Blo 1132632 1213751 := bstep (se 1 (by rfl) ⟨910313, by rfl⟩ : syracuseStep 1213751 = 1820627) B1820627
theorem B2557259 : Blo 1132632 2557259 := bstep (se 1 (by rfl) ⟨1917944, by rfl⟩ : syracuseStep 2557259 = 3835889) B3835889
theorem B2557313 : Blo 1132632 2557313 := bstep (se 2 (by rfl) ⟨958992, by rfl⟩ : syracuseStep 2557313 = 1917985) B1917985
theorem B4851161 : Blo 1132632 4851161 := bstep (se 2 (by rfl) ⟨1819185, by rfl⟩ : syracuseStep 4851161 = 3638371) B3638371
theorem B4851245 : Blo 1132632 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B3835457 : Blo 1132632 3835457 := bstep (se 2 (by rfl) ⟨1438296, by rfl⟩ : syracuseStep 3835457 = 2876593) B2876593
theorem B5736257 : Blo 1132632 5736257 := bstep (se 2 (by rfl) ⟨2151096, by rfl⟩ : syracuseStep 5736257 = 4302193) B4302193
theorem B2426699 : Blo 1132632 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B3835997 : Blo 1132632 3835997 := bstep (se 3 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 3835997 = 1438499) B1438499
theorem B7276817 : Blo 1132632 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B5179993 : Blo 1132632 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B12258053 : Blo 1132632 12258053 := bstep (se 4 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 12258053 = 2298385) B2298385
theorem B16583429 : Blo 1132632 16583429 := bstep (se 4 (by rfl) ⟨1554696, by rfl⟩ : syracuseStep 16583429 = 3109393) B3109393
theorem B84020165 : Blo 1132632 84020165 := bstep (se 4 (by rfl) ⟨7876890, by rfl⟩ : syracuseStep 84020165 = 15753781) B15753781
theorem B22088855 : Blo 1132632 22088855 := bstep (se 1 (by rfl) ⟨16566641, by rfl⟩ : syracuseStep 22088855 = 33133283) B33133283
theorem B6131123 : Blo 1132632 6131123 := bstep (se 1 (by rfl) ⟨4598342, by rfl⟩ : syracuseStep 6131123 = 9196685) B9196685
theorem B5738201 : Blo 1132632 5738201 := bstep (se 2 (by rfl) ⟨2151825, by rfl⟩ : syracuseStep 5738201 = 4303651) B4303651
theorem B36802289 : Blo 1132632 36802289 := bstep (se 2 (by rfl) ⟨13800858, by rfl⟩ : syracuseStep 36802289 = 27601717) B27601717
theorem B9211799 : Blo 1132632 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B8622125 : Blo 1132632 8622125 := bstep (se 3 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 8622125 = 3233297) B3233297
theorem B2723905 : Blo 1132632 2723905 := bstep (se 2 (by rfl) ⟨1021464, by rfl⟩ : syracuseStep 2723905 = 2042929) B2042929
theorem B7770329 : Blo 1132632 7770329 := bstep (se 2 (by rfl) ⟨2913873, by rfl⟩ : syracuseStep 7770329 = 5827747) B5827747
theorem B49746221 : Blo 1132632 49746221 := bstep (se 3 (by rfl) ⟨9327416, by rfl⟩ : syracuseStep 49746221 = 18654833) B18654833
theorem B14521133 : Blo 1132632 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B4854593 : Blo 1132632 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B10916957 : Blo 1132632 10916957 := bstep (se 3 (by rfl) ⟨2046929, by rfl⟩ : syracuseStep 10916957 = 4093859) B4093859
theorem B5739821 : Blo 1132632 5739821 := bstep (se 3 (by rfl) ⟨1076216, by rfl⟩ : syracuseStep 5739821 = 2152433) B2152433
theorem B8164739 : Blo 1132632 8164739 := bstep (se 1 (by rfl) ⟨6123554, by rfl⟩ : syracuseStep 8164739 = 12247109) B12247109
theorem B2725271 : Blo 1132632 2725271 := bstep (se 1 (by rfl) ⟨2043953, by rfl⟩ : syracuseStep 2725271 = 4087907) B4087907
theorem B5182913 : Blo 1132632 5182913 := bstep (se 2 (by rfl) ⟨1943592, by rfl⟩ : syracuseStep 5182913 = 3887185) B3887185
theorem B4363723 : Blo 1132632 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B8165893 : Blo 1132632 8165893 := bstep (se 4 (by rfl) ⟨765552, by rfl⟩ : syracuseStep 8165893 = 1531105) B1531105
theorem B6462017 : Blo 1132632 6462017 := bstep (se 2 (by rfl) ⟨2423256, by rfl⟩ : syracuseStep 6462017 = 4846513) B4846513
theorem B2071255 : Blo 1132632 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B4660013 : Blo 1132632 4660013 := bstep (se 3 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 4660013 = 1747505) B1747505
theorem B2071819 : Blo 1132632 2071819 := bstep (se 1 (by rfl) ⟨1553864, by rfl⟩ : syracuseStep 2071819 = 3107729) B3107729
theorem B1613209 : Blo 1132632 1613209 := bstep (se 2 (by rfl) ⟨604953, by rfl⟩ : syracuseStep 1613209 = 1209907) B1209907
theorem B1941131 : Blo 1132632 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B20717207 : Blo 1132632 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B4595393 : Blo 1132632 4595393 := bstep (se 2 (by rfl) ⟨1723272, by rfl⟩ : syracuseStep 4595393 = 3446545) B3446545
theorem B14524109 : Blo 1132632 14524109 := bstep (se 3 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 14524109 = 5446541) B5446541
theorem B2727731 : Blo 1132632 2727731 := bstep (se 1 (by rfl) ⟨2045798, by rfl⟩ : syracuseStep 2727731 = 4091597) B4091597
theorem B8626013 : Blo 1132632 8626013 := bstep (se 3 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 8626013 = 3234755) B3234755
theorem B39264101 : Blo 1132632 39264101 := bstep (se 4 (by rfl) ⟨3681009, by rfl⟩ : syracuseStep 39264101 = 7362019) B7362019
theorem B1843415 : Blo 1132632 1843415 := bstep (se 1 (by rfl) ⟨1382561, by rfl⟩ : syracuseStep 1843415 = 2765123) B2765123
theorem B4301207 : Blo 1132632 4301207 := bstep (se 1 (by rfl) ⟨3225905, by rfl⟩ : syracuseStep 4301207 = 6451811) B6451811
theorem B3449537 : Blo 1132632 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B1614667 : Blo 1132632 1614667 := bstep (se 1 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 1614667 = 2422001) B2422001
theorem B6464407 : Blo 1132632 6464407 := bstep (se 1 (by rfl) ⟨4848305, by rfl⟩ : syracuseStep 6464407 = 9696611) B9696611
theorem B5743709 : Blo 1132632 5743709 := bstep (se 3 (by rfl) ⟨1076945, by rfl⟩ : syracuseStep 5743709 = 2153891) B2153891
theorem B9839717 : Blo 1132632 9839717 := bstep (se 4 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 9839717 = 1844947) B1844947
theorem B4662659 : Blo 1132632 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B1942937 : Blo 1132632 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B9676381 : Blo 1132632 9676381 := bstep (se 3 (by rfl) ⟨1814321, by rfl⟩ : syracuseStep 9676381 = 3628643) B3628643
theorem B4302467 : Blo 1132632 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B4597469 : Blo 1132632 4597469 := bstep (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) B1724051
theorem B2041625 : Blo 1132632 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B10889005 : Blo 1132632 10889005 := bstep (se 3 (by rfl) ⟨2041688, by rfl⟩ : syracuseStep 10889005 = 4083377) B4083377
theorem B1615897 : Blo 1132632 1615897 := bstep (se 2 (by rfl) ⟨605961, by rfl⟩ : syracuseStep 1615897 = 1211923) B1211923
theorem B8726707 : Blo 1132632 8726707 := bstep (se 1 (by rfl) ⟨6545030, by rfl⟩ : syracuseStep 8726707 = 13090061) B13090061
theorem B4368563 : Blo 1132632 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B4598147 : Blo 1132632 4598147 := bstep (se 1 (by rfl) ⟨3448610, by rfl⟩ : syracuseStep 4598147 = 6897221) B6897221
theorem B36743651 : Blo 1132632 36743651 := bstep (se 1 (by rfl) ⟨27557738, by rfl⟩ : syracuseStep 36743651 = 55115477) B55115477
theorem B70724189 : Blo 1132632 70724189 := bstep (se 3 (by rfl) ⟨13260785, by rfl⟩ : syracuseStep 70724189 = 26521571) B26521571
theorem B31074947 : Blo 1132632 31074947 := bstep (se 1 (by rfl) ⟨23306210, by rfl⟩ : syracuseStep 31074947 = 46612421) B46612421
theorem B1911755 : Blo 1132632 1911755 := bstep (se 1 (by rfl) ⟨1433816, by rfl⟩ : syracuseStep 1911755 = 2867633) B2867633
theorem B8170445 : Blo 1132632 8170445 := bstep (se 3 (by rfl) ⟨1531958, by rfl⟩ : syracuseStep 8170445 = 3063917) B3063917
theorem B24849443 : Blo 1132632 24849443 := bstep (se 1 (by rfl) ⟨18637082, by rfl⟩ : syracuseStep 24849443 = 37274165) B37274165
theorem B1911883 : Blo 1132632 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B5745815 : Blo 1132632 5745815 := bstep (se 1 (by rfl) ⟨4309361, by rfl⟩ : syracuseStep 5745815 = 8618723) B8618723
theorem B2043073 : Blo 1132632 2043073 := bstep (se 2 (by rfl) ⟨766152, by rfl⟩ : syracuseStep 2043073 = 1532305) B1532305
theorem B1912025 : Blo 1132632 1912025 := bstep (se 2 (by rfl) ⟨717009, by rfl⟩ : syracuseStep 1912025 = 1434019) B1434019
theorem B1912153 : Blo 1132632 1912153 := bstep (se 2 (by rfl) ⟨717057, by rfl⟩ : syracuseStep 1912153 = 1434115) B1434115
theorem B1617241 : Blo 1132632 1617241 := bstep (se 2 (by rfl) ⟨606465, by rfl⟩ : syracuseStep 1617241 = 1212931) B1212931
theorem B1617355 : Blo 1132632 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B2043649 : Blo 1132632 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B1912727 : Blo 1132632 1912727 := bstep (se 1 (by rfl) ⟨1434545, by rfl⟩ : syracuseStep 1912727 = 2869091) B2869091
theorem B1814489 : Blo 1132632 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B1912855 : Blo 1132632 1912855 := bstep (se 1 (by rfl) ⟨1434641, by rfl⟩ : syracuseStep 1912855 = 2869283) B2869283
theorem B1913483 : Blo 1132632 1913483 := bstep (se 1 (by rfl) ⟨1435112, by rfl⟩ : syracuseStep 1913483 = 2870225) B2870225
theorem B9187991 : Blo 1132632 9187991 := bstep (se 1 (by rfl) ⟨6890993, by rfl⟩ : syracuseStep 9187991 = 13781987) B13781987
theorem B1815193 : Blo 1132632 1815193 := bstep (se 2 (by rfl) ⟨680697, by rfl⟩ : syracuseStep 1815193 = 1361395) B1361395
theorem B4305581 : Blo 1132632 4305581 := bstep (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) B1614593
theorem B1913611 : Blo 1132632 1913611 := bstep (se 1 (by rfl) ⟨1435208, by rfl⟩ : syracuseStep 1913611 = 2870417) B2870417
theorem B19411811 : Blo 1132632 19411811 := bstep (se 1 (by rfl) ⟨14558858, by rfl⟩ : syracuseStep 19411811 = 29117717) B29117717
theorem B1913753 : Blo 1132632 1913753 := bstep (se 2 (by rfl) ⟨717657, by rfl⟩ : syracuseStep 1913753 = 1435315) B1435315
theorem B1913881 : Blo 1132632 1913881 := bstep (se 2 (by rfl) ⟨717705, by rfl⟩ : syracuseStep 1913881 = 1435411) B1435411
theorem B4601261 : Blo 1132632 4601261 := bstep (se 3 (by rfl) ⟨862736, by rfl⟩ : syracuseStep 4601261 = 1725473) B1725473
theorem B4306355 : Blo 1132632 4306355 := bstep (se 1 (by rfl) ⟨3229766, by rfl⟩ : syracuseStep 4306355 = 6459533) B6459533
theorem B1914455 : Blo 1132632 1914455 := bstep (se 1 (by rfl) ⟨1435841, by rfl⟩ : syracuseStep 1914455 = 2871683) B2871683
theorem B1914583 : Blo 1132632 1914583 := bstep (se 1 (by rfl) ⟨1435937, by rfl⟩ : syracuseStep 1914583 = 2871875) B2871875
theorem B2045783 : Blo 1132632 2045783 := bstep (se 1 (by rfl) ⟨1534337, by rfl⟩ : syracuseStep 2045783 = 3068675) B3068675
theorem B3225689 : Blo 1132632 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B1915211 : Blo 1132632 1915211 := bstep (se 1 (by rfl) ⟨1436408, by rfl⟩ : syracuseStep 1915211 = 2872817) B2872817
theorem B1292663 : Blo 1132632 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B3226007 : Blo 1132632 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B1915339 : Blo 1132632 1915339 := bstep (se 1 (by rfl) ⟨1436504, by rfl⟩ : syracuseStep 1915339 = 2873009) B2873009
theorem B2046475 : Blo 1132632 2046475 := bstep (se 1 (by rfl) ⟨1534856, by rfl⟩ : syracuseStep 2046475 = 3069713) B3069713
theorem B1915481 : Blo 1132632 1915481 := bstep (se 2 (by rfl) ⟨718305, by rfl⟩ : syracuseStep 1915481 = 1436611) B1436611
theorem B16366211 : Blo 1132632 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B5749379 : Blo 1132632 5749379 := bstep (se 1 (by rfl) ⟨4312034, by rfl⟩ : syracuseStep 5749379 = 8624069) B8624069
theorem B14006915 : Blo 1132632 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B18430669 : Blo 1132632 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B1915609 : Blo 1132632 1915609 := bstep (se 2 (by rfl) ⟨718353, by rfl⟩ : syracuseStep 1915609 = 1436707) B1436707
theorem B2046721 : Blo 1132632 2046721 := bstep (se 2 (by rfl) ⟨767520, by rfl⟩ : syracuseStep 2046721 = 1535041) B1535041
theorem B4307843 : Blo 1132632 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B3456179 : Blo 1132632 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B3226817 : Blo 1132632 3226817 := bstep (se 2 (by rfl) ⟨1210056, by rfl⟩ : syracuseStep 3226817 = 2420113) B2420113
theorem B1916183 : Blo 1132632 1916183 := bstep (se 1 (by rfl) ⟨1437137, by rfl⟩ : syracuseStep 1916183 = 2874275) B2874275
theorem B2047283 : Blo 1132632 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B4308299 : Blo 1132632 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B1916311 : Blo 1132632 1916311 := bstep (se 1 (by rfl) ⟨1437233, by rfl⟩ : syracuseStep 1916311 = 2874467) B2874467
theorem B4308497 : Blo 1132632 4308497 := bstep (se 2 (by rfl) ⟨1615686, by rfl⟩ : syracuseStep 4308497 = 3231373) B3231373
theorem B1818263 : Blo 1132632 1818263 := bstep (se 1 (by rfl) ⟨1363697, by rfl⟩ : syracuseStep 1818263 = 2727395) B2727395
theorem B4374317 : Blo 1132632 4374317 := bstep (se 3 (by rfl) ⟨820184, by rfl⟩ : syracuseStep 4374317 = 1640369) B1640369
theorem B3063703 : Blo 1132632 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B2867147 : Blo 1132632 2867147 := bstep (se 1 (by rfl) ⟨2150360, by rfl⟩ : syracuseStep 2867147 = 4300721) B4300721
theorem B1916939 : Blo 1132632 1916939 := bstep (se 1 (by rfl) ⟨1437704, by rfl⟩ : syracuseStep 1916939 = 2875409) B2875409
theorem B6471697 : Blo 1132632 6471697 := bstep (se 2 (by rfl) ⟨2426886, by rfl⟩ : syracuseStep 6471697 = 4853773) B4853773
theorem B18432035 : Blo 1132632 18432035 := bstep (se 1 (by rfl) ⟨13824026, by rfl⟩ : syracuseStep 18432035 = 27648053) B27648053
theorem B7356509 : Blo 1132632 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B1917067 : Blo 1132632 1917067 := bstep (se 1 (by rfl) ⟨1437800, by rfl⟩ : syracuseStep 1917067 = 2875601) B2875601
theorem B4309271 : Blo 1132632 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B1917209 : Blo 1132632 1917209 := bstep (se 2 (by rfl) ⟨718953, by rfl⟩ : syracuseStep 1917209 = 1437907) B1437907
theorem B2867521 : Blo 1132632 2867521 := bstep (se 2 (by rfl) ⟨1075320, by rfl⟩ : syracuseStep 2867521 = 2150641) B2150641
theorem B1917337 : Blo 1132632 1917337 := bstep (se 2 (by rfl) ⟨719001, by rfl⟩ : syracuseStep 1917337 = 1438003) B1438003
theorem B14729651 : Blo 1132632 14729651 := bstep (se 1 (by rfl) ⟨11047238, by rfl⟩ : syracuseStep 14729651 = 22094477) B22094477
theorem B4309469 : Blo 1132632 4309469 := bstep (se 3 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 4309469 = 1616051) B1616051
theorem B3228491 : Blo 1132632 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B2868119 : Blo 1132632 2868119 := bstep (se 1 (by rfl) ⟨2151089, by rfl⟩ : syracuseStep 2868119 = 4302179) B4302179
theorem B1917911 : Blo 1132632 1917911 := bstep (se 1 (by rfl) ⟨1438433, by rfl⟩ : syracuseStep 1917911 = 2876867) B2876867
theorem B25183307 : Blo 1132632 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B1918039 : Blo 1132632 1918039 := bstep (se 1 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 1918039 = 2877059) B2877059
theorem B34915697 : Blo 1132632 34915697 := bstep (se 2 (by rfl) ⟨13093386, by rfl⟩ : syracuseStep 34915697 = 26186773) B26186773
theorem B7259543 : Blo 1132632 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B8603171 : Blo 1132632 8603171 := bstep (se 1 (by rfl) ⟨6452378, by rfl⟩ : syracuseStep 8603171 = 12904757) B12904757
theorem B2868929 : Blo 1132632 2868929 := bstep (se 2 (by rfl) ⟨1075848, by rfl⟩ : syracuseStep 2868929 = 2151697) B2151697
theorem B8275729 : Blo 1132632 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B5457881 : Blo 1132632 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B1722379 : Blo 1132632 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B4605997 : Blo 1132632 4605997 := bstep (se 3 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 4605997 = 1727249) B1727249
theorem B3229789 : Blo 1132632 3229789 := bstep (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) B1211171
theorem B1132651 : Blo 1132632 1132651 := bstep (se 1 (by rfl) ⟨849488, by rfl⟩ : syracuseStep 1132651 = 1698977) B1698977
theorem B1132663 : Blo 1132632 1132663 := bstep (se 1 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 1132663 = 1698995) B1698995
theorem B1132683 : Blo 1132632 1132683 := bstep (se 1 (by rfl) ⟨849512, by rfl⟩ : syracuseStep 1132683 = 1699025) B1699025
theorem B1132695 : Blo 1132632 1132695 := bstep (se 1 (by rfl) ⟨849521, by rfl⟩ : syracuseStep 1132695 = 1699043) B1699043
theorem B1132715 : Blo 1132632 1132715 := bstep (se 1 (by rfl) ⟨849536, by rfl⟩ : syracuseStep 1132715 = 1699073) B1699073
theorem B1132727 : Blo 1132632 1132727 := bstep (se 1 (by rfl) ⟨849545, by rfl⟩ : syracuseStep 1132727 = 1699091) B1699091
theorem B1132747 : Blo 1132632 1132747 := bstep (se 1 (by rfl) ⟨849560, by rfl⟩ : syracuseStep 1132747 = 1699121) B1699121
theorem B1132759 : Blo 1132632 1132759 := bstep (se 1 (by rfl) ⟨849569, by rfl⟩ : syracuseStep 1132759 = 1699139) B1699139
theorem B2869465 : Blo 1132632 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B1132779 : Blo 1132632 1132779 := bstep (se 1 (by rfl) ⟨849584, by rfl⟩ : syracuseStep 1132779 = 1699169) B1699169
theorem B1132791 : Blo 1132632 1132791 := bstep (se 1 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 1132791 = 1699187) B1699187
theorem B1132811 : Blo 1132632 1132811 := bstep (se 1 (by rfl) ⟨849608, by rfl⟩ : syracuseStep 1132811 = 1699217) B1699217
theorem B5753105 : Blo 1132632 5753105 := bstep (se 2 (by rfl) ⟨2157414, by rfl⟩ : syracuseStep 5753105 = 4314829) B4314829
theorem B1132823 : Blo 1132632 1132823 := bstep (se 1 (by rfl) ⟨849617, by rfl⟩ : syracuseStep 1132823 = 1699235) B1699235
theorem B1132843 : Blo 1132632 1132843 := bstep (se 1 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 1132843 = 1699265) B1699265
theorem B1132855 : Blo 1132632 1132855 := bstep (se 1 (by rfl) ⟨849641, by rfl⟩ : syracuseStep 1132855 = 1699283) B1699283
theorem B6637889 : Blo 1132632 6637889 := bstep (se 2 (by rfl) ⟨2489208, by rfl⟩ : syracuseStep 6637889 = 4978417) B4978417
theorem B1132875 : Blo 1132632 1132875 := bstep (se 1 (by rfl) ⟨849656, by rfl⟩ : syracuseStep 1132875 = 1699313) B1699313
theorem B1132887 : Blo 1132632 1132887 := bstep (se 1 (by rfl) ⟨849665, by rfl⟩ : syracuseStep 1132887 = 1699331) B1699331
theorem B1132907 : Blo 1132632 1132907 := bstep (se 1 (by rfl) ⟨849680, by rfl⟩ : syracuseStep 1132907 = 1699361) B1699361
theorem B1132919 : Blo 1132632 1132919 := bstep (se 1 (by rfl) ⟨849689, by rfl⟩ : syracuseStep 1132919 = 1699379) B1699379
theorem B4311427 : Blo 1132632 4311427 := bstep (se 1 (by rfl) ⟨3233570, by rfl⟩ : syracuseStep 4311427 = 6467141) B6467141
theorem B1132939 : Blo 1132632 1132939 := bstep (se 1 (by rfl) ⟨849704, by rfl⟩ : syracuseStep 1132939 = 1699409) B1699409
theorem B1132951 : Blo 1132632 1132951 := bstep (se 1 (by rfl) ⟨849713, by rfl⟩ : syracuseStep 1132951 = 1699427) B1699427
theorem B1132971 : Blo 1132632 1132971 := bstep (se 1 (by rfl) ⟨849728, by rfl⟩ : syracuseStep 1132971 = 1699457) B1699457
theorem B3230131 : Blo 1132632 3230131 := bstep (se 1 (by rfl) ⟨2422598, by rfl⟩ : syracuseStep 3230131 = 4845197) B4845197
theorem B5753267 : Blo 1132632 5753267 := bstep (se 1 (by rfl) ⟨4314950, by rfl⟩ : syracuseStep 5753267 = 8629901) B8629901
theorem B1132983 : Blo 1132632 1132983 := bstep (se 1 (by rfl) ⟨849737, by rfl⟩ : syracuseStep 1132983 = 1699475) B1699475
theorem B1133003 : Blo 1132632 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B1133015 : Blo 1132632 1133015 := bstep (se 1 (by rfl) ⟨849761, by rfl⟩ : syracuseStep 1133015 = 1699523) B1699523
theorem B1133035 : Blo 1132632 1133035 := bstep (se 1 (by rfl) ⟨849776, by rfl⟩ : syracuseStep 1133035 = 1699553) B1699553
theorem B1133047 : Blo 1132632 1133047 := bstep (se 1 (by rfl) ⟨849785, by rfl⟩ : syracuseStep 1133047 = 1699571) B1699571
theorem B1133067 : Blo 1132632 1133067 := bstep (se 1 (by rfl) ⟨849800, by rfl⟩ : syracuseStep 1133067 = 1699601) B1699601
theorem B1133079 : Blo 1132632 1133079 := bstep (se 1 (by rfl) ⟨849809, by rfl⟩ : syracuseStep 1133079 = 1699619) B1699619
theorem B1133099 : Blo 1132632 1133099 := bstep (se 1 (by rfl) ⟨849824, by rfl⟩ : syracuseStep 1133099 = 1699649) B1699649
theorem B1133111 : Blo 1132632 1133111 := bstep (se 1 (by rfl) ⟨849833, by rfl⟩ : syracuseStep 1133111 = 1699667) B1699667
theorem B1133131 : Blo 1132632 1133131 := bstep (se 1 (by rfl) ⟨849848, by rfl⟩ : syracuseStep 1133131 = 1699697) B1699697
theorem B1133143 : Blo 1132632 1133143 := bstep (se 1 (by rfl) ⟨849857, by rfl⟩ : syracuseStep 1133143 = 1699715) B1699715
theorem B1133163 : Blo 1132632 1133163 := bstep (se 1 (by rfl) ⟨849872, by rfl⟩ : syracuseStep 1133163 = 1699745) B1699745
theorem B1133175 : Blo 1132632 1133175 := bstep (se 1 (by rfl) ⟨849881, by rfl⟩ : syracuseStep 1133175 = 1699763) B1699763
theorem B1133195 : Blo 1132632 1133195 := bstep (se 1 (by rfl) ⟨849896, by rfl⟩ : syracuseStep 1133195 = 1699793) B1699793
theorem B1133207 : Blo 1132632 1133207 := bstep (se 1 (by rfl) ⟨849905, by rfl⟩ : syracuseStep 1133207 = 1699811) B1699811
theorem B1133227 : Blo 1132632 1133227 := bstep (se 1 (by rfl) ⟨849920, by rfl⟩ : syracuseStep 1133227 = 1699841) B1699841
theorem B4311731 : Blo 1132632 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B1133239 : Blo 1132632 1133239 := bstep (se 1 (by rfl) ⟨849929, by rfl⟩ : syracuseStep 1133239 = 1699859) B1699859
theorem B1133259 : Blo 1132632 1133259 := bstep (se 1 (by rfl) ⟨849944, by rfl⟩ : syracuseStep 1133259 = 1699889) B1699889
theorem B1133271 : Blo 1132632 1133271 := bstep (se 1 (by rfl) ⟨849953, by rfl⟩ : syracuseStep 1133271 = 1699907) B1699907
theorem B1133291 : Blo 1132632 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B1133303 : Blo 1132632 1133303 := bstep (se 1 (by rfl) ⟨849977, by rfl⟩ : syracuseStep 1133303 = 1699955) B1699955
theorem B1133323 : Blo 1132632 1133323 := bstep (se 1 (by rfl) ⟨849992, by rfl⟩ : syracuseStep 1133323 = 1699985) B1699985
theorem B1133335 : Blo 1132632 1133335 := bstep (se 1 (by rfl) ⟨850001, by rfl⟩ : syracuseStep 1133335 = 1700003) B1700003
theorem B1133355 : Blo 1132632 1133355 := bstep (se 1 (by rfl) ⟨850016, by rfl⟩ : syracuseStep 1133355 = 1700033) B1700033
theorem B1133367 : Blo 1132632 1133367 := bstep (se 1 (by rfl) ⟨850025, by rfl⟩ : syracuseStep 1133367 = 1700051) B1700051
theorem B1133387 : Blo 1132632 1133387 := bstep (se 1 (by rfl) ⟨850040, by rfl⟩ : syracuseStep 1133387 = 1700081) B1700081
theorem B1133399 : Blo 1132632 1133399 := bstep (se 1 (by rfl) ⟨850049, by rfl⟩ : syracuseStep 1133399 = 1700099) B1700099
theorem B1133419 : Blo 1132632 1133419 := bstep (se 1 (by rfl) ⟨850064, by rfl⟩ : syracuseStep 1133419 = 1700129) B1700129
theorem B1133431 : Blo 1132632 1133431 := bstep (se 1 (by rfl) ⟨850073, by rfl⟩ : syracuseStep 1133431 = 1700147) B1700147
theorem B1133451 : Blo 1132632 1133451 := bstep (se 1 (by rfl) ⟨850088, by rfl⟩ : syracuseStep 1133451 = 1700177) B1700177
theorem B1133463 : Blo 1132632 1133463 := bstep (se 1 (by rfl) ⟨850097, by rfl⟩ : syracuseStep 1133463 = 1700195) B1700195
theorem B1133483 : Blo 1132632 1133483 := bstep (se 1 (by rfl) ⟨850112, by rfl⟩ : syracuseStep 1133483 = 1700225) B1700225
theorem B1133495 : Blo 1132632 1133495 := bstep (se 1 (by rfl) ⟨850121, by rfl⟩ : syracuseStep 1133495 = 1700243) B1700243
theorem B1133515 : Blo 1132632 1133515 := bstep (se 1 (by rfl) ⟨850136, by rfl⟩ : syracuseStep 1133515 = 1700273) B1700273
theorem B1133527 : Blo 1132632 1133527 := bstep (se 1 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 1133527 = 1700291) B1700291
theorem B1133547 : Blo 1132632 1133547 := bstep (se 1 (by rfl) ⟨850160, by rfl⟩ : syracuseStep 1133547 = 1700321) B1700321
theorem B1133559 : Blo 1132632 1133559 := bstep (se 1 (by rfl) ⟨850169, by rfl⟩ : syracuseStep 1133559 = 1700339) B1700339
theorem B1133579 : Blo 1132632 1133579 := bstep (se 1 (by rfl) ⟨850184, by rfl⟩ : syracuseStep 1133579 = 1700369) B1700369
theorem B1133591 : Blo 1132632 1133591 := bstep (se 1 (by rfl) ⟨850193, by rfl⟩ : syracuseStep 1133591 = 1700387) B1700387
theorem B1133611 : Blo 1132632 1133611 := bstep (se 1 (by rfl) ⟨850208, by rfl⟩ : syracuseStep 1133611 = 1700417) B1700417
theorem B1133623 : Blo 1132632 1133623 := bstep (se 1 (by rfl) ⟨850217, by rfl⟩ : syracuseStep 1133623 = 1700435) B1700435
theorem B1133643 : Blo 1132632 1133643 := bstep (se 1 (by rfl) ⟨850232, by rfl⟩ : syracuseStep 1133643 = 1700465) B1700465
theorem B1133655 : Blo 1132632 1133655 := bstep (se 1 (by rfl) ⟨850241, by rfl⟩ : syracuseStep 1133655 = 1700483) B1700483
theorem B7261285 : Blo 1132632 7261285 := bstep (se 4 (by rfl) ⟨680745, by rfl⟩ : syracuseStep 7261285 = 1361491) B1361491
theorem B1133675 : Blo 1132632 1133675 := bstep (se 1 (by rfl) ⟨850256, by rfl⟩ : syracuseStep 1133675 = 1700513) B1700513
theorem B1133687 : Blo 1132632 1133687 := bstep (se 1 (by rfl) ⟨850265, by rfl⟩ : syracuseStep 1133687 = 1700531) B1700531
theorem B1133707 : Blo 1132632 1133707 := bstep (se 1 (by rfl) ⟨850280, by rfl⟩ : syracuseStep 1133707 = 1700561) B1700561
theorem B1133719 : Blo 1132632 1133719 := bstep (se 1 (by rfl) ⟨850289, by rfl⟩ : syracuseStep 1133719 = 1700579) B1700579
theorem B1133739 : Blo 1132632 1133739 := bstep (se 1 (by rfl) ⟨850304, by rfl⟩ : syracuseStep 1133739 = 1700609) B1700609
theorem B1133751 : Blo 1132632 1133751 := bstep (se 1 (by rfl) ⟨850313, by rfl⟩ : syracuseStep 1133751 = 1700627) B1700627
theorem B1133771 : Blo 1132632 1133771 := bstep (se 1 (by rfl) ⟨850328, by rfl⟩ : syracuseStep 1133771 = 1700657) B1700657
theorem B1133783 : Blo 1132632 1133783 := bstep (se 1 (by rfl) ⟨850337, by rfl⟩ : syracuseStep 1133783 = 1700675) B1700675
theorem B1363159 : Blo 1132632 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B1133803 : Blo 1132632 1133803 := bstep (se 1 (by rfl) ⟨850352, by rfl⟩ : syracuseStep 1133803 = 1700705) B1700705
theorem B1133815 : Blo 1132632 1133815 := bstep (se 1 (by rfl) ⟨850361, by rfl⟩ : syracuseStep 1133815 = 1700723) B1700723
theorem B1133835 : Blo 1132632 1133835 := bstep (se 1 (by rfl) ⟨850376, by rfl⟩ : syracuseStep 1133835 = 1700753) B1700753
theorem B1133847 : Blo 1132632 1133847 := bstep (se 1 (by rfl) ⟨850385, by rfl⟩ : syracuseStep 1133847 = 1700771) B1700771
theorem B1133867 : Blo 1132632 1133867 := bstep (se 1 (by rfl) ⟨850400, by rfl⟩ : syracuseStep 1133867 = 1700801) B1700801
theorem B2870579 : Blo 1132632 2870579 := bstep (se 1 (by rfl) ⟨2152934, by rfl⟩ : syracuseStep 2870579 = 4305869) B4305869
theorem B1133879 : Blo 1132632 1133879 := bstep (se 1 (by rfl) ⟨850409, by rfl⟩ : syracuseStep 1133879 = 1700819) B1700819
theorem B4312385 : Blo 1132632 4312385 := bstep (se 2 (by rfl) ⟨1617144, by rfl⟩ : syracuseStep 4312385 = 3234289) B3234289
theorem B1133899 : Blo 1132632 1133899 := bstep (se 1 (by rfl) ⟨850424, by rfl⟩ : syracuseStep 1133899 = 1700849) B1700849
theorem B1133911 : Blo 1132632 1133911 := bstep (se 1 (by rfl) ⟨850433, by rfl⟩ : syracuseStep 1133911 = 1700867) B1700867
theorem B3231065 : Blo 1132632 3231065 := bstep (se 2 (by rfl) ⟨1211649, by rfl⟩ : syracuseStep 3231065 = 2423299) B2423299
theorem B1133931 : Blo 1132632 1133931 := bstep (se 1 (by rfl) ⟨850448, by rfl⟩ : syracuseStep 1133931 = 1700897) B1700897
theorem B1133943 : Blo 1132632 1133943 := bstep (se 1 (by rfl) ⟨850457, by rfl⟩ : syracuseStep 1133943 = 1700915) B1700915
theorem B1133963 : Blo 1132632 1133963 := bstep (se 1 (by rfl) ⟨850472, by rfl⟩ : syracuseStep 1133963 = 1700945) B1700945
theorem B1133975 : Blo 1132632 1133975 := bstep (se 1 (by rfl) ⟨850481, by rfl⟩ : syracuseStep 1133975 = 1700963) B1700963
theorem B1133995 : Blo 1132632 1133995 := bstep (se 1 (by rfl) ⟨850496, by rfl⟩ : syracuseStep 1133995 = 1700993) B1700993
theorem B1134007 : Blo 1132632 1134007 := bstep (se 1 (by rfl) ⟨850505, by rfl⟩ : syracuseStep 1134007 = 1701011) B1701011
theorem B1134027 : Blo 1132632 1134027 := bstep (se 1 (by rfl) ⟨850520, by rfl⟩ : syracuseStep 1134027 = 1701041) B1701041
theorem B1134039 : Blo 1132632 1134039 := bstep (se 1 (by rfl) ⟨850529, by rfl⟩ : syracuseStep 1134039 = 1701059) B1701059
theorem B1134059 : Blo 1132632 1134059 := bstep (se 1 (by rfl) ⟨850544, by rfl⟩ : syracuseStep 1134059 = 1701089) B1701089
theorem B1134071 : Blo 1132632 1134071 := bstep (se 1 (by rfl) ⟨850553, by rfl⟩ : syracuseStep 1134071 = 1701107) B1701107
theorem B1134091 : Blo 1132632 1134091 := bstep (se 1 (by rfl) ⟨850568, by rfl⟩ : syracuseStep 1134091 = 1701137) B1701137
theorem B1134103 : Blo 1132632 1134103 := bstep (se 1 (by rfl) ⟨850577, by rfl⟩ : syracuseStep 1134103 = 1701155) B1701155
theorem B1134123 : Blo 1132632 1134123 := bstep (se 1 (by rfl) ⟨850592, by rfl⟩ : syracuseStep 1134123 = 1701185) B1701185
theorem B1134135 : Blo 1132632 1134135 := bstep (se 1 (by rfl) ⟨850601, by rfl⟩ : syracuseStep 1134135 = 1701203) B1701203
theorem B1134155 : Blo 1132632 1134155 := bstep (se 1 (by rfl) ⟨850616, by rfl⟩ : syracuseStep 1134155 = 1701233) B1701233
theorem B1134167 : Blo 1132632 1134167 := bstep (se 1 (by rfl) ⟨850625, by rfl⟩ : syracuseStep 1134167 = 1701251) B1701251
theorem B2870873 : Blo 1132632 2870873 := bstep (se 2 (by rfl) ⟨1076577, by rfl⟩ : syracuseStep 2870873 = 2153155) B2153155
theorem B1134187 : Blo 1132632 1134187 := bstep (se 1 (by rfl) ⟨850640, by rfl⟩ : syracuseStep 1134187 = 1701281) B1701281
theorem B1134199 : Blo 1132632 1134199 := bstep (se 1 (by rfl) ⟨850649, by rfl⟩ : syracuseStep 1134199 = 1701299) B1701299
theorem B1134219 : Blo 1132632 1134219 := bstep (se 1 (by rfl) ⟨850664, by rfl⟩ : syracuseStep 1134219 = 1701329) B1701329
theorem B1134231 : Blo 1132632 1134231 := bstep (se 1 (by rfl) ⟨850673, by rfl⟩ : syracuseStep 1134231 = 1701347) B1701347
theorem B1134251 : Blo 1132632 1134251 := bstep (se 1 (by rfl) ⟨850688, by rfl⟩ : syracuseStep 1134251 = 1701377) B1701377
theorem B1134263 : Blo 1132632 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B1134283 : Blo 1132632 1134283 := bstep (se 1 (by rfl) ⟨850712, by rfl⟩ : syracuseStep 1134283 = 1701425) B1701425
theorem B1134295 : Blo 1132632 1134295 := bstep (se 1 (by rfl) ⟨850721, by rfl⟩ : syracuseStep 1134295 = 1701443) B1701443
theorem B1134315 : Blo 1132632 1134315 := bstep (se 1 (by rfl) ⟨850736, by rfl⟩ : syracuseStep 1134315 = 1701473) B1701473
theorem B1134327 : Blo 1132632 1134327 := bstep (se 1 (by rfl) ⟨850745, by rfl⟩ : syracuseStep 1134327 = 1701491) B1701491
theorem B1134347 : Blo 1132632 1134347 := bstep (se 1 (by rfl) ⟨850760, by rfl⟩ : syracuseStep 1134347 = 1701521) B1701521
theorem B1134359 : Blo 1132632 1134359 := bstep (se 1 (by rfl) ⟨850769, by rfl⟩ : syracuseStep 1134359 = 1701539) B1701539
theorem B1134379 : Blo 1132632 1134379 := bstep (se 1 (by rfl) ⟨850784, by rfl⟩ : syracuseStep 1134379 = 1701569) B1701569
theorem B8179501 : Blo 1132632 8179501 := bstep (se 3 (by rfl) ⟨1533656, by rfl⟩ : syracuseStep 8179501 = 3067313) B3067313
theorem B1134391 : Blo 1132632 1134391 := bstep (se 1 (by rfl) ⟨850793, by rfl⟩ : syracuseStep 1134391 = 1701587) B1701587
theorem B3886913 : Blo 1132632 3886913 := bstep (se 2 (by rfl) ⟨1457592, by rfl⟩ : syracuseStep 3886913 = 2915185) B2915185
theorem B1134411 : Blo 1132632 1134411 := bstep (se 1 (by rfl) ⟨850808, by rfl⟩ : syracuseStep 1134411 = 1701617) B1701617
theorem B3067723 : Blo 1132632 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B1134423 : Blo 1132632 1134423 := bstep (se 1 (by rfl) ⟨850817, by rfl⟩ : syracuseStep 1134423 = 1701635) B1701635
theorem B18665315 : Blo 1132632 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B1134443 : Blo 1132632 1134443 := bstep (se 1 (by rfl) ⟨850832, by rfl⟩ : syracuseStep 1134443 = 1701665) B1701665
theorem B1134455 : Blo 1132632 1134455 := bstep (se 1 (by rfl) ⟨850841, by rfl⟩ : syracuseStep 1134455 = 1701683) B1701683
theorem B1134475 : Blo 1132632 1134475 := bstep (se 1 (by rfl) ⟨850856, by rfl⟩ : syracuseStep 1134475 = 1701713) B1701713
theorem B1134487 : Blo 1132632 1134487 := bstep (se 1 (by rfl) ⟨850865, by rfl⟩ : syracuseStep 1134487 = 1701731) B1701731
theorem B1134507 : Blo 1132632 1134507 := bstep (se 1 (by rfl) ⟨850880, by rfl⟩ : syracuseStep 1134507 = 1701761) B1701761
theorem B1134519 : Blo 1132632 1134519 := bstep (se 1 (by rfl) ⟨850889, by rfl⟩ : syracuseStep 1134519 = 1701779) B1701779
theorem B1134539 : Blo 1132632 1134539 := bstep (se 1 (by rfl) ⟨850904, by rfl⟩ : syracuseStep 1134539 = 1701809) B1701809
theorem B1134551 : Blo 1132632 1134551 := bstep (se 1 (by rfl) ⟨850913, by rfl⟩ : syracuseStep 1134551 = 1701827) B1701827
theorem B1134571 : Blo 1132632 1134571 := bstep (se 1 (by rfl) ⟨850928, by rfl⟩ : syracuseStep 1134571 = 1701857) B1701857
theorem B1134583 : Blo 1132632 1134583 := bstep (se 1 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 1134583 = 1701875) B1701875
theorem B1134603 : Blo 1132632 1134603 := bstep (se 1 (by rfl) ⟨850952, by rfl⟩ : syracuseStep 1134603 = 1701905) B1701905
theorem B1134615 : Blo 1132632 1134615 := bstep (se 1 (by rfl) ⟨850961, by rfl⟩ : syracuseStep 1134615 = 1701923) B1701923
theorem B1134635 : Blo 1132632 1134635 := bstep (se 1 (by rfl) ⟨850976, by rfl⟩ : syracuseStep 1134635 = 1701953) B1701953
theorem B1134647 : Blo 1132632 1134647 := bstep (se 1 (by rfl) ⟨850985, by rfl⟩ : syracuseStep 1134647 = 1701971) B1701971
theorem B1134667 : Blo 1132632 1134667 := bstep (se 1 (by rfl) ⟨851000, by rfl⟩ : syracuseStep 1134667 = 1702001) B1702001
theorem B1134679 : Blo 1132632 1134679 := bstep (se 1 (by rfl) ⟨851009, by rfl⟩ : syracuseStep 1134679 = 1702019) B1702019
theorem B2150489 : Blo 1132632 2150489 := bstep (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) B1612867
theorem B1134699 : Blo 1132632 1134699 := bstep (se 1 (by rfl) ⟨851024, by rfl⟩ : syracuseStep 1134699 = 1702049) B1702049
theorem B1134711 : Blo 1132632 1134711 := bstep (se 1 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 1134711 = 1702067) B1702067
theorem B1134731 : Blo 1132632 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B1134743 : Blo 1132632 1134743 := bstep (se 1 (by rfl) ⟨851057, by rfl⟩ : syracuseStep 1134743 = 1702115) B1702115
theorem B1134763 : Blo 1132632 1134763 := bstep (se 1 (by rfl) ⟨851072, by rfl⟩ : syracuseStep 1134763 = 1702145) B1702145
theorem B1134775 : Blo 1132632 1134775 := bstep (se 1 (by rfl) ⟨851081, by rfl⟩ : syracuseStep 1134775 = 1702163) B1702163
theorem B1134795 : Blo 1132632 1134795 := bstep (se 1 (by rfl) ⟨851096, by rfl⟩ : syracuseStep 1134795 = 1702193) B1702193
theorem B1134807 : Blo 1132632 1134807 := bstep (se 1 (by rfl) ⟨851105, by rfl⟩ : syracuseStep 1134807 = 1702211) B1702211
theorem B1134827 : Blo 1132632 1134827 := bstep (se 1 (by rfl) ⟨851120, by rfl⟩ : syracuseStep 1134827 = 1702241) B1702241
theorem B1134839 : Blo 1132632 1134839 := bstep (se 1 (by rfl) ⟨851129, by rfl⟩ : syracuseStep 1134839 = 1702259) B1702259
theorem B1134859 : Blo 1132632 1134859 := bstep (se 1 (by rfl) ⟨851144, by rfl⟩ : syracuseStep 1134859 = 1702289) B1702289
theorem B1134871 : Blo 1132632 1134871 := bstep (se 1 (by rfl) ⟨851153, by rfl⟩ : syracuseStep 1134871 = 1702307) B1702307
theorem B1134891 : Blo 1132632 1134891 := bstep (se 1 (by rfl) ⟨851168, by rfl⟩ : syracuseStep 1134891 = 1702337) B1702337
theorem B4084013 : Blo 1132632 4084013 := bstep (se 3 (by rfl) ⟨765752, by rfl⟩ : syracuseStep 4084013 = 1531505) B1531505
theorem B1134903 : Blo 1132632 1134903 := bstep (se 1 (by rfl) ⟨851177, by rfl⟩ : syracuseStep 1134903 = 1702355) B1702355
theorem B1134923 : Blo 1132632 1134923 := bstep (se 1 (by rfl) ⟨851192, by rfl⟩ : syracuseStep 1134923 = 1702385) B1702385
theorem B1134935 : Blo 1132632 1134935 := bstep (se 1 (by rfl) ⟨851201, by rfl⟩ : syracuseStep 1134935 = 1702403) B1702403
theorem B1134955 : Blo 1132632 1134955 := bstep (se 1 (by rfl) ⟨851216, by rfl⟩ : syracuseStep 1134955 = 1702433) B1702433
theorem B1134967 : Blo 1132632 1134967 := bstep (se 1 (by rfl) ⟨851225, by rfl⟩ : syracuseStep 1134967 = 1702451) B1702451
theorem B1134987 : Blo 1132632 1134987 := bstep (se 1 (by rfl) ⟨851240, by rfl⟩ : syracuseStep 1134987 = 1702481) B1702481
theorem B1134999 : Blo 1132632 1134999 := bstep (se 1 (by rfl) ⟨851249, by rfl⟩ : syracuseStep 1134999 = 1702499) B1702499
theorem B1135019 : Blo 1132632 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B7000499 : Blo 1132632 7000499 := bstep (se 1 (by rfl) ⟨5250374, by rfl⟩ : syracuseStep 7000499 = 10500749) B10500749
theorem B1135031 : Blo 1132632 1135031 := bstep (se 1 (by rfl) ⟨851273, by rfl⟩ : syracuseStep 1135031 = 1702547) B1702547
theorem B1135051 : Blo 1132632 1135051 := bstep (se 1 (by rfl) ⟨851288, by rfl⟩ : syracuseStep 1135051 = 1702577) B1702577
theorem B1135063 : Blo 1132632 1135063 := bstep (se 1 (by rfl) ⟨851297, by rfl⟩ : syracuseStep 1135063 = 1702595) B1702595
theorem B1135083 : Blo 1132632 1135083 := bstep (se 1 (by rfl) ⟨851312, by rfl⟩ : syracuseStep 1135083 = 1702625) B1702625
theorem B1135095 : Blo 1132632 1135095 := bstep (se 1 (by rfl) ⟨851321, by rfl⟩ : syracuseStep 1135095 = 1702643) B1702643
theorem B1135115 : Blo 1132632 1135115 := bstep (se 1 (by rfl) ⟨851336, by rfl⟩ : syracuseStep 1135115 = 1702673) B1702673
theorem B1135127 : Blo 1132632 1135127 := bstep (se 1 (by rfl) ⟨851345, by rfl⟩ : syracuseStep 1135127 = 1702691) B1702691
theorem B1135147 : Blo 1132632 1135147 := bstep (se 1 (by rfl) ⟨851360, by rfl⟩ : syracuseStep 1135147 = 1702721) B1702721
theorem B4313645 : Blo 1132632 4313645 := bstep (se 3 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 4313645 = 1617617) B1617617
theorem B1135159 : Blo 1132632 1135159 := bstep (se 1 (by rfl) ⟨851369, by rfl⟩ : syracuseStep 1135159 = 1702739) B1702739
theorem B1135179 : Blo 1132632 1135179 := bstep (se 1 (by rfl) ⟨851384, by rfl⟩ : syracuseStep 1135179 = 1702769) B1702769
theorem B4313675 : Blo 1132632 4313675 := bstep (se 1 (by rfl) ⟨3235256, by rfl⟩ : syracuseStep 4313675 = 6470513) B6470513
theorem B1135191 : Blo 1132632 1135191 := bstep (se 1 (by rfl) ⟨851393, by rfl⟩ : syracuseStep 1135191 = 1702787) B1702787
theorem B1135211 : Blo 1132632 1135211 := bstep (se 1 (by rfl) ⟨851408, by rfl⟩ : syracuseStep 1135211 = 1702817) B1702817
theorem B1135223 : Blo 1132632 1135223 := bstep (se 1 (by rfl) ⟨851417, by rfl⟩ : syracuseStep 1135223 = 1702835) B1702835
theorem B1135243 : Blo 1132632 1135243 := bstep (se 1 (by rfl) ⟨851432, by rfl⟩ : syracuseStep 1135243 = 1702865) B1702865
theorem B4838039 : Blo 1132632 4838039 := bstep (se 1 (by rfl) ⟨3628529, by rfl⟩ : syracuseStep 4838039 = 7257059) B7257059
theorem B1135255 : Blo 1132632 1135255 := bstep (se 1 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 1135255 = 1702883) B1702883
theorem B1135275 : Blo 1132632 1135275 := bstep (se 1 (by rfl) ⟨851456, by rfl⟩ : syracuseStep 1135275 = 1702913) B1702913
theorem B1135287 : Blo 1132632 1135287 := bstep (se 1 (by rfl) ⟨851465, by rfl⟩ : syracuseStep 1135287 = 1702931) B1702931
theorem B1135307 : Blo 1132632 1135307 := bstep (se 1 (by rfl) ⟨851480, by rfl⟩ : syracuseStep 1135307 = 1702961) B1702961
theorem B2151127 : Blo 1132632 2151127 := bstep (se 1 (by rfl) ⟨1613345, by rfl⟩ : syracuseStep 2151127 = 3226691) B3226691
theorem B1135319 : Blo 1132632 1135319 := bstep (se 1 (by rfl) ⟨851489, by rfl⟩ : syracuseStep 1135319 = 1702979) B1702979
theorem B4084445 : Blo 1132632 4084445 := bstep (se 3 (by rfl) ⟨765833, by rfl⟩ : syracuseStep 4084445 = 1531667) B1531667
theorem B3232477 : Blo 1132632 3232477 := bstep (se 3 (by rfl) ⟨606089, by rfl⟩ : syracuseStep 3232477 = 1212179) B1212179
theorem B1135339 : Blo 1132632 1135339 := bstep (se 1 (by rfl) ⟨851504, by rfl⟩ : syracuseStep 1135339 = 1703009) B1703009
theorem B1135351 : Blo 1132632 1135351 := bstep (se 1 (by rfl) ⟨851513, by rfl⟩ : syracuseStep 1135351 = 1703027) B1703027
theorem B1135371 : Blo 1132632 1135371 := bstep (se 1 (by rfl) ⟨851528, by rfl⟩ : syracuseStep 1135371 = 1703057) B1703057
theorem B1135383 : Blo 1132632 1135383 := bstep (se 1 (by rfl) ⟨851537, by rfl⟩ : syracuseStep 1135383 = 1703075) B1703075
theorem B1135403 : Blo 1132632 1135403 := bstep (se 1 (by rfl) ⟨851552, by rfl⟩ : syracuseStep 1135403 = 1703105) B1703105
theorem B10343213 : Blo 1132632 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B1135415 : Blo 1132632 1135415 := bstep (se 1 (by rfl) ⟨851561, by rfl⟩ : syracuseStep 1135415 = 1703123) B1703123
theorem B1135435 : Blo 1132632 1135435 := bstep (se 1 (by rfl) ⟨851576, by rfl⟩ : syracuseStep 1135435 = 1703153) B1703153
theorem B1135447 : Blo 1132632 1135447 := bstep (se 1 (by rfl) ⟨851585, by rfl⟩ : syracuseStep 1135447 = 1703171) B1703171
theorem B3068761 : Blo 1132632 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B1135467 : Blo 1132632 1135467 := bstep (se 1 (by rfl) ⟨851600, by rfl⟩ : syracuseStep 1135467 = 1703201) B1703201
theorem B1135479 : Blo 1132632 1135479 := bstep (se 1 (by rfl) ⟨851609, by rfl⟩ : syracuseStep 1135479 = 1703219) B1703219
theorem B1135499 : Blo 1132632 1135499 := bstep (se 1 (by rfl) ⟨851624, by rfl⟩ : syracuseStep 1135499 = 1703249) B1703249
theorem B1135511 : Blo 1132632 1135511 := bstep (se 1 (by rfl) ⟨851633, by rfl⟩ : syracuseStep 1135511 = 1703267) B1703267
theorem B1135531 : Blo 1132632 1135531 := bstep (se 1 (by rfl) ⟨851648, by rfl⟩ : syracuseStep 1135531 = 1703297) B1703297
theorem B1135543 : Blo 1132632 1135543 := bstep (se 1 (by rfl) ⟨851657, by rfl⟩ : syracuseStep 1135543 = 1703315) B1703315
theorem B3232705 : Blo 1132632 3232705 := bstep (se 2 (by rfl) ⟨1212264, by rfl⟩ : syracuseStep 3232705 = 2424529) B2424529
theorem B1135563 : Blo 1132632 1135563 := bstep (se 1 (by rfl) ⟨851672, by rfl⟩ : syracuseStep 1135563 = 1703345) B1703345
theorem B1135575 : Blo 1132632 1135575 := bstep (se 1 (by rfl) ⟨851681, by rfl⟩ : syracuseStep 1135575 = 1703363) B1703363
theorem B1725401 : Blo 1132632 1725401 := bstep (se 2 (by rfl) ⟨647025, by rfl⟩ : syracuseStep 1725401 = 1294051) B1294051
theorem B1135595 : Blo 1132632 1135595 := bstep (se 1 (by rfl) ⟨851696, by rfl⟩ : syracuseStep 1135595 = 1703393) B1703393
theorem B1135607 : Blo 1132632 1135607 := bstep (se 1 (by rfl) ⟨851705, by rfl⟩ : syracuseStep 1135607 = 1703411) B1703411
theorem B1135627 : Blo 1132632 1135627 := bstep (se 1 (by rfl) ⟨851720, by rfl⟩ : syracuseStep 1135627 = 1703441) B1703441
theorem B1135639 : Blo 1132632 1135639 := bstep (se 1 (by rfl) ⟨851729, by rfl⟩ : syracuseStep 1135639 = 1703459) B1703459
theorem B1135659 : Blo 1132632 1135659 := bstep (se 1 (by rfl) ⟨851744, by rfl⟩ : syracuseStep 1135659 = 1703489) B1703489
theorem B1135671 : Blo 1132632 1135671 := bstep (se 1 (by rfl) ⟨851753, by rfl⟩ : syracuseStep 1135671 = 1703507) B1703507
theorem B1135691 : Blo 1132632 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B1135703 : Blo 1132632 1135703 := bstep (se 1 (by rfl) ⟨851777, by rfl⟩ : syracuseStep 1135703 = 1703555) B1703555
theorem B1135723 : Blo 1132632 1135723 := bstep (se 1 (by rfl) ⟨851792, by rfl⟩ : syracuseStep 1135723 = 1703585) B1703585
theorem B1135735 : Blo 1132632 1135735 := bstep (se 1 (by rfl) ⟨851801, by rfl⟩ : syracuseStep 1135735 = 1703603) B1703603
theorem B1135755 : Blo 1132632 1135755 := bstep (se 1 (by rfl) ⟨851816, by rfl⟩ : syracuseStep 1135755 = 1703633) B1703633
theorem B1135767 : Blo 1132632 1135767 := bstep (se 1 (by rfl) ⟨851825, by rfl⟩ : syracuseStep 1135767 = 1703651) B1703651
theorem B1135787 : Blo 1132632 1135787 := bstep (se 1 (by rfl) ⟨851840, by rfl⟩ : syracuseStep 1135787 = 1703681) B1703681
theorem B1135799 : Blo 1132632 1135799 := bstep (se 1 (by rfl) ⟨851849, by rfl⟩ : syracuseStep 1135799 = 1703699) B1703699
theorem B2872523 : Blo 1132632 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B1135819 : Blo 1132632 1135819 := bstep (se 1 (by rfl) ⟨851864, by rfl⟩ : syracuseStep 1135819 = 1703729) B1703729
theorem B1135831 : Blo 1132632 1135831 := bstep (se 1 (by rfl) ⟨851873, by rfl⟩ : syracuseStep 1135831 = 1703747) B1703747
theorem B4314329 : Blo 1132632 4314329 := bstep (se 2 (by rfl) ⟨1617873, by rfl⟩ : syracuseStep 4314329 = 3235747) B3235747
theorem B1135851 : Blo 1132632 1135851 := bstep (se 1 (by rfl) ⟨851888, by rfl⟩ : syracuseStep 1135851 = 1703777) B1703777
theorem B1135863 : Blo 1132632 1135863 := bstep (se 1 (by rfl) ⟨851897, by rfl⟩ : syracuseStep 1135863 = 1703795) B1703795
theorem B1135883 : Blo 1132632 1135883 := bstep (se 1 (by rfl) ⟨851912, by rfl⟩ : syracuseStep 1135883 = 1703825) B1703825
theorem B3233047 : Blo 1132632 3233047 := bstep (se 1 (by rfl) ⟨2424785, by rfl⟩ : syracuseStep 3233047 = 4849571) B4849571
theorem B1135895 : Blo 1132632 1135895 := bstep (se 1 (by rfl) ⟨851921, by rfl⟩ : syracuseStep 1135895 = 1703843) B1703843
theorem B1135915 : Blo 1132632 1135915 := bstep (se 1 (by rfl) ⟨851936, by rfl⟩ : syracuseStep 1135915 = 1703873) B1703873
theorem B1135927 : Blo 1132632 1135927 := bstep (se 1 (by rfl) ⟨851945, by rfl⟩ : syracuseStep 1135927 = 1703891) B1703891
theorem B1135947 : Blo 1132632 1135947 := bstep (se 1 (by rfl) ⟨851960, by rfl⟩ : syracuseStep 1135947 = 1703921) B1703921
theorem B1135959 : Blo 1132632 1135959 := bstep (se 1 (by rfl) ⟨851969, by rfl⟩ : syracuseStep 1135959 = 1703939) B1703939
theorem B1135979 : Blo 1132632 1135979 := bstep (se 1 (by rfl) ⟨851984, by rfl⟩ : syracuseStep 1135979 = 1703969) B1703969
theorem B1135991 : Blo 1132632 1135991 := bstep (se 1 (by rfl) ⟨851993, by rfl⟩ : syracuseStep 1135991 = 1703987) B1703987
theorem B1136011 : Blo 1132632 1136011 := bstep (se 1 (by rfl) ⟨852008, by rfl⟩ : syracuseStep 1136011 = 1704017) B1704017
theorem B1136023 : Blo 1132632 1136023 := bstep (se 1 (by rfl) ⟨852017, by rfl⟩ : syracuseStep 1136023 = 1704035) B1704035
theorem B1136043 : Blo 1132632 1136043 := bstep (se 1 (by rfl) ⟨852032, by rfl⟩ : syracuseStep 1136043 = 1704065) B1704065
theorem B1136055 : Blo 1132632 1136055 := bstep (se 1 (by rfl) ⟨852041, by rfl⟩ : syracuseStep 1136055 = 1704083) B1704083
theorem B1136075 : Blo 1132632 1136075 := bstep (se 1 (by rfl) ⟨852056, by rfl⟩ : syracuseStep 1136075 = 1704113) B1704113
theorem B1136087 : Blo 1132632 1136087 := bstep (se 1 (by rfl) ⟨852065, by rfl⟩ : syracuseStep 1136087 = 1704131) B1704131
theorem B1136107 : Blo 1132632 1136107 := bstep (se 1 (by rfl) ⟨852080, by rfl⟩ : syracuseStep 1136107 = 1704161) B1704161
theorem B1136119 : Blo 1132632 1136119 := bstep (se 1 (by rfl) ⟨852089, by rfl⟩ : syracuseStep 1136119 = 1704179) B1704179
theorem B2151947 : Blo 1132632 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B1136139 : Blo 1132632 1136139 := bstep (se 1 (by rfl) ⟨852104, by rfl⟩ : syracuseStep 1136139 = 1704209) B1704209
theorem B1136151 : Blo 1132632 1136151 := bstep (se 1 (by rfl) ⟨852113, by rfl⟩ : syracuseStep 1136151 = 1704227) B1704227
theorem B4314647 : Blo 1132632 4314647 := bstep (se 1 (by rfl) ⟨3235985, by rfl⟩ : syracuseStep 4314647 = 6471971) B6471971
theorem B1136171 : Blo 1132632 1136171 := bstep (se 1 (by rfl) ⟨852128, by rfl⟩ : syracuseStep 1136171 = 1704257) B1704257
theorem B1136183 : Blo 1132632 1136183 := bstep (se 1 (by rfl) ⟨852137, by rfl⟩ : syracuseStep 1136183 = 1704275) B1704275
theorem B2152001 : Blo 1132632 2152001 := bstep (se 2 (by rfl) ⟨807000, by rfl⟩ : syracuseStep 2152001 = 1614001) B1614001
theorem B1136203 : Blo 1132632 1136203 := bstep (se 1 (by rfl) ⟨852152, by rfl⟩ : syracuseStep 1136203 = 1704305) B1704305
theorem B1136215 : Blo 1132632 1136215 := bstep (se 1 (by rfl) ⟨852161, by rfl⟩ : syracuseStep 1136215 = 1704323) B1704323
theorem B1136235 : Blo 1132632 1136235 := bstep (se 1 (by rfl) ⟨852176, by rfl⟩ : syracuseStep 1136235 = 1704353) B1704353
theorem B1136247 : Blo 1132632 1136247 := bstep (se 1 (by rfl) ⟨852185, by rfl⟩ : syracuseStep 1136247 = 1704371) B1704371
theorem B1136267 : Blo 1132632 1136267 := bstep (se 1 (by rfl) ⟨852200, by rfl⟩ : syracuseStep 1136267 = 1704401) B1704401
theorem B1136279 : Blo 1132632 1136279 := bstep (se 1 (by rfl) ⟨852209, by rfl⟩ : syracuseStep 1136279 = 1704419) B1704419
theorem B1136299 : Blo 1132632 1136299 := bstep (se 1 (by rfl) ⟨852224, by rfl⟩ : syracuseStep 1136299 = 1704449) B1704449
theorem B1136311 : Blo 1132632 1136311 := bstep (se 1 (by rfl) ⟨852233, by rfl⟩ : syracuseStep 1136311 = 1704467) B1704467
theorem B3823307 : Blo 1132632 3823307 := bstep (se 1 (by rfl) ⟨2867480, by rfl⟩ : syracuseStep 3823307 = 5734961) B5734961
theorem B1136331 : Blo 1132632 1136331 := bstep (se 1 (by rfl) ⟨852248, by rfl⟩ : syracuseStep 1136331 = 1704497) B1704497
theorem B1136343 : Blo 1132632 1136343 := bstep (se 1 (by rfl) ⟨852257, by rfl⟩ : syracuseStep 1136343 = 1704515) B1704515
theorem B1136363 : Blo 1132632 1136363 := bstep (se 1 (by rfl) ⟨852272, by rfl⟩ : syracuseStep 1136363 = 1704545) B1704545
theorem B1136375 : Blo 1132632 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B1136395 : Blo 1132632 1136395 := bstep (se 1 (by rfl) ⟨852296, by rfl⟩ : syracuseStep 1136395 = 1704593) B1704593
theorem B1136407 : Blo 1132632 1136407 := bstep (se 1 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 1136407 = 1704611) B1704611
theorem B1136427 : Blo 1132632 1136427 := bstep (se 1 (by rfl) ⟨852320, by rfl⟩ : syracuseStep 1136427 = 1704641) B1704641
theorem B1136439 : Blo 1132632 1136439 := bstep (se 1 (by rfl) ⟨852329, by rfl⟩ : syracuseStep 1136439 = 1704659) B1704659
theorem B4085569 : Blo 1132632 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B1136459 : Blo 1132632 1136459 := bstep (se 1 (by rfl) ⟨852344, by rfl⟩ : syracuseStep 1136459 = 1704689) B1704689
theorem B1136471 : Blo 1132632 1136471 := bstep (se 1 (by rfl) ⟨852353, by rfl⟩ : syracuseStep 1136471 = 1704707) B1704707
theorem B19912547 : Blo 1132632 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B1136491 : Blo 1132632 1136491 := bstep (se 1 (by rfl) ⟨852368, by rfl⟩ : syracuseStep 1136491 = 1704737) B1704737
theorem B1136503 : Blo 1132632 1136503 := bstep (se 1 (by rfl) ⟨852377, by rfl⟩ : syracuseStep 1136503 = 1704755) B1704755
theorem B1136523 : Blo 1132632 1136523 := bstep (se 1 (by rfl) ⟨852392, by rfl⟩ : syracuseStep 1136523 = 1704785) B1704785
theorem B1136535 : Blo 1132632 1136535 := bstep (se 1 (by rfl) ⟨852401, by rfl⟩ : syracuseStep 1136535 = 1704803) B1704803
theorem B1136555 : Blo 1132632 1136555 := bstep (se 1 (by rfl) ⟨852416, by rfl⟩ : syracuseStep 1136555 = 1704833) B1704833
theorem B1136567 : Blo 1132632 1136567 := bstep (se 1 (by rfl) ⟨852425, by rfl⟩ : syracuseStep 1136567 = 1704851) B1704851
theorem B1136587 : Blo 1132632 1136587 := bstep (se 1 (by rfl) ⟨852440, by rfl⟩ : syracuseStep 1136587 = 1704881) B1704881
theorem B1136599 : Blo 1132632 1136599 := bstep (se 1 (by rfl) ⟨852449, by rfl⟩ : syracuseStep 1136599 = 1704899) B1704899
theorem B3823577 : Blo 1132632 3823577 := bstep (se 2 (by rfl) ⟨1433841, by rfl⟩ : syracuseStep 3823577 = 2867683) B2867683
theorem B10901465 : Blo 1132632 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 1132632 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B1136619 : Blo 1132632 1136619 := bstep (se 1 (by rfl) ⟨852464, by rfl⟩ : syracuseStep 1136619 = 1704929) B1704929
theorem B1136631 : Blo 1132632 1136631 := bstep (se 1 (by rfl) ⟨852473, by rfl⟩ : syracuseStep 1136631 = 1704947) B1704947
theorem B2873495 : Blo 1132632 2873495 := bstep (se 1 (by rfl) ⟨2155121, by rfl⟩ : syracuseStep 2873495 = 4310243) B4310243
theorem B4315315 : Blo 1132632 4315315 := bstep (se 1 (by rfl) ⟨3236486, by rfl⟩ : syracuseStep 4315315 = 6472973) B6472973
theorem B8181977 : Blo 1132632 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B6904109 : Blo 1132632 6904109 := bstep (se 3 (by rfl) ⟨1294520, by rfl⟩ : syracuseStep 6904109 = 2589041) B2589041
theorem B2152919 : Blo 1132632 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B3824279 : Blo 1132632 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B9689777 : Blo 1132632 9689777 := bstep (se 2 (by rfl) ⟨3633666, by rfl⟩ : syracuseStep 9689777 = 7267333) B7267333
theorem B8608517 : Blo 1132632 8608517 := bstep (se 4 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 8608517 = 1614097) B1614097
theorem B4086551 : Blo 1132632 4086551 := bstep (se 1 (by rfl) ⟨3064913, by rfl⟩ : syracuseStep 4086551 = 6129827) B6129827
theorem B2874163 : Blo 1132632 2874163 := bstep (se 1 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 2874163 = 4311245) B4311245
theorem B2874305 : Blo 1132632 2874305 := bstep (se 2 (by rfl) ⟨1077864, by rfl⟩ : syracuseStep 2874305 = 2155729) B2155729
theorem B2153459 : Blo 1132632 2153459 := bstep (se 1 (by rfl) ⟨1615094, by rfl⟩ : syracuseStep 2153459 = 3230189) B3230189
theorem B4840499 : Blo 1132632 4840499 := bstep (se 1 (by rfl) ⟨3630374, by rfl⟩ : syracuseStep 4840499 = 7260749) B7260749
theorem B3824819 : Blo 1132632 3824819 := bstep (se 1 (by rfl) ⟨2868614, by rfl⟩ : syracuseStep 3824819 = 5737229) B5737229
theorem B4840651 : Blo 1132632 4840651 := bstep (se 1 (by rfl) ⟨3630488, by rfl⟩ : syracuseStep 4840651 = 7260977) B7260977
theorem B4840721 : Blo 1132632 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B9690461 : Blo 1132632 9690461 := bstep (se 3 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 9690461 = 3633923) B3633923
theorem B3825089 : Blo 1132632 3825089 := bstep (se 2 (by rfl) ⟨1434408, by rfl⟩ : syracuseStep 3825089 = 2868817) B2868817
theorem B2153945 : Blo 1132632 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B3628567 : Blo 1132632 3628567 := bstep (se 1 (by rfl) ⟨2721425, by rfl⟩ : syracuseStep 3628567 = 5442851) B5442851
theorem B3235393 : Blo 1132632 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B10346417 : Blo 1132632 10346417 := bstep (se 2 (by rfl) ⟨3879906, by rfl⟩ : syracuseStep 10346417 = 7759813) B7759813
theorem B3825629 : Blo 1132632 3825629 := bstep (se 3 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 3825629 = 1434611) B1434611
theorem B7004225 : Blo 1132632 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B2875571 : Blo 1132632 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B3629387 : Blo 1132632 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B18407897 : Blo 1132632 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B4088323 : Blo 1132632 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B2876107 : Blo 1132632 2876107 := bstep (se 1 (by rfl) ⟨2157080, by rfl⟩ : syracuseStep 2876107 = 4314161) B4314161
theorem B2548439 : Blo 1132632 2548439 := bstep (se 1 (by rfl) ⟨1911329, by rfl⟩ : syracuseStep 2548439 = 3822659) B3822659
theorem B4088627 : Blo 1132632 4088627 := bstep (se 1 (by rfl) ⟨3066470, by rfl⟩ : syracuseStep 4088627 = 6132941) B6132941
theorem B2876249 : Blo 1132632 2876249 := bstep (se 2 (by rfl) ⟨1078593, by rfl⟩ : syracuseStep 2876249 = 2157187) B2157187
theorem B2548619 : Blo 1132632 2548619 := bstep (se 1 (by rfl) ⟨1911464, by rfl⟩ : syracuseStep 2548619 = 3822929) B3822929
theorem B2155403 : Blo 1132632 2155403 := bstep (se 1 (by rfl) ⟨1616552, by rfl⟩ : syracuseStep 2155403 = 3233105) B3233105
theorem B4842413 : Blo 1132632 4842413 := bstep (se 3 (by rfl) ⟨907952, by rfl⟩ : syracuseStep 4842413 = 1815905) B1815905
theorem B2548673 : Blo 1132632 2548673 := bstep (se 2 (by rfl) ⟨955752, by rfl⟩ : syracuseStep 2548673 = 1911505) B1911505
theorem B2155585 : Blo 1132632 2155585 := bstep (se 2 (by rfl) ⟨808344, by rfl⟩ : syracuseStep 2155585 = 1616689) B1616689
theorem B3826763 : Blo 1132632 3826763 := bstep (se 1 (by rfl) ⟨2870072, by rfl⟩ : syracuseStep 3826763 = 5740145) B5740145
theorem B8610947 : Blo 1132632 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B1434763 : Blo 1132632 1434763 := bstep (se 1 (by rfl) ⟨1076072, by rfl⟩ : syracuseStep 1434763 = 2152145) B2152145
theorem B2548889 : Blo 1132632 2548889 := bstep (se 2 (by rfl) ⟨955833, by rfl⟩ : syracuseStep 2548889 = 1911667) B1911667
theorem B2548979 : Blo 1132632 2548979 := bstep (se 1 (by rfl) ⟨1911734, by rfl⟩ : syracuseStep 2548979 = 3823469) B3823469
theorem B2549015 : Blo 1132632 2549015 := bstep (se 1 (by rfl) ⟨1911761, by rfl⟩ : syracuseStep 2549015 = 3823523) B3823523
theorem B3827033 : Blo 1132632 3827033 := bstep (se 2 (by rfl) ⟨1435137, by rfl⟩ : syracuseStep 3827033 = 2870275) B2870275
theorem B2549195 : Blo 1132632 2549195 := bstep (se 1 (by rfl) ⟨1911896, by rfl⟩ : syracuseStep 2549195 = 3823793) B3823793
theorem B2549249 : Blo 1132632 2549249 := bstep (se 2 (by rfl) ⟨955968, by rfl⟩ : syracuseStep 2549249 = 1911937) B1911937
theorem B2156033 : Blo 1132632 2156033 := bstep (se 2 (by rfl) ⟨808512, by rfl⟩ : syracuseStep 2156033 = 1617025) B1617025
theorem B4843097 : Blo 1132632 4843097 := bstep (se 2 (by rfl) ⟨1816161, by rfl⟩ : syracuseStep 4843097 = 3632323) B3632323
theorem B2877079 : Blo 1132632 2877079 := bstep (se 1 (by rfl) ⟨2157809, by rfl⟩ : syracuseStep 2877079 = 4315619) B4315619
theorem B2549465 : Blo 1132632 2549465 := bstep (se 2 (by rfl) ⟨956049, by rfl⟩ : syracuseStep 2549465 = 1912099) B1912099
theorem B2549555 : Blo 1132632 2549555 := bstep (se 1 (by rfl) ⟨1912166, by rfl⟩ : syracuseStep 2549555 = 3824333) B3824333
theorem B3630899 : Blo 1132632 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B2549591 : Blo 1132632 2549591 := bstep (se 1 (by rfl) ⟨1912193, by rfl⟩ : syracuseStep 2549591 = 3824387) B3824387
theorem B2156375 : Blo 1132632 2156375 := bstep (se 1 (by rfl) ⟨1617281, by rfl⟩ : syracuseStep 2156375 = 3234563) B3234563
theorem B2549771 : Blo 1132632 2549771 := bstep (se 1 (by rfl) ⟨1912328, by rfl⟩ : syracuseStep 2549771 = 3824657) B3824657
theorem B8185873 : Blo 1132632 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B3827735 : Blo 1132632 3827735 := bstep (se 1 (by rfl) ⟨2870801, by rfl⟩ : syracuseStep 3827735 = 5741603) B5741603
theorem B2549825 : Blo 1132632 2549825 := bstep (se 2 (by rfl) ⟨956184, by rfl⟩ : syracuseStep 2549825 = 1912369) B1912369
theorem B1435735 : Blo 1132632 1435735 := bstep (se 1 (by rfl) ⟨1076801, by rfl⟩ : syracuseStep 1435735 = 2153603) B2153603
theorem B2550041 : Blo 1132632 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B11659585 : Blo 1132632 11659585 := bstep (se 2 (by rfl) ⟨4372344, by rfl⟩ : syracuseStep 11659585 = 8744689) B8744689
theorem B2550131 : Blo 1132632 2550131 := bstep (se 1 (by rfl) ⟨1912598, by rfl⟩ : syracuseStep 2550131 = 3825197) B3825197
theorem B2550167 : Blo 1132632 2550167 := bstep (se 1 (by rfl) ⟨1912625, by rfl⟩ : syracuseStep 2550167 = 3825251) B3825251
theorem B2157043 : Blo 1132632 2157043 := bstep (se 1 (by rfl) ⟨1617782, by rfl⟩ : syracuseStep 2157043 = 3235565) B3235565
theorem B3828275 : Blo 1132632 3828275 := bstep (se 1 (by rfl) ⟨2871206, by rfl⟩ : syracuseStep 3828275 = 5742413) B5742413
theorem B2550347 : Blo 1132632 2550347 := bstep (se 1 (by rfl) ⟨1912760, by rfl⟩ : syracuseStep 2550347 = 3825521) B3825521
theorem B2550401 : Blo 1132632 2550401 := bstep (se 2 (by rfl) ⟨956400, by rfl⟩ : syracuseStep 2550401 = 1912801) B1912801
theorem B10349261 : Blo 1132632 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B3828545 : Blo 1132632 3828545 := bstep (se 2 (by rfl) ⟨1435704, by rfl⟩ : syracuseStep 3828545 = 2871409) B2871409
theorem B2550617 : Blo 1132632 2550617 := bstep (se 2 (by rfl) ⟨956481, by rfl⟩ : syracuseStep 2550617 = 1912963) B1912963
theorem B1436555 : Blo 1132632 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B5172113 : Blo 1132632 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B2550707 : Blo 1132632 2550707 := bstep (se 1 (by rfl) ⟨1913030, by rfl⟩ : syracuseStep 2550707 = 3826061) B3826061
theorem B2157491 : Blo 1132632 2157491 := bstep (se 1 (by rfl) ⟨1618118, by rfl⟩ : syracuseStep 2157491 = 3236237) B3236237
theorem B2550743 : Blo 1132632 2550743 := bstep (se 1 (by rfl) ⟨1913057, by rfl⟩ : syracuseStep 2550743 = 3826115) B3826115
theorem B2157529 : Blo 1132632 2157529 := bstep (se 2 (by rfl) ⟨809073, by rfl⟩ : syracuseStep 2157529 = 1618147) B1618147
theorem B20671523 : Blo 1132632 20671523 := bstep (se 1 (by rfl) ⟨15503642, by rfl⟩ : syracuseStep 20671523 = 31007285) B31007285
theorem B2911307 : Blo 1132632 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B2550923 : Blo 1132632 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B2419865 : Blo 1132632 2419865 := bstep (se 2 (by rfl) ⟨907449, by rfl⟩ : syracuseStep 2419865 = 1814899) B1814899
theorem B2550977 : Blo 1132632 2550977 := bstep (se 2 (by rfl) ⟨956616, by rfl⟩ : syracuseStep 2550977 = 1913233) B1913233
theorem B1699019 : Blo 1132632 1699019 := bstep (se 1 (by rfl) ⟨1274264, by rfl⟩ : syracuseStep 1699019 = 2548529) B2548529
theorem B1699031 : Blo 1132632 1699031 := bstep (se 1 (by rfl) ⟨1274273, by rfl⟩ : syracuseStep 1699031 = 2548547) B2548547
theorem B1699097 : Blo 1132632 1699097 := bstep (se 2 (by rfl) ⟨637161, by rfl⟩ : syracuseStep 1699097 = 1274323) B1274323
theorem B1535257 : Blo 1132632 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B3829085 : Blo 1132632 3829085 := bstep (se 3 (by rfl) ⟨717953, by rfl⟩ : syracuseStep 3829085 = 1435907) B1435907
theorem B1699211 : Blo 1132632 1699211 := bstep (se 1 (by rfl) ⟨1274408, by rfl⟩ : syracuseStep 1699211 = 2548817) B2548817
theorem B1699223 : Blo 1132632 1699223 := bstep (se 1 (by rfl) ⟨1274417, by rfl⟩ : syracuseStep 1699223 = 2548835) B2548835
theorem B2551193 : Blo 1132632 2551193 := bstep (se 2 (by rfl) ⟨956697, by rfl⟩ : syracuseStep 2551193 = 1913395) B1913395
theorem B1699289 : Blo 1132632 1699289 := bstep (se 2 (by rfl) ⟨637233, by rfl⟩ : syracuseStep 1699289 = 1274467) B1274467
theorem B2551283 : Blo 1132632 2551283 := bstep (se 1 (by rfl) ⟨1913462, by rfl⟩ : syracuseStep 2551283 = 3826925) B3826925
theorem B2551319 : Blo 1132632 2551319 := bstep (se 1 (by rfl) ⟨1913489, by rfl⟩ : syracuseStep 2551319 = 3826979) B3826979
theorem B2420275 : Blo 1132632 2420275 := bstep (se 1 (by rfl) ⟨1815206, by rfl⟩ : syracuseStep 2420275 = 3630413) B3630413
theorem B1699403 : Blo 1132632 1699403 := bstep (se 1 (by rfl) ⟨1274552, by rfl⟩ : syracuseStep 1699403 = 2549105) B2549105
theorem B1437259 : Blo 1132632 1437259 := bstep (se 1 (by rfl) ⟨1077944, by rfl⟩ : syracuseStep 1437259 = 2155889) B2155889
theorem B1699415 : Blo 1132632 1699415 := bstep (se 1 (by rfl) ⟨1274561, by rfl⟩ : syracuseStep 1699415 = 2549123) B2549123
theorem B1699481 : Blo 1132632 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B2551499 : Blo 1132632 2551499 := bstep (se 1 (by rfl) ⟨1913624, by rfl⟩ : syracuseStep 2551499 = 3827249) B3827249
theorem B2551553 : Blo 1132632 2551553 := bstep (se 2 (by rfl) ⟨956832, by rfl⟩ : syracuseStep 2551553 = 1913665) B1913665
theorem B1699595 : Blo 1132632 1699595 := bstep (se 1 (by rfl) ⟨1274696, by rfl⟩ : syracuseStep 1699595 = 2549393) B2549393
theorem B1699607 : Blo 1132632 1699607 := bstep (se 1 (by rfl) ⟨1274705, by rfl⟩ : syracuseStep 1699607 = 2549411) B2549411
theorem B2420531 : Blo 1132632 2420531 := bstep (se 1 (by rfl) ⟨1815398, by rfl⟩ : syracuseStep 2420531 = 3630797) B3630797
theorem B1535819 : Blo 1132632 1535819 := bstep (se 1 (by rfl) ⟨1151864, by rfl⟩ : syracuseStep 1535819 = 2303729) B2303729
theorem B1437527 : Blo 1132632 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B1699673 : Blo 1132632 1699673 := bstep (se 2 (by rfl) ⟨637377, by rfl⟩ : syracuseStep 1699673 = 1274755) B1274755
theorem B4091741 : Blo 1132632 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B1699787 : Blo 1132632 1699787 := bstep (se 1 (by rfl) ⟨1274840, by rfl⟩ : syracuseStep 1699787 = 2549681) B2549681
theorem B1699799 : Blo 1132632 1699799 := bstep (se 1 (by rfl) ⟨1274849, by rfl⟩ : syracuseStep 1699799 = 2549699) B2549699
theorem B2551769 : Blo 1132632 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B1699865 : Blo 1132632 1699865 := bstep (se 2 (by rfl) ⟨637449, by rfl⟩ : syracuseStep 1699865 = 1274899) B1274899
theorem B2551859 : Blo 1132632 2551859 := bstep (se 1 (by rfl) ⟨1913894, by rfl⟩ : syracuseStep 2551859 = 3827789) B3827789
theorem B2551895 : Blo 1132632 2551895 := bstep (se 1 (by rfl) ⟨1913921, by rfl⟩ : syracuseStep 2551895 = 3827843) B3827843
theorem B13791325 : Blo 1132632 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B3633245 : Blo 1132632 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B1699979 : Blo 1132632 1699979 := bstep (se 1 (by rfl) ⟨1274984, by rfl⟩ : syracuseStep 1699979 = 2549969) B2549969
theorem B1699991 : Blo 1132632 1699991 := bstep (se 1 (by rfl) ⟨1274993, by rfl⟩ : syracuseStep 1699991 = 2549987) B2549987
theorem B6549655 : Blo 1132632 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B1700057 : Blo 1132632 1700057 := bstep (se 2 (by rfl) ⟨637521, by rfl⟩ : syracuseStep 1700057 = 1275043) B1275043
theorem B2552075 : Blo 1132632 2552075 := bstep (se 1 (by rfl) ⟨1914056, by rfl⟩ : syracuseStep 2552075 = 3828113) B3828113
theorem B2552129 : Blo 1132632 2552129 := bstep (se 2 (by rfl) ⟨957048, by rfl⟩ : syracuseStep 2552129 = 1914097) B1914097
theorem B1700171 : Blo 1132632 1700171 := bstep (se 1 (by rfl) ⟨1275128, by rfl⟩ : syracuseStep 1700171 = 2550257) B2550257
theorem B1700183 : Blo 1132632 1700183 := bstep (se 1 (by rfl) ⟨1275137, by rfl⟩ : syracuseStep 1700183 = 2550275) B2550275
theorem B1274251 : Blo 1132632 1274251 := bstep (se 1 (by rfl) ⟨955688, by rfl⟩ : syracuseStep 1274251 = 1911377) B1911377
theorem B1700249 : Blo 1132632 1700249 := bstep (se 2 (by rfl) ⟨637593, by rfl⟩ : syracuseStep 1700249 = 1275187) B1275187
theorem B3830219 : Blo 1132632 3830219 := bstep (se 1 (by rfl) ⟨2872664, by rfl⟩ : syracuseStep 3830219 = 5745329) B5745329
theorem B8614349 : Blo 1132632 8614349 := bstep (se 3 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 8614349 = 3230381) B3230381
theorem B1274359 : Blo 1132632 1274359 := bstep (se 1 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 1274359 = 1911539) B1911539
theorem B1700363 : Blo 1132632 1700363 := bstep (se 1 (by rfl) ⟨1275272, by rfl⟩ : syracuseStep 1700363 = 2550545) B2550545
theorem B1700375 : Blo 1132632 1700375 := bstep (se 1 (by rfl) ⟨1275281, by rfl⟩ : syracuseStep 1700375 = 2550563) B2550563
theorem B1438231 : Blo 1132632 1438231 := bstep (se 1 (by rfl) ⟨1078673, by rfl⟩ : syracuseStep 1438231 = 2157347) B2157347
theorem B2552345 : Blo 1132632 2552345 := bstep (se 2 (by rfl) ⟨957129, by rfl⟩ : syracuseStep 2552345 = 1914259) B1914259
theorem B1700441 : Blo 1132632 1700441 := bstep (se 2 (by rfl) ⟨637665, by rfl⟩ : syracuseStep 1700441 = 1275331) B1275331
theorem B2552435 : Blo 1132632 2552435 := bstep (se 1 (by rfl) ⟨1914326, by rfl⟩ : syracuseStep 2552435 = 3828653) B3828653
theorem B2552471 : Blo 1132632 2552471 := bstep (se 1 (by rfl) ⟨1914353, by rfl⟩ : syracuseStep 2552471 = 3828707) B3828707
theorem B1274539 : Blo 1132632 1274539 := bstep (se 1 (by rfl) ⟨955904, by rfl⟩ : syracuseStep 1274539 = 1911809) B1911809
theorem B1700555 : Blo 1132632 1700555 := bstep (se 1 (by rfl) ⟨1275416, by rfl⟩ : syracuseStep 1700555 = 2550833) B2550833
theorem B1700567 : Blo 1132632 1700567 := bstep (se 1 (by rfl) ⟨1275425, by rfl⟩ : syracuseStep 1700567 = 2550851) B2550851
theorem B3830489 : Blo 1132632 3830489 := bstep (se 2 (by rfl) ⟨1436433, by rfl⟩ : syracuseStep 3830489 = 2872867) B2872867
theorem B2421505 : Blo 1132632 2421505 := bstep (se 2 (by rfl) ⟨908064, by rfl⟩ : syracuseStep 2421505 = 1816129) B1816129
theorem B1274647 : Blo 1132632 1274647 := bstep (se 1 (by rfl) ⟨955985, by rfl⟩ : syracuseStep 1274647 = 1911971) B1911971
theorem B1700633 : Blo 1132632 1700633 := bstep (se 2 (by rfl) ⟨637737, by rfl⟩ : syracuseStep 1700633 = 1275475) B1275475
theorem B2552651 : Blo 1132632 2552651 := bstep (se 1 (by rfl) ⟨1914488, by rfl⟩ : syracuseStep 2552651 = 3828977) B3828977
theorem B29487971 : Blo 1132632 29487971 := bstep (se 1 (by rfl) ⟨22115978, by rfl⟩ : syracuseStep 29487971 = 44231957) B44231957
theorem B2552705 : Blo 1132632 2552705 := bstep (se 2 (by rfl) ⟨957264, by rfl⟩ : syracuseStep 2552705 = 1914529) B1914529
theorem B1700747 : Blo 1132632 1700747 := bstep (se 1 (by rfl) ⟨1275560, by rfl⟩ : syracuseStep 1700747 = 2551121) B2551121
theorem B1700759 : Blo 1132632 1700759 := bstep (se 1 (by rfl) ⟨1275569, by rfl⟩ : syracuseStep 1700759 = 2551139) B2551139
theorem B2913175 : Blo 1132632 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B8614835 : Blo 1132632 8614835 := bstep (se 1 (by rfl) ⟨6461126, by rfl⟩ : syracuseStep 8614835 = 12922253) B12922253
theorem B4846529 : Blo 1132632 4846529 := bstep (se 2 (by rfl) ⟨1817448, by rfl⟩ : syracuseStep 4846529 = 3634897) B3634897
theorem B1274827 : Blo 1132632 1274827 := bstep (se 1 (by rfl) ⟨956120, by rfl⟩ : syracuseStep 1274827 = 1912241) B1912241
theorem B1700825 : Blo 1132632 1700825 := bstep (se 2 (by rfl) ⟨637809, by rfl⟩ : syracuseStep 1700825 = 1275619) B1275619
theorem B1274935 : Blo 1132632 1274935 := bstep (se 1 (by rfl) ⟨956201, by rfl⟩ : syracuseStep 1274935 = 1912403) B1912403
theorem B6911041 : Blo 1132632 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B1700939 : Blo 1132632 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1700951 : Blo 1132632 1700951 := bstep (se 1 (by rfl) ⟨1275713, by rfl⟩ : syracuseStep 1700951 = 2551427) B2551427
theorem B2552921 : Blo 1132632 2552921 := bstep (se 2 (by rfl) ⟨957345, by rfl⟩ : syracuseStep 2552921 = 1914691) B1914691
theorem B1701017 : Blo 1132632 1701017 := bstep (se 2 (by rfl) ⟨637881, by rfl⟩ : syracuseStep 1701017 = 1275763) B1275763
theorem B2553011 : Blo 1132632 2553011 := bstep (se 1 (by rfl) ⟨1914758, by rfl⟩ : syracuseStep 2553011 = 3829517) B3829517
theorem B2553047 : Blo 1132632 2553047 := bstep (se 1 (by rfl) ⟨1914785, by rfl⟩ : syracuseStep 2553047 = 3829571) B3829571
theorem B1275115 : Blo 1132632 1275115 := bstep (se 1 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 1275115 = 1912673) B1912673
theorem B1701131 : Blo 1132632 1701131 := bstep (se 1 (by rfl) ⟨1275848, by rfl⟩ : syracuseStep 1701131 = 2551697) B2551697
theorem B1701143 : Blo 1132632 1701143 := bstep (se 1 (by rfl) ⟨1275857, by rfl⟩ : syracuseStep 1701143 = 2551715) B2551715
theorem B4846871 : Blo 1132632 4846871 := bstep (se 1 (by rfl) ⟨3635153, by rfl⟩ : syracuseStep 4846871 = 7270307) B7270307
theorem B5174579 : Blo 1132632 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B3241291 : Blo 1132632 3241291 := bstep (se 1 (by rfl) ⟨2430968, by rfl⟩ : syracuseStep 3241291 = 4861937) B4861937
theorem B1275223 : Blo 1132632 1275223 := bstep (se 1 (by rfl) ⟨956417, by rfl⟩ : syracuseStep 1275223 = 1912835) B1912835
theorem B1701209 : Blo 1132632 1701209 := bstep (se 2 (by rfl) ⟨637953, by rfl⟩ : syracuseStep 1701209 = 1275907) B1275907
theorem B2553227 : Blo 1132632 2553227 := bstep (se 1 (by rfl) ⟨1914920, by rfl⟩ : syracuseStep 2553227 = 3829841) B3829841
theorem B3831191 : Blo 1132632 3831191 := bstep (se 1 (by rfl) ⟨2873393, by rfl⟩ : syracuseStep 3831191 = 5746787) B5746787
theorem B2553281 : Blo 1132632 2553281 := bstep (se 2 (by rfl) ⟨957480, by rfl⟩ : syracuseStep 2553281 = 1914961) B1914961
theorem B1701323 : Blo 1132632 1701323 := bstep (se 1 (by rfl) ⟨1275992, by rfl⟩ : syracuseStep 1701323 = 2551985) B2551985
theorem B1701335 : Blo 1132632 1701335 := bstep (se 1 (by rfl) ⟨1276001, by rfl⟩ : syracuseStep 1701335 = 2552003) B2552003
theorem B1275403 : Blo 1132632 1275403 := bstep (se 1 (by rfl) ⟨956552, by rfl⟩ : syracuseStep 1275403 = 1913105) B1913105
theorem B1701401 : Blo 1132632 1701401 := bstep (se 2 (by rfl) ⟨638025, by rfl⟩ : syracuseStep 1701401 = 1276051) B1276051
theorem B5535307 : Blo 1132632 5535307 := bstep (se 1 (by rfl) ⟨4151480, by rfl⟩ : syracuseStep 5535307 = 8302961) B8302961
theorem B1275511 : Blo 1132632 1275511 := bstep (se 1 (by rfl) ⟨956633, by rfl⟩ : syracuseStep 1275511 = 1913267) B1913267
theorem B4421251 : Blo 1132632 4421251 := bstep (se 1 (by rfl) ⟨3315938, by rfl⟩ : syracuseStep 4421251 = 6631877) B6631877
theorem B1701515 : Blo 1132632 1701515 := bstep (se 1 (by rfl) ⟨1276136, by rfl⟩ : syracuseStep 1701515 = 2552273) B2552273
theorem B1701527 : Blo 1132632 1701527 := bstep (se 1 (by rfl) ⟨1276145, by rfl⟩ : syracuseStep 1701527 = 2552291) B2552291
theorem B2553497 : Blo 1132632 2553497 := bstep (se 2 (by rfl) ⟨957561, by rfl⟩ : syracuseStep 2553497 = 1915123) B1915123
theorem B1701593 : Blo 1132632 1701593 := bstep (se 2 (by rfl) ⟨638097, by rfl⟩ : syracuseStep 1701593 = 1276195) B1276195
theorem B2553587 : Blo 1132632 2553587 := bstep (se 1 (by rfl) ⟨1915190, by rfl⟩ : syracuseStep 2553587 = 3830381) B3830381
theorem B2553623 : Blo 1132632 2553623 := bstep (se 1 (by rfl) ⟨1915217, by rfl⟩ : syracuseStep 2553623 = 3830435) B3830435
theorem B1275691 : Blo 1132632 1275691 := bstep (se 1 (by rfl) ⟨956768, by rfl⟩ : syracuseStep 1275691 = 1913537) B1913537
theorem B1701707 : Blo 1132632 1701707 := bstep (se 1 (by rfl) ⟨1276280, by rfl⟩ : syracuseStep 1701707 = 2552561) B2552561
theorem B1701719 : Blo 1132632 1701719 := bstep (se 1 (by rfl) ⟨1276289, by rfl⟩ : syracuseStep 1701719 = 2552579) B2552579
theorem B17495909 : Blo 1132632 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B1275799 : Blo 1132632 1275799 := bstep (se 1 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 1275799 = 1913699) B1913699
theorem B1701785 : Blo 1132632 1701785 := bstep (se 2 (by rfl) ⟨638169, by rfl⟩ : syracuseStep 1701785 = 1276339) B1276339
theorem B3831731 : Blo 1132632 3831731 := bstep (se 1 (by rfl) ⟨2873798, by rfl⟩ : syracuseStep 3831731 = 5747597) B5747597
theorem B2553803 : Blo 1132632 2553803 := bstep (se 1 (by rfl) ⟨1915352, by rfl⟩ : syracuseStep 2553803 = 3830705) B3830705
theorem B2553857 : Blo 1132632 2553857 := bstep (se 2 (by rfl) ⟨957696, by rfl⟩ : syracuseStep 2553857 = 1915393) B1915393
theorem B1701899 : Blo 1132632 1701899 := bstep (se 1 (by rfl) ⟨1276424, by rfl⟩ : syracuseStep 1701899 = 2552849) B2552849
theorem B1701911 : Blo 1132632 1701911 := bstep (se 1 (by rfl) ⟨1276433, by rfl⟩ : syracuseStep 1701911 = 2552867) B2552867
theorem B1210411 : Blo 1132632 1210411 := bstep (se 1 (by rfl) ⟨907808, by rfl⟩ : syracuseStep 1210411 = 1815617) B1815617
theorem B1275979 : Blo 1132632 1275979 := bstep (se 1 (by rfl) ⟨956984, by rfl⟩ : syracuseStep 1275979 = 1913969) B1913969
theorem B1964119 : Blo 1132632 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1701977 : Blo 1132632 1701977 := bstep (se 2 (by rfl) ⟨638241, by rfl⟩ : syracuseStep 1701977 = 1276483) B1276483
theorem B4847795 : Blo 1132632 4847795 := bstep (se 1 (by rfl) ⟨3635846, by rfl⟩ : syracuseStep 4847795 = 7271693) B7271693
theorem B1276087 : Blo 1132632 1276087 := bstep (se 1 (by rfl) ⟨957065, by rfl⟩ : syracuseStep 1276087 = 1914131) B1914131
theorem B3832001 : Blo 1132632 3832001 := bstep (se 2 (by rfl) ⟨1437000, by rfl⟩ : syracuseStep 3832001 = 2874001) B2874001
theorem B1702091 : Blo 1132632 1702091 := bstep (se 1 (by rfl) ⟨1276568, by rfl⟩ : syracuseStep 1702091 = 2553137) B2553137
theorem B1702103 : Blo 1132632 1702103 := bstep (se 1 (by rfl) ⟨1276577, by rfl⟩ : syracuseStep 1702103 = 2553155) B2553155
theorem B7272665 : Blo 1132632 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B2554073 : Blo 1132632 2554073 := bstep (se 2 (by rfl) ⟨957777, by rfl⟩ : syracuseStep 2554073 = 1915555) B1915555
theorem B1702169 : Blo 1132632 1702169 := bstep (se 2 (by rfl) ⟨638313, by rfl⟩ : syracuseStep 1702169 = 1276627) B1276627
theorem B2554163 : Blo 1132632 2554163 := bstep (se 1 (by rfl) ⟨1915622, by rfl⟩ : syracuseStep 2554163 = 3831245) B3831245
theorem B2554199 : Blo 1132632 2554199 := bstep (se 1 (by rfl) ⟨1915649, by rfl⟩ : syracuseStep 2554199 = 3831299) B3831299
theorem B8616293 : Blo 1132632 8616293 := bstep (se 4 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 8616293 = 1615555) B1615555
theorem B1276267 : Blo 1132632 1276267 := bstep (se 1 (by rfl) ⟨957200, by rfl⟩ : syracuseStep 1276267 = 1914401) B1914401
theorem B1702283 : Blo 1132632 1702283 := bstep (se 1 (by rfl) ⟨1276712, by rfl⟩ : syracuseStep 1702283 = 2553425) B2553425
theorem B1702295 : Blo 1132632 1702295 := bstep (se 1 (by rfl) ⟨1276721, by rfl⟩ : syracuseStep 1702295 = 2553443) B2553443
theorem B14547377 : Blo 1132632 14547377 := bstep (se 2 (by rfl) ⟨5455266, by rfl⟩ : syracuseStep 14547377 = 10910533) B10910533
theorem B1276375 : Blo 1132632 1276375 := bstep (se 1 (by rfl) ⟨957281, by rfl⟩ : syracuseStep 1276375 = 1914563) B1914563
theorem B1702361 : Blo 1132632 1702361 := bstep (se 2 (by rfl) ⟨638385, by rfl⟩ : syracuseStep 1702361 = 1276771) B1276771
theorem B2554379 : Blo 1132632 2554379 := bstep (se 1 (by rfl) ⟨1915784, by rfl⟩ : syracuseStep 2554379 = 3831569) B3831569
theorem B4094509 : Blo 1132632 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B2554433 : Blo 1132632 2554433 := bstep (se 2 (by rfl) ⟨957912, by rfl⟩ : syracuseStep 2554433 = 1915825) B1915825
theorem B12909131 : Blo 1132632 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B1702475 : Blo 1132632 1702475 := bstep (se 1 (by rfl) ⟨1276856, by rfl⟩ : syracuseStep 1702475 = 2553713) B2553713
theorem B1636951 : Blo 1132632 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B1702487 : Blo 1132632 1702487 := bstep (se 1 (by rfl) ⟨1276865, by rfl⟩ : syracuseStep 1702487 = 2553731) B2553731
theorem B1276555 : Blo 1132632 1276555 := bstep (se 1 (by rfl) ⟨957416, by rfl⟩ : syracuseStep 1276555 = 1914833) B1914833
theorem B1702553 : Blo 1132632 1702553 := bstep (se 2 (by rfl) ⟨638457, by rfl⟩ : syracuseStep 1702553 = 1276915) B1276915
theorem B3832541 : Blo 1132632 3832541 := bstep (se 3 (by rfl) ⟨718601, by rfl⟩ : syracuseStep 3832541 = 1437203) B1437203
theorem B1276663 : Blo 1132632 1276663 := bstep (se 1 (by rfl) ⟨957497, by rfl⟩ : syracuseStep 1276663 = 1914995) B1914995
theorem B1702667 : Blo 1132632 1702667 := bstep (se 1 (by rfl) ⟨1277000, by rfl⟩ : syracuseStep 1702667 = 2554001) B2554001
theorem B1702679 : Blo 1132632 1702679 := bstep (se 1 (by rfl) ⟨1277009, by rfl⟩ : syracuseStep 1702679 = 2554019) B2554019
theorem B2554649 : Blo 1132632 2554649 := bstep (se 2 (by rfl) ⟨957993, by rfl⟩ : syracuseStep 2554649 = 1915987) B1915987
theorem B8616779 : Blo 1132632 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B2423641 : Blo 1132632 2423641 := bstep (se 2 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 2423641 = 1817731) B1817731
theorem B1702745 : Blo 1132632 1702745 := bstep (se 2 (by rfl) ⟨638529, by rfl⟩ : syracuseStep 1702745 = 1277059) B1277059
theorem B2554739 : Blo 1132632 2554739 := bstep (se 1 (by rfl) ⟨1916054, by rfl⟩ : syracuseStep 2554739 = 3832109) B3832109
theorem B2554775 : Blo 1132632 2554775 := bstep (se 1 (by rfl) ⟨1916081, by rfl⟩ : syracuseStep 2554775 = 3832163) B3832163
theorem B1276843 : Blo 1132632 1276843 := bstep (se 1 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 1276843 = 1915265) B1915265
theorem B1702859 : Blo 1132632 1702859 := bstep (se 1 (by rfl) ⟨1277144, by rfl⟩ : syracuseStep 1702859 = 2554289) B2554289
theorem B1702871 : Blo 1132632 1702871 := bstep (se 1 (by rfl) ⟨1277153, by rfl⟩ : syracuseStep 1702871 = 2554307) B2554307
theorem B9206801 : Blo 1132632 9206801 := bstep (se 2 (by rfl) ⟨3452550, by rfl⟩ : syracuseStep 9206801 = 6905101) B6905101
theorem B1276951 : Blo 1132632 1276951 := bstep (se 1 (by rfl) ⟨957713, by rfl⟩ : syracuseStep 1276951 = 1915427) B1915427
theorem B1702937 : Blo 1132632 1702937 := bstep (se 2 (by rfl) ⟨638601, by rfl⟩ : syracuseStep 1702937 = 1277203) B1277203
theorem B2554955 : Blo 1132632 2554955 := bstep (se 1 (by rfl) ⟨1916216, by rfl⟩ : syracuseStep 2554955 = 3832433) B3832433
theorem B2555009 : Blo 1132632 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B1703051 : Blo 1132632 1703051 := bstep (se 1 (by rfl) ⟨1277288, by rfl⟩ : syracuseStep 1703051 = 2554577) B2554577
theorem B4848785 : Blo 1132632 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B1703063 : Blo 1132632 1703063 := bstep (se 1 (by rfl) ⟨1277297, by rfl⟩ : syracuseStep 1703063 = 2554595) B2554595
theorem B5176493 : Blo 1132632 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B1277131 : Blo 1132632 1277131 := bstep (se 1 (by rfl) ⟨957848, by rfl⟩ : syracuseStep 1277131 = 1915697) B1915697
theorem B1703129 : Blo 1132632 1703129 := bstep (se 2 (by rfl) ⟨638673, by rfl⟩ : syracuseStep 1703129 = 1277347) B1277347
theorem B1277239 : Blo 1132632 1277239 := bstep (se 1 (by rfl) ⟨957929, by rfl⟩ : syracuseStep 1277239 = 1915859) B1915859
theorem B1703243 : Blo 1132632 1703243 := bstep (se 1 (by rfl) ⟨1277432, by rfl⟩ : syracuseStep 1703243 = 2554865) B2554865
theorem B1703255 : Blo 1132632 1703255 := bstep (se 1 (by rfl) ⟨1277441, by rfl⟩ : syracuseStep 1703255 = 2554883) B2554883
theorem B2555225 : Blo 1132632 2555225 := bstep (se 2 (by rfl) ⟨958209, by rfl⟩ : syracuseStep 2555225 = 1916419) B1916419
theorem B6126949 : Blo 1132632 6126949 := bstep (se 4 (by rfl) ⟨574401, by rfl⟩ : syracuseStep 6126949 = 1148803) B1148803
theorem B1703321 : Blo 1132632 1703321 := bstep (se 2 (by rfl) ⟨638745, by rfl⟩ : syracuseStep 1703321 = 1277491) B1277491
theorem B2555315 : Blo 1132632 2555315 := bstep (se 1 (by rfl) ⟨1916486, by rfl⟩ : syracuseStep 2555315 = 3832973) B3832973
theorem B2555351 : Blo 1132632 2555351 := bstep (se 1 (by rfl) ⟨1916513, by rfl⟩ : syracuseStep 2555351 = 3833027) B3833027
theorem B1277419 : Blo 1132632 1277419 := bstep (se 1 (by rfl) ⟨958064, by rfl⟩ : syracuseStep 1277419 = 1916129) B1916129
theorem B1703435 : Blo 1132632 1703435 := bstep (se 1 (by rfl) ⟨1277576, by rfl⟩ : syracuseStep 1703435 = 2555153) B2555153
theorem B1703447 : Blo 1132632 1703447 := bstep (se 1 (by rfl) ⟨1277585, by rfl⟩ : syracuseStep 1703447 = 2555171) B2555171
theorem B1277527 : Blo 1132632 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B1703513 : Blo 1132632 1703513 := bstep (se 2 (by rfl) ⟨638817, by rfl⟩ : syracuseStep 1703513 = 1277635) B1277635
theorem B2555531 : Blo 1132632 2555531 := bstep (se 1 (by rfl) ⟨1916648, by rfl⟩ : syracuseStep 2555531 = 3833297) B3833297
theorem B2588311 : Blo 1132632 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B2555585 : Blo 1132632 2555585 := bstep (se 2 (by rfl) ⟨958344, by rfl⟩ : syracuseStep 2555585 = 1916689) B1916689
theorem B1703627 : Blo 1132632 1703627 := bstep (se 1 (by rfl) ⟨1277720, by rfl⟩ : syracuseStep 1703627 = 2555441) B2555441
theorem B1703639 : Blo 1132632 1703639 := bstep (se 1 (by rfl) ⟨1277729, by rfl⟩ : syracuseStep 1703639 = 2555459) B2555459
theorem B1277707 : Blo 1132632 1277707 := bstep (se 1 (by rfl) ⟨958280, by rfl⟩ : syracuseStep 1277707 = 1916561) B1916561
theorem B1703705 : Blo 1132632 1703705 := bstep (se 2 (by rfl) ⟨638889, by rfl⟩ : syracuseStep 1703705 = 1277779) B1277779
theorem B3833675 : Blo 1132632 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B1277815 : Blo 1132632 1277815 := bstep (se 1 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 1277815 = 1916723) B1916723
theorem B1703819 : Blo 1132632 1703819 := bstep (se 1 (by rfl) ⟨1277864, by rfl⟩ : syracuseStep 1703819 = 2555729) B2555729
theorem B1703831 : Blo 1132632 1703831 := bstep (se 1 (by rfl) ⟨1277873, by rfl⟩ : syracuseStep 1703831 = 2555747) B2555747
theorem B2555801 : Blo 1132632 2555801 := bstep (se 2 (by rfl) ⟨958425, by rfl⟩ : syracuseStep 2555801 = 1916851) B1916851
theorem B1703897 : Blo 1132632 1703897 := bstep (se 2 (by rfl) ⟨638961, by rfl⟩ : syracuseStep 1703897 = 1277923) B1277923
theorem B2555891 : Blo 1132632 2555891 := bstep (se 1 (by rfl) ⟨1916918, by rfl⟩ : syracuseStep 2555891 = 3833837) B3833837
theorem B1277959 : Blo 1132632 1277959 := bstep (se 1 (by rfl) ⟨958469, by rfl⟩ : syracuseStep 1277959 = 1916939) B1916939
theorem B1703951 : Blo 1132632 1703951 := bstep (se 1 (by rfl) ⟨1277963, by rfl⟩ : syracuseStep 1703951 = 2555927) B2555927
theorem B12288023 : Blo 1132632 12288023 := bstep (se 1 (by rfl) ⟨9216017, by rfl⟩ : syracuseStep 12288023 = 18432035) B18432035
theorem B1703993 : Blo 1132632 1703993 := bstep (se 2 (by rfl) ⟨638997, by rfl⟩ : syracuseStep 1703993 = 1277995) B1277995
theorem B2555963 : Blo 1132632 2555963 := bstep (se 1 (by rfl) ⟨1916972, by rfl⟩ : syracuseStep 2555963 = 3833945) B3833945
theorem B1704071 : Blo 1132632 1704071 := bstep (se 1 (by rfl) ⟨1278053, by rfl⟩ : syracuseStep 1704071 = 2556107) B2556107
theorem B1704107 : Blo 1132632 1704107 := bstep (se 1 (by rfl) ⟨1278080, by rfl⟩ : syracuseStep 1704107 = 2556161) B2556161
theorem B2556089 : Blo 1132632 2556089 := bstep (se 2 (by rfl) ⟨958533, by rfl⟩ : syracuseStep 2556089 = 1917067) B1917067
theorem B1278139 : Blo 1132632 1278139 := bstep (se 1 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 1278139 = 1917209) B1917209
theorem B1704137 : Blo 1132632 1704137 := bstep (se 2 (by rfl) ⟨639051, by rfl⟩ : syracuseStep 1704137 = 1278103) B1278103
theorem B5734637 : Blo 1132632 5734637 := bstep (se 3 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 5734637 = 2150489) B2150489
theorem B1704251 : Blo 1132632 1704251 := bstep (se 1 (by rfl) ⟨1278188, by rfl⟩ : syracuseStep 1704251 = 2556377) B2556377
theorem B1704311 : Blo 1132632 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B1704335 : Blo 1132632 1704335 := bstep (se 1 (by rfl) ⟨1278251, by rfl⟩ : syracuseStep 1704335 = 2556503) B2556503
theorem B1704377 : Blo 1132632 1704377 := bstep (se 2 (by rfl) ⟨639141, by rfl⟩ : syracuseStep 1704377 = 1278283) B1278283
theorem B1704455 : Blo 1132632 1704455 := bstep (se 1 (by rfl) ⟨1278341, by rfl⟩ : syracuseStep 1704455 = 2556683) B2556683
theorem B2556431 : Blo 1132632 2556431 := bstep (se 1 (by rfl) ⟨1917323, by rfl⟩ : syracuseStep 2556431 = 3834647) B3834647
theorem B2556449 : Blo 1132632 2556449 := bstep (se 2 (by rfl) ⟨958668, by rfl⟩ : syracuseStep 2556449 = 1917337) B1917337
theorem B4850219 : Blo 1132632 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B1704491 : Blo 1132632 1704491 := bstep (se 1 (by rfl) ⟨1278368, by rfl⟩ : syracuseStep 1704491 = 2556737) B2556737
theorem B1704521 : Blo 1132632 1704521 := bstep (se 2 (by rfl) ⟨639195, by rfl⟩ : syracuseStep 1704521 = 1278391) B1278391
theorem B1278607 : Blo 1132632 1278607 := bstep (se 1 (by rfl) ⟨958955, by rfl⟩ : syracuseStep 1278607 = 1917911) B1917911
theorem B1704635 : Blo 1132632 1704635 := bstep (se 1 (by rfl) ⟨1278476, by rfl⟩ : syracuseStep 1704635 = 2556953) B2556953
theorem B1704695 : Blo 1132632 1704695 := bstep (se 1 (by rfl) ⟨1278521, by rfl⟩ : syracuseStep 1704695 = 2557043) B2557043
theorem B1704719 : Blo 1132632 1704719 := bstep (se 1 (by rfl) ⟨1278539, by rfl⟩ : syracuseStep 1704719 = 2557079) B2557079
theorem B1704761 : Blo 1132632 1704761 := bstep (se 2 (by rfl) ⟨639285, by rfl⟩ : syracuseStep 1704761 = 1278571) B1278571
theorem B2556791 : Blo 1132632 2556791 := bstep (se 1 (by rfl) ⟨1917593, by rfl⟩ : syracuseStep 2556791 = 3835187) B3835187
theorem B1704839 : Blo 1132632 1704839 := bstep (se 1 (by rfl) ⟨1278629, by rfl⟩ : syracuseStep 1704839 = 2557259) B2557259
theorem B1704875 : Blo 1132632 1704875 := bstep (se 1 (by rfl) ⟨1278656, by rfl⟩ : syracuseStep 1704875 = 2557313) B2557313
theorem B3834809 : Blo 1132632 3834809 := bstep (se 2 (by rfl) ⟨1438053, by rfl⟩ : syracuseStep 3834809 = 2876107) B2876107
theorem B1704905 : Blo 1132632 1704905 := bstep (se 2 (by rfl) ⟨639339, by rfl⟩ : syracuseStep 1704905 = 1278679) B1278679
theorem B5735447 : Blo 1132632 5735447 := bstep (se 1 (by rfl) ⟨4301585, by rfl⟩ : syracuseStep 5735447 = 8603171) B8603171
theorem B2556971 : Blo 1132632 2556971 := bstep (se 1 (by rfl) ⟨1917728, by rfl⟩ : syracuseStep 2556971 = 3835457) B3835457
theorem B8619209 : Blo 1132632 8619209 := bstep (se 2 (by rfl) ⟨3232203, by rfl⟩ : syracuseStep 8619209 = 6464407) B6464407
theorem B2557331 : Blo 1132632 2557331 := bstep (se 1 (by rfl) ⟨1917998, by rfl⟩ : syracuseStep 2557331 = 3835997) B3835997
theorem B2557385 : Blo 1132632 2557385 := bstep (se 2 (by rfl) ⟨959019, by rfl⟩ : syracuseStep 2557385 = 1918039) B1918039
theorem B4851211 : Blo 1132632 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B3835403 : Blo 1132632 3835403 := bstep (se 1 (by rfl) ⟨2876552, by rfl⟩ : syracuseStep 3835403 = 5753105) B5753105
theorem B3835511 : Blo 1132632 3835511 := bstep (se 1 (by rfl) ⟨2876633, by rfl⟩ : syracuseStep 3835511 = 5753267) B5753267
theorem B12945581 : Blo 1132632 12945581 := bstep (se 3 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 12945581 = 4854593) B4854593
theorem B3836105 : Blo 1132632 3836105 := bstep (se 2 (by rfl) ⟨1438539, by rfl⟩ : syracuseStep 3836105 = 2877079) B2877079
theorem B14518673 : Blo 1132632 14518673 := bstep (se 2 (by rfl) ⟨5444502, by rfl⟩ : syracuseStep 14518673 = 10889005) B10889005
theorem B2591275 : Blo 1132632 2591275 := bstep (se 1 (by rfl) ⟨1943456, by rfl⟩ : syracuseStep 2591275 = 3886913) B3886913
theorem B2296505 : Blo 1132632 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B10914497 : Blo 1132632 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B10914533 : Blo 1132632 10914533 := bstep (se 4 (by rfl) ⟨1023237, by rfl⟩ : syracuseStep 10914533 = 2046475) B2046475
theorem B5180219 : Blo 1132632 5180219 := bstep (se 1 (by rfl) ⟨3885164, by rfl⟩ : syracuseStep 5180219 = 7770329) B7770329
theorem B2722675 : Blo 1132632 2722675 := bstep (se 1 (by rfl) ⟨2042006, by rfl⟩ : syracuseStep 2722675 = 4084013) B4084013
theorem B33164147 : Blo 1132632 33164147 := bstep (se 1 (by rfl) ⟨24873110, by rfl⟩ : syracuseStep 33164147 = 49746221) B49746221
theorem B27626629 : Blo 1132632 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B7277971 : Blo 1132632 7277971 := bstep (se 1 (by rfl) ⟨5458478, by rfl⟩ : syracuseStep 7277971 = 10916957) B10916957
theorem B5443159 : Blo 1132632 5443159 := bstep (se 1 (by rfl) ⟨4082369, by rfl⟩ : syracuseStep 5443159 = 8164739) B8164739
theorem B13275031 : Blo 1132632 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B5738525 : Blo 1132632 5738525 := bstep (se 3 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 5738525 = 2151947) B2151947
theorem B2724097 : Blo 1132632 2724097 := bstep (se 2 (by rfl) ⟨1021536, by rfl⟩ : syracuseStep 2724097 = 2043073) B2043073
theorem B6459851 : Blo 1132632 6459851 := bstep (se 1 (by rfl) ⟨4844888, by rfl⟩ : syracuseStep 6459851 = 9689777) B9689777
theorem B5739011 : Blo 1132632 5739011 := bstep (se 1 (by rfl) ⟨4304258, by rfl⟩ : syracuseStep 5739011 = 8608517) B8608517
theorem B2724367 : Blo 1132632 2724367 := bstep (se 1 (by rfl) ⟨2043275, by rfl⟩ : syracuseStep 2724367 = 4086551) B4086551
theorem B5444333 : Blo 1132632 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B6460307 : Blo 1132632 6460307 := bstep (se 1 (by rfl) ⟨4845230, by rfl⟩ : syracuseStep 6460307 = 9690461) B9690461
theorem B14554349 : Blo 1132632 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B18388433 : Blo 1132632 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B2299691 : Blo 1132632 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B2725751 : Blo 1132632 2725751 := bstep (se 1 (by rfl) ⟨2044313, by rfl⟩ : syracuseStep 2725751 = 4088627) B4088627
theorem B6559811 : Blo 1132632 6559811 := bstep (se 1 (by rfl) ⟨4919858, by rfl⟩ : syracuseStep 6559811 = 9839717) B9839717
theorem B5740631 : Blo 1132632 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B17701037 : Blo 1132632 17701037 := bstep (se 3 (by rfl) ⟨3318944, by rfl⟩ : syracuseStep 17701037 = 6637889) B6637889
theorem B3447101 : Blo 1132632 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B12261725 : Blo 1132632 12261725 := bstep (se 3 (by rfl) ⟨2299073, by rfl⟩ : syracuseStep 12261725 = 4598147) B4598147
theorem B5741117 : Blo 1132632 5741117 := bstep (se 3 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 5741117 = 2152919) B2152919
theorem B9214721 : Blo 1132632 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B20716631 : Blo 1132632 20716631 := bstep (se 1 (by rfl) ⟨15537473, by rfl⟩ : syracuseStep 20716631 = 31074947) B31074947
theorem B5446963 : Blo 1132632 5446963 := bstep (se 1 (by rfl) ⟨4085222, by rfl⟩ : syracuseStep 5446963 = 8170445) B8170445
theorem B7380409 : Blo 1132632 7380409 := bstep (se 2 (by rfl) ⟨2767653, by rfl⟩ : syracuseStep 7380409 = 5535307) B5535307
theorem B1613243 : Blo 1132632 1613243 := bstep (se 1 (by rfl) ⟨1209932, by rfl⟩ : syracuseStep 1613243 = 2419865) B2419865
theorem B12426701 : Blo 1132632 12426701 := bstep (se 3 (by rfl) ⟨2330006, by rfl⟩ : syracuseStep 12426701 = 4660013) B4660013
theorem B23273189 : Blo 1132632 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B5447425 : Blo 1132632 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B1613687 : Blo 1132632 1613687 := bstep (se 1 (by rfl) ⟨1210265, by rfl⟩ : syracuseStep 1613687 = 2420531) B2420531
theorem B2727827 : Blo 1132632 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B1613881 : Blo 1132632 1613881 := bstep (se 2 (by rfl) ⟨605205, by rfl⟩ : syracuseStep 1613881 = 1210411) B1210411
theorem B5742899 : Blo 1132632 5742899 := bstep (se 1 (by rfl) ⟨4307174, by rfl⟩ : syracuseStep 5742899 = 8614349) B8614349
theorem B5743223 : Blo 1132632 5743223 := bstep (se 1 (by rfl) ⟨4307417, by rfl⟩ : syracuseStep 5743223 = 8614835) B8614835
theorem B10887857 : Blo 1132632 10887857 := bstep (se 2 (by rfl) ⟨4082946, by rfl⟩ : syracuseStep 10887857 = 8165893) B8165893
theorem B3449719 : Blo 1132632 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B2761673 : Blo 1132632 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B2728961 : Blo 1132632 2728961 := bstep (se 2 (by rfl) ⟨1023360, by rfl⟩ : syracuseStep 2728961 = 2046721) B2046721
theorem B5744195 : Blo 1132632 5744195 := bstep (se 1 (by rfl) ⟨4308146, by rfl⟩ : syracuseStep 5744195 = 8616293) B8616293
theorem B2762425 : Blo 1132632 2762425 := bstep (se 2 (by rfl) ⟨1035909, by rfl⟩ : syracuseStep 2762425 = 2071819) B2071819
theorem B16361189 : Blo 1132632 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B8169265 : Blo 1132632 8169265 := bstep (se 2 (by rfl) ⟨3063474, by rfl⟩ : syracuseStep 8169265 = 6126949) B6126949
theorem B5744519 : Blo 1132632 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B6137867 : Blo 1132632 6137867 := bstep (se 1 (by rfl) ⟨4603400, by rfl⟩ : syracuseStep 6137867 = 9206801) B9206801
theorem B3450995 : Blo 1132632 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B2304119 : Blo 1132632 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B3451081 : Blo 1132632 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B1911431 : Blo 1132632 1911431 := bstep (se 1 (by rfl) ⟨1433573, by rfl⟩ : syracuseStep 1911431 = 2867147) B2867147
theorem B8628929 : Blo 1132632 8628929 := bstep (se 2 (by rfl) ⟨3235848, by rfl⟩ : syracuseStep 8628929 = 6471697) B6471697
theorem B1912079 : Blo 1132632 1912079 := bstep (se 1 (by rfl) ⟨1434059, by rfl⟩ : syracuseStep 1912079 = 2868119) B2868119
theorem B16788871 : Blo 1132632 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B14724611 : Blo 1132632 14724611 := bstep (se 1 (by rfl) ⟨11043458, by rfl⟩ : syracuseStep 14724611 = 22086917) B22086917
theorem B9678365 : Blo 1132632 9678365 := bstep (se 3 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 9678365 = 3629387) B3629387
theorem B23277131 : Blo 1132632 23277131 := bstep (se 1 (by rfl) ⟨17457848, by rfl⟩ : syracuseStep 23277131 = 34915697) B34915697
theorem B46542437 : Blo 1132632 46542437 := bstep (se 4 (by rfl) ⟨4363353, by rfl⟩ : syracuseStep 46542437 = 8726707) B8726707
theorem B1912619 : Blo 1132632 1912619 := bstep (se 1 (by rfl) ⟨1434464, by rfl⟩ : syracuseStep 1912619 = 2868929) B2868929
theorem B1913017 : Blo 1132632 1913017 := bstep (se 2 (by rfl) ⟨717381, by rfl⟩ : syracuseStep 1913017 = 1434763) B1434763
theorem B8172035 : Blo 1132632 8172035 := bstep (se 1 (by rfl) ⟨6129026, by rfl⟩ : syracuseStep 8172035 = 12258053) B12258053
theorem B11055619 : Blo 1132632 11055619 := bstep (se 1 (by rfl) ⟨8291714, by rfl⟩ : syracuseStep 11055619 = 16583429) B16583429
theorem B10891853 : Blo 1132632 10891853 := bstep (se 3 (by rfl) ⟨2042222, by rfl⟩ : syracuseStep 10891853 = 4084445) B4084445
theorem B56013443 : Blo 1132632 56013443 := bstep (se 1 (by rfl) ⟨42010082, by rfl⟩ : syracuseStep 56013443 = 84020165) B84020165
theorem B14725903 : Blo 1132632 14725903 := bstep (se 1 (by rfl) ⟨11044427, by rfl⟩ : syracuseStep 14725903 = 22088855) B22088855
theorem B1913719 : Blo 1132632 1913719 := bstep (se 1 (by rfl) ⟨1435289, by rfl⟩ : syracuseStep 1913719 = 2870579) B2870579
theorem B1913915 : Blo 1132632 1913915 := bstep (se 1 (by rfl) ⟨1435436, by rfl⟩ : syracuseStep 1913915 = 2870873) B2870873
theorem B6468781 : Blo 1132632 6468781 := bstep (se 3 (by rfl) ⟨1212896, by rfl⟩ : syracuseStep 6468781 = 2425793) B2425793
theorem B4601069 : Blo 1132632 4601069 := bstep (se 3 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 4601069 = 1725401) B1725401
theorem B6141199 : Blo 1132632 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B21804389 : Blo 1132632 21804389 := bstep (se 4 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 21804389 = 4088323) B4088323
theorem B5748083 : Blo 1132632 5748083 := bstep (se 1 (by rfl) ⟨4311062, by rfl⟩ : syracuseStep 5748083 = 8622125) B8622125
theorem B6141329 : Blo 1132632 6141329 := bstep (se 2 (by rfl) ⟨2302998, by rfl⟩ : syracuseStep 6141329 = 4605997) B4605997
theorem B1914313 : Blo 1132632 1914313 := bstep (se 2 (by rfl) ⟨717867, by rfl⟩ : syracuseStep 1914313 = 1435735) B1435735
theorem B4306385 : Blo 1132632 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B4666999 : Blo 1132632 4666999 := bstep (se 1 (by rfl) ⟨3500249, by rfl⟩ : syracuseStep 4666999 = 7000499) B7000499
theorem B15546113 : Blo 1132632 15546113 := bstep (se 2 (by rfl) ⟨5829792, by rfl⟩ : syracuseStep 15546113 = 11659585) B11659585
theorem B3225359 : Blo 1132632 3225359 := bstep (se 1 (by rfl) ⟨2419019, by rfl⟩ : syracuseStep 3225359 = 4838039) B4838039
theorem B5748569 : Blo 1132632 5748569 := bstep (se 2 (by rfl) ⟨2155713, by rfl⟩ : syracuseStep 5748569 = 4311427) B4311427
theorem B9680755 : Blo 1132632 9680755 := bstep (se 1 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 9680755 = 14521133) B14521133
theorem B6895475 : Blo 1132632 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B4306841 : Blo 1132632 4306841 := bstep (se 2 (by rfl) ⟨1615065, by rfl⟩ : syracuseStep 4306841 = 3230131) B3230131
theorem B9681029 : Blo 1132632 9681029 := bstep (se 4 (by rfl) ⟨907596, by rfl⟩ : syracuseStep 9681029 = 1815193) B1815193
theorem B1915015 : Blo 1132632 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B1816847 : Blo 1132632 1816847 := bstep (se 1 (by rfl) ⟨1362635, by rfl⟩ : syracuseStep 1816847 = 2725271) B2725271
theorem B1915663 : Blo 1132632 1915663 := bstep (se 1 (by rfl) ⟨1436747, by rfl⟩ : syracuseStep 1915663 = 2873495) B2873495
theorem B9681713 : Blo 1132632 9681713 := bstep (se 2 (by rfl) ⟨3630642, by rfl⟩ : syracuseStep 9681713 = 7261285) B7261285
theorem B4602739 : Blo 1132632 4602739 := bstep (se 1 (by rfl) ⟨3452054, by rfl⟩ : syracuseStep 4602739 = 6904109) B6904109
theorem B4308011 : Blo 1132632 4308011 := bstep (se 1 (by rfl) ⟨3231008, by rfl⟩ : syracuseStep 4308011 = 6462017) B6462017
theorem B1916203 : Blo 1132632 1916203 := bstep (se 1 (by rfl) ⟨1437152, by rfl⟩ : syracuseStep 1916203 = 2874305) B2874305
theorem B3226999 : Blo 1132632 3226999 := bstep (se 1 (by rfl) ⟨2420249, by rfl⟩ : syracuseStep 3226999 = 4840499) B4840499
theorem B3227033 : Blo 1132632 3227033 := bstep (se 2 (by rfl) ⟨1210137, by rfl⟩ : syracuseStep 3227033 = 2420275) B2420275
theorem B1916345 : Blo 1132632 1916345 := bstep (se 2 (by rfl) ⟨718629, by rfl⟩ : syracuseStep 1916345 = 1437259) B1437259
theorem B3227147 : Blo 1132632 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B6471197 : Blo 1132632 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B5455421 : Blo 1132632 5455421 := bstep (se 3 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 5455421 = 2045783) B2045783
theorem B13811471 : Blo 1132632 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B3063595 : Blo 1132632 3063595 := bstep (se 1 (by rfl) ⟨2297696, by rfl⟩ : syracuseStep 3063595 = 4595393) B4595393
theorem B9682739 : Blo 1132632 9682739 := bstep (se 1 (by rfl) ⟨7262054, by rfl⟩ : syracuseStep 9682739 = 14524109) B14524109
theorem B1818487 : Blo 1132632 1818487 := bstep (se 1 (by rfl) ⟨1363865, by rfl⟩ : syracuseStep 1818487 = 2727731) B2727731
theorem B5750675 : Blo 1132632 5750675 := bstep (se 1 (by rfl) ⟨4313006, by rfl⟩ : syracuseStep 5750675 = 8626013) B8626013
theorem B6897611 : Blo 1132632 6897611 := bstep (se 1 (by rfl) ⟨5173208, by rfl⟩ : syracuseStep 6897611 = 10346417) B10346417
theorem B4669483 : Blo 1132632 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B1917047 : Blo 1132632 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1228943 : Blo 1132632 1228943 := bstep (se 1 (by rfl) ⟨921707, by rfl⟩ : syracuseStep 1228943 = 1843415) B1843415
theorem B8732873 : Blo 1132632 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B2867471 : Blo 1132632 2867471 := bstep (se 1 (by rfl) ⟨2150603, by rfl⟩ : syracuseStep 2867471 = 4301207) B4301207
theorem B12271931 : Blo 1132632 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B1917499 : Blo 1132632 1917499 := bstep (se 1 (by rfl) ⟨1438124, by rfl⟩ : syracuseStep 1917499 = 2876249) B2876249
theorem B3228275 : Blo 1132632 3228275 := bstep (se 1 (by rfl) ⟨2421206, by rfl⟩ : syracuseStep 3228275 = 4842413) B4842413
theorem B1917641 : Blo 1132632 1917641 := bstep (se 2 (by rfl) ⟨719115, by rfl⟩ : syracuseStep 1917641 = 1438231) B1438231
theorem B1295291 : Blo 1132632 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B2868169 : Blo 1132632 2868169 := bstep (se 2 (by rfl) ⟨1075563, by rfl⟩ : syracuseStep 2868169 = 2151127) B2151127
theorem B4309969 : Blo 1132632 4309969 := bstep (se 2 (by rfl) ⟨1616238, by rfl⟩ : syracuseStep 4309969 = 3232477) B3232477
theorem B3228673 : Blo 1132632 3228673 := bstep (se 2 (by rfl) ⟨1210752, by rfl⟩ : syracuseStep 3228673 = 2421505) B2421505
theorem B3228731 : Blo 1132632 3228731 := bstep (se 1 (by rfl) ⟨2421548, by rfl⟩ : syracuseStep 3228731 = 4843097) B4843097
theorem B8602685 : Blo 1132632 8602685 := bstep (se 3 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 8602685 = 3226007) B3226007
theorem B2868311 : Blo 1132632 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B3064979 : Blo 1132632 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B3884233 : Blo 1132632 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B4310273 : Blo 1132632 4310273 := bstep (se 2 (by rfl) ⟨1616352, by rfl⟩ : syracuseStep 4310273 = 3232705) B3232705
theorem B24495767 : Blo 1132632 24495767 := bstep (se 1 (by rfl) ⟨18371825, by rfl⟩ : syracuseStep 24495767 = 36743651) B36743651
theorem B4310729 : Blo 1132632 4310729 := bstep (se 2 (by rfl) ⟨1616523, by rfl⟩ : syracuseStep 4310729 = 3233047) B3233047
theorem B6899507 : Blo 1132632 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B13781015 : Blo 1132632 13781015 := bstep (se 1 (by rfl) ⟨10335761, by rfl⟩ : syracuseStep 13781015 = 20671523) B20671523
theorem B16566295 : Blo 1132632 16566295 := bstep (se 1 (by rfl) ⟨12424721, by rfl⟩ : syracuseStep 16566295 = 24849443) B24849443
theorem B1132679 : Blo 1132632 1132679 := bstep (se 1 (by rfl) ⟨849509, by rfl⟩ : syracuseStep 1132679 = 1699019) B1699019
theorem B1132687 : Blo 1132632 1132687 := bstep (se 1 (by rfl) ⟨849515, by rfl⟩ : syracuseStep 1132687 = 1699031) B1699031
theorem B1132731 : Blo 1132632 1132731 := bstep (se 1 (by rfl) ⟨849548, by rfl⟩ : syracuseStep 1132731 = 1699097) B1699097
theorem B1132807 : Blo 1132632 1132807 := bstep (se 1 (by rfl) ⟨849605, by rfl⟩ : syracuseStep 1132807 = 1699211) B1699211
theorem B1132815 : Blo 1132632 1132815 := bstep (se 1 (by rfl) ⟨849611, by rfl⟩ : syracuseStep 1132815 = 1699223) B1699223
theorem B1132859 : Blo 1132632 1132859 := bstep (se 1 (by rfl) ⟨849644, by rfl⟩ : syracuseStep 1132859 = 1699289) B1699289
theorem B1132935 : Blo 1132632 1132935 := bstep (se 1 (by rfl) ⟨849701, by rfl⟩ : syracuseStep 1132935 = 1699403) B1699403
theorem B1132943 : Blo 1132632 1132943 := bstep (se 1 (by rfl) ⟨849707, by rfl⟩ : syracuseStep 1132943 = 1699415) B1699415
theorem B1132987 : Blo 1132632 1132987 := bstep (se 1 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 1132987 = 1699481) B1699481
theorem B1133063 : Blo 1132632 1133063 := bstep (se 1 (by rfl) ⟨849797, by rfl⟩ : syracuseStep 1133063 = 1699595) B1699595
theorem B1133071 : Blo 1132632 1133071 := bstep (se 1 (by rfl) ⟨849803, by rfl⟩ : syracuseStep 1133071 = 1699607) B1699607
theorem B1133115 : Blo 1132632 1133115 := bstep (se 1 (by rfl) ⟨849836, by rfl⟩ : syracuseStep 1133115 = 1699673) B1699673
theorem B1133191 : Blo 1132632 1133191 := bstep (se 1 (by rfl) ⟨849893, by rfl⟩ : syracuseStep 1133191 = 1699787) B1699787
theorem B1133199 : Blo 1132632 1133199 := bstep (se 1 (by rfl) ⟨849899, by rfl⟩ : syracuseStep 1133199 = 1699799) B1699799
theorem B1133243 : Blo 1132632 1133243 := bstep (se 1 (by rfl) ⟨849932, by rfl⟩ : syracuseStep 1133243 = 1699865) B1699865
theorem B1133319 : Blo 1132632 1133319 := bstep (se 1 (by rfl) ⟨849989, by rfl⟩ : syracuseStep 1133319 = 1699979) B1699979
theorem B1133327 : Blo 1132632 1133327 := bstep (se 1 (by rfl) ⟨849995, by rfl⟩ : syracuseStep 1133327 = 1699991) B1699991
theorem B1133371 : Blo 1132632 1133371 := bstep (se 1 (by rfl) ⟨850028, by rfl⟩ : syracuseStep 1133371 = 1700057) B1700057
theorem B1133447 : Blo 1132632 1133447 := bstep (se 1 (by rfl) ⟨850085, by rfl⟩ : syracuseStep 1133447 = 1700171) B1700171
theorem B1133455 : Blo 1132632 1133455 := bstep (se 1 (by rfl) ⟨850091, by rfl⟩ : syracuseStep 1133455 = 1700183) B1700183
theorem B5753753 : Blo 1132632 5753753 := bstep (se 2 (by rfl) ⟨2157657, by rfl⟩ : syracuseStep 5753753 = 4315315) B4315315
theorem B1133499 : Blo 1132632 1133499 := bstep (se 1 (by rfl) ⟨850124, by rfl⟩ : syracuseStep 1133499 = 1700249) B1700249
theorem B1133575 : Blo 1132632 1133575 := bstep (se 1 (by rfl) ⟨850181, by rfl⟩ : syracuseStep 1133575 = 1700363) B1700363
theorem B1133583 : Blo 1132632 1133583 := bstep (se 1 (by rfl) ⟨850187, by rfl⟩ : syracuseStep 1133583 = 1700375) B1700375
theorem B1133627 : Blo 1132632 1133627 := bstep (se 1 (by rfl) ⟨850220, by rfl⟩ : syracuseStep 1133627 = 1700441) B1700441
theorem B2870387 : Blo 1132632 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B1133703 : Blo 1132632 1133703 := bstep (se 1 (by rfl) ⟨850277, by rfl⟩ : syracuseStep 1133703 = 1700555) B1700555
theorem B1133711 : Blo 1132632 1133711 := bstep (se 1 (by rfl) ⟨850283, by rfl⟩ : syracuseStep 1133711 = 1700567) B1700567
theorem B1133755 : Blo 1132632 1133755 := bstep (se 1 (by rfl) ⟨850316, by rfl⟩ : syracuseStep 1133755 = 1700633) B1700633
theorem B1133831 : Blo 1132632 1133831 := bstep (se 1 (by rfl) ⟨850373, by rfl⟩ : syracuseStep 1133831 = 1700747) B1700747
theorem B1133839 : Blo 1132632 1133839 := bstep (se 1 (by rfl) ⟨850379, by rfl⟩ : syracuseStep 1133839 = 1700759) B1700759
theorem B3231019 : Blo 1132632 3231019 := bstep (se 1 (by rfl) ⟨2423264, by rfl⟩ : syracuseStep 3231019 = 4846529) B4846529
theorem B1133883 : Blo 1132632 1133883 := bstep (se 1 (by rfl) ⟨850412, by rfl⟩ : syracuseStep 1133883 = 1700825) B1700825
theorem B1133959 : Blo 1132632 1133959 := bstep (se 1 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 1133959 = 1700939) B1700939
theorem B1133967 : Blo 1132632 1133967 := bstep (se 1 (by rfl) ⟨850475, by rfl⟩ : syracuseStep 1133967 = 1700951) B1700951
theorem B5459345 : Blo 1132632 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1134011 : Blo 1132632 1134011 := bstep (se 1 (by rfl) ⟨850508, by rfl⟩ : syracuseStep 1134011 = 1701017) B1701017
theorem B2182601 : Blo 1132632 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B1134087 : Blo 1132632 1134087 := bstep (se 1 (by rfl) ⟨850565, by rfl⟩ : syracuseStep 1134087 = 1701131) B1701131
theorem B1134095 : Blo 1132632 1134095 := bstep (se 1 (by rfl) ⟨850571, by rfl⟩ : syracuseStep 1134095 = 1701143) B1701143
theorem B3231247 : Blo 1132632 3231247 := bstep (se 1 (by rfl) ⟨2423435, by rfl⟩ : syracuseStep 3231247 = 4846871) B4846871
theorem B1134139 : Blo 1132632 1134139 := bstep (se 1 (by rfl) ⟨850604, by rfl⟩ : syracuseStep 1134139 = 1701209) B1701209
theorem B3067507 : Blo 1132632 3067507 := bstep (se 1 (by rfl) ⟨2300630, by rfl⟩ : syracuseStep 3067507 = 4601261) B4601261
theorem B2870903 : Blo 1132632 2870903 := bstep (se 1 (by rfl) ⟨2153177, by rfl⟩ : syracuseStep 2870903 = 4306355) B4306355
theorem B1134215 : Blo 1132632 1134215 := bstep (se 1 (by rfl) ⟨850661, by rfl⟩ : syracuseStep 1134215 = 1701323) B1701323
theorem B1134223 : Blo 1132632 1134223 := bstep (se 1 (by rfl) ⟨850667, by rfl⟩ : syracuseStep 1134223 = 1701335) B1701335
theorem B1134267 : Blo 1132632 1134267 := bstep (se 1 (by rfl) ⟨850700, by rfl⟩ : syracuseStep 1134267 = 1701401) B1701401
theorem B1134343 : Blo 1132632 1134343 := bstep (se 1 (by rfl) ⟨850757, by rfl⟩ : syracuseStep 1134343 = 1701515) B1701515
theorem B1134351 : Blo 1132632 1134351 := bstep (se 1 (by rfl) ⟨850763, by rfl⟩ : syracuseStep 1134351 = 1701527) B1701527
theorem B3231521 : Blo 1132632 3231521 := bstep (se 2 (by rfl) ⟨1211820, by rfl⟩ : syracuseStep 3231521 = 2423641) B2423641
theorem B1134395 : Blo 1132632 1134395 := bstep (se 1 (by rfl) ⟨850796, by rfl⟩ : syracuseStep 1134395 = 1701593) B1701593
theorem B1134471 : Blo 1132632 1134471 := bstep (se 1 (by rfl) ⟨850853, by rfl⟩ : syracuseStep 1134471 = 1701707) B1701707
theorem B1134479 : Blo 1132632 1134479 := bstep (se 1 (by rfl) ⟨850859, by rfl⟩ : syracuseStep 1134479 = 1701719) B1701719
theorem B1134523 : Blo 1132632 1134523 := bstep (se 1 (by rfl) ⟨850892, by rfl⟩ : syracuseStep 1134523 = 1701785) B1701785
theorem B10899461 : Blo 1132632 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B1134599 : Blo 1132632 1134599 := bstep (se 1 (by rfl) ⟨850949, by rfl⟩ : syracuseStep 1134599 = 1701899) B1701899
theorem B1134607 : Blo 1132632 1134607 := bstep (se 1 (by rfl) ⟨850955, by rfl⟩ : syracuseStep 1134607 = 1701911) B1701911
theorem B2150459 : Blo 1132632 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B1134651 : Blo 1132632 1134651 := bstep (se 1 (by rfl) ⟨850988, by rfl⟩ : syracuseStep 1134651 = 1701977) B1701977
theorem B3231863 : Blo 1132632 3231863 := bstep (se 1 (by rfl) ⟨2423897, by rfl⟩ : syracuseStep 3231863 = 4847795) B4847795
theorem B1134727 : Blo 1132632 1134727 := bstep (se 1 (by rfl) ⟨851045, by rfl⟩ : syracuseStep 1134727 = 1702091) B1702091
theorem B1134735 : Blo 1132632 1134735 := bstep (se 1 (by rfl) ⟨851051, by rfl⟩ : syracuseStep 1134735 = 1702103) B1702103
theorem B1134779 : Blo 1132632 1134779 := bstep (se 1 (by rfl) ⟨851084, by rfl⟩ : syracuseStep 1134779 = 1702169) B1702169
theorem B1134855 : Blo 1132632 1134855 := bstep (se 1 (by rfl) ⟨851141, by rfl⟩ : syracuseStep 1134855 = 1702283) B1702283
theorem B1134863 : Blo 1132632 1134863 := bstep (se 1 (by rfl) ⟨851147, by rfl⟩ : syracuseStep 1134863 = 1702295) B1702295
theorem B1134907 : Blo 1132632 1134907 := bstep (se 1 (by rfl) ⟨851180, by rfl⟩ : syracuseStep 1134907 = 1702361) B1702361
theorem B8606087 : Blo 1132632 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B1134983 : Blo 1132632 1134983 := bstep (se 1 (by rfl) ⟨851237, by rfl⟩ : syracuseStep 1134983 = 1702475) B1702475
theorem B1134991 : Blo 1132632 1134991 := bstep (se 1 (by rfl) ⟨851243, by rfl⟩ : syracuseStep 1134991 = 1702487) B1702487
theorem B1135035 : Blo 1132632 1135035 := bstep (se 1 (by rfl) ⟨851276, by rfl⟩ : syracuseStep 1135035 = 1702553) B1702553
theorem B1135111 : Blo 1132632 1135111 := bstep (se 1 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 1135111 = 1702667) B1702667
theorem B1135119 : Blo 1132632 1135119 := bstep (se 1 (by rfl) ⟨851339, by rfl⟩ : syracuseStep 1135119 = 1702679) B1702679
theorem B2150945 : Blo 1132632 2150945 := bstep (se 2 (by rfl) ⟨806604, by rfl⟩ : syracuseStep 2150945 = 1613209) B1613209
theorem B1135163 : Blo 1132632 1135163 := bstep (se 1 (by rfl) ⟨851372, by rfl⟩ : syracuseStep 1135163 = 1702745) B1702745
theorem B2871895 : Blo 1132632 2871895 := bstep (se 1 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 2871895 = 4307843) B4307843
theorem B1135239 : Blo 1132632 1135239 := bstep (se 1 (by rfl) ⟨851429, by rfl⟩ : syracuseStep 1135239 = 1702859) B1702859
theorem B1135247 : Blo 1132632 1135247 := bstep (se 1 (by rfl) ⟨851435, by rfl⟩ : syracuseStep 1135247 = 1702871) B1702871
theorem B1135291 : Blo 1132632 1135291 := bstep (se 1 (by rfl) ⟨851468, by rfl⟩ : syracuseStep 1135291 = 1702937) B1702937
theorem B4838089 : Blo 1132632 4838089 := bstep (se 2 (by rfl) ⟨1814283, by rfl⟩ : syracuseStep 4838089 = 3628567) B3628567
theorem B4313857 : Blo 1132632 4313857 := bstep (se 2 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 4313857 = 3235393) B3235393
theorem B1135367 : Blo 1132632 1135367 := bstep (se 1 (by rfl) ⟨851525, by rfl⟩ : syracuseStep 1135367 = 1703051) B1703051
theorem B3232523 : Blo 1132632 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B1135375 : Blo 1132632 1135375 := bstep (se 1 (by rfl) ⟨851531, by rfl⟩ : syracuseStep 1135375 = 1703063) B1703063
theorem B2151211 : Blo 1132632 2151211 := bstep (se 1 (by rfl) ⟨1613408, by rfl⟩ : syracuseStep 2151211 = 3226817) B3226817
theorem B1135419 : Blo 1132632 1135419 := bstep (se 1 (by rfl) ⟨851564, by rfl⟩ : syracuseStep 1135419 = 1703129) B1703129
theorem B1364855 : Blo 1132632 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B2872199 : Blo 1132632 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1135495 : Blo 1132632 1135495 := bstep (se 1 (by rfl) ⟨851621, by rfl⟩ : syracuseStep 1135495 = 1703243) B1703243
theorem B1135503 : Blo 1132632 1135503 := bstep (se 1 (by rfl) ⟨851627, by rfl⟩ : syracuseStep 1135503 = 1703255) B1703255
theorem B1135547 : Blo 1132632 1135547 := bstep (se 1 (by rfl) ⟨851660, by rfl⟩ : syracuseStep 1135547 = 1703321) B1703321
theorem B1135623 : Blo 1132632 1135623 := bstep (se 1 (by rfl) ⟨851717, by rfl⟩ : syracuseStep 1135623 = 1703435) B1703435
theorem B2872331 : Blo 1132632 2872331 := bstep (se 1 (by rfl) ⟨2154248, by rfl⟩ : syracuseStep 2872331 = 4308497) B4308497
theorem B1135631 : Blo 1132632 1135631 := bstep (se 1 (by rfl) ⟨851723, by rfl⟩ : syracuseStep 1135631 = 1703447) B1703447
theorem B1135675 : Blo 1132632 1135675 := bstep (se 1 (by rfl) ⟨851756, by rfl⟩ : syracuseStep 1135675 = 1703513) B1703513
theorem B1135751 : Blo 1132632 1135751 := bstep (se 1 (by rfl) ⟨851813, by rfl⟩ : syracuseStep 1135751 = 1703627) B1703627
theorem B1135759 : Blo 1132632 1135759 := bstep (se 1 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 1135759 = 1703639) B1703639
theorem B1135803 : Blo 1132632 1135803 := bstep (se 1 (by rfl) ⟨851852, by rfl⟩ : syracuseStep 1135803 = 1703705) B1703705
theorem B4084937 : Blo 1132632 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1135879 : Blo 1132632 1135879 := bstep (se 1 (by rfl) ⟨851909, by rfl⟩ : syracuseStep 1135879 = 1703819) B1703819
theorem B1135887 : Blo 1132632 1135887 := bstep (se 1 (by rfl) ⟨851915, by rfl⟩ : syracuseStep 1135887 = 1703831) B1703831
theorem B1135931 : Blo 1132632 1135931 := bstep (se 1 (by rfl) ⟨851948, by rfl⟩ : syracuseStep 1135931 = 1703897) B1703897
theorem B3822983 : Blo 1132632 3822983 := bstep (se 1 (by rfl) ⟨2867237, by rfl⟩ : syracuseStep 3822983 = 5734475) B5734475
theorem B23287175 : Blo 1132632 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B1136007 : Blo 1132632 1136007 := bstep (se 1 (by rfl) ⟨852005, by rfl⟩ : syracuseStep 1136007 = 1704011) B1704011
theorem B1136015 : Blo 1132632 1136015 := bstep (se 1 (by rfl) ⟨852011, by rfl⟩ : syracuseStep 1136015 = 1704023) B1704023
theorem B4904339 : Blo 1132632 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B1136059 : Blo 1132632 1136059 := bstep (se 1 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 1136059 = 1704089) B1704089
theorem B1136135 : Blo 1132632 1136135 := bstep (se 1 (by rfl) ⟨852101, by rfl⟩ : syracuseStep 1136135 = 1704203) B1704203
theorem B2872847 : Blo 1132632 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B1136143 : Blo 1132632 1136143 := bstep (se 1 (by rfl) ⟨852107, by rfl⟩ : syracuseStep 1136143 = 1704215) B1704215
theorem B1136187 : Blo 1132632 1136187 := bstep (se 1 (by rfl) ⟨852140, by rfl⟩ : syracuseStep 1136187 = 1704281) B1704281
theorem B9819767 : Blo 1132632 9819767 := bstep (se 1 (by rfl) ⟨7364825, by rfl⟩ : syracuseStep 9819767 = 14729651) B14729651
theorem B1136263 : Blo 1132632 1136263 := bstep (se 1 (by rfl) ⟨852197, by rfl⟩ : syracuseStep 1136263 = 1704395) B1704395
theorem B1136271 : Blo 1132632 1136271 := bstep (se 1 (by rfl) ⟨852203, by rfl⟩ : syracuseStep 1136271 = 1704407) B1704407
theorem B2872979 : Blo 1132632 2872979 := bstep (se 1 (by rfl) ⟨2154734, by rfl⟩ : syracuseStep 2872979 = 4309469) B4309469
theorem B1136315 : Blo 1132632 1136315 := bstep (se 1 (by rfl) ⟨852236, by rfl⟩ : syracuseStep 1136315 = 1704473) B1704473
theorem B3823361 : Blo 1132632 3823361 := bstep (se 2 (by rfl) ⟨1433760, by rfl⟩ : syracuseStep 3823361 = 2867521) B2867521
theorem B1136391 : Blo 1132632 1136391 := bstep (se 1 (by rfl) ⟨852293, by rfl⟩ : syracuseStep 1136391 = 1704587) B1704587
theorem B1136399 : Blo 1132632 1136399 := bstep (se 1 (by rfl) ⟨852299, by rfl⟩ : syracuseStep 1136399 = 1704599) B1704599
theorem B1136443 : Blo 1132632 1136443 := bstep (se 1 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 1136443 = 1704665) B1704665
theorem B2152327 : Blo 1132632 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B1136519 : Blo 1132632 1136519 := bstep (se 1 (by rfl) ⟨852389, by rfl⟩ : syracuseStep 1136519 = 1704779) B1704779
theorem B1136527 : Blo 1132632 1136527 := bstep (se 1 (by rfl) ⟨852395, by rfl⟩ : syracuseStep 1136527 = 1704791) B1704791
theorem B1136571 : Blo 1132632 1136571 := bstep (se 1 (by rfl) ⟨852428, by rfl⟩ : syracuseStep 1136571 = 1704857) B1704857
theorem B4839695 : Blo 1132632 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B3234107 : Blo 1132632 3234107 := bstep (se 1 (by rfl) ⟨2425580, by rfl⟩ : syracuseStep 3234107 = 4851161) B4851161
theorem B3234163 : Blo 1132632 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B2152889 : Blo 1132632 2152889 := bstep (se 2 (by rfl) ⟨807333, by rfl⟩ : syracuseStep 2152889 = 1614667) B1614667
theorem B3824171 : Blo 1132632 3824171 := bstep (se 1 (by rfl) ⟨2868128, by rfl⟩ : syracuseStep 3824171 = 5736257) B5736257
theorem B3234505 : Blo 1132632 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B2874113 : Blo 1132632 2874113 := bstep (se 2 (by rfl) ⟨1077792, by rfl⟩ : syracuseStep 2874113 = 2155585) B2155585
theorem B2874487 : Blo 1132632 2874487 := bstep (se 1 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 2874487 = 4311731) B4311731
theorem B12901841 : Blo 1132632 12901841 := bstep (se 2 (by rfl) ⟨4838190, by rfl⟩ : syracuseStep 12901841 = 9676381) B9676381
theorem B2874923 : Blo 1132632 2874923 := bstep (se 1 (by rfl) ⟨2156192, by rfl⟩ : syracuseStep 2874923 = 4312385) B4312385
theorem B2154043 : Blo 1132632 2154043 := bstep (se 1 (by rfl) ⟨1615532, by rfl⟩ : syracuseStep 2154043 = 3231065) B3231065
theorem B4087415 : Blo 1132632 4087415 := bstep (se 1 (by rfl) ⟨3065561, by rfl⟩ : syracuseStep 4087415 = 6131123) B6131123
theorem B11034305 : Blo 1132632 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B3825467 : Blo 1132632 3825467 := bstep (se 1 (by rfl) ⟨2869100, by rfl⟩ : syracuseStep 3825467 = 5738201) B5738201
theorem B12443543 : Blo 1132632 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B2154529 : Blo 1132632 2154529 := bstep (se 2 (by rfl) ⟨807948, by rfl⟩ : syracuseStep 2154529 = 1615897) B1615897
theorem B3825953 : Blo 1132632 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B2875763 : Blo 1132632 2875763 := bstep (se 1 (by rfl) ⟨2156822, by rfl⟩ : syracuseStep 2875763 = 4313645) B4313645
theorem B2875783 : Blo 1132632 2875783 := bstep (se 1 (by rfl) ⟨2156837, by rfl⟩ : syracuseStep 2875783 = 4313675) B4313675
theorem B2876057 : Blo 1132632 2876057 := bstep (se 2 (by rfl) ⟨1078521, by rfl⟩ : syracuseStep 2876057 = 2157043) B2157043
theorem B2876219 : Blo 1132632 2876219 := bstep (se 1 (by rfl) ⟨2157164, by rfl⟩ : syracuseStep 2876219 = 4314329) B4314329
theorem B3236669 : Blo 1132632 3236669 := bstep (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) B1213751
theorem B3826547 : Blo 1132632 3826547 := bstep (se 1 (by rfl) ⟨2869910, by rfl⟩ : syracuseStep 3826547 = 5739821) B5739821
theorem B2876431 : Blo 1132632 2876431 := bstep (se 1 (by rfl) ⟨2157323, by rfl⟩ : syracuseStep 2876431 = 4314647) B4314647
theorem B1434667 : Blo 1132632 1434667 := bstep (se 1 (by rfl) ⟨1076000, by rfl⟩ : syracuseStep 1434667 = 2152001) B2152001
theorem B2548871 : Blo 1132632 2548871 := bstep (se 1 (by rfl) ⟨1911653, by rfl⟩ : syracuseStep 2548871 = 3823307) B3823307
theorem B13821101 : Blo 1132632 13821101 := bstep (se 3 (by rfl) ⟨2591456, by rfl⟩ : syracuseStep 13821101 = 5182913) B5182913
theorem B2876705 : Blo 1132632 2876705 := bstep (se 2 (by rfl) ⟨1078764, by rfl⟩ : syracuseStep 2876705 = 2157529) B2157529
theorem B2549051 : Blo 1132632 2549051 := bstep (se 1 (by rfl) ⟨1911788, by rfl⟩ : syracuseStep 2549051 = 3823577) B3823577
theorem B7267643 : Blo 1132632 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 1132632 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B2549177 : Blo 1132632 2549177 := bstep (se 2 (by rfl) ⟨955941, by rfl⟩ : syracuseStep 2549177 = 1911883) B1911883
theorem B2549519 : Blo 1132632 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B2549537 : Blo 1132632 2549537 := bstep (se 2 (by rfl) ⟨956076, by rfl⟩ : syracuseStep 2549537 = 1912153) B1912153
theorem B2156321 : Blo 1132632 2156321 := bstep (se 2 (by rfl) ⟨808620, by rfl⟩ : syracuseStep 2156321 = 1617241) B1617241
theorem B2156473 : Blo 1132632 2156473 := bstep (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) B1617355
theorem B1435639 : Blo 1132632 1435639 := bstep (se 1 (by rfl) ⟨1076729, by rfl⟩ : syracuseStep 1435639 = 2153459) B2153459
theorem B2549879 : Blo 1132632 2549879 := bstep (se 1 (by rfl) ⟨1912409, by rfl⟩ : syracuseStep 2549879 = 3824819) B3824819
theorem B2550059 : Blo 1132632 2550059 := bstep (se 1 (by rfl) ⟨1912544, by rfl⟩ : syracuseStep 2550059 = 3825089) B3825089
theorem B1435963 : Blo 1132632 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B10906001 : Blo 1132632 10906001 := bstep (se 2 (by rfl) ⟨4089750, by rfl⟩ : syracuseStep 10906001 = 8179501) B8179501
theorem B26176067 : Blo 1132632 26176067 := bstep (se 1 (by rfl) ⟨19632050, by rfl⟩ : syracuseStep 26176067 = 39264101) B39264101
theorem B2550419 : Blo 1132632 2550419 := bstep (se 1 (by rfl) ⟨1912814, by rfl⟩ : syracuseStep 2550419 = 3825629) B3825629
theorem B2550473 : Blo 1132632 2550473 := bstep (se 2 (by rfl) ⟨956427, by rfl⟩ : syracuseStep 2550473 = 1912855) B1912855
theorem B3631873 : Blo 1132632 3631873 := bstep (se 2 (by rfl) ⟨1361952, by rfl⟩ : syracuseStep 3631873 = 2723905) B2723905
theorem B1698959 : Blo 1132632 1698959 := bstep (se 1 (by rfl) ⟨1274219, by rfl⟩ : syracuseStep 1698959 = 2548439) B2548439
theorem B1699001 : Blo 1132632 1699001 := bstep (se 2 (by rfl) ⟨637125, by rfl⟩ : syracuseStep 1699001 = 1274251) B1274251
theorem B21818605 : Blo 1132632 21818605 := bstep (se 3 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 21818605 = 8181977) B8181977
theorem B1699079 : Blo 1132632 1699079 := bstep (se 1 (by rfl) ⟨1274309, by rfl⟩ : syracuseStep 1699079 = 2548619) B2548619
theorem B1436935 : Blo 1132632 1436935 := bstep (se 1 (by rfl) ⟨1077701, by rfl⟩ : syracuseStep 1436935 = 2155403) B2155403
theorem B1699115 : Blo 1132632 1699115 := bstep (se 1 (by rfl) ⟨1274336, by rfl⟩ : syracuseStep 1699115 = 2548673) B2548673
theorem B1699145 : Blo 1132632 1699145 := bstep (se 2 (by rfl) ⟨637179, by rfl⟩ : syracuseStep 1699145 = 1274359) B1274359
theorem B2551175 : Blo 1132632 2551175 := bstep (se 1 (by rfl) ⟨1913381, by rfl⟩ : syracuseStep 2551175 = 3826763) B3826763
theorem B3829139 : Blo 1132632 3829139 := bstep (se 1 (by rfl) ⟨2871854, by rfl⟩ : syracuseStep 3829139 = 5743709) B5743709
theorem B1699259 : Blo 1132632 1699259 := bstep (se 1 (by rfl) ⟨1274444, by rfl⟩ : syracuseStep 1699259 = 2548889) B2548889
theorem B1699319 : Blo 1132632 1699319 := bstep (se 1 (by rfl) ⟨1274489, by rfl⟩ : syracuseStep 1699319 = 2548979) B2548979
theorem B1699343 : Blo 1132632 1699343 := bstep (se 1 (by rfl) ⟨1274507, by rfl⟩ : syracuseStep 1699343 = 2549015) B2549015
theorem B1699385 : Blo 1132632 1699385 := bstep (se 2 (by rfl) ⟨637269, by rfl⟩ : syracuseStep 1699385 = 1274539) B1274539
theorem B2551355 : Blo 1132632 2551355 := bstep (se 1 (by rfl) ⟨1913516, by rfl⟩ : syracuseStep 2551355 = 3827033) B3827033
theorem B3108439 : Blo 1132632 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B1699463 : Blo 1132632 1699463 := bstep (se 1 (by rfl) ⟨1274597, by rfl⟩ : syracuseStep 1699463 = 2549195) B2549195
theorem B1699499 : Blo 1132632 1699499 := bstep (se 1 (by rfl) ⟨1274624, by rfl⟩ : syracuseStep 1699499 = 2549249) B2549249
theorem B1437355 : Blo 1132632 1437355 := bstep (se 1 (by rfl) ⟨1078016, by rfl⟩ : syracuseStep 1437355 = 2156033) B2156033
theorem B2551481 : Blo 1132632 2551481 := bstep (se 2 (by rfl) ⟨956805, by rfl⟩ : syracuseStep 2551481 = 1913611) B1913611
theorem B1699529 : Blo 1132632 1699529 := bstep (se 2 (by rfl) ⟨637323, by rfl⟩ : syracuseStep 1699529 = 1274647) B1274647
theorem B4091681 : Blo 1132632 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B7270181 : Blo 1132632 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B1699643 : Blo 1132632 1699643 := bstep (se 1 (by rfl) ⟨1274732, by rfl⟩ : syracuseStep 1699643 = 2549465) B2549465
theorem B1699703 : Blo 1132632 1699703 := bstep (se 1 (by rfl) ⟨1274777, by rfl⟩ : syracuseStep 1699703 = 2549555) B2549555
theorem B2420599 : Blo 1132632 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B1699727 : Blo 1132632 1699727 := bstep (se 1 (by rfl) ⟨1274795, by rfl⟩ : syracuseStep 1699727 = 2549591) B2549591
theorem B1437583 : Blo 1132632 1437583 := bstep (se 1 (by rfl) ⟨1078187, by rfl⟩ : syracuseStep 1437583 = 2156375) B2156375
theorem B1699769 : Blo 1132632 1699769 := bstep (se 2 (by rfl) ⟨637413, by rfl⟩ : syracuseStep 1699769 = 1274827) B1274827
theorem B1699847 : Blo 1132632 1699847 := bstep (se 1 (by rfl) ⟨1274885, by rfl⟩ : syracuseStep 1699847 = 2549771) B2549771
theorem B2551823 : Blo 1132632 2551823 := bstep (se 1 (by rfl) ⟨1913867, by rfl⟩ : syracuseStep 2551823 = 3827735) B3827735
theorem B2551841 : Blo 1132632 2551841 := bstep (se 2 (by rfl) ⟨956940, by rfl⟩ : syracuseStep 2551841 = 1913881) B1913881
theorem B1699883 : Blo 1132632 1699883 := bstep (se 1 (by rfl) ⟨1274912, by rfl⟩ : syracuseStep 1699883 = 2549825) B2549825
theorem B1699913 : Blo 1132632 1699913 := bstep (se 2 (by rfl) ⟨637467, by rfl⟩ : syracuseStep 1699913 = 1274935) B1274935
theorem B2912375 : Blo 1132632 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B8188037 : Blo 1132632 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B1700027 : Blo 1132632 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B1700087 : Blo 1132632 1700087 := bstep (se 1 (by rfl) ⟨1275065, by rfl⟩ : syracuseStep 1700087 = 2550131) B2550131
theorem B1700111 : Blo 1132632 1700111 := bstep (se 1 (by rfl) ⟨1275083, by rfl⟩ : syracuseStep 1700111 = 2550167) B2550167
theorem B1700153 : Blo 1132632 1700153 := bstep (se 2 (by rfl) ⟨637557, by rfl⟩ : syracuseStep 1700153 = 1275115) B1275115
theorem B2552183 : Blo 1132632 2552183 := bstep (se 1 (by rfl) ⟨1914137, by rfl⟩ : syracuseStep 2552183 = 3828275) B3828275
theorem B1700231 : Blo 1132632 1700231 := bstep (se 1 (by rfl) ⟨1275173, by rfl⟩ : syracuseStep 1700231 = 2550347) B2550347
theorem B47149459 : Blo 1132632 47149459 := bstep (se 1 (by rfl) ⟨35362094, by rfl⟩ : syracuseStep 47149459 = 70724189) B70724189
theorem B1700267 : Blo 1132632 1700267 := bstep (se 1 (by rfl) ⟨1275200, by rfl⟩ : syracuseStep 1700267 = 2550401) B2550401
theorem B4321721 : Blo 1132632 4321721 := bstep (se 2 (by rfl) ⟨1620645, by rfl⟩ : syracuseStep 4321721 = 3241291) B3241291
theorem B1700297 : Blo 1132632 1700297 := bstep (se 2 (by rfl) ⟨637611, by rfl⟩ : syracuseStep 1700297 = 1275223) B1275223
theorem B2552363 : Blo 1132632 2552363 := bstep (se 1 (by rfl) ⟨1914272, by rfl⟩ : syracuseStep 2552363 = 3828545) B3828545
theorem B1700411 : Blo 1132632 1700411 := bstep (se 1 (by rfl) ⟨1275308, by rfl⟩ : syracuseStep 1700411 = 2550617) B2550617
theorem B1700471 : Blo 1132632 1700471 := bstep (se 1 (by rfl) ⟨1275353, by rfl⟩ : syracuseStep 1700471 = 2550707) B2550707
theorem B1438327 : Blo 1132632 1438327 := bstep (se 1 (by rfl) ⟨1078745, by rfl⟩ : syracuseStep 1438327 = 2157491) B2157491
theorem B1274503 : Blo 1132632 1274503 := bstep (se 1 (by rfl) ⟨955877, by rfl⟩ : syracuseStep 1274503 = 1911755) B1911755
theorem B1700495 : Blo 1132632 1700495 := bstep (se 1 (by rfl) ⟨1275371, by rfl⟩ : syracuseStep 1700495 = 2550743) B2550743
theorem B1700537 : Blo 1132632 1700537 := bstep (se 2 (by rfl) ⟨637701, by rfl⟩ : syracuseStep 1700537 = 1275403) B1275403
theorem B1700615 : Blo 1132632 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B3830543 : Blo 1132632 3830543 := bstep (se 1 (by rfl) ⟨2872907, by rfl⟩ : syracuseStep 3830543 = 5745815) B5745815
theorem B1700651 : Blo 1132632 1700651 := bstep (se 1 (by rfl) ⟨1275488, by rfl⟩ : syracuseStep 1700651 = 2550977) B2550977
theorem B1274683 : Blo 1132632 1274683 := bstep (se 1 (by rfl) ⟨956012, by rfl⟩ : syracuseStep 1274683 = 1912025) B1912025
theorem B1700681 : Blo 1132632 1700681 := bstep (se 2 (by rfl) ⟨637755, by rfl⟩ : syracuseStep 1700681 = 1275511) B1275511
theorem B5895001 : Blo 1132632 5895001 := bstep (se 2 (by rfl) ⟨2210625, by rfl⟩ : syracuseStep 5895001 = 4421251) B4421251
theorem B2552723 : Blo 1132632 2552723 := bstep (se 1 (by rfl) ⟨1914542, by rfl⟩ : syracuseStep 2552723 = 3829085) B3829085
theorem B1700795 : Blo 1132632 1700795 := bstep (se 1 (by rfl) ⟨1275596, by rfl⟩ : syracuseStep 1700795 = 2551193) B2551193
theorem B2552777 : Blo 1132632 2552777 := bstep (se 2 (by rfl) ⟨957291, by rfl⟩ : syracuseStep 2552777 = 1914583) B1914583
theorem B1700855 : Blo 1132632 1700855 := bstep (se 1 (by rfl) ⟨1275641, by rfl⟩ : syracuseStep 1700855 = 2551283) B2551283
theorem B1700879 : Blo 1132632 1700879 := bstep (se 1 (by rfl) ⟨1275659, by rfl⟩ : syracuseStep 1700879 = 2551319) B2551319
theorem B3830813 : Blo 1132632 3830813 := bstep (se 3 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 3830813 = 1436555) B1436555
theorem B13792301 : Blo 1132632 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B1700921 : Blo 1132632 1700921 := bstep (se 2 (by rfl) ⟨637845, by rfl⟩ : syracuseStep 1700921 = 1275691) B1275691
theorem B1700999 : Blo 1132632 1700999 := bstep (se 1 (by rfl) ⟨1275749, by rfl⟩ : syracuseStep 1700999 = 2551499) B2551499
theorem B1701035 : Blo 1132632 1701035 := bstep (se 1 (by rfl) ⟨1275776, by rfl⟩ : syracuseStep 1701035 = 2551553) B2551553
theorem B1701065 : Blo 1132632 1701065 := bstep (se 2 (by rfl) ⟨637899, by rfl⟩ : syracuseStep 1701065 = 1275799) B1275799
theorem B1275151 : Blo 1132632 1275151 := bstep (se 1 (by rfl) ⟨956363, by rfl⟩ : syracuseStep 1275151 = 1912727) B1912727
theorem B1209659 : Blo 1132632 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B1701179 : Blo 1132632 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B1701239 : Blo 1132632 1701239 := bstep (se 1 (by rfl) ⟨1275929, by rfl⟩ : syracuseStep 1701239 = 2551859) B2551859
theorem B1701263 : Blo 1132632 1701263 := bstep (se 1 (by rfl) ⟨1275947, by rfl⟩ : syracuseStep 1701263 = 2551895) B2551895
theorem B2422163 : Blo 1132632 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1701305 : Blo 1132632 1701305 := bstep (se 2 (by rfl) ⟨637989, by rfl⟩ : syracuseStep 1701305 = 1275979) B1275979
theorem B2618825 : Blo 1132632 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B1701383 : Blo 1132632 1701383 := bstep (se 1 (by rfl) ⟨1276037, by rfl⟩ : syracuseStep 1701383 = 2552075) B2552075
theorem B7763485 : Blo 1132632 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B1701419 : Blo 1132632 1701419 := bstep (se 1 (by rfl) ⟨1276064, by rfl⟩ : syracuseStep 1701419 = 2552129) B2552129
theorem B1701449 : Blo 1132632 1701449 := bstep (se 2 (by rfl) ⟨638043, by rfl⟩ : syracuseStep 1701449 = 1276087) B1276087
theorem B2553479 : Blo 1132632 2553479 := bstep (se 1 (by rfl) ⟨1915109, by rfl⟩ : syracuseStep 2553479 = 3830219) B3830219
theorem B1701563 : Blo 1132632 1701563 := bstep (se 1 (by rfl) ⟨1276172, by rfl⟩ : syracuseStep 1701563 = 2552345) B2552345
theorem B1701623 : Blo 1132632 1701623 := bstep (se 1 (by rfl) ⟨1276217, by rfl⟩ : syracuseStep 1701623 = 2552435) B2552435
theorem B1275655 : Blo 1132632 1275655 := bstep (se 1 (by rfl) ⟨956741, by rfl⟩ : syracuseStep 1275655 = 1913483) B1913483
theorem B6125327 : Blo 1132632 6125327 := bstep (se 1 (by rfl) ⟨4593995, by rfl⟩ : syracuseStep 6125327 = 9187991) B9187991
theorem B1701647 : Blo 1132632 1701647 := bstep (se 1 (by rfl) ⟨1276235, by rfl⟩ : syracuseStep 1701647 = 2552471) B2552471
theorem B1701689 : Blo 1132632 1701689 := bstep (se 2 (by rfl) ⟨638133, by rfl⟩ : syracuseStep 1701689 = 1276267) B1276267
theorem B2553659 : Blo 1132632 2553659 := bstep (se 1 (by rfl) ⟨1915244, by rfl⟩ : syracuseStep 2553659 = 3830489) B3830489
theorem B1701767 : Blo 1132632 1701767 := bstep (se 1 (by rfl) ⟨1276325, by rfl⟩ : syracuseStep 1701767 = 2552651) B2552651
theorem B19658647 : Blo 1132632 19658647 := bstep (se 1 (by rfl) ⟨14743985, by rfl⟩ : syracuseStep 19658647 = 29487971) B29487971
theorem B12941207 : Blo 1132632 12941207 := bstep (se 1 (by rfl) ⟨9705905, by rfl⟩ : syracuseStep 12941207 = 19411811) B19411811
theorem B1701803 : Blo 1132632 1701803 := bstep (se 1 (by rfl) ⟨1276352, by rfl⟩ : syracuseStep 1701803 = 2552705) B2552705
theorem B2553785 : Blo 1132632 2553785 := bstep (se 2 (by rfl) ⟨957669, by rfl⟩ : syracuseStep 2553785 = 1915339) B1915339
theorem B1275835 : Blo 1132632 1275835 := bstep (se 1 (by rfl) ⟨956876, by rfl⟩ : syracuseStep 1275835 = 1913753) B1913753
theorem B1701833 : Blo 1132632 1701833 := bstep (se 2 (by rfl) ⟨638187, by rfl⟩ : syracuseStep 1701833 = 1276375) B1276375
theorem B1701947 : Blo 1132632 1701947 := bstep (se 1 (by rfl) ⟨1276460, by rfl⟩ : syracuseStep 1701947 = 2552921) B2552921
theorem B1702007 : Blo 1132632 1702007 := bstep (se 1 (by rfl) ⟨1276505, by rfl⟩ : syracuseStep 1702007 = 2553011) B2553011
theorem B1702031 : Blo 1132632 1702031 := bstep (se 1 (by rfl) ⟨1276523, by rfl⟩ : syracuseStep 1702031 = 2553047) B2553047
theorem B1702073 : Blo 1132632 1702073 := bstep (se 2 (by rfl) ⟨638277, by rfl⟩ : syracuseStep 1702073 = 1276555) B1276555
theorem B1702151 : Blo 1132632 1702151 := bstep (se 1 (by rfl) ⟨1276613, by rfl⟩ : syracuseStep 1702151 = 2553227) B2553227
theorem B2554127 : Blo 1132632 2554127 := bstep (se 1 (by rfl) ⟨1915595, by rfl⟩ : syracuseStep 2554127 = 3831191) B3831191
theorem B24574225 : Blo 1132632 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B2554145 : Blo 1132632 2554145 := bstep (se 2 (by rfl) ⟨957804, by rfl⟩ : syracuseStep 2554145 = 1915609) B1915609
theorem B1702187 : Blo 1132632 1702187 := bstep (se 1 (by rfl) ⟨1276640, by rfl⟩ : syracuseStep 1702187 = 2553281) B2553281
theorem B1702217 : Blo 1132632 1702217 := bstep (se 2 (by rfl) ⟨638331, by rfl⟩ : syracuseStep 1702217 = 1276663) B1276663
theorem B1276303 : Blo 1132632 1276303 := bstep (se 1 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 1276303 = 1914455) B1914455
theorem B3832217 : Blo 1132632 3832217 := bstep (se 2 (by rfl) ⟨1437081, by rfl⟩ : syracuseStep 3832217 = 2874163) B2874163
theorem B1702331 : Blo 1132632 1702331 := bstep (se 1 (by rfl) ⟨1276748, by rfl⟩ : syracuseStep 1702331 = 2553497) B2553497
theorem B1702391 : Blo 1132632 1702391 := bstep (se 1 (by rfl) ⟨1276793, by rfl⟩ : syracuseStep 1702391 = 2553587) B2553587
theorem B1702415 : Blo 1132632 1702415 := bstep (se 1 (by rfl) ⟨1276811, by rfl⟩ : syracuseStep 1702415 = 2553623) B2553623
theorem B1702457 : Blo 1132632 1702457 := bstep (se 2 (by rfl) ⟨638421, by rfl⟩ : syracuseStep 1702457 = 1276843) B1276843
theorem B11663939 : Blo 1132632 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B2554487 : Blo 1132632 2554487 := bstep (se 1 (by rfl) ⟨1915865, by rfl⟩ : syracuseStep 2554487 = 3831731) B3831731
theorem B1702535 : Blo 1132632 1702535 := bstep (se 1 (by rfl) ⟨1276901, by rfl⟩ : syracuseStep 1702535 = 2553803) B2553803
theorem B1702571 : Blo 1132632 1702571 := bstep (se 1 (by rfl) ⟨1276928, by rfl⟩ : syracuseStep 1702571 = 2553857) B2553857
theorem B1702601 : Blo 1132632 1702601 := bstep (se 2 (by rfl) ⟨638475, by rfl⟩ : syracuseStep 1702601 = 1276951) B1276951
theorem B2554667 : Blo 1132632 2554667 := bstep (se 1 (by rfl) ⟨1916000, by rfl⟩ : syracuseStep 2554667 = 3832001) B3832001
theorem B4848443 : Blo 1132632 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B1702715 : Blo 1132632 1702715 := bstep (se 1 (by rfl) ⟨1277036, by rfl⟩ : syracuseStep 1702715 = 2554073) B2554073
theorem B1702775 : Blo 1132632 1702775 := bstep (se 1 (by rfl) ⟨1277081, by rfl⟩ : syracuseStep 1702775 = 2554163) B2554163
theorem B1276807 : Blo 1132632 1276807 := bstep (se 1 (by rfl) ⟨957605, by rfl⟩ : syracuseStep 1276807 = 1915211) B1915211
theorem B1702799 : Blo 1132632 1702799 := bstep (se 1 (by rfl) ⟨1277099, by rfl⟩ : syracuseStep 1702799 = 2554199) B2554199
theorem B6454201 : Blo 1132632 6454201 := bstep (se 2 (by rfl) ⟨2420325, by rfl⟩ : syracuseStep 6454201 = 4840651) B4840651
theorem B1702841 : Blo 1132632 1702841 := bstep (se 2 (by rfl) ⟨638565, by rfl⟩ : syracuseStep 1702841 = 1277131) B1277131
theorem B9698251 : Blo 1132632 9698251 := bstep (se 1 (by rfl) ⟨7273688, by rfl⟩ : syracuseStep 9698251 = 14547377) B14547377
theorem B1702919 : Blo 1132632 1702919 := bstep (se 1 (by rfl) ⟨1277189, by rfl⟩ : syracuseStep 1702919 = 2554379) B2554379
theorem B5176349 : Blo 1132632 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B1702955 : Blo 1132632 1702955 := bstep (se 1 (by rfl) ⟨1277216, by rfl⟩ : syracuseStep 1702955 = 2554433) B2554433
theorem B1276987 : Blo 1132632 1276987 := bstep (se 1 (by rfl) ⟨957740, by rfl⟩ : syracuseStep 1276987 = 1915481) B1915481
theorem B1702985 : Blo 1132632 1702985 := bstep (se 2 (by rfl) ⟨638619, by rfl⟩ : syracuseStep 1702985 = 1277239) B1277239
theorem B10910807 : Blo 1132632 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B3832919 : Blo 1132632 3832919 := bstep (se 1 (by rfl) ⟨2874689, by rfl⟩ : syracuseStep 3832919 = 5749379) B5749379
theorem B9337943 : Blo 1132632 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B2555027 : Blo 1132632 2555027 := bstep (se 1 (by rfl) ⟨1916270, by rfl⟩ : syracuseStep 2555027 = 3832541) B3832541
theorem B1703099 : Blo 1132632 1703099 := bstep (se 1 (by rfl) ⟨1277324, by rfl⟩ : syracuseStep 1703099 = 2554649) B2554649
theorem B2555081 : Blo 1132632 2555081 := bstep (se 2 (by rfl) ⟨958155, by rfl⟩ : syracuseStep 2555081 = 1916311) B1916311
theorem B1703159 : Blo 1132632 1703159 := bstep (se 1 (by rfl) ⟨1277369, by rfl⟩ : syracuseStep 1703159 = 2554739) B2554739
theorem B1703183 : Blo 1132632 1703183 := bstep (se 1 (by rfl) ⟨1277387, by rfl⟩ : syracuseStep 1703183 = 2554775) B2554775
theorem B98139437 : Blo 1132632 98139437 := bstep (se 3 (by rfl) ⟨18401144, by rfl⟩ : syracuseStep 98139437 = 36802289) B36802289
theorem B1703225 : Blo 1132632 1703225 := bstep (se 2 (by rfl) ⟨638709, by rfl⟩ : syracuseStep 1703225 = 1277419) B1277419
theorem B1703303 : Blo 1132632 1703303 := bstep (se 1 (by rfl) ⟨1277477, by rfl⟩ : syracuseStep 1703303 = 2554955) B2554955
theorem B1703339 : Blo 1132632 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B1703369 : Blo 1132632 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B1277455 : Blo 1132632 1277455 := bstep (se 1 (by rfl) ⟨958091, by rfl⟩ : syracuseStep 1277455 = 1916183) B1916183
theorem B4095517 : Blo 1132632 4095517 := bstep (se 3 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 4095517 = 1535819) B1535819
theorem B1703483 : Blo 1132632 1703483 := bstep (se 1 (by rfl) ⟨1277612, by rfl⟩ : syracuseStep 1703483 = 2555225) B2555225
theorem B3833405 : Blo 1132632 3833405 := bstep (se 3 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 3833405 = 1437527) B1437527
theorem B1703543 : Blo 1132632 1703543 := bstep (se 1 (by rfl) ⟨1277657, by rfl⟩ : syracuseStep 1703543 = 2555315) B2555315
theorem B1703567 : Blo 1132632 1703567 := bstep (se 1 (by rfl) ⟨1277675, by rfl⟩ : syracuseStep 1703567 = 2555351) B2555351
theorem B1703609 : Blo 1132632 1703609 := bstep (se 2 (by rfl) ⟨638853, by rfl⟩ : syracuseStep 1703609 = 1277707) B1277707
theorem B1703687 : Blo 1132632 1703687 := bstep (se 1 (by rfl) ⟨1277765, by rfl⟩ : syracuseStep 1703687 = 2555531) B2555531
theorem B1212175 : Blo 1132632 1212175 := bstep (se 1 (by rfl) ⟨909131, by rfl⟩ : syracuseStep 1212175 = 1818263) B1818263
theorem B1703723 : Blo 1132632 1703723 := bstep (se 1 (by rfl) ⟨1277792, by rfl⟩ : syracuseStep 1703723 = 2555585) B2555585
theorem B1703753 : Blo 1132632 1703753 := bstep (se 2 (by rfl) ⟨638907, by rfl⟩ : syracuseStep 1703753 = 1277815) B1277815
theorem B2916211 : Blo 1132632 2916211 := bstep (se 1 (by rfl) ⟨2187158, by rfl⟩ : syracuseStep 2916211 = 4374317) B4374317
theorem B2555783 : Blo 1132632 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B1703867 : Blo 1132632 1703867 := bstep (se 1 (by rfl) ⟨1277900, by rfl⟩ : syracuseStep 1703867 = 2555801) B2555801
theorem B1703927 : Blo 1132632 1703927 := bstep (se 1 (by rfl) ⟨1277945, by rfl⟩ : syracuseStep 1703927 = 2555891) B2555891
theorem B1703945 : Blo 1132632 1703945 := bstep (se 2 (by rfl) ⟨638979, by rfl⟩ : syracuseStep 1703945 = 1277959) B1277959
theorem B29065229 : Blo 1132632 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B8192015 : Blo 1132632 8192015 := bstep (se 1 (by rfl) ⟨6144011, by rfl⟩ : syracuseStep 8192015 = 12288023) B12288023
theorem B1703975 : Blo 1132632 1703975 := bstep (se 1 (by rfl) ⟨1277981, by rfl⟩ : syracuseStep 1703975 = 2555963) B2555963
theorem B6225977 : Blo 1132632 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B1278031 : Blo 1132632 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B1704059 : Blo 1132632 1704059 := bstep (se 1 (by rfl) ⟨1278044, by rfl⟩ : syracuseStep 1704059 = 2556089) B2556089
theorem B1704185 : Blo 1132632 1704185 := bstep (se 2 (by rfl) ⟨639069, by rfl⟩ : syracuseStep 1704185 = 1278139) B1278139
theorem B1704287 : Blo 1132632 1704287 := bstep (se 1 (by rfl) ⟨1278215, by rfl⟩ : syracuseStep 1704287 = 2556431) B2556431
theorem B1704299 : Blo 1132632 1704299 := bstep (se 1 (by rfl) ⟨1278224, by rfl⟩ : syracuseStep 1704299 = 2556449) B2556449
theorem B3277181 : Blo 1132632 3277181 := bstep (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) B1228943
theorem B1278427 : Blo 1132632 1278427 := bstep (se 1 (by rfl) ⟨958820, by rfl⟩ : syracuseStep 1278427 = 1917641) B1917641
theorem B3834377 : Blo 1132632 3834377 := bstep (se 2 (by rfl) ⟨1437891, by rfl⟩ : syracuseStep 3834377 = 2875783) B2875783
theorem B1704527 : Blo 1132632 1704527 := bstep (se 1 (by rfl) ⟨1278395, by rfl⟩ : syracuseStep 1704527 = 2556791) B2556791
theorem B2556539 : Blo 1132632 2556539 := bstep (se 1 (by rfl) ⟨1917404, by rfl⟩ : syracuseStep 2556539 = 3834809) B3834809
theorem B1704647 : Blo 1132632 1704647 := bstep (se 1 (by rfl) ⟨1278485, by rfl⟩ : syracuseStep 1704647 = 2556971) B2556971
theorem B5735123 : Blo 1132632 5735123 := bstep (se 1 (by rfl) ⟨4301342, by rfl⟩ : syracuseStep 5735123 = 8602685) B8602685
theorem B2556665 : Blo 1132632 2556665 := bstep (se 2 (by rfl) ⟨958749, by rfl⟩ : syracuseStep 2556665 = 1917499) B1917499
theorem B1704809 : Blo 1132632 1704809 := bstep (se 2 (by rfl) ⟨639303, by rfl⟩ : syracuseStep 1704809 = 1278607) B1278607
theorem B1704887 : Blo 1132632 1704887 := bstep (se 1 (by rfl) ⟨1278665, by rfl⟩ : syracuseStep 1704887 = 2557331) B2557331
theorem B1704923 : Blo 1132632 1704923 := bstep (se 1 (by rfl) ⟨1278692, by rfl⟩ : syracuseStep 1704923 = 2557385) B2557385
theorem B2556935 : Blo 1132632 2556935 := bstep (se 1 (by rfl) ⟨1917701, by rfl⟩ : syracuseStep 2556935 = 3835403) B3835403
theorem B2557007 : Blo 1132632 2557007 := bstep (se 1 (by rfl) ⟨1917755, by rfl⟩ : syracuseStep 2557007 = 3835511) B3835511
theorem B3835241 : Blo 1132632 3835241 := bstep (se 2 (by rfl) ⟨1438215, by rfl⟩ : syracuseStep 3835241 = 2876431) B2876431
theorem B2557403 : Blo 1132632 2557403 := bstep (se 1 (by rfl) ⟨1918052, by rfl⟩ : syracuseStep 2557403 = 3836105) B3836105
theorem B5178977 : Blo 1132632 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B7276331 : Blo 1132632 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B7276355 : Blo 1132632 7276355 := bstep (se 1 (by rfl) ⟨5457266, by rfl⟩ : syracuseStep 7276355 = 10914533) B10914533
theorem B3835835 : Blo 1132632 3835835 := bstep (se 1 (by rfl) ⟨2876876, by rfl⟩ : syracuseStep 3835835 = 5753753) B5753753
theorem B251463781 : Blo 1132632 251463781 := bstep (se 4 (by rfl) ⟨23574729, by rfl⟩ : syracuseStep 251463781 = 47149459) B47149459
theorem B3639563 : Blo 1132632 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B3639613 : Blo 1132632 3639613 := bstep (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) B1364855
theorem B22088393 : Blo 1132632 22088393 := bstep (se 2 (by rfl) ⟨8283147, by rfl⟩ : syracuseStep 22088393 = 16566295) B16566295
theorem B5737391 : Blo 1132632 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B2723291 : Blo 1132632 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B9702899 : Blo 1132632 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B12258955 : Blo 1132632 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B6459101 : Blo 1132632 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B6983533 : Blo 1132632 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B11800691 : Blo 1132632 11800691 := bstep (se 1 (by rfl) ⟨8850518, by rfl⟩ : syracuseStep 11800691 = 17701037) B17701037
theorem B36835505 : Blo 1132632 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B22385161 : Blo 1132632 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B9703961 : Blo 1132632 9703961 := bstep (se 2 (by rfl) ⟨3638985, by rfl⟩ : syracuseStep 9703961 = 7277971) B7277971
theorem B6132509 : Blo 1132632 6132509 := bstep (se 3 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 6132509 = 2299691) B2299691
theorem B2724943 : Blo 1132632 2724943 := bstep (se 1 (by rfl) ⟨2043707, by rfl⟩ : syracuseStep 2724943 = 4087415) B4087415
theorem B17700041 : Blo 1132632 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B8295695 : Blo 1132632 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B9214067 : Blo 1132632 9214067 := bstep (se 1 (by rfl) ⟨6910550, by rfl⟩ : syracuseStep 9214067 = 13821101) B13821101
theorem B19634537 : Blo 1132632 19634537 := bstep (se 2 (by rfl) ⟨7362951, by rfl⟩ : syracuseStep 19634537 = 14725903) B14725903
theorem B2300663 : Blo 1132632 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B8625041 : Blo 1132632 8625041 := bstep (se 2 (by rfl) ⟨3234390, by rfl⟩ : syracuseStep 8625041 = 6468781) B6468781
theorem B1941583 : Blo 1132632 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B5448023 : Blo 1132632 5448023 := bstep (se 1 (by rfl) ⟨4086017, by rfl⟩ : syracuseStep 5448023 = 8172035) B8172035
theorem B6136985 : Blo 1132632 6136985 := bstep (se 2 (by rfl) ⟨2301369, by rfl⟩ : syracuseStep 6136985 = 4602739) B4602739
theorem B4301981 : Blo 1132632 4301981 := bstep (se 3 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 4301981 = 1613243) B1613243
theorem B10364075 : Blo 1132632 10364075 := bstep (se 1 (by rfl) ⟨7773056, by rfl⟩ : syracuseStep 10364075 = 15546113) B15546113
theorem B33137869 : Blo 1132632 33137869 := bstep (se 3 (by rfl) ⟨6213350, by rfl⟩ : syracuseStep 33137869 = 12426701) B12426701
theorem B4596983 : Blo 1132632 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B8627471 : Blo 1132632 8627471 := bstep (se 1 (by rfl) ⟨6470603, by rfl⟩ : syracuseStep 8627471 = 12941207) B12941207
theorem B6464933 : Blo 1132632 6464933 := bstep (se 4 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 6464933 = 1212175) B1212175
theorem B7775959 : Blo 1132632 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B4302665 : Blo 1132632 4302665 := bstep (se 2 (by rfl) ⟨1613499, by rfl⟩ : syracuseStep 4302665 = 3226999) B3226999
theorem B9840545 : Blo 1132632 9840545 := bstep (se 2 (by rfl) ⟨3690204, by rfl⟩ : syracuseStep 9840545 = 7380409) B7380409
theorem B3450899 : Blo 1132632 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B4303165 : Blo 1132632 4303165 := bstep (se 3 (by rfl) ⟨806843, by rfl⟩ : syracuseStep 4303165 = 1613687) B1613687
theorem B4598407 : Blo 1132632 4598407 := bstep (se 1 (by rfl) ⟨3448805, by rfl⟩ : syracuseStep 4598407 = 6897611) B6897611
theorem B1911647 : Blo 1132632 1911647 := bstep (se 1 (by rfl) ⟨1433735, by rfl⟩ : syracuseStep 1911647 = 2867471) B2867471
theorem B1912207 : Blo 1132632 1912207 := bstep (se 1 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 1912207 = 2868311) B2868311
theorem B2043319 : Blo 1132632 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B5746139 : Blo 1132632 5746139 := bstep (se 1 (by rfl) ⟨4309604, by rfl⟩ : syracuseStep 5746139 = 8619209) B8619209
theorem B16330511 : Blo 1132632 16330511 := bstep (se 1 (by rfl) ⟨12247883, by rfl⟩ : syracuseStep 16330511 = 24495767) B24495767
theorem B4599671 : Blo 1132632 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B5746625 : Blo 1132632 5746625 := bstep (se 2 (by rfl) ⟨2154984, by rfl⟩ : syracuseStep 5746625 = 4309969) B4309969
theorem B4304897 : Blo 1132632 4304897 := bstep (se 2 (by rfl) ⟨1614336, by rfl⟩ : syracuseStep 4304897 = 3228673) B3228673
theorem B9187343 : Blo 1132632 9187343 := bstep (se 1 (by rfl) ⟨6890507, by rfl⟩ : syracuseStep 9187343 = 13781015) B13781015
theorem B1912889 : Blo 1132632 1912889 := bstep (se 2 (by rfl) ⟨717333, by rfl⟩ : syracuseStep 1912889 = 1434667) B1434667
theorem B8630387 : Blo 1132632 8630387 := bstep (se 1 (by rfl) ⟨6472790, by rfl⟩ : syracuseStep 8630387 = 12945581) B12945581
theorem B9679115 : Blo 1132632 9679115 := bstep (se 1 (by rfl) ⟨7259336, by rfl⟩ : syracuseStep 9679115 = 14518673) B14518673
theorem B3453479 : Blo 1132632 3453479 := bstep (se 1 (by rfl) ⟨2590109, by rfl⟩ : syracuseStep 3453479 = 5180219) B5180219
theorem B6468281 : Blo 1132632 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B1913591 : Blo 1132632 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B3683233 : Blo 1132632 3683233 := bstep (se 2 (by rfl) ⟨1381212, by rfl⟩ : syracuseStep 3683233 = 2762425) B2762425
theorem B1455067 : Blo 1132632 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B10892353 : Blo 1132632 10892353 := bstep (se 2 (by rfl) ⟨4084632, by rfl⟩ : syracuseStep 10892353 = 8169265) B8169265
theorem B1913935 : Blo 1132632 1913935 := bstep (se 1 (by rfl) ⟨1435451, by rfl⟩ : syracuseStep 1913935 = 2870903) B2870903
theorem B3454109 : Blo 1132632 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B1914185 : Blo 1132632 1914185 := bstep (se 2 (by rfl) ⟨717819, by rfl⟩ : syracuseStep 1914185 = 1435639) B1435639
theorem B4601441 : Blo 1132632 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B4306567 : Blo 1132632 4306567 := bstep (se 1 (by rfl) ⟨3229925, by rfl⟩ : syracuseStep 4306567 = 6459851) B6459851
theorem B1914617 : Blo 1132632 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B1914799 : Blo 1132632 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B4306871 : Blo 1132632 4306871 := bstep (se 1 (by rfl) ⟨3230153, by rfl⟩ : syracuseStep 4306871 = 6460307) B6460307
theorem B1914887 : Blo 1132632 1914887 := bstep (se 1 (by rfl) ⟨1436165, by rfl⟩ : syracuseStep 1914887 = 2872331) B2872331
theorem B3455033 : Blo 1132632 3455033 := bstep (se 2 (by rfl) ⟨1295637, by rfl⟩ : syracuseStep 3455033 = 2591275) B2591275
theorem B3225757 : Blo 1132632 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B5748893 : Blo 1132632 5748893 := bstep (se 3 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 5748893 = 2155835) B2155835
theorem B1915231 : Blo 1132632 1915231 := bstep (se 1 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 1915231 = 2872847) B2872847
theorem B1915319 : Blo 1132632 1915319 := bstep (se 1 (by rfl) ⟨1436489, by rfl⟩ : syracuseStep 1915319 = 2872979) B2872979
theorem B1817167 : Blo 1132632 1817167 := bstep (se 1 (by rfl) ⟨1362875, by rfl⟩ : syracuseStep 1817167 = 2725751) B2725751
theorem B4373207 : Blo 1132632 4373207 := bstep (se 1 (by rfl) ⟨3279905, by rfl⟩ : syracuseStep 4373207 = 6559811) B6559811
theorem B3226463 : Blo 1132632 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B52312949 : Blo 1132632 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B8174483 : Blo 1132632 8174483 := bstep (se 1 (by rfl) ⟨6130862, by rfl⟩ : syracuseStep 8174483 = 12261725) B12261725
theorem B1915913 : Blo 1132632 1915913 := bstep (se 2 (by rfl) ⟨718467, by rfl⟩ : syracuseStep 1915913 = 1436935) B1436935
theorem B4308025 : Blo 1132632 4308025 := bstep (se 2 (by rfl) ⟨1615509, by rfl⟩ : syracuseStep 4308025 = 3231019) B3231019
theorem B31440005 : Blo 1132632 31440005 := bstep (se 4 (by rfl) ⟨2947500, by rfl⟩ : syracuseStep 31440005 = 5895001) B5895001
theorem B1916075 : Blo 1132632 1916075 := bstep (se 1 (by rfl) ⟨1437056, by rfl⟩ : syracuseStep 1916075 = 2874113) B2874113
theorem B6143147 : Blo 1132632 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B18398501 : Blo 1132632 18398501 := bstep (se 4 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 18398501 = 3449719) B3449719
theorem B4308329 : Blo 1132632 4308329 := bstep (se 2 (by rfl) ⟨1615623, by rfl⟩ : syracuseStep 4308329 = 3231247) B3231247
theorem B13811087 : Blo 1132632 13811087 := bstep (se 1 (by rfl) ⟨10358315, by rfl⟩ : syracuseStep 13811087 = 20716631) B20716631
theorem B5750189 : Blo 1132632 5750189 := bstep (se 3 (by rfl) ⟨1078160, by rfl⟩ : syracuseStep 5750189 = 2156321) B2156321
theorem B7257545 : Blo 1132632 7257545 := bstep (se 2 (by rfl) ⟨2721579, by rfl⟩ : syracuseStep 7257545 = 5443159) B5443159
theorem B1916473 : Blo 1132632 1916473 := bstep (se 2 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 1916473 = 1437355) B1437355
theorem B8601227 : Blo 1132632 8601227 := bstep (se 1 (by rfl) ⟨6450920, by rfl⟩ : syracuseStep 8601227 = 12901841) B12901841
theorem B1916615 : Blo 1132632 1916615 := bstep (se 1 (by rfl) ⟨1437461, by rfl⟩ : syracuseStep 1916615 = 2874923) B2874923
theorem B7356203 : Blo 1132632 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B15515459 : Blo 1132632 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B3227465 : Blo 1132632 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B1916777 : Blo 1132632 1916777 := bstep (se 2 (by rfl) ⟨718791, by rfl⟩ : syracuseStep 1916777 = 1437583) B1437583
theorem B1818551 : Blo 1132632 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B16367645 : Blo 1132632 16367645 := bstep (se 3 (by rfl) ⟨3068933, by rfl⟩ : syracuseStep 16367645 = 6137867) B6137867
theorem B1917175 : Blo 1132632 1917175 := bstep (se 1 (by rfl) ⟨1437881, by rfl⟩ : syracuseStep 1917175 = 2875763) B2875763
theorem B1917371 : Blo 1132632 1917371 := bstep (se 1 (by rfl) ⟨1438028, by rfl⟩ : syracuseStep 1917371 = 2876057) B2876057
theorem B7258571 : Blo 1132632 7258571 := bstep (se 1 (by rfl) ⟨5443928, by rfl⟩ : syracuseStep 7258571 = 10887857) B10887857
theorem B1917479 : Blo 1132632 1917479 := bstep (se 1 (by rfl) ⟨1438109, by rfl⟩ : syracuseStep 1917479 = 2876219) B2876219
theorem B1819307 : Blo 1132632 1819307 := bstep (se 1 (by rfl) ⟨1364480, by rfl⟩ : syracuseStep 1819307 = 2728961) B2728961
theorem B1917769 : Blo 1132632 1917769 := bstep (se 2 (by rfl) ⟨719163, by rfl⟩ : syracuseStep 1917769 = 1438327) B1438327
theorem B9192269 : Blo 1132632 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B1917803 : Blo 1132632 1917803 := bstep (se 1 (by rfl) ⟨1438352, by rfl⟩ : syracuseStep 1917803 = 2876705) B2876705
theorem B5751809 : Blo 1132632 5751809 := bstep (se 2 (by rfl) ⟨2156928, by rfl⟩ : syracuseStep 5751809 = 4313857) B4313857
theorem B2868281 : Blo 1132632 2868281 := bstep (se 2 (by rfl) ⟨1075605, by rfl⟩ : syracuseStep 2868281 = 2151211) B2151211
theorem B17450711 : Blo 1132632 17450711 := bstep (se 1 (by rfl) ⟨13088033, by rfl⟩ : syracuseStep 17450711 = 26176067) B26176067
theorem B5752619 : Blo 1132632 5752619 := bstep (se 1 (by rfl) ⟨4314464, by rfl⟩ : syracuseStep 5752619 = 8628929) B8628929
theorem B1132639 : Blo 1132632 1132639 := bstep (se 1 (by rfl) ⟨849479, by rfl⟩ : syracuseStep 1132639 = 1698959) B1698959
theorem B1132667 : Blo 1132632 1132667 := bstep (se 1 (by rfl) ⟨849500, by rfl⟩ : syracuseStep 1132667 = 1699001) B1699001
theorem B1132719 : Blo 1132632 1132719 := bstep (se 1 (by rfl) ⟨849539, by rfl⟩ : syracuseStep 1132719 = 1699079) B1699079
theorem B1132743 : Blo 1132632 1132743 := bstep (se 1 (by rfl) ⟨849557, by rfl⟩ : syracuseStep 1132743 = 1699115) B1699115
theorem B1132763 : Blo 1132632 1132763 := bstep (se 1 (by rfl) ⟨849572, by rfl⟩ : syracuseStep 1132763 = 1699145) B1699145
theorem B1132839 : Blo 1132632 1132839 := bstep (se 1 (by rfl) ⟨849629, by rfl⟩ : syracuseStep 1132839 = 1699259) B1699259
theorem B1132879 : Blo 1132632 1132879 := bstep (se 1 (by rfl) ⟨849659, by rfl⟩ : syracuseStep 1132879 = 1699319) B1699319
theorem B9816407 : Blo 1132632 9816407 := bstep (se 1 (by rfl) ⟨7362305, by rfl⟩ : syracuseStep 9816407 = 14724611) B14724611
theorem B1132895 : Blo 1132632 1132895 := bstep (se 1 (by rfl) ⟨849671, by rfl⟩ : syracuseStep 1132895 = 1699343) B1699343
theorem B1132923 : Blo 1132632 1132923 := bstep (se 1 (by rfl) ⟨849692, by rfl⟩ : syracuseStep 1132923 = 1699385) B1699385
theorem B15518087 : Blo 1132632 15518087 := bstep (se 1 (by rfl) ⟨11638565, by rfl⟩ : syracuseStep 15518087 = 23277131) B23277131
theorem B1132975 : Blo 1132632 1132975 := bstep (se 1 (by rfl) ⟨849731, by rfl⟩ : syracuseStep 1132975 = 1699463) B1699463
theorem B1132999 : Blo 1132632 1132999 := bstep (se 1 (by rfl) ⟨849749, by rfl⟩ : syracuseStep 1132999 = 1699499) B1699499
theorem B1133019 : Blo 1132632 1133019 := bstep (se 1 (by rfl) ⟨849764, by rfl⟩ : syracuseStep 1133019 = 1699529) B1699529
theorem B2869769 : Blo 1132632 2869769 := bstep (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) B2152327
theorem B1133095 : Blo 1132632 1133095 := bstep (se 1 (by rfl) ⟨849821, by rfl⟩ : syracuseStep 1133095 = 1699643) B1699643
theorem B1133135 : Blo 1132632 1133135 := bstep (se 1 (by rfl) ⟨849851, by rfl⟩ : syracuseStep 1133135 = 1699703) B1699703
theorem B1133151 : Blo 1132632 1133151 := bstep (se 1 (by rfl) ⟨849863, by rfl⟩ : syracuseStep 1133151 = 1699727) B1699727
theorem B1133179 : Blo 1132632 1133179 := bstep (se 1 (by rfl) ⟨849884, by rfl⟩ : syracuseStep 1133179 = 1699769) B1699769
theorem B1133231 : Blo 1132632 1133231 := bstep (se 1 (by rfl) ⟨849923, by rfl⟩ : syracuseStep 1133231 = 1699847) B1699847
theorem B1133255 : Blo 1132632 1133255 := bstep (se 1 (by rfl) ⟨849941, by rfl⟩ : syracuseStep 1133255 = 1699883) B1699883
theorem B1133275 : Blo 1132632 1133275 := bstep (se 1 (by rfl) ⟨849956, by rfl⟩ : syracuseStep 1133275 = 1699913) B1699913
theorem B5458691 : Blo 1132632 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B1133351 : Blo 1132632 1133351 := bstep (se 1 (by rfl) ⟨850013, by rfl⟩ : syracuseStep 1133351 = 1700027) B1700027
theorem B1133391 : Blo 1132632 1133391 := bstep (se 1 (by rfl) ⟨850043, by rfl⟩ : syracuseStep 1133391 = 1700087) B1700087
theorem B1133407 : Blo 1132632 1133407 := bstep (se 1 (by rfl) ⟨850055, by rfl⟩ : syracuseStep 1133407 = 1700111) B1700111
theorem B1133435 : Blo 1132632 1133435 := bstep (se 1 (by rfl) ⟨850076, by rfl⟩ : syracuseStep 1133435 = 1700153) B1700153
theorem B1133487 : Blo 1132632 1133487 := bstep (se 1 (by rfl) ⟨850115, by rfl⟩ : syracuseStep 1133487 = 1700231) B1700231
theorem B1133511 : Blo 1132632 1133511 := bstep (se 1 (by rfl) ⟨850133, by rfl⟩ : syracuseStep 1133511 = 1700267) B1700267
theorem B1133531 : Blo 1132632 1133531 := bstep (se 1 (by rfl) ⟨850148, by rfl⟩ : syracuseStep 1133531 = 1700297) B1700297
theorem B1133607 : Blo 1132632 1133607 := bstep (se 1 (by rfl) ⟨850205, by rfl⟩ : syracuseStep 1133607 = 1700411) B1700411
theorem B7261235 : Blo 1132632 7261235 := bstep (se 1 (by rfl) ⟨5445926, by rfl⟩ : syracuseStep 7261235 = 10891853) B10891853
theorem B1133647 : Blo 1132632 1133647 := bstep (se 1 (by rfl) ⟨850235, by rfl⟩ : syracuseStep 1133647 = 1700471) B1700471
theorem B37342295 : Blo 1132632 37342295 := bstep (se 1 (by rfl) ⟨28006721, by rfl⟩ : syracuseStep 37342295 = 56013443) B56013443
theorem B1133663 : Blo 1132632 1133663 := bstep (se 1 (by rfl) ⟨850247, by rfl⟩ : syracuseStep 1133663 = 1700495) B1700495
theorem B1133691 : Blo 1132632 1133691 := bstep (se 1 (by rfl) ⟨850268, by rfl⟩ : syracuseStep 1133691 = 1700537) B1700537
theorem B4312217 : Blo 1132632 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B1133743 : Blo 1132632 1133743 := bstep (se 1 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 1133743 = 1700615) B1700615
theorem B1133767 : Blo 1132632 1133767 := bstep (se 1 (by rfl) ⟨850325, by rfl⟩ : syracuseStep 1133767 = 1700651) B1700651
theorem B1133787 : Blo 1132632 1133787 := bstep (se 1 (by rfl) ⟨850340, by rfl⟩ : syracuseStep 1133787 = 1700681) B1700681
theorem B1133863 : Blo 1132632 1133863 := bstep (se 1 (by rfl) ⟨850397, by rfl⟩ : syracuseStep 1133863 = 1700795) B1700795
theorem B1133903 : Blo 1132632 1133903 := bstep (se 1 (by rfl) ⟨850427, by rfl⟩ : syracuseStep 1133903 = 1700855) B1700855
theorem B1133919 : Blo 1132632 1133919 := bstep (se 1 (by rfl) ⟨850439, by rfl⟩ : syracuseStep 1133919 = 1700879) B1700879
theorem B9194867 : Blo 1132632 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B1133947 : Blo 1132632 1133947 := bstep (se 1 (by rfl) ⟨850460, by rfl⟩ : syracuseStep 1133947 = 1700921) B1700921
theorem B1133999 : Blo 1132632 1133999 := bstep (se 1 (by rfl) ⟨850499, by rfl⟩ : syracuseStep 1133999 = 1700999) B1700999
theorem B1134023 : Blo 1132632 1134023 := bstep (se 1 (by rfl) ⟨850517, by rfl⟩ : syracuseStep 1134023 = 1701035) B1701035
theorem B1134043 : Blo 1132632 1134043 := bstep (se 1 (by rfl) ⟨850532, by rfl⟩ : syracuseStep 1134043 = 1701065) B1701065
theorem B3067379 : Blo 1132632 3067379 := bstep (se 1 (by rfl) ⟨2300534, by rfl⟩ : syracuseStep 3067379 = 4601069) B4601069
theorem B1134119 : Blo 1132632 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B14536259 : Blo 1132632 14536259 := bstep (se 1 (by rfl) ⟨10902194, by rfl⟩ : syracuseStep 14536259 = 21804389) B21804389
theorem B1134159 : Blo 1132632 1134159 := bstep (se 1 (by rfl) ⟨850619, by rfl⟩ : syracuseStep 1134159 = 1701239) B1701239
theorem B1134175 : Blo 1132632 1134175 := bstep (se 1 (by rfl) ⟨850631, by rfl⟩ : syracuseStep 1134175 = 1701263) B1701263
theorem B4312673 : Blo 1132632 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B1134203 : Blo 1132632 1134203 := bstep (se 1 (by rfl) ⟨850652, by rfl⟩ : syracuseStep 1134203 = 1701305) B1701305
theorem B2870923 : Blo 1132632 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B1134255 : Blo 1132632 1134255 := bstep (se 1 (by rfl) ⟨850691, by rfl⟩ : syracuseStep 1134255 = 1701383) B1701383
theorem B1134279 : Blo 1132632 1134279 := bstep (se 1 (by rfl) ⟨850709, by rfl⟩ : syracuseStep 1134279 = 1701419) B1701419
theorem B1134299 : Blo 1132632 1134299 := bstep (se 1 (by rfl) ⟨850724, by rfl⟩ : syracuseStep 1134299 = 1701449) B1701449
theorem B1134375 : Blo 1132632 1134375 := bstep (se 1 (by rfl) ⟨850781, by rfl⟩ : syracuseStep 1134375 = 1701563) B1701563
theorem B1134415 : Blo 1132632 1134415 := bstep (se 1 (by rfl) ⟨850811, by rfl⟩ : syracuseStep 1134415 = 1701623) B1701623
theorem B2150239 : Blo 1132632 2150239 := bstep (se 1 (by rfl) ⟨1612679, by rfl⟩ : syracuseStep 2150239 = 3225359) B3225359
theorem B4083551 : Blo 1132632 4083551 := bstep (se 1 (by rfl) ⟨3062663, by rfl⟩ : syracuseStep 4083551 = 6125327) B6125327
theorem B1134431 : Blo 1132632 1134431 := bstep (se 1 (by rfl) ⟨850823, by rfl⟩ : syracuseStep 1134431 = 1701647) B1701647
theorem B1134459 : Blo 1132632 1134459 := bstep (se 1 (by rfl) ⟨850844, by rfl⟩ : syracuseStep 1134459 = 1701689) B1701689
theorem B8605601 : Blo 1132632 8605601 := bstep (se 2 (by rfl) ⟨3227100, by rfl⟩ : syracuseStep 8605601 = 6454201) B6454201
theorem B1134511 : Blo 1132632 1134511 := bstep (se 1 (by rfl) ⟨850883, by rfl⟩ : syracuseStep 1134511 = 1701767) B1701767
theorem B12931001 : Blo 1132632 12931001 := bstep (se 2 (by rfl) ⟨4849125, by rfl⟩ : syracuseStep 12931001 = 9698251) B9698251
theorem B2871227 : Blo 1132632 2871227 := bstep (se 1 (by rfl) ⟨2153420, by rfl⟩ : syracuseStep 2871227 = 4306841) B4306841
theorem B1134535 : Blo 1132632 1134535 := bstep (se 1 (by rfl) ⟨850901, by rfl⟩ : syracuseStep 1134535 = 1701803) B1701803
theorem B1134555 : Blo 1132632 1134555 := bstep (se 1 (by rfl) ⟨850916, by rfl⟩ : syracuseStep 1134555 = 1701833) B1701833
theorem B1134631 : Blo 1132632 1134631 := bstep (se 1 (by rfl) ⟨850973, by rfl⟩ : syracuseStep 1134631 = 1701947) B1701947
theorem B1134671 : Blo 1132632 1134671 := bstep (se 1 (by rfl) ⟨851003, by rfl⟩ : syracuseStep 1134671 = 1702007) B1702007
theorem B1134687 : Blo 1132632 1134687 := bstep (se 1 (by rfl) ⟨851015, by rfl⟩ : syracuseStep 1134687 = 1702031) B1702031
theorem B1134715 : Blo 1132632 1134715 := bstep (se 1 (by rfl) ⟨851036, by rfl⟩ : syracuseStep 1134715 = 1702073) B1702073
theorem B1134767 : Blo 1132632 1134767 := bstep (se 1 (by rfl) ⟨851075, by rfl⟩ : syracuseStep 1134767 = 1702151) B1702151
theorem B1134791 : Blo 1132632 1134791 := bstep (se 1 (by rfl) ⟨851093, by rfl⟩ : syracuseStep 1134791 = 1702187) B1702187
theorem B1134811 : Blo 1132632 1134811 := bstep (se 1 (by rfl) ⟨851108, by rfl⟩ : syracuseStep 1134811 = 1702217) B1702217
theorem B1134887 : Blo 1132632 1134887 := bstep (se 1 (by rfl) ⟨851165, by rfl⟩ : syracuseStep 1134887 = 1702331) B1702331
theorem B1134927 : Blo 1132632 1134927 := bstep (se 1 (by rfl) ⟨851195, by rfl⟩ : syracuseStep 1134927 = 1702391) B1702391
theorem B1134943 : Blo 1132632 1134943 := bstep (se 1 (by rfl) ⟨851207, by rfl⟩ : syracuseStep 1134943 = 1702415) B1702415
theorem B1134971 : Blo 1132632 1134971 := bstep (se 1 (by rfl) ⟨851228, by rfl⟩ : syracuseStep 1134971 = 1702457) B1702457
theorem B7262617 : Blo 1132632 7262617 := bstep (se 2 (by rfl) ⟨2723481, by rfl⟩ : syracuseStep 7262617 = 5446963) B5446963
theorem B1135023 : Blo 1132632 1135023 := bstep (se 1 (by rfl) ⟨851267, by rfl⟩ : syracuseStep 1135023 = 1702535) B1702535
theorem B1135047 : Blo 1132632 1135047 := bstep (se 1 (by rfl) ⟨851285, by rfl⟩ : syracuseStep 1135047 = 1702571) B1702571
theorem B1135067 : Blo 1132632 1135067 := bstep (se 1 (by rfl) ⟨851300, by rfl⟩ : syracuseStep 1135067 = 1702601) B1702601
theorem B3232295 : Blo 1132632 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B1135143 : Blo 1132632 1135143 := bstep (se 1 (by rfl) ⟨851357, by rfl⟩ : syracuseStep 1135143 = 1702715) B1702715
theorem B1135183 : Blo 1132632 1135183 := bstep (se 1 (by rfl) ⟨851387, by rfl⟩ : syracuseStep 1135183 = 1702775) B1702775
theorem B1135199 : Blo 1132632 1135199 := bstep (se 1 (by rfl) ⟨851399, by rfl⟩ : syracuseStep 1135199 = 1702799) B1702799
theorem B1135227 : Blo 1132632 1135227 := bstep (se 1 (by rfl) ⟨851420, by rfl⟩ : syracuseStep 1135227 = 1702841) B1702841
theorem B1135279 : Blo 1132632 1135279 := bstep (se 1 (by rfl) ⟨851459, by rfl⟩ : syracuseStep 1135279 = 1702919) B1702919
theorem B2872007 : Blo 1132632 2872007 := bstep (se 1 (by rfl) ⟨2154005, by rfl⟩ : syracuseStep 2872007 = 4308011) B4308011
theorem B1135303 : Blo 1132632 1135303 := bstep (se 1 (by rfl) ⟨851477, by rfl⟩ : syracuseStep 1135303 = 1702955) B1702955
theorem B5460689 : Blo 1132632 5460689 := bstep (se 2 (by rfl) ⟨2047758, by rfl⟩ : syracuseStep 5460689 = 4095517) B4095517
theorem B1135323 : Blo 1132632 1135323 := bstep (se 1 (by rfl) ⟨851492, by rfl⟩ : syracuseStep 1135323 = 1702985) B1702985
theorem B2872057 : Blo 1132632 2872057 := bstep (se 2 (by rfl) ⟨1077021, by rfl⟩ : syracuseStep 2872057 = 2154043) B2154043
theorem B1135399 : Blo 1132632 1135399 := bstep (se 1 (by rfl) ⟨851549, by rfl⟩ : syracuseStep 1135399 = 1703099) B1703099
theorem B1135439 : Blo 1132632 1135439 := bstep (se 1 (by rfl) ⟨851579, by rfl⟩ : syracuseStep 1135439 = 1703159) B1703159
theorem B1135455 : Blo 1132632 1135455 := bstep (se 1 (by rfl) ⟨851591, by rfl⟩ : syracuseStep 1135455 = 1703183) B1703183
theorem B65426291 : Blo 1132632 65426291 := bstep (se 1 (by rfl) ⟨49069718, by rfl⟩ : syracuseStep 65426291 = 98139437) B98139437
theorem B1135483 : Blo 1132632 1135483 := bstep (se 1 (by rfl) ⟨851612, by rfl⟩ : syracuseStep 1135483 = 1703225) B1703225
theorem B1135535 : Blo 1132632 1135535 := bstep (se 1 (by rfl) ⟨851651, by rfl⟩ : syracuseStep 1135535 = 1703303) B1703303
theorem B2151355 : Blo 1132632 2151355 := bstep (se 1 (by rfl) ⟨1613516, by rfl⟩ : syracuseStep 2151355 = 3227033) B3227033
theorem B1135559 : Blo 1132632 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B1135579 : Blo 1132632 1135579 := bstep (se 1 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 1135579 = 1703369) B1703369
theorem B7263233 : Blo 1132632 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B2151431 : Blo 1132632 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B4314131 : Blo 1132632 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B1135655 : Blo 1132632 1135655 := bstep (se 1 (by rfl) ⟨851741, by rfl⟩ : syracuseStep 1135655 = 1703483) B1703483
theorem B4084793 : Blo 1132632 4084793 := bstep (se 2 (by rfl) ⟨1531797, by rfl⟩ : syracuseStep 4084793 = 3063595) B3063595
theorem B1135695 : Blo 1132632 1135695 := bstep (se 1 (by rfl) ⟨851771, by rfl⟩ : syracuseStep 1135695 = 1703543) B1703543
theorem B1135711 : Blo 1132632 1135711 := bstep (se 1 (by rfl) ⟨851783, by rfl⟩ : syracuseStep 1135711 = 1703567) B1703567
theorem B1135739 : Blo 1132632 1135739 := bstep (se 1 (by rfl) ⟨851804, by rfl⟩ : syracuseStep 1135739 = 1703609) B1703609
theorem B3888281 : Blo 1132632 3888281 := bstep (se 2 (by rfl) ⟨1458105, by rfl⟩ : syracuseStep 3888281 = 2916211) B2916211
theorem B1135791 : Blo 1132632 1135791 := bstep (se 1 (by rfl) ⟨851843, by rfl⟩ : syracuseStep 1135791 = 1703687) B1703687
theorem B1135815 : Blo 1132632 1135815 := bstep (se 1 (by rfl) ⟨851861, by rfl⟩ : syracuseStep 1135815 = 1703723) B1703723
theorem B1135835 : Blo 1132632 1135835 := bstep (se 1 (by rfl) ⟨851876, by rfl⟩ : syracuseStep 1135835 = 1703753) B1703753
theorem B1135911 : Blo 1132632 1135911 := bstep (se 1 (by rfl) ⟨851933, by rfl⟩ : syracuseStep 1135911 = 1703867) B1703867
theorem B1135951 : Blo 1132632 1135951 := bstep (se 1 (by rfl) ⟨851963, by rfl⟩ : syracuseStep 1135951 = 1703927) B1703927
theorem B1135967 : Blo 1132632 1135967 := bstep (se 1 (by rfl) ⟨851975, by rfl⟩ : syracuseStep 1135967 = 1703951) B1703951
theorem B1135995 : Blo 1132632 1135995 := bstep (se 1 (by rfl) ⟨851996, by rfl⟩ : syracuseStep 1135995 = 1703993) B1703993
theorem B2872705 : Blo 1132632 2872705 := bstep (se 2 (by rfl) ⟨1077264, by rfl⟩ : syracuseStep 2872705 = 2154529) B2154529
theorem B2151841 : Blo 1132632 2151841 := bstep (se 2 (by rfl) ⟨806940, by rfl⟩ : syracuseStep 2151841 = 1613881) B1613881
theorem B1136047 : Blo 1132632 1136047 := bstep (se 1 (by rfl) ⟨852035, by rfl⟩ : syracuseStep 1136047 = 1704071) B1704071
theorem B1136071 : Blo 1132632 1136071 := bstep (se 1 (by rfl) ⟨852053, by rfl⟩ : syracuseStep 1136071 = 1704107) B1704107
theorem B5821915 : Blo 1132632 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B1136091 : Blo 1132632 1136091 := bstep (se 1 (by rfl) ⟨852068, by rfl⟩ : syracuseStep 1136091 = 1704137) B1704137
theorem B3823091 : Blo 1132632 3823091 := bstep (se 1 (by rfl) ⟨2867318, by rfl⟩ : syracuseStep 3823091 = 5734637) B5734637
theorem B8181287 : Blo 1132632 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B1136167 : Blo 1132632 1136167 := bstep (se 1 (by rfl) ⟨852125, by rfl⟩ : syracuseStep 1136167 = 1704251) B1704251
theorem B1136207 : Blo 1132632 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B1136223 : Blo 1132632 1136223 := bstep (se 1 (by rfl) ⟨852167, by rfl⟩ : syracuseStep 1136223 = 1704335) B1704335
theorem B1136251 : Blo 1132632 1136251 := bstep (se 1 (by rfl) ⟨852188, by rfl⟩ : syracuseStep 1136251 = 1704377) B1704377
theorem B1136303 : Blo 1132632 1136303 := bstep (se 1 (by rfl) ⟨852227, by rfl⟩ : syracuseStep 1136303 = 1704455) B1704455
theorem B1136327 : Blo 1132632 1136327 := bstep (se 1 (by rfl) ⟨852245, by rfl⟩ : syracuseStep 1136327 = 1704491) B1704491
theorem B1136347 : Blo 1132632 1136347 := bstep (se 1 (by rfl) ⟨852260, by rfl⟩ : syracuseStep 1136347 = 1704521) B1704521
theorem B2152183 : Blo 1132632 2152183 := bstep (se 1 (by rfl) ⟨1614137, by rfl⟩ : syracuseStep 2152183 = 3228275) B3228275
theorem B1136423 : Blo 1132632 1136423 := bstep (se 1 (by rfl) ⟨852317, by rfl⟩ : syracuseStep 1136423 = 1704635) B1704635
theorem B1136463 : Blo 1132632 1136463 := bstep (se 1 (by rfl) ⟨852347, by rfl⟩ : syracuseStep 1136463 = 1704695) B1704695
theorem B1136479 : Blo 1132632 1136479 := bstep (se 1 (by rfl) ⟨852359, by rfl⟩ : syracuseStep 1136479 = 1704719) B1704719
theorem B1136507 : Blo 1132632 1136507 := bstep (se 1 (by rfl) ⟨852380, by rfl⟩ : syracuseStep 1136507 = 1704761) B1704761
theorem B1136559 : Blo 1132632 1136559 := bstep (se 1 (by rfl) ⟨852419, by rfl⟩ : syracuseStep 1136559 = 1704839) B1704839
theorem B1136583 : Blo 1132632 1136583 := bstep (se 1 (by rfl) ⟨852437, by rfl⟩ : syracuseStep 1136583 = 1704875) B1704875
theorem B1136603 : Blo 1132632 1136603 := bstep (se 1 (by rfl) ⟨852452, by rfl⟩ : syracuseStep 1136603 = 1704905) B1704905
theorem B3823631 : Blo 1132632 3823631 := bstep (se 1 (by rfl) ⟨2867723, by rfl⟩ : syracuseStep 3823631 = 5735447) B5735447
theorem B2152487 : Blo 1132632 2152487 := bstep (se 1 (by rfl) ⟨1614365, by rfl⟩ : syracuseStep 2152487 = 3228731) B3228731
theorem B2873515 : Blo 1132632 2873515 := bstep (se 1 (by rfl) ⟨2155136, by rfl⟩ : syracuseStep 2873515 = 4310273) B4310273
theorem B2873819 : Blo 1132632 2873819 := bstep (se 1 (by rfl) ⟨2155364, by rfl⟩ : syracuseStep 2873819 = 4310729) B4310729
theorem B11524589 : Blo 1132632 11524589 := bstep (se 3 (by rfl) ⟨2160860, by rfl⟩ : syracuseStep 11524589 = 4321721) B4321721
theorem B3824225 : Blo 1132632 3824225 := bstep (se 2 (by rfl) ⟨1434084, by rfl⟩ : syracuseStep 3824225 = 2868169) B2868169
theorem B12933917 : Blo 1132632 12933917 := bstep (se 3 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 12933917 = 4850219) B4850219
theorem B1531003 : Blo 1132632 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B22109431 : Blo 1132632 22109431 := bstep (se 1 (by rfl) ⟨16582073, by rfl⟩ : syracuseStep 22109431 = 33164147) B33164147
theorem B2154347 : Blo 1132632 2154347 := bstep (se 1 (by rfl) ⟨1615760, by rfl⟩ : syracuseStep 2154347 = 3231521) B3231521
theorem B7364461 : Blo 1132632 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B2875297 : Blo 1132632 2875297 := bstep (se 2 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 2875297 = 2156473) B2156473
theorem B3825683 : Blo 1132632 3825683 := bstep (se 1 (by rfl) ⟨2869262, by rfl⟩ : syracuseStep 3825683 = 5738525) B5738525
theorem B1433639 : Blo 1132632 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B2154575 : Blo 1132632 2154575 := bstep (se 1 (by rfl) ⟨1615931, by rfl⟩ : syracuseStep 2154575 = 3231863) B3231863
theorem B3826007 : Blo 1132632 3826007 := bstep (se 1 (by rfl) ⟨2869505, by rfl⟩ : syracuseStep 3826007 = 5739011) B5739011
theorem B1433963 : Blo 1132632 1433963 := bstep (se 1 (by rfl) ⟨1075472, by rfl⟩ : syracuseStep 1433963 = 2150945) B2150945
theorem B3629555 : Blo 1132632 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B2155015 : Blo 1132632 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B2548655 : Blo 1132632 2548655 := bstep (se 1 (by rfl) ⟨1911491, by rfl⟩ : syracuseStep 2548655 = 3822983) B3822983
theorem B15524783 : Blo 1132632 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B4842497 : Blo 1132632 4842497 := bstep (se 2 (by rfl) ⟨1815936, by rfl⟩ : syracuseStep 4842497 = 3631873) B3631873
theorem B6546511 : Blo 1132632 6546511 := bstep (se 1 (by rfl) ⟨4909883, by rfl⟩ : syracuseStep 6546511 = 9819767) B9819767
theorem B3630233 : Blo 1132632 3630233 := bstep (se 2 (by rfl) ⟨1361337, by rfl⟩ : syracuseStep 3630233 = 2722675) B2722675
theorem B2548907 : Blo 1132632 2548907 := bstep (se 1 (by rfl) ⟨1911680, by rfl⟩ : syracuseStep 2548907 = 3823361) B3823361
theorem B3827087 : Blo 1132632 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B2156071 : Blo 1132632 2156071 := bstep (se 1 (by rfl) ⟨1617053, by rfl⟩ : syracuseStep 2156071 = 3234107) B3234107
theorem B1435259 : Blo 1132632 1435259 := bstep (se 1 (by rfl) ⟨1076444, by rfl⟩ : syracuseStep 1435259 = 2152889) B2152889
theorem B29091473 : Blo 1132632 29091473 := bstep (se 2 (by rfl) ⟨10909302, by rfl⟩ : syracuseStep 29091473 = 21818605) B21818605
theorem B2549447 : Blo 1132632 2549447 := bstep (se 1 (by rfl) ⟨1912085, by rfl⟩ : syracuseStep 2549447 = 3824171) B3824171
theorem B3827411 : Blo 1132632 3827411 := bstep (se 1 (by rfl) ⟨2870558, by rfl⟩ : syracuseStep 3827411 = 5741117) B5741117
theorem B4090009 : Blo 1132632 4090009 := bstep (se 2 (by rfl) ⟨1533753, by rfl⟩ : syracuseStep 4090009 = 3067507) B3067507
theorem B2550311 : Blo 1132632 2550311 := bstep (se 1 (by rfl) ⟨1912733, by rfl⟩ : syracuseStep 2550311 = 3825467) B3825467
theorem B2550635 : Blo 1132632 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B3828599 : Blo 1132632 3828599 := bstep (se 1 (by rfl) ⟨2871449, by rfl⟩ : syracuseStep 3828599 = 5742899) B5742899
theorem B2550689 : Blo 1132632 2550689 := bstep (se 2 (by rfl) ⟨956508, by rfl⟩ : syracuseStep 2550689 = 1913017) B1913017
theorem B3632129 : Blo 1132632 3632129 := bstep (se 2 (by rfl) ⟨1362048, by rfl⟩ : syracuseStep 3632129 = 2724097) B2724097
theorem B3828815 : Blo 1132632 3828815 := bstep (se 1 (by rfl) ⟨2871611, by rfl⟩ : syracuseStep 3828815 = 5743223) B5743223
theorem B2157779 : Blo 1132632 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B2551031 : Blo 1132632 2551031 := bstep (se 1 (by rfl) ⟨1913273, by rfl⟩ : syracuseStep 2551031 = 3826547) B3826547
theorem B14740825 : Blo 1132632 14740825 := bstep (se 2 (by rfl) ⟨5527809, by rfl⟩ : syracuseStep 14740825 = 11055619) B11055619
theorem B3632489 : Blo 1132632 3632489 := bstep (se 2 (by rfl) ⟨1362183, by rfl⟩ : syracuseStep 3632489 = 2724367) B2724367
theorem B1699247 : Blo 1132632 1699247 := bstep (se 1 (by rfl) ⟨1274435, by rfl⟩ : syracuseStep 1699247 = 2548871) B2548871
theorem B3829193 : Blo 1132632 3829193 := bstep (se 2 (by rfl) ⟨1435947, by rfl⟩ : syracuseStep 3829193 = 2871895) B2871895
theorem B1699337 : Blo 1132632 1699337 := bstep (se 2 (by rfl) ⟨637251, by rfl⟩ : syracuseStep 1699337 = 1274503) B1274503
theorem B1699367 : Blo 1132632 1699367 := bstep (se 1 (by rfl) ⟨1274525, by rfl⟩ : syracuseStep 1699367 = 2549051) B2549051
theorem B4845095 : Blo 1132632 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B6450785 : Blo 1132632 6450785 := bstep (se 2 (by rfl) ⟨2419044, by rfl⟩ : syracuseStep 6450785 = 4838089) B4838089
theorem B1699451 : Blo 1132632 1699451 := bstep (se 1 (by rfl) ⟨1274588, by rfl⟩ : syracuseStep 1699451 = 2549177) B2549177
theorem B3829463 : Blo 1132632 3829463 := bstep (se 1 (by rfl) ⟨2872097, by rfl⟩ : syracuseStep 3829463 = 5744195) B5744195
theorem B1699577 : Blo 1132632 1699577 := bstep (se 2 (by rfl) ⟨637341, by rfl⟩ : syracuseStep 1699577 = 1274683) B1274683
theorem B10907459 : Blo 1132632 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B2551625 : Blo 1132632 2551625 := bstep (se 2 (by rfl) ⟨956859, by rfl⟩ : syracuseStep 2551625 = 1913719) B1913719
theorem B1699679 : Blo 1132632 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B1699691 : Blo 1132632 1699691 := bstep (se 1 (by rfl) ⟨1274768, by rfl⟩ : syracuseStep 1699691 = 2549537) B2549537
theorem B3829679 : Blo 1132632 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B1699919 : Blo 1132632 1699919 := bstep (se 1 (by rfl) ⟨1274939, by rfl⟩ : syracuseStep 1699919 = 2549879) B2549879
theorem B1536079 : Blo 1132632 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B1700039 : Blo 1132632 1700039 := bstep (se 1 (by rfl) ⟨1275029, by rfl⟩ : syracuseStep 1700039 = 2550059) B2550059
theorem B7270667 : Blo 1132632 7270667 := bstep (se 1 (by rfl) ⟨5453000, by rfl⟩ : syracuseStep 7270667 = 10906001) B10906001
theorem B1700201 : Blo 1132632 1700201 := bstep (se 2 (by rfl) ⟨637575, by rfl⟩ : syracuseStep 1700201 = 1275151) B1275151
theorem B8188265 : Blo 1132632 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B1274287 : Blo 1132632 1274287 := bstep (se 1 (by rfl) ⟨955715, by rfl⟩ : syracuseStep 1274287 = 1911431) B1911431
theorem B1700279 : Blo 1132632 1700279 := bstep (se 1 (by rfl) ⟨1275209, by rfl⟩ : syracuseStep 1700279 = 2550419) B2550419
theorem B1700315 : Blo 1132632 1700315 := bstep (se 1 (by rfl) ⟨1275236, by rfl⟩ : syracuseStep 1700315 = 2550473) B2550473
theorem B2552417 : Blo 1132632 2552417 := bstep (se 2 (by rfl) ⟨957156, by rfl⟩ : syracuseStep 2552417 = 1914313) B1914313
theorem B10351313 : Blo 1132632 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B6222665 : Blo 1132632 6222665 := bstep (se 2 (by rfl) ⟨2333499, by rfl⟩ : syracuseStep 6222665 = 4666999) B4666999
theorem B1274719 : Blo 1132632 1274719 := bstep (se 1 (by rfl) ⟨956039, by rfl⟩ : syracuseStep 1274719 = 1912079) B1912079
theorem B1700783 : Blo 1132632 1700783 := bstep (se 1 (by rfl) ⟨1275587, by rfl⟩ : syracuseStep 1700783 = 2551175) B2551175
theorem B2552759 : Blo 1132632 2552759 := bstep (se 1 (by rfl) ⟨1914569, by rfl⟩ : syracuseStep 2552759 = 3829139) B3829139
theorem B1700873 : Blo 1132632 1700873 := bstep (se 2 (by rfl) ⟨637827, by rfl⟩ : syracuseStep 1700873 = 1275655) B1275655
theorem B6452243 : Blo 1132632 6452243 := bstep (se 1 (by rfl) ⟨4839182, by rfl⟩ : syracuseStep 6452243 = 9678365) B9678365
theorem B1700903 : Blo 1132632 1700903 := bstep (se 1 (by rfl) ⟨1275677, by rfl⟩ : syracuseStep 1700903 = 2551355) B2551355
theorem B31028291 : Blo 1132632 31028291 := bstep (se 1 (by rfl) ⟨23271218, by rfl⟩ : syracuseStep 31028291 = 46542437) B46542437
theorem B1700987 : Blo 1132632 1700987 := bstep (se 1 (by rfl) ⟨1275740, by rfl⟩ : syracuseStep 1700987 = 2551481) B2551481
theorem B12907673 : Blo 1132632 12907673 := bstep (se 2 (by rfl) ⟨4840377, by rfl⟩ : syracuseStep 12907673 = 9680755) B9680755
theorem B4846787 : Blo 1132632 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B1275079 : Blo 1132632 1275079 := bstep (se 1 (by rfl) ⟨956309, by rfl⟩ : syracuseStep 1275079 = 1912619) B1912619
theorem B26211529 : Blo 1132632 26211529 := bstep (se 2 (by rfl) ⟨9829323, by rfl⟩ : syracuseStep 26211529 = 19658647) B19658647
theorem B1701113 : Blo 1132632 1701113 := bstep (se 2 (by rfl) ⟨637917, by rfl⟩ : syracuseStep 1701113 = 1275835) B1275835
theorem B1701215 : Blo 1132632 1701215 := bstep (se 1 (by rfl) ⟨1275911, by rfl⟩ : syracuseStep 1701215 = 2551823) B2551823
theorem B1701227 : Blo 1132632 1701227 := bstep (se 1 (by rfl) ⟨1275920, by rfl⟩ : syracuseStep 1701227 = 2551841) B2551841
theorem B2553353 : Blo 1132632 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B1701455 : Blo 1132632 1701455 := bstep (se 1 (by rfl) ⟨1276091, by rfl⟩ : syracuseStep 1701455 = 2552183) B2552183
theorem B32765633 : Blo 1132632 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B1701575 : Blo 1132632 1701575 := bstep (se 1 (by rfl) ⟨1276181, by rfl⟩ : syracuseStep 1701575 = 2552363) B2552363
theorem B16578341 : Blo 1132632 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B2553695 : Blo 1132632 2553695 := bstep (se 1 (by rfl) ⟨1915271, by rfl⟩ : syracuseStep 2553695 = 3830543) B3830543
theorem B1701737 : Blo 1132632 1701737 := bstep (se 2 (by rfl) ⟨638151, by rfl⟩ : syracuseStep 1701737 = 1276303) B1276303
theorem B1701815 : Blo 1132632 1701815 := bstep (se 1 (by rfl) ⟨1276361, by rfl⟩ : syracuseStep 1701815 = 2552723) B2552723
theorem B1701851 : Blo 1132632 1701851 := bstep (se 1 (by rfl) ⟨1276388, by rfl⟩ : syracuseStep 1701851 = 2552777) B2552777
theorem B2553875 : Blo 1132632 2553875 := bstep (se 1 (by rfl) ⟨1915406, by rfl⟩ : syracuseStep 2553875 = 3830813) B3830813
theorem B1275943 : Blo 1132632 1275943 := bstep (se 1 (by rfl) ⟨956957, by rfl⟩ : syracuseStep 1275943 = 1913915) B1913915
theorem B3832055 : Blo 1132632 3832055 := bstep (se 1 (by rfl) ⟨2874041, by rfl⟩ : syracuseStep 3832055 = 5748083) B5748083
theorem B4094219 : Blo 1132632 4094219 := bstep (se 1 (by rfl) ⟨3070664, by rfl⟩ : syracuseStep 4094219 = 6141329) B6141329
theorem B2554217 : Blo 1132632 2554217 := bstep (se 2 (by rfl) ⟨957831, by rfl⟩ : syracuseStep 2554217 = 1915663) B1915663
theorem B1702319 : Blo 1132632 1702319 := bstep (se 1 (by rfl) ⟨1276739, by rfl⟩ : syracuseStep 1702319 = 2553479) B2553479
theorem B1702409 : Blo 1132632 1702409 := bstep (se 2 (by rfl) ⟨638403, by rfl⟩ : syracuseStep 1702409 = 1276807) B1276807
theorem B1702439 : Blo 1132632 1702439 := bstep (se 1 (by rfl) ⟨1276829, by rfl⟩ : syracuseStep 1702439 = 2553659) B2553659
theorem B3832379 : Blo 1132632 3832379 := bstep (se 1 (by rfl) ⟨2874284, by rfl⟩ : syracuseStep 3832379 = 5748569) B5748569
theorem B1702523 : Blo 1132632 1702523 := bstep (se 1 (by rfl) ⟨1276892, by rfl⟩ : syracuseStep 1702523 = 2553785) B2553785
theorem B1702649 : Blo 1132632 1702649 := bstep (se 2 (by rfl) ⟨638493, by rfl⟩ : syracuseStep 1702649 = 1276987) B1276987
theorem B6454019 : Blo 1132632 6454019 := bstep (se 1 (by rfl) ⟨4840514, by rfl⟩ : syracuseStep 6454019 = 9681029) B9681029
theorem B3832649 : Blo 1132632 3832649 := bstep (se 2 (by rfl) ⟨1437243, by rfl⟩ : syracuseStep 3832649 = 2874487) B2874487
theorem B1211231 : Blo 1132632 1211231 := bstep (se 1 (by rfl) ⟨908423, by rfl⟩ : syracuseStep 1211231 = 1816847) B1816847
theorem B1702751 : Blo 1132632 1702751 := bstep (se 1 (by rfl) ⟨1277063, by rfl⟩ : syracuseStep 1702751 = 2554127) B2554127
theorem B1702763 : Blo 1132632 1702763 := bstep (se 1 (by rfl) ⟨1277072, by rfl⟩ : syracuseStep 1702763 = 2554145) B2554145
theorem B2554811 : Blo 1132632 2554811 := bstep (se 1 (by rfl) ⟨1916108, by rfl⟩ : syracuseStep 2554811 = 3832217) B3832217
theorem B2554937 : Blo 1132632 2554937 := bstep (se 2 (by rfl) ⟨958101, by rfl⟩ : syracuseStep 2554937 = 1916203) B1916203
theorem B1702991 : Blo 1132632 1702991 := bstep (se 1 (by rfl) ⟨1277243, by rfl⟩ : syracuseStep 1702991 = 2554487) B2554487
theorem B1703111 : Blo 1132632 1703111 := bstep (se 1 (by rfl) ⟨1277333, by rfl⟩ : syracuseStep 1703111 = 2554667) B2554667
theorem B6454475 : Blo 1132632 6454475 := bstep (se 1 (by rfl) ⟨4840856, by rfl⟩ : syracuseStep 6454475 = 9681713) B9681713
theorem B1703273 : Blo 1132632 1703273 := bstep (se 2 (by rfl) ⟨638727, by rfl⟩ : syracuseStep 1703273 = 1277455) B1277455
theorem B7273871 : Blo 1132632 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B2555279 : Blo 1132632 2555279 := bstep (se 1 (by rfl) ⟨1916459, by rfl⟩ : syracuseStep 2555279 = 3832919) B3832919
theorem B6225295 : Blo 1132632 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B10911149 : Blo 1132632 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1703351 : Blo 1132632 1703351 := bstep (se 1 (by rfl) ⟨1277513, by rfl⟩ : syracuseStep 1703351 = 2555027) B2555027
theorem B1703387 : Blo 1132632 1703387 := bstep (se 1 (by rfl) ⟨1277540, by rfl⟩ : syracuseStep 1703387 = 2555081) B2555081
theorem B1277563 : Blo 1132632 1277563 := bstep (se 1 (by rfl) ⟨958172, by rfl⟩ : syracuseStep 1277563 = 1916345) B1916345
theorem B3636947 : Blo 1132632 3636947 := bstep (se 1 (by rfl) ⟨2727710, by rfl⟩ : syracuseStep 3636947 = 5455421) B5455421
theorem B2555603 : Blo 1132632 2555603 := bstep (se 1 (by rfl) ⟨1916702, by rfl⟩ : syracuseStep 2555603 = 3833405) B3833405
theorem B2424649 : Blo 1132632 2424649 := bstep (se 2 (by rfl) ⟨909243, by rfl⟩ : syracuseStep 2424649 = 1818487) B1818487
theorem B9207647 : Blo 1132632 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B6455159 : Blo 1132632 6455159 := bstep (se 1 (by rfl) ⟨4841369, by rfl⟩ : syracuseStep 6455159 = 9682739) B9682739
theorem B1703855 : Blo 1132632 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B3833783 : Blo 1132632 3833783 := bstep (se 1 (by rfl) ⟨2875337, by rfl⟩ : syracuseStep 3833783 = 5750675) B5750675
theorem B10911763 : Blo 1132632 10911763 := bstep (se 1 (by rfl) ⟨8183822, by rfl⟩ : syracuseStep 10911763 = 16367645) B16367645
theorem B2588777 : Blo 1132632 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B1704041 : Blo 1132632 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B1278247 : Blo 1132632 1278247 := bstep (se 1 (by rfl) ⟨958685, by rfl⟩ : syracuseStep 1278247 = 1917371) B1917371
theorem B2556233 : Blo 1132632 2556233 := bstep (se 2 (by rfl) ⟨958587, by rfl⟩ : syracuseStep 2556233 = 1917175) B1917175
theorem B2556251 : Blo 1132632 2556251 := bstep (se 1 (by rfl) ⟨1917188, by rfl⟩ : syracuseStep 2556251 = 3834377) B3834377
theorem B1278319 : Blo 1132632 1278319 := bstep (se 1 (by rfl) ⟨958739, by rfl⟩ : syracuseStep 1278319 = 1917479) B1917479
theorem B1704359 : Blo 1132632 1704359 := bstep (se 1 (by rfl) ⟨1278269, by rfl⟩ : syracuseStep 1704359 = 2556539) B2556539
theorem B1704443 : Blo 1132632 1704443 := bstep (se 1 (by rfl) ⟨1278332, by rfl⟩ : syracuseStep 1704443 = 2556665) B2556665
theorem B6128179 : Blo 1132632 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B1278535 : Blo 1132632 1278535 := bstep (se 1 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 1278535 = 1917803) B1917803
theorem B1704569 : Blo 1132632 1704569 := bstep (se 2 (by rfl) ⟨639213, by rfl⟩ : syracuseStep 1704569 = 1278427) B1278427
theorem B3834539 : Blo 1132632 3834539 := bstep (se 1 (by rfl) ⟨2875904, by rfl⟩ : syracuseStep 3834539 = 5751809) B5751809
theorem B1704623 : Blo 1132632 1704623 := bstep (se 1 (by rfl) ⟨1278467, by rfl⟩ : syracuseStep 1704623 = 2556935) B2556935
theorem B1704671 : Blo 1132632 1704671 := bstep (se 1 (by rfl) ⟨1278503, by rfl⟩ : syracuseStep 1704671 = 2557007) B2557007
theorem B2556827 : Blo 1132632 2556827 := bstep (se 1 (by rfl) ⟨1917620, by rfl⟩ : syracuseStep 2556827 = 3835241) B3835241
theorem B1704935 : Blo 1132632 1704935 := bstep (se 1 (by rfl) ⟨1278701, by rfl⟩ : syracuseStep 1704935 = 2557403) B2557403
theorem B2557025 : Blo 1132632 2557025 := bstep (se 2 (by rfl) ⟨958884, by rfl⟩ : syracuseStep 2557025 = 1917769) B1917769
theorem B11633807 : Blo 1132632 11633807 := bstep (se 1 (by rfl) ⟨8725355, by rfl⟩ : syracuseStep 11633807 = 17450711) B17450711
theorem B4850887 : Blo 1132632 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B3835079 : Blo 1132632 3835079 := bstep (se 1 (by rfl) ⟨2876309, by rfl⟩ : syracuseStep 3835079 = 5752619) B5752619
theorem B4850903 : Blo 1132632 4850903 := bstep (se 1 (by rfl) ⟨3638177, by rfl⟩ : syracuseStep 4850903 = 7276355) B7276355
theorem B2557223 : Blo 1132632 2557223 := bstep (se 1 (by rfl) ⟨1917917, by rfl⟩ : syracuseStep 2557223 = 3835835) B3835835
theorem B2426375 : Blo 1132632 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B4851485 : Blo 1132632 4851485 := bstep (se 3 (by rfl) ⟨909653, by rfl⟩ : syracuseStep 4851485 = 1819307) B1819307
theorem B3639127 : Blo 1132632 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B6129911 : Blo 1132632 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B2722367 : Blo 1132632 2722367 := bstep (se 1 (by rfl) ⟨2041775, by rfl⟩ : syracuseStep 2722367 = 4083551) B4083551
theorem B5737067 : Blo 1132632 5737067 := bstep (se 1 (by rfl) ⟨4302800, by rfl⟩ : syracuseStep 5737067 = 8605601) B8605601
theorem B8620667 : Blo 1132632 8620667 := bstep (se 1 (by rfl) ⟨6465500, by rfl⟩ : syracuseStep 8620667 = 12931001) B12931001
theorem B7867127 : Blo 1132632 7867127 := bstep (se 1 (by rfl) ⟨5900345, by rfl⟩ : syracuseStep 7867127 = 11800691) B11800691
theorem B335285041 : Blo 1132632 335285041 := bstep (se 2 (by rfl) ⟨125731890, by rfl⟩ : syracuseStep 335285041 = 251463781) B251463781
theorem B5737553 : Blo 1132632 5737553 := bstep (se 2 (by rfl) ⟨2151582, by rfl⟩ : syracuseStep 5737553 = 4303165) B4303165
theorem B4852817 : Blo 1132632 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B3640459 : Blo 1132632 3640459 := bstep (se 1 (by rfl) ⟨2730344, by rfl⟩ : syracuseStep 3640459 = 5460689) B5460689
theorem B43617527 : Blo 1132632 43617527 := bstep (se 1 (by rfl) ⟨32713145, by rfl⟩ : syracuseStep 43617527 = 65426291) B65426291
theorem B2723195 : Blo 1132632 2723195 := bstep (se 1 (by rfl) ⟨2042396, by rfl⟩ : syracuseStep 2723195 = 4084793) B4084793
theorem B11800027 : Blo 1132632 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B6131209 : Blo 1132632 6131209 := bstep (se 2 (by rfl) ⟨2299203, by rfl⟩ : syracuseStep 6131209 = 4598407) B4598407
theorem B8622611 : Blo 1132632 8622611 := bstep (se 1 (by rfl) ⟨6466958, by rfl⟩ : syracuseStep 8622611 = 12933917) B12933917
theorem B2724425 : Blo 1132632 2724425 := bstep (se 2 (by rfl) ⟨1021659, by rfl⟩ : syracuseStep 2724425 = 2043319) B2043319
theorem B9311377 : Blo 1132632 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B9213421 : Blo 1132632 9213421 := bstep (se 3 (by rfl) ⟨1727516, by rfl⟩ : syracuseStep 9213421 = 3455033) B3455033
theorem B6560363 : Blo 1132632 6560363 := bstep (se 1 (by rfl) ⟨4920272, by rfl⟩ : syracuseStep 6560363 = 9840545) B9840545
theorem B1940089 : Blo 1132632 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B2300599 : Blo 1132632 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B14523137 : Blo 1132632 14523137 := bstep (se 2 (by rfl) ⟨5446176, by rfl⟩ : syracuseStep 14523137 = 10892353) B10892353
theorem B6135101 : Blo 1132632 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B5742089 : Blo 1132632 5742089 := bstep (se 2 (by rfl) ⟨2153283, by rfl⟩ : syracuseStep 5742089 = 4306567) B4306567
theorem B4300523 : Blo 1132632 4300523 := bstep (se 1 (by rfl) ⟨3225392, by rfl⟩ : syracuseStep 4300523 = 6450785) B6450785
theorem B10887007 : Blo 1132632 10887007 := bstep (se 1 (by rfl) ⟨8165255, by rfl⟩ : syracuseStep 10887007 = 16330511) B16330511
theorem B4301009 : Blo 1132632 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2302319 : Blo 1132632 2302319 := bstep (se 1 (by rfl) ⟨1726739, by rfl⟩ : syracuseStep 2302319 = 3453479) B3453479
theorem B4301495 : Blo 1132632 4301495 := bstep (se 1 (by rfl) ⟨3226121, by rfl⟩ : syracuseStep 4301495 = 6452243) B6452243
theorem B20685527 : Blo 1132632 20685527 := bstep (se 1 (by rfl) ⟨15514145, by rfl⟩ : syracuseStep 20685527 = 31028291) B31028291
theorem B2302739 : Blo 1132632 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B11052227 : Blo 1132632 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B49063157 : Blo 1132632 49063157 := bstep (se 5 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 49063157 = 4599671) B4599671
theorem B5744033 : Blo 1132632 5744033 := bstep (se 2 (by rfl) ⟨2154012, by rfl⟩ : syracuseStep 5744033 = 4308025) B4308025
theorem B2041337 : Blo 1132632 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B2729479 : Blo 1132632 2729479 := bstep (se 1 (by rfl) ⟨2047109, by rfl⟩ : syracuseStep 2729479 = 4094219) B4094219
theorem B4302679 : Blo 1132632 4302679 := bstep (se 1 (by rfl) ⟨3227009, by rfl⟩ : syracuseStep 4302679 = 6454019) B6454019
theorem B8300393 : Blo 1132632 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B34875299 : Blo 1132632 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B5449655 : Blo 1132632 5449655 := bstep (se 1 (by rfl) ⟨4087241, by rfl⟩ : syracuseStep 5449655 = 8174483) B8174483
theorem B4302983 : Blo 1132632 4302983 := bstep (se 1 (by rfl) ⟨3227237, by rfl⟩ : syracuseStep 4302983 = 6454475) B6454475
theorem B12265667 : Blo 1132632 12265667 := bstep (se 1 (by rfl) ⟨9199250, by rfl⟩ : syracuseStep 12265667 = 18398501) B18398501
theorem B6138431 : Blo 1132632 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B4303439 : Blo 1132632 4303439 := bstep (se 1 (by rfl) ⟨3227579, by rfl⟩ : syracuseStep 4303439 = 6455159) B6455159
theorem B19376819 : Blo 1132632 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B1912187 : Blo 1132632 1912187 := bstep (se 1 (by rfl) ⟨1434140, by rfl⟩ : syracuseStep 1912187 = 2868281) B2868281
theorem B3452651 : Blo 1132632 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B44183825 : Blo 1132632 44183825 := bstep (se 2 (by rfl) ⟨16568934, by rfl⟩ : syracuseStep 44183825 = 33137869) B33137869
theorem B1913179 : Blo 1132632 1913179 := bstep (se 1 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 1913179 = 2869769) B2869769
theorem B14725595 : Blo 1132632 14725595 := bstep (se 1 (by rfl) ⟨11044196, by rfl⟩ : syracuseStep 14725595 = 22088393) B22088393
theorem B10367945 : Blo 1132632 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B1815527 : Blo 1132632 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B2044919 : Blo 1132632 2044919 := bstep (se 1 (by rfl) ⟨1533689, by rfl⟩ : syracuseStep 2044919 = 3067379) B3067379
theorem B6468599 : Blo 1132632 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B4306067 : Blo 1132632 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B1914151 : Blo 1132632 1914151 := bstep (se 1 (by rfl) ⟨1435613, by rfl⟩ : syracuseStep 1914151 = 2871227) B2871227
theorem B119387525 : Blo 1132632 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B24557003 : Blo 1132632 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B5453345 : Blo 1132632 5453345 := bstep (se 2 (by rfl) ⟨2045004, by rfl⟩ : syracuseStep 5453345 = 4090009) B4090009
theorem B6469307 : Blo 1132632 6469307 := bstep (se 1 (by rfl) ⟨4851980, by rfl⟩ : syracuseStep 6469307 = 9703961) B9703961
theorem B10368749 : Blo 1132632 10368749 := bstep (se 3 (by rfl) ⟨1944140, by rfl⟩ : syracuseStep 10368749 = 3888281) B3888281
theorem B1914671 : Blo 1132632 1914671 := bstep (se 1 (by rfl) ⟨1436003, by rfl⟩ : syracuseStep 1914671 = 2872007) B2872007
theorem B5454191 : Blo 1132632 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B6142711 : Blo 1132632 6142711 := bstep (se 1 (by rfl) ⟨4607033, by rfl⟩ : syracuseStep 6142711 = 9214067) B9214067
theorem B13089691 : Blo 1132632 13089691 := bstep (se 1 (by rfl) ⟨9817268, by rfl⟩ : syracuseStep 13089691 = 19634537) B19634537
theorem B1915879 : Blo 1132632 1915879 := bstep (se 1 (by rfl) ⟨1436909, by rfl⟩ : syracuseStep 1915879 = 2873819) B2873819
theorem B7683059 : Blo 1132632 7683059 := bstep (se 1 (by rfl) ⟨5762294, by rfl⟩ : syracuseStep 7683059 = 11524589) B11524589
theorem B5750027 : Blo 1132632 5750027 := bstep (se 1 (by rfl) ⟨4312520, by rfl⟩ : syracuseStep 5750027 = 8625041) B8625041
theorem B2866985 : Blo 1132632 2866985 := bstep (se 2 (by rfl) ⟨1075119, by rfl⟩ : syracuseStep 2866985 = 2150239) B2150239
theorem B2048105 : Blo 1132632 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B34914725 : Blo 1132632 34914725 := bstep (se 4 (by rfl) ⟨3273255, by rfl⟩ : syracuseStep 34914725 = 6546511) B6546511
theorem B9683489 : Blo 1132632 9683489 := bstep (se 2 (by rfl) ⟨3631308, by rfl⟩ : syracuseStep 9683489 = 7262617) B7262617
theorem B3228331 : Blo 1132632 3228331 := bstep (se 1 (by rfl) ⟨2421248, by rfl⟩ : syracuseStep 3228331 = 4842497) B4842497
theorem B2867987 : Blo 1132632 2867987 := bstep (se 1 (by rfl) ⟨2150990, by rfl⟩ : syracuseStep 2867987 = 4301981) B4301981
theorem B3064655 : Blo 1132632 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B5751647 : Blo 1132632 5751647 := bstep (se 1 (by rfl) ⟨4313735, by rfl⟩ : syracuseStep 5751647 = 8627471) B8627471
theorem B4309955 : Blo 1132632 4309955 := bstep (se 1 (by rfl) ⟨3232466, by rfl⟩ : syracuseStep 4309955 = 6464933) B6464933
theorem B2868443 : Blo 1132632 2868443 := bstep (se 1 (by rfl) ⟨2151332, by rfl⟩ : syracuseStep 2868443 = 4302665) B4302665
theorem B2868473 : Blo 1132632 2868473 := bstep (se 2 (by rfl) ⟨1075677, by rfl⟩ : syracuseStep 2868473 = 2151355) B2151355
theorem B34948705 : Blo 1132632 34948705 := bstep (se 2 (by rfl) ⟨13105764, by rfl⟩ : syracuseStep 34948705 = 26211529) B26211529
theorem B2869121 : Blo 1132632 2869121 := bstep (se 2 (by rfl) ⟨1075920, by rfl⟩ : syracuseStep 2869121 = 2151841) B2151841
theorem B3229949 : Blo 1132632 3229949 := bstep (se 3 (by rfl) ⟨605615, by rfl⟩ : syracuseStep 3229949 = 1211231) B1211231
theorem B1132831 : Blo 1132632 1132831 := bstep (se 1 (by rfl) ⟨849623, by rfl⟩ : syracuseStep 1132831 = 1699247) B1699247
theorem B2869577 : Blo 1132632 2869577 := bstep (se 2 (by rfl) ⟨1076091, by rfl⟩ : syracuseStep 2869577 = 2152183) B2152183
theorem B1132891 : Blo 1132632 1132891 := bstep (se 1 (by rfl) ⟨849668, by rfl⟩ : syracuseStep 1132891 = 1699337) B1699337
theorem B1132911 : Blo 1132632 1132911 := bstep (se 1 (by rfl) ⟨849683, by rfl⟩ : syracuseStep 1132911 = 1699367) B1699367
theorem B3230063 : Blo 1132632 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B1132967 : Blo 1132632 1132967 := bstep (se 1 (by rfl) ⟨849725, by rfl⟩ : syracuseStep 1132967 = 1699451) B1699451
theorem B1133051 : Blo 1132632 1133051 := bstep (se 1 (by rfl) ⟨849788, by rfl⟩ : syracuseStep 1133051 = 1699577) B1699577
theorem B1133119 : Blo 1132632 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B1133127 : Blo 1132632 1133127 := bstep (se 1 (by rfl) ⟨849845, by rfl⟩ : syracuseStep 1133127 = 1699691) B1699691
theorem B2869931 : Blo 1132632 2869931 := bstep (se 1 (by rfl) ⟨2152448, by rfl⟩ : syracuseStep 2869931 = 4304897) B4304897
theorem B1133279 : Blo 1132632 1133279 := bstep (se 1 (by rfl) ⟨849959, by rfl⟩ : syracuseStep 1133279 = 1699919) B1699919
theorem B5753591 : Blo 1132632 5753591 := bstep (se 1 (by rfl) ⟨4315193, by rfl⟩ : syracuseStep 5753591 = 8630387) B8630387
theorem B1133359 : Blo 1132632 1133359 := bstep (se 1 (by rfl) ⟨850019, by rfl⟩ : syracuseStep 1133359 = 1700039) B1700039
theorem B1133467 : Blo 1132632 1133467 := bstep (se 1 (by rfl) ⟨850100, by rfl⟩ : syracuseStep 1133467 = 1700201) B1700201
theorem B5458843 : Blo 1132632 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B1133519 : Blo 1132632 1133519 := bstep (se 1 (by rfl) ⟨850139, by rfl⟩ : syracuseStep 1133519 = 1700279) B1700279
theorem B1133543 : Blo 1132632 1133543 := bstep (se 1 (by rfl) ⟨850157, by rfl⟩ : syracuseStep 1133543 = 1700315) B1700315
theorem B4312187 : Blo 1132632 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B6900875 : Blo 1132632 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B4148443 : Blo 1132632 4148443 := bstep (se 1 (by rfl) ⟨3111332, by rfl⟩ : syracuseStep 4148443 = 6222665) B6222665
theorem B5754077 : Blo 1132632 5754077 := bstep (se 3 (by rfl) ⟨1078889, by rfl⟩ : syracuseStep 5754077 = 2157779) B2157779
theorem B1133855 : Blo 1132632 1133855 := bstep (se 1 (by rfl) ⟨850391, by rfl⟩ : syracuseStep 1133855 = 1700783) B1700783
theorem B1133915 : Blo 1132632 1133915 := bstep (se 1 (by rfl) ⟨850436, by rfl⟩ : syracuseStep 1133915 = 1700873) B1700873
theorem B1133935 : Blo 1132632 1133935 := bstep (se 1 (by rfl) ⟨850451, by rfl⟩ : syracuseStep 1133935 = 1700903) B1700903
theorem B1133991 : Blo 1132632 1133991 := bstep (se 1 (by rfl) ⟨850493, by rfl⟩ : syracuseStep 1133991 = 1700987) B1700987
theorem B8605115 : Blo 1132632 8605115 := bstep (se 1 (by rfl) ⟨6453836, by rfl⟩ : syracuseStep 8605115 = 12907673) B12907673
theorem B3231191 : Blo 1132632 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B1134075 : Blo 1132632 1134075 := bstep (se 1 (by rfl) ⟨850556, by rfl⟩ : syracuseStep 1134075 = 1701113) B1701113
theorem B1134143 : Blo 1132632 1134143 := bstep (se 1 (by rfl) ⟨850607, by rfl⟩ : syracuseStep 1134143 = 1701215) B1701215
theorem B1134151 : Blo 1132632 1134151 := bstep (se 1 (by rfl) ⟨850613, by rfl⟩ : syracuseStep 1134151 = 1701227) B1701227
theorem B1134303 : Blo 1132632 1134303 := bstep (se 1 (by rfl) ⟨850727, by rfl⟩ : syracuseStep 1134303 = 1701455) B1701455
theorem B3067627 : Blo 1132632 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B21843755 : Blo 1132632 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B1134383 : Blo 1132632 1134383 := bstep (se 1 (by rfl) ⟨850787, by rfl⟩ : syracuseStep 1134383 = 1701575) B1701575
theorem B1134491 : Blo 1132632 1134491 := bstep (se 1 (by rfl) ⟨850868, by rfl⟩ : syracuseStep 1134491 = 1701737) B1701737
theorem B2871247 : Blo 1132632 2871247 := bstep (se 1 (by rfl) ⟨2153435, by rfl⟩ : syracuseStep 2871247 = 4306871) B4306871
theorem B1134543 : Blo 1132632 1134543 := bstep (se 1 (by rfl) ⟨850907, by rfl⟩ : syracuseStep 1134543 = 1701815) B1701815
theorem B1134567 : Blo 1132632 1134567 := bstep (se 1 (by rfl) ⟨850925, by rfl⟩ : syracuseStep 1134567 = 1701851) B1701851
theorem B1134879 : Blo 1132632 1134879 := bstep (se 1 (by rfl) ⟨851159, by rfl⟩ : syracuseStep 1134879 = 1702319) B1702319
theorem B29479241 : Blo 1132632 29479241 := bstep (se 2 (by rfl) ⟨11054715, by rfl⟩ : syracuseStep 29479241 = 22109431) B22109431
theorem B1134939 : Blo 1132632 1134939 := bstep (se 1 (by rfl) ⟨851204, by rfl⟩ : syracuseStep 1134939 = 1702409) B1702409
theorem B1134959 : Blo 1132632 1134959 := bstep (se 1 (by rfl) ⟨851219, by rfl⟩ : syracuseStep 1134959 = 1702439) B1702439
theorem B1135015 : Blo 1132632 1135015 := bstep (se 1 (by rfl) ⟨851261, by rfl⟩ : syracuseStep 1135015 = 1702523) B1702523
theorem B1135099 : Blo 1132632 1135099 := bstep (se 1 (by rfl) ⟨851324, by rfl⟩ : syracuseStep 1135099 = 1702649) B1702649
theorem B2150975 : Blo 1132632 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B1135167 : Blo 1132632 1135167 := bstep (se 1 (by rfl) ⟨851375, by rfl⟩ : syracuseStep 1135167 = 1702751) B1702751
theorem B1135175 : Blo 1132632 1135175 := bstep (se 1 (by rfl) ⟨851381, by rfl⟩ : syracuseStep 1135175 = 1702763) B1702763
theorem B1135327 : Blo 1132632 1135327 := bstep (se 1 (by rfl) ⟨851495, by rfl⟩ : syracuseStep 1135327 = 1702991) B1702991
theorem B20960003 : Blo 1132632 20960003 := bstep (se 1 (by rfl) ⟨15720002, by rfl⟩ : syracuseStep 20960003 = 31440005) B31440005
theorem B1135407 : Blo 1132632 1135407 := bstep (se 1 (by rfl) ⟨851555, by rfl⟩ : syracuseStep 1135407 = 1703111) B1703111
theorem B8606573 : Blo 1132632 8606573 := bstep (se 3 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 8606573 = 3227465) B3227465
theorem B2872219 : Blo 1132632 2872219 := bstep (se 1 (by rfl) ⟨2154164, by rfl⟩ : syracuseStep 2872219 = 4308329) B4308329
theorem B1135515 : Blo 1132632 1135515 := bstep (se 1 (by rfl) ⟨851636, by rfl⟩ : syracuseStep 1135515 = 1703273) B1703273
theorem B1135567 : Blo 1132632 1135567 := bstep (se 1 (by rfl) ⟨851675, by rfl⟩ : syracuseStep 1135567 = 1703351) B1703351
theorem B4838363 : Blo 1132632 4838363 := bstep (se 1 (by rfl) ⟨3628772, by rfl⟩ : syracuseStep 4838363 = 7257545) B7257545
theorem B1135591 : Blo 1132632 1135591 := bstep (se 1 (by rfl) ⟨851693, by rfl⟩ : syracuseStep 1135591 = 1703387) B1703387
theorem B3232865 : Blo 1132632 3232865 := bstep (se 2 (by rfl) ⟨1212324, by rfl⟩ : syracuseStep 3232865 = 2424649) B2424649
theorem B9819281 : Blo 1132632 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B4904135 : Blo 1132632 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B10343639 : Blo 1132632 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B1135903 : Blo 1132632 1135903 := bstep (se 1 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 1135903 = 1703855) B1703855
theorem B1135963 : Blo 1132632 1135963 := bstep (se 1 (by rfl) ⟨851972, by rfl⟩ : syracuseStep 1135963 = 1703945) B1703945
theorem B5461343 : Blo 1132632 5461343 := bstep (se 1 (by rfl) ⟨4096007, by rfl⟩ : syracuseStep 5461343 = 8192015) B8192015
theorem B1135983 : Blo 1132632 1135983 := bstep (se 1 (by rfl) ⟨851987, by rfl⟩ : syracuseStep 1135983 = 1703975) B1703975
theorem B4150651 : Blo 1132632 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B1136039 : Blo 1132632 1136039 := bstep (se 1 (by rfl) ⟨852029, by rfl⟩ : syracuseStep 1136039 = 1704059) B1704059
theorem B3823037 : Blo 1132632 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B1136123 : Blo 1132632 1136123 := bstep (se 1 (by rfl) ⟨852092, by rfl⟩ : syracuseStep 1136123 = 1704185) B1704185
theorem B1136191 : Blo 1132632 1136191 := bstep (se 1 (by rfl) ⟨852143, by rfl⟩ : syracuseStep 1136191 = 1704287) B1704287
theorem B1136199 : Blo 1132632 1136199 := bstep (se 1 (by rfl) ⟨852149, by rfl⟩ : syracuseStep 1136199 = 1704299) B1704299
theorem B2184787 : Blo 1132632 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B4839047 : Blo 1132632 4839047 := bstep (se 1 (by rfl) ⟨3629285, by rfl⟩ : syracuseStep 4839047 = 7258571) B7258571
theorem B1136351 : Blo 1132632 1136351 := bstep (se 1 (by rfl) ⟨852263, by rfl⟩ : syracuseStep 1136351 = 1704527) B1704527
theorem B1136431 : Blo 1132632 1136431 := bstep (se 1 (by rfl) ⟨852323, by rfl⟩ : syracuseStep 1136431 = 1704647) B1704647
theorem B3823415 : Blo 1132632 3823415 := bstep (se 1 (by rfl) ⟨2867561, by rfl⟩ : syracuseStep 3823415 = 5735123) B5735123
theorem B1136539 : Blo 1132632 1136539 := bstep (se 1 (by rfl) ⟨852404, by rfl⟩ : syracuseStep 1136539 = 1704809) B1704809
theorem B1136591 : Blo 1132632 1136591 := bstep (se 1 (by rfl) ⟨852443, by rfl⟩ : syracuseStep 1136591 = 1704887) B1704887
theorem B1136615 : Blo 1132632 1136615 := bstep (se 1 (by rfl) ⟨852461, by rfl⟩ : syracuseStep 1136615 = 1704923) B1704923
theorem B2873353 : Blo 1132632 2873353 := bstep (se 2 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 2873353 = 2155015) B2155015
theorem B3823901 : Blo 1132632 3823901 := bstep (se 3 (by rfl) ⟨716981, by rfl⟩ : syracuseStep 3823901 = 1433963) B1433963
theorem B6544271 : Blo 1132632 6544271 := bstep (se 1 (by rfl) ⟨4908203, by rfl⟩ : syracuseStep 6544271 = 9816407) B9816407
theorem B10345391 : Blo 1132632 10345391 := bstep (se 1 (by rfl) ⟨7759043, by rfl⟩ : syracuseStep 10345391 = 15518087) B15518087
theorem B3824927 : Blo 1132632 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B4840823 : Blo 1132632 4840823 := bstep (se 1 (by rfl) ⟨3630617, by rfl⟩ : syracuseStep 4840823 = 7261235) B7261235
theorem B2874761 : Blo 1132632 2874761 := bstep (se 2 (by rfl) ⟨1078035, by rfl⟩ : syracuseStep 2874761 = 2156071) B2156071
theorem B24894863 : Blo 1132632 24894863 := bstep (se 1 (by rfl) ⟨18671147, by rfl⟩ : syracuseStep 24894863 = 37342295) B37342295
theorem B2874811 : Blo 1132632 2874811 := bstep (se 1 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 2874811 = 4312217) B4312217
theorem B9690839 : Blo 1132632 9690839 := bstep (se 1 (by rfl) ⟨7268129, by rfl⟩ : syracuseStep 9690839 = 14536259) B14536259
theorem B2875115 : Blo 1132632 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B2154863 : Blo 1132632 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B4088339 : Blo 1132632 4088339 := bstep (se 1 (by rfl) ⟨3066254, by rfl⟩ : syracuseStep 4088339 = 6132509) B6132509
theorem B4842155 : Blo 1132632 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B1434287 : Blo 1132632 1434287 := bstep (se 1 (by rfl) ⟨1075715, by rfl⟩ : syracuseStep 1434287 = 2151431) B2151431
theorem B2876087 : Blo 1132632 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B5530463 : Blo 1132632 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2548727 : Blo 1132632 2548727 := bstep (se 1 (by rfl) ⟨1911545, by rfl⟩ : syracuseStep 2548727 = 3823091) B3823091
theorem B2549087 : Blo 1132632 2549087 := bstep (se 1 (by rfl) ⟨1911815, by rfl⟩ : syracuseStep 2549087 = 3823631) B3823631
theorem B1434991 : Blo 1132632 1434991 := bstep (se 1 (by rfl) ⟨1076243, by rfl⟩ : syracuseStep 1434991 = 2152487) B2152487
theorem B3827357 : Blo 1132632 3827357 := bstep (se 3 (by rfl) ⟨717629, by rfl⟩ : syracuseStep 3827357 = 1435259) B1435259
theorem B2549483 : Blo 1132632 2549483 := bstep (se 1 (by rfl) ⟨1912112, by rfl⟩ : syracuseStep 2549483 = 3824225) B3824225
theorem B19654433 : Blo 1132632 19654433 := bstep (se 2 (by rfl) ⟨7370412, by rfl⟩ : syracuseStep 19654433 = 14740825) B14740825
theorem B2549609 : Blo 1132632 2549609 := bstep (se 2 (by rfl) ⟨956103, by rfl⟩ : syracuseStep 2549609 = 1912207) B1912207
theorem B16345273 : Blo 1132632 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B3827897 : Blo 1132632 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B1436231 : Blo 1132632 1436231 := bstep (se 1 (by rfl) ⟨1077173, by rfl⟩ : syracuseStep 1436231 = 2154347) B2154347
theorem B2550455 : Blo 1132632 2550455 := bstep (se 1 (by rfl) ⟨1912841, by rfl⟩ : syracuseStep 2550455 = 3825683) B3825683
theorem B1436383 : Blo 1132632 1436383 := bstep (se 1 (by rfl) ⟨1077287, by rfl⟩ : syracuseStep 1436383 = 2154575) B2154575
theorem B2550671 : Blo 1132632 2550671 := bstep (se 1 (by rfl) ⟨1913003, by rfl⟩ : syracuseStep 2550671 = 3826007) B3826007
theorem B3632015 : Blo 1132632 3632015 := bstep (se 1 (by rfl) ⟨2724011, by rfl⟩ : syracuseStep 3632015 = 5448023) B5448023
theorem B2419703 : Blo 1132632 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B1699049 : Blo 1132632 1699049 := bstep (se 2 (by rfl) ⟨637143, by rfl⟩ : syracuseStep 1699049 = 1274287) B1274287
theorem B1699103 : Blo 1132632 1699103 := bstep (se 1 (by rfl) ⟨1274327, by rfl⟩ : syracuseStep 1699103 = 2548655) B2548655
theorem B10349855 : Blo 1132632 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B2420155 : Blo 1132632 2420155 := bstep (se 1 (by rfl) ⟨1815116, by rfl⟩ : syracuseStep 2420155 = 3630233) B3630233
theorem B4091323 : Blo 1132632 4091323 := bstep (se 1 (by rfl) ⟨3068492, by rfl⟩ : syracuseStep 4091323 = 6136985) B6136985
theorem B1699271 : Blo 1132632 1699271 := bstep (se 1 (by rfl) ⟨1274453, by rfl⟩ : syracuseStep 1699271 = 2548907) B2548907
theorem B6909383 : Blo 1132632 6909383 := bstep (se 1 (by rfl) ⟨5182037, by rfl⟩ : syracuseStep 6909383 = 10364075) B10364075
theorem B2551391 : Blo 1132632 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B3829409 : Blo 1132632 3829409 := bstep (se 2 (by rfl) ⟨1436028, by rfl⟩ : syracuseStep 3829409 = 2872057) B2872057
theorem B19394315 : Blo 1132632 19394315 := bstep (se 1 (by rfl) ⟨14545736, by rfl⟩ : syracuseStep 19394315 = 29091473) B29091473
theorem B1699625 : Blo 1132632 1699625 := bstep (se 2 (by rfl) ⟨637359, by rfl⟩ : syracuseStep 1699625 = 1274719) B1274719
theorem B1699631 : Blo 1132632 1699631 := bstep (se 1 (by rfl) ⟨1274723, by rfl⟩ : syracuseStep 1699631 = 2549447) B2549447
theorem B2551607 : Blo 1132632 2551607 := bstep (se 1 (by rfl) ⟨1913705, by rfl⟩ : syracuseStep 2551607 = 3827411) B3827411
theorem B4910977 : Blo 1132632 4910977 := bstep (se 2 (by rfl) ⟨1841616, by rfl⟩ : syracuseStep 4910977 = 3683233) B3683233
theorem B3633257 : Blo 1132632 3633257 := bstep (se 2 (by rfl) ⟨1362471, by rfl⟩ : syracuseStep 3633257 = 2724943) B2724943
theorem B2551913 : Blo 1132632 2551913 := bstep (se 2 (by rfl) ⟨956967, by rfl⟩ : syracuseStep 2551913 = 1913935) B1913935
theorem B1700105 : Blo 1132632 1700105 := bstep (se 2 (by rfl) ⟨637539, by rfl⟩ : syracuseStep 1700105 = 1275079) B1275079
theorem B1700207 : Blo 1132632 1700207 := bstep (se 1 (by rfl) ⟨1275155, by rfl⟩ : syracuseStep 1700207 = 2550311) B2550311
theorem B3830273 : Blo 1132632 3830273 := bstep (se 2 (by rfl) ⟨1436352, by rfl⟩ : syracuseStep 3830273 = 2872705) B2872705
theorem B1274431 : Blo 1132632 1274431 := bstep (se 1 (by rfl) ⟨955823, by rfl⟩ : syracuseStep 1274431 = 1911647) B1911647
theorem B1700423 : Blo 1132632 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B2552399 : Blo 1132632 2552399 := bstep (se 1 (by rfl) ⟨1914299, by rfl⟩ : syracuseStep 2552399 = 3828599) B3828599
theorem B1700459 : Blo 1132632 1700459 := bstep (se 1 (by rfl) ⟨1275344, by rfl⟩ : syracuseStep 1700459 = 2550689) B2550689
theorem B7762553 : Blo 1132632 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B2421419 : Blo 1132632 2421419 := bstep (se 1 (by rfl) ⟨1816064, by rfl⟩ : syracuseStep 2421419 = 3632129) B3632129
theorem B2552543 : Blo 1132632 2552543 := bstep (se 1 (by rfl) ⟨1914407, by rfl⟩ : syracuseStep 2552543 = 3828815) B3828815
theorem B1700687 : Blo 1132632 1700687 := bstep (se 1 (by rfl) ⟨1275515, by rfl⟩ : syracuseStep 1700687 = 2551031) B2551031
theorem B2421659 : Blo 1132632 2421659 := bstep (se 1 (by rfl) ⟨1816244, by rfl⟩ : syracuseStep 2421659 = 3632489) B3632489
theorem B2552795 : Blo 1132632 2552795 := bstep (se 1 (by rfl) ⟨1914596, by rfl⟩ : syracuseStep 2552795 = 3829193) B3829193
theorem B3830759 : Blo 1132632 3830759 := bstep (se 1 (by rfl) ⟨2873069, by rfl⟩ : syracuseStep 3830759 = 5746139) B5746139
theorem B2552975 : Blo 1132632 2552975 := bstep (se 1 (by rfl) ⟨1914731, by rfl⟩ : syracuseStep 2552975 = 3829463) B3829463
theorem B7271639 : Blo 1132632 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B1701083 : Blo 1132632 1701083 := bstep (se 1 (by rfl) ⟨1275812, by rfl⟩ : syracuseStep 1701083 = 2551625) B2551625
theorem B2553065 : Blo 1132632 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B2553119 : Blo 1132632 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B3831083 : Blo 1132632 3831083 := bstep (se 1 (by rfl) ⟨2873312, by rfl⟩ : syracuseStep 3831083 = 5746625) B5746625
theorem B6124895 : Blo 1132632 6124895 := bstep (se 1 (by rfl) ⟨4593671, by rfl⟩ : syracuseStep 6124895 = 9187343) B9187343
theorem B1275259 : Blo 1132632 1275259 := bstep (se 1 (by rfl) ⟨956444, by rfl⟩ : syracuseStep 1275259 = 1912889) B1912889
theorem B1701257 : Blo 1132632 1701257 := bstep (se 2 (by rfl) ⟨637971, by rfl⟩ : syracuseStep 1701257 = 1275943) B1275943
theorem B6452743 : Blo 1132632 6452743 := bstep (se 1 (by rfl) ⟨4839557, by rfl⟩ : syracuseStep 6452743 = 9679115) B9679115
theorem B4847111 : Blo 1132632 4847111 := bstep (se 1 (by rfl) ⟨3635333, by rfl⟩ : syracuseStep 4847111 = 7270667) B7270667
theorem B3831353 : Blo 1132632 3831353 := bstep (se 2 (by rfl) ⟨1436757, by rfl⟩ : syracuseStep 3831353 = 2873515) B2873515
theorem B1701611 : Blo 1132632 1701611 := bstep (se 1 (by rfl) ⟨1276208, by rfl⟩ : syracuseStep 1701611 = 2552417) B2552417
theorem B2553641 : Blo 1132632 2553641 := bstep (se 2 (by rfl) ⟨957615, by rfl⟩ : syracuseStep 2553641 = 1915231) B1915231
theorem B1275727 : Blo 1132632 1275727 := bstep (se 1 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 1275727 = 1913591) B1913591
theorem B1701839 : Blo 1132632 1701839 := bstep (se 1 (by rfl) ⟨1276379, by rfl⟩ : syracuseStep 1701839 = 2552759) B2552759
theorem B2422889 : Blo 1132632 2422889 := bstep (se 2 (by rfl) ⟨908583, by rfl⟩ : syracuseStep 2422889 = 1817167) B1817167
theorem B1276123 : Blo 1132632 1276123 := bstep (se 1 (by rfl) ⟨957092, by rfl⟩ : syracuseStep 1276123 = 1914185) B1914185
theorem B1702235 : Blo 1132632 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B1276411 : Blo 1132632 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B1702463 : Blo 1132632 1702463 := bstep (se 1 (by rfl) ⟨1276847, by rfl⟩ : syracuseStep 1702463 = 2553695) B2553695
theorem B1276591 : Blo 1132632 1276591 := bstep (se 1 (by rfl) ⟨957443, by rfl⟩ : syracuseStep 1276591 = 1914887) B1914887
theorem B1702583 : Blo 1132632 1702583 := bstep (se 1 (by rfl) ⟨1276937, by rfl⟩ : syracuseStep 1702583 = 2553875) B2553875
theorem B3832595 : Blo 1132632 3832595 := bstep (se 1 (by rfl) ⟨2874446, by rfl⟩ : syracuseStep 3832595 = 5748893) B5748893
theorem B2554703 : Blo 1132632 2554703 := bstep (se 1 (by rfl) ⟨1916027, by rfl⟩ : syracuseStep 2554703 = 3832055) B3832055
theorem B1702811 : Blo 1132632 1702811 := bstep (se 1 (by rfl) ⟨1277108, by rfl⟩ : syracuseStep 1702811 = 2554217) B2554217
theorem B1276879 : Blo 1132632 1276879 := bstep (se 1 (by rfl) ⟨957659, by rfl⟩ : syracuseStep 1276879 = 1915319) B1915319
theorem B2554919 : Blo 1132632 2554919 := bstep (se 1 (by rfl) ⟨1916189, by rfl⟩ : syracuseStep 2554919 = 3832379) B3832379
theorem B2915471 : Blo 1132632 2915471 := bstep (se 1 (by rfl) ⟨2186603, by rfl⟩ : syracuseStep 2915471 = 4373207) B4373207
theorem B2555099 : Blo 1132632 2555099 := bstep (se 1 (by rfl) ⟨1916324, by rfl⟩ : syracuseStep 2555099 = 3832649) B3832649
theorem B9698525 : Blo 1132632 9698525 := bstep (se 3 (by rfl) ⟨1818473, by rfl⟩ : syracuseStep 9698525 = 3636947) B3636947
theorem B1703207 : Blo 1132632 1703207 := bstep (se 1 (by rfl) ⟨1277405, by rfl⟩ : syracuseStep 1703207 = 2554811) B2554811
theorem B1277275 : Blo 1132632 1277275 := bstep (se 1 (by rfl) ⟨957956, by rfl⟩ : syracuseStep 1277275 = 1915913) B1915913
theorem B1703291 : Blo 1132632 1703291 := bstep (se 1 (by rfl) ⟨1277468, by rfl⟩ : syracuseStep 1703291 = 2554937) B2554937
theorem B2555297 : Blo 1132632 2555297 := bstep (se 2 (by rfl) ⟨958236, by rfl⟩ : syracuseStep 2555297 = 1916473) B1916473
theorem B1277383 : Blo 1132632 1277383 := bstep (se 1 (by rfl) ⟨958037, by rfl⟩ : syracuseStep 1277383 = 1916075) B1916075
theorem B4095431 : Blo 1132632 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B1703417 : Blo 1132632 1703417 := bstep (se 2 (by rfl) ⟨638781, by rfl⟩ : syracuseStep 1703417 = 1277563) B1277563
theorem B4849247 : Blo 1132632 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B9207391 : Blo 1132632 9207391 := bstep (se 1 (by rfl) ⟨6905543, by rfl⟩ : syracuseStep 9207391 = 13811087) B13811087
theorem B1703519 : Blo 1132632 1703519 := bstep (se 1 (by rfl) ⟨1277639, by rfl⟩ : syracuseStep 1703519 = 2555279) B2555279
theorem B7274099 : Blo 1132632 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B3833459 : Blo 1132632 3833459 := bstep (se 1 (by rfl) ⟨2875094, by rfl⟩ : syracuseStep 3833459 = 5750189) B5750189
theorem B5734151 : Blo 1132632 5734151 := bstep (se 1 (by rfl) ⟨4300613, by rfl⟩ : syracuseStep 5734151 = 8601227) B8601227
theorem B1277743 : Blo 1132632 1277743 := bstep (se 1 (by rfl) ⟨958307, by rfl⟩ : syracuseStep 1277743 = 1916615) B1916615
theorem B1703735 : Blo 1132632 1703735 := bstep (se 1 (by rfl) ⟨1277801, by rfl⟩ : syracuseStep 1703735 = 2555603) B2555603
theorem B4849469 : Blo 1132632 4849469 := bstep (se 3 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 4849469 = 1818551) B1818551
theorem B3833729 : Blo 1132632 3833729 := bstep (se 2 (by rfl) ⟨1437648, by rfl⟩ : syracuseStep 3833729 = 2875297) B2875297
theorem B1277851 : Blo 1132632 1277851 := bstep (se 1 (by rfl) ⟨958388, by rfl⟩ : syracuseStep 1277851 = 1916777) B1916777
theorem B2555855 : Blo 1132632 2555855 := bstep (se 1 (by rfl) ⟨1916891, by rfl⟩ : syracuseStep 2555855 = 3833783) B3833783
theorem B14549017 : Blo 1132632 14549017 := bstep (se 2 (by rfl) ⟨5455881, by rfl⟩ : syracuseStep 14549017 = 10911763) B10911763
theorem B1704155 : Blo 1132632 1704155 := bstep (se 1 (by rfl) ⟨1278116, by rfl⟩ : syracuseStep 1704155 = 2556233) B2556233
theorem B1704167 : Blo 1132632 1704167 := bstep (se 1 (by rfl) ⟨1278125, by rfl⟩ : syracuseStep 1704167 = 2556251) B2556251
theorem B6455659 : Blo 1132632 6455659 := bstep (se 1 (by rfl) ⟨4841744, by rfl⟩ : syracuseStep 6455659 = 9683489) B9683489
theorem B1704329 : Blo 1132632 1704329 := bstep (se 2 (by rfl) ⟨639123, by rfl⟩ : syracuseStep 1704329 = 1278247) B1278247
theorem B2556359 : Blo 1132632 2556359 := bstep (se 1 (by rfl) ⟨1917269, by rfl⟩ : syracuseStep 2556359 = 3834539) B3834539
theorem B1704425 : Blo 1132632 1704425 := bstep (se 2 (by rfl) ⟨639159, by rfl⟩ : syracuseStep 1704425 = 1278319) B1278319
theorem B3834431 : Blo 1132632 3834431 := bstep (se 1 (by rfl) ⟨2875823, by rfl⟩ : syracuseStep 3834431 = 5751647) B5751647
theorem B1704551 : Blo 1132632 1704551 := bstep (se 1 (by rfl) ⟨1278413, by rfl⟩ : syracuseStep 1704551 = 2556827) B2556827
theorem B1704683 : Blo 1132632 1704683 := bstep (se 1 (by rfl) ⟨1278512, by rfl⟩ : syracuseStep 1704683 = 2557025) B2557025
theorem B1704713 : Blo 1132632 1704713 := bstep (se 2 (by rfl) ⟨639267, by rfl⟩ : syracuseStep 1704713 = 1278535) B1278535
theorem B2556719 : Blo 1132632 2556719 := bstep (se 1 (by rfl) ⟨1917539, by rfl⟩ : syracuseStep 2556719 = 3835079) B3835079
theorem B1704815 : Blo 1132632 1704815 := bstep (se 1 (by rfl) ⟨1278611, by rfl⟩ : syracuseStep 1704815 = 2557223) B2557223
theorem B5735933 : Blo 1132632 5735933 := bstep (se 3 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 5735933 = 2150975) B2150975
theorem B6457117 : Blo 1132632 6457117 := bstep (se 3 (by rfl) ⟨1210709, by rfl⟩ : syracuseStep 6457117 = 2421419) B2421419
theorem B5244751 : Blo 1132632 5244751 := bstep (se 1 (by rfl) ⟨3933563, by rfl⟩ : syracuseStep 5244751 = 7867127) B7867127
theorem B3835727 : Blo 1132632 3835727 := bstep (se 1 (by rfl) ⟨2876795, by rfl⟩ : syracuseStep 3835727 = 5753591) B5753591
theorem B3639305 : Blo 1132632 3639305 := bstep (se 2 (by rfl) ⟨1364739, by rfl⟩ : syracuseStep 3639305 = 2729479) B2729479
theorem B46598273 : Blo 1132632 46598273 := bstep (se 2 (by rfl) ⟨17474352, by rfl⟩ : syracuseStep 46598273 = 34948705) B34948705
theorem B3836051 : Blo 1132632 3836051 := bstep (se 1 (by rfl) ⟨2877038, by rfl⟩ : syracuseStep 3836051 = 5754077) B5754077
theorem B5736743 : Blo 1132632 5736743 := bstep (se 1 (by rfl) ⟨4302557, by rfl⟩ : syracuseStep 5736743 = 8605115) B8605115
theorem B5736905 : Blo 1132632 5736905 := bstep (se 2 (by rfl) ⟨2151339, by rfl⟩ : syracuseStep 5736905 = 4302679) B4302679
theorem B4852169 : Blo 1132632 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B41388565 : Blo 1132632 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B21793697 : Blo 1132632 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B5737715 : Blo 1132632 5737715 := bstep (se 1 (by rfl) ⟨4303286, by rfl⟩ : syracuseStep 5737715 = 8606573) B8606573
theorem B3640895 : Blo 1132632 3640895 := bstep (se 1 (by rfl) ⟨2730671, by rfl⟩ : syracuseStep 3640895 = 5461343) B5461343
theorem B7278457 : Blo 1132632 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B1273466933 : Blo 1132632 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B4853945 : Blo 1132632 4853945 := bstep (se 2 (by rfl) ⟨1820229, by rfl⟩ : syracuseStep 4853945 = 3640459) B3640459
theorem B15733369 : Blo 1132632 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B6460559 : Blo 1132632 6460559 := bstep (se 1 (by rfl) ⟨4845419, by rfl⟩ : syracuseStep 6460559 = 9690839) B9690839
theorem B2725559 : Blo 1132632 2725559 := bstep (se 1 (by rfl) ⟨2044169, by rfl⟩ : syracuseStep 2725559 = 4088339) B4088339
theorem B32708771 : Blo 1132632 32708771 := bstep (se 1 (by rfl) ⟨24531578, by rfl⟩ : syracuseStep 32708771 = 49063157) B49063157
theorem B12917879 : Blo 1132632 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B1613135 : Blo 1132632 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B2301767 : Blo 1132632 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B20488157 : Blo 1132632 20488157 := bstep (se 3 (by rfl) ⟨3841529, by rfl⟩ : syracuseStep 20488157 = 7683059) B7683059
theorem B7774589 : Blo 1132632 7774589 := bstep (se 3 (by rfl) ⟨1457735, by rfl⟩ : syracuseStep 7774589 = 2915471) B2915471
theorem B1614439 : Blo 1132632 1614439 := bstep (se 1 (by rfl) ⟨1210829, by rfl⟩ : syracuseStep 1614439 = 2421659) B2421659
theorem B1615259 : Blo 1132632 1615259 := bstep (se 1 (by rfl) ⟨1211444, by rfl⟩ : syracuseStep 1615259 = 2422889) B2422889
theorem B6465683 : Blo 1132632 6465683 := bstep (se 1 (by rfl) ⟨4849262, by rfl⟩ : syracuseStep 6465683 = 9698525) B9698525
theorem B2730287 : Blo 1132632 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B1911323 : Blo 1132632 1911323 := bstep (se 1 (by rfl) ⟨1433492, by rfl⟩ : syracuseStep 1911323 = 2866985) B2866985
theorem B23276483 : Blo 1132632 23276483 := bstep (se 1 (by rfl) ⟨17457362, by rfl⟩ : syracuseStep 23276483 = 34914725) B34914725
theorem B1911991 : Blo 1132632 1911991 := bstep (se 1 (by rfl) ⟨1433993, by rfl⟩ : syracuseStep 1911991 = 2867987) B2867987
theorem B2043103 : Blo 1132632 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B1912295 : Blo 1132632 1912295 := bstep (se 1 (by rfl) ⟨1434221, by rfl⟩ : syracuseStep 1912295 = 2868443) B2868443
theorem B1912315 : Blo 1132632 1912315 := bstep (se 1 (by rfl) ⟨1434236, by rfl⟩ : syracuseStep 1912315 = 2868473) B2868473
theorem B4304441 : Blo 1132632 4304441 := bstep (se 2 (by rfl) ⟨1614165, by rfl⟩ : syracuseStep 4304441 = 3228331) B3228331
theorem B5746301 : Blo 1132632 5746301 := bstep (se 3 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 5746301 = 2154863) B2154863
theorem B1617583 : Blo 1132632 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B39268253 : Blo 1132632 39268253 := bstep (se 3 (by rfl) ⟨7362797, by rfl⟩ : syracuseStep 39268253 = 14725595) B14725595
theorem B1912747 : Blo 1132632 1912747 := bstep (se 1 (by rfl) ⟨1434560, by rfl⟩ : syracuseStep 1912747 = 2869121) B2869121
theorem B1913051 : Blo 1132632 1913051 := bstep (se 1 (by rfl) ⟨1434788, by rfl⟩ : syracuseStep 1913051 = 2869577) B2869577
theorem B6467849 : Blo 1132632 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B5747111 : Blo 1132632 5747111 := bstep (se 1 (by rfl) ⟨4310333, by rfl⟩ : syracuseStep 5747111 = 8620667) B8620667
theorem B1913287 : Blo 1132632 1913287 := bstep (se 1 (by rfl) ⟨1434965, by rfl⟩ : syracuseStep 1913287 = 2869931) B2869931
theorem B1913321 : Blo 1132632 1913321 := bstep (se 2 (by rfl) ⟨717495, by rfl⟩ : syracuseStep 1913321 = 1434991) B1434991
theorem B4600583 : Blo 1132632 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B29078351 : Blo 1132632 29078351 := bstep (se 1 (by rfl) ⟨21808763, by rfl⟩ : syracuseStep 29078351 = 43617527) B43617527
theorem B1815463 : Blo 1132632 1815463 := bstep (se 1 (by rfl) ⟨1361597, by rfl⟩ : syracuseStep 1815463 = 2723195) B2723195
theorem B14562503 : Blo 1132632 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B32683621 : Blo 1132632 32683621 := bstep (se 4 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 32683621 = 6128179) B6128179
theorem B5748407 : Blo 1132632 5748407 := bstep (se 1 (by rfl) ⟨4311305, by rfl⟩ : syracuseStep 5748407 = 8622611) B8622611
theorem B1816283 : Blo 1132632 1816283 := bstep (se 1 (by rfl) ⟨1362212, by rfl⟩ : syracuseStep 1816283 = 2724425) B2724425
theorem B29472605 : Blo 1132632 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B3225575 : Blo 1132632 3225575 := bstep (se 1 (by rfl) ⟨2419181, by rfl⟩ : syracuseStep 3225575 = 4838363) B4838363
theorem B1915177 : Blo 1132632 1915177 := bstep (se 2 (by rfl) ⟨718191, by rfl⟩ : syracuseStep 1915177 = 1436383) B1436383
theorem B3226031 : Blo 1132632 3226031 := bstep (se 1 (by rfl) ⟨2419523, by rfl⟩ : syracuseStep 3226031 = 4839047) B4839047
theorem B9682091 : Blo 1132632 9682091 := bstep (se 1 (by rfl) ⟨7261568, by rfl⟩ : syracuseStep 9682091 = 14523137) B14523137
theorem B3226873 : Blo 1132632 3226873 := bstep (se 2 (by rfl) ⟨1210077, by rfl⟩ : syracuseStep 3226873 = 2420155) B2420155
theorem B5455097 : Blo 1132632 5455097 := bstep (se 2 (by rfl) ⟨2045661, by rfl⟩ : syracuseStep 5455097 = 4091323) B4091323
theorem B6896927 : Blo 1132632 6896927 := bstep (se 1 (by rfl) ⟨5172695, by rfl⟩ : syracuseStep 6896927 = 10345391) B10345391
theorem B8174945 : Blo 1132632 8174945 := bstep (se 2 (by rfl) ⟨3065604, by rfl⟩ : syracuseStep 8174945 = 6131209) B6131209
theorem B3227215 : Blo 1132632 3227215 := bstep (se 1 (by rfl) ⟨2420411, by rfl⟩ : syracuseStep 3227215 = 4840823) B4840823
theorem B1916507 : Blo 1132632 1916507 := bstep (se 1 (by rfl) ⟨1437380, by rfl⟩ : syracuseStep 1916507 = 2874761) B2874761
theorem B16596575 : Blo 1132632 16596575 := bstep (se 1 (by rfl) ⟨12447431, by rfl⟩ : syracuseStep 16596575 = 24894863) B24894863
theorem B2867015 : Blo 1132632 2867015 := bstep (se 1 (by rfl) ⟨2150261, by rfl⟩ : syracuseStep 2867015 = 4300523) B4300523
theorem B1916743 : Blo 1132632 1916743 := bstep (se 1 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 1916743 = 2875115) B2875115
theorem B2867339 : Blo 1132632 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B3228103 : Blo 1132632 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B2867663 : Blo 1132632 2867663 := bstep (se 1 (by rfl) ⟨2150747, by rfl⟩ : syracuseStep 2867663 = 4301495) B4301495
theorem B1917391 : Blo 1132632 1917391 := bstep (se 1 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 1917391 = 2876087) B2876087
theorem B3686975 : Blo 1132632 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B1360891 : Blo 1132632 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B23250199 : Blo 1132632 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B2868655 : Blo 1132632 2868655 := bstep (se 1 (by rfl) ⟨2151491, by rfl⟩ : syracuseStep 2868655 = 4302983) B4302983
theorem B8177111 : Blo 1132632 8177111 := bstep (se 1 (by rfl) ⟨6132833, by rfl⟩ : syracuseStep 8177111 = 12265667) B12265667
theorem B7259645 : Blo 1132632 7259645 := bstep (se 3 (by rfl) ⟨1361183, by rfl⟩ : syracuseStep 7259645 = 2722367) B2722367
theorem B2868959 : Blo 1132632 2868959 := bstep (se 1 (by rfl) ⟨2151719, by rfl⟩ : syracuseStep 2868959 = 4303439) B4303439
theorem B8603657 : Blo 1132632 8603657 := bstep (se 2 (by rfl) ⟨3226371, by rfl⟩ : syracuseStep 8603657 = 6452743) B6452743
theorem B1132699 : Blo 1132632 1132699 := bstep (se 1 (by rfl) ⟨849524, by rfl⟩ : syracuseStep 1132699 = 1699049) B1699049
theorem B1132735 : Blo 1132632 1132735 := bstep (se 1 (by rfl) ⟨849551, by rfl⟩ : syracuseStep 1132735 = 1699103) B1699103
theorem B6899903 : Blo 1132632 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B1132847 : Blo 1132632 1132847 := bstep (se 1 (by rfl) ⟨849635, by rfl⟩ : syracuseStep 1132847 = 1699271) B1699271
theorem B4606255 : Blo 1132632 4606255 := bstep (se 1 (by rfl) ⟨3454691, by rfl⟩ : syracuseStep 4606255 = 6909383) B6909383
theorem B17451389 : Blo 1132632 17451389 := bstep (se 3 (by rfl) ⟨3272135, by rfl⟩ : syracuseStep 17451389 = 6544271) B6544271
theorem B12929543 : Blo 1132632 12929543 := bstep (se 1 (by rfl) ⟨9697157, by rfl⟩ : syracuseStep 12929543 = 19394315) B19394315
theorem B1133083 : Blo 1132632 1133083 := bstep (se 1 (by rfl) ⟨849812, by rfl⟩ : syracuseStep 1133083 = 1699625) B1699625
theorem B1133087 : Blo 1132632 1133087 := bstep (se 1 (by rfl) ⟨849815, by rfl⟩ : syracuseStep 1133087 = 1699631) B1699631
theorem B1133403 : Blo 1132632 1133403 := bstep (se 1 (by rfl) ⟨850052, by rfl⟩ : syracuseStep 1133403 = 1700105) B1700105
theorem B1133471 : Blo 1132632 1133471 := bstep (se 1 (by rfl) ⟨850103, by rfl⟩ : syracuseStep 1133471 = 1700207) B1700207
theorem B1133615 : Blo 1132632 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B1133639 : Blo 1132632 1133639 := bstep (se 1 (by rfl) ⟨850229, by rfl⟩ : syracuseStep 1133639 = 1700459) B1700459
theorem B1133791 : Blo 1132632 1133791 := bstep (se 1 (by rfl) ⟨850343, by rfl⟩ : syracuseStep 1133791 = 1700687) B1700687
theorem B1363279 : Blo 1132632 1363279 := bstep (se 1 (by rfl) ⟨1022459, by rfl⟩ : syracuseStep 1363279 = 2044919) B2044919
theorem B4312399 : Blo 1132632 4312399 := bstep (se 1 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 4312399 = 6468599) B6468599
theorem B2870711 : Blo 1132632 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B1134055 : Blo 1132632 1134055 := bstep (se 1 (by rfl) ⟨850541, by rfl⟩ : syracuseStep 1134055 = 1701083) B1701083
theorem B4083263 : Blo 1132632 4083263 := bstep (se 1 (by rfl) ⟨3062447, by rfl⟩ : syracuseStep 4083263 = 6124895) B6124895
theorem B3067465 : Blo 1132632 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B1134171 : Blo 1132632 1134171 := bstep (se 1 (by rfl) ⟨850628, by rfl⟩ : syracuseStep 1134171 = 1701257) B1701257
theorem B16371335 : Blo 1132632 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B3231407 : Blo 1132632 3231407 := bstep (se 1 (by rfl) ⟨2423555, by rfl⟩ : syracuseStep 3231407 = 4847111) B4847111
theorem B4312871 : Blo 1132632 4312871 := bstep (se 1 (by rfl) ⟨3234653, by rfl⟩ : syracuseStep 4312871 = 6469307) B6469307
theorem B1134407 : Blo 1132632 1134407 := bstep (se 1 (by rfl) ⟨850805, by rfl⟩ : syracuseStep 1134407 = 1701611) B1701611
theorem B17452921 : Blo 1132632 17452921 := bstep (se 2 (by rfl) ⟨6544845, by rfl⟩ : syracuseStep 17452921 = 13089691) B13089691
theorem B1134559 : Blo 1132632 1134559 := bstep (se 1 (by rfl) ⟨850919, by rfl⟩ : syracuseStep 1134559 = 1701839) B1701839
theorem B1134823 : Blo 1132632 1134823 := bstep (se 1 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 1134823 = 1702235) B1702235
theorem B1134975 : Blo 1132632 1134975 := bstep (se 1 (by rfl) ⟨851231, by rfl⟩ : syracuseStep 1134975 = 1702463) B1702463
theorem B1135055 : Blo 1132632 1135055 := bstep (se 1 (by rfl) ⟨851291, by rfl⟩ : syracuseStep 1135055 = 1702583) B1702583
theorem B1135207 : Blo 1132632 1135207 := bstep (se 1 (by rfl) ⟨851405, by rfl⟩ : syracuseStep 1135207 = 1702811) B1702811
theorem B12276521 : Blo 1132632 12276521 := bstep (se 2 (by rfl) ⟨4603695, by rfl⟩ : syracuseStep 12276521 = 9207391) B9207391
theorem B1135471 : Blo 1132632 1135471 := bstep (se 1 (by rfl) ⟨851603, by rfl⟩ : syracuseStep 1135471 = 1703207) B1703207
theorem B1135527 : Blo 1132632 1135527 := bstep (se 1 (by rfl) ⟨851645, by rfl⟩ : syracuseStep 1135527 = 1703291) B1703291
theorem B1135611 : Blo 1132632 1135611 := bstep (se 1 (by rfl) ⟨851708, by rfl⟩ : syracuseStep 1135611 = 1703417) B1703417
theorem B3232831 : Blo 1132632 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B1135679 : Blo 1132632 1135679 := bstep (se 1 (by rfl) ⟨851759, by rfl⟩ : syracuseStep 1135679 = 1703519) B1703519
theorem B3822767 : Blo 1132632 3822767 := bstep (se 1 (by rfl) ⟨2867075, by rfl⟩ : syracuseStep 3822767 = 5734151) B5734151
theorem B1135823 : Blo 1132632 1135823 := bstep (se 1 (by rfl) ⟨851867, by rfl⟩ : syracuseStep 1135823 = 1703735) B1703735
theorem B3232979 : Blo 1132632 3232979 := bstep (se 1 (by rfl) ⟨2424734, by rfl⟩ : syracuseStep 3232979 = 4849469) B4849469
theorem B1725851 : Blo 1132632 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B1136027 : Blo 1132632 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B5461613 : Blo 1132632 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B1136239 : Blo 1132632 1136239 := bstep (se 1 (by rfl) ⟨852179, by rfl⟩ : syracuseStep 1136239 = 1704359) B1704359
theorem B1136295 : Blo 1132632 1136295 := bstep (se 1 (by rfl) ⟨852221, by rfl⟩ : syracuseStep 1136295 = 1704443) B1704443
theorem B1136379 : Blo 1132632 1136379 := bstep (se 1 (by rfl) ⟨852284, by rfl⟩ : syracuseStep 1136379 = 1704569) B1704569
theorem B1136415 : Blo 1132632 1136415 := bstep (se 1 (by rfl) ⟨852311, by rfl⟩ : syracuseStep 1136415 = 1704623) B1704623
theorem B1136447 : Blo 1132632 1136447 := bstep (se 1 (by rfl) ⟨852335, by rfl⟩ : syracuseStep 1136447 = 1704671) B1704671
theorem B2873303 : Blo 1132632 2873303 := bstep (se 1 (by rfl) ⟨2154977, by rfl⟩ : syracuseStep 2873303 = 4309955) B4309955
theorem B1136623 : Blo 1132632 1136623 := bstep (se 1 (by rfl) ⟨852467, by rfl⟩ : syracuseStep 1136623 = 1704935) B1704935
theorem B3233935 : Blo 1132632 3233935 := bstep (se 1 (by rfl) ⟨2425451, by rfl⟩ : syracuseStep 3233935 = 4850903) B4850903
theorem B3234323 : Blo 1132632 3234323 := bstep (se 1 (by rfl) ⟨2425742, by rfl⟩ : syracuseStep 3234323 = 4851485) B4851485
theorem B4086607 : Blo 1132632 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B2153299 : Blo 1132632 2153299 := bstep (se 1 (by rfl) ⟨1614974, by rfl⟩ : syracuseStep 2153299 = 3229949) B3229949
theorem B2153375 : Blo 1132632 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B3824711 : Blo 1132632 3824711 := bstep (se 1 (by rfl) ⟨2868533, by rfl⟩ : syracuseStep 3824711 = 5737067) B5737067
theorem B3824765 : Blo 1132632 3824765 := bstep (se 3 (by rfl) ⟨717143, by rfl⟩ : syracuseStep 3824765 = 1434287) B1434287
theorem B55893341 : Blo 1132632 55893341 := bstep (se 3 (by rfl) ⟨10480001, by rfl⟩ : syracuseStep 55893341 = 20960003) B20960003
theorem B3825035 : Blo 1132632 3825035 := bstep (se 1 (by rfl) ⟨2868776, by rfl⟩ : syracuseStep 3825035 = 5737553) B5737553
theorem B3235211 : Blo 1132632 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B2874791 : Blo 1132632 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B2154127 : Blo 1132632 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B19652827 : Blo 1132632 19652827 := bstep (se 1 (by rfl) ⟨14739620, by rfl⟩ : syracuseStep 19652827 = 29479241) B29479241
theorem B31023485 : Blo 1132632 31023485 := bstep (se 3 (by rfl) ⟨5816903, by rfl⟩ : syracuseStep 31023485 = 11633807) B11633807
theorem B27583037 : Blo 1132632 27583037 := bstep (se 3 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 27583037 = 10343639) B10343639
theorem B2155243 : Blo 1132632 2155243 := bstep (se 1 (by rfl) ⟨1616432, by rfl⟩ : syracuseStep 2155243 = 3232865) B3232865
theorem B6546187 : Blo 1132632 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B3269423 : Blo 1132632 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B2548691 : Blo 1132632 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B447046721 : Blo 1132632 447046721 := bstep (se 2 (by rfl) ⟨167642520, by rfl⟩ : syracuseStep 447046721 = 335285041) B335285041
theorem B2548943 : Blo 1132632 2548943 := bstep (se 1 (by rfl) ⟨1911707, by rfl⟩ : syracuseStep 2548943 = 3823415) B3823415
theorem B14542253 : Blo 1132632 14542253 := bstep (se 3 (by rfl) ⟨2726672, by rfl⟩ : syracuseStep 14542253 = 5453345) B5453345
theorem B2549267 : Blo 1132632 2549267 := bstep (se 1 (by rfl) ⟨1911950, by rfl⟩ : syracuseStep 2549267 = 3823901) B3823901
theorem B5531257 : Blo 1132632 5531257 := bstep (se 2 (by rfl) ⟨2074221, by rfl⟩ : syracuseStep 5531257 = 4148443) B4148443
theorem B2549951 : Blo 1132632 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B4090067 : Blo 1132632 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B4090169 : Blo 1132632 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B3828059 : Blo 1132632 3828059 := bstep (se 1 (by rfl) ⟨2871044, by rfl⟩ : syracuseStep 3828059 = 5742089) B5742089
theorem B6547969 : Blo 1132632 6547969 := bstep (se 2 (by rfl) ⟨2455488, by rfl⟩ : syracuseStep 6547969 = 4910977) B4910977
theorem B3828329 : Blo 1132632 3828329 := bstep (se 2 (by rfl) ⟨1435623, by rfl⟩ : syracuseStep 3828329 = 2871247) B2871247
theorem B1534879 : Blo 1132632 1534879 := bstep (se 1 (by rfl) ⟨1151159, by rfl⟩ : syracuseStep 1534879 = 2302319) B2302319
theorem B2550905 : Blo 1132632 2550905 := bstep (se 2 (by rfl) ⟨956589, by rfl⟩ : syracuseStep 2550905 = 1913179) B1913179
theorem B13790351 : Blo 1132632 13790351 := bstep (se 1 (by rfl) ⟨10342763, by rfl⟩ : syracuseStep 13790351 = 20685527) B20685527
theorem B1535159 : Blo 1132632 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B1699151 : Blo 1132632 1699151 := bstep (se 1 (by rfl) ⟨1274363, by rfl⟩ : syracuseStep 1699151 = 2548727) B2548727
theorem B1699241 : Blo 1132632 1699241 := bstep (se 2 (by rfl) ⟨637215, by rfl⟩ : syracuseStep 1699241 = 1274431) B1274431
theorem B1699391 : Blo 1132632 1699391 := bstep (se 1 (by rfl) ⟨1274543, by rfl⟩ : syracuseStep 1699391 = 2549087) B2549087
theorem B3829355 : Blo 1132632 3829355 := bstep (se 1 (by rfl) ⟨2872016, by rfl⟩ : syracuseStep 3829355 = 5744033) B5744033
theorem B2551571 : Blo 1132632 2551571 := bstep (se 1 (by rfl) ⟨1913678, by rfl⟩ : syracuseStep 2551571 = 3827357) B3827357
theorem B1699655 : Blo 1132632 1699655 := bstep (se 1 (by rfl) ⟨1274741, by rfl⟩ : syracuseStep 1699655 = 2549483) B2549483
theorem B13102955 : Blo 1132632 13102955 := bstep (se 1 (by rfl) ⟨9827216, by rfl⟩ : syracuseStep 13102955 = 19654433) B19654433
theorem B3829625 : Blo 1132632 3829625 := bstep (se 2 (by rfl) ⟨1436109, by rfl⟩ : syracuseStep 3829625 = 2872219) B2872219
theorem B1699739 : Blo 1132632 1699739 := bstep (se 1 (by rfl) ⟨1274804, by rfl⟩ : syracuseStep 1699739 = 2549609) B2549609
theorem B5533595 : Blo 1132632 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B3633103 : Blo 1132632 3633103 := bstep (se 1 (by rfl) ⟨2724827, by rfl⟩ : syracuseStep 3633103 = 5449655) B5449655
theorem B2551931 : Blo 1132632 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B3829949 : Blo 1132632 3829949 := bstep (se 3 (by rfl) ⟨718115, by rfl⟩ : syracuseStep 3829949 = 1436231) B1436231
theorem B12415169 : Blo 1132632 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B17494301 : Blo 1132632 17494301 := bstep (se 3 (by rfl) ⟨3280181, by rfl⟩ : syracuseStep 17494301 = 6560363) B6560363
theorem B4092287 : Blo 1132632 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B2552201 : Blo 1132632 2552201 := bstep (se 2 (by rfl) ⟨957075, by rfl⟩ : syracuseStep 2552201 = 1914151) B1914151
theorem B1700303 : Blo 1132632 1700303 := bstep (se 1 (by rfl) ⟨1275227, by rfl⟩ : syracuseStep 1700303 = 2550455) B2550455
theorem B1700345 : Blo 1132632 1700345 := bstep (se 2 (by rfl) ⟨637629, by rfl⟩ : syracuseStep 1700345 = 1275259) B1275259
theorem B5534201 : Blo 1132632 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B1700447 : Blo 1132632 1700447 := bstep (se 1 (by rfl) ⟨1275335, by rfl⟩ : syracuseStep 1700447 = 2550671) B2550671
theorem B2421343 : Blo 1132632 2421343 := bstep (se 1 (by rfl) ⟨1816007, by rfl⟩ : syracuseStep 2421343 = 3632015) B3632015
theorem B12284561 : Blo 1132632 12284561 := bstep (se 2 (by rfl) ⟨4606710, by rfl⟩ : syracuseStep 12284561 = 9213421) B9213421
theorem B2913049 : Blo 1132632 2913049 := bstep (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) B2184787
theorem B1274791 : Blo 1132632 1274791 := bstep (se 1 (by rfl) ⟨956093, by rfl⟩ : syracuseStep 1274791 = 1912187) B1912187
theorem B1700927 : Blo 1132632 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B1700969 : Blo 1132632 1700969 := bstep (se 2 (by rfl) ⟨637863, by rfl⟩ : syracuseStep 1700969 = 1275727) B1275727
theorem B2552939 : Blo 1132632 2552939 := bstep (se 1 (by rfl) ⟨1914704, by rfl⟩ : syracuseStep 2552939 = 3829409) B3829409
theorem B1701071 : Blo 1132632 1701071 := bstep (se 1 (by rfl) ⟨1275803, by rfl⟩ : syracuseStep 1701071 = 2551607) B2551607
theorem B3831137 : Blo 1132632 3831137 := bstep (se 2 (by rfl) ⟨1436676, by rfl⟩ : syracuseStep 3831137 = 2873353) B2873353
theorem B2422171 : Blo 1132632 2422171 := bstep (se 1 (by rfl) ⟨1816628, by rfl⟩ : syracuseStep 2422171 = 3633257) B3633257
theorem B1701275 : Blo 1132632 1701275 := bstep (se 1 (by rfl) ⟨1275956, by rfl⟩ : syracuseStep 1701275 = 2551913) B2551913
theorem B29455883 : Blo 1132632 29455883 := bstep (se 1 (by rfl) ⟨22091912, by rfl⟩ : syracuseStep 29455883 = 44183825) B44183825
theorem B1701497 : Blo 1132632 1701497 := bstep (se 2 (by rfl) ⟨638061, by rfl⟩ : syracuseStep 1701497 = 1276123) B1276123
theorem B2553515 : Blo 1132632 2553515 := bstep (se 1 (by rfl) ⟨1915136, by rfl⟩ : syracuseStep 2553515 = 3830273) B3830273
theorem B1701599 : Blo 1132632 1701599 := bstep (se 1 (by rfl) ⟨1276199, by rfl⟩ : syracuseStep 1701599 = 2552399) B2552399
theorem B5175035 : Blo 1132632 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B1701695 : Blo 1132632 1701695 := bstep (se 1 (by rfl) ⟨1276271, by rfl⟩ : syracuseStep 1701695 = 2552543) B2552543
theorem B6911963 : Blo 1132632 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B1701863 : Blo 1132632 1701863 := bstep (se 1 (by rfl) ⟨1276397, by rfl⟩ : syracuseStep 1701863 = 2552795) B2552795
theorem B1210351 : Blo 1132632 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B2553839 : Blo 1132632 2553839 := bstep (se 1 (by rfl) ⟨1915379, by rfl⟩ : syracuseStep 2553839 = 3830759) B3830759
theorem B1701881 : Blo 1132632 1701881 := bstep (se 2 (by rfl) ⟨638205, by rfl⟩ : syracuseStep 1701881 = 1276411) B1276411
theorem B1701983 : Blo 1132632 1701983 := bstep (se 1 (by rfl) ⟨1276487, by rfl⟩ : syracuseStep 1701983 = 2552975) B2552975
theorem B4847759 : Blo 1132632 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1702043 : Blo 1132632 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B1702079 : Blo 1132632 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B2554055 : Blo 1132632 2554055 := bstep (se 1 (by rfl) ⟨1915541, by rfl⟩ : syracuseStep 2554055 = 3831083) B3831083
theorem B1702121 : Blo 1132632 1702121 := bstep (se 2 (by rfl) ⟨638295, by rfl⟩ : syracuseStep 1702121 = 1276591) B1276591
theorem B8190281 : Blo 1132632 8190281 := bstep (se 2 (by rfl) ⟨3071355, by rfl⟩ : syracuseStep 8190281 = 6142711) B6142711
theorem B2554235 : Blo 1132632 2554235 := bstep (se 1 (by rfl) ⟨1915676, by rfl⟩ : syracuseStep 2554235 = 3831353) B3831353
theorem B6912499 : Blo 1132632 6912499 := bstep (se 1 (by rfl) ⟨5184374, by rfl⟩ : syracuseStep 6912499 = 10368749) B10368749
theorem B1702427 : Blo 1132632 1702427 := bstep (se 1 (by rfl) ⟨1276820, by rfl⟩ : syracuseStep 1702427 = 2553641) B2553641
theorem B1276447 : Blo 1132632 1276447 := bstep (se 1 (by rfl) ⟨957335, by rfl⟩ : syracuseStep 1276447 = 1914671) B1914671
theorem B1702505 : Blo 1132632 1702505 := bstep (se 2 (by rfl) ⟨638439, by rfl⟩ : syracuseStep 1702505 = 1276879) B1276879
theorem B2554505 : Blo 1132632 2554505 := bstep (se 2 (by rfl) ⟨957939, by rfl⟩ : syracuseStep 2554505 = 1915879) B1915879
theorem B3636127 : Blo 1132632 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1703033 : Blo 1132632 1703033 := bstep (se 2 (by rfl) ⟨638637, by rfl⟩ : syracuseStep 1703033 = 1277275) B1277275
theorem B2555063 : Blo 1132632 2555063 := bstep (se 1 (by rfl) ⟨1916297, by rfl⟩ : syracuseStep 2555063 = 3832595) B3832595
theorem B1703135 : Blo 1132632 1703135 := bstep (se 1 (by rfl) ⟨1277351, by rfl⟩ : syracuseStep 1703135 = 2554703) B2554703
theorem B3833081 : Blo 1132632 3833081 := bstep (se 2 (by rfl) ⟨1437405, by rfl⟩ : syracuseStep 3833081 = 2874811) B2874811
theorem B1703177 : Blo 1132632 1703177 := bstep (se 2 (by rfl) ⟨638691, by rfl⟩ : syracuseStep 1703177 = 1277383) B1277383
theorem B1703279 : Blo 1132632 1703279 := bstep (se 1 (by rfl) ⟨1277459, by rfl⟩ : syracuseStep 1703279 = 2554919) B2554919
theorem B1703399 : Blo 1132632 1703399 := bstep (se 1 (by rfl) ⟨1277549, by rfl⟩ : syracuseStep 1703399 = 2555099) B2555099
theorem B3833351 : Blo 1132632 3833351 := bstep (se 1 (by rfl) ⟨2875013, by rfl⟩ : syracuseStep 3833351 = 5750027) B5750027
theorem B1703531 : Blo 1132632 1703531 := bstep (se 1 (by rfl) ⟨1277648, by rfl⟩ : syracuseStep 1703531 = 2555297) B2555297
theorem B1703657 : Blo 1132632 1703657 := bstep (se 2 (by rfl) ⟨638871, by rfl⟩ : syracuseStep 1703657 = 1277743) B1277743
theorem B4849399 : Blo 1132632 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B2555639 : Blo 1132632 2555639 := bstep (se 1 (by rfl) ⟨1916729, by rfl⟩ : syracuseStep 2555639 = 3833459) B3833459
theorem B14516009 : Blo 1132632 14516009 := bstep (se 2 (by rfl) ⟨5443503, by rfl⟩ : syracuseStep 14516009 = 10887007) B10887007
theorem B1703801 : Blo 1132632 1703801 := bstep (se 2 (by rfl) ⟨638925, by rfl⟩ : syracuseStep 1703801 = 1277851) B1277851
theorem B2555819 : Blo 1132632 2555819 := bstep (se 1 (by rfl) ⟨1916864, by rfl⟩ : syracuseStep 2555819 = 3833729) B3833729
theorem B1703903 : Blo 1132632 1703903 := bstep (se 1 (by rfl) ⟨1277927, by rfl⟩ : syracuseStep 1703903 = 2555855) B2555855
theorem B19398689 : Blo 1132632 19398689 := bstep (se 2 (by rfl) ⟨7274508, by rfl⟩ : syracuseStep 19398689 = 14549017) B14549017
theorem B1704239 : Blo 1132632 1704239 := bstep (se 1 (by rfl) ⟨1278179, by rfl⟩ : syracuseStep 1704239 = 2556359) B2556359
theorem B2457983 : Blo 1132632 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B2556287 : Blo 1132632 2556287 := bstep (se 1 (by rfl) ⟨1917215, by rfl⟩ : syracuseStep 2556287 = 3834431) B3834431
theorem B1704479 : Blo 1132632 1704479 := bstep (se 1 (by rfl) ⟨1278359, by rfl⟩ : syracuseStep 1704479 = 2556719) B2556719
theorem B2556521 : Blo 1132632 2556521 := bstep (se 2 (by rfl) ⟨958695, by rfl⟩ : syracuseStep 2556521 = 1917391) B1917391
theorem B10912765 : Blo 1132632 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B2557151 : Blo 1132632 2557151 := bstep (se 1 (by rfl) ⟨1917863, by rfl⟩ : syracuseStep 2557151 = 3835727) B3835727
theorem B5735771 : Blo 1132632 5735771 := bstep (se 1 (by rfl) ⟨4301828, by rfl⟩ : syracuseStep 5735771 = 8603657) B8603657
theorem B2426203 : Blo 1132632 2426203 := bstep (se 1 (by rfl) ⟨1819652, by rfl⟩ : syracuseStep 2426203 = 3639305) B3639305
theorem B31065515 : Blo 1132632 31065515 := bstep (se 1 (by rfl) ⟨23299136, by rfl⟩ : syracuseStep 31065515 = 46598273) B46598273
theorem B2557367 : Blo 1132632 2557367 := bstep (se 1 (by rfl) ⟨1918025, by rfl⟩ : syracuseStep 2557367 = 3836051) B3836051
theorem B8619695 : Blo 1132632 8619695 := bstep (se 1 (by rfl) ⟨6464771, by rfl⟩ : syracuseStep 8619695 = 12929543) B12929543
theorem B31000265 : Blo 1132632 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B8718461 : Blo 1132632 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B7375009 : Blo 1132632 7375009 := bstep (se 2 (by rfl) ⟨2765628, by rfl⟩ : syracuseStep 7375009 = 5531257) B5531257
theorem B2722175 : Blo 1132632 2722175 := bstep (se 1 (by rfl) ⟨2041631, by rfl⟩ : syracuseStep 2722175 = 4083263) B4083263
theorem B2427263 : Blo 1132632 2427263 := bstep (se 1 (by rfl) ⟨1820447, by rfl⟩ : syracuseStep 2427263 = 3640895) B3640895
theorem B55184753 : Blo 1132632 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B1150567 : Blo 1132632 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B3641075 : Blo 1132632 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B15536261 : Blo 1132632 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B2724137 : Blo 1132632 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B37262227 : Blo 1132632 37262227 := bstep (se 1 (by rfl) ⟨27946670, by rfl⟩ : syracuseStep 37262227 = 55893341) B55893341
theorem B23270561 : Blo 1132632 23270561 := bstep (se 2 (by rfl) ⟨8726460, by rfl⟩ : syracuseStep 23270561 = 17452921) B17452921
theorem B9704609 : Blo 1132632 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B20682323 : Blo 1132632 20682323 := bstep (se 1 (by rfl) ⟨15511742, by rfl⟩ : syracuseStep 20682323 = 31023485) B31023485
theorem B18388691 : Blo 1132632 18388691 := bstep (se 1 (by rfl) ⟨13791518, by rfl⟩ : syracuseStep 18388691 = 27583037) B27583037
theorem B298031147 : Blo 1132632 298031147 := bstep (se 1 (by rfl) ⟨223523360, by rfl⟩ : syracuseStep 298031147 = 447046721) B447046721
theorem B7280765 : Blo 1132632 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B20977825 : Blo 1132632 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B46537037 : Blo 1132632 46537037 := bstep (se 3 (by rfl) ⟨8725694, by rfl⟩ : syracuseStep 46537037 = 17451389) B17451389
theorem B2726711 : Blo 1132632 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B2726779 : Blo 1132632 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B1613801 : Blo 1132632 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B36774269 : Blo 1132632 36774269 := bstep (se 3 (by rfl) ⟨6895175, by rfl⟩ : syracuseStep 36774269 = 13790351) B13790351
theorem B9216665 : Blo 1132632 9216665 := bstep (se 2 (by rfl) ⟨3456249, by rfl⟩ : syracuseStep 9216665 = 6912499) B6912499
theorem B18391805 : Blo 1132632 18391805 := bstep (se 3 (by rfl) ⟨3448463, by rfl⟩ : syracuseStep 18391805 = 6896927) B6896927
theorem B9708335 : Blo 1132632 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B4301693 : Blo 1132632 4301693 := bstep (se 3 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 4301693 = 1613135) B1613135
theorem B19637255 : Blo 1132632 19637255 := bstep (se 1 (by rfl) ⟨14727941, by rfl⟩ : syracuseStep 19637255 = 29455883) B29455883
theorem B5448809 : Blo 1132632 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B3450023 : Blo 1132632 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B4302497 : Blo 1132632 4302497 := bstep (se 2 (by rfl) ⟨1613436, by rfl⟩ : syracuseStep 4302497 = 3226873) B3226873
theorem B43656893 : Blo 1132632 43656893 := bstep (se 3 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 43656893 = 16371335) B16371335
theorem B4302953 : Blo 1132632 4302953 := bstep (se 2 (by rfl) ⟨1613607, by rfl⟩ : syracuseStep 4302953 = 3227215) B3227215
theorem B5449963 : Blo 1132632 5449963 := bstep (se 1 (by rfl) ⟨4087472, by rfl⟩ : syracuseStep 5449963 = 8174945) B8174945
theorem B6465865 : Blo 1132632 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B9677339 : Blo 1132632 9677339 := bstep (se 1 (by rfl) ⟨7258004, by rfl⟩ : syracuseStep 9677339 = 14516009) B14516009
theorem B1911343 : Blo 1132632 1911343 := bstep (se 1 (by rfl) ⟨1433507, by rfl⟩ : syracuseStep 1911343 = 2867015) B2867015
theorem B1911559 : Blo 1132632 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B1911775 : Blo 1132632 1911775 := bstep (se 1 (by rfl) ⟨1433831, by rfl⟩ : syracuseStep 1911775 = 2867663) B2867663
theorem B4304137 : Blo 1132632 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B5451407 : Blo 1132632 5451407 := bstep (se 1 (by rfl) ⟨4088555, by rfl⟩ : syracuseStep 5451407 = 8177111) B8177111
theorem B8728249 : Blo 1132632 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B1912639 : Blo 1132632 1912639 := bstep (se 1 (by rfl) ⟨1434479, by rfl⟩ : syracuseStep 1912639 = 2868959) B2868959
theorem B14757869 : Blo 1132632 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B4599935 : Blo 1132632 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B14529131 : Blo 1132632 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B1913807 : Blo 1132632 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B6993001 : Blo 1132632 6993001 := bstep (se 2 (by rfl) ⟨2622375, by rfl⟩ : syracuseStep 6993001 = 5244751) B5244751
theorem B6141673 : Blo 1132632 6141673 := bstep (se 2 (by rfl) ⟨2303127, by rfl⟩ : syracuseStep 6141673 = 4606255) B4606255
theorem B8730625 : Blo 1132632 8730625 := bstep (se 2 (by rfl) ⟨3273984, by rfl⟩ : syracuseStep 8730625 = 6547969) B6547969
theorem B4307039 : Blo 1132632 4307039 := bstep (se 1 (by rfl) ⟨3230279, by rfl⟩ : syracuseStep 4307039 = 6460559) B6460559
theorem B4307357 : Blo 1132632 4307357 := bstep (se 3 (by rfl) ⟨807629, by rfl⟩ : syracuseStep 4307357 = 1615259) B1615259
theorem B1817039 : Blo 1132632 1817039 := bstep (se 1 (by rfl) ⟨1362779, by rfl⟩ : syracuseStep 1817039 = 2725559) B2725559
theorem B2046505 : Blo 1132632 2046505 := bstep (se 2 (by rfl) ⟨767439, by rfl⟩ : syracuseStep 2046505 = 1534879) B1534879
theorem B1915535 : Blo 1132632 1915535 := bstep (se 1 (by rfl) ⟨1436651, by rfl⟩ : syracuseStep 1915535 = 2873303) B2873303
theorem B21805847 : Blo 1132632 21805847 := bstep (se 1 (by rfl) ⟨16354385, by rfl⟩ : syracuseStep 21805847 = 32708771) B32708771
theorem B1817705 : Blo 1132632 1817705 := bstep (se 2 (by rfl) ⟨681639, by rfl⟩ : syracuseStep 1817705 = 1363279) B1363279
theorem B5749865 : Blo 1132632 5749865 := bstep (se 2 (by rfl) ⟨2156199, by rfl⟩ : syracuseStep 5749865 = 4312399) B4312399
theorem B1916527 : Blo 1132632 1916527 := bstep (se 1 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 1916527 = 2874791) B2874791
theorem B7258085 : Blo 1132632 7258085 := bstep (se 4 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 7258085 = 1360891) B1360891
theorem B3228457 : Blo 1132632 3228457 := bstep (se 2 (by rfl) ⟨1210671, by rfl⟩ : syracuseStep 3228457 = 2421343) B2421343
theorem B21840749 : Blo 1132632 21840749 := bstep (se 3 (by rfl) ⟨4095140, by rfl⟩ : syracuseStep 21840749 = 8190281) B8190281
theorem B4310441 : Blo 1132632 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B4310455 : Blo 1132632 4310455 := bstep (se 1 (by rfl) ⟨3232841, by rfl⟩ : syracuseStep 4310455 = 6465683) B6465683
theorem B3229561 : Blo 1132632 3229561 := bstep (se 2 (by rfl) ⟨1211085, by rfl⟩ : syracuseStep 3229561 = 2422171) B2422171
theorem B15517655 : Blo 1132632 15517655 := bstep (se 1 (by rfl) ⟨11638241, by rfl⟩ : syracuseStep 15517655 = 23276483) B23276483
theorem B1132767 : Blo 1132632 1132767 := bstep (se 1 (by rfl) ⟨849575, by rfl⟩ : syracuseStep 1132767 = 1699151) B1699151
theorem B1132827 : Blo 1132632 1132827 := bstep (se 1 (by rfl) ⟨849620, by rfl⟩ : syracuseStep 1132827 = 1699241) B1699241
theorem B2869627 : Blo 1132632 2869627 := bstep (se 1 (by rfl) ⟨2152220, by rfl⟩ : syracuseStep 2869627 = 4304441) B4304441
theorem B1132927 : Blo 1132632 1132927 := bstep (se 1 (by rfl) ⟨849695, by rfl⟩ : syracuseStep 1132927 = 1699391) B1699391
theorem B1133103 : Blo 1132632 1133103 := bstep (se 1 (by rfl) ⟨849827, by rfl⟩ : syracuseStep 1133103 = 1699655) B1699655
theorem B8735303 : Blo 1132632 8735303 := bstep (se 1 (by rfl) ⟨6551477, by rfl⟩ : syracuseStep 8735303 = 13102955) B13102955
theorem B1133159 : Blo 1132632 1133159 := bstep (se 1 (by rfl) ⟨849869, by rfl⟩ : syracuseStep 1133159 = 1699739) B1699739
theorem B3689063 : Blo 1132632 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B8276779 : Blo 1132632 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B4311899 : Blo 1132632 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B4311913 : Blo 1132632 4311913 := bstep (se 2 (by rfl) ⟨1616967, by rfl⟩ : syracuseStep 4311913 = 3233935) B3233935
theorem B1133535 : Blo 1132632 1133535 := bstep (se 1 (by rfl) ⟨850151, by rfl⟩ : syracuseStep 1133535 = 1700303) B1700303
theorem B1133563 : Blo 1132632 1133563 := bstep (se 1 (by rfl) ⟨850172, by rfl⟩ : syracuseStep 1133563 = 1700345) B1700345
theorem B1133631 : Blo 1132632 1133631 := bstep (se 1 (by rfl) ⟨850223, by rfl⟩ : syracuseStep 1133631 = 1700447) B1700447
theorem B3067055 : Blo 1132632 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B19385567 : Blo 1132632 19385567 := bstep (se 1 (by rfl) ⟨14539175, by rfl⟩ : syracuseStep 19385567 = 29078351) B29078351
theorem B1133951 : Blo 1132632 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B1133979 : Blo 1132632 1133979 := bstep (se 1 (by rfl) ⟨850484, by rfl⟩ : syracuseStep 1133979 = 1700969) B1700969
theorem B1134047 : Blo 1132632 1134047 := bstep (se 1 (by rfl) ⟨850535, by rfl⟩ : syracuseStep 1134047 = 1701071) B1701071
theorem B1134183 : Blo 1132632 1134183 := bstep (se 1 (by rfl) ⟨850637, by rfl⟩ : syracuseStep 1134183 = 1701275) B1701275
theorem B1134331 : Blo 1132632 1134331 := bstep (se 1 (by rfl) ⟨850748, by rfl⟩ : syracuseStep 1134331 = 1701497) B1701497
theorem B2871065 : Blo 1132632 2871065 := bstep (se 2 (by rfl) ⟨1076649, by rfl⟩ : syracuseStep 2871065 = 2153299) B2153299
theorem B1134399 : Blo 1132632 1134399 := bstep (se 1 (by rfl) ⟨850799, by rfl⟩ : syracuseStep 1134399 = 1701599) B1701599
theorem B1134463 : Blo 1132632 1134463 := bstep (se 1 (by rfl) ⟨850847, by rfl⟩ : syracuseStep 1134463 = 1701695) B1701695
theorem B19648403 : Blo 1132632 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B4607975 : Blo 1132632 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B2150383 : Blo 1132632 2150383 := bstep (se 1 (by rfl) ⟨1612787, by rfl⟩ : syracuseStep 2150383 = 3225575) B3225575
theorem B1134575 : Blo 1132632 1134575 := bstep (se 1 (by rfl) ⟨850931, by rfl⟩ : syracuseStep 1134575 = 1701863) B1701863
theorem B1134587 : Blo 1132632 1134587 := bstep (se 1 (by rfl) ⟨850940, by rfl⟩ : syracuseStep 1134587 = 1701881) B1701881
theorem B1134655 : Blo 1132632 1134655 := bstep (se 1 (by rfl) ⟨850991, by rfl⟩ : syracuseStep 1134655 = 1701983) B1701983
theorem B3231839 : Blo 1132632 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B1134695 : Blo 1132632 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B1134719 : Blo 1132632 1134719 := bstep (se 1 (by rfl) ⟨851039, by rfl⟩ : syracuseStep 1134719 = 1702079) B1702079
theorem B1134747 : Blo 1132632 1134747 := bstep (se 1 (by rfl) ⟨851060, by rfl⟩ : syracuseStep 1134747 = 1702121) B1702121
theorem B2150687 : Blo 1132632 2150687 := bstep (se 1 (by rfl) ⟨1613015, by rfl⟩ : syracuseStep 2150687 = 3226031) B3226031
theorem B1134951 : Blo 1132632 1134951 := bstep (se 1 (by rfl) ⟨851213, by rfl⟩ : syracuseStep 1134951 = 1702427) B1702427
theorem B1135003 : Blo 1132632 1135003 := bstep (se 1 (by rfl) ⟨851252, by rfl⟩ : syracuseStep 1135003 = 1702505) B1702505
theorem B1135355 : Blo 1132632 1135355 := bstep (se 1 (by rfl) ⟨851516, by rfl⟩ : syracuseStep 1135355 = 1703033) B1703033
theorem B1135423 : Blo 1132632 1135423 := bstep (se 1 (by rfl) ⟨851567, by rfl⟩ : syracuseStep 1135423 = 1703135) B1703135
theorem B1135451 : Blo 1132632 1135451 := bstep (se 1 (by rfl) ⟨851588, by rfl⟩ : syracuseStep 1135451 = 1703177) B1703177
theorem B2872169 : Blo 1132632 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B1135519 : Blo 1132632 1135519 := bstep (se 1 (by rfl) ⟨851639, by rfl⟩ : syracuseStep 1135519 = 1703279) B1703279
theorem B1135599 : Blo 1132632 1135599 := bstep (se 1 (by rfl) ⟨851699, by rfl⟩ : syracuseStep 1135599 = 1703399) B1703399
theorem B11064383 : Blo 1132632 11064383 := bstep (se 1 (by rfl) ⟨8298287, by rfl⟩ : syracuseStep 11064383 = 16596575) B16596575
theorem B1135687 : Blo 1132632 1135687 := bstep (se 1 (by rfl) ⟨851765, by rfl⟩ : syracuseStep 1135687 = 1703531) B1703531
theorem B1135771 : Blo 1132632 1135771 := bstep (se 1 (by rfl) ⟨851828, by rfl⟩ : syracuseStep 1135771 = 1703657) B1703657
theorem B1135867 : Blo 1132632 1135867 := bstep (se 1 (by rfl) ⟨851900, by rfl⟩ : syracuseStep 1135867 = 1703801) B1703801
theorem B1135935 : Blo 1132632 1135935 := bstep (se 1 (by rfl) ⟨851951, by rfl⟩ : syracuseStep 1135935 = 1703903) B1703903
theorem B1136103 : Blo 1132632 1136103 := bstep (se 1 (by rfl) ⟨852077, by rfl⟩ : syracuseStep 1136103 = 1704155) B1704155
theorem B1136111 : Blo 1132632 1136111 := bstep (se 1 (by rfl) ⟨852083, by rfl⟩ : syracuseStep 1136111 = 1704167) B1704167
theorem B1136219 : Blo 1132632 1136219 := bstep (se 1 (by rfl) ⟨852164, by rfl⟩ : syracuseStep 1136219 = 1704329) B1704329
theorem B26203769 : Blo 1132632 26203769 := bstep (se 2 (by rfl) ⟨9826413, by rfl⟩ : syracuseStep 26203769 = 19652827) B19652827
theorem B1136283 : Blo 1132632 1136283 := bstep (se 1 (by rfl) ⟨852212, by rfl⟩ : syracuseStep 1136283 = 1704425) B1704425
theorem B1136367 : Blo 1132632 1136367 := bstep (se 1 (by rfl) ⟨852275, by rfl⟩ : syracuseStep 1136367 = 1704551) B1704551
theorem B8607545 : Blo 1132632 8607545 := bstep (se 2 (by rfl) ⟨3227829, by rfl⟩ : syracuseStep 8607545 = 6455659) B6455659
theorem B1136455 : Blo 1132632 1136455 := bstep (se 1 (by rfl) ⟨852341, by rfl⟩ : syracuseStep 1136455 = 1704683) B1704683
theorem B1136475 : Blo 1132632 1136475 := bstep (se 1 (by rfl) ⟨852356, by rfl⟩ : syracuseStep 1136475 = 1704713) B1704713
theorem B1136543 : Blo 1132632 1136543 := bstep (se 1 (by rfl) ⟨852407, by rfl⟩ : syracuseStep 1136543 = 1704815) B1704815
theorem B2152585 : Blo 1132632 2152585 := bstep (se 2 (by rfl) ⟨807219, by rfl⟩ : syracuseStep 2152585 = 1614439) B1614439
theorem B2873657 : Blo 1132632 2873657 := bstep (se 2 (by rfl) ⟨1077621, by rfl⟩ : syracuseStep 2873657 = 2155243) B2155243
theorem B20732237 : Blo 1132632 20732237 := bstep (se 3 (by rfl) ⟨3887294, by rfl⟩ : syracuseStep 20732237 = 7774589) B7774589
theorem B3823955 : Blo 1132632 3823955 := bstep (se 1 (by rfl) ⟨2867966, by rfl⟩ : syracuseStep 3823955 = 5735933) B5735933
theorem B4839763 : Blo 1132632 4839763 := bstep (se 1 (by rfl) ⟨3629822, by rfl⟩ : syracuseStep 4839763 = 7259645) B7259645
theorem B3824495 : Blo 1132632 3824495 := bstep (se 1 (by rfl) ⟨2868371, by rfl⟩ : syracuseStep 3824495 = 5736743) B5736743
theorem B3824603 : Blo 1132632 3824603 := bstep (se 1 (by rfl) ⟨2868452, by rfl⟩ : syracuseStep 3824603 = 5736905) B5736905
theorem B3234779 : Blo 1132632 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B3824873 : Blo 1132632 3824873 := bstep (se 2 (by rfl) ⟨1434327, by rfl⟩ : syracuseStep 3824873 = 2868655) B2868655
theorem B3825143 : Blo 1132632 3825143 := bstep (se 1 (by rfl) ⟨2868857, by rfl⟩ : syracuseStep 3825143 = 5737715) B5737715
theorem B8609489 : Blo 1132632 8609489 := bstep (se 2 (by rfl) ⟨3228558, by rfl⟩ : syracuseStep 8609489 = 6457117) B6457117
theorem B2154271 : Blo 1132632 2154271 := bstep (se 1 (by rfl) ⟨1615703, by rfl⟩ : syracuseStep 2154271 = 3231407) B3231407
theorem B2875247 : Blo 1132632 2875247 := bstep (se 1 (by rfl) ⟨2156435, by rfl⟩ : syracuseStep 2875247 = 4312871) B4312871
theorem B848977955 : Blo 1132632 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B3235963 : Blo 1132632 3235963 := bstep (se 1 (by rfl) ⟨2426972, by rfl⟩ : syracuseStep 3235963 = 4853945) B4853945
theorem B8184347 : Blo 1132632 8184347 := bstep (se 1 (by rfl) ⟨6138260, by rfl⟩ : syracuseStep 8184347 = 12276521) B12276521
theorem B2548511 : Blo 1132632 2548511 := bstep (se 1 (by rfl) ⟨1911383, by rfl⟩ : syracuseStep 2548511 = 3822767) B3822767
theorem B2155319 : Blo 1132632 2155319 := bstep (se 1 (by rfl) ⟨1616489, by rfl⟩ : syracuseStep 2155319 = 3232979) B3232979
theorem B2549321 : Blo 1132632 2549321 := bstep (se 2 (by rfl) ⟨955995, by rfl⟩ : syracuseStep 2549321 = 1911991) B1911991
theorem B2156215 : Blo 1132632 2156215 := bstep (se 1 (by rfl) ⟨1617161, by rfl⟩ : syracuseStep 2156215 = 3234323) B3234323
theorem B4843421 : Blo 1132632 4843421 := bstep (se 3 (by rfl) ⟨908141, by rfl⟩ : syracuseStep 4843421 = 1816283) B1816283
theorem B1435583 : Blo 1132632 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B2549753 : Blo 1132632 2549753 := bstep (se 2 (by rfl) ⟨956157, by rfl⟩ : syracuseStep 2549753 = 1912315) B1912315
theorem B2549807 : Blo 1132632 2549807 := bstep (se 1 (by rfl) ⟨1912355, by rfl⟩ : syracuseStep 2549807 = 3824711) B3824711
theorem B8611919 : Blo 1132632 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B2549843 : Blo 1132632 2549843 := bstep (se 1 (by rfl) ⟨1912382, by rfl⟩ : syracuseStep 2549843 = 3824765) B3824765
theorem B4089953 : Blo 1132632 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B2156777 : Blo 1132632 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B2550023 : Blo 1132632 2550023 := bstep (se 1 (by rfl) ⟨1912517, by rfl⟩ : syracuseStep 2550023 = 3825035) B3825035
theorem B2156807 : Blo 1132632 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B1534511 : Blo 1132632 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B2550329 : Blo 1132632 2550329 := bstep (se 2 (by rfl) ⟨956373, by rfl⟩ : syracuseStep 2550329 = 1912747) B1912747
theorem B4844137 : Blo 1132632 4844137 := bstep (se 2 (by rfl) ⟨1816551, by rfl⟩ : syracuseStep 4844137 = 3633103) B3633103
theorem B13658771 : Blo 1132632 13658771 := bstep (se 1 (by rfl) ⟨10244078, by rfl⟩ : syracuseStep 13658771 = 20488157) B20488157
theorem B2551049 : Blo 1132632 2551049 := bstep (se 2 (by rfl) ⟨956643, by rfl⟩ : syracuseStep 2551049 = 1913287) B1913287
theorem B1699127 : Blo 1132632 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B1699295 : Blo 1132632 1699295 := bstep (se 1 (by rfl) ⟨1274471, by rfl⟩ : syracuseStep 1699295 = 2548943) B2548943
theorem B9694835 : Blo 1132632 9694835 := bstep (se 1 (by rfl) ⟨7271126, by rfl⟩ : syracuseStep 9694835 = 14542253) B14542253
theorem B1699511 : Blo 1132632 1699511 := bstep (se 1 (by rfl) ⟨1274633, by rfl⟩ : syracuseStep 1699511 = 2549267) B2549267
theorem B1699721 : Blo 1132632 1699721 := bstep (se 2 (by rfl) ⟨637395, by rfl⟩ : syracuseStep 1699721 = 1274791) B1274791
theorem B2420617 : Blo 1132632 2420617 := bstep (se 2 (by rfl) ⟨907731, by rfl⟩ : syracuseStep 2420617 = 1815463) B1815463
theorem B1699967 : Blo 1132632 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B2552039 : Blo 1132632 2552039 := bstep (se 1 (by rfl) ⟨1914029, by rfl⟩ : syracuseStep 2552039 = 3828059) B3828059
theorem B1274215 : Blo 1132632 1274215 := bstep (se 1 (by rfl) ⟨955661, by rfl⟩ : syracuseStep 1274215 = 1911323) B1911323
theorem B2552219 : Blo 1132632 2552219 := bstep (se 1 (by rfl) ⟨1914164, by rfl⟩ : syracuseStep 2552219 = 3828329) B3828329
theorem B1700603 : Blo 1132632 1700603 := bstep (se 1 (by rfl) ⟨1275452, by rfl⟩ : syracuseStep 1700603 = 2550905) B2550905
theorem B43578161 : Blo 1132632 43578161 := bstep (se 2 (by rfl) ⟨16341810, by rfl⟩ : syracuseStep 43578161 = 32683621) B32683621
theorem B1274863 : Blo 1132632 1274863 := bstep (se 1 (by rfl) ⟨956147, by rfl⟩ : syracuseStep 1274863 = 1912295) B1912295
theorem B2552903 : Blo 1132632 2552903 := bstep (se 1 (by rfl) ⟨1914677, by rfl⟩ : syracuseStep 2552903 = 3829355) B3829355
theorem B3830867 : Blo 1132632 3830867 := bstep (se 1 (by rfl) ⟨2873150, by rfl⟩ : syracuseStep 3830867 = 5746301) B5746301
theorem B1701047 : Blo 1132632 1701047 := bstep (se 1 (by rfl) ⟨1275785, by rfl⟩ : syracuseStep 1701047 = 2551571) B2551571
theorem B2553083 : Blo 1132632 2553083 := bstep (se 1 (by rfl) ⟨1914812, by rfl⟩ : syracuseStep 2553083 = 3829625) B3829625
theorem B26178835 : Blo 1132632 26178835 := bstep (se 1 (by rfl) ⟨19634126, by rfl⟩ : syracuseStep 26178835 = 39268253) B39268253
theorem B1701287 : Blo 1132632 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B2553299 : Blo 1132632 2553299 := bstep (se 1 (by rfl) ⟨1914974, by rfl⟩ : syracuseStep 2553299 = 3829949) B3829949
theorem B1275367 : Blo 1132632 1275367 := bstep (se 1 (by rfl) ⟨956525, by rfl⟩ : syracuseStep 1275367 = 1913051) B1913051
theorem B11662867 : Blo 1132632 11662867 := bstep (se 1 (by rfl) ⟨8747150, by rfl⟩ : syracuseStep 11662867 = 17494301) B17494301
theorem B1701467 : Blo 1132632 1701467 := bstep (se 1 (by rfl) ⟨1276100, by rfl⟩ : syracuseStep 1701467 = 2552201) B2552201
theorem B3831407 : Blo 1132632 3831407 := bstep (se 1 (by rfl) ⟨2873555, by rfl⟩ : syracuseStep 3831407 = 5747111) B5747111
theorem B1275547 : Blo 1132632 1275547 := bstep (se 1 (by rfl) ⟨956660, by rfl⟩ : syracuseStep 1275547 = 1913321) B1913321
theorem B2553569 : Blo 1132632 2553569 := bstep (se 2 (by rfl) ⟨957588, by rfl⟩ : syracuseStep 2553569 = 1915177) B1915177
theorem B8189707 : Blo 1132632 8189707 := bstep (se 1 (by rfl) ⟨6142280, by rfl⟩ : syracuseStep 8189707 = 12284561) B12284561
theorem B4093757 : Blo 1132632 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B1701929 : Blo 1132632 1701929 := bstep (se 2 (by rfl) ⟨638223, by rfl⟩ : syracuseStep 1701929 = 1276447) B1276447
theorem B1701959 : Blo 1132632 1701959 := bstep (se 1 (by rfl) ⟨1276469, by rfl⟩ : syracuseStep 1701959 = 2552939) B2552939
theorem B2554091 : Blo 1132632 2554091 := bstep (se 1 (by rfl) ⟨1915568, by rfl⟩ : syracuseStep 2554091 = 3831137) B3831137
theorem B1702343 : Blo 1132632 1702343 := bstep (se 1 (by rfl) ⟨1276757, by rfl⟩ : syracuseStep 1702343 = 2553515) B2553515
theorem B3832271 : Blo 1132632 3832271 := bstep (se 1 (by rfl) ⟨2874203, by rfl⟩ : syracuseStep 3832271 = 5748407) B5748407
theorem B4848169 : Blo 1132632 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B1702559 : Blo 1132632 1702559 := bstep (se 1 (by rfl) ⟨1276919, by rfl⟩ : syracuseStep 1702559 = 2553839) B2553839
theorem B1702703 : Blo 1132632 1702703 := bstep (se 1 (by rfl) ⟨1277027, by rfl⟩ : syracuseStep 1702703 = 2554055) B2554055
theorem B1702823 : Blo 1132632 1702823 := bstep (se 1 (by rfl) ⟨1277117, by rfl⟩ : syracuseStep 1702823 = 2554235) B2554235
theorem B1703003 : Blo 1132632 1703003 := bstep (se 1 (by rfl) ⟨1277252, by rfl⟩ : syracuseStep 1703003 = 2554505) B2554505
theorem B6454727 : Blo 1132632 6454727 := bstep (se 1 (by rfl) ⟨4841045, by rfl⟩ : syracuseStep 6454727 = 9682091) B9682091
theorem B1703375 : Blo 1132632 1703375 := bstep (se 1 (by rfl) ⟨1277531, by rfl⟩ : syracuseStep 1703375 = 2555063) B2555063
theorem B3636731 : Blo 1132632 3636731 := bstep (se 1 (by rfl) ⟨2727548, by rfl⟩ : syracuseStep 3636731 = 5455097) B5455097
theorem B2555387 : Blo 1132632 2555387 := bstep (se 1 (by rfl) ⟨1916540, by rfl⟩ : syracuseStep 2555387 = 3833081) B3833081
theorem B2555567 : Blo 1132632 2555567 := bstep (se 1 (by rfl) ⟨1916675, by rfl⟩ : syracuseStep 2555567 = 3833351) B3833351
theorem B1277671 : Blo 1132632 1277671 := bstep (se 1 (by rfl) ⟨958253, by rfl⟩ : syracuseStep 1277671 = 1916507) B1916507
theorem B2555657 : Blo 1132632 2555657 := bstep (se 2 (by rfl) ⟨958371, by rfl⟩ : syracuseStep 2555657 = 1916743) B1916743
theorem B1703759 : Blo 1132632 1703759 := bstep (se 1 (by rfl) ⟨1277819, by rfl⟩ : syracuseStep 1703759 = 2555639) B2555639
theorem B1703879 : Blo 1132632 1703879 := bstep (se 1 (by rfl) ⟨1277909, by rfl⟩ : syracuseStep 1703879 = 2555819) B2555819
theorem B8618237 : Blo 1132632 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B1704191 : Blo 1132632 1704191 := bstep (se 1 (by rfl) ⟨1278143, by rfl⟩ : syracuseStep 1704191 = 2556287) B2556287
theorem B1704347 : Blo 1132632 1704347 := bstep (se 1 (by rfl) ⟨1278260, by rfl⟩ : syracuseStep 1704347 = 2556521) B2556521
theorem B1704767 : Blo 1132632 1704767 := bstep (se 1 (by rfl) ⟨1278575, by rfl⟩ : syracuseStep 1704767 = 2557151) B2557151
theorem B20710343 : Blo 1132632 20710343 := bstep (se 1 (by rfl) ⟨15532757, by rfl⟩ : syracuseStep 20710343 = 31065515) B31065515
theorem B1704911 : Blo 1132632 1704911 := bstep (se 1 (by rfl) ⟨1278683, by rfl⟩ : syracuseStep 1704911 = 2557367) B2557367
theorem B6554621 : Blo 1132632 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B14550353 : Blo 1132632 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B2459375 : Blo 1132632 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B2427383 : Blo 1132632 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B10357507 : Blo 1132632 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B9833345 : Blo 1132632 9833345 := bstep (se 2 (by rfl) ⟨3687504, by rfl⟩ : syracuseStep 9833345 = 7375009) B7375009
theorem B8621153 : Blo 1132632 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B7376255 : Blo 1132632 7376255 := bstep (se 1 (by rfl) ⟨5532191, by rfl⟩ : syracuseStep 7376255 = 11064383) B11064383
theorem B6458849 : Blo 1132632 6458849 := bstep (se 2 (by rfl) ⟨2422068, by rfl⟩ : syracuseStep 6458849 = 4844137) B4844137
theorem B17469179 : Blo 1132632 17469179 := bstep (se 1 (by rfl) ⟨13101884, by rfl⟩ : syracuseStep 17469179 = 26203769) B26203769
theorem B12259127 : Blo 1132632 12259127 := bstep (se 1 (by rfl) ⟨9194345, by rfl⟩ : syracuseStep 12259127 = 18388691) B18388691
theorem B5738363 : Blo 1132632 5738363 := bstep (se 1 (by rfl) ⟨4303772, by rfl⟩ : syracuseStep 5738363 = 8607545) B8607545
theorem B4853843 : Blo 1132632 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B5738849 : Blo 1132632 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B11637665 : Blo 1132632 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B5739659 : Blo 1132632 5739659 := bstep (se 1 (by rfl) ⟨4304744, by rfl⟩ : syracuseStep 5739659 = 8609489) B8609489
theorem B24516179 : Blo 1132632 24516179 := bstep (se 1 (by rfl) ⟨18387134, by rfl⟩ : syracuseStep 24516179 = 36774269) B36774269
theorem B12261203 : Blo 1132632 12261203 := bstep (se 1 (by rfl) ⟨9195902, by rfl⟩ : syracuseStep 12261203 = 18391805) B18391805
theorem B2300015 : Blo 1132632 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B29104595 : Blo 1132632 29104595 := bstep (se 1 (by rfl) ⟨21828446, by rfl⟩ : syracuseStep 29104595 = 43656893) B43656893
theorem B49682969 : Blo 1132632 49682969 := bstep (se 2 (by rfl) ⟨18631113, by rfl⟩ : syracuseStep 49682969 = 37262227) B37262227
theorem B5741279 : Blo 1132632 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B2726635 : Blo 1132632 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B34905113 : Blo 1132632 34905113 := bstep (se 2 (by rfl) ⟨13089417, by rfl⟩ : syracuseStep 34905113 = 26178835) B26178835
theorem B10919609 : Blo 1132632 10919609 := bstep (se 2 (by rfl) ⟨4094853, by rfl⟩ : syracuseStep 10919609 = 8189707) B8189707
theorem B6463223 : Blo 1132632 6463223 := bstep (se 1 (by rfl) ⟨4847417, by rfl⟩ : syracuseStep 6463223 = 9694835) B9694835
theorem B9838579 : Blo 1132632 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B11640833 : Blo 1132632 11640833 := bstep (se 2 (by rfl) ⟨4365312, by rfl⟩ : syracuseStep 11640833 = 8730625) B8730625
theorem B6136357 : Blo 1132632 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B6464225 : Blo 1132632 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B2728673 : Blo 1132632 2728673 := bstep (se 2 (by rfl) ⟨1023252, by rfl⟩ : syracuseStep 2728673 = 2046505) B2046505
theorem B2729171 : Blo 1132632 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B4303151 : Blo 1132632 4303151 := bstep (se 1 (by rfl) ⟨3227363, by rfl⟩ : syracuseStep 4303151 = 6454727) B6454727
theorem B4303469 : Blo 1132632 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B14560499 : Blo 1132632 14560499 := bstep (se 1 (by rfl) ⟨10920374, by rfl⟩ : syracuseStep 14560499 = 21840749) B21840749
theorem B4304609 : Blo 1132632 4304609 := bstep (se 2 (by rfl) ⟨1614228, by rfl⟩ : syracuseStep 4304609 = 3228457) B3228457
theorem B5746463 : Blo 1132632 5746463 := bstep (se 1 (by rfl) ⟨4309847, by rfl⟩ : syracuseStep 5746463 = 8619695) B8619695
theorem B5812307 : Blo 1132632 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B1814783 : Blo 1132632 1814783 := bstep (se 1 (by rfl) ⟨1361087, by rfl⟩ : syracuseStep 1814783 = 2722175) B2722175
theorem B1618175 : Blo 1132632 1618175 := bstep (se 1 (by rfl) ⟨1213631, by rfl⟩ : syracuseStep 1618175 = 2427263) B2427263
theorem B5747273 : Blo 1132632 5747273 := bstep (se 2 (by rfl) ⟨2155227, by rfl⟩ : syracuseStep 5747273 = 4310455) B4310455
theorem B2044703 : Blo 1132632 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B12923711 : Blo 1132632 12923711 := bstep (se 1 (by rfl) ⟨9692783, by rfl⟩ : syracuseStep 12923711 = 19385567) B19385567
theorem B4306081 : Blo 1132632 4306081 := bstep (se 2 (by rfl) ⟨1614780, by rfl⟩ : syracuseStep 4306081 = 3229561) B3229561
theorem B1914043 : Blo 1132632 1914043 := bstep (se 1 (by rfl) ⟨1435532, by rfl⟩ : syracuseStep 1914043 = 2871065) B2871065
theorem B1816091 : Blo 1132632 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B1914779 : Blo 1132632 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B15513707 : Blo 1132632 15513707 := bstep (se 1 (by rfl) ⟨11635280, by rfl⟩ : syracuseStep 15513707 = 23270561) B23270561
theorem B6469739 : Blo 1132632 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B5749217 : Blo 1132632 5749217 := bstep (se 2 (by rfl) ⟨2155956, by rfl⟩ : syracuseStep 5749217 = 4311913) B4311913
theorem B198687431 : Blo 1132632 198687431 := bstep (se 1 (by rfl) ⟨149015573, by rfl⟩ : syracuseStep 198687431 = 298031147) B298031147
theorem B1915771 : Blo 1132632 1915771 := bstep (se 1 (by rfl) ⟨1436828, by rfl⟩ : syracuseStep 1915771 = 2873657) B2873657
theorem B1817807 : Blo 1132632 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B3227489 : Blo 1132632 3227489 := bstep (se 2 (by rfl) ⟨1210308, by rfl⟩ : syracuseStep 3227489 = 2420617) B2420617
theorem B1916831 : Blo 1132632 1916831 := bstep (se 1 (by rfl) ⟨1437623, by rfl⟩ : syracuseStep 1916831 = 2875247) B2875247
theorem B2867177 : Blo 1132632 2867177 := bstep (se 2 (by rfl) ⟨1075191, by rfl⟩ : syracuseStep 2867177 = 2150383) B2150383
theorem B565985303 : Blo 1132632 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B5456231 : Blo 1132632 5456231 := bstep (se 1 (by rfl) ⟨4092173, by rfl⟩ : syracuseStep 5456231 = 8184347) B8184347
theorem B6144443 : Blo 1132632 6144443 := bstep (se 1 (by rfl) ⟨4608332, by rfl⟩ : syracuseStep 6144443 = 9216665) B9216665
theorem B6472223 : Blo 1132632 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B2867795 : Blo 1132632 2867795 := bstep (se 1 (by rfl) ⟨2150846, by rfl⟩ : syracuseStep 2867795 = 4301693) B4301693
theorem B13091503 : Blo 1132632 13091503 := bstep (se 1 (by rfl) ⟨9818627, by rfl⟩ : syracuseStep 13091503 = 19637255) B19637255
theorem B5751485 : Blo 1132632 5751485 := bstep (se 3 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 5751485 = 2156807) B2156807
theorem B2868331 : Blo 1132632 2868331 := bstep (se 1 (by rfl) ⟨2151248, by rfl⟩ : syracuseStep 2868331 = 4302497) B4302497
theorem B3228947 : Blo 1132632 3228947 := bstep (se 1 (by rfl) ⟨2421710, by rfl⟩ : syracuseStep 3228947 = 4843421) B4843421
theorem B2868635 : Blo 1132632 2868635 := bstep (se 1 (by rfl) ⟨2151476, by rfl⟩ : syracuseStep 2868635 = 4302953) B4302953
theorem B9324001 : Blo 1132632 9324001 := bstep (se 2 (by rfl) ⟨3496500, by rfl⟩ : syracuseStep 9324001 = 6993001) B6993001
theorem B15550489 : Blo 1132632 15550489 := bstep (se 2 (by rfl) ⟨5831433, by rfl⟩ : syracuseStep 15550489 = 11662867) B11662867
theorem B1132751 : Blo 1132632 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B1132863 : Blo 1132632 1132863 := bstep (se 1 (by rfl) ⟨849647, by rfl⟩ : syracuseStep 1132863 = 1699295) B1699295
theorem B1133007 : Blo 1132632 1133007 := bstep (se 1 (by rfl) ⟨849755, by rfl⟩ : syracuseStep 1133007 = 1699511) B1699511
theorem B1133147 : Blo 1132632 1133147 := bstep (se 1 (by rfl) ⟨849860, by rfl⟩ : syracuseStep 1133147 = 1699721) B1699721
theorem B1133311 : Blo 1132632 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B3066623 : Blo 1132632 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B2870113 : Blo 1132632 2870113 := bstep (se 2 (by rfl) ⟨1076292, by rfl⟩ : syracuseStep 2870113 = 2152585) B2152585
theorem B27970433 : Blo 1132632 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B9686087 : Blo 1132632 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B1133735 : Blo 1132632 1133735 := bstep (se 1 (by rfl) ⟨850301, by rfl⟩ : syracuseStep 1133735 = 1700603) B1700603
theorem B29052107 : Blo 1132632 29052107 := bstep (se 1 (by rfl) ⟨21789080, by rfl⟩ : syracuseStep 29052107 = 43578161) B43578161
theorem B1134031 : Blo 1132632 1134031 := bstep (se 1 (by rfl) ⟨850523, by rfl⟩ : syracuseStep 1134031 = 1701047) B1701047
theorem B1134191 : Blo 1132632 1134191 := bstep (se 1 (by rfl) ⟨850643, by rfl⟩ : syracuseStep 1134191 = 1701287) B1701287
theorem B1134311 : Blo 1132632 1134311 := bstep (se 1 (by rfl) ⟨850733, by rfl⟩ : syracuseStep 1134311 = 1701467) B1701467
theorem B32755589 : Blo 1132632 32755589 := bstep (se 4 (by rfl) ⟨3070836, by rfl⟩ : syracuseStep 32755589 = 6141673) B6141673
theorem B1134619 : Blo 1132632 1134619 := bstep (se 1 (by rfl) ⟨850964, by rfl⟩ : syracuseStep 1134619 = 1701929) B1701929
theorem B1134639 : Blo 1132632 1134639 := bstep (se 1 (by rfl) ⟨850979, by rfl⟩ : syracuseStep 1134639 = 1701959) B1701959
theorem B2871359 : Blo 1132632 2871359 := bstep (se 1 (by rfl) ⟨2153519, by rfl⟩ : syracuseStep 2871359 = 4307039) B4307039
theorem B2871571 : Blo 1132632 2871571 := bstep (se 1 (by rfl) ⟨2153678, by rfl⟩ : syracuseStep 2871571 = 4307357) B4307357
theorem B1134895 : Blo 1132632 1134895 := bstep (se 1 (by rfl) ⟨851171, by rfl⟩ : syracuseStep 1134895 = 1702343) B1702343
theorem B1135039 : Blo 1132632 1135039 := bstep (se 1 (by rfl) ⟨851279, by rfl⟩ : syracuseStep 1135039 = 1702559) B1702559
theorem B14537231 : Blo 1132632 14537231 := bstep (se 1 (by rfl) ⟨10902923, by rfl⟩ : syracuseStep 14537231 = 21805847) B21805847
theorem B1135135 : Blo 1132632 1135135 := bstep (se 1 (by rfl) ⟨851351, by rfl⟩ : syracuseStep 1135135 = 1702703) B1702703
theorem B1135215 : Blo 1132632 1135215 := bstep (se 1 (by rfl) ⟨851411, by rfl⟩ : syracuseStep 1135215 = 1702823) B1702823
theorem B1135335 : Blo 1132632 1135335 := bstep (se 1 (by rfl) ⟨851501, by rfl⟩ : syracuseStep 1135335 = 1703003) B1703003
theorem B1135583 : Blo 1132632 1135583 := bstep (se 1 (by rfl) ⟨851687, by rfl⟩ : syracuseStep 1135583 = 1703375) B1703375
theorem B2872361 : Blo 1132632 2872361 := bstep (se 2 (by rfl) ⟨1077135, by rfl⟩ : syracuseStep 2872361 = 2154271) B2154271
theorem B1135839 : Blo 1132632 1135839 := bstep (se 1 (by rfl) ⟨851879, by rfl⟩ : syracuseStep 1135839 = 1703759) B1703759
theorem B1135919 : Blo 1132632 1135919 := bstep (se 1 (by rfl) ⟨851939, by rfl⟩ : syracuseStep 1135919 = 1703879) B1703879
theorem B4838723 : Blo 1132632 4838723 := bstep (se 1 (by rfl) ⟨3629042, by rfl⟩ : syracuseStep 4838723 = 7258085) B7258085
theorem B12932459 : Blo 1132632 12932459 := bstep (se 1 (by rfl) ⟨9699344, by rfl⟩ : syracuseStep 12932459 = 19398689) B19398689
theorem B4314617 : Blo 1132632 4314617 := bstep (se 2 (by rfl) ⟨1617981, by rfl⟩ : syracuseStep 4314617 = 3235963) B3235963
theorem B1136159 : Blo 1132632 1136159 := bstep (se 1 (by rfl) ⟨852119, by rfl⟩ : syracuseStep 1136159 = 1704239) B1704239
theorem B1136319 : Blo 1132632 1136319 := bstep (se 1 (by rfl) ⟨852239, by rfl⟩ : syracuseStep 1136319 = 1704479) B1704479
theorem B3823847 : Blo 1132632 3823847 := bstep (se 1 (by rfl) ⟨2867885, by rfl⟩ : syracuseStep 3823847 = 5735771) B5735771
theorem B2873627 : Blo 1132632 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B20666843 : Blo 1132632 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B10345103 : Blo 1132632 10345103 := bstep (se 1 (by rfl) ⟨7758827, by rfl⟩ : syracuseStep 10345103 = 15517655) B15517655
theorem B2874599 : Blo 1132632 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B2874953 : Blo 1132632 2874953 := bstep (se 2 (by rfl) ⟨1078107, by rfl⟩ : syracuseStep 2874953 = 2156215) B2156215
theorem B36789835 : Blo 1132632 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B13098935 : Blo 1132632 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B1433791 : Blo 1132632 1433791 := bstep (se 1 (by rfl) ⟨1075343, by rfl⟩ : syracuseStep 1433791 = 2150687) B2150687
theorem B7266617 : Blo 1132632 7266617 := bstep (se 2 (by rfl) ⟨2724981, by rfl⟩ : syracuseStep 7266617 = 5449963) B5449963
theorem B3826169 : Blo 1132632 3826169 := bstep (se 2 (by rfl) ⟨1434813, by rfl⟩ : syracuseStep 3826169 = 2869627) B2869627
theorem B2548457 : Blo 1132632 2548457 := bstep (se 2 (by rfl) ⟨955671, by rfl⟩ : syracuseStep 2548457 = 1911343) B1911343
theorem B2548745 : Blo 1132632 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B13788215 : Blo 1132632 13788215 := bstep (se 1 (by rfl) ⟨10341161, by rfl⟩ : syracuseStep 13788215 = 20682323) B20682323
theorem B11035705 : Blo 1132632 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B2549033 : Blo 1132632 2549033 := bstep (se 2 (by rfl) ⟨955887, by rfl⟩ : syracuseStep 2549033 = 1911775) B1911775
theorem B31024691 : Blo 1132632 31024691 := bstep (se 1 (by rfl) ⟨23268518, by rfl⟩ : syracuseStep 31024691 = 46537037) B46537037
theorem B13821491 : Blo 1132632 13821491 := bstep (se 1 (by rfl) ⟨10366118, by rfl⟩ : syracuseStep 13821491 = 20732237) B20732237
theorem B2549303 : Blo 1132632 2549303 := bstep (se 1 (by rfl) ⟨1911977, by rfl⟩ : syracuseStep 2549303 = 3823955) B3823955
theorem B2549663 : Blo 1132632 2549663 := bstep (se 1 (by rfl) ⟨1912247, by rfl⟩ : syracuseStep 2549663 = 3824495) B3824495
theorem B2549735 : Blo 1132632 2549735 := bstep (se 1 (by rfl) ⟨1912301, by rfl⟩ : syracuseStep 2549735 = 3824603) B3824603
theorem B2156519 : Blo 1132632 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B2549915 : Blo 1132632 2549915 := bstep (se 1 (by rfl) ⟨1912436, by rfl⟩ : syracuseStep 2549915 = 3824873) B3824873
theorem B2550095 : Blo 1132632 2550095 := bstep (se 1 (by rfl) ⟨1912571, by rfl⟩ : syracuseStep 2550095 = 3825143) B3825143
theorem B2550185 : Blo 1132632 2550185 := bstep (se 2 (by rfl) ⟨956319, by rfl⟩ : syracuseStep 2550185 = 1912639) B1912639
theorem B3828221 : Blo 1132632 3828221 := bstep (se 3 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 3828221 = 1435583) B1435583
theorem B1698953 : Blo 1132632 1698953 := bstep (se 2 (by rfl) ⟨637107, by rfl⟩ : syracuseStep 1698953 = 1274215) B1274215
theorem B1699007 : Blo 1132632 1699007 := bstep (se 1 (by rfl) ⟨1274255, by rfl⟩ : syracuseStep 1699007 = 2548511) B2548511
theorem B1436879 : Blo 1132632 1436879 := bstep (se 1 (by rfl) ⟨1077659, by rfl⟩ : syracuseStep 1436879 = 2155319) B2155319
theorem B3632539 : Blo 1132632 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B1699547 : Blo 1132632 1699547 := bstep (se 1 (by rfl) ⟨1274660, by rfl⟩ : syracuseStep 1699547 = 2549321) B2549321
theorem B1699817 : Blo 1132632 1699817 := bstep (se 2 (by rfl) ⟨637431, by rfl⟩ : syracuseStep 1699817 = 1274863) B1274863
theorem B1699835 : Blo 1132632 1699835 := bstep (se 1 (by rfl) ⟨1274876, by rfl⟩ : syracuseStep 1699835 = 2549753) B2549753
theorem B1699871 : Blo 1132632 1699871 := bstep (se 1 (by rfl) ⟨1274903, by rfl⟩ : syracuseStep 1699871 = 2549807) B2549807
theorem B1699895 : Blo 1132632 1699895 := bstep (se 1 (by rfl) ⟨1274921, by rfl⟩ : syracuseStep 1699895 = 2549843) B2549843
theorem B4092029 : Blo 1132632 4092029 := bstep (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) B1534511
theorem B1437851 : Blo 1132632 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1700015 : Blo 1132632 1700015 := bstep (se 1 (by rfl) ⟨1275011, by rfl⟩ : syracuseStep 1700015 = 2550023) B2550023
theorem B23294141 : Blo 1132632 23294141 := bstep (se 3 (by rfl) ⟨4367651, by rfl⟩ : syracuseStep 23294141 = 8735303) B8735303
theorem B6451559 : Blo 1132632 6451559 := bstep (se 1 (by rfl) ⟨4838669, by rfl⟩ : syracuseStep 6451559 = 9677339) B9677339
theorem B1700219 : Blo 1132632 1700219 := bstep (se 1 (by rfl) ⟨1275164, by rfl⟩ : syracuseStep 1700219 = 2550329) B2550329
theorem B9105847 : Blo 1132632 9105847 := bstep (se 1 (by rfl) ⟨6829385, by rfl⟩ : syracuseStep 9105847 = 13658771) B13658771
theorem B12939749 : Blo 1132632 12939749 := bstep (se 4 (by rfl) ⟨1213101, by rfl⟩ : syracuseStep 12939749 = 2426203) B2426203
theorem B1700489 : Blo 1132632 1700489 := bstep (se 2 (by rfl) ⟨637683, by rfl⟩ : syracuseStep 1700489 = 1275367) B1275367
theorem B1700699 : Blo 1132632 1700699 := bstep (se 1 (by rfl) ⟨1275524, by rfl⟩ : syracuseStep 1700699 = 2551049) B2551049
theorem B1700729 : Blo 1132632 1700729 := bstep (se 2 (by rfl) ⟨637773, by rfl⟩ : syracuseStep 1700729 = 1275547) B1275547
theorem B3634271 : Blo 1132632 3634271 := bstep (se 1 (by rfl) ⟨2725703, by rfl⟩ : syracuseStep 3634271 = 5451407) B5451407
theorem B1701359 : Blo 1132632 1701359 := bstep (se 1 (by rfl) ⟨1276019, by rfl⟩ : syracuseStep 1701359 = 2552039) B2552039
theorem B1701479 : Blo 1132632 1701479 := bstep (se 1 (by rfl) ⟨1276109, by rfl⟩ : syracuseStep 1701479 = 2552219) B2552219
theorem B6453017 : Blo 1132632 6453017 := bstep (se 2 (by rfl) ⟨2419881, by rfl⟩ : syracuseStep 6453017 = 4839763) B4839763
theorem B1275871 : Blo 1132632 1275871 := bstep (se 1 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 1275871 = 1913807) B1913807
theorem B1701935 : Blo 1132632 1701935 := bstep (se 1 (by rfl) ⟨1276451, by rfl⟩ : syracuseStep 1701935 = 2552903) B2552903
theorem B2553911 : Blo 1132632 2553911 := bstep (se 1 (by rfl) ⟨1915433, by rfl⟩ : syracuseStep 2553911 = 3830867) B3830867
theorem B1702055 : Blo 1132632 1702055 := bstep (se 1 (by rfl) ⟨1276541, by rfl⟩ : syracuseStep 1702055 = 2553083) B2553083
theorem B1702199 : Blo 1132632 1702199 := bstep (se 1 (by rfl) ⟨1276649, by rfl⟩ : syracuseStep 1702199 = 2553299) B2553299
theorem B2554271 : Blo 1132632 2554271 := bstep (se 1 (by rfl) ⟨1915703, by rfl⟩ : syracuseStep 2554271 = 3831407) B3831407
theorem B1702379 : Blo 1132632 1702379 := bstep (se 1 (by rfl) ⟨1276784, by rfl⟩ : syracuseStep 1702379 = 2553569) B2553569
theorem B3635705 : Blo 1132632 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B1702727 : Blo 1132632 1702727 := bstep (se 1 (by rfl) ⟨1277045, by rfl⟩ : syracuseStep 1702727 = 2554091) B2554091
theorem B1211359 : Blo 1132632 1211359 := bstep (se 1 (by rfl) ⟨908519, by rfl⟩ : syracuseStep 1211359 = 1817039) B1817039
theorem B2554847 : Blo 1132632 2554847 := bstep (se 1 (by rfl) ⟨1916135, by rfl⟩ : syracuseStep 2554847 = 3832271) B3832271
theorem B1277023 : Blo 1132632 1277023 := bstep (se 1 (by rfl) ⟨957767, by rfl⟩ : syracuseStep 1277023 = 1915535) B1915535
theorem B1211803 : Blo 1132632 1211803 := bstep (se 1 (by rfl) ⟨908852, by rfl⟩ : syracuseStep 1211803 = 1817705) B1817705
theorem B3833243 : Blo 1132632 3833243 := bstep (se 1 (by rfl) ⟨2874932, by rfl⟩ : syracuseStep 3833243 = 5749865) B5749865
theorem B2555369 : Blo 1132632 2555369 := bstep (se 2 (by rfl) ⟨958263, by rfl⟩ : syracuseStep 2555369 = 1916527) B1916527
theorem B1703561 : Blo 1132632 1703561 := bstep (se 2 (by rfl) ⟨638835, by rfl⟩ : syracuseStep 1703561 = 1277671) B1277671
theorem B2424487 : Blo 1132632 2424487 := bstep (se 1 (by rfl) ⟨1818365, by rfl⟩ : syracuseStep 2424487 = 3636731) B3636731
theorem B1703591 : Blo 1132632 1703591 := bstep (se 1 (by rfl) ⟨1277693, by rfl⟩ : syracuseStep 1703591 = 2555387) B2555387
theorem B1703711 : Blo 1132632 1703711 := bstep (se 1 (by rfl) ⟨1277783, by rfl⟩ : syracuseStep 1703711 = 2555567) B2555567
theorem B1703771 : Blo 1132632 1703771 := bstep (se 1 (by rfl) ⟨1277828, by rfl⟩ : syracuseStep 1703771 = 2555657) B2555657
theorem B12287933 : Blo 1132632 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B377323535 : Blo 1132632 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B3637487 : Blo 1132632 3637487 := bstep (se 1 (by rfl) ⟨2728115, by rfl⟩ : syracuseStep 3637487 = 5456231) B5456231
theorem B4096295 : Blo 1132632 4096295 := bstep (se 1 (by rfl) ⟨3072221, by rfl⟩ : syracuseStep 4096295 = 6144443) B6144443
theorem B3834269 : Blo 1132632 3834269 := bstep (se 3 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 3834269 = 1437851) B1437851
theorem B3834323 : Blo 1132632 3834323 := bstep (se 1 (by rfl) ⟨2875742, by rfl⟩ : syracuseStep 3834323 = 5751485) B5751485
theorem B9700235 : Blo 1132632 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B1639583 : Blo 1132632 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B14714273 : Blo 1132632 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B18646955 : Blo 1132632 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B6555563 : Blo 1132632 6555563 := bstep (se 1 (by rfl) ⟨4916672, by rfl⟩ : syracuseStep 6555563 = 9833345) B9833345
theorem B6457391 : Blo 1132632 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B19368071 : Blo 1132632 19368071 := bstep (se 1 (by rfl) ⟨14526053, by rfl⟩ : syracuseStep 19368071 = 29052107) B29052107
theorem B4917503 : Blo 1132632 4917503 := bstep (se 1 (by rfl) ⟨3688127, by rfl⟩ : syracuseStep 4917503 = 7376255) B7376255
theorem B48564517 : Blo 1132632 48564517 := bstep (se 4 (by rfl) ⟨4552923, by rfl⟩ : syracuseStep 48564517 = 9105847) B9105847
theorem B7277789 : Blo 1132632 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B8621639 : Blo 1132632 8621639 := bstep (se 1 (by rfl) ⟨6466229, by rfl⟩ : syracuseStep 8621639 = 12932459) B12932459
theorem B19403063 : Blo 1132632 19403063 := bstep (se 1 (by rfl) ⟨14552297, by rfl⟩ : syracuseStep 19403063 = 29104595) B29104595
theorem B23270075 : Blo 1132632 23270075 := bstep (se 1 (by rfl) ⟨17452556, by rfl⟩ : syracuseStep 23270075 = 34905113) B34905113
theorem B7279739 : Blo 1132632 7279739 := bstep (se 1 (by rfl) ⟨5459804, by rfl⟩ : syracuseStep 7279739 = 10919609) B10919609
theorem B20683127 : Blo 1132632 20683127 := bstep (se 1 (by rfl) ⟨15512345, by rfl⟩ : syracuseStep 20683127 = 31024691) B31024691
theorem B9214327 : Blo 1132632 9214327 := bstep (se 1 (by rfl) ⟨6910745, by rfl⟩ : syracuseStep 9214327 = 13821491) B13821491
theorem B5741441 : Blo 1132632 5741441 := bstep (se 2 (by rfl) ⟨2153040, by rfl⟩ : syracuseStep 5741441 = 4306081) B4306081
theorem B6462949 : Blo 1132632 6462949 := bstep (se 4 (by rfl) ⟨605901, by rfl⟩ : syracuseStep 6462949 = 1211803) B1211803
theorem B9706999 : Blo 1132632 9706999 := bstep (se 1 (by rfl) ⟨7280249, by rfl⟩ : syracuseStep 9706999 = 14560499) B14560499
theorem B3874871 : Blo 1132632 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B2728019 : Blo 1132632 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B4301039 : Blo 1132632 4301039 := bstep (se 1 (by rfl) ⟨3225779, by rfl⟩ : syracuseStep 4301039 = 6451559) B6451559
theorem B8626499 : Blo 1132632 8626499 := bstep (se 1 (by rfl) ⟨6469874, by rfl⟩ : syracuseStep 8626499 = 12939749) B12939749
theorem B4302011 : Blo 1132632 4302011 := bstep (se 1 (by rfl) ⟨3226508, by rfl⟩ : syracuseStep 4302011 = 6453017) B6453017
theorem B1615145 : Blo 1132632 1615145 := bstep (se 2 (by rfl) ⟨605679, by rfl⟩ : syracuseStep 1615145 = 1211359) B1211359
theorem B132458287 : Blo 1132632 132458287 := bstep (se 1 (by rfl) ⟨99343715, by rfl⟩ : syracuseStep 132458287 = 198687431) B198687431
theorem B13118105 : Blo 1132632 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B1911451 : Blo 1132632 1911451 := bstep (se 1 (by rfl) ⟨1433588, by rfl⟩ : syracuseStep 1911451 = 2867177) B2867177
theorem B5745491 : Blo 1132632 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B1911721 : Blo 1132632 1911721 := bstep (se 2 (by rfl) ⟨716895, by rfl⟩ : syracuseStep 1911721 = 1433791) B1433791
theorem B1911863 : Blo 1132632 1911863 := bstep (se 1 (by rfl) ⟨1433897, by rfl⟩ : syracuseStep 1911863 = 2867795) B2867795
theorem B4369747 : Blo 1132632 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B1912423 : Blo 1132632 1912423 := bstep (se 1 (by rfl) ⟨1434317, by rfl⟩ : syracuseStep 1912423 = 2868635) B2868635
theorem B1618255 : Blo 1132632 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B2044415 : Blo 1132632 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B12432001 : Blo 1132632 12432001 := bstep (se 2 (by rfl) ⟨4662000, by rfl⟩ : syracuseStep 12432001 = 9324001) B9324001
theorem B5747435 : Blo 1132632 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B5452541 : Blo 1132632 5452541 := bstep (se 3 (by rfl) ⟨1022351, by rfl⟩ : syracuseStep 5452541 = 2044703) B2044703
theorem B4305899 : Blo 1132632 4305899 := bstep (se 1 (by rfl) ⟨3229424, by rfl⟩ : syracuseStep 4305899 = 6458849) B6458849
theorem B11646119 : Blo 1132632 11646119 := bstep (se 1 (by rfl) ⟨8734589, by rfl⟩ : syracuseStep 11646119 = 17469179) B17469179
theorem B55227581 : Blo 1132632 55227581 := bstep (se 3 (by rfl) ⟨10355171, by rfl⟩ : syracuseStep 55227581 = 20710343) B20710343
theorem B8172751 : Blo 1132632 8172751 := bstep (se 1 (by rfl) ⟨6129563, by rfl⟩ : syracuseStep 8172751 = 12259127) B12259127
theorem B21837059 : Blo 1132632 21837059 := bstep (se 1 (by rfl) ⟨16377794, by rfl⟩ : syracuseStep 21837059 = 32755589) B32755589
theorem B1914239 : Blo 1132632 1914239 := bstep (se 1 (by rfl) ⟨1435679, by rfl⟩ : syracuseStep 1914239 = 2871359) B2871359
theorem B1914907 : Blo 1132632 1914907 := bstep (se 1 (by rfl) ⟨1436180, by rfl⟩ : syracuseStep 1914907 = 2872361) B2872361
theorem B3225815 : Blo 1132632 3225815 := bstep (se 1 (by rfl) ⟨2419361, by rfl⟩ : syracuseStep 3225815 = 4838723) B4838723
theorem B13810009 : Blo 1132632 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B8174135 : Blo 1132632 8174135 := bstep (se 1 (by rfl) ⟨6130601, by rfl⟩ : syracuseStep 8174135 = 12261203) B12261203
theorem B1915751 : Blo 1132632 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B13777895 : Blo 1132632 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B6896735 : Blo 1132632 6896735 := bstep (se 1 (by rfl) ⟨5172551, by rfl⟩ : syracuseStep 6896735 = 10345103) B10345103
theorem B1916399 : Blo 1132632 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B1916635 : Blo 1132632 1916635 := bstep (se 1 (by rfl) ⟨1437476, by rfl⟩ : syracuseStep 1916635 = 2874953) B2874953
theorem B4308815 : Blo 1132632 4308815 := bstep (se 1 (by rfl) ⟨3231611, by rfl⟩ : syracuseStep 4308815 = 6463223) B6463223
theorem B8732623 : Blo 1132632 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B41369885 : Blo 1132632 41369885 := bstep (se 3 (by rfl) ⟨7756853, by rfl⟩ : syracuseStep 41369885 = 15513707) B15513707
theorem B4309483 : Blo 1132632 4309483 := bstep (se 1 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 4309483 = 6464225) B6464225
theorem B1819115 : Blo 1132632 1819115 := bstep (se 1 (by rfl) ⟨1364336, by rfl⟩ : syracuseStep 1819115 = 2728673) B2728673
theorem B9192143 : Blo 1132632 9192143 := bstep (se 1 (by rfl) ⟨6894107, by rfl⟩ : syracuseStep 9192143 = 13788215) B13788215
theorem B2868767 : Blo 1132632 2868767 := bstep (se 1 (by rfl) ⟨2151575, by rfl⟩ : syracuseStep 2868767 = 4303151) B4303151
theorem B2868979 : Blo 1132632 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B1132635 : Blo 1132632 1132635 := bstep (se 1 (by rfl) ⟨849476, by rfl⟩ : syracuseStep 1132635 = 1698953) B1698953
theorem B1132671 : Blo 1132632 1132671 := bstep (se 1 (by rfl) ⟨849503, by rfl⟩ : syracuseStep 1132671 = 1699007) B1699007
theorem B1133031 : Blo 1132632 1133031 := bstep (se 1 (by rfl) ⟨849773, by rfl⟩ : syracuseStep 1133031 = 1699547) B1699547
theorem B2869739 : Blo 1132632 2869739 := bstep (se 1 (by rfl) ⟨2152304, by rfl⟩ : syracuseStep 2869739 = 4304609) B4304609
theorem B1133211 : Blo 1132632 1133211 := bstep (se 1 (by rfl) ⟨849908, by rfl⟩ : syracuseStep 1133211 = 1699817) B1699817
theorem B1133223 : Blo 1132632 1133223 := bstep (se 1 (by rfl) ⟨849917, by rfl⟩ : syracuseStep 1133223 = 1699835) B1699835
theorem B1133247 : Blo 1132632 1133247 := bstep (se 1 (by rfl) ⟨849935, by rfl⟩ : syracuseStep 1133247 = 1699871) B1699871
theorem B1133263 : Blo 1132632 1133263 := bstep (se 1 (by rfl) ⟨849947, by rfl⟩ : syracuseStep 1133263 = 1699895) B1699895
theorem B1133343 : Blo 1132632 1133343 := bstep (se 1 (by rfl) ⟨850007, by rfl⟩ : syracuseStep 1133343 = 1700015) B1700015
theorem B1133479 : Blo 1132632 1133479 := bstep (se 1 (by rfl) ⟨850109, by rfl⟩ : syracuseStep 1133479 = 1700219) B1700219
theorem B1133659 : Blo 1132632 1133659 := bstep (se 1 (by rfl) ⟨850244, by rfl⟩ : syracuseStep 1133659 = 1700489) B1700489
theorem B1133799 : Blo 1132632 1133799 := bstep (se 1 (by rfl) ⟨850349, by rfl⟩ : syracuseStep 1133799 = 1700699) B1700699
theorem B1133819 : Blo 1132632 1133819 := bstep (se 1 (by rfl) ⟨850364, by rfl⟩ : syracuseStep 1133819 = 1700729) B1700729
theorem B1134239 : Blo 1132632 1134239 := bstep (se 1 (by rfl) ⟨850679, by rfl⟩ : syracuseStep 1134239 = 1701359) B1701359
theorem B1134319 : Blo 1132632 1134319 := bstep (se 1 (by rfl) ⟨850739, by rfl⟩ : syracuseStep 1134319 = 1701479) B1701479
theorem B1134623 : Blo 1132632 1134623 := bstep (se 1 (by rfl) ⟨850967, by rfl⟩ : syracuseStep 1134623 = 1701935) B1701935
theorem B4313159 : Blo 1132632 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B1134703 : Blo 1132632 1134703 := bstep (se 1 (by rfl) ⟨851027, by rfl⟩ : syracuseStep 1134703 = 1702055) B1702055
theorem B1134799 : Blo 1132632 1134799 := bstep (se 1 (by rfl) ⟨851099, by rfl⟩ : syracuseStep 1134799 = 1702199) B1702199
theorem B1134919 : Blo 1132632 1134919 := bstep (se 1 (by rfl) ⟨851189, by rfl⟩ : syracuseStep 1134919 = 1702379) B1702379
theorem B1135151 : Blo 1132632 1135151 := bstep (se 1 (by rfl) ⟨851363, by rfl⟩ : syracuseStep 1135151 = 1702727) B1702727
theorem B3232649 : Blo 1132632 3232649 := bstep (se 2 (by rfl) ⟨1212243, by rfl⟩ : syracuseStep 3232649 = 2424487) B2424487
theorem B1135707 : Blo 1132632 1135707 := bstep (se 1 (by rfl) ⟨851780, by rfl⟩ : syracuseStep 1135707 = 1703561) B1703561
theorem B1135727 : Blo 1132632 1135727 := bstep (se 1 (by rfl) ⟨851795, by rfl⟩ : syracuseStep 1135727 = 1703591) B1703591
theorem B1135807 : Blo 1132632 1135807 := bstep (se 1 (by rfl) ⟨851855, by rfl⟩ : syracuseStep 1135807 = 1703711) B1703711
theorem B1135847 : Blo 1132632 1135847 := bstep (se 1 (by rfl) ⟨851885, by rfl⟩ : syracuseStep 1135847 = 1703771) B1703771
theorem B2151659 : Blo 1132632 2151659 := bstep (se 1 (by rfl) ⟨1613744, by rfl⟩ : syracuseStep 2151659 = 3227489) B3227489
theorem B1136127 : Blo 1132632 1136127 := bstep (se 1 (by rfl) ⟨852095, by rfl⟩ : syracuseStep 1136127 = 1704191) B1704191
theorem B1136231 : Blo 1132632 1136231 := bstep (se 1 (by rfl) ⟨852173, by rfl⟩ : syracuseStep 1136231 = 1704347) B1704347
theorem B4314815 : Blo 1132632 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B1136511 : Blo 1132632 1136511 := bstep (se 1 (by rfl) ⟨852383, by rfl⟩ : syracuseStep 1136511 = 1704767) B1704767
theorem B1136607 : Blo 1132632 1136607 := bstep (se 1 (by rfl) ⟨852455, by rfl⟩ : syracuseStep 1136607 = 1704911) B1704911
theorem B4839421 : Blo 1132632 4839421 := bstep (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) B1814783
theorem B4315133 : Blo 1132632 4315133 := bstep (se 3 (by rfl) ⟨809087, by rfl⟩ : syracuseStep 4315133 = 1618175) B1618175
theorem B8181809 : Blo 1132632 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B2152631 : Blo 1132632 2152631 := bstep (se 1 (by rfl) ⟨1614473, by rfl⟩ : syracuseStep 2152631 = 3228947) B3228947
theorem B17455337 : Blo 1132632 17455337 := bstep (se 2 (by rfl) ⟨6545751, by rfl⟩ : syracuseStep 17455337 = 13091503) B13091503
theorem B3824441 : Blo 1132632 3824441 := bstep (se 2 (by rfl) ⟨1434165, by rfl⟩ : syracuseStep 3824441 = 2868331) B2868331
theorem B19389941 : Blo 1132632 19389941 := bstep (se 5 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 19389941 = 1817807) B1817807
theorem B3825575 : Blo 1132632 3825575 := bstep (se 1 (by rfl) ⟨2869181, by rfl⟩ : syracuseStep 3825575 = 5738363) B5738363
theorem B20733985 : Blo 1132632 20733985 := bstep (se 2 (by rfl) ⟨7775244, by rfl⟩ : syracuseStep 20733985 = 15550489) B15550489
theorem B3235895 : Blo 1132632 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B3825899 : Blo 1132632 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B9691487 : Blo 1132632 9691487 := bstep (se 1 (by rfl) ⟨7268615, by rfl⟩ : syracuseStep 9691487 = 14537231) B14537231
theorem B7758443 : Blo 1132632 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B3826439 : Blo 1132632 3826439 := bstep (se 1 (by rfl) ⟨2869829, by rfl⟩ : syracuseStep 3826439 = 5739659) B5739659
theorem B2876411 : Blo 1132632 2876411 := bstep (se 1 (by rfl) ⟨2157308, by rfl⟩ : syracuseStep 2876411 = 4314617) B4314617
theorem B16344119 : Blo 1132632 16344119 := bstep (se 1 (by rfl) ⟨12258089, by rfl⟩ : syracuseStep 16344119 = 24516179) B24516179
theorem B3826817 : Blo 1132632 3826817 := bstep (se 2 (by rfl) ⟨1435056, by rfl⟩ : syracuseStep 3826817 = 2870113) B2870113
theorem B1533343 : Blo 1132632 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B2549231 : Blo 1132632 2549231 := bstep (se 1 (by rfl) ⟨1911923, by rfl⟩ : syracuseStep 2549231 = 3823847) B3823847
theorem B33121979 : Blo 1132632 33121979 := bstep (se 1 (by rfl) ⟨24841484, by rfl⟩ : syracuseStep 33121979 = 49682969) B49682969
theorem B3827519 : Blo 1132632 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B4843385 : Blo 1132632 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B7760555 : Blo 1132632 7760555 := bstep (se 1 (by rfl) ⟨5820416, by rfl⟩ : syracuseStep 7760555 = 11640833) B11640833
theorem B4844411 : Blo 1132632 4844411 := bstep (se 1 (by rfl) ⟨3633308, by rfl⟩ : syracuseStep 4844411 = 7266617) B7266617
theorem B2550779 : Blo 1132632 2550779 := bstep (se 1 (by rfl) ⟨1913084, by rfl⟩ : syracuseStep 2550779 = 3826169) B3826169
theorem B3828761 : Blo 1132632 3828761 := bstep (se 2 (by rfl) ⟨1435785, by rfl⟩ : syracuseStep 3828761 = 2871571) B2871571
theorem B1698971 : Blo 1132632 1698971 := bstep (se 1 (by rfl) ⟨1274228, by rfl⟩ : syracuseStep 1698971 = 2548457) B2548457
theorem B1699163 : Blo 1132632 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B1699355 : Blo 1132632 1699355 := bstep (se 1 (by rfl) ⟨1274516, by rfl⟩ : syracuseStep 1699355 = 2549033) B2549033
theorem B1699535 : Blo 1132632 1699535 := bstep (se 1 (by rfl) ⟨1274651, by rfl⟩ : syracuseStep 1699535 = 2549303) B2549303
theorem B1699775 : Blo 1132632 1699775 := bstep (se 1 (by rfl) ⟨1274831, by rfl⟩ : syracuseStep 1699775 = 2549663) B2549663
theorem B9695213 : Blo 1132632 9695213 := bstep (se 3 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 9695213 = 3635705) B3635705
theorem B1699823 : Blo 1132632 1699823 := bstep (se 1 (by rfl) ⟨1274867, by rfl⟩ : syracuseStep 1699823 = 2549735) B2549735
theorem B1437679 : Blo 1132632 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B1699943 : Blo 1132632 1699943 := bstep (se 1 (by rfl) ⟨1274957, by rfl⟩ : syracuseStep 1699943 = 2549915) B2549915
theorem B1700063 : Blo 1132632 1700063 := bstep (se 1 (by rfl) ⟨1275047, by rfl⟩ : syracuseStep 1700063 = 2550095) B2550095
theorem B2552057 : Blo 1132632 2552057 := bstep (se 2 (by rfl) ⟨957021, by rfl⟩ : syracuseStep 2552057 = 1914043) B1914043
theorem B1700123 : Blo 1132632 1700123 := bstep (se 1 (by rfl) ⟨1275092, by rfl⟩ : syracuseStep 1700123 = 2550185) B2550185
theorem B2552147 : Blo 1132632 2552147 := bstep (se 1 (by rfl) ⟨1914110, by rfl⟩ : syracuseStep 2552147 = 3828221) B3828221
theorem B3830975 : Blo 1132632 3830975 := bstep (se 1 (by rfl) ⟨2873231, by rfl⟩ : syracuseStep 3830975 = 5746463) B5746463
theorem B1701161 : Blo 1132632 1701161 := bstep (se 2 (by rfl) ⟨637935, by rfl⟩ : syracuseStep 1701161 = 1275871) B1275871
theorem B15529427 : Blo 1132632 15529427 := bstep (se 1 (by rfl) ⟨11647070, by rfl⟩ : syracuseStep 15529427 = 23294141) B23294141
theorem B3831515 : Blo 1132632 3831515 := bstep (se 1 (by rfl) ⟨2873636, by rfl⟩ : syracuseStep 3831515 = 5747273) B5747273
theorem B3831677 : Blo 1132632 3831677 := bstep (se 3 (by rfl) ⟨718439, by rfl⟩ : syracuseStep 3831677 = 1436879) B1436879
theorem B8615807 : Blo 1132632 8615807 := bstep (se 1 (by rfl) ⟨6461855, by rfl⟩ : syracuseStep 8615807 = 12923711) B12923711
theorem B2422847 : Blo 1132632 2422847 := bstep (se 1 (by rfl) ⟨1817135, by rfl⟩ : syracuseStep 2422847 = 3634271) B3634271
theorem B3635513 : Blo 1132632 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B1210727 : Blo 1132632 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B2554361 : Blo 1132632 2554361 := bstep (se 2 (by rfl) ⟨957885, by rfl⟩ : syracuseStep 2554361 = 1915771) B1915771
theorem B1276519 : Blo 1132632 1276519 := bstep (se 1 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 1276519 = 1914779) B1914779
theorem B1702607 : Blo 1132632 1702607 := bstep (se 1 (by rfl) ⟨1276955, by rfl⟩ : syracuseStep 1702607 = 2553911) B2553911
theorem B1702697 : Blo 1132632 1702697 := bstep (se 2 (by rfl) ⟨638511, by rfl⟩ : syracuseStep 1702697 = 1277023) B1277023
theorem B1702847 : Blo 1132632 1702847 := bstep (se 1 (by rfl) ⟨1277135, by rfl⟩ : syracuseStep 1702847 = 2554271) B2554271
theorem B3832811 : Blo 1132632 3832811 := bstep (se 1 (by rfl) ⟨2874608, by rfl⟩ : syracuseStep 3832811 = 5749217) B5749217
theorem B1703231 : Blo 1132632 1703231 := bstep (se 1 (by rfl) ⟨1277423, by rfl⟩ : syracuseStep 1703231 = 2554847) B2554847
theorem B49053113 : Blo 1132632 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B2555495 : Blo 1132632 2555495 := bstep (se 1 (by rfl) ⟨1916621, by rfl⟩ : syracuseStep 2555495 = 3833243) B3833243
theorem B1703579 : Blo 1132632 1703579 := bstep (se 1 (by rfl) ⟨1277684, by rfl⟩ : syracuseStep 1703579 = 2555369) B2555369
theorem B1277887 : Blo 1132632 1277887 := bstep (se 1 (by rfl) ⟨958415, by rfl⟩ : syracuseStep 1277887 = 1916831) B1916831
theorem B8191955 : Blo 1132632 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B2424991 : Blo 1132632 2424991 := bstep (se 1 (by rfl) ⟨1818743, by rfl⟩ : syracuseStep 2424991 = 3637487) B3637487
theorem B2556179 : Blo 1132632 2556179 := bstep (se 1 (by rfl) ⟨1917134, by rfl⟩ : syracuseStep 2556179 = 3834269) B3834269
theorem B2556215 : Blo 1132632 2556215 := bstep (se 1 (by rfl) ⟨1917161, by rfl⟩ : syracuseStep 2556215 = 3834323) B3834323
theorem B1212743 : Blo 1132632 1212743 := bstep (se 1 (by rfl) ⟨909557, by rfl⟩ : syracuseStep 1212743 = 1819115) B1819115
theorem B6128095 : Blo 1132632 6128095 := bstep (se 1 (by rfl) ⟨4596071, by rfl⟩ : syracuseStep 6128095 = 9192143) B9192143
theorem B12912047 : Blo 1132632 12912047 := bstep (se 1 (by rfl) ⟨9684035, by rfl⟩ : syracuseStep 12912047 = 19368071) B19368071
theorem B3278335 : Blo 1132632 3278335 := bstep (se 1 (by rfl) ⟨2458751, by rfl⟩ : syracuseStep 3278335 = 4917503) B4917503
theorem B64752689 : Blo 1132632 64752689 := bstep (se 2 (by rfl) ⟨24282258, by rfl⟩ : syracuseStep 64752689 = 48564517) B48564517
theorem B4853159 : Blo 1132632 4853159 := bstep (se 1 (by rfl) ⟨3639869, by rfl⟩ : syracuseStep 4853159 = 7279739) B7279739
theorem B11636891 : Blo 1132632 11636891 := bstep (se 1 (by rfl) ⟨8727668, by rfl⟩ : syracuseStep 11636891 = 17455337) B17455337
theorem B6460991 : Blo 1132632 6460991 := bstep (se 1 (by rfl) ⟨4845743, by rfl⟩ : syracuseStep 6460991 = 9691487) B9691487
theorem B21797693 : Blo 1132632 21797693 := bstep (se 3 (by rfl) ⟨4087067, by rfl⟩ : syracuseStep 21797693 = 8174135) B8174135
theorem B36741053 : Blo 1132632 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B6463475 : Blo 1132632 6463475 := bstep (se 1 (by rfl) ⟨4847606, by rfl⟩ : syracuseStep 6463475 = 9695213) B9695213
theorem B19407437 : Blo 1132632 19407437 := bstep (se 3 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 19407437 = 7277789) B7277789
theorem B14558039 : Blo 1132632 14558039 := bstep (se 1 (by rfl) ⟨10918529, by rfl⟩ : syracuseStep 14558039 = 21837059) B21837059
theorem B5743871 : Blo 1132632 5743871 := bstep (se 1 (by rfl) ⟨4307903, by rfl⟩ : syracuseStep 5743871 = 8615807) B8615807
theorem B1615231 : Blo 1132632 1615231 := bstep (se 1 (by rfl) ⟨1211423, by rfl⟩ : syracuseStep 1615231 = 2422847) B2422847
theorem B4597823 : Blo 1132632 4597823 := bstep (se 1 (by rfl) ⟨3448367, by rfl⟩ : syracuseStep 4597823 = 6896735) B6896735
theorem B11643497 : Blo 1132632 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B2730863 : Blo 1132632 2730863 := bstep (se 1 (by rfl) ⟨2048147, by rfl⟩ : syracuseStep 2730863 = 4096295) B4096295
theorem B6466823 : Blo 1132632 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B5745977 : Blo 1132632 5745977 := bstep (se 2 (by rfl) ⟨2154741, by rfl⟩ : syracuseStep 5745977 = 4309483) B4309483
theorem B9809515 : Blo 1132632 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B1912511 : Blo 1132632 1912511 := bstep (se 1 (by rfl) ⟨1434383, by rfl⟩ : syracuseStep 1912511 = 2868767) B2868767
theorem B12431303 : Blo 1132632 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B4370375 : Blo 1132632 4370375 := bstep (se 1 (by rfl) ⟨3277781, by rfl⟩ : syracuseStep 4370375 = 6555563) B6555563
theorem B4304927 : Blo 1132632 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B20689181 : Blo 1132632 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B1913159 : Blo 1132632 1913159 := bstep (se 1 (by rfl) ⟨1434869, by rfl⟩ : syracuseStep 1913159 = 2869739) B2869739
theorem B2044457 : Blo 1132632 2044457 := bstep (se 2 (by rfl) ⟨766671, by rfl⟩ : syracuseStep 2044457 = 1533343) B1533343
theorem B5747759 : Blo 1132632 5747759 := bstep (se 1 (by rfl) ⟨4310819, by rfl⟩ : syracuseStep 5747759 = 8621639) B8621639
theorem B15513383 : Blo 1132632 15513383 := bstep (se 1 (by rfl) ⟨11635037, by rfl⟩ : syracuseStep 15513383 = 23270075) B23270075
theorem B4307053 : Blo 1132632 4307053 := bstep (se 3 (by rfl) ⟨807572, by rfl⟩ : syracuseStep 4307053 = 1615145) B1615145
theorem B5454539 : Blo 1132632 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B12926627 : Blo 1132632 12926627 := bstep (se 1 (by rfl) ⟨9694970, by rfl⟩ : syracuseStep 12926627 = 19389941) B19389941
theorem B1916905 : Blo 1132632 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B1818679 : Blo 1132632 1818679 := bstep (se 1 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 1818679 = 2728019) B2728019
theorem B2867359 : Blo 1132632 2867359 := bstep (se 1 (by rfl) ⟨2150519, by rfl⟩ : syracuseStep 2867359 = 4301039) B4301039
theorem B5750999 : Blo 1132632 5750999 := bstep (se 1 (by rfl) ⟨4313249, by rfl⟩ : syracuseStep 5750999 = 8626499) B8626499
theorem B1917607 : Blo 1132632 1917607 := bstep (se 1 (by rfl) ⟨1438205, by rfl⟩ : syracuseStep 1917607 = 2876411) B2876411
theorem B10896079 : Blo 1132632 10896079 := bstep (se 1 (by rfl) ⟨8172059, by rfl⟩ : syracuseStep 10896079 = 16344119) B16344119
theorem B2868007 : Blo 1132632 2868007 := bstep (se 1 (by rfl) ⟨2151005, by rfl⟩ : syracuseStep 2868007 = 4302011) B4302011
theorem B3228605 : Blo 1132632 3228605 := bstep (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) B1210727
theorem B3228923 : Blo 1132632 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B10897001 : Blo 1132632 10897001 := bstep (se 2 (by rfl) ⟨4086375, by rfl⟩ : syracuseStep 10897001 = 8172751) B8172751
theorem B3229607 : Blo 1132632 3229607 := bstep (se 1 (by rfl) ⟨2422205, by rfl⟩ : syracuseStep 3229607 = 4844411) B4844411
theorem B1132647 : Blo 1132632 1132647 := bstep (se 1 (by rfl) ⟨849485, by rfl⟩ : syracuseStep 1132647 = 1698971) B1698971
theorem B1132775 : Blo 1132632 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B1132903 : Blo 1132632 1132903 := bstep (se 1 (by rfl) ⟨849677, by rfl⟩ : syracuseStep 1132903 = 1699355) B1699355
theorem B1133023 : Blo 1132632 1133023 := bstep (se 1 (by rfl) ⟨849767, by rfl⟩ : syracuseStep 1133023 = 1699535) B1699535
theorem B1133183 : Blo 1132632 1133183 := bstep (se 1 (by rfl) ⟨849887, by rfl⟩ : syracuseStep 1133183 = 1699775) B1699775
theorem B1133215 : Blo 1132632 1133215 := bstep (se 1 (by rfl) ⟨849911, by rfl⟩ : syracuseStep 1133215 = 1699823) B1699823
theorem B1133295 : Blo 1132632 1133295 := bstep (se 1 (by rfl) ⟨849971, by rfl⟩ : syracuseStep 1133295 = 1699943) B1699943
theorem B1133375 : Blo 1132632 1133375 := bstep (se 1 (by rfl) ⟨850031, by rfl⟩ : syracuseStep 1133375 = 1700063) B1700063
theorem B1133415 : Blo 1132632 1133415 := bstep (se 1 (by rfl) ⟨850061, by rfl⟩ : syracuseStep 1133415 = 1700123) B1700123
theorem B1362943 : Blo 1132632 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B2870599 : Blo 1132632 2870599 := bstep (se 1 (by rfl) ⟨2152949, by rfl⟩ : syracuseStep 2870599 = 4305899) B4305899
theorem B36818387 : Blo 1132632 36818387 := bstep (se 1 (by rfl) ⟨27613790, by rfl⟩ : syracuseStep 36818387 = 55227581) B55227581
theorem B1134107 : Blo 1132632 1134107 := bstep (se 1 (by rfl) ⟨850580, by rfl⟩ : syracuseStep 1134107 = 1701161) B1701161
theorem B2150543 : Blo 1132632 2150543 := bstep (se 1 (by rfl) ⟨1612907, by rfl⟩ : syracuseStep 2150543 = 3225815) B3225815
theorem B1135071 : Blo 1132632 1135071 := bstep (se 1 (by rfl) ⟨851303, by rfl⟩ : syracuseStep 1135071 = 1702607) B1702607
theorem B1135131 : Blo 1132632 1135131 := bstep (se 1 (by rfl) ⟨851348, by rfl⟩ : syracuseStep 1135131 = 1702697) B1702697
theorem B1135231 : Blo 1132632 1135231 := bstep (se 1 (by rfl) ⟨851423, by rfl⟩ : syracuseStep 1135231 = 1702847) B1702847
theorem B1135487 : Blo 1132632 1135487 := bstep (se 1 (by rfl) ⟨851615, by rfl⟩ : syracuseStep 1135487 = 1703231) B1703231
theorem B1135719 : Blo 1132632 1135719 := bstep (se 1 (by rfl) ⟨851789, by rfl⟩ : syracuseStep 1135719 = 1703579) B1703579
theorem B21845213 : Blo 1132632 21845213 := bstep (se 3 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 21845213 = 8191955) B8191955
theorem B2872543 : Blo 1132632 2872543 := bstep (se 1 (by rfl) ⟨2154407, by rfl⟩ : syracuseStep 2872543 = 4308815) B4308815
theorem B251549023 : Blo 1132632 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B27645313 : Blo 1132632 27645313 := bstep (se 2 (by rfl) ⟨10366992, by rfl⟩ : syracuseStep 27645313 = 20733985) B20733985
theorem B27579923 : Blo 1132632 27579923 := bstep (se 1 (by rfl) ⟨20684942, by rfl⟩ : syracuseStep 27579923 = 41369885) B41369885
theorem B17488885 : Blo 1132632 17488885 := bstep (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) B1639583
theorem B3825305 : Blo 1132632 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B176611049 : Blo 1132632 176611049 := bstep (se 2 (by rfl) ⟨66229143, by rfl⟩ : syracuseStep 176611049 = 132458287) B132458287
theorem B2875439 : Blo 1132632 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B12935375 : Blo 1132632 12935375 := bstep (se 1 (by rfl) ⟨9701531, by rfl⟩ : syracuseStep 12935375 = 19403063) B19403063
theorem B31056317 : Blo 1132632 31056317 := bstep (se 3 (by rfl) ⟨5823059, by rfl⟩ : syracuseStep 31056317 = 11646119) B11646119
theorem B2155099 : Blo 1132632 2155099 := bstep (se 1 (by rfl) ⟨1616324, by rfl⟩ : syracuseStep 2155099 = 3232649) B3232649
theorem B1434439 : Blo 1132632 1434439 := bstep (se 1 (by rfl) ⟨1075829, by rfl⟩ : syracuseStep 1434439 = 2151659) B2151659
theorem B2548601 : Blo 1132632 2548601 := bstep (se 2 (by rfl) ⟨955725, by rfl⟩ : syracuseStep 2548601 = 1911451) B1911451
theorem B2876543 : Blo 1132632 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B2548961 : Blo 1132632 2548961 := bstep (se 2 (by rfl) ⟨955860, by rfl⟩ : syracuseStep 2548961 = 1911721) B1911721
theorem B2876755 : Blo 1132632 2876755 := bstep (se 1 (by rfl) ⟨2157566, by rfl⟩ : syracuseStep 2876755 = 4315133) B4315133
theorem B1435087 : Blo 1132632 1435087 := bstep (se 1 (by rfl) ⟨1076315, by rfl⟩ : syracuseStep 1435087 = 2152631) B2152631
theorem B13788751 : Blo 1132632 13788751 := bstep (se 1 (by rfl) ⟨10341563, by rfl⟩ : syracuseStep 13788751 = 20683127) B20683127
theorem B5826329 : Blo 1132632 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B2549627 : Blo 1132632 2549627 := bstep (se 1 (by rfl) ⟨1912220, by rfl⟩ : syracuseStep 2549627 = 3824441) B3824441
theorem B3827627 : Blo 1132632 3827627 := bstep (se 1 (by rfl) ⟨2870720, by rfl⟩ : syracuseStep 3827627 = 5741441) B5741441
theorem B2549897 : Blo 1132632 2549897 := bstep (se 2 (by rfl) ⟨956211, by rfl⟩ : syracuseStep 2549897 = 1912423) B1912423
theorem B2550383 : Blo 1132632 2550383 := bstep (se 1 (by rfl) ⟨1912787, by rfl⟩ : syracuseStep 2550383 = 3825575) B3825575
theorem B2583247 : Blo 1132632 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B2157263 : Blo 1132632 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B2550599 : Blo 1132632 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B2157673 : Blo 1132632 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B2550959 : Blo 1132632 2550959 := bstep (se 1 (by rfl) ⟨1913219, by rfl⟩ : syracuseStep 2550959 = 3826439) B3826439
theorem B2551211 : Blo 1132632 2551211 := bstep (se 1 (by rfl) ⟨1913408, by rfl⟩ : syracuseStep 2551211 = 3826817) B3826817
theorem B16576001 : Blo 1132632 16576001 := bstep (se 2 (by rfl) ⟨6216000, by rfl⟩ : syracuseStep 16576001 = 12432001) B12432001
theorem B1699487 : Blo 1132632 1699487 := bstep (se 1 (by rfl) ⟨1274615, by rfl⟩ : syracuseStep 1699487 = 2549231) B2549231
theorem B22081319 : Blo 1132632 22081319 := bstep (se 1 (by rfl) ⟨16560989, by rfl⟩ : syracuseStep 22081319 = 33121979) B33121979
theorem B2551679 : Blo 1132632 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B8745403 : Blo 1132632 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B5173703 : Blo 1132632 5173703 := bstep (se 1 (by rfl) ⟨3880277, by rfl⟩ : syracuseStep 5173703 = 7760555) B7760555
theorem B3830327 : Blo 1132632 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B1700519 : Blo 1132632 1700519 := bstep (se 1 (by rfl) ⟨1275389, by rfl⟩ : syracuseStep 1700519 = 2550779) B2550779
theorem B2552507 : Blo 1132632 2552507 := bstep (se 1 (by rfl) ⟨1914380, by rfl⟩ : syracuseStep 2552507 = 3828761) B3828761
theorem B1274575 : Blo 1132632 1274575 := bstep (se 1 (by rfl) ⟨955931, by rfl⟩ : syracuseStep 1274575 = 1911863) B1911863
theorem B6452561 : Blo 1132632 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B2553209 : Blo 1132632 2553209 := bstep (se 2 (by rfl) ⟨957453, by rfl⟩ : syracuseStep 2553209 = 1914907) B1914907
theorem B1701371 : Blo 1132632 1701371 := bstep (se 1 (by rfl) ⟨1276028, by rfl⟩ : syracuseStep 1701371 = 2552057) B2552057
theorem B1701431 : Blo 1132632 1701431 := bstep (se 1 (by rfl) ⟨1276073, by rfl⟩ : syracuseStep 1701431 = 2552147) B2552147
theorem B18413345 : Blo 1132632 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B3831623 : Blo 1132632 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B12285769 : Blo 1132632 12285769 := bstep (se 2 (by rfl) ⟨4607163, by rfl⟩ : syracuseStep 12285769 = 9214327) B9214327
theorem B3635027 : Blo 1132632 3635027 := bstep (se 1 (by rfl) ⟨2726270, by rfl⟩ : syracuseStep 3635027 = 5452541) B5452541
theorem B2553983 : Blo 1132632 2553983 := bstep (se 1 (by rfl) ⟨1915487, by rfl⟩ : syracuseStep 2553983 = 3830975) B3830975
theorem B1702025 : Blo 1132632 1702025 := bstep (se 2 (by rfl) ⟨638259, by rfl⟩ : syracuseStep 1702025 = 1276519) B1276519
theorem B1276159 : Blo 1132632 1276159 := bstep (se 1 (by rfl) ⟨957119, by rfl⟩ : syracuseStep 1276159 = 1914239) B1914239
theorem B10352951 : Blo 1132632 10352951 := bstep (se 1 (by rfl) ⟨7764713, by rfl⟩ : syracuseStep 10352951 = 15529427) B15529427
theorem B2554343 : Blo 1132632 2554343 := bstep (se 1 (by rfl) ⟨1915757, by rfl⟩ : syracuseStep 2554343 = 3831515) B3831515
theorem B2554451 : Blo 1132632 2554451 := bstep (se 1 (by rfl) ⟨1915838, by rfl⟩ : syracuseStep 2554451 = 3831677) B3831677
theorem B2423675 : Blo 1132632 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B1702907 : Blo 1132632 1702907 := bstep (se 1 (by rfl) ⟨1277180, by rfl⟩ : syracuseStep 1702907 = 2554361) B2554361
theorem B1277167 : Blo 1132632 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B8617265 : Blo 1132632 8617265 := bstep (se 2 (by rfl) ⟨3231474, by rfl⟩ : syracuseStep 8617265 = 6462949) B6462949
theorem B2555207 : Blo 1132632 2555207 := bstep (se 1 (by rfl) ⟨1916405, by rfl⟩ : syracuseStep 2555207 = 3832811) B3832811
theorem B12942665 : Blo 1132632 12942665 := bstep (se 2 (by rfl) ⟨4853499, by rfl⟩ : syracuseStep 12942665 = 9706999) B9706999
theorem B2555513 : Blo 1132632 2555513 := bstep (se 2 (by rfl) ⟨958317, by rfl⟩ : syracuseStep 2555513 = 1916635) B1916635
theorem B32702075 : Blo 1132632 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B1277599 : Blo 1132632 1277599 := bstep (se 1 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 1277599 = 1916399) B1916399
theorem B1703663 : Blo 1132632 1703663 := bstep (se 1 (by rfl) ⟨1277747, by rfl⟩ : syracuseStep 1703663 = 2555495) B2555495
theorem B1703849 : Blo 1132632 1703849 := bstep (se 2 (by rfl) ⟨638943, by rfl⟩ : syracuseStep 1703849 = 1277887) B1277887
theorem B2424905 : Blo 1132632 2424905 := bstep (se 2 (by rfl) ⟨909339, by rfl⟩ : syracuseStep 2424905 = 1818679) B1818679
theorem B3833999 : Blo 1132632 3833999 := bstep (se 1 (by rfl) ⟨2875499, by rfl⟩ : syracuseStep 3833999 = 5750999) B5750999
theorem B1704119 : Blo 1132632 1704119 := bstep (se 1 (by rfl) ⟨1278089, by rfl⟩ : syracuseStep 1704119 = 2556179) B2556179
theorem B1704143 : Blo 1132632 1704143 := bstep (se 1 (by rfl) ⟨1278107, by rfl⟩ : syracuseStep 1704143 = 2556215) B2556215
theorem B2556809 : Blo 1132632 2556809 := bstep (se 2 (by rfl) ⟨958803, by rfl⟩ : syracuseStep 2556809 = 1917607) B1917607
theorem B3835673 : Blo 1132632 3835673 := bstep (se 2 (by rfl) ⟨1438377, by rfl⟩ : syracuseStep 3835673 = 2876755) B2876755
theorem B18385001 : Blo 1132632 18385001 := bstep (se 2 (by rfl) ⟨6894375, by rfl⟩ : syracuseStep 18385001 = 13788751) B13788751
theorem B24545591 : Blo 1132632 24545591 := bstep (se 1 (by rfl) ⟨18409193, by rfl⟩ : syracuseStep 24545591 = 36818387) B36818387
theorem B3444329 : Blo 1132632 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B18386615 : Blo 1132632 18386615 := bstep (se 1 (by rfl) ⟨13789961, by rfl⟩ : syracuseStep 18386615 = 27579923) B27579923
theorem B117740699 : Blo 1132632 117740699 := bstep (se 1 (by rfl) ⟨88305524, by rfl⟩ : syracuseStep 117740699 = 176611049) B176611049
theorem B8623583 : Blo 1132632 8623583 := bstep (se 1 (by rfl) ⟨6467687, by rfl⟩ : syracuseStep 8623583 = 12935375) B12935375
theorem B9705359 : Blo 1132632 9705359 := bstep (se 1 (by rfl) ⟨7279019, by rfl⟩ : syracuseStep 9705359 = 14558039) B14558039
theorem B11050667 : Blo 1132632 11050667 := bstep (se 1 (by rfl) ⟨8288000, by rfl⟩ : syracuseStep 11050667 = 16576001) B16576001
theorem B14720879 : Blo 1132632 14720879 := bstep (se 1 (by rfl) ⟨11040659, by rfl⟩ : syracuseStep 14720879 = 22081319) B22081319
theorem B5742737 : Blo 1132632 5742737 := bstep (se 2 (by rfl) ⟨2153526, by rfl⟩ : syracuseStep 5742737 = 4307053) B4307053
theorem B3449135 : Blo 1132632 3449135 := bstep (se 1 (by rfl) ⟨2586851, by rfl⟩ : syracuseStep 3449135 = 5173703) B5173703
theorem B4301707 : Blo 1132632 4301707 := bstep (se 1 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 4301707 = 6452561) B6452561
theorem B1615783 : Blo 1132632 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B5744843 : Blo 1132632 5744843 := bstep (se 1 (by rfl) ⟨4308632, by rfl⟩ : syracuseStep 5744843 = 8617265) B8617265
theorem B8628443 : Blo 1132632 8628443 := bstep (se 1 (by rfl) ⟨6471332, by rfl⟩ : syracuseStep 8628443 = 12942665) B12942665
theorem B21801383 : Blo 1132632 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B8170793 : Blo 1132632 8170793 := bstep (se 2 (by rfl) ⟨3064047, by rfl⟩ : syracuseStep 8170793 = 6128095) B6128095
theorem B14528105 : Blo 1132632 14528105 := bstep (se 2 (by rfl) ⟨5448039, by rfl⟩ : syracuseStep 14528105 = 10896079) B10896079
theorem B1912585 : Blo 1132632 1912585 := bstep (se 2 (by rfl) ⟨717219, by rfl⟩ : syracuseStep 1912585 = 1434439) B1434439
theorem B1913449 : Blo 1132632 1913449 := bstep (se 2 (by rfl) ⟨717543, by rfl⟩ : syracuseStep 1913449 = 1435087) B1435087
theorem B4371113 : Blo 1132632 4371113 := bstep (se 2 (by rfl) ⟨1639167, by rfl⟩ : syracuseStep 4371113 = 3278335) B3278335
theorem B43168459 : Blo 1132632 43168459 := bstep (se 1 (by rfl) ⟨32376344, by rfl⟩ : syracuseStep 43168459 = 64752689) B64752689
theorem B14563475 : Blo 1132632 14563475 := bstep (se 1 (by rfl) ⟨10922606, by rfl⟩ : syracuseStep 14563475 = 21845213) B21845213
theorem B4307327 : Blo 1132632 4307327 := bstep (se 1 (by rfl) ⟨3230495, by rfl⟩ : syracuseStep 4307327 = 6460991) B6460991
theorem B1817257 : Blo 1132632 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B14531795 : Blo 1132632 14531795 := bstep (se 1 (by rfl) ⟨10898846, by rfl⟩ : syracuseStep 14531795 = 21797693) B21797693
theorem B24494035 : Blo 1132632 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B4308983 : Blo 1132632 4308983 := bstep (se 1 (by rfl) ⟨3231737, by rfl⟩ : syracuseStep 4308983 = 6463475) B6463475
theorem B1916959 : Blo 1132632 1916959 := bstep (se 1 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 1916959 = 2875439) B2875439
theorem B1917695 : Blo 1132632 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B3884219 : Blo 1132632 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B3065215 : Blo 1132632 3065215 := bstep (se 1 (by rfl) ⟨2298911, by rfl⟩ : syracuseStep 3065215 = 4597823) B4597823
theorem B335398697 : Blo 1132632 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B1820575 : Blo 1132632 1820575 := bstep (se 1 (by rfl) ⟨1365431, by rfl⟩ : syracuseStep 1820575 = 2730863) B2730863
theorem B4311215 : Blo 1132632 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1132991 : Blo 1132632 1132991 := bstep (se 1 (by rfl) ⟨849743, by rfl⟩ : syracuseStep 1132991 = 1699487) B1699487
theorem B2869951 : Blo 1132632 2869951 := bstep (se 1 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 2869951 = 4304927) B4304927
theorem B1362971 : Blo 1132632 1362971 := bstep (se 1 (by rfl) ⟨1022228, by rfl⟩ : syracuseStep 1362971 = 2044457) B2044457
theorem B1133679 : Blo 1132632 1133679 := bstep (se 1 (by rfl) ⟨850259, by rfl⟩ : syracuseStep 1133679 = 1700519) B1700519
theorem B52317413 : Blo 1132632 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1134247 : Blo 1132632 1134247 := bstep (se 1 (by rfl) ⟨850685, by rfl⟩ : syracuseStep 1134247 = 1701371) B1701371
theorem B1134287 : Blo 1132632 1134287 := bstep (se 1 (by rfl) ⟨850715, by rfl⟩ : syracuseStep 1134287 = 1701431) B1701431
theorem B12275563 : Blo 1132632 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B10342255 : Blo 1132632 10342255 := bstep (se 1 (by rfl) ⟨7756691, by rfl⟩ : syracuseStep 10342255 = 15513383) B15513383
theorem B23318513 : Blo 1132632 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B1134683 : Blo 1132632 1134683 := bstep (se 1 (by rfl) ⟨851012, by rfl⟩ : syracuseStep 1134683 = 1702025) B1702025
theorem B6901967 : Blo 1132632 6901967 := bstep (se 1 (by rfl) ⟨5176475, by rfl⟩ : syracuseStep 6901967 = 10352951) B10352951
theorem B1135271 : Blo 1132632 1135271 := bstep (se 1 (by rfl) ⟨851453, by rfl⟩ : syracuseStep 1135271 = 1702907) B1702907
theorem B1135775 : Blo 1132632 1135775 := bstep (se 1 (by rfl) ⟨851831, by rfl⟩ : syracuseStep 1135775 = 1703663) B1703663
theorem B1135899 : Blo 1132632 1135899 := bstep (se 1 (by rfl) ⟨851924, by rfl⟩ : syracuseStep 1135899 = 1703849) B1703849
theorem B3823145 : Blo 1132632 3823145 := bstep (se 2 (by rfl) ⟨1433679, by rfl⟩ : syracuseStep 3823145 = 2867359) B2867359
theorem B3233321 : Blo 1132632 3233321 := bstep (se 2 (by rfl) ⟨1212495, by rfl⟩ : syracuseStep 3233321 = 2424991) B2424991
theorem B2152403 : Blo 1132632 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B2873465 : Blo 1132632 2873465 := bstep (se 2 (by rfl) ⟨1077549, by rfl⟩ : syracuseStep 2873465 = 2155099) B2155099
theorem B3233981 : Blo 1132632 3233981 := bstep (se 3 (by rfl) ⟨606371, by rfl⟩ : syracuseStep 3233981 = 1212743) B1212743
theorem B8608031 : Blo 1132632 8608031 := bstep (se 1 (by rfl) ⟨6456023, by rfl⟩ : syracuseStep 8608031 = 12912047) B12912047
theorem B3824009 : Blo 1132632 3824009 := bstep (se 2 (by rfl) ⟨1434003, by rfl⟩ : syracuseStep 3824009 = 2868007) B2868007
theorem B7264667 : Blo 1132632 7264667 := bstep (se 1 (by rfl) ⟨5448500, by rfl⟩ : syracuseStep 7264667 = 10897001) B10897001
theorem B2153071 : Blo 1132632 2153071 := bstep (se 1 (by rfl) ⟨1614803, by rfl⟩ : syracuseStep 2153071 = 3229607) B3229607
theorem B2153641 : Blo 1132632 2153641 := bstep (se 2 (by rfl) ⟨807615, by rfl⟩ : syracuseStep 2153641 = 1615231) B1615231
theorem B3235439 : Blo 1132632 3235439 := bstep (se 1 (by rfl) ⟨2426579, by rfl⟩ : syracuseStep 3235439 = 4853159) B4853159
theorem B1433695 : Blo 1132632 1433695 := bstep (se 1 (by rfl) ⟨1075271, by rfl⟩ : syracuseStep 1433695 = 2150543) B2150543
theorem B7757927 : Blo 1132632 7757927 := bstep (se 1 (by rfl) ⟨5818445, by rfl⟩ : syracuseStep 7757927 = 11636891) B11636891
theorem B8610461 : Blo 1132632 8610461 := bstep (se 3 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 8610461 = 3228923) B3228923
theorem B2876897 : Blo 1132632 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B3827465 : Blo 1132632 3827465 := bstep (se 2 (by rfl) ⟨1435299, by rfl⟩ : syracuseStep 3827465 = 2870599) B2870599
theorem B2550203 : Blo 1132632 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B20704211 : Blo 1132632 20704211 := bstep (se 1 (by rfl) ⟨15528158, by rfl⟩ : syracuseStep 20704211 = 31056317) B31056317
theorem B12938291 : Blo 1132632 12938291 := bstep (se 1 (by rfl) ⟨9703718, by rfl⟩ : syracuseStep 12938291 = 19407437) B19407437
theorem B11660537 : Blo 1132632 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B1699067 : Blo 1132632 1699067 := bstep (se 1 (by rfl) ⟨1274300, by rfl⟩ : syracuseStep 1699067 = 2548601) B2548601
theorem B1699307 : Blo 1132632 1699307 := bstep (se 1 (by rfl) ⟨1274480, by rfl⟩ : syracuseStep 1699307 = 2548961) B2548961
theorem B3829247 : Blo 1132632 3829247 := bstep (se 1 (by rfl) ⟨2871935, by rfl⟩ : syracuseStep 3829247 = 5743871) B5743871
theorem B1699433 : Blo 1132632 1699433 := bstep (se 2 (by rfl) ⟨637287, by rfl⟩ : syracuseStep 1699433 = 1274575) B1274575
theorem B1699751 : Blo 1132632 1699751 := bstep (se 1 (by rfl) ⟨1274813, by rfl⟩ : syracuseStep 1699751 = 2549627) B2549627
theorem B2551751 : Blo 1132632 2551751 := bstep (se 1 (by rfl) ⟨1913813, by rfl⟩ : syracuseStep 2551751 = 3827627) B3827627
theorem B1699931 : Blo 1132632 1699931 := bstep (se 1 (by rfl) ⟨1274948, by rfl⟩ : syracuseStep 1699931 = 2549897) B2549897
theorem B3830057 : Blo 1132632 3830057 := bstep (se 2 (by rfl) ⟨1436271, by rfl⟩ : syracuseStep 3830057 = 2872543) B2872543
theorem B7762331 : Blo 1132632 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B1700255 : Blo 1132632 1700255 := bstep (se 1 (by rfl) ⟨1275191, by rfl⟩ : syracuseStep 1700255 = 2550383) B2550383
theorem B1438175 : Blo 1132632 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B36860417 : Blo 1132632 36860417 := bstep (se 2 (by rfl) ⟨13822656, by rfl⟩ : syracuseStep 36860417 = 27645313) B27645313
theorem B1700399 : Blo 1132632 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B1700639 : Blo 1132632 1700639 := bstep (se 1 (by rfl) ⟨1275479, by rfl⟩ : syracuseStep 1700639 = 2550959) B2550959
theorem B3830651 : Blo 1132632 3830651 := bstep (se 1 (by rfl) ⟨2872988, by rfl⟩ : syracuseStep 3830651 = 5745977) B5745977
theorem B1700807 : Blo 1132632 1700807 := bstep (se 1 (by rfl) ⟨1275605, by rfl⟩ : syracuseStep 1700807 = 2551211) B2551211
theorem B16381025 : Blo 1132632 16381025 := bstep (se 2 (by rfl) ⟨6142884, by rfl⟩ : syracuseStep 16381025 = 12285769) B12285769
theorem B1275007 : Blo 1132632 1275007 := bstep (se 1 (by rfl) ⟨956255, by rfl⟩ : syracuseStep 1275007 = 1912511) B1912511
theorem B1701119 : Blo 1132632 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B8287535 : Blo 1132632 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B2913583 : Blo 1132632 2913583 := bstep (se 1 (by rfl) ⟨2185187, by rfl⟩ : syracuseStep 2913583 = 4370375) B4370375
theorem B13792787 : Blo 1132632 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B1275439 : Blo 1132632 1275439 := bstep (se 1 (by rfl) ⟨956579, by rfl⟩ : syracuseStep 1275439 = 1913159) B1913159
theorem B1701545 : Blo 1132632 1701545 := bstep (se 2 (by rfl) ⟨638079, by rfl⟩ : syracuseStep 1701545 = 1276159) B1276159
theorem B2553551 : Blo 1132632 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B1701671 : Blo 1132632 1701671 := bstep (se 1 (by rfl) ⟨1276253, by rfl⟩ : syracuseStep 1701671 = 2552507) B2552507
theorem B3831839 : Blo 1132632 3831839 := bstep (se 1 (by rfl) ⟨2873879, by rfl⟩ : syracuseStep 3831839 = 5747759) B5747759
theorem B1702139 : Blo 1132632 1702139 := bstep (se 1 (by rfl) ⟨1276604, by rfl⟩ : syracuseStep 1702139 = 2553209) B2553209
theorem B2554415 : Blo 1132632 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B2423351 : Blo 1132632 2423351 := bstep (se 1 (by rfl) ⟨1817513, by rfl⟩ : syracuseStep 2423351 = 3635027) B3635027
theorem B1702655 : Blo 1132632 1702655 := bstep (se 1 (by rfl) ⟨1276991, by rfl⟩ : syracuseStep 1702655 = 2553983) B2553983
theorem B1702889 : Blo 1132632 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B1702895 : Blo 1132632 1702895 := bstep (se 1 (by rfl) ⟨1277171, by rfl⟩ : syracuseStep 1702895 = 2554343) B2554343
theorem B1702967 : Blo 1132632 1702967 := bstep (se 1 (by rfl) ⟨1277225, by rfl⟩ : syracuseStep 1702967 = 2554451) B2554451
theorem B3636359 : Blo 1132632 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B1703465 : Blo 1132632 1703465 := bstep (se 2 (by rfl) ⟨638799, by rfl⟩ : syracuseStep 1703465 = 1277599) B1277599
theorem B1703471 : Blo 1132632 1703471 := bstep (se 1 (by rfl) ⟨1277603, by rfl⟩ : syracuseStep 1703471 = 2555207) B2555207
theorem B1703675 : Blo 1132632 1703675 := bstep (se 1 (by rfl) ⟨1277756, by rfl⟩ : syracuseStep 1703675 = 2555513) B2555513
theorem B8617751 : Blo 1132632 8617751 := bstep (se 1 (by rfl) ⟨6463313, by rfl⟩ : syracuseStep 8617751 = 12926627) B12926627
theorem B2555873 : Blo 1132632 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B2555945 : Blo 1132632 2555945 := bstep (se 2 (by rfl) ⟨958479, by rfl⟩ : syracuseStep 2555945 = 1916959) B1916959
theorem B2555999 : Blo 1132632 2555999 := bstep (se 1 (by rfl) ⟨1916999, by rfl⟩ : syracuseStep 2555999 = 3833999) B3833999
theorem B1278463 : Blo 1132632 1278463 := bstep (se 1 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 1278463 = 1917695) B1917695
theorem B1704539 : Blo 1132632 1704539 := bstep (se 1 (by rfl) ⟨1278404, by rfl⟩ : syracuseStep 1704539 = 2556809) B2556809
theorem B2589479 : Blo 1132632 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B5735609 : Blo 1132632 5735609 := bstep (se 2 (by rfl) ⟨2150853, by rfl⟩ : syracuseStep 5735609 = 4301707) B4301707
theorem B2557115 : Blo 1132632 2557115 := bstep (se 1 (by rfl) ⟨1917836, by rfl⟩ : syracuseStep 2557115 = 3835673) B3835673
theorem B3835133 : Blo 1132632 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B12256667 : Blo 1132632 12256667 := bstep (se 1 (by rfl) ⟨9192500, by rfl⟩ : syracuseStep 12256667 = 18385001) B18385001
theorem B12257743 : Blo 1132632 12257743 := bstep (se 1 (by rfl) ⟨9193307, by rfl⟩ : syracuseStep 12257743 = 18386615) B18386615
theorem B5738687 : Blo 1132632 5738687 := bstep (se 1 (by rfl) ⟨4304015, by rfl⟩ : syracuseStep 5738687 = 8608031) B8608031
theorem B2299423 : Blo 1132632 2299423 := bstep (se 1 (by rfl) ⟨1724567, by rfl⟩ : syracuseStep 2299423 = 3449135) B3449135
theorem B5740307 : Blo 1132632 5740307 := bstep (se 1 (by rfl) ⟨4305230, by rfl⟩ : syracuseStep 5740307 = 8610461) B8610461
theorem B19372445 : Blo 1132632 19372445 := bstep (se 3 (by rfl) ⟨3632333, by rfl⟩ : syracuseStep 19372445 = 7264667) B7264667
theorem B13802807 : Blo 1132632 13802807 := bstep (se 1 (by rfl) ⟨10352105, by rfl⟩ : syracuseStep 13802807 = 20704211) B20704211
theorem B8625527 : Blo 1132632 8625527 := bstep (se 1 (by rfl) ⟨6469145, by rfl⟩ : syracuseStep 8625527 = 12938291) B12938291
theorem B5447195 : Blo 1132632 5447195 := bstep (se 1 (by rfl) ⟨4085396, by rfl⟩ : syracuseStep 5447195 = 8170793) B8170793
theorem B10920683 : Blo 1132632 10920683 := bstep (se 1 (by rfl) ⟨8190512, by rfl⟩ : syracuseStep 10920683 = 16381025) B16381025
theorem B9708983 : Blo 1132632 9708983 := bstep (se 1 (by rfl) ⟨7281737, by rfl⟩ : syracuseStep 9708983 = 14563475) B14563475
theorem B9184877 : Blo 1132632 9184877 := bstep (se 3 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 9184877 = 3444329) B3444329
theorem B1615567 : Blo 1132632 1615567 := bstep (se 1 (by rfl) ⟨1211675, by rfl⟩ : syracuseStep 1615567 = 2423351) B2423351
theorem B9709733 : Blo 1132632 9709733 := bstep (se 4 (by rfl) ⟨910287, by rfl⟩ : syracuseStep 9709733 = 1820575) B1820575
theorem B5745167 : Blo 1132632 5745167 := bstep (se 1 (by rfl) ⟨4308875, by rfl⟩ : syracuseStep 5745167 = 8617751) B8617751
theorem B1616603 : Blo 1132632 1616603 := bstep (se 1 (by rfl) ⟨1212452, by rfl⟩ : syracuseStep 1616603 = 2424905) B2424905
theorem B1911593 : Blo 1132632 1911593 := bstep (se 2 (by rfl) ⟨716847, by rfl⟩ : syracuseStep 1911593 = 1433695) B1433695
theorem B16363727 : Blo 1132632 16363727 := bstep (se 1 (by rfl) ⟨12272795, by rfl⟩ : syracuseStep 16363727 = 24545591) B24545591
theorem B34878275 : Blo 1132632 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B15545675 : Blo 1132632 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B78493799 : Blo 1132632 78493799 := bstep (se 1 (by rfl) ⟨58870349, by rfl⟩ : syracuseStep 78493799 = 117740699) B117740699
theorem B5749055 : Blo 1132632 5749055 := bstep (se 1 (by rfl) ⟨4311791, by rfl⟩ : syracuseStep 5749055 = 8623583) B8623583
theorem B6470239 : Blo 1132632 6470239 := bstep (se 1 (by rfl) ⟨4852679, by rfl⟩ : syracuseStep 6470239 = 9705359) B9705359
theorem B1915643 : Blo 1132632 1915643 := bstep (se 1 (by rfl) ⟨1436732, by rfl⟩ : syracuseStep 1915643 = 2873465) B2873465
theorem B16367417 : Blo 1132632 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B9813919 : Blo 1132632 9813919 := bstep (se 1 (by rfl) ⟨7360439, by rfl⟩ : syracuseStep 9813919 = 14720879) B14720879
theorem B57557945 : Blo 1132632 57557945 := bstep (se 2 (by rfl) ⟨21584229, by rfl⟩ : syracuseStep 57557945 = 43168459) B43168459
theorem B1917931 : Blo 1132632 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B5752295 : Blo 1132632 5752295 := bstep (se 1 (by rfl) ⟨4314221, by rfl⟩ : syracuseStep 5752295 = 8628443) B8628443
theorem B14534255 : Blo 1132632 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B3884777 : Blo 1132632 3884777 := bstep (se 2 (by rfl) ⟨1456791, by rfl⟩ : syracuseStep 3884777 = 2913583) B2913583
theorem B1132711 : Blo 1132632 1132711 := bstep (se 1 (by rfl) ⟨849533, by rfl⟩ : syracuseStep 1132711 = 1699067) B1699067
theorem B1132871 : Blo 1132632 1132871 := bstep (se 1 (by rfl) ⟨849653, by rfl⟩ : syracuseStep 1132871 = 1699307) B1699307
theorem B1132955 : Blo 1132632 1132955 := bstep (se 1 (by rfl) ⟨849716, by rfl⟩ : syracuseStep 1132955 = 1699433) B1699433
theorem B9685403 : Blo 1132632 9685403 := bstep (se 1 (by rfl) ⟨7264052, by rfl⟩ : syracuseStep 9685403 = 14528105) B14528105
theorem B1133167 : Blo 1132632 1133167 := bstep (se 1 (by rfl) ⟨849875, by rfl⟩ : syracuseStep 1133167 = 1699751) B1699751
theorem B1133287 : Blo 1132632 1133287 := bstep (se 1 (by rfl) ⟨849965, by rfl⟩ : syracuseStep 1133287 = 1699931) B1699931
theorem B1133503 : Blo 1132632 1133503 := bstep (se 1 (by rfl) ⟨850127, by rfl⟩ : syracuseStep 1133503 = 1700255) B1700255
theorem B1133599 : Blo 1132632 1133599 := bstep (se 1 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 1133599 = 1700399) B1700399
theorem B1133759 : Blo 1132632 1133759 := bstep (se 1 (by rfl) ⟨850319, by rfl⟩ : syracuseStep 1133759 = 1700639) B1700639
theorem B1133871 : Blo 1132632 1133871 := bstep (se 1 (by rfl) ⟨850403, by rfl⟩ : syracuseStep 1133871 = 1700807) B1700807
theorem B2870761 : Blo 1132632 2870761 := bstep (se 2 (by rfl) ⟨1076535, by rfl⟩ : syracuseStep 2870761 = 2153071) B2153071
theorem B1134079 : Blo 1132632 1134079 := bstep (se 1 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 1134079 = 1701119) B1701119
theorem B5525023 : Blo 1132632 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B9195191 : Blo 1132632 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B1134363 : Blo 1132632 1134363 := bstep (se 1 (by rfl) ⟨850772, by rfl⟩ : syracuseStep 1134363 = 1701545) B1701545
theorem B1134447 : Blo 1132632 1134447 := bstep (se 1 (by rfl) ⟨850835, by rfl⟩ : syracuseStep 1134447 = 1701671) B1701671
theorem B1134759 : Blo 1132632 1134759 := bstep (se 1 (by rfl) ⟨851069, by rfl⟩ : syracuseStep 1134759 = 1702139) B1702139
theorem B2871521 : Blo 1132632 2871521 := bstep (se 2 (by rfl) ⟨1076820, by rfl⟩ : syracuseStep 2871521 = 2153641) B2153641
theorem B2871551 : Blo 1132632 2871551 := bstep (se 1 (by rfl) ⟨2153663, by rfl⟩ : syracuseStep 2871551 = 4307327) B4307327
theorem B1135103 : Blo 1132632 1135103 := bstep (se 1 (by rfl) ⟨851327, by rfl⟩ : syracuseStep 1135103 = 1702655) B1702655
theorem B1135259 : Blo 1132632 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B1135263 : Blo 1132632 1135263 := bstep (se 1 (by rfl) ⟨851447, by rfl⟩ : syracuseStep 1135263 = 1702895) B1702895
theorem B1135311 : Blo 1132632 1135311 := bstep (se 1 (by rfl) ⟨851483, by rfl⟩ : syracuseStep 1135311 = 1702967) B1702967
theorem B9687863 : Blo 1132632 9687863 := bstep (se 1 (by rfl) ⟨7265897, by rfl⟩ : syracuseStep 9687863 = 14531795) B14531795
theorem B1135643 : Blo 1132632 1135643 := bstep (se 1 (by rfl) ⟨851732, by rfl⟩ : syracuseStep 1135643 = 1703465) B1703465
theorem B1135647 : Blo 1132632 1135647 := bstep (se 1 (by rfl) ⟨851735, by rfl⟩ : syracuseStep 1135647 = 1703471) B1703471
theorem B1135783 : Blo 1132632 1135783 := bstep (se 1 (by rfl) ⟨851837, by rfl⟩ : syracuseStep 1135783 = 1703675) B1703675
theorem B32658713 : Blo 1132632 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B2872655 : Blo 1132632 2872655 := bstep (se 1 (by rfl) ⟨2154491, by rfl⟩ : syracuseStep 2872655 = 4308983) B4308983
theorem B1136079 : Blo 1132632 1136079 := bstep (se 1 (by rfl) ⟨852059, by rfl⟩ : syracuseStep 1136079 = 1704119) B1704119
theorem B1136095 : Blo 1132632 1136095 := bstep (se 1 (by rfl) ⟨852071, by rfl⟩ : syracuseStep 1136095 = 1704143) B1704143
theorem B18405245 : Blo 1132632 18405245 := bstep (se 3 (by rfl) ⟨3450983, by rfl⟩ : syracuseStep 18405245 = 6901967) B6901967
theorem B223599131 : Blo 1132632 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B2874143 : Blo 1132632 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B4086953 : Blo 1132632 4086953 := bstep (se 2 (by rfl) ⟨1532607, by rfl⟩ : syracuseStep 4086953 = 3065215) B3065215
theorem B2154377 : Blo 1132632 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B3826601 : Blo 1132632 3826601 := bstep (se 2 (by rfl) ⟨1434975, by rfl⟩ : syracuseStep 3826601 = 2869951) B2869951
theorem B2548763 : Blo 1132632 2548763 := bstep (se 1 (by rfl) ⟨1911572, by rfl⟩ : syracuseStep 2548763 = 3823145) B3823145
theorem B2155547 : Blo 1132632 2155547 := bstep (se 1 (by rfl) ⟨1616660, by rfl⟩ : syracuseStep 2155547 = 3233321) B3233321
theorem B1434935 : Blo 1132632 1434935 := bstep (se 1 (by rfl) ⟨1076201, by rfl⟩ : syracuseStep 1434935 = 2152403) B2152403
theorem B2155987 : Blo 1132632 2155987 := bstep (se 1 (by rfl) ⟨1616990, by rfl⟩ : syracuseStep 2155987 = 3233981) B3233981
theorem B2549339 : Blo 1132632 2549339 := bstep (se 1 (by rfl) ⟨1912004, by rfl⟩ : syracuseStep 2549339 = 3824009) B3824009
theorem B2550113 : Blo 1132632 2550113 := bstep (se 2 (by rfl) ⟨956292, by rfl⟩ : syracuseStep 2550113 = 1912585) B1912585
theorem B2156959 : Blo 1132632 2156959 := bstep (se 1 (by rfl) ⟨1617719, by rfl⟩ : syracuseStep 2156959 = 3235439) B3235439
theorem B7367111 : Blo 1132632 7367111 := bstep (se 1 (by rfl) ⟨5525333, by rfl⟩ : syracuseStep 7367111 = 11050667) B11050667
theorem B13789673 : Blo 1132632 13789673 := bstep (se 2 (by rfl) ⟨5171127, by rfl⟩ : syracuseStep 13789673 = 10342255) B10342255
theorem B5171951 : Blo 1132632 5171951 := bstep (se 1 (by rfl) ⟨3878963, by rfl⟩ : syracuseStep 5171951 = 7757927) B7757927
theorem B3828491 : Blo 1132632 3828491 := bstep (se 1 (by rfl) ⟨2871368, by rfl⟩ : syracuseStep 3828491 = 5742737) B5742737
theorem B2551265 : Blo 1132632 2551265 := bstep (se 2 (by rfl) ⟨956724, by rfl⟩ : syracuseStep 2551265 = 1913449) B1913449
theorem B2551643 : Blo 1132632 2551643 := bstep (se 1 (by rfl) ⟨1913732, by rfl⟩ : syracuseStep 2551643 = 3827465) B3827465
theorem B3829895 : Blo 1132632 3829895 := bstep (se 1 (by rfl) ⟨2872421, by rfl⟩ : syracuseStep 3829895 = 5744843) B5744843
theorem B1700009 : Blo 1132632 1700009 := bstep (se 2 (by rfl) ⟨637503, by rfl⟩ : syracuseStep 1700009 = 1275007) B1275007
theorem B1700135 : Blo 1132632 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B1700585 : Blo 1132632 1700585 := bstep (se 2 (by rfl) ⟨637719, by rfl⟩ : syracuseStep 1700585 = 1275439) B1275439
theorem B2552831 : Blo 1132632 2552831 := bstep (se 1 (by rfl) ⟨1914623, by rfl⟩ : syracuseStep 2552831 = 3829247) B3829247
theorem B1701167 : Blo 1132632 1701167 := bstep (se 1 (by rfl) ⟨1275875, by rfl⟩ : syracuseStep 1701167 = 2551751) B2551751
theorem B3634589 : Blo 1132632 3634589 := bstep (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) B1362971
theorem B2553371 : Blo 1132632 2553371 := bstep (se 1 (by rfl) ⟨1915028, by rfl⟩ : syracuseStep 2553371 = 3830057) B3830057
theorem B5174887 : Blo 1132632 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B24573611 : Blo 1132632 24573611 := bstep (se 1 (by rfl) ⟨18430208, by rfl⟩ : syracuseStep 24573611 = 36860417) B36860417
theorem B2914075 : Blo 1132632 2914075 := bstep (se 1 (by rfl) ⟨2185556, by rfl⟩ : syracuseStep 2914075 = 4371113) B4371113
theorem B2553767 : Blo 1132632 2553767 := bstep (se 1 (by rfl) ⟨1915325, by rfl⟩ : syracuseStep 2553767 = 3830651) B3830651
theorem B31094765 : Blo 1132632 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B2423009 : Blo 1132632 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B1702367 : Blo 1132632 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B2554559 : Blo 1132632 2554559 := bstep (se 1 (by rfl) ⟨1915919, by rfl⟩ : syracuseStep 2554559 = 3831839) B3831839
theorem B1702943 : Blo 1132632 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B2424239 : Blo 1132632 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B1703915 : Blo 1132632 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B1703963 : Blo 1132632 1703963 := bstep (se 1 (by rfl) ⟨1277972, by rfl⟩ : syracuseStep 1703963 = 2555945) B2555945
theorem B1703999 : Blo 1132632 1703999 := bstep (se 1 (by rfl) ⟨1277999, by rfl⟩ : syracuseStep 1703999 = 2555999) B2555999
theorem B38371963 : Blo 1132632 38371963 := bstep (se 1 (by rfl) ⟨28778972, by rfl⟩ : syracuseStep 38371963 = 57557945) B57557945
theorem B1704617 : Blo 1132632 1704617 := bstep (se 2 (by rfl) ⟨639231, by rfl⟩ : syracuseStep 1704617 = 1278463) B1278463
theorem B1704743 : Blo 1132632 1704743 := bstep (se 1 (by rfl) ⟨1278557, by rfl⟩ : syracuseStep 1704743 = 2557115) B2557115
theorem B2556755 : Blo 1132632 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B3834863 : Blo 1132632 3834863 := bstep (se 1 (by rfl) ⟨2876147, by rfl⟩ : syracuseStep 3834863 = 5752295) B5752295
theorem B2589851 : Blo 1132632 2589851 := bstep (se 1 (by rfl) ⟨1942388, by rfl⟩ : syracuseStep 2589851 = 3884777) B3884777
theorem B2557241 : Blo 1132632 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B6456935 : Blo 1132632 6456935 := bstep (se 1 (by rfl) ⟨4842701, by rfl⟩ : syracuseStep 6456935 = 9685403) B9685403
theorem B6130127 : Blo 1132632 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B6458575 : Blo 1132632 6458575 := bstep (se 1 (by rfl) ⟨4843931, by rfl⟩ : syracuseStep 6458575 = 9687863) B9687863
theorem B12914963 : Blo 1132632 12914963 := bstep (se 1 (by rfl) ⟨9686222, by rfl⟩ : syracuseStep 12914963 = 19372445) B19372445
theorem B149066087 : Blo 1132632 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B2724635 : Blo 1132632 2724635 := bstep (se 1 (by rfl) ⟨2043476, by rfl⟩ : syracuseStep 2724635 = 4086953) B4086953
theorem B7280455 : Blo 1132632 7280455 := bstep (se 1 (by rfl) ⟨5460341, by rfl⟩ : syracuseStep 7280455 = 10920683) B10920683
theorem B3447967 : Blo 1132632 3447967 := bstep (se 1 (by rfl) ⟨2585975, by rfl⟩ : syracuseStep 3447967 = 5171951) B5171951
theorem B8626985 : Blo 1132632 8626985 := bstep (se 2 (by rfl) ⟨3235119, by rfl⟩ : syracuseStep 8626985 = 6470239) B6470239
theorem B10363783 : Blo 1132632 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B15541733 : Blo 1132632 15541733 := bstep (se 4 (by rfl) ⟨1457037, by rfl⟩ : syracuseStep 15541733 = 2914075) B2914075
theorem B1615339 : Blo 1132632 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B1616159 : Blo 1132632 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B5745005 : Blo 1132632 5745005 := bstep (se 3 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 5745005 = 2154377) B2154377
theorem B13085225 : Blo 1132632 13085225 := bstep (se 2 (by rfl) ⟨4906959, by rfl⟩ : syracuseStep 13085225 = 9813919) B9813919
theorem B8171111 : Blo 1132632 8171111 := bstep (se 1 (by rfl) ⟨6128333, by rfl⟩ : syracuseStep 8171111 = 12256667) B12256667
theorem B1914347 : Blo 1132632 1914347 := bstep (se 1 (by rfl) ⟨1435760, by rfl⟩ : syracuseStep 1914347 = 2871521) B2871521
theorem B1914367 : Blo 1132632 1914367 := bstep (se 1 (by rfl) ⟨1435775, by rfl⟩ : syracuseStep 1914367 = 2871551) B2871551
theorem B21772475 : Blo 1132632 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B1915103 : Blo 1132632 1915103 := bstep (se 1 (by rfl) ⟨1436327, by rfl⟩ : syracuseStep 1915103 = 2872655) B2872655
theorem B12270163 : Blo 1132632 12270163 := bstep (se 1 (by rfl) ⟨9202622, by rfl⟩ : syracuseStep 12270163 = 18405245) B18405245
theorem B1916095 : Blo 1132632 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B5750351 : Blo 1132632 5750351 := bstep (se 1 (by rfl) ⟨4312763, by rfl⟩ : syracuseStep 5750351 = 8625527) B8625527
theorem B6472655 : Blo 1132632 6472655 := bstep (se 1 (by rfl) ⟨4854491, by rfl⟩ : syracuseStep 6472655 = 9708983) B9708983
theorem B6473155 : Blo 1132632 6473155 := bstep (se 1 (by rfl) ⟨4854866, by rfl⟩ : syracuseStep 6473155 = 9709733) B9709733
theorem B9193115 : Blo 1132632 9193115 := bstep (se 1 (by rfl) ⟨6894836, by rfl⟩ : syracuseStep 9193115 = 13789673) B13789673
theorem B4310941 : Blo 1132632 4310941 := bstep (se 3 (by rfl) ⟨808301, by rfl⟩ : syracuseStep 4310941 = 1616603) B1616603
theorem B3065897 : Blo 1132632 3065897 := bstep (se 2 (by rfl) ⟨1149711, by rfl⟩ : syracuseStep 3065897 = 2299423) B2299423
theorem B6899849 : Blo 1132632 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B1133339 : Blo 1132632 1133339 := bstep (se 1 (by rfl) ⟨850004, by rfl⟩ : syracuseStep 1133339 = 1700009) B1700009
theorem B1133423 : Blo 1132632 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B1133723 : Blo 1132632 1133723 := bstep (se 1 (by rfl) ⟨850292, by rfl⟩ : syracuseStep 1133723 = 1700585) B1700585
theorem B23252183 : Blo 1132632 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B1134111 : Blo 1132632 1134111 := bstep (se 1 (by rfl) ⟨850583, by rfl⟩ : syracuseStep 1134111 = 1701167) B1701167
theorem B20729843 : Blo 1132632 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B1134911 : Blo 1132632 1134911 := bstep (se 1 (by rfl) ⟨851183, by rfl⟩ : syracuseStep 1134911 = 1702367) B1702367
theorem B1135295 : Blo 1132632 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B1135943 : Blo 1132632 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B1136359 : Blo 1132632 1136359 := bstep (se 1 (by rfl) ⟨852269, by rfl⟩ : syracuseStep 1136359 = 1704539) B1704539
theorem B1726319 : Blo 1132632 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B3823739 : Blo 1132632 3823739 := bstep (se 1 (by rfl) ⟨2867804, by rfl⟩ : syracuseStep 3823739 = 5735609) B5735609
theorem B9689503 : Blo 1132632 9689503 := bstep (se 1 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 9689503 = 14534255) B14534255
theorem B2874649 : Blo 1132632 2874649 := bstep (se 2 (by rfl) ⟨1077993, by rfl⟩ : syracuseStep 2874649 = 2155987) B2155987
theorem B2154089 : Blo 1132632 2154089 := bstep (se 2 (by rfl) ⟨807783, by rfl⟩ : syracuseStep 2154089 = 1615567) B1615567
theorem B3825791 : Blo 1132632 3825791 := bstep (se 1 (by rfl) ⟨2869343, by rfl⟩ : syracuseStep 3825791 = 5738687) B5738687
theorem B2875945 : Blo 1132632 2875945 := bstep (se 2 (by rfl) ⟨1078479, by rfl⟩ : syracuseStep 2875945 = 2156959) B2156959
theorem B16343657 : Blo 1132632 16343657 := bstep (se 2 (by rfl) ⟨6128871, by rfl⟩ : syracuseStep 16343657 = 12257743) B12257743
theorem B3826493 : Blo 1132632 3826493 := bstep (se 3 (by rfl) ⟨717467, by rfl⟩ : syracuseStep 3826493 = 1434935) B1434935
theorem B9692237 : Blo 1132632 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B3826871 : Blo 1132632 3826871 := bstep (se 1 (by rfl) ⟨2870153, by rfl⟩ : syracuseStep 3826871 = 5740307) B5740307
theorem B3827681 : Blo 1132632 3827681 := bstep (se 2 (by rfl) ⟨1435380, by rfl⟩ : syracuseStep 3827681 = 2870761) B2870761
theorem B7366697 : Blo 1132632 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B9201871 : Blo 1132632 9201871 := bstep (se 1 (by rfl) ⟨6901403, by rfl⟩ : syracuseStep 9201871 = 13802807) B13802807
theorem B3631463 : Blo 1132632 3631463 := bstep (se 1 (by rfl) ⟨2723597, by rfl⟩ : syracuseStep 3631463 = 5447195) B5447195
theorem B2551067 : Blo 1132632 2551067 := bstep (se 1 (by rfl) ⟨1913300, by rfl⟩ : syracuseStep 2551067 = 3826601) B3826601
theorem B1699175 : Blo 1132632 1699175 := bstep (se 1 (by rfl) ⟨1274381, by rfl⟩ : syracuseStep 1699175 = 2548763) B2548763
theorem B1437031 : Blo 1132632 1437031 := bstep (se 1 (by rfl) ⟨1077773, by rfl⟩ : syracuseStep 1437031 = 2155547) B2155547
theorem B1699559 : Blo 1132632 1699559 := bstep (se 1 (by rfl) ⟨1274669, by rfl⟩ : syracuseStep 1699559 = 2549339) B2549339
theorem B6123251 : Blo 1132632 6123251 := bstep (se 1 (by rfl) ⟨4592438, by rfl⟩ : syracuseStep 6123251 = 9184877) B9184877
theorem B1700075 : Blo 1132632 1700075 := bstep (se 1 (by rfl) ⟨1275056, by rfl⟩ : syracuseStep 1700075 = 2550113) B2550113
theorem B4911407 : Blo 1132632 4911407 := bstep (se 1 (by rfl) ⟨3683555, by rfl⟩ : syracuseStep 4911407 = 7367111) B7367111
theorem B3830111 : Blo 1132632 3830111 := bstep (se 1 (by rfl) ⟨2872583, by rfl⟩ : syracuseStep 3830111 = 5745167) B5745167
theorem B2552327 : Blo 1132632 2552327 := bstep (se 1 (by rfl) ⟨1914245, by rfl⟩ : syracuseStep 2552327 = 3828491) B3828491
theorem B1274395 : Blo 1132632 1274395 := bstep (se 1 (by rfl) ⟨955796, by rfl⟩ : syracuseStep 1274395 = 1911593) B1911593
theorem B1700843 : Blo 1132632 1700843 := bstep (se 1 (by rfl) ⟨1275632, by rfl⟩ : syracuseStep 1700843 = 2551265) B2551265
theorem B1701095 : Blo 1132632 1701095 := bstep (se 1 (by rfl) ⟨1275821, by rfl⟩ : syracuseStep 1701095 = 2551643) B2551643
theorem B2553263 : Blo 1132632 2553263 := bstep (se 1 (by rfl) ⟨1914947, by rfl⟩ : syracuseStep 2553263 = 3829895) B3829895
theorem B10909151 : Blo 1132632 10909151 := bstep (se 1 (by rfl) ⟨8181863, by rfl⟩ : syracuseStep 10909151 = 16363727) B16363727
theorem B1701887 : Blo 1132632 1701887 := bstep (se 1 (by rfl) ⟨1276415, by rfl⟩ : syracuseStep 1701887 = 2552831) B2552831
theorem B1702247 : Blo 1132632 1702247 := bstep (se 1 (by rfl) ⟨1276685, by rfl⟩ : syracuseStep 1702247 = 2553371) B2553371
theorem B16382407 : Blo 1132632 16382407 := bstep (se 1 (by rfl) ⟨12286805, by rfl⟩ : syracuseStep 16382407 = 24573611) B24573611
theorem B1702511 : Blo 1132632 1702511 := bstep (se 1 (by rfl) ⟨1276883, by rfl⟩ : syracuseStep 1702511 = 2553767) B2553767
theorem B52329199 : Blo 1132632 52329199 := bstep (se 1 (by rfl) ⟨39246899, by rfl⟩ : syracuseStep 52329199 = 78493799) B78493799
theorem B3832703 : Blo 1132632 3832703 := bstep (se 1 (by rfl) ⟨2874527, by rfl⟩ : syracuseStep 3832703 = 5749055) B5749055
theorem B1703039 : Blo 1132632 1703039 := bstep (se 1 (by rfl) ⟨1277279, by rfl⟩ : syracuseStep 1703039 = 2554559) B2554559
theorem B1277095 : Blo 1132632 1277095 := bstep (se 1 (by rfl) ⟨957821, by rfl⟩ : syracuseStep 1277095 = 1915643) B1915643
theorem B10911611 : Blo 1132632 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B1704503 : Blo 1132632 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B2556575 : Blo 1132632 2556575 := bstep (se 1 (by rfl) ⟨1917431, by rfl⟩ : syracuseStep 2556575 = 3834863) B3834863
theorem B3834593 : Blo 1132632 3834593 := bstep (se 2 (by rfl) ⟨1437972, by rfl⟩ : syracuseStep 3834593 = 2875945) B2875945
theorem B1704827 : Blo 1132632 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B397509565 : Blo 1132632 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B15501455 : Blo 1132632 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B24514973 : Blo 1132632 24514973 := bstep (se 3 (by rfl) ⟨4596557, by rfl⟩ : syracuseStep 24514973 = 9193115) B9193115
theorem B6461491 : Blo 1132632 6461491 := bstep (se 1 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 6461491 = 9692237) B9692237
theorem B8723483 : Blo 1132632 8723483 := bstep (se 1 (by rfl) ⟨6542612, by rfl⟩ : syracuseStep 8723483 = 13085225) B13085225
theorem B5447407 : Blo 1132632 5447407 := bstep (se 1 (by rfl) ⟨4085555, by rfl⟩ : syracuseStep 5447407 = 8171111) B8171111
theorem B9707273 : Blo 1132632 9707273 := bstep (se 2 (by rfl) ⟨3640227, by rfl⟩ : syracuseStep 9707273 = 7280455) B7280455
theorem B12919337 : Blo 1132632 12919337 := bstep (se 2 (by rfl) ⟨4844751, by rfl⟩ : syracuseStep 12919337 = 9689503) B9689503
theorem B16360217 : Blo 1132632 16360217 := bstep (se 2 (by rfl) ⟨6135081, by rfl⟩ : syracuseStep 16360217 = 12270163) B12270163
theorem B69772265 : Blo 1132632 69772265 := bstep (se 2 (by rfl) ⟨26164599, by rfl⟩ : syracuseStep 69772265 = 52329199) B52329199
theorem B4597289 : Blo 1132632 4597289 := bstep (se 2 (by rfl) ⟨1723983, by rfl⟩ : syracuseStep 4597289 = 3447967) B3447967
theorem B51162617 : Blo 1132632 51162617 := bstep (se 2 (by rfl) ⟨19185981, by rfl⟩ : syracuseStep 51162617 = 38371963) B38371963
theorem B4304623 : Blo 1132632 4304623 := bstep (se 1 (by rfl) ⟨3228467, by rfl⟩ : syracuseStep 4304623 = 6456935) B6456935
theorem B4599899 : Blo 1132632 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B8630873 : Blo 1132632 8630873 := bstep (se 2 (by rfl) ⟨3236577, by rfl⟩ : syracuseStep 8630873 = 6473155) B6473155
theorem B5747921 : Blo 1132632 5747921 := bstep (se 2 (by rfl) ⟨2155470, by rfl⟩ : syracuseStep 5747921 = 4310941) B4310941
theorem B12269161 : Blo 1132632 12269161 := bstep (se 2 (by rfl) ⟨4600935, by rfl⟩ : syracuseStep 12269161 = 9201871) B9201871
theorem B1916041 : Blo 1132632 1916041 := bstep (se 2 (by rfl) ⟨718515, by rfl⟩ : syracuseStep 1916041 = 1437031) B1437031
theorem B4603517 : Blo 1132632 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B8175725 : Blo 1132632 8175725 := bstep (se 3 (by rfl) ⟨1532948, by rfl⟩ : syracuseStep 8175725 = 3065897) B3065897
theorem B10895771 : Blo 1132632 10895771 := bstep (se 1 (by rfl) ⟨8171828, by rfl⟩ : syracuseStep 10895771 = 16343657) B16343657
theorem B5751323 : Blo 1132632 5751323 := bstep (se 1 (by rfl) ⟨4313492, by rfl⟩ : syracuseStep 5751323 = 8626985) B8626985
theorem B4309757 : Blo 1132632 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B1132783 : Blo 1132632 1132783 := bstep (se 1 (by rfl) ⟨849587, by rfl⟩ : syracuseStep 1132783 = 1699175) B1699175
theorem B1133039 : Blo 1132632 1133039 := bstep (se 1 (by rfl) ⟨849779, by rfl⟩ : syracuseStep 1133039 = 1699559) B1699559
theorem B4082167 : Blo 1132632 4082167 := bstep (se 1 (by rfl) ⟨3061625, by rfl⟩ : syracuseStep 4082167 = 6123251) B6123251
theorem B1133383 : Blo 1132632 1133383 := bstep (se 1 (by rfl) ⟨850037, by rfl⟩ : syracuseStep 1133383 = 1700075) B1700075
theorem B21843209 : Blo 1132632 21843209 := bstep (se 2 (by rfl) ⟨8191203, by rfl⟩ : syracuseStep 21843209 = 16382407) B16382407
theorem B1133895 : Blo 1132632 1133895 := bstep (se 1 (by rfl) ⟨850421, by rfl⟩ : syracuseStep 1133895 = 1700843) B1700843
theorem B1134063 : Blo 1132632 1134063 := bstep (se 1 (by rfl) ⟨850547, by rfl⟩ : syracuseStep 1134063 = 1701095) B1701095
theorem B1134591 : Blo 1132632 1134591 := bstep (se 1 (by rfl) ⟨850943, by rfl⟩ : syracuseStep 1134591 = 1701887) B1701887
theorem B1134831 : Blo 1132632 1134831 := bstep (se 1 (by rfl) ⟨851123, by rfl⟩ : syracuseStep 1134831 = 1702247) B1702247
theorem B1135007 : Blo 1132632 1135007 := bstep (se 1 (by rfl) ⟨851255, by rfl⟩ : syracuseStep 1135007 = 1702511) B1702511
theorem B1135359 : Blo 1132632 1135359 := bstep (se 1 (by rfl) ⟨851519, by rfl⟩ : syracuseStep 1135359 = 1703039) B1703039
theorem B1135975 : Blo 1132632 1135975 := bstep (se 1 (by rfl) ⟨851981, by rfl⟩ : syracuseStep 1135975 = 1703963) B1703963
theorem B1135999 : Blo 1132632 1135999 := bstep (se 1 (by rfl) ⟨851999, by rfl⟩ : syracuseStep 1135999 = 1703999) B1703999
theorem B1136411 : Blo 1132632 1136411 := bstep (se 1 (by rfl) ⟨852308, by rfl⟩ : syracuseStep 1136411 = 1704617) B1704617
theorem B1136495 : Blo 1132632 1136495 := bstep (se 1 (by rfl) ⟨852371, by rfl⟩ : syracuseStep 1136495 = 1704743) B1704743
theorem B4315103 : Blo 1132632 4315103 := bstep (se 1 (by rfl) ⟨3236327, by rfl⟩ : syracuseStep 4315103 = 6472655) B6472655
theorem B13818377 : Blo 1132632 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B2153785 : Blo 1132632 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B7265693 : Blo 1132632 7265693 := bstep (se 3 (by rfl) ⟨1362317, by rfl⟩ : syracuseStep 7265693 = 2724635) B2724635
theorem B13819895 : Blo 1132632 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B8609975 : Blo 1132632 8609975 := bstep (se 1 (by rfl) ⟨6457481, by rfl⟩ : syracuseStep 8609975 = 12914963) B12914963
theorem B6906269 : Blo 1132632 6906269 := bstep (se 3 (by rfl) ⟨1294925, by rfl⟩ : syracuseStep 6906269 = 2589851) B2589851
theorem B41444621 : Blo 1132632 41444621 := bstep (se 3 (by rfl) ⟨7770866, by rfl⟩ : syracuseStep 41444621 = 15541733) B15541733
theorem B2549159 : Blo 1132632 2549159 := bstep (se 1 (by rfl) ⟨1911869, by rfl⟩ : syracuseStep 2549159 = 3823739) B3823739
theorem B8611433 : Blo 1132632 8611433 := bstep (se 2 (by rfl) ⟨3229287, by rfl⟩ : syracuseStep 8611433 = 6458575) B6458575
theorem B1436059 : Blo 1132632 1436059 := bstep (se 1 (by rfl) ⟨1077044, by rfl⟩ : syracuseStep 1436059 = 2154089) B2154089
theorem B2550527 : Blo 1132632 2550527 := bstep (se 1 (by rfl) ⟨1912895, by rfl⟩ : syracuseStep 2550527 = 3825791) B3825791
theorem B2550995 : Blo 1132632 2550995 := bstep (se 1 (by rfl) ⟨1913246, by rfl⟩ : syracuseStep 2550995 = 3826493) B3826493
theorem B1699193 : Blo 1132632 1699193 := bstep (se 2 (by rfl) ⟨637197, by rfl⟩ : syracuseStep 1699193 = 1274395) B1274395
theorem B2551247 : Blo 1132632 2551247 := bstep (se 1 (by rfl) ⟨1913435, by rfl⟩ : syracuseStep 2551247 = 3826871) B3826871
theorem B16347005 : Blo 1132632 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B2551787 : Blo 1132632 2551787 := bstep (se 1 (by rfl) ⟨1913840, by rfl⟩ : syracuseStep 2551787 = 3827681) B3827681
theorem B4911131 : Blo 1132632 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B2420975 : Blo 1132632 2420975 := bstep (se 1 (by rfl) ⟨1815731, by rfl⟩ : syracuseStep 2420975 = 3631463) B3631463
theorem B3830003 : Blo 1132632 3830003 := bstep (se 1 (by rfl) ⟨2872502, by rfl⟩ : syracuseStep 3830003 = 5745005) B5745005
theorem B2552489 : Blo 1132632 2552489 := bstep (se 2 (by rfl) ⟨957183, by rfl⟩ : syracuseStep 2552489 = 1914367) B1914367
theorem B1700711 : Blo 1132632 1700711 := bstep (se 1 (by rfl) ⟨1275533, by rfl⟩ : syracuseStep 1700711 = 2551067) B2551067
theorem B3274271 : Blo 1132632 3274271 := bstep (se 1 (by rfl) ⟨2455703, by rfl⟩ : syracuseStep 3274271 = 4911407) B4911407
theorem B2553407 : Blo 1132632 2553407 := bstep (se 1 (by rfl) ⟨1915055, by rfl⟩ : syracuseStep 2553407 = 3830111) B3830111
theorem B1701551 : Blo 1132632 1701551 := bstep (se 1 (by rfl) ⟨1276163, by rfl⟩ : syracuseStep 1701551 = 2552327) B2552327
theorem B1702175 : Blo 1132632 1702175 := bstep (se 1 (by rfl) ⟨1276631, by rfl⟩ : syracuseStep 1702175 = 2553263) B2553263
theorem B7272767 : Blo 1132632 7272767 := bstep (se 1 (by rfl) ⟨5454575, by rfl⟩ : syracuseStep 7272767 = 10909151) B10909151
theorem B1276231 : Blo 1132632 1276231 := bstep (se 1 (by rfl) ⟨957173, by rfl⟩ : syracuseStep 1276231 = 1914347) B1914347
theorem B14514983 : Blo 1132632 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B1276735 : Blo 1132632 1276735 := bstep (se 1 (by rfl) ⟨957551, by rfl⟩ : syracuseStep 1276735 = 1915103) B1915103
theorem B1702793 : Blo 1132632 1702793 := bstep (se 2 (by rfl) ⟨638547, by rfl⟩ : syracuseStep 1702793 = 1277095) B1277095
theorem B2554793 : Blo 1132632 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B3832865 : Blo 1132632 3832865 := bstep (se 2 (by rfl) ⟨1437324, by rfl⟩ : syracuseStep 3832865 = 2874649) B2874649
theorem B2555135 : Blo 1132632 2555135 := bstep (se 1 (by rfl) ⟨1916351, by rfl⟩ : syracuseStep 2555135 = 3832703) B3832703
theorem B3833567 : Blo 1132632 3833567 := bstep (se 1 (by rfl) ⟨2875175, by rfl⟩ : syracuseStep 3833567 = 5750351) B5750351
theorem B7274407 : Blo 1132632 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B3834215 : Blo 1132632 3834215 := bstep (se 1 (by rfl) ⟨2875661, by rfl⟩ : syracuseStep 3834215 = 5751323) B5751323
theorem B1704383 : Blo 1132632 1704383 := bstep (se 1 (by rfl) ⟨1278287, by rfl⟩ : syracuseStep 1704383 = 2556575) B2556575
theorem B2556395 : Blo 1132632 2556395 := bstep (se 1 (by rfl) ⟨1917296, by rfl⟩ : syracuseStep 2556395 = 3834593) B3834593
theorem B6455933 : Blo 1132632 6455933 := bstep (se 3 (by rfl) ⟨1210487, by rfl⟩ : syracuseStep 6455933 = 2420975) B2420975
theorem B18416717 : Blo 1132632 18416717 := bstep (se 3 (by rfl) ⟨3453134, by rfl⟩ : syracuseStep 18416717 = 6906269) B6906269
theorem B5442889 : Blo 1132632 5442889 := bstep (se 2 (by rfl) ⟨2041083, by rfl⟩ : syracuseStep 5442889 = 4082167) B4082167
theorem B5739497 : Blo 1132632 5739497 := bstep (se 2 (by rfl) ⟨2152311, by rfl⟩ : syracuseStep 5739497 = 4304623) B4304623
theorem B9213263 : Blo 1132632 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B5739983 : Blo 1132632 5739983 := bstep (se 1 (by rfl) ⟨4304987, by rfl⟩ : syracuseStep 5739983 = 8609975) B8609975
theorem B27629747 : Blo 1132632 27629747 := bstep (se 1 (by rfl) ⟨20722310, by rfl⟩ : syracuseStep 27629747 = 41444621) B41444621
theorem B5740955 : Blo 1132632 5740955 := bstep (se 1 (by rfl) ⟨4305716, by rfl⟩ : syracuseStep 5740955 = 8611433) B8611433
theorem B16358881 : Blo 1132632 16358881 := bstep (se 2 (by rfl) ⟨6134580, by rfl⟩ : syracuseStep 16358881 = 12269161) B12269161
theorem B9676655 : Blo 1132632 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B5450483 : Blo 1132632 5450483 := bstep (se 1 (by rfl) ⟨4087862, by rfl⟩ : syracuseStep 5450483 = 8175725) B8175725
theorem B10334303 : Blo 1132632 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B14562139 : Blo 1132632 14562139 := bstep (se 1 (by rfl) ⟨10921604, by rfl⟩ : syracuseStep 14562139 = 21843209) B21843209
theorem B1914745 : Blo 1132632 1914745 := bstep (se 2 (by rfl) ⟨718029, by rfl⟩ : syracuseStep 1914745 = 1436059) B1436059
theorem B5815655 : Blo 1132632 5815655 := bstep (se 1 (by rfl) ⟨4361741, by rfl⟩ : syracuseStep 5815655 = 8723483) B8723483
theorem B6471515 : Blo 1132632 6471515 := bstep (se 1 (by rfl) ⟨4853636, by rfl⟩ : syracuseStep 6471515 = 9707273) B9707273
theorem B46514843 : Blo 1132632 46514843 := bstep (se 1 (by rfl) ⟨34886132, by rfl⟩ : syracuseStep 46514843 = 69772265) B69772265
theorem B3064859 : Blo 1132632 3064859 := bstep (se 1 (by rfl) ⟨2298644, by rfl⟩ : syracuseStep 3064859 = 4597289) B4597289
theorem B36849005 : Blo 1132632 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B1132795 : Blo 1132632 1132795 := bstep (se 1 (by rfl) ⟨849596, by rfl⟩ : syracuseStep 1132795 = 1699193) B1699193
theorem B10898003 : Blo 1132632 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B3066599 : Blo 1132632 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B5753915 : Blo 1132632 5753915 := bstep (se 1 (by rfl) ⟨4315436, by rfl⟩ : syracuseStep 5753915 = 8630873) B8630873
theorem B1133807 : Blo 1132632 1133807 := bstep (se 1 (by rfl) ⟨850355, by rfl⟩ : syracuseStep 1133807 = 1700711) B1700711
theorem B2182847 : Blo 1132632 2182847 := bstep (se 1 (by rfl) ⟨1637135, by rfl⟩ : syracuseStep 2182847 = 3274271) B3274271
theorem B1134367 : Blo 1132632 1134367 := bstep (se 1 (by rfl) ⟨850775, by rfl⟩ : syracuseStep 1134367 = 1701551) B1701551
theorem B1134783 : Blo 1132632 1134783 := bstep (se 1 (by rfl) ⟨851087, by rfl⟩ : syracuseStep 1134783 = 1702175) B1702175
theorem B2871713 : Blo 1132632 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1135195 : Blo 1132632 1135195 := bstep (se 1 (by rfl) ⟨851396, by rfl⟩ : syracuseStep 1135195 = 1702793) B1702793
theorem B7263209 : Blo 1132632 7263209 := bstep (se 2 (by rfl) ⟨2723703, by rfl⟩ : syracuseStep 7263209 = 5447407) B5447407
theorem B3069011 : Blo 1132632 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B13096349 : Blo 1132632 13096349 := bstep (se 3 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 13096349 = 4911131) B4911131
theorem B7263847 : Blo 1132632 7263847 := bstep (se 1 (by rfl) ⟨5447885, by rfl⟩ : syracuseStep 7263847 = 10895771) B10895771
theorem B1136335 : Blo 1132632 1136335 := bstep (se 1 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 1136335 = 1704503) B1704503
theorem B2873171 : Blo 1132632 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1136551 : Blo 1132632 1136551 := bstep (se 1 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 1136551 = 1704827) B1704827
theorem B530012753 : Blo 1132632 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B16343315 : Blo 1132632 16343315 := bstep (se 1 (by rfl) ⟨12257486, by rfl⟩ : syracuseStep 16343315 = 24514973) B24514973
theorem B2876735 : Blo 1132632 2876735 := bstep (se 1 (by rfl) ⟨2157551, by rfl⟩ : syracuseStep 2876735 = 4315103) B4315103
theorem B4843795 : Blo 1132632 4843795 := bstep (se 1 (by rfl) ⟨3632846, by rfl⟩ : syracuseStep 4843795 = 7265693) B7265693
theorem B8612891 : Blo 1132632 8612891 := bstep (se 1 (by rfl) ⟨6459668, by rfl⟩ : syracuseStep 8612891 = 12919337) B12919337
theorem B10906811 : Blo 1132632 10906811 := bstep (se 1 (by rfl) ⟨8180108, by rfl⟩ : syracuseStep 10906811 = 16360217) B16360217
theorem B1699439 : Blo 1132632 1699439 := bstep (se 1 (by rfl) ⟨1274579, by rfl⟩ : syracuseStep 1699439 = 2549159) B2549159
theorem B1700351 : Blo 1132632 1700351 := bstep (se 1 (by rfl) ⟨1275263, by rfl⟩ : syracuseStep 1700351 = 2550527) B2550527
theorem B1700663 : Blo 1132632 1700663 := bstep (se 1 (by rfl) ⟨1275497, by rfl⟩ : syracuseStep 1700663 = 2550995) B2550995
theorem B1700831 : Blo 1132632 1700831 := bstep (se 1 (by rfl) ⟨1275623, by rfl⟩ : syracuseStep 1700831 = 2551247) B2551247
theorem B34108411 : Blo 1132632 34108411 := bstep (se 1 (by rfl) ⟨25581308, by rfl⟩ : syracuseStep 34108411 = 51162617) B51162617
theorem B1701191 : Blo 1132632 1701191 := bstep (se 1 (by rfl) ⟨1275893, by rfl⟩ : syracuseStep 1701191 = 2551787) B2551787
theorem B8615321 : Blo 1132632 8615321 := bstep (se 2 (by rfl) ⟨3230745, by rfl⟩ : syracuseStep 8615321 = 6461491) B6461491
theorem B2553335 : Blo 1132632 2553335 := bstep (se 1 (by rfl) ⟨1915001, by rfl⟩ : syracuseStep 2553335 = 3830003) B3830003
theorem B1701641 : Blo 1132632 1701641 := bstep (se 2 (by rfl) ⟨638115, by rfl⟩ : syracuseStep 1701641 = 1276231) B1276231
theorem B1701659 : Blo 1132632 1701659 := bstep (se 1 (by rfl) ⟨1276244, by rfl⟩ : syracuseStep 1701659 = 2552489) B2552489
theorem B3831947 : Blo 1132632 3831947 := bstep (se 1 (by rfl) ⟨2873960, by rfl⟩ : syracuseStep 3831947 = 5747921) B5747921
theorem B1702271 : Blo 1132632 1702271 := bstep (se 1 (by rfl) ⟨1276703, by rfl⟩ : syracuseStep 1702271 = 2553407) B2553407
theorem B1702313 : Blo 1132632 1702313 := bstep (se 2 (by rfl) ⟨638367, by rfl⟩ : syracuseStep 1702313 = 1276735) B1276735
theorem B2554721 : Blo 1132632 2554721 := bstep (se 2 (by rfl) ⟨958020, by rfl⟩ : syracuseStep 2554721 = 1916041) B1916041
theorem B4848511 : Blo 1132632 4848511 := bstep (se 1 (by rfl) ⟨3636383, by rfl⟩ : syracuseStep 4848511 = 7272767) B7272767
theorem B1703195 : Blo 1132632 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B2555243 : Blo 1132632 2555243 := bstep (se 1 (by rfl) ⟨1916432, by rfl⟩ : syracuseStep 2555243 = 3832865) B3832865
theorem B1703423 : Blo 1132632 1703423 := bstep (se 1 (by rfl) ⟨1277567, by rfl⟩ : syracuseStep 1703423 = 2555135) B2555135
theorem B2555711 : Blo 1132632 2555711 := bstep (se 1 (by rfl) ⟨1916783, by rfl⟩ : syracuseStep 2555711 = 3833567) B3833567
theorem B9699209 : Blo 1132632 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B2556143 : Blo 1132632 2556143 := bstep (se 1 (by rfl) ⟨1917107, by rfl⟩ : syracuseStep 2556143 = 3834215) B3834215
theorem B1704263 : Blo 1132632 1704263 := bstep (se 1 (by rfl) ⟨1278197, by rfl⟩ : syracuseStep 1704263 = 2556395) B2556395
theorem B3835943 : Blo 1132632 3835943 := bstep (se 1 (by rfl) ⟨2876957, by rfl⟩ : syracuseStep 3835943 = 5753915) B5753915
theorem B6458393 : Blo 1132632 6458393 := bstep (se 2 (by rfl) ⟨2421897, by rfl⟩ : syracuseStep 6458393 = 4843795) B4843795
theorem B18419831 : Blo 1132632 18419831 := bstep (se 1 (by rfl) ⟨13814873, by rfl⟩ : syracuseStep 18419831 = 27629747) B27629747
theorem B353341835 : Blo 1132632 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B5741927 : Blo 1132632 5741927 := bstep (se 1 (by rfl) ⟨4306445, by rfl⟩ : syracuseStep 5741927 = 8612891) B8612891
theorem B6889535 : Blo 1132632 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B5743547 : Blo 1132632 5743547 := bstep (se 1 (by rfl) ⟨4307660, by rfl⟩ : syracuseStep 5743547 = 8615321) B8615321
theorem B6464681 : Blo 1132632 6464681 := bstep (se 2 (by rfl) ⟨2424255, by rfl⟩ : syracuseStep 6464681 = 4848511) B4848511
theorem B3877103 : Blo 1132632 3877103 := bstep (se 1 (by rfl) ⟨2907827, by rfl⟩ : syracuseStep 3877103 = 5815655) B5815655
theorem B6466139 : Blo 1132632 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B4303955 : Blo 1132632 4303955 := bstep (se 1 (by rfl) ⟨3227966, by rfl⟩ : syracuseStep 4303955 = 6455933) B6455933
theorem B31009895 : Blo 1132632 31009895 := bstep (se 1 (by rfl) ⟨23257421, by rfl⟩ : syracuseStep 31009895 = 46514843) B46514843
theorem B2043239 : Blo 1132632 2043239 := bstep (se 1 (by rfl) ⟨1532429, by rfl⟩ : syracuseStep 2043239 = 3064859) B3064859
theorem B1914475 : Blo 1132632 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B2046007 : Blo 1132632 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B6142175 : Blo 1132632 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B8730899 : Blo 1132632 8730899 := bstep (se 1 (by rfl) ⟨6548174, by rfl⟩ : syracuseStep 8730899 = 13096349) B13096349
theorem B1915447 : Blo 1132632 1915447 := bstep (se 1 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 1915447 = 2873171) B2873171
theorem B7257185 : Blo 1132632 7257185 := bstep (se 2 (by rfl) ⟨2721444, by rfl⟩ : syracuseStep 7257185 = 5442889) B5442889
theorem B10895543 : Blo 1132632 10895543 := bstep (se 1 (by rfl) ⟨8171657, by rfl⟩ : syracuseStep 10895543 = 16343315) B16343315
theorem B1917823 : Blo 1132632 1917823 := bstep (se 1 (by rfl) ⟨1438367, by rfl⟩ : syracuseStep 1917823 = 2876735) B2876735
theorem B19416185 : Blo 1132632 19416185 := bstep (se 2 (by rfl) ⟨7281069, by rfl⟩ : syracuseStep 19416185 = 14562139) B14562139
theorem B8177597 : Blo 1132632 8177597 := bstep (se 3 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 8177597 = 3066599) B3066599
theorem B9685129 : Blo 1132632 9685129 := bstep (se 2 (by rfl) ⟨3631923, by rfl⟩ : syracuseStep 9685129 = 7263847) B7263847
theorem B1132959 : Blo 1132632 1132959 := bstep (se 1 (by rfl) ⟨849719, by rfl⟩ : syracuseStep 1132959 = 1699439) B1699439
theorem B1133567 : Blo 1132632 1133567 := bstep (se 1 (by rfl) ⟨850175, by rfl⟩ : syracuseStep 1133567 = 1700351) B1700351
theorem B1133775 : Blo 1132632 1133775 := bstep (se 1 (by rfl) ⟨850331, by rfl⟩ : syracuseStep 1133775 = 1700663) B1700663
theorem B1133887 : Blo 1132632 1133887 := bstep (se 1 (by rfl) ⟨850415, by rfl⟩ : syracuseStep 1133887 = 1700831) B1700831
theorem B1134127 : Blo 1132632 1134127 := bstep (se 1 (by rfl) ⟨850595, by rfl⟩ : syracuseStep 1134127 = 1701191) B1701191
theorem B1134427 : Blo 1132632 1134427 := bstep (se 1 (by rfl) ⟨850820, by rfl⟩ : syracuseStep 1134427 = 1701641) B1701641
theorem B1134439 : Blo 1132632 1134439 := bstep (se 1 (by rfl) ⟨850829, by rfl⟩ : syracuseStep 1134439 = 1701659) B1701659
theorem B1134847 : Blo 1132632 1134847 := bstep (se 1 (by rfl) ⟨851135, by rfl⟩ : syracuseStep 1134847 = 1702271) B1702271
theorem B1134875 : Blo 1132632 1134875 := bstep (se 1 (by rfl) ⟨851156, by rfl⟩ : syracuseStep 1134875 = 1702313) B1702313
theorem B5820925 : Blo 1132632 5820925 := bstep (se 3 (by rfl) ⟨1091423, by rfl⟩ : syracuseStep 5820925 = 2182847) B2182847
theorem B21811841 : Blo 1132632 21811841 := bstep (se 2 (by rfl) ⟨8179440, by rfl⟩ : syracuseStep 21811841 = 16358881) B16358881
theorem B1135463 : Blo 1132632 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B1135615 : Blo 1132632 1135615 := bstep (se 1 (by rfl) ⟨851711, by rfl⟩ : syracuseStep 1135615 = 1703423) B1703423
theorem B4314343 : Blo 1132632 4314343 := bstep (se 1 (by rfl) ⟨3235757, by rfl⟩ : syracuseStep 4314343 = 6471515) B6471515
theorem B1136255 : Blo 1132632 1136255 := bstep (se 1 (by rfl) ⟨852191, by rfl⟩ : syracuseStep 1136255 = 1704383) B1704383
theorem B12277811 : Blo 1132632 12277811 := bstep (se 1 (by rfl) ⟨9208358, by rfl⟩ : syracuseStep 12277811 = 18416717) B18416717
theorem B24566003 : Blo 1132632 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B7265335 : Blo 1132632 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B4842139 : Blo 1132632 4842139 := bstep (se 1 (by rfl) ⟨3631604, by rfl⟩ : syracuseStep 4842139 = 7263209) B7263209
theorem B3826331 : Blo 1132632 3826331 := bstep (se 1 (by rfl) ⟨2869748, by rfl⟩ : syracuseStep 3826331 = 5739497) B5739497
theorem B3826655 : Blo 1132632 3826655 := bstep (se 1 (by rfl) ⟨2869991, by rfl⟩ : syracuseStep 3826655 = 5739983) B5739983
theorem B3827303 : Blo 1132632 3827303 := bstep (se 1 (by rfl) ⟨2870477, by rfl⟩ : syracuseStep 3827303 = 5740955) B5740955
theorem B6451103 : Blo 1132632 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B45477881 : Blo 1132632 45477881 := bstep (se 2 (by rfl) ⟨17054205, by rfl⟩ : syracuseStep 45477881 = 34108411) B34108411
theorem B3633655 : Blo 1132632 3633655 := bstep (se 1 (by rfl) ⟨2725241, by rfl⟩ : syracuseStep 3633655 = 5450483) B5450483
theorem B7271207 : Blo 1132632 7271207 := bstep (se 1 (by rfl) ⟨5453405, by rfl⟩ : syracuseStep 7271207 = 10906811) B10906811
theorem B2552993 : Blo 1132632 2552993 := bstep (se 2 (by rfl) ⟨957372, by rfl⟩ : syracuseStep 2552993 = 1914745) B1914745
theorem B1702223 : Blo 1132632 1702223 := bstep (se 1 (by rfl) ⟨1276667, by rfl⟩ : syracuseStep 1702223 = 2553335) B2553335
theorem B2554631 : Blo 1132632 2554631 := bstep (se 1 (by rfl) ⟨1915973, by rfl⟩ : syracuseStep 2554631 = 3831947) B3831947
theorem B1703147 : Blo 1132632 1703147 := bstep (se 1 (by rfl) ⟨1277360, by rfl⟩ : syracuseStep 1703147 = 2554721) B2554721
theorem B1703495 : Blo 1132632 1703495 := bstep (se 1 (by rfl) ⟨1277621, by rfl⟩ : syracuseStep 1703495 = 2555243) B2555243
theorem B1703807 : Blo 1132632 1703807 := bstep (se 1 (by rfl) ⟨1277855, by rfl⟩ : syracuseStep 1703807 = 2555711) B2555711
theorem B1704095 : Blo 1132632 1704095 := bstep (se 1 (by rfl) ⟨1278071, by rfl⟩ : syracuseStep 1704095 = 2556143) B2556143
theorem B12944123 : Blo 1132632 12944123 := bstep (se 1 (by rfl) ⟨9708092, by rfl⟩ : syracuseStep 12944123 = 19416185) B19416185
theorem B6456185 : Blo 1132632 6456185 := bstep (se 2 (by rfl) ⟨2421069, by rfl⟩ : syracuseStep 6456185 = 4842139) B4842139
theorem B2557097 : Blo 1132632 2557097 := bstep (se 2 (by rfl) ⟨958911, by rfl⟩ : syracuseStep 2557097 = 1917823) B1917823
theorem B2557295 : Blo 1132632 2557295 := bstep (se 1 (by rfl) ⟨1917971, by rfl⟩ : syracuseStep 2557295 = 3835943) B3835943
theorem B12913505 : Blo 1132632 12913505 := bstep (se 2 (by rfl) ⟨4842564, by rfl⟩ : syracuseStep 12913505 = 9685129) B9685129
theorem B4593023 : Blo 1132632 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B4300735 : Blo 1132632 4300735 := bstep (se 1 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 4300735 = 6451103) B6451103
theorem B30318587 : Blo 1132632 30318587 := bstep (se 1 (by rfl) ⟨22738940, by rfl⟩ : syracuseStep 30318587 = 45477881) B45477881
theorem B2728009 : Blo 1132632 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B5448637 : Blo 1132632 5448637 := bstep (se 3 (by rfl) ⟨1021619, by rfl⟩ : syracuseStep 5448637 = 2043239) B2043239
theorem B5451731 : Blo 1132632 5451731 := bstep (se 1 (by rfl) ⟨4088798, by rfl⟩ : syracuseStep 5451731 = 8177597) B8177597
theorem B4305595 : Blo 1132632 4305595 := bstep (se 1 (by rfl) ⟨3229196, by rfl⟩ : syracuseStep 4305595 = 6458393) B6458393
theorem B10338941 : Blo 1132632 10338941 := bstep (se 3 (by rfl) ⟨1938551, by rfl⟩ : syracuseStep 10338941 = 3877103) B3877103
theorem B4309787 : Blo 1132632 4309787 := bstep (se 1 (by rfl) ⟨3232340, by rfl⟩ : syracuseStep 4309787 = 6464681) B6464681
theorem B5752457 : Blo 1132632 5752457 := bstep (se 2 (by rfl) ⟨2157171, by rfl⟩ : syracuseStep 5752457 = 4314343) B4314343
theorem B4310759 : Blo 1132632 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B2869303 : Blo 1132632 2869303 := bstep (se 1 (by rfl) ⟨2151977, by rfl⟩ : syracuseStep 2869303 = 4303955) B4303955
theorem B9687113 : Blo 1132632 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B5820599 : Blo 1132632 5820599 := bstep (se 1 (by rfl) ⟨4365449, by rfl⟩ : syracuseStep 5820599 = 8730899) B8730899
theorem B1134815 : Blo 1132632 1134815 := bstep (se 1 (by rfl) ⟨851111, by rfl⟩ : syracuseStep 1134815 = 1702223) B1702223
theorem B4838123 : Blo 1132632 4838123 := bstep (se 1 (by rfl) ⟨3628592, by rfl⟩ : syracuseStep 4838123 = 7257185) B7257185
theorem B1135431 : Blo 1132632 1135431 := bstep (se 1 (by rfl) ⟨851573, by rfl⟩ : syracuseStep 1135431 = 1703147) B1703147
theorem B1135663 : Blo 1132632 1135663 := bstep (se 1 (by rfl) ⟨851747, by rfl⟩ : syracuseStep 1135663 = 1703495) B1703495
theorem B1135871 : Blo 1132632 1135871 := bstep (se 1 (by rfl) ⟨851903, by rfl⟩ : syracuseStep 1135871 = 1703807) B1703807
theorem B7263695 : Blo 1132632 7263695 := bstep (se 1 (by rfl) ⟨5447771, by rfl⟩ : syracuseStep 7263695 = 10895543) B10895543
theorem B1136175 : Blo 1132632 1136175 := bstep (se 1 (by rfl) ⟨852131, by rfl⟩ : syracuseStep 1136175 = 1704263) B1704263
theorem B12279887 : Blo 1132632 12279887 := bstep (se 1 (by rfl) ⟨9209915, by rfl⟩ : syracuseStep 12279887 = 18419831) B18419831
theorem B235561223 : Blo 1132632 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B14541227 : Blo 1132632 14541227 := bstep (se 1 (by rfl) ⟨10905920, by rfl⟩ : syracuseStep 14541227 = 21811841) B21811841
theorem B8185207 : Blo 1132632 8185207 := bstep (se 1 (by rfl) ⟨6138905, by rfl⟩ : syracuseStep 8185207 = 12277811) B12277811
theorem B16377335 : Blo 1132632 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B3827951 : Blo 1132632 3827951 := bstep (se 1 (by rfl) ⟨2870963, by rfl⟩ : syracuseStep 3827951 = 5741927) B5741927
theorem B2550887 : Blo 1132632 2550887 := bstep (se 1 (by rfl) ⟨1913165, by rfl⟩ : syracuseStep 2550887 = 3826331) B3826331
theorem B3829031 : Blo 1132632 3829031 := bstep (se 1 (by rfl) ⟨2871773, by rfl⟩ : syracuseStep 3829031 = 5743547) B5743547
theorem B2551103 : Blo 1132632 2551103 := bstep (se 1 (by rfl) ⟨1913327, by rfl⟩ : syracuseStep 2551103 = 3826655) B3826655
theorem B4844873 : Blo 1132632 4844873 := bstep (se 2 (by rfl) ⟨1816827, by rfl⟩ : syracuseStep 4844873 = 3633655) B3633655
theorem B7761233 : Blo 1132632 7761233 := bstep (se 2 (by rfl) ⟨2910462, by rfl⟩ : syracuseStep 7761233 = 5820925) B5820925
theorem B2551535 : Blo 1132632 2551535 := bstep (se 1 (by rfl) ⟨1913651, by rfl⟩ : syracuseStep 2551535 = 3827303) B3827303
theorem B20673263 : Blo 1132632 20673263 := bstep (se 1 (by rfl) ⟨15504947, by rfl⟩ : syracuseStep 20673263 = 31009895) B31009895
theorem B2552633 : Blo 1132632 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B4847471 : Blo 1132632 4847471 := bstep (se 1 (by rfl) ⟨3635603, by rfl⟩ : syracuseStep 4847471 = 7271207) B7271207
theorem B2553929 : Blo 1132632 2553929 := bstep (se 2 (by rfl) ⟨957723, by rfl⟩ : syracuseStep 2553929 = 1915447) B1915447
theorem B1701995 : Blo 1132632 1701995 := bstep (se 1 (by rfl) ⟨1276496, by rfl⟩ : syracuseStep 1701995 = 2552993) B2552993
theorem B4094783 : Blo 1132632 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B1703087 : Blo 1132632 1703087 := bstep (se 1 (by rfl) ⟨1277315, by rfl⟩ : syracuseStep 1703087 = 2554631) B2554631
theorem B14549381 : Blo 1132632 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B628163261 : Blo 1132632 628163261 := bstep (se 3 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 628163261 = 235561223) B235561223
theorem B1704731 : Blo 1132632 1704731 := bstep (se 1 (by rfl) ⟨1278548, by rfl⟩ : syracuseStep 1704731 = 2557097) B2557097
theorem B1704863 : Blo 1132632 1704863 := bstep (se 1 (by rfl) ⟨1278647, by rfl⟩ : syracuseStep 1704863 = 2557295) B2557295
theorem B3834971 : Blo 1132632 3834971 := bstep (se 1 (by rfl) ⟨2876228, by rfl⟩ : syracuseStep 3834971 = 5752457) B5752457
theorem B10913609 : Blo 1132632 10913609 := bstep (se 2 (by rfl) ⟨4092603, by rfl⟩ : syracuseStep 10913609 = 8185207) B8185207
theorem B6458075 : Blo 1132632 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B5740793 : Blo 1132632 5740793 := bstep (se 2 (by rfl) ⟨2152797, by rfl⟩ : syracuseStep 5740793 = 4305595) B4305595
theorem B10918223 : Blo 1132632 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B2729855 : Blo 1132632 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B6892627 : Blo 1132632 6892627 := bstep (se 1 (by rfl) ⟨5169470, by rfl⟩ : syracuseStep 6892627 = 10338941) B10338941
theorem B8629415 : Blo 1132632 8629415 := bstep (se 1 (by rfl) ⟨6472061, by rfl⟩ : syracuseStep 8629415 = 12944123) B12944123
theorem B4304123 : Blo 1132632 4304123 := bstep (se 1 (by rfl) ⟨3228092, by rfl⟩ : syracuseStep 4304123 = 6456185) B6456185
theorem B55128701 : Blo 1132632 55128701 := bstep (se 3 (by rfl) ⟨10336631, by rfl⟩ : syracuseStep 55128701 = 20673263) B20673263
theorem B3880399 : Blo 1132632 3880399 := bstep (se 1 (by rfl) ⟨2910299, by rfl⟩ : syracuseStep 3880399 = 5820599) B5820599
theorem B3225415 : Blo 1132632 3225415 := bstep (se 1 (by rfl) ⟨2419061, by rfl⟩ : syracuseStep 3225415 = 4838123) B4838123
theorem B3062015 : Blo 1132632 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B3229915 : Blo 1132632 3229915 := bstep (se 1 (by rfl) ⟨2422436, by rfl⟩ : syracuseStep 3229915 = 4844873) B4844873
theorem B3231647 : Blo 1132632 3231647 := bstep (se 1 (by rfl) ⟨2423735, by rfl⟩ : syracuseStep 3231647 = 4847471) B4847471
theorem B1134663 : Blo 1132632 1134663 := bstep (se 1 (by rfl) ⟨850997, by rfl⟩ : syracuseStep 1134663 = 1701995) B1701995
theorem B1135391 : Blo 1132632 1135391 := bstep (se 1 (by rfl) ⟨851543, by rfl⟩ : syracuseStep 1135391 = 1703087) B1703087
theorem B1136063 : Blo 1132632 1136063 := bstep (se 1 (by rfl) ⟨852047, by rfl⟩ : syracuseStep 1136063 = 1704095) B1704095
theorem B2873191 : Blo 1132632 2873191 := bstep (se 1 (by rfl) ⟨2154893, by rfl⟩ : syracuseStep 2873191 = 4309787) B4309787
theorem B2873839 : Blo 1132632 2873839 := bstep (se 1 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 2873839 = 4310759) B4310759
theorem B7264849 : Blo 1132632 7264849 := bstep (se 2 (by rfl) ⟨2724318, by rfl⟩ : syracuseStep 7264849 = 5448637) B5448637
theorem B8609003 : Blo 1132632 8609003 := bstep (se 1 (by rfl) ⟨6456752, by rfl⟩ : syracuseStep 8609003 = 12913505) B12913505
theorem B3825737 : Blo 1132632 3825737 := bstep (se 2 (by rfl) ⟨1434651, by rfl⟩ : syracuseStep 3825737 = 2869303) B2869303
theorem B4842463 : Blo 1132632 4842463 := bstep (se 1 (by rfl) ⟨3631847, by rfl⟩ : syracuseStep 4842463 = 7263695) B7263695
theorem B20212391 : Blo 1132632 20212391 := bstep (se 1 (by rfl) ⟨15159293, by rfl⟩ : syracuseStep 20212391 = 30318587) B30318587
theorem B8186591 : Blo 1132632 8186591 := bstep (se 1 (by rfl) ⟨6139943, by rfl⟩ : syracuseStep 8186591 = 12279887) B12279887
theorem B9694151 : Blo 1132632 9694151 := bstep (se 1 (by rfl) ⟨7270613, by rfl⟩ : syracuseStep 9694151 = 14541227) B14541227
theorem B2551967 : Blo 1132632 2551967 := bstep (se 1 (by rfl) ⟨1913975, by rfl⟩ : syracuseStep 2551967 = 3827951) B3827951
theorem B1700591 : Blo 1132632 1700591 := bstep (se 1 (by rfl) ⟨1275443, by rfl⟩ : syracuseStep 1700591 = 2550887) B2550887
theorem B2552687 : Blo 1132632 2552687 := bstep (se 1 (by rfl) ⟨1914515, by rfl⟩ : syracuseStep 2552687 = 3829031) B3829031
theorem B1700735 : Blo 1132632 1700735 := bstep (se 1 (by rfl) ⟨1275551, by rfl⟩ : syracuseStep 1700735 = 2551103) B2551103
theorem B5174155 : Blo 1132632 5174155 := bstep (se 1 (by rfl) ⟨3880616, by rfl⟩ : syracuseStep 5174155 = 7761233) B7761233
theorem B1701023 : Blo 1132632 1701023 := bstep (se 1 (by rfl) ⟨1275767, by rfl⟩ : syracuseStep 1701023 = 2551535) B2551535
theorem B3634487 : Blo 1132632 3634487 := bstep (se 1 (by rfl) ⟨2725865, by rfl⟩ : syracuseStep 3634487 = 5451731) B5451731
theorem B1701755 : Blo 1132632 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B1702619 : Blo 1132632 1702619 := bstep (se 1 (by rfl) ⟨1276964, by rfl⟩ : syracuseStep 1702619 = 2553929) B2553929
theorem B5734313 : Blo 1132632 5734313 := bstep (se 2 (by rfl) ⟨2150367, by rfl⟩ : syracuseStep 5734313 = 4300735) B4300735
theorem B9699587 : Blo 1132632 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B418775507 : Blo 1132632 418775507 := bstep (se 1 (by rfl) ⟨314081630, by rfl⟩ : syracuseStep 418775507 = 628163261) B628163261
theorem B2556647 : Blo 1132632 2556647 := bstep (se 1 (by rfl) ⟨1917485, by rfl⟩ : syracuseStep 2556647 = 3834971) B3834971
theorem B7275739 : Blo 1132632 7275739 := bstep (se 1 (by rfl) ⟨5456804, by rfl⟩ : syracuseStep 7275739 = 10913609) B10913609
theorem B6456617 : Blo 1132632 6456617 := bstep (se 2 (by rfl) ⟨2421231, by rfl⟩ : syracuseStep 6456617 = 4842463) B4842463
theorem B7278815 : Blo 1132632 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B5739335 : Blo 1132632 5739335 := bstep (se 1 (by rfl) ⟨4304501, by rfl⟩ : syracuseStep 5739335 = 8609003) B8609003
theorem B13474927 : Blo 1132632 13474927 := bstep (se 1 (by rfl) ⟨10106195, by rfl⟩ : syracuseStep 13474927 = 20212391) B20212391
theorem B6462767 : Blo 1132632 6462767 := bstep (se 1 (by rfl) ⟨4847075, by rfl⟩ : syracuseStep 6462767 = 9694151) B9694151
theorem B4300553 : Blo 1132632 4300553 := bstep (se 2 (by rfl) ⟨1612707, by rfl⟩ : syracuseStep 4300553 = 3225415) B3225415
theorem B2041343 : Blo 1132632 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B4305383 : Blo 1132632 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B4306553 : Blo 1132632 4306553 := bstep (se 2 (by rfl) ⟨1614957, by rfl⟩ : syracuseStep 4306553 = 3229915) B3229915
theorem B9190169 : Blo 1132632 9190169 := bstep (se 2 (by rfl) ⟨3446313, by rfl⟩ : syracuseStep 9190169 = 6892627) B6892627
theorem B6898873 : Blo 1132632 6898873 := bstep (se 2 (by rfl) ⟨2587077, by rfl⟩ : syracuseStep 6898873 = 5174155) B5174155
theorem B1819903 : Blo 1132632 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B5457727 : Blo 1132632 5457727 := bstep (se 1 (by rfl) ⟨4093295, by rfl⟩ : syracuseStep 5457727 = 8186591) B8186591
theorem B5752943 : Blo 1132632 5752943 := bstep (se 1 (by rfl) ⟨4314707, by rfl⟩ : syracuseStep 5752943 = 8629415) B8629415
theorem B2869415 : Blo 1132632 2869415 := bstep (se 1 (by rfl) ⟨2152061, by rfl⟩ : syracuseStep 2869415 = 4304123) B4304123
theorem B36752467 : Blo 1132632 36752467 := bstep (se 1 (by rfl) ⟨27564350, by rfl⟩ : syracuseStep 36752467 = 55128701) B55128701
theorem B1133727 : Blo 1132632 1133727 := bstep (se 1 (by rfl) ⟨850295, by rfl⟩ : syracuseStep 1133727 = 1700591) B1700591
theorem B1133823 : Blo 1132632 1133823 := bstep (se 1 (by rfl) ⟨850367, by rfl⟩ : syracuseStep 1133823 = 1700735) B1700735
theorem B1134015 : Blo 1132632 1134015 := bstep (se 1 (by rfl) ⟨850511, by rfl⟩ : syracuseStep 1134015 = 1701023) B1701023
theorem B9686465 : Blo 1132632 9686465 := bstep (se 2 (by rfl) ⟨3632424, by rfl⟩ : syracuseStep 9686465 = 7264849) B7264849
theorem B1134503 : Blo 1132632 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B1135079 : Blo 1132632 1135079 := bstep (se 1 (by rfl) ⟨851309, by rfl⟩ : syracuseStep 1135079 = 1702619) B1702619
theorem B3822875 : Blo 1132632 3822875 := bstep (se 1 (by rfl) ⟨2867156, by rfl⟩ : syracuseStep 3822875 = 5734313) B5734313
theorem B1136487 : Blo 1132632 1136487 := bstep (se 1 (by rfl) ⟨852365, by rfl⟩ : syracuseStep 1136487 = 1704731) B1704731
theorem B1136575 : Blo 1132632 1136575 := bstep (se 1 (by rfl) ⟨852431, by rfl⟩ : syracuseStep 1136575 = 1704863) B1704863
theorem B2154431 : Blo 1132632 2154431 := bstep (se 1 (by rfl) ⟨1615823, by rfl⟩ : syracuseStep 2154431 = 3231647) B3231647
theorem B3827195 : Blo 1132632 3827195 := bstep (se 1 (by rfl) ⟨2870396, by rfl⟩ : syracuseStep 3827195 = 5740793) B5740793
theorem B2550491 : Blo 1132632 2550491 := bstep (se 1 (by rfl) ⟨1912868, by rfl⟩ : syracuseStep 2550491 = 3825737) B3825737
theorem B5173865 : Blo 1132632 5173865 := bstep (se 2 (by rfl) ⟨1940199, by rfl⟩ : syracuseStep 5173865 = 3880399) B3880399
theorem B3830921 : Blo 1132632 3830921 := bstep (se 2 (by rfl) ⟨1436595, by rfl⟩ : syracuseStep 3830921 = 2873191) B2873191
theorem B1701311 : Blo 1132632 1701311 := bstep (se 1 (by rfl) ⟨1275983, by rfl⟩ : syracuseStep 1701311 = 2551967) B2551967
theorem B1701791 : Blo 1132632 1701791 := bstep (se 1 (by rfl) ⟨1276343, by rfl⟩ : syracuseStep 1701791 = 2552687) B2552687
theorem B3831785 : Blo 1132632 3831785 := bstep (se 2 (by rfl) ⟨1436919, by rfl⟩ : syracuseStep 3831785 = 2873839) B2873839
theorem B2422991 : Blo 1132632 2422991 := bstep (se 1 (by rfl) ⟨1817243, by rfl⟩ : syracuseStep 2422991 = 3634487) B3634487
theorem B279183671 : Blo 1132632 279183671 := bstep (se 1 (by rfl) ⟨209387753, by rfl⟩ : syracuseStep 279183671 = 418775507) B418775507
theorem B1704431 : Blo 1132632 1704431 := bstep (se 1 (by rfl) ⟨1278323, by rfl⟩ : syracuseStep 1704431 = 2556647) B2556647
theorem B3835295 : Blo 1132632 3835295 := bstep (se 1 (by rfl) ⟨2876471, by rfl⟩ : syracuseStep 3835295 = 5752943) B5752943
theorem B9700985 : Blo 1132632 9700985 := bstep (se 2 (by rfl) ⟨3637869, by rfl⟩ : syracuseStep 9700985 = 7275739) B7275739
theorem B2426537 : Blo 1132632 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B6457643 : Blo 1132632 6457643 := bstep (se 1 (by rfl) ⟨4843232, by rfl⟩ : syracuseStep 6457643 = 9686465) B9686465
theorem B7276969 : Blo 1132632 7276969 := bstep (se 2 (by rfl) ⟨2728863, by rfl⟩ : syracuseStep 7276969 = 5457727) B5457727
theorem B4852543 : Blo 1132632 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B6461309 : Blo 1132632 6461309 := bstep (se 3 (by rfl) ⟨1211495, by rfl⟩ : syracuseStep 6461309 = 2422991) B2422991
theorem B71866277 : Blo 1132632 71866277 := bstep (se 4 (by rfl) ⟨6737463, by rfl⟩ : syracuseStep 71866277 = 13474927) B13474927
theorem B3449243 : Blo 1132632 3449243 := bstep (se 1 (by rfl) ⟨2586932, by rfl⟩ : syracuseStep 3449243 = 5173865) B5173865
theorem B6466391 : Blo 1132632 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B4304411 : Blo 1132632 4304411 := bstep (se 1 (by rfl) ⟨3228308, by rfl⟩ : syracuseStep 4304411 = 6456617) B6456617
theorem B1912943 : Blo 1132632 1912943 := bstep (se 1 (by rfl) ⟨1434707, by rfl⟩ : syracuseStep 1912943 = 2869415) B2869415
theorem B49003289 : Blo 1132632 49003289 := bstep (se 2 (by rfl) ⟨18376233, by rfl⟩ : syracuseStep 49003289 = 36752467) B36752467
theorem B4308511 : Blo 1132632 4308511 := bstep (se 1 (by rfl) ⟨3231383, by rfl⟩ : syracuseStep 4308511 = 6462767) B6462767
theorem B2867035 : Blo 1132632 2867035 := bstep (se 1 (by rfl) ⟨2150276, by rfl⟩ : syracuseStep 2867035 = 4300553) B4300553
theorem B1360895 : Blo 1132632 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B2870255 : Blo 1132632 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B1134207 : Blo 1132632 1134207 := bstep (se 1 (by rfl) ⟨850655, by rfl⟩ : syracuseStep 1134207 = 1701311) B1701311
theorem B2871035 : Blo 1132632 2871035 := bstep (se 1 (by rfl) ⟨2153276, by rfl⟩ : syracuseStep 2871035 = 4306553) B4306553
theorem B1134527 : Blo 1132632 1134527 := bstep (se 1 (by rfl) ⟨850895, by rfl⟩ : syracuseStep 1134527 = 1701791) B1701791
theorem B9198497 : Blo 1132632 9198497 := bstep (se 2 (by rfl) ⟨3449436, by rfl⟩ : syracuseStep 9198497 = 6898873) B6898873
theorem B3826223 : Blo 1132632 3826223 := bstep (se 1 (by rfl) ⟨2869667, by rfl⟩ : syracuseStep 3826223 = 5739335) B5739335
theorem B2548583 : Blo 1132632 2548583 := bstep (se 1 (by rfl) ⟨1911437, by rfl⟩ : syracuseStep 2548583 = 3822875) B3822875
theorem B1436287 : Blo 1132632 1436287 := bstep (se 1 (by rfl) ⟨1077215, by rfl⟩ : syracuseStep 1436287 = 2154431) B2154431
theorem B2551463 : Blo 1132632 2551463 := bstep (se 1 (by rfl) ⟨1913597, by rfl⟩ : syracuseStep 2551463 = 3827195) B3827195
theorem B1700327 : Blo 1132632 1700327 := bstep (se 1 (by rfl) ⟨1275245, by rfl⟩ : syracuseStep 1700327 = 2550491) B2550491
theorem B2553947 : Blo 1132632 2553947 := bstep (se 1 (by rfl) ⟨1915460, by rfl⟩ : syracuseStep 2553947 = 3830921) B3830921
theorem B2554523 : Blo 1132632 2554523 := bstep (se 1 (by rfl) ⟨1915892, by rfl⟩ : syracuseStep 2554523 = 3831785) B3831785
theorem B6126779 : Blo 1132632 6126779 := bstep (se 1 (by rfl) ⟨4595084, by rfl⟩ : syracuseStep 6126779 = 9190169) B9190169
theorem B186122447 : Blo 1132632 186122447 := bstep (se 1 (by rfl) ⟨139591835, by rfl⟩ : syracuseStep 186122447 = 279183671) B279183671
theorem B2556863 : Blo 1132632 2556863 := bstep (se 1 (by rfl) ⟨1917647, by rfl⟩ : syracuseStep 2556863 = 3835295) B3835295
theorem B9702625 : Blo 1132632 9702625 := bstep (se 2 (by rfl) ⟨3638484, by rfl⟩ : syracuseStep 9702625 = 7276969) B7276969
theorem B47910851 : Blo 1132632 47910851 := bstep (se 1 (by rfl) ⟨35933138, by rfl⟩ : syracuseStep 47910851 = 71866277) B71866277
theorem B6132331 : Blo 1132632 6132331 := bstep (se 1 (by rfl) ⟨4599248, by rfl⟩ : syracuseStep 6132331 = 9198497) B9198497
theorem B5744681 : Blo 1132632 5744681 := bstep (se 2 (by rfl) ⟨2154255, by rfl⟩ : syracuseStep 5744681 = 4308511) B4308511
theorem B6467323 : Blo 1132632 6467323 := bstep (se 1 (by rfl) ⟨4850492, by rfl⟩ : syracuseStep 6467323 = 9700985) B9700985
theorem B4305095 : Blo 1132632 4305095 := bstep (se 1 (by rfl) ⟨3228821, by rfl⟩ : syracuseStep 4305095 = 6457643) B6457643
theorem B1913503 : Blo 1132632 1913503 := bstep (se 1 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 1913503 = 2870255) B2870255
theorem B1914023 : Blo 1132632 1914023 := bstep (se 1 (by rfl) ⟨1435517, by rfl⟩ : syracuseStep 1914023 = 2871035) B2871035
theorem B1915049 : Blo 1132632 1915049 := bstep (se 2 (by rfl) ⟨718143, by rfl⟩ : syracuseStep 1915049 = 1436287) B1436287
theorem B6470057 : Blo 1132632 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B4307539 : Blo 1132632 4307539 := bstep (se 1 (by rfl) ⟨3230654, by rfl⟩ : syracuseStep 4307539 = 6461309) B6461309
theorem B6470765 : Blo 1132632 6470765 := bstep (se 3 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 6470765 = 2426537) B2426537
theorem B4310927 : Blo 1132632 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B2869607 : Blo 1132632 2869607 := bstep (se 1 (by rfl) ⟨2152205, by rfl⟩ : syracuseStep 2869607 = 4304411) B4304411
theorem B1133551 : Blo 1132632 1133551 := bstep (se 1 (by rfl) ⟨850163, by rfl⟩ : syracuseStep 1133551 = 1700327) B1700327
theorem B4084519 : Blo 1132632 4084519 := bstep (se 1 (by rfl) ⟨3063389, by rfl⟩ : syracuseStep 4084519 = 6126779) B6126779
theorem B3822713 : Blo 1132632 3822713 := bstep (se 2 (by rfl) ⟨1433517, by rfl⟩ : syracuseStep 3822713 = 2867035) B2867035
theorem B1136287 : Blo 1132632 1136287 := bstep (se 1 (by rfl) ⟨852215, by rfl⟩ : syracuseStep 1136287 = 1704431) B1704431
theorem B9197981 : Blo 1132632 9197981 := bstep (se 3 (by rfl) ⟨1724621, by rfl⟩ : syracuseStep 9197981 = 3449243) B3449243
theorem B3629053 : Blo 1132632 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B2550815 : Blo 1132632 2550815 := bstep (se 1 (by rfl) ⟨1913111, by rfl⟩ : syracuseStep 2550815 = 3826223) B3826223
theorem B1699055 : Blo 1132632 1699055 := bstep (se 1 (by rfl) ⟨1274291, by rfl⟩ : syracuseStep 1699055 = 2548583) B2548583
theorem B1700975 : Blo 1132632 1700975 := bstep (se 1 (by rfl) ⟨1275731, by rfl⟩ : syracuseStep 1700975 = 2551463) B2551463
theorem B1275295 : Blo 1132632 1275295 := bstep (se 1 (by rfl) ⟨956471, by rfl⟩ : syracuseStep 1275295 = 1912943) B1912943
theorem B1702631 : Blo 1132632 1702631 := bstep (se 1 (by rfl) ⟨1276973, by rfl⟩ : syracuseStep 1702631 = 2553947) B2553947
theorem B1703015 : Blo 1132632 1703015 := bstep (se 1 (by rfl) ⟨1277261, by rfl⟩ : syracuseStep 1703015 = 2554523) B2554523
theorem B32668859 : Blo 1132632 32668859 := bstep (se 1 (by rfl) ⟨24501644, by rfl⟩ : syracuseStep 32668859 = 49003289) B49003289
theorem B1704575 : Blo 1132632 1704575 := bstep (se 1 (by rfl) ⟨1278431, by rfl⟩ : syracuseStep 1704575 = 2556863) B2556863
theorem B32705765 : Blo 1132632 32705765 := bstep (se 4 (by rfl) ⟨3066165, by rfl⟩ : syracuseStep 32705765 = 6132331) B6132331
theorem B6131987 : Blo 1132632 6131987 := bstep (se 1 (by rfl) ⟨4598990, by rfl⟩ : syracuseStep 6131987 = 9197981) B9197981
theorem B8623097 : Blo 1132632 8623097 := bstep (se 2 (by rfl) ⟨3233661, by rfl⟩ : syracuseStep 8623097 = 6467323) B6467323
theorem B5446025 : Blo 1132632 5446025 := bstep (se 2 (by rfl) ⟨2042259, by rfl⟩ : syracuseStep 5446025 = 4084519) B4084519
theorem B5743385 : Blo 1132632 5743385 := bstep (se 2 (by rfl) ⟨2153769, by rfl⟩ : syracuseStep 5743385 = 4307539) B4307539
theorem B1913071 : Blo 1132632 1913071 := bstep (se 1 (by rfl) ⟨1434803, by rfl⟩ : syracuseStep 1913071 = 2869607) B2869607
theorem B1132703 : Blo 1132632 1132703 := bstep (se 1 (by rfl) ⟨849527, by rfl⟩ : syracuseStep 1132703 = 1699055) B1699055
theorem B2870063 : Blo 1132632 2870063 := bstep (se 1 (by rfl) ⟨2152547, by rfl⟩ : syracuseStep 2870063 = 4305095) B4305095
theorem B1133983 : Blo 1132632 1133983 := bstep (se 1 (by rfl) ⟨850487, by rfl⟩ : syracuseStep 1133983 = 1700975) B1700975
theorem B4313371 : Blo 1132632 4313371 := bstep (se 1 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 4313371 = 6470057) B6470057
theorem B1135087 : Blo 1132632 1135087 := bstep (se 1 (by rfl) ⟨851315, by rfl⟩ : syracuseStep 1135087 = 1702631) B1702631
theorem B1135343 : Blo 1132632 1135343 := bstep (se 1 (by rfl) ⟨851507, by rfl⟩ : syracuseStep 1135343 = 1703015) B1703015
theorem B4313843 : Blo 1132632 4313843 := bstep (se 1 (by rfl) ⟨3235382, by rfl⟩ : syracuseStep 4313843 = 6470765) B6470765
theorem B21779239 : Blo 1132632 21779239 := bstep (se 1 (by rfl) ⟨16334429, by rfl⟩ : syracuseStep 21779239 = 32668859) B32668859
theorem B19354949 : Blo 1132632 19354949 := bstep (se 4 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 19354949 = 3629053) B3629053
theorem B124081631 : Blo 1132632 124081631 := bstep (se 1 (by rfl) ⟨93061223, by rfl⟩ : syracuseStep 124081631 = 186122447) B186122447
theorem B2873951 : Blo 1132632 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B31940567 : Blo 1132632 31940567 := bstep (se 1 (by rfl) ⟨23955425, by rfl⟩ : syracuseStep 31940567 = 47910851) B47910851
theorem B2548475 : Blo 1132632 2548475 := bstep (se 1 (by rfl) ⟨1911356, by rfl⟩ : syracuseStep 2548475 = 3822713) B3822713
theorem B12936833 : Blo 1132632 12936833 := bstep (se 2 (by rfl) ⟨4851312, by rfl⟩ : syracuseStep 12936833 = 9702625) B9702625
theorem B2551337 : Blo 1132632 2551337 := bstep (se 2 (by rfl) ⟨956751, by rfl⟩ : syracuseStep 2551337 = 1913503) B1913503
theorem B3829787 : Blo 1132632 3829787 := bstep (se 1 (by rfl) ⟨2872340, by rfl⟩ : syracuseStep 3829787 = 5744681) B5744681
theorem B1700393 : Blo 1132632 1700393 := bstep (se 2 (by rfl) ⟨637647, by rfl⟩ : syracuseStep 1700393 = 1275295) B1275295
theorem B1700543 : Blo 1132632 1700543 := bstep (se 1 (by rfl) ⟨1275407, by rfl⟩ : syracuseStep 1700543 = 2550815) B2550815
theorem B1276015 : Blo 1132632 1276015 := bstep (se 1 (by rfl) ⟨957011, by rfl⟩ : syracuseStep 1276015 = 1914023) B1914023
theorem B1276699 : Blo 1132632 1276699 := bstep (se 1 (by rfl) ⟨957524, by rfl⟩ : syracuseStep 1276699 = 1915049) B1915049
theorem B29038985 : Blo 1132632 29038985 := bstep (se 2 (by rfl) ⟨10889619, by rfl⟩ : syracuseStep 29038985 = 21779239) B21779239
theorem B8624555 : Blo 1132632 8624555 := bstep (se 1 (by rfl) ⟨6468416, by rfl⟩ : syracuseStep 8624555 = 12936833) B12936833
theorem B1913375 : Blo 1132632 1913375 := bstep (se 1 (by rfl) ⟨1435031, by rfl⟩ : syracuseStep 1913375 = 2870063) B2870063
theorem B21803843 : Blo 1132632 21803843 := bstep (se 1 (by rfl) ⟨16352882, by rfl⟩ : syracuseStep 21803843 = 32705765) B32705765
theorem B5748731 : Blo 1132632 5748731 := bstep (se 1 (by rfl) ⟨4311548, by rfl⟩ : syracuseStep 5748731 = 8623097) B8623097
theorem B82721087 : Blo 1132632 82721087 := bstep (se 1 (by rfl) ⟨62040815, by rfl⟩ : syracuseStep 82721087 = 124081631) B124081631
theorem B1915967 : Blo 1132632 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B5751161 : Blo 1132632 5751161 := bstep (se 2 (by rfl) ⟨2156685, by rfl⟩ : syracuseStep 5751161 = 4313371) B4313371
theorem B1133595 : Blo 1132632 1133595 := bstep (se 1 (by rfl) ⟨850196, by rfl⟩ : syracuseStep 1133595 = 1700393) B1700393
theorem B1133695 : Blo 1132632 1133695 := bstep (se 1 (by rfl) ⟨850271, by rfl⟩ : syracuseStep 1133695 = 1700543) B1700543
theorem B1136383 : Blo 1132632 1136383 := bstep (se 1 (by rfl) ⟨852287, by rfl⟩ : syracuseStep 1136383 = 1704575) B1704575
theorem B4087991 : Blo 1132632 4087991 := bstep (se 1 (by rfl) ⟨3065993, by rfl⟩ : syracuseStep 4087991 = 6131987) B6131987
theorem B2875895 : Blo 1132632 2875895 := bstep (se 1 (by rfl) ⟨2156921, by rfl⟩ : syracuseStep 2875895 = 4313843) B4313843
theorem B12903299 : Blo 1132632 12903299 := bstep (se 1 (by rfl) ⟨9677474, by rfl⟩ : syracuseStep 12903299 = 19354949) B19354949
theorem B3630683 : Blo 1132632 3630683 := bstep (se 1 (by rfl) ⟨2723012, by rfl⟩ : syracuseStep 3630683 = 5446025) B5446025
theorem B21293711 : Blo 1132632 21293711 := bstep (se 1 (by rfl) ⟨15970283, by rfl⟩ : syracuseStep 21293711 = 31940567) B31940567
theorem B2550761 : Blo 1132632 2550761 := bstep (se 2 (by rfl) ⟨956535, by rfl⟩ : syracuseStep 2550761 = 1913071) B1913071
theorem B1698983 : Blo 1132632 1698983 := bstep (se 1 (by rfl) ⟨1274237, by rfl⟩ : syracuseStep 1698983 = 2548475) B2548475
theorem B3828923 : Blo 1132632 3828923 := bstep (se 1 (by rfl) ⟨2871692, by rfl⟩ : syracuseStep 3828923 = 5743385) B5743385
theorem B1700891 : Blo 1132632 1700891 := bstep (se 1 (by rfl) ⟨1275668, by rfl⟩ : syracuseStep 1700891 = 2551337) B2551337
theorem B2553191 : Blo 1132632 2553191 := bstep (se 1 (by rfl) ⟨1914893, by rfl⟩ : syracuseStep 2553191 = 3829787) B3829787
theorem B1701353 : Blo 1132632 1701353 := bstep (se 2 (by rfl) ⟨638007, by rfl⟩ : syracuseStep 1701353 = 1276015) B1276015
theorem B1702265 : Blo 1132632 1702265 := bstep (se 2 (by rfl) ⟨638349, by rfl⟩ : syracuseStep 1702265 = 1276699) B1276699
theorem B3834107 : Blo 1132632 3834107 := bstep (se 1 (by rfl) ⟨2875580, by rfl⟩ : syracuseStep 3834107 = 5751161) B5751161
theorem B2725327 : Blo 1132632 2725327 := bstep (se 1 (by rfl) ⟨2043995, by rfl⟩ : syracuseStep 2725327 = 4087991) B4087991
theorem B14195807 : Blo 1132632 14195807 := bstep (se 1 (by rfl) ⟨10646855, by rfl⟩ : syracuseStep 14195807 = 21293711) B21293711
theorem B5749703 : Blo 1132632 5749703 := bstep (se 1 (by rfl) ⟨4312277, by rfl⟩ : syracuseStep 5749703 = 8624555) B8624555
theorem B1917263 : Blo 1132632 1917263 := bstep (se 1 (by rfl) ⟨1437947, by rfl⟩ : syracuseStep 1917263 = 2875895) B2875895
theorem B8602199 : Blo 1132632 8602199 := bstep (se 1 (by rfl) ⟨6451649, by rfl⟩ : syracuseStep 8602199 = 12903299) B12903299
theorem B1132655 : Blo 1132632 1132655 := bstep (se 1 (by rfl) ⟨849491, by rfl⟩ : syracuseStep 1132655 = 1698983) B1698983
theorem B14535895 : Blo 1132632 14535895 := bstep (se 1 (by rfl) ⟨10901921, by rfl⟩ : syracuseStep 14535895 = 21803843) B21803843
theorem B1133927 : Blo 1132632 1133927 := bstep (se 1 (by rfl) ⟨850445, by rfl⟩ : syracuseStep 1133927 = 1700891) B1700891
theorem B1134235 : Blo 1132632 1134235 := bstep (se 1 (by rfl) ⟨850676, by rfl⟩ : syracuseStep 1134235 = 1701353) B1701353
theorem B1134843 : Blo 1132632 1134843 := bstep (se 1 (by rfl) ⟨851132, by rfl⟩ : syracuseStep 1134843 = 1702265) B1702265
theorem B19359323 : Blo 1132632 19359323 := bstep (se 1 (by rfl) ⟨14519492, by rfl⟩ : syracuseStep 19359323 = 29038985) B29038985
theorem B2420455 : Blo 1132632 2420455 := bstep (se 1 (by rfl) ⟨1815341, by rfl⟩ : syracuseStep 2420455 = 3630683) B3630683
theorem B1700507 : Blo 1132632 1700507 := bstep (se 1 (by rfl) ⟨1275380, by rfl⟩ : syracuseStep 1700507 = 2550761) B2550761
theorem B2552615 : Blo 1132632 2552615 := bstep (se 1 (by rfl) ⟨1914461, by rfl⟩ : syracuseStep 2552615 = 3828923) B3828923
theorem B1275583 : Blo 1132632 1275583 := bstep (se 1 (by rfl) ⟨956687, by rfl⟩ : syracuseStep 1275583 = 1913375) B1913375
theorem B1702127 : Blo 1132632 1702127 := bstep (se 1 (by rfl) ⟨1276595, by rfl⟩ : syracuseStep 1702127 = 2553191) B2553191
theorem B3832487 : Blo 1132632 3832487 := bstep (se 1 (by rfl) ⟨2874365, by rfl⟩ : syracuseStep 3832487 = 5748731) B5748731
theorem B55147391 : Blo 1132632 55147391 := bstep (se 1 (by rfl) ⟨41360543, by rfl⟩ : syracuseStep 55147391 = 82721087) B82721087
theorem B1277311 : Blo 1132632 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B2556071 : Blo 1132632 2556071 := bstep (se 1 (by rfl) ⟨1917053, by rfl⟩ : syracuseStep 2556071 = 3834107) B3834107
theorem B1278175 : Blo 1132632 1278175 := bstep (se 1 (by rfl) ⟨958631, by rfl⟩ : syracuseStep 1278175 = 1917263) B1917263
theorem B5734799 : Blo 1132632 5734799 := bstep (se 1 (by rfl) ⟨4301099, by rfl⟩ : syracuseStep 5734799 = 8602199) B8602199
theorem B19381193 : Blo 1132632 19381193 := bstep (se 2 (by rfl) ⟨7267947, by rfl⟩ : syracuseStep 19381193 = 14535895) B14535895
theorem B3227273 : Blo 1132632 3227273 := bstep (se 2 (by rfl) ⟨1210227, by rfl⟩ : syracuseStep 3227273 = 2420455) B2420455
theorem B1133671 : Blo 1132632 1133671 := bstep (se 1 (by rfl) ⟨850253, by rfl⟩ : syracuseStep 1133671 = 1700507) B1700507
theorem B1134751 : Blo 1132632 1134751 := bstep (se 1 (by rfl) ⟨851063, by rfl⟩ : syracuseStep 1134751 = 1702127) B1702127
theorem B9463871 : Blo 1132632 9463871 := bstep (se 1 (by rfl) ⟨7097903, by rfl⟩ : syracuseStep 9463871 = 14195807) B14195807
theorem B12906215 : Blo 1132632 12906215 := bstep (se 1 (by rfl) ⟨9679661, by rfl⟩ : syracuseStep 12906215 = 19359323) B19359323
theorem B3633769 : Blo 1132632 3633769 := bstep (se 2 (by rfl) ⟨1362663, by rfl⟩ : syracuseStep 3633769 = 2725327) B2725327
theorem B1700777 : Blo 1132632 1700777 := bstep (se 2 (by rfl) ⟨637791, by rfl⟩ : syracuseStep 1700777 = 1275583) B1275583
theorem B1701743 : Blo 1132632 1701743 := bstep (se 1 (by rfl) ⟨1276307, by rfl⟩ : syracuseStep 1701743 = 2552615) B2552615
theorem B2554991 : Blo 1132632 2554991 := bstep (se 1 (by rfl) ⟨1916243, by rfl⟩ : syracuseStep 2554991 = 3832487) B3832487
theorem B1703081 : Blo 1132632 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B36764927 : Blo 1132632 36764927 := bstep (se 1 (by rfl) ⟨27573695, by rfl⟩ : syracuseStep 36764927 = 55147391) B55147391
theorem B3833135 : Blo 1132632 3833135 := bstep (se 1 (by rfl) ⟨2874851, by rfl⟩ : syracuseStep 3833135 = 5749703) B5749703
theorem B1704047 : Blo 1132632 1704047 := bstep (se 1 (by rfl) ⟨1278035, by rfl⟩ : syracuseStep 1704047 = 2556071) B2556071
theorem B1704233 : Blo 1132632 1704233 := bstep (se 2 (by rfl) ⟨639087, by rfl⟩ : syracuseStep 1704233 = 1278175) B1278175
theorem B25236989 : Blo 1132632 25236989 := bstep (se 3 (by rfl) ⟨4731935, by rfl⟩ : syracuseStep 25236989 = 9463871) B9463871
theorem B12920795 : Blo 1132632 12920795 := bstep (se 1 (by rfl) ⟨9690596, by rfl⟩ : syracuseStep 12920795 = 19381193) B19381193
theorem B8604143 : Blo 1132632 8604143 := bstep (se 1 (by rfl) ⟨6453107, by rfl⟩ : syracuseStep 8604143 = 12906215) B12906215
theorem B1133851 : Blo 1132632 1133851 := bstep (se 1 (by rfl) ⟨850388, by rfl⟩ : syracuseStep 1133851 = 1700777) B1700777
theorem B1134495 : Blo 1132632 1134495 := bstep (se 1 (by rfl) ⟨850871, by rfl⟩ : syracuseStep 1134495 = 1701743) B1701743
theorem B1135387 : Blo 1132632 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B2151515 : Blo 1132632 2151515 := bstep (se 1 (by rfl) ⟨1613636, by rfl⟩ : syracuseStep 2151515 = 3227273) B3227273
theorem B3823199 : Blo 1132632 3823199 := bstep (se 1 (by rfl) ⟨2867399, by rfl⟩ : syracuseStep 3823199 = 5734799) B5734799
theorem B4845025 : Blo 1132632 4845025 := bstep (se 2 (by rfl) ⟨1816884, by rfl⟩ : syracuseStep 4845025 = 3633769) B3633769
theorem B1703327 : Blo 1132632 1703327 := bstep (se 1 (by rfl) ⟨1277495, by rfl⟩ : syracuseStep 1703327 = 2554991) B2554991
theorem B24509951 : Blo 1132632 24509951 := bstep (se 1 (by rfl) ⟨18382463, by rfl⟩ : syracuseStep 24509951 = 36764927) B36764927
theorem B2555423 : Blo 1132632 2555423 := bstep (se 1 (by rfl) ⟨1916567, by rfl⟩ : syracuseStep 2555423 = 3833135) B3833135
theorem B5736095 : Blo 1132632 5736095 := bstep (se 1 (by rfl) ⟨4302071, by rfl⟩ : syracuseStep 5736095 = 8604143) B8604143
theorem B6460033 : Blo 1132632 6460033 := bstep (se 2 (by rfl) ⟨2422512, by rfl⟩ : syracuseStep 6460033 = 4845025) B4845025
theorem B1135551 : Blo 1132632 1135551 := bstep (se 1 (by rfl) ⟨851663, by rfl⟩ : syracuseStep 1135551 = 1703327) B1703327
theorem B16339967 : Blo 1132632 16339967 := bstep (se 1 (by rfl) ⟨12254975, by rfl⟩ : syracuseStep 16339967 = 24509951) B24509951
theorem B1076778197 : Blo 1132632 1076778197 := bstep (se 7 (by rfl) ⟨12618494, by rfl⟩ : syracuseStep 1076778197 = 25236989) B25236989
theorem B1136031 : Blo 1132632 1136031 := bstep (se 1 (by rfl) ⟨852023, by rfl⟩ : syracuseStep 1136031 = 1704047) B1704047
theorem B1136155 : Blo 1132632 1136155 := bstep (se 1 (by rfl) ⟨852116, by rfl⟩ : syracuseStep 1136155 = 1704233) B1704233
theorem B1434343 : Blo 1132632 1434343 := bstep (se 1 (by rfl) ⟨1075757, by rfl⟩ : syracuseStep 1434343 = 2151515) B2151515
theorem B2548799 : Blo 1132632 2548799 := bstep (se 1 (by rfl) ⟨1911599, by rfl⟩ : syracuseStep 2548799 = 3823199) B3823199
theorem B8613863 : Blo 1132632 8613863 := bstep (se 1 (by rfl) ⟨6460397, by rfl⟩ : syracuseStep 8613863 = 12920795) B12920795
theorem B1703615 : Blo 1132632 1703615 := bstep (se 1 (by rfl) ⟨1277711, by rfl⟩ : syracuseStep 1703615 = 2555423) B2555423
theorem B717852131 : Blo 1132632 717852131 := bstep (se 1 (by rfl) ⟨538389098, by rfl⟩ : syracuseStep 717852131 = 1076778197) B1076778197
theorem B5742575 : Blo 1132632 5742575 := bstep (se 1 (by rfl) ⟨4306931, by rfl⟩ : syracuseStep 5742575 = 8613863) B8613863
theorem B1912457 : Blo 1132632 1912457 := bstep (se 2 (by rfl) ⟨717171, by rfl⟩ : syracuseStep 1912457 = 1434343) B1434343
theorem B10893311 : Blo 1132632 10893311 := bstep (se 1 (by rfl) ⟨8169983, by rfl⟩ : syracuseStep 10893311 = 16339967) B16339967
theorem B1135743 : Blo 1132632 1135743 := bstep (se 1 (by rfl) ⟨851807, by rfl⟩ : syracuseStep 1135743 = 1703615) B1703615
theorem B3824063 : Blo 1132632 3824063 := bstep (se 1 (by rfl) ⟨2868047, by rfl⟩ : syracuseStep 3824063 = 5736095) B5736095
theorem B1699199 : Blo 1132632 1699199 := bstep (se 1 (by rfl) ⟨1274399, by rfl⟩ : syracuseStep 1699199 = 2548799) B2548799
theorem B8613377 : Blo 1132632 8613377 := bstep (se 2 (by rfl) ⟨3230016, by rfl⟩ : syracuseStep 8613377 = 6460033) B6460033
theorem B5742251 : Blo 1132632 5742251 := bstep (se 1 (by rfl) ⟨4306688, by rfl⟩ : syracuseStep 5742251 = 8613377) B8613377
theorem B1132799 : Blo 1132632 1132799 := bstep (se 1 (by rfl) ⟨849599, by rfl⟩ : syracuseStep 1132799 = 1699199) B1699199
theorem B7262207 : Blo 1132632 7262207 := bstep (se 1 (by rfl) ⟨5446655, by rfl⟩ : syracuseStep 7262207 = 10893311) B10893311
theorem B478568087 : Blo 1132632 478568087 := bstep (se 1 (by rfl) ⟨358926065, by rfl⟩ : syracuseStep 478568087 = 717852131) B717852131
theorem B2549375 : Blo 1132632 2549375 := bstep (se 1 (by rfl) ⟨1912031, by rfl⟩ : syracuseStep 2549375 = 3824063) B3824063
theorem B3828383 : Blo 1132632 3828383 := bstep (se 1 (by rfl) ⟨2871287, by rfl⟩ : syracuseStep 3828383 = 5742575) B5742575
theorem B1274971 : Blo 1132632 1274971 := bstep (se 1 (by rfl) ⟨956228, by rfl⟩ : syracuseStep 1274971 = 1912457) B1912457
theorem B319045391 : Blo 1132632 319045391 := bstep (se 1 (by rfl) ⟨239284043, by rfl⟩ : syracuseStep 319045391 = 478568087) B478568087
theorem B4841471 : Blo 1132632 4841471 := bstep (se 1 (by rfl) ⟨3631103, by rfl⟩ : syracuseStep 4841471 = 7262207) B7262207
theorem B3828167 : Blo 1132632 3828167 := bstep (se 1 (by rfl) ⟨2871125, by rfl⟩ : syracuseStep 3828167 = 5742251) B5742251
theorem B1699583 : Blo 1132632 1699583 := bstep (se 1 (by rfl) ⟨1274687, by rfl⟩ : syracuseStep 1699583 = 2549375) B2549375
theorem B1699961 : Blo 1132632 1699961 := bstep (se 2 (by rfl) ⟨637485, by rfl⟩ : syracuseStep 1699961 = 1274971) B1274971
theorem B2552255 : Blo 1132632 2552255 := bstep (se 1 (by rfl) ⟨1914191, by rfl⟩ : syracuseStep 2552255 = 3828383) B3828383
theorem B1133055 : Blo 1132632 1133055 := bstep (se 1 (by rfl) ⟨849791, by rfl⟩ : syracuseStep 1133055 = 1699583) B1699583
theorem B1133307 : Blo 1132632 1133307 := bstep (se 1 (by rfl) ⟨849980, by rfl⟩ : syracuseStep 1133307 = 1699961) B1699961
theorem B2552111 : Blo 1132632 2552111 := bstep (se 1 (by rfl) ⟨1914083, by rfl⟩ : syracuseStep 2552111 = 3828167) B3828167
theorem B1701503 : Blo 1132632 1701503 := bstep (se 1 (by rfl) ⟨1276127, by rfl⟩ : syracuseStep 1701503 = 2552255) B2552255
theorem B212696927 : Blo 1132632 212696927 := bstep (se 1 (by rfl) ⟨159522695, by rfl⟩ : syracuseStep 212696927 = 319045391) B319045391
theorem B12910589 : Blo 1132632 12910589 := bstep (se 3 (by rfl) ⟨2420735, by rfl⟩ : syracuseStep 12910589 = 4841471) B4841471
theorem B141797951 : Blo 1132632 141797951 := bstep (se 1 (by rfl) ⟨106348463, by rfl⟩ : syracuseStep 141797951 = 212696927) B212696927
theorem B1134335 : Blo 1132632 1134335 := bstep (se 1 (by rfl) ⟨850751, by rfl⟩ : syracuseStep 1134335 = 1701503) B1701503
theorem B8607059 : Blo 1132632 8607059 := bstep (se 1 (by rfl) ⟨6455294, by rfl⟩ : syracuseStep 8607059 = 12910589) B12910589
theorem B1701407 : Blo 1132632 1701407 := bstep (se 1 (by rfl) ⟨1276055, by rfl⟩ : syracuseStep 1701407 = 2552111) B2552111
theorem B5738039 : Blo 1132632 5738039 := bstep (se 1 (by rfl) ⟨4303529, by rfl⟩ : syracuseStep 5738039 = 8607059) B8607059
theorem B1134271 : Blo 1132632 1134271 := bstep (se 1 (by rfl) ⟨850703, by rfl⟩ : syracuseStep 1134271 = 1701407) B1701407
theorem B94531967 : Blo 1132632 94531967 := bstep (se 1 (by rfl) ⟨70898975, by rfl⟩ : syracuseStep 94531967 = 141797951) B141797951
theorem B63021311 : Blo 1132632 63021311 := bstep (se 1 (by rfl) ⟨47265983, by rfl⟩ : syracuseStep 63021311 = 94531967) B94531967
theorem B3825359 : Blo 1132632 3825359 := bstep (se 1 (by rfl) ⟨2869019, by rfl⟩ : syracuseStep 3825359 = 5738039) B5738039
theorem B42014207 : Blo 1132632 42014207 := bstep (se 1 (by rfl) ⟨31510655, by rfl⟩ : syracuseStep 42014207 = 63021311) B63021311
theorem B2550239 : Blo 1132632 2550239 := bstep (se 1 (by rfl) ⟨1912679, by rfl⟩ : syracuseStep 2550239 = 3825359) B3825359
theorem B28009471 : Blo 1132632 28009471 := bstep (se 1 (by rfl) ⟨21007103, by rfl⟩ : syracuseStep 28009471 = 42014207) B42014207
theorem B1700159 : Blo 1132632 1700159 := bstep (se 1 (by rfl) ⟨1275119, by rfl⟩ : syracuseStep 1700159 = 2550239) B2550239
theorem B1133439 : Blo 1132632 1133439 := bstep (se 1 (by rfl) ⟨850079, by rfl⟩ : syracuseStep 1133439 = 1700159) B1700159
theorem B37345961 : Blo 1132632 37345961 := bstep (se 2 (by rfl) ⟨14004735, by rfl⟩ : syracuseStep 37345961 = 28009471) B28009471
theorem B24897307 : Blo 1132632 24897307 := bstep (se 1 (by rfl) ⟨18672980, by rfl⟩ : syracuseStep 24897307 = 37345961) B37345961
theorem B33196409 : Blo 1132632 33196409 := bstep (se 2 (by rfl) ⟨12448653, by rfl⟩ : syracuseStep 33196409 = 24897307) B24897307
theorem B22130939 : Blo 1132632 22130939 := bstep (se 1 (by rfl) ⟨16598204, by rfl⟩ : syracuseStep 22130939 = 33196409) B33196409
theorem B59015837 : Blo 1132632 59015837 := bstep (se 3 (by rfl) ⟨11065469, by rfl⟩ : syracuseStep 59015837 = 22130939) B22130939
theorem B39343891 : Blo 1132632 39343891 := bstep (se 1 (by rfl) ⟨29507918, by rfl⟩ : syracuseStep 39343891 = 59015837) B59015837
theorem B52458521 : Blo 1132632 52458521 := bstep (se 2 (by rfl) ⟨19671945, by rfl⟩ : syracuseStep 52458521 = 39343891) B39343891
theorem B139889389 : Blo 1132632 139889389 := bstep (se 3 (by rfl) ⟨26229260, by rfl⟩ : syracuseStep 139889389 = 52458521) B52458521
theorem B186519185 : Blo 1132632 186519185 := bstep (se 2 (by rfl) ⟨69944694, by rfl⟩ : syracuseStep 186519185 = 139889389) B139889389
theorem B124346123 : Blo 1132632 124346123 := bstep (se 1 (by rfl) ⟨93259592, by rfl⟩ : syracuseStep 124346123 = 186519185) B186519185
theorem B82897415 : Blo 1132632 82897415 := bstep (se 1 (by rfl) ⟨62173061, by rfl⟩ : syracuseStep 82897415 = 124346123) B124346123
theorem B55264943 : Blo 1132632 55264943 := bstep (se 1 (by rfl) ⟨41448707, by rfl⟩ : syracuseStep 55264943 = 82897415) B82897415
theorem B36843295 : Blo 1132632 36843295 := bstep (se 1 (by rfl) ⟨27632471, by rfl⟩ : syracuseStep 36843295 = 55264943) B55264943
theorem B49124393 : Blo 1132632 49124393 := bstep (se 2 (by rfl) ⟨18421647, by rfl⟩ : syracuseStep 49124393 = 36843295) B36843295
theorem B32749595 : Blo 1132632 32749595 := bstep (se 1 (by rfl) ⟨24562196, by rfl⟩ : syracuseStep 32749595 = 49124393) B49124393
theorem B21833063 : Blo 1132632 21833063 := bstep (se 1 (by rfl) ⟨16374797, by rfl⟩ : syracuseStep 21833063 = 32749595) B32749595
theorem B14555375 : Blo 1132632 14555375 := bstep (se 1 (by rfl) ⟨10916531, by rfl⟩ : syracuseStep 14555375 = 21833063) B21833063
theorem B9703583 : Blo 1132632 9703583 := bstep (se 1 (by rfl) ⟨7277687, by rfl⟩ : syracuseStep 9703583 = 14555375) B14555375
theorem B6469055 : Blo 1132632 6469055 := bstep (se 1 (by rfl) ⟨4851791, by rfl⟩ : syracuseStep 6469055 = 9703583) B9703583
theorem B4312703 : Blo 1132632 4312703 := bstep (se 1 (by rfl) ⟨3234527, by rfl⟩ : syracuseStep 4312703 = 6469055) B6469055
theorem B2875135 : Blo 1132632 2875135 := bstep (se 1 (by rfl) ⟨2156351, by rfl⟩ : syracuseStep 2875135 = 4312703) B4312703
theorem B3833513 : Blo 1132632 3833513 := bstep (se 2 (by rfl) ⟨1437567, by rfl⟩ : syracuseStep 3833513 = 2875135) B2875135
theorem B2555675 : Blo 1132632 2555675 := bstep (se 1 (by rfl) ⟨1916756, by rfl⟩ : syracuseStep 2555675 = 3833513) B3833513
theorem B1703783 : Blo 1132632 1703783 := bstep (se 1 (by rfl) ⟨1277837, by rfl⟩ : syracuseStep 1703783 = 2555675) B2555675
theorem B1135855 : Blo 1132632 1135855 := bstep (se 1 (by rfl) ⟨851891, by rfl⟩ : syracuseStep 1135855 = 1703783) B1703783

theorem C0 (j : ℕ) (h1 : 283158 ≤ j) (h2 : j ≤ 283857) : Blo 1132632 (4 * j + 3) := by
  interval_cases j
  · exact B1132635
  · exact B1132639
  · exact B1132643
  · exact B1132647
  · exact B1132651
  · exact B1132655
  · exact B1132659
  · exact B1132663
  · exact B1132667
  · exact B1132671
  · exact B1132675
  · exact B1132679
  · exact B1132683
  · exact B1132687
  · exact B1132691
  · exact B1132695
  · exact B1132699
  · exact B1132703
  · exact B1132707
  · exact B1132711
  · exact B1132715
  · exact B1132719
  · exact B1132723
  · exact B1132727
  · exact B1132731
  · exact B1132735
  · exact B1132739
  · exact B1132743
  · exact B1132747
  · exact B1132751
  · exact B1132755
  · exact B1132759
  · exact B1132763
  · exact B1132767
  · exact B1132771
  · exact B1132775
  · exact B1132779
  · exact B1132783
  · exact B1132787
  · exact B1132791
  · exact B1132795
  · exact B1132799
  · exact B1132803
  · exact B1132807
  · exact B1132811
  · exact B1132815
  · exact B1132819
  · exact B1132823
  · exact B1132827
  · exact B1132831
  · exact B1132835
  · exact B1132839
  · exact B1132843
  · exact B1132847
  · exact B1132851
  · exact B1132855
  · exact B1132859
  · exact B1132863
  · exact B1132867
  · exact B1132871
  · exact B1132875
  · exact B1132879
  · exact B1132883
  · exact B1132887
  · exact B1132891
  · exact B1132895
  · exact B1132899
  · exact B1132903
  · exact B1132907
  · exact B1132911
  · exact B1132915
  · exact B1132919
  · exact B1132923
  · exact B1132927
  · exact B1132931
  · exact B1132935
  · exact B1132939
  · exact B1132943
  · exact B1132947
  · exact B1132951
  · exact B1132955
  · exact B1132959
  · exact B1132963
  · exact B1132967
  · exact B1132971
  · exact B1132975
  · exact B1132979
  · exact B1132983
  · exact B1132987
  · exact B1132991
  · exact B1132995
  · exact B1132999
  · exact B1133003
  · exact B1133007
  · exact B1133011
  · exact B1133015
  · exact B1133019
  · exact B1133023
  · exact B1133027
  · exact B1133031
  · exact B1133035
  · exact B1133039
  · exact B1133043
  · exact B1133047
  · exact B1133051
  · exact B1133055
  · exact B1133059
  · exact B1133063
  · exact B1133067
  · exact B1133071
  · exact B1133075
  · exact B1133079
  · exact B1133083
  · exact B1133087
  · exact B1133091
  · exact B1133095
  · exact B1133099
  · exact B1133103
  · exact B1133107
  · exact B1133111
  · exact B1133115
  · exact B1133119
  · exact B1133123
  · exact B1133127
  · exact B1133131
  · exact B1133135
  · exact B1133139
  · exact B1133143
  · exact B1133147
  · exact B1133151
  · exact B1133155
  · exact B1133159
  · exact B1133163
  · exact B1133167
  · exact B1133171
  · exact B1133175
  · exact B1133179
  · exact B1133183
  · exact B1133187
  · exact B1133191
  · exact B1133195
  · exact B1133199
  · exact B1133203
  · exact B1133207
  · exact B1133211
  · exact B1133215
  · exact B1133219
  · exact B1133223
  · exact B1133227
  · exact B1133231
  · exact B1133235
  · exact B1133239
  · exact B1133243
  · exact B1133247
  · exact B1133251
  · exact B1133255
  · exact B1133259
  · exact B1133263
  · exact B1133267
  · exact B1133271
  · exact B1133275
  · exact B1133279
  · exact B1133283
  · exact B1133287
  · exact B1133291
  · exact B1133295
  · exact B1133299
  · exact B1133303
  · exact B1133307
  · exact B1133311
  · exact B1133315
  · exact B1133319
  · exact B1133323
  · exact B1133327
  · exact B1133331
  · exact B1133335
  · exact B1133339
  · exact B1133343
  · exact B1133347
  · exact B1133351
  · exact B1133355
  · exact B1133359
  · exact B1133363
  · exact B1133367
  · exact B1133371
  · exact B1133375
  · exact B1133379
  · exact B1133383
  · exact B1133387
  · exact B1133391
  · exact B1133395
  · exact B1133399
  · exact B1133403
  · exact B1133407
  · exact B1133411
  · exact B1133415
  · exact B1133419
  · exact B1133423
  · exact B1133427
  · exact B1133431
  · exact B1133435
  · exact B1133439
  · exact B1133443
  · exact B1133447
  · exact B1133451
  · exact B1133455
  · exact B1133459
  · exact B1133463
  · exact B1133467
  · exact B1133471
  · exact B1133475
  · exact B1133479
  · exact B1133483
  · exact B1133487
  · exact B1133491
  · exact B1133495
  · exact B1133499
  · exact B1133503
  · exact B1133507
  · exact B1133511
  · exact B1133515
  · exact B1133519
  · exact B1133523
  · exact B1133527
  · exact B1133531
  · exact B1133535
  · exact B1133539
  · exact B1133543
  · exact B1133547
  · exact B1133551
  · exact B1133555
  · exact B1133559
  · exact B1133563
  · exact B1133567
  · exact B1133571
  · exact B1133575
  · exact B1133579
  · exact B1133583
  · exact B1133587
  · exact B1133591
  · exact B1133595
  · exact B1133599
  · exact B1133603
  · exact B1133607
  · exact B1133611
  · exact B1133615
  · exact B1133619
  · exact B1133623
  · exact B1133627
  · exact B1133631
  · exact B1133635
  · exact B1133639
  · exact B1133643
  · exact B1133647
  · exact B1133651
  · exact B1133655
  · exact B1133659
  · exact B1133663
  · exact B1133667
  · exact B1133671
  · exact B1133675
  · exact B1133679
  · exact B1133683
  · exact B1133687
  · exact B1133691
  · exact B1133695
  · exact B1133699
  · exact B1133703
  · exact B1133707
  · exact B1133711
  · exact B1133715
  · exact B1133719
  · exact B1133723
  · exact B1133727
  · exact B1133731
  · exact B1133735
  · exact B1133739
  · exact B1133743
  · exact B1133747
  · exact B1133751
  · exact B1133755
  · exact B1133759
  · exact B1133763
  · exact B1133767
  · exact B1133771
  · exact B1133775
  · exact B1133779
  · exact B1133783
  · exact B1133787
  · exact B1133791
  · exact B1133795
  · exact B1133799
  · exact B1133803
  · exact B1133807
  · exact B1133811
  · exact B1133815
  · exact B1133819
  · exact B1133823
  · exact B1133827
  · exact B1133831
  · exact B1133835
  · exact B1133839
  · exact B1133843
  · exact B1133847
  · exact B1133851
  · exact B1133855
  · exact B1133859
  · exact B1133863
  · exact B1133867
  · exact B1133871
  · exact B1133875
  · exact B1133879
  · exact B1133883
  · exact B1133887
  · exact B1133891
  · exact B1133895
  · exact B1133899
  · exact B1133903
  · exact B1133907
  · exact B1133911
  · exact B1133915
  · exact B1133919
  · exact B1133923
  · exact B1133927
  · exact B1133931
  · exact B1133935
  · exact B1133939
  · exact B1133943
  · exact B1133947
  · exact B1133951
  · exact B1133955
  · exact B1133959
  · exact B1133963
  · exact B1133967
  · exact B1133971
  · exact B1133975
  · exact B1133979
  · exact B1133983
  · exact B1133987
  · exact B1133991
  · exact B1133995
  · exact B1133999
  · exact B1134003
  · exact B1134007
  · exact B1134011
  · exact B1134015
  · exact B1134019
  · exact B1134023
  · exact B1134027
  · exact B1134031
  · exact B1134035
  · exact B1134039
  · exact B1134043
  · exact B1134047
  · exact B1134051
  · exact B1134055
  · exact B1134059
  · exact B1134063
  · exact B1134067
  · exact B1134071
  · exact B1134075
  · exact B1134079
  · exact B1134083
  · exact B1134087
  · exact B1134091
  · exact B1134095
  · exact B1134099
  · exact B1134103
  · exact B1134107
  · exact B1134111
  · exact B1134115
  · exact B1134119
  · exact B1134123
  · exact B1134127
  · exact B1134131
  · exact B1134135
  · exact B1134139
  · exact B1134143
  · exact B1134147
  · exact B1134151
  · exact B1134155
  · exact B1134159
  · exact B1134163
  · exact B1134167
  · exact B1134171
  · exact B1134175
  · exact B1134179
  · exact B1134183
  · exact B1134187
  · exact B1134191
  · exact B1134195
  · exact B1134199
  · exact B1134203
  · exact B1134207
  · exact B1134211
  · exact B1134215
  · exact B1134219
  · exact B1134223
  · exact B1134227
  · exact B1134231
  · exact B1134235
  · exact B1134239
  · exact B1134243
  · exact B1134247
  · exact B1134251
  · exact B1134255
  · exact B1134259
  · exact B1134263
  · exact B1134267
  · exact B1134271
  · exact B1134275
  · exact B1134279
  · exact B1134283
  · exact B1134287
  · exact B1134291
  · exact B1134295
  · exact B1134299
  · exact B1134303
  · exact B1134307
  · exact B1134311
  · exact B1134315
  · exact B1134319
  · exact B1134323
  · exact B1134327
  · exact B1134331
  · exact B1134335
  · exact B1134339
  · exact B1134343
  · exact B1134347
  · exact B1134351
  · exact B1134355
  · exact B1134359
  · exact B1134363
  · exact B1134367
  · exact B1134371
  · exact B1134375
  · exact B1134379
  · exact B1134383
  · exact B1134387
  · exact B1134391
  · exact B1134395
  · exact B1134399
  · exact B1134403
  · exact B1134407
  · exact B1134411
  · exact B1134415
  · exact B1134419
  · exact B1134423
  · exact B1134427
  · exact B1134431
  · exact B1134435
  · exact B1134439
  · exact B1134443
  · exact B1134447
  · exact B1134451
  · exact B1134455
  · exact B1134459
  · exact B1134463
  · exact B1134467
  · exact B1134471
  · exact B1134475
  · exact B1134479
  · exact B1134483
  · exact B1134487
  · exact B1134491
  · exact B1134495
  · exact B1134499
  · exact B1134503
  · exact B1134507
  · exact B1134511
  · exact B1134515
  · exact B1134519
  · exact B1134523
  · exact B1134527
  · exact B1134531
  · exact B1134535
  · exact B1134539
  · exact B1134543
  · exact B1134547
  · exact B1134551
  · exact B1134555
  · exact B1134559
  · exact B1134563
  · exact B1134567
  · exact B1134571
  · exact B1134575
  · exact B1134579
  · exact B1134583
  · exact B1134587
  · exact B1134591
  · exact B1134595
  · exact B1134599
  · exact B1134603
  · exact B1134607
  · exact B1134611
  · exact B1134615
  · exact B1134619
  · exact B1134623
  · exact B1134627
  · exact B1134631
  · exact B1134635
  · exact B1134639
  · exact B1134643
  · exact B1134647
  · exact B1134651
  · exact B1134655
  · exact B1134659
  · exact B1134663
  · exact B1134667
  · exact B1134671
  · exact B1134675
  · exact B1134679
  · exact B1134683
  · exact B1134687
  · exact B1134691
  · exact B1134695
  · exact B1134699
  · exact B1134703
  · exact B1134707
  · exact B1134711
  · exact B1134715
  · exact B1134719
  · exact B1134723
  · exact B1134727
  · exact B1134731
  · exact B1134735
  · exact B1134739
  · exact B1134743
  · exact B1134747
  · exact B1134751
  · exact B1134755
  · exact B1134759
  · exact B1134763
  · exact B1134767
  · exact B1134771
  · exact B1134775
  · exact B1134779
  · exact B1134783
  · exact B1134787
  · exact B1134791
  · exact B1134795
  · exact B1134799
  · exact B1134803
  · exact B1134807
  · exact B1134811
  · exact B1134815
  · exact B1134819
  · exact B1134823
  · exact B1134827
  · exact B1134831
  · exact B1134835
  · exact B1134839
  · exact B1134843
  · exact B1134847
  · exact B1134851
  · exact B1134855
  · exact B1134859
  · exact B1134863
  · exact B1134867
  · exact B1134871
  · exact B1134875
  · exact B1134879
  · exact B1134883
  · exact B1134887
  · exact B1134891
  · exact B1134895
  · exact B1134899
  · exact B1134903
  · exact B1134907
  · exact B1134911
  · exact B1134915
  · exact B1134919
  · exact B1134923
  · exact B1134927
  · exact B1134931
  · exact B1134935
  · exact B1134939
  · exact B1134943
  · exact B1134947
  · exact B1134951
  · exact B1134955
  · exact B1134959
  · exact B1134963
  · exact B1134967
  · exact B1134971
  · exact B1134975
  · exact B1134979
  · exact B1134983
  · exact B1134987
  · exact B1134991
  · exact B1134995
  · exact B1134999
  · exact B1135003
  · exact B1135007
  · exact B1135011
  · exact B1135015
  · exact B1135019
  · exact B1135023
  · exact B1135027
  · exact B1135031
  · exact B1135035
  · exact B1135039
  · exact B1135043
  · exact B1135047
  · exact B1135051
  · exact B1135055
  · exact B1135059
  · exact B1135063
  · exact B1135067
  · exact B1135071
  · exact B1135075
  · exact B1135079
  · exact B1135083
  · exact B1135087
  · exact B1135091
  · exact B1135095
  · exact B1135099
  · exact B1135103
  · exact B1135107
  · exact B1135111
  · exact B1135115
  · exact B1135119
  · exact B1135123
  · exact B1135127
  · exact B1135131
  · exact B1135135
  · exact B1135139
  · exact B1135143
  · exact B1135147
  · exact B1135151
  · exact B1135155
  · exact B1135159
  · exact B1135163
  · exact B1135167
  · exact B1135171
  · exact B1135175
  · exact B1135179
  · exact B1135183
  · exact B1135187
  · exact B1135191
  · exact B1135195
  · exact B1135199
  · exact B1135203
  · exact B1135207
  · exact B1135211
  · exact B1135215
  · exact B1135219
  · exact B1135223
  · exact B1135227
  · exact B1135231
  · exact B1135235
  · exact B1135239
  · exact B1135243
  · exact B1135247
  · exact B1135251
  · exact B1135255
  · exact B1135259
  · exact B1135263
  · exact B1135267
  · exact B1135271
  · exact B1135275
  · exact B1135279
  · exact B1135283
  · exact B1135287
  · exact B1135291
  · exact B1135295
  · exact B1135299
  · exact B1135303
  · exact B1135307
  · exact B1135311
  · exact B1135315
  · exact B1135319
  · exact B1135323
  · exact B1135327
  · exact B1135331
  · exact B1135335
  · exact B1135339
  · exact B1135343
  · exact B1135347
  · exact B1135351
  · exact B1135355
  · exact B1135359
  · exact B1135363
  · exact B1135367
  · exact B1135371
  · exact B1135375
  · exact B1135379
  · exact B1135383
  · exact B1135387
  · exact B1135391
  · exact B1135395
  · exact B1135399
  · exact B1135403
  · exact B1135407
  · exact B1135411
  · exact B1135415
  · exact B1135419
  · exact B1135423
  · exact B1135427
  · exact B1135431

theorem C1 (j : ℕ) (h1 : 283858 ≤ j) (h2 : j ≤ 284157) : Blo 1132632 (4 * j + 3) := by
  interval_cases j
  · exact B1135435
  · exact B1135439
  · exact B1135443
  · exact B1135447
  · exact B1135451
  · exact B1135455
  · exact B1135459
  · exact B1135463
  · exact B1135467
  · exact B1135471
  · exact B1135475
  · exact B1135479
  · exact B1135483
  · exact B1135487
  · exact B1135491
  · exact B1135495
  · exact B1135499
  · exact B1135503
  · exact B1135507
  · exact B1135511
  · exact B1135515
  · exact B1135519
  · exact B1135523
  · exact B1135527
  · exact B1135531
  · exact B1135535
  · exact B1135539
  · exact B1135543
  · exact B1135547
  · exact B1135551
  · exact B1135555
  · exact B1135559
  · exact B1135563
  · exact B1135567
  · exact B1135571
  · exact B1135575
  · exact B1135579
  · exact B1135583
  · exact B1135587
  · exact B1135591
  · exact B1135595
  · exact B1135599
  · exact B1135603
  · exact B1135607
  · exact B1135611
  · exact B1135615
  · exact B1135619
  · exact B1135623
  · exact B1135627
  · exact B1135631
  · exact B1135635
  · exact B1135639
  · exact B1135643
  · exact B1135647
  · exact B1135651
  · exact B1135655
  · exact B1135659
  · exact B1135663
  · exact B1135667
  · exact B1135671
  · exact B1135675
  · exact B1135679
  · exact B1135683
  · exact B1135687
  · exact B1135691
  · exact B1135695
  · exact B1135699
  · exact B1135703
  · exact B1135707
  · exact B1135711
  · exact B1135715
  · exact B1135719
  · exact B1135723
  · exact B1135727
  · exact B1135731
  · exact B1135735
  · exact B1135739
  · exact B1135743
  · exact B1135747
  · exact B1135751
  · exact B1135755
  · exact B1135759
  · exact B1135763
  · exact B1135767
  · exact B1135771
  · exact B1135775
  · exact B1135779
  · exact B1135783
  · exact B1135787
  · exact B1135791
  · exact B1135795
  · exact B1135799
  · exact B1135803
  · exact B1135807
  · exact B1135811
  · exact B1135815
  · exact B1135819
  · exact B1135823
  · exact B1135827
  · exact B1135831
  · exact B1135835
  · exact B1135839
  · exact B1135843
  · exact B1135847
  · exact B1135851
  · exact B1135855
  · exact B1135859
  · exact B1135863
  · exact B1135867
  · exact B1135871
  · exact B1135875
  · exact B1135879
  · exact B1135883
  · exact B1135887
  · exact B1135891
  · exact B1135895
  · exact B1135899
  · exact B1135903
  · exact B1135907
  · exact B1135911
  · exact B1135915
  · exact B1135919
  · exact B1135923
  · exact B1135927
  · exact B1135931
  · exact B1135935
  · exact B1135939
  · exact B1135943
  · exact B1135947
  · exact B1135951
  · exact B1135955
  · exact B1135959
  · exact B1135963
  · exact B1135967
  · exact B1135971
  · exact B1135975
  · exact B1135979
  · exact B1135983
  · exact B1135987
  · exact B1135991
  · exact B1135995
  · exact B1135999
  · exact B1136003
  · exact B1136007
  · exact B1136011
  · exact B1136015
  · exact B1136019
  · exact B1136023
  · exact B1136027
  · exact B1136031
  · exact B1136035
  · exact B1136039
  · exact B1136043
  · exact B1136047
  · exact B1136051
  · exact B1136055
  · exact B1136059
  · exact B1136063
  · exact B1136067
  · exact B1136071
  · exact B1136075
  · exact B1136079
  · exact B1136083
  · exact B1136087
  · exact B1136091
  · exact B1136095
  · exact B1136099
  · exact B1136103
  · exact B1136107
  · exact B1136111
  · exact B1136115
  · exact B1136119
  · exact B1136123
  · exact B1136127
  · exact B1136131
  · exact B1136135
  · exact B1136139
  · exact B1136143
  · exact B1136147
  · exact B1136151
  · exact B1136155
  · exact B1136159
  · exact B1136163
  · exact B1136167
  · exact B1136171
  · exact B1136175
  · exact B1136179
  · exact B1136183
  · exact B1136187
  · exact B1136191
  · exact B1136195
  · exact B1136199
  · exact B1136203
  · exact B1136207
  · exact B1136211
  · exact B1136215
  · exact B1136219
  · exact B1136223
  · exact B1136227
  · exact B1136231
  · exact B1136235
  · exact B1136239
  · exact B1136243
  · exact B1136247
  · exact B1136251
  · exact B1136255
  · exact B1136259
  · exact B1136263
  · exact B1136267
  · exact B1136271
  · exact B1136275
  · exact B1136279
  · exact B1136283
  · exact B1136287
  · exact B1136291
  · exact B1136295
  · exact B1136299
  · exact B1136303
  · exact B1136307
  · exact B1136311
  · exact B1136315
  · exact B1136319
  · exact B1136323
  · exact B1136327
  · exact B1136331
  · exact B1136335
  · exact B1136339
  · exact B1136343
  · exact B1136347
  · exact B1136351
  · exact B1136355
  · exact B1136359
  · exact B1136363
  · exact B1136367
  · exact B1136371
  · exact B1136375
  · exact B1136379
  · exact B1136383
  · exact B1136387
  · exact B1136391
  · exact B1136395
  · exact B1136399
  · exact B1136403
  · exact B1136407
  · exact B1136411
  · exact B1136415
  · exact B1136419
  · exact B1136423
  · exact B1136427
  · exact B1136431
  · exact B1136435
  · exact B1136439
  · exact B1136443
  · exact B1136447
  · exact B1136451
  · exact B1136455
  · exact B1136459
  · exact B1136463
  · exact B1136467
  · exact B1136471
  · exact B1136475
  · exact B1136479
  · exact B1136483
  · exact B1136487
  · exact B1136491
  · exact B1136495
  · exact B1136499
  · exact B1136503
  · exact B1136507
  · exact B1136511
  · exact B1136515
  · exact B1136519
  · exact B1136523
  · exact B1136527
  · exact B1136531
  · exact B1136535
  · exact B1136539
  · exact B1136543
  · exact B1136547
  · exact B1136551
  · exact B1136555
  · exact B1136559
  · exact B1136563
  · exact B1136567
  · exact B1136571
  · exact B1136575
  · exact B1136579
  · exact B1136583
  · exact B1136587
  · exact B1136591
  · exact B1136595
  · exact B1136599
  · exact B1136603
  · exact B1136607
  · exact B1136611
  · exact B1136615
  · exact B1136619
  · exact B1136623
  · exact B1136627
  · exact B1136631

theorem solution (m : ℕ) (hlo : 1132632 ≤ m) (hhi : m ≤ 1136632) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 283158 ≤ j := by omega
    have hj2 : j ≤ 284157 := by omega
    have hb : Blo 1132632 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 283858 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
